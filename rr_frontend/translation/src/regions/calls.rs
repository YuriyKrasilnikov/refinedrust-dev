// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Provides functionality for generating lifetime annotations for calls.

use std::collections::{BTreeMap, BTreeSet};

use derive_more::Debug;
use log::info;
use radium::{code, coq};
use rr_rustc_interface::middle::ty::TypeFolder as _;
use rr_rustc_interface::middle::{mir, ty};

use crate::base::*;
use crate::environment::borrowck::facts;
use crate::environment::polonius_info;
use crate::environment::region_folder::*;
use crate::regions::inclusion_tracker::InclusionTracker;
use crate::types;

// solve the constraints for the new_regions
// we first identify what kinds of constraints these new regions are subject to
#[derive(Debug)]
pub(crate) enum CallRegionKind {
    // this is just an intersection of local regions.
    Intersection(BTreeSet<Region>),
    // this is equal to a specific region
    EqR(Region),
}

pub(crate) struct CallRegions {
    pub early_regions: Vec<Region>,
    pub late_regions: Vec<Region>,
    pub classification: BTreeMap<Region, CallRegionKind>,
}

/// Compute instantiations for the lifetime parameters of a function.
/// Each of the lifetimes in the function's signature has one Polonius inference variable at the
/// call site, and we need to find an instantiation for these.
/// `substs` are the substitutions for the early-bound regions
pub(crate) fn compute_call_regions<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    incl_tracker: &InclusionTracker<'_, '_>,
    substs: &[ty::GenericArg<'tcx>],
    loc: mir::Location,
    num_expected_late_bounds: usize,
) -> CallRegions {
    let info = incl_tracker.info();

    let midpoint = info.interner.get_point_index(&facts::Point {
        location: loc,
        typ: facts::PointType::Mid,
    });

    let mut early_regions = Vec::new();
    for a in substs {
        if let ty::GenericArgKind::Lifetime(r) = a.kind()
            && let ty::RegionKind::ReVar(r) = r.kind()
        {
            early_regions.push(r.into());
        }
    }
    info!("call args: {substs:?}");
    info!("call region instantiations (early): {:?}", early_regions);

    // this is a hack to identify the inference variables introduced for the
    // call's late-bound universals.
    // TODO: Can we get this information in a less hacky way?
    // One approach: compute the early + late bound regions for a given DefId, similarly to how
    // we do it when starting to translate a function
    // Problem: this doesn't give a straightforward way to compute their instantiation

    // now find all the regions that appear in type parameters we instantiate.
    // These are regions that the callee doesn't know about.
    let mut generic_regions: BTreeSet<facts::Region> = BTreeSet::new();
    let mut clos = |r: ty::Region<'tcx>, _| match r.kind() {
        ty::RegionKind::ReVar(rv) => {
            generic_regions.insert(rv.into());
            r
        },
        _ => r,
    };

    for a in substs {
        if let ty::GenericArgKind::Type(c) = a.kind() {
            let mut folder = RegionFolder::new(tcx, &mut clos);
            folder.fold_ty(c);
        }
    }
    info!("Regions of generic args: {:?}", generic_regions);

    // go over all region constraints initiated at this location
    let new_constraints = info.get_new_subset_constraints_at_point(midpoint);
    let mut new_regions = BTreeSet::new();
    let mut relevant_constraints = Vec::new();
    for (r1, r2) in &new_constraints {
        if matches!(info.get_region_kind(*r1), polonius_info::RegionKind::Unknown(_)) {
            // this is probably a inference variable for the call
            new_regions.insert(*r1);
            relevant_constraints.push((*r1, *r2));
        }
        if matches!(info.get_region_kind(*r2), polonius_info::RegionKind::Unknown(_)) {
            new_regions.insert(*r2);
            relevant_constraints.push((*r1, *r2));
        }
    }
    // first sort this to enable cycle resolution
    let mut new_regions_sorted: Vec<Region> = new_regions.iter().copied().collect();
    new_regions_sorted.sort();
    info!("new regions: {new_regions_sorted:?}");
    info!("relevant constraints: {relevant_constraints:?}");

    // identify the late-bound regions
    let mut late_regions = Vec::new();
    for r in &new_regions_sorted {
        // only take the ones which are not early bound and
        // which are not due to a generic (the callee doesn't care about generic regions)
        if !early_regions.contains(r) && !generic_regions.contains(r) {
            late_regions.push(*r);
        }
    }
    info!("computed late regions: {:?}, expected: {num_expected_late_bounds:?}", late_regions.len());

    // Heuristic: if we have too many late bounds here, try to filter spurious extra late bounds.
    // If a late bound is equal to an early bound, it is likely to be spurious.
    // Ideally, we'd have a more reliable way of computing an instantiation for late-bounds.
    if late_regions.len() > num_expected_late_bounds {
        late_regions.retain(|x| {
            !early_regions
                .iter()
                .any(|y| relevant_constraints.contains(&(*x, *y)) && relevant_constraints.contains(&(*y, *x)))
        });
    }
    info!("call region instantiations (late): {:?}", late_regions);

    // Notes:
    // - if two of the call regions need to be equal due to constraints on the function, we define the one
    //   with the larger id in terms of the other one
    // - we ignore unidirectional subset constraints between call regions (these do not help in finding a
    //   solution if we take the transitive closure beforehand)
    // - if a call region needs to be equal to a local region, we directly define it in terms of the local
    //   region
    // - otherwise, it will be an intersection of local regions
    let mut new_regions_classification = BTreeMap::new();
    // compute transitive closure of constraints
    let relevant_constraints = polonius_info::compute_transitive_closure(relevant_constraints);
    for r in &new_regions_sorted {
        for (r1, r2) in &relevant_constraints {
            if *r2 != *r {
                continue;
            }
            // reflexive constraints do not help us, of course.
            if *r1 == *r2 {
                continue;
            }
            // r1 should be known or a new region
            if !incl_tracker.is_region_known(*r1, midpoint) && !new_regions.contains(r1) {
                // this is a constraint that won't help us
                continue;
            }

            // i.e. (flipping it around when we are talking about lifetimes),
            // r needs to be a sublft of r1
            if relevant_constraints.contains(&(*r2, *r1)) {
                // if r1 is also a new region and r2 is ordered before it, we will
                // just define r1 in terms of r2
                if new_regions.contains(r1) && r2.as_u32() < r1.as_u32() {
                    continue;
                }
                // need an equality constraint
                new_regions_classification.insert(*r2, CallRegionKind::EqR(*r1));
                // do not consider the rest of the constraints as r is already
                // fully specified
                break;
            }

            // the intersection also needs to contain r1
            if new_regions.contains(r1) {
                // we do not need this constraint, since we already computed the
                // transitive closure.
                continue;
            }

            let kind = new_regions_classification
                .entry(*r)
                .or_insert(CallRegionKind::Intersection(BTreeSet::new()));

            let CallRegionKind::Intersection(s) = kind else {
                unreachable!();
            };

            s.insert(*r1);
        }
    }
    info!("call arg classification: {:?}", new_regions_classification);

    CallRegions {
        early_regions,
        late_regions,
        classification: new_regions_classification,
    }
}

/// Compute annotations for recovering unconstrained regions that we have recovered by analyzing
/// the function's signature.\
/// Returns:
/// - the vector of annotations to emit
/// - the set of remaining unconstrained regions for which we have not figured out a mapping
pub(crate) fn compute_unconstrained_region_annots<'tcx>(
    inclusion_tracker: &mut InclusionTracker<'_, 'tcx>,
    ty_translator: &types::LocalTX<'_, 'tcx>,
    loc: mir::Location,
    unconstrained_regions: BTreeSet<facts::Region>,
    early_region_map: &BTreeMap<coq::Ident, usize>,
) -> Result<(Vec<code::Annotation>, BTreeSet<facts::Region>), TranslationError<'tcx>> {
    let info = inclusion_tracker.info();
    let midpoint = info.interner.get_point_index(&facts::Point {
        location: loc,
        typ: facts::PointType::Mid,
    });

    let mut remaining_regions = BTreeSet::new();

    let mut unconstrained_annotations = Vec::new();
    for r in unconstrained_regions {
        let translated_region = ty_translator.translate_region_var(r)?;
        // check if we have recovered a mapping
        if let Some(early_region_idx) = early_region_map.get(&translated_region) {
            let scope = ty_translator.scope.borrow();

            let early_lft_vid = scope.lifetime_scope.early_regions[*early_region_idx].unwrap();
            let early_lft_name = &scope.lifetime_scope.region_names[&early_lft_vid];
            unconstrained_annotations
                .push(code::Annotation::CopyLftName(early_lft_name.lft().to_owned(), translated_region));

            inclusion_tracker.add_static_inclusion(r, early_lft_vid, midpoint);
            inclusion_tracker.add_static_inclusion(early_lft_vid, r, midpoint);
        } else {
            remaining_regions.insert(r);
        }
    }
    Ok((unconstrained_annotations, remaining_regions))
}
