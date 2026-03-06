// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Provides functionality for generating initial lifetime constraints.

use std::collections::{BTreeMap, HashMap};

use log::{info, trace};
use radium::{coq, specs};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};

use crate::base::*;
use crate::environment::borrowck::facts;
use crate::environment::polonius_info::PoloniusInfo;
use crate::environment::{Environment, polonius_info};
use crate::regions::arg_folder::instantiate_open;
use crate::regions::inclusion_tracker::InclusionTracker;
use crate::regions::region_bi_folder::RegionBiFolder;
use crate::regions::{EarlyLateRegionMap, LftConstr};
use crate::traits::resolution;
use crate::types::scope;

/// Process the signature of a function by instantiating the region variables with their
/// Polonius variables.
/// Returns the argument and return type signature instantiated in this way.
/// Moreover, returns a `EarlyLateRegionMap` that contains the mapping of indices to Polonius
/// region variables.
pub(crate) fn replace_fnsig_args_with_polonius_vars<'def, 'tcx>(
    env: &Environment<'tcx>,
    params: &[ty::GenericArg<'tcx>],
    of_did: DefId,
    num_universal_regions: usize,
    num_early_bounds: usize,
    num_late_bounds: usize,
    sig: ty::Binder<'tcx, ty::FnSig<'tcx>>,
) -> (Vec<ty::Ty<'tcx>>, ty::Ty<'tcx>, EarlyLateRegionMap<'def>) {
    trace!(
        "enter replace_fnsig_args_with_polonius_vars for {of_did:?}, num_universal_regions={num_universal_regions:?}, num_early_bounds={num_early_bounds:?}, num_late_bounds={num_late_bounds:?}"
    );

    // a mapping of Polonius region IDs to names
    let mut universal_lifetimes = BTreeMap::new();
    let mut lifetime_names = HashMap::new();

    let mut region_substitution_early: Vec<Option<facts::Region>> = Vec::new();

    // We have to enumerate universal region variables in the same way that the borrow checker does,
    // as implemented in `compiler/rustc_borrowck/src/universal_regions.rs`.
    // There, universal regions are divided into three successive groups:
    // - global regions, starting at index 0: only 'static
    // - external regions (in case of closures/coroutines), containing regions from the surrounding scopes
    //   (i.e. a surrounding function's late bounds, and the regions of the captures)
    // - local regions, containing local early/late regions The last local region always seems to be the local
    //   function lifetime.
    // Note: We handle external regions separately from this function just for closures.
    let first_late_bound = num_universal_regions - 1 - num_late_bounds;
    let first_early_bound = first_late_bound - num_early_bounds;

    // we create a substitution that replaces early bound regions with their Polonius
    // region variables
    let mut subst_early_bounds: Vec<ty::GenericArg<'tcx>> = Vec::new();
    let mut early_count = 0;
    for a in params {
        if let ty::GenericArgKind::Lifetime(r) = a.kind() {
            let next_id = facts::Region::from_usize(first_early_bound + early_count);
            let revar = ty::Region::new_var(env.tcx(), next_id.into());
            subst_early_bounds.push(ty::GenericArg::from(revar));

            region_substitution_early.push(Some(next_id));

            match r.kind() {
                ty::RegionKind::ReEarlyParam(r) => {
                    let mut name = strip_coq_ident(r.name.as_str());
                    let origin = scope::determine_origin_of_lft_param(of_did, env.tcx(), r);

                    if name == "_" {
                        name = format!("{}", next_id.index());
                    }
                    universal_lifetimes.insert(
                        next_id,
                        specs::LftParam::new(coq::Ident::new(&format!("ulft_{}", name)), origin),
                    );
                    lifetime_names.insert(name, next_id);
                },
                _ => {
                    unimplemented!("didn't expect a region of kind {:?}", r);
                },
            }
            early_count += 1;
        } else {
            subst_early_bounds.push(*a);
            region_substitution_early.push(None);
        }
    }
    let subst_early_bounds = env.tcx().mk_args(&subst_early_bounds);

    trace!("Computed early region map {region_substitution_early:?}");

    // add names for late bound region variables
    let mut late_count = 0;
    let mut region_substitution_late = Vec::new();
    for b in sig.bound_vars() {
        let next_id = facts::Region::from_usize(first_late_bound + late_count);

        let ty::BoundVariableKind::Region(r) = b else {
            continue;
        };

        region_substitution_late.push(next_id);

        match r {
            ty::BoundRegionKind::Named(did) => {
                if let Some(name) = env.tcx().opt_item_name(did) {
                    let mut region_name = strip_coq_ident(name.as_str());
                    if region_name == "_" {
                        region_name = next_id.as_usize().to_string();
                    } else {
                        lifetime_names.insert(region_name.clone(), next_id);
                    }
                    universal_lifetimes.insert(
                        next_id,
                        specs::LftParam::new(
                            coq::Ident::new(&format!("ulft_{}", region_name)),
                            specs::LftParamOrigin::LocalLateBound,
                        ),
                    );
                }
            },
            ty::BoundRegionKind::NamedForPrinting(name) => {
                let mut region_name = strip_coq_ident(name.as_str());
                if region_name == "_" {
                    region_name = next_id.as_usize().to_string();
                } else {
                    lifetime_names.insert(region_name.clone(), next_id);
                }
                universal_lifetimes.insert(
                    next_id,
                    specs::LftParam::new(
                        coq::Ident::new(&format!("ulft_{}", region_name)),
                        specs::LftParamOrigin::LocalLateBound,
                    ),
                );
            },
            ty::BoundRegionKind::Anon => {
                universal_lifetimes.insert(
                    next_id,
                    specs::LftParam::new(
                        coq::Ident::new(&format!("ulft_{}", next_id.as_usize())),
                        specs::LftParamOrigin::LocalLateBound,
                    ),
                );
            },
            _ => (),
        }

        late_count += 1;
    }

    // replace late-bound region variables by re-enumerating them in the same way as the MIR
    // type checker does (that this happens in the same way is important to make the names
    // line up!)
    let mut next_index = first_late_bound;
    let mut folder = |_| {
        let cur_index = next_index;
        next_index += 1;
        ty::Region::new_var(env.tcx(), ty::RegionVid::from_usize(cur_index))
    };
    let (late_sig, _late_region_map) = env.tcx().instantiate_bound_regions(sig, &mut folder);

    // replace early bound variables
    let inputs: Vec<_> = late_sig
        .inputs()
        .iter()
        .map(|ty| instantiate_open(*ty, env.tcx(), subst_early_bounds))
        .collect();

    let output = instantiate_open(late_sig.output(), env.tcx(), subst_early_bounds);

    trace!("Computed late region map {region_substitution_late:?}");

    let region_map = EarlyLateRegionMap::new(
        region_substitution_early,
        vec![region_substitution_late],
        vec![],
        vec![],
        universal_lifetimes,
        lifetime_names,
    );

    trace!("leave replace_fnsig_args_with_polonius_vars for {of_did:?}");

    (inputs, output, region_map)
}

/// At the start of the function, there's a universal (placeholder) region for reference argument.
/// These get subsequently relabeled by Polonius.
/// Given the relabeled region, find the original placeholder region.
pub(crate) fn find_placeholder_region_for(
    r: facts::Region,
    info: &PoloniusInfo<'_, '_>,
) -> Option<facts::Region> {
    let root_location = mir::Location {
        block: mir::BasicBlock::from_usize(0),
        statement_index: 0,
    };
    let root_point = info.interner.get_point_index(&facts::Point {
        location: root_location,
        typ: facts::PointType::Start,
    });

    for (r1, r2, p) in &info.borrowck_in_facts.subset_base {
        let k1 = info.get_region_kind(*r1);
        if *p == root_point && *r2 == r && matches!(k1, polonius_info::RegionKind::Universal(_)) {
            info!("find placeholder region for: {:?} ⊑ {:?} = r", r1, r2);
            return Some(*r1);
        }
    }
    None
}

/// Insert the initial universal constraints into the tracker.
pub(crate) fn initialize_inclusion_tracker<'a, 'tcx>(
    lifetime_scope: &EarlyLateRegionMap<'_>,
    info: &'a PoloniusInfo<'a, 'tcx>,
) -> InclusionTracker<'a, 'tcx> {
    let mut inclusion_tracker = InclusionTracker::new(info);

    let root_location = mir::Location {
        block: mir::BasicBlock::from_usize(0),
        statement_index: 0,
    };
    let root_point = info.interner.get_point_index(&facts::Point {
        location: root_location,
        typ: facts::PointType::Start,
    });
    for cstr in &lifetime_scope.constraints {
        match cstr {
            LftConstr::RegionOutlives(r1, r2) => {
                inclusion_tracker.add_static_inclusion(*r1, *r2, root_point);
            },
            LftConstr::TypeOutlives(_, _) => (),
        }
    }

    for (r1, r2) in &info.borrowck_in_facts.known_placeholder_subset {
        inclusion_tracker.add_static_inclusion(*r1, *r2, root_point);
    }

    inclusion_tracker
}

/// Get additional constraints between capture places and value lifetimes that hold at the
/// beginning of the closure.
pub(crate) fn get_initial_closure_constraints<'a>(
    info: &'a PoloniusInfo<'a, '_>,
    inclusion_tracker: &mut InclusionTracker<'a, '_>,
) -> Vec<(polonius_info::AtomicRegion, polonius_info::AtomicRegion)> {
    let input_facts = &info.borrowck_in_facts;

    let root_location = mir::Location {
        block: mir::BasicBlock::from_usize(0),
        statement_index: 0,
    };
    let root_point = info.interner.get_point_index(&facts::Point {
        location: root_location,
        typ: facts::PointType::Mid,
    });

    let mut closure_constraints = Vec::new();

    for (r1, r2, p) in &input_facts.subset_base {
        if *p == root_point && input_facts.subset_base.contains(&(*r2, *r1, *p)) {
            let lft1 = info.mk_atomic_region(*r1);
            let lft2 = info.mk_atomic_region(*r2);

            if lft1.is_place() && lft2.is_value() {
                inclusion_tracker.add_static_inclusion(*r1, *r2, root_point);
                inclusion_tracker.add_static_inclusion(*r2, *r1, root_point);

                closure_constraints.push((lft1, lft2));
            }
        }
    }
    closure_constraints
}

/// Determine initial constraints between universal regions and local place regions.
/// Returns an initial mapping for the name map that initializes place regions of arguments
/// with universals.
/// We structurally compare the regions in the function signature args `sig_args` with the regions
/// in the body's `local_args`.
pub(crate) fn get_initial_universal_arg_constraints<'a, 'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    info: &'a PoloniusInfo<'a, 'tcx>,
    inclusion_tracker: &mut InclusionTracker<'a, 'tcx>,
    sig_args: &[ty::Ty<'tcx>],
    local_args: &[ty::Ty<'tcx>],
) -> Vec<(polonius_info::AtomicRegion, polonius_info::AtomicRegion)> {
    info!("computing initial universal constraints for {sig_args:?} and {local_args:?}");

    // Polonius generates a base subset constraint uregion ⊑ pregion.
    // We turn that into pregion = uregion, as we do strong updates at the top-level.
    assert!(sig_args.len() == local_args.len());

    // compute the mapping
    let mut unifier = InitialPoloniusUnifier::new(tcx, typing_env);
    for (a1, a2) in local_args.iter().zip(sig_args.iter()) {
        let a1_normalized = resolution::normalize_type(tcx, typing_env, *a1).unwrap();
        let a2_normalized = resolution::normalize_type(tcx, typing_env, *a2).unwrap();
        unifier.map_tys(a1_normalized, a2_normalized);
    }

    // add the inclusions to the inclusion tracker

    let root_location = mir::Location {
        block: mir::BasicBlock::from_usize(0),
        statement_index: 0,
    };
    let root_point = info.interner.get_point_index(&facts::Point {
        location: root_location,
        typ: facts::PointType::Start,
    });

    let mut initial_arg_mapping = Vec::new();
    for (l, s) in unifier.get_result() {
        if l == s {
            continue;
        }
        inclusion_tracker.add_static_inclusion(s, l, root_point);
        inclusion_tracker.add_static_inclusion(l, s, root_point);

        let lft1 = info.mk_atomic_region(l);
        let lft2 = info.mk_atomic_region(s);
        initial_arg_mapping.push((lft2, lft1));
    }

    initial_arg_mapping
}

pub(crate) struct InitialPoloniusUnifier<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    mapping: BTreeMap<Region, Region>,
}
impl<'tcx> InitialPoloniusUnifier<'tcx> {
    pub(crate) const fn new(tcx: ty::TyCtxt<'tcx>, typing_env: ty::TypingEnv<'tcx>) -> Self {
        Self {
            tcx,
            typing_env,
            mapping: BTreeMap::new(),
        }
    }

    pub(crate) fn get_result(self) -> BTreeMap<Region, Region> {
        self.mapping
    }
}
impl<'tcx> RegionBiFolder<'tcx> for InitialPoloniusUnifier<'tcx> {
    fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn typing_env(&self) -> &ty::TypingEnv<'tcx> {
        &self.typing_env
    }

    fn map_regions(&mut self, r1: ty::Region<'tcx>, r2: ty::Region<'tcx>) {
        if let ty::RegionKind::ReVar(l1) = r1.kind()
            && let ty::RegionKind::ReVar(l2) = r2.kind()
        {
            if let Some(l22) = self.mapping.get(&l1.into()) {
                assert_eq!(l2, (*l22).into());
            } else {
                self.mapping.insert(l1.into(), l2.into());
            }
        }
    }
}
