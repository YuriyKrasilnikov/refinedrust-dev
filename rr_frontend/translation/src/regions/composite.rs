// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Provides functionality for generating lifetime annotations for composite expressions.

use std::collections::HashSet;

use radium::code;
use rr_rustc_interface::middle::ty::TypeFolder as _;
use rr_rustc_interface::middle::{mir, ty};

use crate::environment::borrowck::facts;
use crate::environment::region_folder::*;
use crate::regions::inclusion_tracker::InclusionTracker;
use crate::types;

/// On creating a composite value (e.g. a struct or enum), the composite value gets its own
/// Polonius regions We need to map these regions properly to the respective lifetimes.
pub(crate) fn get_composite_rvalue_creation_annots<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    inclusion_tracker: &mut InclusionTracker<'_, 'tcx>,
    ty_translator: &types::LocalTX<'_, 'tcx>,
    loc: mir::Location,
    rhs_ty: ty::Ty<'tcx>,
) -> Vec<code::Annotation> {
    let info = inclusion_tracker.info();
    let input_facts = &info.borrowck_in_facts;
    let subset_base = &input_facts.subset_base;

    let regions_of_ty = get_regions_of_ty(tcx, rhs_ty);

    let mut annots = Vec::new();

    // Polonius subset constraint are spawned for the midpoint
    let midpoint = info.interner.get_point_index(&facts::Point {
        location: loc,
        typ: facts::PointType::Mid,
    });

    for (s1, s2, point) in subset_base {
        if *point == midpoint {
            let lft1 = info.mk_atomic_region(*s1);
            let lft2 = info.mk_atomic_region(*s2);

            // a place lifetime is included in a value lifetime
            if lft2.is_value() && lft1.is_place() {
                // make sure it's not due to an assignment constraint
                if regions_of_ty.contains(s2) && !subset_base.contains(&(*s2, *s1, midpoint)) {
                    // we enforce this inclusion by setting the lifetimes to be equal
                    inclusion_tracker.add_static_inclusion(*s1, *s2, midpoint);
                    inclusion_tracker.add_static_inclusion(*s2, *s1, midpoint);

                    let annot = code::Annotation::CopyLftName(
                        ty_translator.format_atomic_region(lft1),
                        ty_translator.format_atomic_region(lft2),
                    );
                    annots.push(annot);
                }
            }
        }
    }
    annots
}

/// Get the regions appearing in a type.
fn get_regions_of_ty<'tcx>(tcx: ty::TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> HashSet<facts::Region> {
    let mut regions = HashSet::new();
    let mut clos = |r: ty::Region<'tcx>, _| match r.kind() {
        ty::RegionKind::ReVar(rv) => {
            regions.insert(rv.into());
            r
        },
        _ => r,
    };
    let mut folder = RegionFolder::new(tcx, &mut clos);
    folder.fold_ty(ty);
    regions
}
