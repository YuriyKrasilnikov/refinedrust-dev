// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashMap;

use derive_more::Display;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;

use crate::{environment, rustcmp, search};

pub(crate) mod registry;
pub(crate) mod requirements;
pub(crate) mod resolution;

#[derive(Debug, Clone, Display, Eq, PartialEq)]
pub(crate) enum Error<'tcx> {
    /// This `DefId` is not a trait
    #[display("The given `DefId` {:?} is not a trait", _0)]
    NotATrait(DefId),

    /// This `DefId` is not an impl of a trait
    #[display("The given `DefId` {:?} is not a trait implementation", _0)]
    NotATraitImpl(DefId),

    /// This closure does not implement the closure trait
    #[display("Did not find trait impl of {:?} for closure {:?}", _1, _0)]
    NotAClosureTraitImpl(DefId, ty::ClosureKind),

    /// This `DefId` does not represent a closure trait, when it was expected to.
    #[display("This DefId does not represent a closure trait {:?}", _0)]
    NotAClosureTrait(DefId),

    /// The trait for this closure kind could not be found
    #[display("Could not find the trait for closure kind {:?}", _0)]
    CouldNotFindClosureTrait(ty::ClosureKind),

    /// This `DefId` is not a trait method
    #[display("The given `DefId` {:?} is not a trait method", _0)]
    NotATraitMethod(DefId),

    /// This `DefId` is not an assoc type
    #[display("The given `DefId` {:?} is not an associated type", _0)]
    NotAnAssocType(DefId),

    /// We encountered an associated constant
    #[display("Associated constants are not supported")]
    AssocConstNotSupported,

    /// This trait already exists
    #[display("This trait {:?} already has been registered", _0)]
    TraitAlreadyExists(DefId),

    /// This trait impl already exists
    #[display("This trait impl {:?} already has been registered", _0)]
    ImplAlreadyExists(DefId),

    /// This closure trait impl already exists
    #[display("This closure ({:?}, {:?}) already has been registered", _0, _1)]
    ClosureImplAlreadyExists(DefId, ty::ClosureKind),

    /// Trait hasn't been registered yet but is used
    #[display("This trait {:?} has not been registered yet", _0)]
    UnregisteredTrait(DefId),

    /// Trait impl hasn't been registered yet but is used
    #[display("This trait impl {:?} of {:?} has not been registered yet", _0, _1)]
    UnregisteredImpl(DefId, DefId),

    /// Cannot find this trait instance in the local environment
    #[display("An instance for this trait {:?} cannot by found with generic args {:?}", _0, _1)]
    UnknownLocalInstance(DefId, ty::GenericArgsRef<'tcx>),

    #[display("An error occurred when parsing the specification of the trait {:?}: {:?}", _0, _1)]
    TraitSpec(DefId, String),

    #[display("An error occurred when parsing the specification of the trait impl {:?}: {:?}", _0, _1)]
    TraitImplSpec(DefId, String),
}

pub(crate) type TraitResult<'tcx, T> = Result<T, Error<'tcx>>;

/// Given a particular reference to a trait, get the associated type constraints for this trait reference.
pub(crate) fn get_trait_assoc_constraints<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    trait_ref: ty::TraitRef<'tcx>,
) -> Vec<Option<ty::Ty<'tcx>>> {
    let mut assoc_ty_map = HashMap::new();

    // TODO: check if caller_bounds does the right thing for implied bounds
    let clauses = typing_env.param_env.caller_bounds();
    for cl in clauses {
        let cl_kind = cl.kind();
        let cl_kind = cl_kind.skip_binder();

        // only look for trait predicates for now
        if let ty::ClauseKind::Projection(proj) = cl_kind
            && trait_ref.def_id == proj.trait_def_id(tcx)
            && trait_ref.args == proj.projection_term.args
        {
            // same trait and same args
            let idx = environment::get_trait_associated_type_index(tcx, proj.def_id()).unwrap();
            let ty = proj.term.as_type().unwrap();
            assoc_ty_map.insert(idx, ty);
        }
    }

    let assoc_tys = environment::get_trait_assoc_types(tcx, trait_ref.def_id);
    assoc_tys
        .into_iter()
        .enumerate()
        .map(|(idx, _)| assoc_ty_map.get(&idx).copied())
        .collect()
}

/// Sort associated items of a trait in a stable way.
pub(crate) fn sort_assoc_items<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    items: &'tcx ty::AssocItems,
) -> Vec<&'tcx ty::AssocItem> {
    let mut items: Vec<_> = items.in_definition_order().collect();
    items.sort_by(|a, b| rustcmp::cmp_defid(tcx, a.def_id, b.def_id));

    items
}

/// Check if this is a derive trait that does not need spec annotations to implement.
pub(crate) fn is_derive_trait_with_no_annotations(tcx: ty::TyCtxt<'_>, trait_did: DefId) -> Option<bool> {
    let copy_did = search::try_resolve_did(tcx, &["core", "marker", "Copy"])?;
    let clone_did = search::try_resolve_did(tcx, &["core", "clone", "Clone"])?;
    let debug_did = search::try_resolve_did(tcx, &["core", "fmt", "Debug"])?;

    Some(trait_did == copy_did || trait_did == clone_did || trait_did == debug_did)
}

/// Check if this is a derive trait that needs spec annotations to implement.
pub(crate) fn is_derive_trait_with_annotations(tcx: ty::TyCtxt<'_>, trait_did: DefId) -> Option<bool> {
    let eq_did = search::try_resolve_did(tcx, &["core", "cmp", "Eq"])?;
    let partial_eq_did = search::try_resolve_did(tcx, &["core", "cmp", "PartialEq"])?;
    let ord_did = search::try_resolve_did(tcx, &["core", "cmp", "Ord"])?;
    let partial_ord_did = search::try_resolve_did(tcx, &["core", "cmp", "PartialOrd"])?;

    Some(
        trait_did == eq_did
            || trait_did == partial_eq_did
            || trait_did == ord_did
            || trait_did == partial_ord_did,
    )
}
