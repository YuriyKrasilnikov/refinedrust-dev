// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

//! This module defines the interface provided to a verifier.
pub(crate) mod borrowck;
mod collect_closure_defs_visitor;
mod collect_prusti_spec_visitor;
mod dump_borrowck_info;
mod loops;
pub(crate) mod mir_analyses;
pub(crate) mod mir_sets;
pub(crate) mod mir_storage;
pub(crate) mod mir_utils;
pub(crate) mod polonius_info;
pub(crate) mod procedure;
pub(crate) mod region_folder;

use rr_rustc_interface::hir;
use rr_rustc_interface::hir::def_id::{DefId, LocalDefId};
use rr_rustc_interface::middle::{mir, ty};

use crate::environment::collect_closure_defs_visitor::CollectClosureDefsVisitor;
use crate::environment::collect_prusti_spec_visitor::CollectPrustiSpecVisitor;
use crate::environment::procedure::Procedure;
use crate::{attrs, traits};

pub(crate) fn get_closure_self_ty_from_var_ty<'tcx>(
    var_ty: ty::Ty<'tcx>,
    kind: ty::ClosureKind,
) -> ty::Ty<'tcx> {
    match kind {
        ty::ClosureKind::Fn => {
            if let ty::TyKind::Ref(_, ty, _) = var_ty.kind() {
                *ty
            } else {
                unreachable!();
            }
        },
        ty::ClosureKind::FnMut => {
            if let ty::TyKind::Ref(_, ty, _) = var_ty.kind() {
                *ty
            } else {
                unreachable!("unexpected type {:?}", var_ty);
            }
        },
        ty::ClosureKind::FnOnce => var_ty,
    }
}

/// Get the meta info for a closure, with the Polonius regions.
pub(crate) fn get_closure_args<'tcx>(tcx: ty::TyCtxt<'tcx>, did: DefId) -> ty::ClosureArgs<ty::TyCtxt<'tcx>> {
    let closure_kind = match tcx.type_of(did).instantiate_identity().kind() {
        ty::TyKind::Closure(_def, closure_args) => closure_args.as_closure().kind(),
        _ => panic!("can not handle non-closures"),
    };

    // Now, we get the type of the closure local in the MIR, in order to get the Polonius regions.
    let proc = get_procedure(tcx, did);
    let body = proc.get_mir();
    let local_decls = &body.local_decls;
    let closure_arg = local_decls.get(mir::Local::from_usize(1)).unwrap();
    let closure_ty = get_closure_self_ty_from_var_ty(closure_arg.ty, closure_kind);

    let ty::TyKind::Closure(_, closure_args) = closure_ty.kind() else {
        unreachable!();
    };

    closure_args.as_closure()
}

/// Get ids of Rust procedures.
pub(crate) fn get_procedures(tcx: ty::TyCtxt<'_>) -> Vec<LocalDefId> {
    let mut visitor = CollectPrustiSpecVisitor::new(tcx);
    visitor.run();
    // TODO: cache results
    let (functions, _, _, _, _) = visitor.get_results();
    functions
}

/// Get ids of Rust statics.
pub(crate) fn get_statics(tcx: ty::TyCtxt<'_>) -> Vec<LocalDefId> {
    let mut visitor = CollectPrustiSpecVisitor::new(tcx);
    visitor.run();
    // TODO: cache results
    let (_, _, statics, _, _) = visitor.get_results();
    statics
}

/// Get ids of Rust modules.
pub(crate) fn get_modules(tcx: ty::TyCtxt<'_>) -> Vec<LocalDefId> {
    let mut visitor = CollectPrustiSpecVisitor::new(tcx);
    visitor.run();
    // TODO: cache results
    let (_, modules, _, _, _) = visitor.get_results();
    modules
}

/// Get ids of trait declarations.
pub(crate) fn get_traits(tcx: ty::TyCtxt<'_>) -> Vec<LocalDefId> {
    let mut visitor = CollectPrustiSpecVisitor::new(tcx);
    visitor.run();
    // TODO: cache results
    let (_, _, _, _, traits) = visitor.get_results();
    traits
}

/// Get ids of trait impls.
pub(crate) fn get_trait_impls(tcx: ty::TyCtxt<'_>) -> Vec<LocalDefId> {
    let mut visitor = CollectPrustiSpecVisitor::new(tcx);
    // TODO cache results
    visitor.run();
    visitor.get_trait_impls()
}

/// Get ids of Rust closures.
pub(crate) fn get_closures(tcx: ty::TyCtxt<'_>) -> Vec<LocalDefId> {
    let mut cl_visitor = CollectClosureDefsVisitor::new(tcx);
    tcx.hir_visit_all_item_likes_in_crate(&mut cl_visitor);
    cl_visitor.get_closure_defs()
}

/// Find whether the procedure has a particular `[tool]::<name>` attribute.
pub(crate) fn has_tool_attribute(tcx: ty::TyCtxt<'_>, def_id: DefId, name: &str) -> bool {
    #[expect(deprecated)]
    attrs::has_tool_attr(tcx.get_all_attrs(def_id), name)
}

/// Find whether the procedure has a particular `[tool]::<name>` attribute; if so, return its
/// name.
pub(crate) fn get_tool_attribute<'a>(
    tcx: ty::TyCtxt<'a>,
    def_id: DefId,
    name: &str,
) -> Option<&'a hir::AttrArgs> {
    #[expect(deprecated)]
    attrs::get_tool_attr(tcx.get_all_attrs(def_id), name)
}

/// Check whether the procedure has any `[tool]` attribute.
pub(crate) fn has_any_tool_attribute(tcx: ty::TyCtxt<'_>, def_id: DefId) -> bool {
    #[expect(deprecated)]
    attrs::has_any_tool_attr(tcx.get_all_attrs(def_id))
}

/// Get the attributes of an item (e.g. procedures).
pub(crate) fn get_attributes(tcx: ty::TyCtxt<'_>, def_id: DefId) -> &[hir::Attribute] {
    #[expect(deprecated)]
    tcx.get_all_attrs(def_id)
}

/// Get tool attributes of this function, including selected attributes from the surrounding impl.
pub(crate) fn get_attributes_of_function<'tcx, F>(
    tcx: ty::TyCtxt<'tcx>,
    did: DefId,
    propagate_from_impl: &F,
) -> Vec<&'tcx hir::AttrItem>
where
    F: for<'a> Fn(&'a hir::AttrItem) -> bool,
{
    let attrs = get_attributes(tcx, did);
    let mut filtered_attrs = attrs::filter_for_tool(attrs);
    // also add selected attributes from the surrounding impl
    if let Some(impl_did) = tcx.impl_of_assoc(did) {
        let impl_attrs = get_attributes(tcx, impl_did);
        let filtered_impl_attrs = attrs::filter_for_tool(impl_attrs);
        filtered_attrs.extend(filtered_impl_attrs.into_iter().filter(|x| propagate_from_impl(x)));
    }

    // for closures, propagate from the surrounding function
    if is_closure(tcx, did) {
        let parent_did = tcx.parent(did);
        let parent_attrs = get_attributes_of_function(tcx, parent_did, propagate_from_impl);
        filtered_attrs.extend(parent_attrs.into_iter().filter(|x| propagate_from_impl(x)));
    }

    filtered_attrs
}

/// Check if `did` is a closure.
pub(crate) fn is_closure(tcx: ty::TyCtxt<'_>, did: DefId) -> bool {
    let ty = tcx.type_of(did).skip_binder();
    matches!(ty.kind(), ty::TyKind::Closure(_, _))
}

/// Get an absolute `def_path`. Note: not preserved across compilations!
pub(crate) fn get_item_def_path(tcx: ty::TyCtxt<'_>, def_id: DefId) -> String {
    let def_path = tcx.def_path(def_id);
    let mut crate_name = tcx.crate_name(def_path.krate).to_string();
    crate_name.push_str(&def_path.to_string_no_crate_verbose());
    crate_name
}

pub(crate) fn get_absolute_item_name(tcx: ty::TyCtxt<'_>, def_id: DefId) -> String {
    tcx.def_path_str(def_id)
}

pub(crate) fn get_item_name(tcx: ty::TyCtxt<'_>, def_id: DefId) -> String {
    tcx.def_path_str(def_id)
    // tcx.item_path_str(def_id)
}

/// Get the name of an item without the path prefix.
pub(crate) fn get_assoc_item_name(tcx: ty::TyCtxt<'_>, trait_method_did: DefId) -> Option<String> {
    let def_path = tcx.def_path(trait_method_did);
    if let Some(last_elem) = def_path.data.last()
        && let Some(name) = last_elem.data.get_opt_name()
    {
        return Some(name.as_str().to_owned());
    }
    None
}

/// Get the associated types of a trait.
pub(crate) fn get_trait_assoc_types(tcx: ty::TyCtxt<'_>, trait_did: DefId) -> Vec<DefId> {
    let assoc_items: &ty::AssocItems = tcx.associated_items(trait_did);
    let items = traits::sort_assoc_items(tcx, assoc_items);

    let mut assoc_tys = Vec::new();
    for c in items {
        if ty::AssocTag::Type == c.tag() {
            assoc_tys.push(c.def_id);
        }
    }
    assoc_tys
}

/// Get the index in the sorted list of associated types.
pub(crate) fn get_trait_associated_type_index(tcx: ty::TyCtxt<'_>, assoc_did: DefId) -> Option<usize> {
    let trait_did = tcx.trait_of_assoc(assoc_did)?;
    let sorted_dids = get_trait_assoc_types(tcx, trait_did);
    for (idx, did) in sorted_dids.iter().enumerate() {
        if *did == assoc_did {
            return Some(idx);
        }
    }
    None
}

/// Check if this is the `DefId` of a method.
pub(crate) fn is_method_did(tcx: ty::TyCtxt<'_>, did: DefId) -> bool {
    if tcx.is_trait(did) {
        return false;
    }

    if tcx.trait_of_assoc(did).is_some() {
        let it = tcx.associated_item(did);
        return matches!(it.kind, ty::AssocKind::Fn { .. });
    }

    // TODO: find a more robust way to check this. We cannot call `type_of` on all dids.
    let ty = tcx.type_of(did).skip_binder();
    matches!(ty.kind(), ty::TyKind::FnDef(_, _))
}

/// Get the id of a trait impl surrounding a method.
#[must_use]
pub(crate) fn trait_impl_of_method(tcx: ty::TyCtxt<'_>, method_did: DefId) -> Option<DefId> {
    if let Some(impl_did) = tcx.impl_of_assoc(method_did) {
        tcx.impl_is_of_trait(impl_did).then_some(impl_did)
    } else {
        None
    }
}

/// Get a Procedure.
pub(crate) fn get_procedure<'tcx>(tcx: ty::TyCtxt<'tcx>, proc_def_id: DefId) -> Procedure<'tcx> {
    Procedure::new(tcx, proc_def_id)
}

pub(crate) fn dump_borrowck_info<'a, 'tcx>(
    env: ty::TyCtxt<'tcx>,
    procedure: DefId,
    info: &'a polonius_info::PoloniusInfo<'a, 'tcx>,
) {
    dump_borrowck_info::dump_borrowck_info(env, procedure, info);
}
