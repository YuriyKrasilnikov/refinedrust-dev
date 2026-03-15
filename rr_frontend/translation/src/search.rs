// These functions have been adapted from Miri (https://github.com/rust-lang/miri/blob/31fb32e49f42df19b45baccb6aa80c3d726ed6d5/src/helpers.rs#L48) under the MIT license.

//! Utility functions for finding Rust source objects.

use std::collections::HashMap;
use std::mem;

use log::trace;
use rr_rustc_interface::hir::def_id::{CrateNum, DefId, LOCAL_CRATE};
use rr_rustc_interface::middle::{metadata, ty};
use rr_rustc_interface::{hir, span};

use crate::{types, unification};

/// Gets an instance for a path.
/// Taken from Miri <https://github.com/rust-lang/miri/blob/31fb32e49f42df19b45baccb6aa80c3d726ed6d5/src/helpers.rs#L48>.
pub(crate) fn try_resolve_did_direct_in_crate<T>(
    tcx: ty::TyCtxt<'_>,
    krate: CrateNum,
    path: &[T],
) -> Option<DefId>
where
    T: AsRef<str>,
{
    let krate = DefId {
        krate,
        index: hir::def_id::CRATE_DEF_INDEX,
    };

    let mut items: &[metadata::ModChild] = tcx.module_children(krate);
    let mut path_it = path.iter().peekable();

    while let Some(segment) = path_it.next() {
        for item in mem::take(&mut items) {
            let item: &metadata::ModChild = item;
            if item.ident.name.as_str() == segment.as_ref() {
                if path_it.peek().is_none() {
                    return Some(item.res.def_id());
                }

                items = tcx.module_children(item.res.def_id());
                break;
            }
        }
    }
    None
}

pub(crate) fn try_resolve_did_direct<T>(tcx: ty::TyCtxt<'_>, path: &[T]) -> Option<DefId>
where
    T: AsRef<str>,
{
    tcx.crates(())
        .iter()
        .find(|&&krate| tcx.crate_name(krate).as_str() == path[0].as_ref())
        .and_then(|krate| try_resolve_did_direct_in_crate(tcx, *krate, &path[1..]))
}

/// If we want to search in the local crate, we cannot use `module_children`, but need to use
/// `module_children_local`.
pub(crate) fn try_resolve_did_direct_in_local_crate<T>(tcx: ty::TyCtxt<'_>, path: &[T]) -> Option<DefId>
where
    T: AsRef<str>,
{
    let krate = DefId {
        krate: LOCAL_CRATE,
        index: hir::def_id::CRATE_DEF_INDEX,
    };
    let krate = krate.as_local().unwrap();

    let mut items: &[metadata::ModChild] = tcx.module_children_local(krate);
    let mut path_it = path.iter().peekable();

    while let Some(segment) = path_it.next() {
        for item in mem::take(&mut items) {
            let item: &metadata::ModChild = item;
            if item.ident.name.as_str() == segment.as_ref() {
                if path_it.peek().is_none() {
                    return Some(item.res.def_id());
                }

                if let Some(did) = item.res.def_id().as_local() {
                    items = tcx.module_children_local(did);
                    break;
                }
            }
        }
    }
    None
}

pub(crate) fn try_resolve_did<T>(tcx: ty::TyCtxt<'_>, path: &[T]) -> Option<DefId>
where
    T: AsRef<str>,
{
    // current crate?
    if path[0].as_ref() == "crate" {
        return try_resolve_did_direct_in_local_crate(tcx, &path[1..]);
    }

    // relative to global root (::...) ?
    if path[0].as_ref() == "" {
        return try_resolve_did_direct(tcx, &path[1..]);
    }

    // otherwise, first resolve in current crate
    if let Some(did) = try_resolve_did_direct_in_local_crate(tcx, path) {
        return Some(did);
    }

    // otherwise, try relative to global root
    if let Some(did) = try_resolve_did_direct(tcx, path) {
        return Some(did);
    }

    // if the first component is "std", try if we can replace it with "alloc" or "core"
    if path[0].as_ref() == "std" {
        let mut components: Vec<_> = path.iter().map(|x| x.as_ref().to_owned()).collect();
        "core".clone_into(&mut components[0]);
        if let Some(did) = try_resolve_did_direct(tcx, &components) {
            return Some(did);
        }
        // try "alloc"
        "alloc".clone_into(&mut components[0]);
        try_resolve_did_direct(tcx, &components)
    } else {
        None
    }
}

/// Try to resolve the `DefId` of an implementation of a trait for a particular type.
/// Note that this does not, in general, find a unique solution, in case there are complex things
/// with different where clauses going on.
pub(crate) fn try_resolve_trait_impl_did<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    trait_did: DefId,
    trait_args: &[Option<ty::GenericArg<'tcx>>],
    for_type: ty::Ty<'tcx>,
) -> Option<DefId> {
    // get all impls of this trait
    let impls: &ty::trait_def::TraitImpls = tcx.trait_impls_of(trait_did);
    trace!("resolving trait impl for {trait_did:?} with args {trait_args:?} for {for_type:?}");

    if let ty::TyKind::Param(_) = for_type.kind() {
        // this is a blanket impl
        let defs = impls.blanket_impls();
        trace!("found blanket implementations: {:?}", defs);

        let mut solution = None;
        for did in defs {
            let impl_ref: ty::EarlyBinder<'_, ty::TraitRef<'_>> = tcx.impl_trait_ref(*did);
            // now we need to get the constraints and see if we can unify them
            // TODO: come up with algorithm for that
            // - I guess we need to unify the type variables here.
            // - I'm assuming all type variables are open (this should be true -- all variables need to be
            //   universally quantified)
            // - I can just compute a mapping of indices to TyParam
            // - and check that it remains consistent.
            // Then I have an output mapping, and can check if the where clauses are satisfied for
            // that mapping
            let impl_ref = types::normalize_in_function(*did, tcx, impl_ref.skip_binder()).unwrap();

            let this_impl_args = impl_ref.args;
            // filter by the generic instantiation for the trait
            trace!("found impl with args {:?}", this_impl_args);
            // args has self at position 0 and generics of the trait at position 1..

            // check if the generic argument types match up
            let mut unification_map = HashMap::new();
            if !unification::args_unify_types(
                &this_impl_args.as_slice()[1..],
                trait_args,
                &mut unification_map,
            ) {
                trace!("args don't unify: {this_impl_args:?} and {trait_args:?}");
                continue;
            }

            // TODO check if the where clauses match up

            trace!("found impl {:?}", impl_ref);
            if let Some(solution) = solution {
                println!(
                    "Warning: Ambiguous resolution for impl of trait {:?} on type {:?}; solution {:?} but found also {:?}",
                    trait_did, for_type, solution, impl_ref.def_id,
                );
            } else {
                solution = Some(*did);
            }
        }

        solution
    } else {
        let mut unification_map = HashMap::new();

        // this is a non-blanket impl
        let simplified_type = ty::fast_reject::simplify_type(
            tcx,
            for_type,
            ty::fast_reject::TreatParams::InstantiateWithInfer,
        )?;
        let defs = impls.non_blanket_impls().get(&simplified_type)?;
        trace!("found non-blanket implementations: {:?}", defs);

        let mut solution = None;
        for did in defs {
            let impl_self_ty: ty::Ty<'tcx> = tcx.type_of(*did).instantiate_identity();
            let impl_self_ty = types::normalize_in_function(*did, tcx, impl_self_ty).unwrap();

            trace!("trying to unify types: {for_type:?} and {impl_self_ty:?}");
            // check if this is an implementation for the right type
            if unification::unify_types(for_type, impl_self_ty, &mut unification_map) {
                let impl_ref: ty::EarlyBinder<'_, ty::TraitRef<'_>> = tcx.impl_trait_ref(*did);
                let impl_ref = types::normalize_in_function(*did, tcx, impl_ref.skip_binder()).unwrap();

                let this_impl_args = impl_ref.args;
                // filter by the generic instantiation for the trait
                trace!("found impl with args {:?}", this_impl_args);
                // args has self at position 0 and generics of the trait at position 1..

                // check if the generic argument types match up
                let mut unification_map = unification_map.clone();
                if !unification::args_unify_types(
                    &this_impl_args.as_slice()[1..],
                    trait_args,
                    &mut unification_map,
                ) {
                    trace!("args don't unify: {this_impl_args:?} and {trait_args:?}");
                    continue;
                }

                trace!("found impl {:?}", impl_ref);
                if let Some(solution) = solution {
                    println!(
                        "Warning: Ambiguous resolution for impl of trait {:?} on type {:?}; solution {:?} but found also {:?}",
                        trait_did, for_type, solution, impl_ref.def_id,
                    );
                } else {
                    solution = Some(*did);
                }
            }
        }
        solution
    }
}

/// Try to get a defid of a method at the given path.
/// This does not handle trait methods.
/// This also does not handle overlapping method definitions/specialization well.
pub(crate) fn try_resolve_method_did_direct<T>(tcx: ty::TyCtxt<'_>, path: &[T]) -> Option<DefId>
where
    T: AsRef<str>,
{
    tcx.crates(())
        .iter()
        .find(|&&krate| tcx.crate_name(krate).as_str() == path[0].as_ref())
        .and_then(|krate| {
            let krate = DefId {
                krate: *krate,
                index: hir::def_id::CRATE_DEF_INDEX,
            };

            let mut items: &[metadata::ModChild] = tcx.module_children(krate);
            let mut path_it = path.iter().skip(1).peekable();

            while let Some(segment) = path_it.next() {
                //trace!("following segment {:?}; items to look at: {:?}", segment.as_ref(), items);
                for item in mem::take(&mut items) {
                    let item: &metadata::ModChild = item;

                    if item.ident.name.as_str() != segment.as_ref() {
                        continue;
                    }

                    trace!("taking path: {:?}", segment.as_ref());
                    if path_it.peek().is_none() {
                        return Some(item.res.def_id());
                    }

                    // just the method remaining
                    if path_it.len() != 1 {
                        items = tcx.module_children(item.res.def_id());
                        break;
                    }

                    let did: DefId = item.res.def_id();
                    let impls: &[DefId] = tcx.inherent_impls(did);
                    //trace!("trying to find method among impls {:?}", impls);
                    if impls.is_empty() {
                        //trace!("children: {:?}", tcx.module_children(item.res.def_id()));
                    }

                    let find = path_it.next().unwrap();
                    for impl_did in impls {
                        //let ty = tcx.type_of(*impl_did);
                        //info!("type of impl: {:?}", ty);
                        let items: &ty::AssocItems = tcx.associated_items(*impl_did);
                        //info!("items here: {:?}", items);
                        // TODO more robust error handling if there are multiple matches.
                        for item in items.in_definition_order() {
                            //info!("comparing: {:?} with {:?}", item.name.as_str(), find);
                            if item.name().as_str() == find.as_ref() {
                                return Some(item.def_id);
                            }
                        }
                        //info!("impl items: {:?}", items);
                    }

                    //info!("inherent impls for {:?}: {:?}", did, impls);
                    return None;
                }
            }

            None
        })
}

/// Try to resolve a method from an incoherent impl of one of the built-in primitive types.
pub(crate) fn try_resolve_method_did_incoherent(tcx: ty::TyCtxt<'_>, path: &[String]) -> Option<DefId> {
    let simplified_ty = if path[0..3] == ["core", "ptr", "mut_ptr"] {
        let param_ty = ty::ParamTy::new(0, span::Symbol::intern("dummy"));
        let param_ty = ty::TyKind::Param(param_ty);
        let param_ty = tcx.mk_ty_from_kind(param_ty);

        let mut_ptr_ty = ty::TyKind::RawPtr(param_ty, hir::Mutability::Mut);
        let mut_ptr_ty = tcx.mk_ty_from_kind(mut_ptr_ty);

        Some((
            ty::fast_reject::simplify_type(tcx, mut_ptr_ty, ty::fast_reject::TreatParams::AsRigid).unwrap(),
            3,
        ))
    } else if path[0..3] == ["core", "ptr", "const_ptr"] {
        let param_ty = ty::ParamTy::new(0, span::Symbol::intern("dummy"));
        let param_ty = ty::TyKind::Param(param_ty);
        let param_ty = tcx.mk_ty_from_kind(param_ty);

        let mut_ptr_ty = ty::TyKind::RawPtr(param_ty, hir::Mutability::Not);
        let mut_ptr_ty = tcx.mk_ty_from_kind(mut_ptr_ty);

        Some((
            ty::fast_reject::simplify_type(tcx, mut_ptr_ty, ty::fast_reject::TreatParams::AsRigid).unwrap(),
            3,
        ))
    } else if path[0..2] == ["core", "bool"] {
        let int_ty = ty::TyKind::Bool;
        let int_ty = tcx.mk_ty_from_kind(int_ty);
        Some((ty::fast_reject::simplify_type(tcx, int_ty, ty::fast_reject::TreatParams::AsRigid).unwrap(), 2))
    } else if path[0..2] == ["core", "char"] {
        let int_ty = ty::TyKind::Char;
        let int_ty = tcx.mk_ty_from_kind(int_ty);
        Some((ty::fast_reject::simplify_type(tcx, int_ty, ty::fast_reject::TreatParams::AsRigid).unwrap(), 2))
    } else if path[0..2] == ["core", "num"] {
        let int_ty = match path[2].as_str() {
            "isize" => Some(ty::IntTy::Isize),
            "i8" => Some(ty::IntTy::I8),
            "i16" => Some(ty::IntTy::I16),
            "i32" => Some(ty::IntTy::I32),
            "i64" => Some(ty::IntTy::I64),
            "i128" => Some(ty::IntTy::I128),
            _ => None,
        };
        let uint_ty = match path[2].as_str() {
            "usize" => Some(ty::UintTy::Usize),
            "u8" => Some(ty::UintTy::U8),
            "u16" => Some(ty::UintTy::U16),
            "u32" => Some(ty::UintTy::U32),
            "u64" => Some(ty::UintTy::U64),
            "u128" => Some(ty::UintTy::U128),
            _ => None,
        };

        if let Some(int_ty) = int_ty {
            let int_ty = ty::TyKind::Int(int_ty);
            let int_ty = tcx.mk_ty_from_kind(int_ty);

            Some((
                ty::fast_reject::simplify_type(tcx, int_ty, ty::fast_reject::TreatParams::AsRigid).unwrap(),
                3,
            ))
        } else if let Some(uint_ty) = uint_ty {
            let int_ty = ty::TyKind::Uint(uint_ty);
            let int_ty = tcx.mk_ty_from_kind(int_ty);

            Some((
                ty::fast_reject::simplify_type(tcx, int_ty, ty::fast_reject::TreatParams::AsRigid).unwrap(),
                3,
            ))
        } else {
            None
        }
    }
    // TODO more primitive types
    else {
        None
    };

    if let Some((simplified_ty, method_idx)) = simplified_ty
        && let Some(method) = path.get(method_idx)
    {
        let incoherent_impls: &[DefId] = tcx.incoherent_impls(simplified_ty);

        //trace!("incoherent impls for {:?}: {:?}", simplified_ty, incoherent_impls);

        for impl_did in incoherent_impls {
            let items: &ty::AssocItems = tcx.associated_items(*impl_did);
            //trace!("items in {:?}: {:?}", impl_did, items);
            // TODO: more robustly handle ambiguous matches
            for item in items.in_definition_order() {
                //info!("comparing: {:?} with {:?}", item.name.as_str(), find);
                if item.name().as_str() == method.as_str() {
                    return Some(item.def_id);
                }
            }
        }
    }

    None
}

pub(crate) fn try_resolve_method_did(tcx: ty::TyCtxt<'_>, mut path: Vec<String>) -> Option<DefId> {
    if let Some(did) = try_resolve_method_did_direct(tcx, &path) {
        return Some(did);
    }

    // if the first component is "std", try if we can replace it with "alloc" or "core"
    if path[0] == "std" {
        "core".clone_into(&mut path[0]);
        if let Some(did) = try_resolve_method_did_direct(tcx, &path) {
            return Some(did);
        }
        // try "alloc"
        "alloc".clone_into(&mut path[0]);
        if let Some(did) = try_resolve_method_did_direct(tcx, &path) {
            return Some(did);
        }
    }

    // otherwise, try if this is in an incoherent impl
    try_resolve_method_did_incoherent(tcx, &path)
}

/// Get the `Defid` of a closure trait.
pub(crate) fn get_closure_trait_did(tcx: ty::TyCtxt<'_>, kind: ty::ClosureKind) -> Option<DefId> {
    match kind {
        ty::ClosureKind::Fn => try_resolve_did(tcx, &["core", "ops", "Fn"]),
        ty::ClosureKind::FnMut => try_resolve_did(tcx, &["core", "ops", "FnMut"]),
        ty::ClosureKind::FnOnce => try_resolve_did(tcx, &["core", "ops", "FnOnce"]),
    }
}

/// Given the `DefId` of a trait, determine which (if any) of the closure traits this `DefId` refers to.
pub(crate) fn get_closure_kind_of_trait_did(tcx: ty::TyCtxt<'_>, did: DefId) -> Option<ty::ClosureKind> {
    let fnmut_did = get_closure_trait_did(tcx, ty::ClosureKind::FnMut)?;
    let fn_did = get_closure_trait_did(tcx, ty::ClosureKind::Fn)?;
    let fnonce_did = get_closure_trait_did(tcx, ty::ClosureKind::FnOnce)?;

    if did == fnmut_did {
        Some(ty::ClosureKind::FnMut)
    } else if did == fn_did {
        Some(ty::ClosureKind::Fn)
    } else if did == fnonce_did {
        Some(ty::ClosureKind::FnOnce)
    } else {
        None
    }
}
