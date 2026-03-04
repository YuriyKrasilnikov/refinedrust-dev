// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Provides a flat representation of types that is stable across compilations.

use log::info;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::{ast, span};
use serde::{Deserialize, Serialize};
use span::symbol::Symbol;

use crate::spec_parsers::{ExportAs, RustPath, get_export_as_attr};
use crate::{Environment, attrs, search};

/// An item path that receives generic arguments.
#[derive(Clone, Eq, PartialEq, Debug, Serialize, Deserialize)]
pub(crate) struct PathWithArgs {
    path: Vec<String>,
    /// An encoding of the `GenericArgs` for this definition.
    /// This is `Some(ty)` if:
    /// - the argument represents a type (not a constant or region)
    /// - and the arg is not the trivial identity arg (in case of ADTs)
    args: Vec<Option<Type>>,
}

impl PathWithArgs {
    pub(crate) fn to_item<'tcx>(
        &self,
        tcx: ty::TyCtxt<'tcx>,
    ) -> Option<(DefId, Vec<Option<ty::GenericArg<'tcx>>>)> {
        let did = search::try_resolve_did(tcx, self.path.as_slice())?;

        let mut ty_args = Vec::new();

        for arg in &self.args {
            if let Some(arg) = arg {
                let ty = arg.to_type(tcx)?;
                ty_args.push(Some(ty::GenericArg::from(ty)));
            } else {
                ty_args.push(None);
            }
        }

        Some((did, ty_args))
    }

    /// `args` should be normalized already.
    pub(crate) fn from_item<'tcx>(
        env: &Environment<'tcx>,
        did: DefId,
        args: &[ty::GenericArg<'tcx>],
    ) -> Option<Self> {
        let path = get_export_path_for_did(env, did);
        let mut flattened_args = Vec::new();
        info!("flattening args {args:?} for did {did:?}");
        for arg in args {
            if let Some(ty) = arg.as_type() {
                let flattened_ty = convert_ty_to_flat_type(env, ty)?;
                flattened_args.push(Some(flattened_ty));
            } else {
                flattened_args.push(None);
            }
        }
        Some(Self {
            path: path.path.path,
            args: flattened_args,
        })
    }
}

#[derive(Serialize, Deserialize)]
#[serde(remote = "ty::IntTy")]
pub(crate) enum IntTyDef {
    Isize,
    I8,
    I16,
    I32,
    I64,
    I128,
}
#[derive(Serialize, Deserialize)]
#[serde(remote = "ty::UintTy")]
pub(crate) enum UintTyDef {
    Usize,
    U8,
    U16,
    U32,
    U64,
    U128,
}

#[derive(Serialize, Deserialize)]
#[serde(remote = "ast::Mutability")]
pub(crate) enum MutabilityDef {
    Not,
    Mut,
}

#[derive(Clone, Eq, PartialEq, Debug, Serialize, Deserialize)]
/// A "flattened" representation of types that should be suitable serialized storage, and should be
/// stable enough to resolve to the same actual type across compilations.
/// Currently mostly geared to our trait resolution needs.
pub(crate) enum Type {
    /// Path + generic args
    /// empty args represents the identity substitution
    Adt(PathWithArgs),
    #[serde(with = "IntTyDef")]
    Int(ty::IntTy),
    #[serde(with = "UintTyDef")]
    Uint(ty::UintTy),
    Char,
    Bool,
    Param(u32),
    Ref(u32, #[serde(with = "MutabilityDef")] ast::Mutability, Box<Self>),
    RawPtr(#[serde(with = "MutabilityDef")] ast::Mutability, Box<Self>),
    // TODO: more cases
}

impl Type {
    /// Try to convert a flat type to a type.
    pub(crate) fn to_type<'tcx>(&self, tcx: ty::TyCtxt<'tcx>) -> Option<ty::Ty<'tcx>> {
        match self {
            Self::Adt(path_with_args) => {
                let (did, flat_args) = path_with_args.to_item(tcx)?;

                let ty: ty::EarlyBinder<'_, ty::Ty<'tcx>> = tcx.type_of(did);
                let ty::TyKind::Adt(_, args) = ty.skip_binder().kind() else {
                    return None;
                };

                // build substitution
                let mut substs = Vec::new();
                for (ty_arg, flat_arg) in args.iter().zip(flat_args) {
                    match ty_arg.kind() {
                        ty::GenericArgKind::Type(_) => {
                            if let Some(flat_arg) = flat_arg {
                                substs.push(flat_arg);
                            }
                        },
                        _ => {
                            substs.push(ty_arg);
                        },
                    }
                }

                // substitute
                info!("substituting {:?} with {:?}", ty, substs);
                let subst_ty = if substs.is_empty() {
                    ty.instantiate_identity()
                } else {
                    ty.instantiate(tcx, substs.as_slice())
                };

                Some(subst_ty)
            },
            Self::Bool => Some(tcx.mk_ty_from_kind(ty::TyKind::Bool)),
            Self::Char => Some(tcx.mk_ty_from_kind(ty::TyKind::Char)),
            Self::Int(it) => Some(tcx.mk_ty_from_kind(ty::TyKind::Int(it.to_owned()))),
            Self::Uint(it) => Some(tcx.mk_ty_from_kind(ty::TyKind::Uint(it.to_owned()))),
            Self::RawPtr(m, ty) => {
                let translated_ty = ty.to_type(tcx)?;
                let kind = ty::TyKind::RawPtr(translated_ty, *m);
                Some(tcx.mk_ty_from_kind(kind))
            },
            Self::Param(idx) => {
                // use a dummy. For matching with the procedures from `unification.rs`, we only
                // need the indices to be consistent.
                let param = ty::ParamTy::new(*idx, Symbol::intern("dummy"));
                let kind = ty::TyKind::Param(param);
                Some(tcx.mk_ty_from_kind(kind))
            },
            Self::Ref(idx, m, ty) => {
                let translated_ty = ty.to_type(tcx)?;
                let early = ty::EarlyParamRegion {
                    index: *idx,
                    name: Symbol::intern("dummy"),
                };
                let region = ty::Region::new_early_param(tcx, early);
                let kind = ty::TyKind::Ref(region, translated_ty, *m);
                Some(tcx.mk_ty_from_kind(kind))
            },
        }
    }
}

/// Try to convert a type to a flat type. Assumes the type has been normalized already.
pub(crate) fn convert_ty_to_flat_type<'tcx>(env: &Environment<'tcx>, ty: ty::Ty<'tcx>) -> Option<Type> {
    match ty.kind() {
        ty::TyKind::Adt(def, args) => {
            let did = def.did();
            // TODO: if this is downcast to a variant, this might not work
            let path_with_args = PathWithArgs::from_item(env, did, args.as_slice())?;
            Some(Type::Adt(path_with_args))
        },
        ty::TyKind::Bool => Some(Type::Bool),
        ty::TyKind::Char => Some(Type::Char),
        ty::TyKind::Int(it) => Some(Type::Int(it.to_owned())),
        ty::TyKind::Uint(it) => Some(Type::Uint(it.to_owned())),
        ty::TyKind::Param(p) => Some(Type::Param(p.index)),
        ty::TyKind::RawPtr(ty, m) => {
            let converted_ty = convert_ty_to_flat_type(env, *ty)?;
            Some(Type::RawPtr(*m, Box::new(converted_ty)))
        },
        ty::TyKind::Ref(r, ty, m) => {
            let converted_ty = convert_ty_to_flat_type(env, *ty)?;

            let idx = match r.kind() {
                ty::RegionKind::ReEarlyParam(r) => r.index,
                _ => {
                    unimplemented!("convert_ty_to_flat_type: unhandled region case");
                },
            };
            Some(Type::Ref(idx, *m, Box::new(converted_ty)))
        },
        _ => None,
    }
}

pub(crate) fn get_cleaned_def_path(tcx: ty::TyCtxt<'_>, did: DefId) -> Vec<String> {
    let def_path = tcx.def_path_str(did);
    // we clean this up a bit and segment it
    let mut components = Vec::new();
    for i in def_path.split("::") {
        if i.starts_with('<') && i.ends_with('>') {
            // this is a generic specialization, skip
            continue;
        }
        components.push(i.to_owned());
    }
    info!("split def path {:?} to {:?}", def_path, components);

    components
}

/// Get the optionally annotated "external" path an item should be exported as.
pub(crate) fn get_external_export_path_for_did(env: &Environment<'_>, did: DefId) -> Option<ExportAs> {
    let attrs = env.get_attributes(did);
    if attrs::has_tool_attr(attrs, "export_as") {
        let filtered_attrs = attrs::filter_for_tool(attrs);

        return get_export_as_attr(filtered_attrs.as_slice()).ok();
    }

    let surrounding_did = if let Some(impl_did) = env.tcx().impl_of_assoc(did) {
        // Check for an annotation on the surrounding impl
        Some(impl_did)
    } else if let Some(trait_did) = env.tcx().trait_of_assoc(did) {
        // Check for an annotation on the surrounding trait
        Some(trait_did)
    } else {
        // ADT variants
        env.tcx().opt_parent(did)
    };

    if let Some(surrounding_did) = surrounding_did {
        let attrs = env.get_attributes(surrounding_did);

        if attrs::has_tool_attr(attrs, "export_as") {
            let filtered_attrs = attrs::filter_for_tool(attrs);
            let mut path_prefix = get_export_as_attr(filtered_attrs.as_slice()).unwrap();

            // push the last component of this path
            //let def_path = env.tcx().def_path(did);
            let mut this_path = get_cleaned_def_path(env.tcx(), did);
            path_prefix.path.path.push(this_path.pop().unwrap());

            // this is a method (not in a trait decl, though)
            path_prefix.as_method = env.tcx().impl_of_assoc(did).is_some();

            return Some(path_prefix);
        }
    }

    None
}

/// If this item should be exported as a different item, get that item's `DefId`.
pub(crate) fn get_external_did_for_did(env: &Environment<'_>, did: DefId) -> Option<DefId> {
    let path = get_external_export_path_for_did(env, did)?;

    if env.is_method_did(did) || path.as_method {
        search::try_resolve_method_did(env.tcx(), path.path.path)
    } else {
        search::try_resolve_did(env.tcx(), &path.path.path)
    }
}

/// Get the path we should export an item at.
pub(crate) fn get_export_path_for_did(env: &Environment<'_>, did: DefId) -> ExportAs {
    if let Some(path) = get_external_export_path_for_did(env, did) {
        return path;
    }

    let mut basic_path = get_cleaned_def_path(env.tcx(), did);
    // lets check if this is in the current crate, in that case add the current crate prefix
    if did.as_local().is_some() {
        let crate_name = env.tcx().crate_name(span::def_id::LOCAL_CRATE);
        basic_path.insert(0, crate_name.as_str().to_owned());
    }
    let as_method = env.tcx().impl_of_assoc(did).is_some();
    ExportAs {
        path: RustPath { path: basic_path },
        as_method,
    }
}
