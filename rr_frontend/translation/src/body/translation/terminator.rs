// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::BTreeMap;

use log::{info, trace, warn};
use radium::{code, lang, specs};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};

use super::TX;
use rr_rustc_interface::span;

use crate::base::*;
use crate::environment::borrowck::facts;
use crate::{search, types};

/// Classification of atomic intrinsics.
///
/// Rust atomic methods (e.g. `AtomicU8::load`) compile to MIR intrinsics
/// (`core::intrinsics::atomic_load`). On nightly-2026-02-23, the ordering
/// is a const generic parameter — the intrinsic name does NOT include the
/// ordering suffix.
#[derive(Debug, Clone, Copy)]
enum AtomicIntrinsicKind {
    Load,
    Store,
    Rmw(lang::AtomicRmwOp),
    /// Strong and weak CAS are equivalent in the SC interleaving model.
    Cxchg,
    Fence,
}

/// Strip ordering suffix from old-style atomic intrinsic names.
///
/// Old-style (pre-2025): `atomic_load_seqcst` → `atomic_load`
/// New-style (const generic): `atomic_load` → `atomic_load` (unchanged)
fn strip_atomic_ordering_suffix(name: &str) -> &str {
    const SUFFIXES: &[&str] = &[
        "_seqcst", "_acqrel", "_acquire", "_release", "_relaxed", "_unordered",
    ];
    for suffix in SUFFIXES {
        if let Some(base) = name.strip_suffix(suffix) {
            return base;
        }
    }
    name
}

/// Classify an atomic intrinsic by name.
///
/// Handles both new-style (`atomic_load`) and old-style (`atomic_load_seqcst`)
/// intrinsic names. Returns `None` for unrecognized names.
/// The caller must treat `None` as an error if the name starts with `"atomic_"`.
fn classify_atomic_intrinsic(name: &str) -> Option<AtomicIntrinsicKind> {
    let name = strip_atomic_ordering_suffix(name);
    match name {
        "atomic_load" => Some(AtomicIntrinsicKind::Load),
        "atomic_store" => Some(AtomicIntrinsicKind::Store),
        "atomic_cxchg" | "atomic_cxchgweak" => Some(AtomicIntrinsicKind::Cxchg),
        "atomic_xchg" => Some(AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::Xchg)),
        "atomic_xadd" => Some(AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::Add)),
        "atomic_xsub" => Some(AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::Sub)),
        "atomic_and" => Some(AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::And)),
        "atomic_or" => Some(AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::Or)),
        "atomic_xor" => Some(AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::Xor)),
        "atomic_nand" => Some(AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::Nand)),
        "atomic_max" => Some(AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::MaxSigned)),
        "atomic_min" => Some(AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::MinSigned)),
        "atomic_umax" => Some(AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::MaxUnsigned)),
        "atomic_umin" => Some(AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::MinUnsigned)),
        "atomic_fence" | "atomic_singlethreadfence" => Some(AtomicIntrinsicKind::Fence),
        _ => None,
    }
}

/// Classify a method on a `#[rr::mode(atomic)]` type by name.
///
/// Maps standard atomic method names to Caesium operation equivalents.
/// `signed` selects `MaxSigned`/`MinSigned` vs `MaxUnsigned`/`MinUnsigned` for `fetch_max`/`fetch_min`.
/// Returns `None` for methods that are not atomic operations (e.g. `new`, `into_inner`).
fn classify_atomic_method(name: &str, signed: bool) -> Option<AtomicIntrinsicKind> {
    match name {
        "load" => Some(AtomicIntrinsicKind::Load),
        "store" => Some(AtomicIntrinsicKind::Store),
        "swap" => Some(AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::Xchg)),
        "fetch_add" => Some(AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::Add)),
        "fetch_sub" => Some(AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::Sub)),
        "fetch_and" => Some(AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::And)),
        "fetch_or" => Some(AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::Or)),
        "fetch_xor" => Some(AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::Xor)),
        "fetch_nand" => Some(AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::Nand)),
        "fetch_max" => Some(AtomicIntrinsicKind::Rmw(if signed {
            lang::AtomicRmwOp::MaxSigned
        } else {
            lang::AtomicRmwOp::MaxUnsigned
        })),
        "fetch_min" => Some(AtomicIntrinsicKind::Rmw(if signed {
            lang::AtomicRmwOp::MinSigned
        } else {
            lang::AtomicRmwOp::MinUnsigned
        })),
        "compare_exchange" | "compare_exchange_weak" => Some(AtomicIntrinsicKind::Cxchg),
        _ => None,
    }
}

#[expect(clippy::multiple_inherent_impl)]
impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    fn check_call_destination(func: &mir::Operand<'_>, target_did: DefId) -> bool {
        let mir::Operand::Constant(box c) = func else {
            return false;
        };

        let mir::Const::Val(_, ty) = c.const_ else {
            return false;
        };

        let ty::TyKind::FnDef(did, _) = ty.kind() else {
            return false;
        };

        target_did == *did
    }

    /// Check if a call goes to `std::rt::begin_panic`
    fn is_call_destination_panic(&self, func: &mir::Operand<'_>) -> bool {
        if let Some(panic_id_std) =
            search::try_resolve_did(self.env.tcx(), &["std", "panicking", "begin_panic"])
        {
            if Self::check_call_destination(func, panic_id_std) {
                return true;
            }
        } else {
            warn!("Failed to determine DefId of std::panicking::begin_panic");
        }

        if let Some(panic_id_core) = search::try_resolve_did(self.env.tcx(), &["core", "panicking", "panic"])
        {
            if Self::check_call_destination(func, panic_id_core) {
                return true;
            }
        } else {
            warn!("Failed to determine DefId of core::panicking::panic");
        }

        false
    }

    // Check if the destination of this call is `core::intrinsics::discriminant_value`.
    fn is_call_destination_discriminant(&self, func: &mir::Operand<'_>) -> bool {
        if let Some(discriminant_did) =
            search::try_resolve_did(self.env.tcx(), &["core", "intrinsics", "discriminant_value"])
        {
            if Self::check_call_destination(func, discriminant_did) {
                return true;
            }
        } else {
            warn!("Failed to determine DefId of core::intrinsics::discriminant_value");
        }

        false
    }

    fn make_discriminant_shim(
        &mut self,
        op: &mir::Operand<'tcx>,
        dest: &mir::Place<'tcx>,
    ) -> Result<Vec<code::PrimStmt>, TranslationError<'tcx>> {
        let (translated_op, _) = self.translate_operand(op, false)?;
        let ty = self.get_type_of_operand(op);

        let st = self.ty_translator.translate_type_to_syn_type(ty)?;
        let translated_rhs = code::Expr::Deref {
            ot: st.into(),
            order: lang::Order::Na,
            e: Box::new(translated_op),
        };

        let ty::TyKind::Ref(_, ty, _) = ty.kind() else {
            unreachable!();
        };
        let ty::TyKind::Adt(adt_def, args) = ty.kind() else {
            return Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support discriminant accesses on non-enum types (got {:?})",
                    ty
                ),
            });
        };
        let enum_use = self.ty_translator.generate_enum_use(*adt_def, args)?;
        let els = enum_use.generate_raw_syn_type_term();

        let discriminant_acc = code::Expr::EnumDiscriminant {
            els: els.to_string(),
            e: Box::new(translated_rhs),
        };

        let translated_place = self.translate_place(dest)?;

        // get the discriminant type
        let it = adt_def.repr().discr_type();
        let translated_it = types::TX::translate_integer_type(it);

        let assign = code::PrimStmt::Assign {
            ot: lang::OpType::Int(translated_it),
            order: lang::Order::Na,
            e1: Box::new(translated_place),
            e2: Box::new(discriminant_acc),
        };

        Ok(vec![assign])
    }

    /// Extract `DefId` from a function call operand.
    fn extract_fn_def_id(func: &mir::Operand<'_>) -> Option<DefId> {
        let mir::Operand::Constant(box c) = func else {
            return None;
        };

        let mir::Const::Val(_, ty) = c.const_ else {
            return None;
        };

        let ty::TyKind::FnDef(did, _) = ty.kind() else {
            return None;
        };

        Some(*did)
    }

    /// Check if a function call targets an atomic intrinsic and classify it.
    ///
    /// Returns `Ok(None)` if the call is not an atomic intrinsic (normal function call).
    /// Returns `Err` if the call IS an atomic intrinsic but unrecognized (B₃ FAIL-FIRST).
    fn try_classify_atomic_intrinsic(
        &self,
        func: &mir::Operand<'tcx>,
    ) -> Result<Option<AtomicIntrinsicKind>, TranslationError<'tcx>> {
        let Some(did) = Self::extract_fn_def_id(func) else {
            return Ok(None);
        };

        let Some(intrinsic_def) = self.env.tcx().intrinsic(did) else {
            return Ok(None);
        };

        let name = intrinsic_def.name.as_str();
        if !name.starts_with("atomic_") {
            return Ok(None);
        }

        match classify_atomic_intrinsic(name) {
            Some(kind) => Ok(Some(kind)),
            None => Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "unknown atomic intrinsic '{name}'; \
                     this may be a new intrinsic not yet supported by RefinedRust"
                ),
            }),
        }
    }

    /// Extract the pointee `OpType` from a raw pointer operand.
    fn get_pointee_op_type(
        &self,
        op: &mir::Operand<'tcx>,
    ) -> Result<lang::OpType, TranslationError<'tcx>> {
        let ptr_ty = self.get_type_of_operand(op);
        match ptr_ty.kind() {
            ty::TyKind::RawPtr(pointee_ty, _) => {
                let st = self.ty_translator.translate_type_to_syn_type(*pointee_ty)?;
                Ok((&st).into())
            },
            _ => Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "expected raw pointer type for atomic intrinsic argument, got {ptr_ty:?}"
                ),
            }),
        }
    }

    /// Translate an atomic intrinsic to Caesium primitive statements.
    ///
    /// All Rust memory orderings map to `ScOrd` (sequentially consistent) — a sound
    /// over-approximation in the interleaving semantics model.
    fn translate_atomic_intrinsic(
        &mut self,
        kind: AtomicIntrinsicKind,
        args: &[span::source_map::Spanned<mir::Operand<'tcx>>],
        destination: &mir::Place<'tcx>,
    ) -> Result<Vec<code::PrimStmt>, TranslationError<'tcx>> {
        match kind {
            AtomicIntrinsicKind::Load => {
                // atomic_load<T, ORD>(src: *const T) -> T
                // Emit: dest <-{ot, Na} !{ot, ScOrd}(ptr)
                let ot = self.get_pointee_op_type(&args[0].node)?;
                let (ptr_expr, _) = self.translate_operand(&args[0].node, true)?;

                let deref_expr = code::Expr::Deref {
                    ot: ot.clone(),
                    order: lang::Order::Sc,
                    e: Box::new(ptr_expr),
                };

                let dest_place = self.translate_place(destination)?;
                Ok(vec![code::PrimStmt::Assign {
                    ot,
                    order: lang::Order::Na,
                    e1: Box::new(dest_place),
                    e2: Box::new(deref_expr),
                }])
            },

            AtomicIntrinsicKind::Store => {
                // atomic_store<T, ORD>(dst: *mut T, val: T) -> ()
                // Emit: ptr <-{ot, ScOrd} val; dest <-{UnitOp, Na} zst_val
                let ot = self.get_pointee_op_type(&args[0].node)?;
                let (ptr_expr, _) = self.translate_operand(&args[0].node, true)?;
                let (val_expr, _) = self.translate_operand(&args[1].node, true)?;

                let atomic_store = code::PrimStmt::Assign {
                    ot,
                    order: lang::Order::Sc,
                    e1: Box::new(ptr_expr),
                    e2: Box::new(val_expr),
                };

                let dest_place = self.translate_place(destination)?;
                let unit_assign = code::PrimStmt::Assign {
                    ot: lang::SynType::Unit.into(),
                    order: lang::Order::Na,
                    e1: Box::new(dest_place),
                    e2: Box::new(code::Expr::Literal(code::Literal::ZST)),
                };

                Ok(vec![atomic_store, unit_assign])
            },

            AtomicIntrinsicKind::Rmw(rmw_op) => {
                // atomic_xchg/xadd/xsub/and/or/xor/nand/max/min/umax/umin
                // <T, ORD>(dst: *mut T, val: T) -> T  (returns old value)
                // Emit: dest <-{ot, Na} AtomicRMW op ot (ptr) (val)
                let ot = self.get_pointee_op_type(&args[0].node)?;
                let (ptr_expr, _) = self.translate_operand(&args[0].node, true)?;
                let (val_expr, _) = self.translate_operand(&args[1].node, true)?;

                let rmw_expr = code::Expr::AtomicRmw {
                    op: rmw_op,
                    ot: ot.clone(),
                    target: Box::new(ptr_expr),
                    arg: Box::new(val_expr),
                };

                let dest_place = self.translate_place(destination)?;
                Ok(vec![code::PrimStmt::Assign {
                    ot,
                    order: lang::Order::Na,
                    e1: Box::new(dest_place),
                    e2: Box::new(rmw_expr),
                }])
            },

            AtomicIntrinsicKind::Cxchg => {
                // atomic_cxchg<T, ORD_S, ORD_F>(dst: *mut T, old: T, src: T) -> (T, bool)
                //
                // Caesium CAS returns bool and writes old value to *expected (C11 model).
                // Rust returns (T, bool). Bridge via temporary:
                //   1. local_live temp
                //   2. temp <-{ot} expected_val
                //   3. dest.1 <-{BoolOp} CAS(ot, target, &raw{Mut}(temp), desired)
                //   4. dest.0 <-{ot} copy{ot}(temp)   — old value
                //   5. local_dead temp

                // Pointee SynType + OpType from args[0]: *mut T
                let ptr_ty = self.get_type_of_operand(&args[0].node);
                let ty::TyKind::RawPtr(pointee_ty, _) = ptr_ty.kind() else {
                    return Err(TranslationError::UnsupportedFeature {
                        description: format!(
                            "expected raw pointer for atomic CAS target, got {ptr_ty:?}"
                        ),
                    });
                };
                let pointee_st = self.ty_translator.translate_type_to_syn_type(*pointee_ty)?;
                let ot: lang::OpType = (&pointee_st).into();

                let (target_ptr, _) = self.translate_operand(&args[0].node, true)?;
                let (expected_val, _) = self.translate_operand(&args[1].node, true)?;
                let (desired_val, _) = self.translate_operand(&args[2].node, true)?;

                // Dest tuple (T, bool): get SLS for FieldOf projections
                let dest_pty = self.get_type_of_place(destination);
                let dest_lit = self
                    .ty_translator
                    .generate_structlike_use(dest_pty.ty, dest_pty.variant_index)?;
                let dest_sls = dest_lit
                    .map_or(lang::SynType::Unit, |x| x.generate_raw_syn_type_term())
                    .to_string();
                let dest_place = self.translate_place(destination)?;

                let dest_0 = code::Expr::FieldOf {
                    e: Box::new(dest_place.clone()),
                    sls: dest_sls.clone(),
                    name: "0".to_owned(),
                };
                let dest_1 = code::Expr::FieldOf {
                    e: Box::new(dest_place),
                    sls: dest_sls,
                    name: "1".to_owned(),
                };

                let temp_name = "__cas_expected".to_owned();
                let temp_var = code::Expr::Var(temp_name.clone());

                // 1. Allocate temporary for expected value
                let stmt_live = code::PrimStmt::LocalLive(code::Variable::new(
                    temp_name.clone(),
                    pointee_st,
                ));

                // 2. Store expected value into temporary
                let stmt_store = code::PrimStmt::Assign {
                    ot: ot.clone(),
                    order: lang::Order::Na,
                    e1: Box::new(temp_var.clone()),
                    e2: Box::new(expected_val),
                };

                // 3. CAS: dest.1 <-{BoolOp} CAS(ot, target, &raw{Mut}(temp), desired)
                let cas_expr = code::Expr::Cas {
                    ot: ot.clone(),
                    target: Box::new(target_ptr),
                    expected: Box::new(code::Expr::AddressOf {
                        mt: code::Mutability::Mut,
                        e: Box::new(temp_var.clone()),
                    }),
                    desired: Box::new(desired_val),
                };
                let stmt_cas = code::PrimStmt::Assign {
                    ot: lang::OpType::Bool,
                    order: lang::Order::Na,
                    e1: Box::new(dest_1),
                    e2: Box::new(cas_expr),
                };

                // 4. Read old value: dest.0 <-{ot} copy{ot}(temp)
                // After CAS, temp contains old target value in both cases:
                //   failure: Caesium writes old value to *expected
                //   success: temp unchanged, but expected == old (match was exact)
                let stmt_old = code::PrimStmt::Assign {
                    ot: ot.clone(),
                    order: lang::Order::Na,
                    e1: Box::new(dest_0),
                    e2: Box::new(code::Expr::Copy {
                        ot,
                        order: lang::Order::Na,
                        e: Box::new(temp_var),
                    }),
                };

                // 5. Deallocate temporary
                let stmt_dead = code::PrimStmt::LocalDead(temp_name);

                Ok(vec![stmt_live, stmt_store, stmt_cas, stmt_old, stmt_dead])
            },

            AtomicIntrinsicKind::Fence => {
                // No-op in SC interleaving model. Assign () to destination.
                let dest_place = self.translate_place(destination)?;
                Ok(vec![code::PrimStmt::Assign {
                    ot: lang::SynType::Unit.into(),
                    order: lang::Order::Na,
                    e1: Box::new(dest_place),
                    e2: Box::new(code::Expr::Literal(code::Literal::ZST)),
                }])
            },
        }
    }

    /// Check if a function call targets a method on a `#[rr::mode(atomic)]` type.
    ///
    /// If so, returns the classified operation and the inner value's `OpType`.
    /// Returns `Ok(None)` for non-atomic methods or non-method calls.
    fn try_classify_atomic_method(
        &self,
        func: &mir::Operand<'tcx>,
        args: &[span::source_map::Spanned<mir::Operand<'tcx>>],
    ) -> Result<Option<(AtomicIntrinsicKind, lang::OpType, lang::SynType)>, TranslationError<'tcx>> {
        let Some(did) = Self::extract_fn_def_id(func) else {
            return Ok(None);
        };

        let tcx = self.env.tcx();

        // Must be an associated item (method in an impl block)
        if tcx.impl_of_assoc(did).is_none() {
            return Ok(None);
        }

        // Get the self type from the first argument
        if args.is_empty() {
            return Ok(None);
        }
        let self_ref_ty = self.get_type_of_operand(&args[0].node);
        let adt_ty = match self_ref_ty.kind() {
            ty::TyKind::Ref(_, pointee, _) => *pointee,
            ty::TyKind::Adt(..) => self_ref_ty,
            _ => return Ok(None),
        };
        let ty::TyKind::Adt(adt_def, substs) = adt_ty.kind() else {
            return Ok(None);
        };

        // Single-variant structs only
        if adt_def.variants().len() != 1 {
            return Ok(None);
        }
        let variant = adt_def.variants().iter().next().unwrap();

        // Check mode(atomic) in spec
        if !self.ty_translator.translator.is_variant_atomic(variant.def_id) {
            return Ok(None);
        }

        // Inner field type (repr(transparent) with single field)
        if variant.fields.len() != 1 {
            return Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "mode(atomic) type {} must have exactly one field (repr(transparent))",
                    tcx.def_path_str(adt_def.did())
                ),
            });
        }
        let inner_field = variant.fields.iter().next().unwrap();
        let inner_ty = inner_field.ty(tcx, substs);
        let inner_st = self.ty_translator.translate_type_to_syn_type(inner_ty)?;
        let ot: lang::OpType = (&inner_st).into();

        let signed = matches!(inner_ty.kind(), ty::TyKind::Int(_));
        let method_name = tcx.item_name(did);

        match classify_atomic_method(method_name.as_str(), signed) {
            Some(kind) => Ok(Some((kind, ot, inner_st))),
            None => Ok(None),
        }
    }

    /// Translate an atomic method call on a `#[rr::mode(atomic)]` type to Caesium primitives.
    ///
    /// Method argument conventions (Ordering args are ignored — all map to ScOrd):
    /// - `load(&self, order)` → `Deref` `ScOrd`
    /// - `store(&self, val, order)` → `Assign` `ScOrd`
    /// - `swap`/`fetch_*(&self, val, order)` → `AtomicRMW`
    /// - `compare_exchange(&self, current, new, ord_s, ord_f)` → `CAS` via 5-stmt bridge
    fn translate_atomic_method(
        &mut self,
        kind: AtomicIntrinsicKind,
        ot: lang::OpType,
        st: lang::SynType,
        args: &[span::source_map::Spanned<mir::Operand<'tcx>>],
        destination: &mir::Place<'tcx>,
    ) -> Result<Vec<code::PrimStmt>, TranslationError<'tcx>> {
        match kind {
            AtomicIntrinsicKind::Load => {
                // load(&self, order) -> T
                let (ptr_expr, _) = self.translate_operand(&args[0].node, true)?;

                let deref_expr = code::Expr::Deref {
                    ot: ot.clone(),
                    order: lang::Order::Sc,
                    e: Box::new(ptr_expr),
                };

                let dest_place = self.translate_place(destination)?;
                Ok(vec![code::PrimStmt::Assign {
                    ot,
                    order: lang::Order::Na,
                    e1: Box::new(dest_place),
                    e2: Box::new(deref_expr),
                }])
            },

            AtomicIntrinsicKind::Store => {
                // store(&self, val, order)
                let (ptr_expr, _) = self.translate_operand(&args[0].node, true)?;
                let (val_expr, _) = self.translate_operand(&args[1].node, true)?;

                let atomic_store = code::PrimStmt::Assign {
                    ot,
                    order: lang::Order::Sc,
                    e1: Box::new(ptr_expr),
                    e2: Box::new(val_expr),
                };

                let dest_place = self.translate_place(destination)?;
                let unit_assign = code::PrimStmt::Assign {
                    ot: lang::SynType::Unit.into(),
                    order: lang::Order::Na,
                    e1: Box::new(dest_place),
                    e2: Box::new(code::Expr::Literal(code::Literal::ZST)),
                };

                Ok(vec![atomic_store, unit_assign])
            },

            AtomicIntrinsicKind::Rmw(rmw_op) => {
                // swap/fetch_*(&self, val, order) -> T
                let (ptr_expr, _) = self.translate_operand(&args[0].node, true)?;
                let (val_expr, _) = self.translate_operand(&args[1].node, true)?;

                let rmw_expr = code::Expr::AtomicRmw {
                    op: rmw_op,
                    ot: ot.clone(),
                    target: Box::new(ptr_expr),
                    arg: Box::new(val_expr),
                };

                let dest_place = self.translate_place(destination)?;
                Ok(vec![code::PrimStmt::Assign {
                    ot,
                    order: lang::Order::Na,
                    e1: Box::new(dest_place),
                    e2: Box::new(rmw_expr),
                }])
            },

            AtomicIntrinsicKind::Cxchg => {
                // compare_exchange(&self, current, new, success_ord, failure_ord) -> (T, bool)
                // Same 5-stmt bridge as intrinsic CAS, but args[0] = &self (shared ref).
                let (target_ptr, _) = self.translate_operand(&args[0].node, true)?;
                let (expected_val, _) = self.translate_operand(&args[1].node, true)?;
                let (desired_val, _) = self.translate_operand(&args[2].node, true)?;

                // Dest tuple (T, bool): get SLS for FieldOf projections
                let dest_pty = self.get_type_of_place(destination);
                let dest_lit = self
                    .ty_translator
                    .generate_structlike_use(dest_pty.ty, dest_pty.variant_index)?;
                let dest_sls = dest_lit
                    .map_or(lang::SynType::Unit, |x| x.generate_raw_syn_type_term())
                    .to_string();
                let dest_place = self.translate_place(destination)?;

                let dest_0 = code::Expr::FieldOf {
                    e: Box::new(dest_place.clone()),
                    sls: dest_sls.clone(),
                    name: "0".to_owned(),
                };
                let dest_1 = code::Expr::FieldOf {
                    e: Box::new(dest_place),
                    sls: dest_sls,
                    name: "1".to_owned(),
                };

                let temp_name = "__cas_expected".to_owned();
                let temp_var = code::Expr::Var(temp_name.clone());

                // 1. Allocate temporary for expected value
                let stmt_live = code::PrimStmt::LocalLive(code::Variable::new(
                    temp_name.clone(),
                    st,
                ));

                // 2. Store expected value into temporary
                let stmt_store = code::PrimStmt::Assign {
                    ot: ot.clone(),
                    order: lang::Order::Na,
                    e1: Box::new(temp_var.clone()),
                    e2: Box::new(expected_val),
                };

                // 3. CAS: dest.1 <-{BoolOp} CAS(ot, target, &raw{Mut}(temp), desired)
                let cas_expr = code::Expr::Cas {
                    ot: ot.clone(),
                    target: Box::new(target_ptr),
                    expected: Box::new(code::Expr::AddressOf {
                        mt: code::Mutability::Mut,
                        e: Box::new(temp_var.clone()),
                    }),
                    desired: Box::new(desired_val),
                };
                let stmt_cas = code::PrimStmt::Assign {
                    ot: lang::OpType::Bool,
                    order: lang::Order::Na,
                    e1: Box::new(dest_1),
                    e2: Box::new(cas_expr),
                };

                // 4. Read old value: dest.0 <-{ot} copy{ot}(temp)
                let stmt_old = code::PrimStmt::Assign {
                    ot: ot.clone(),
                    order: lang::Order::Na,
                    e1: Box::new(dest_0),
                    e2: Box::new(code::Expr::Copy {
                        ot,
                        order: lang::Order::Na,
                        e: Box::new(temp_var),
                    }),
                };

                // 5. Deallocate temporary
                let stmt_dead = code::PrimStmt::LocalDead(temp_name);

                Ok(vec![stmt_live, stmt_store, stmt_cas, stmt_old, stmt_dead])
            },

            AtomicIntrinsicKind::Fence => {
                let dest_place = self.translate_place(destination)?;
                Ok(vec![code::PrimStmt::Assign {
                    ot: lang::SynType::Unit.into(),
                    order: lang::Order::Na,
                    e1: Box::new(dest_place),
                    e2: Box::new(code::Expr::Literal(code::Literal::ZST)),
                }])
            },
        }
    }

    /// Translate a terminator.
    /// We pass the dying loans during this terminator. They need to be added at the right
    /// intermediate point.
    pub(crate) fn translate_terminator(
        &mut self,
        term: &mir::Terminator<'tcx>,
        loc: mir::Location,
        dying_loans: Vec<facts::Loan>,
    ) -> Result<code::Stmt, TranslationError<'tcx>> {
        let mut endlfts = self.generate_endlfts(dying_loans.into_iter());

        match &term.kind {
            mir::TerminatorKind::Goto { target } => self.translate_goto_like(&loc, *target),

            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                trace!("translating Call {:?}", term);
                if self.is_call_destination_panic(func) {
                    info!("Replacing call to std::panicking::begin_panic with Stuck");
                    return Ok(code::Stmt::Stuck);
                }
                if self.is_call_destination_discriminant(func) {
                    let op = &args[0].node;
                    let stmt = self.make_discriminant_shim(op, destination)?;
                    let goto = self.translate_goto_like(&loc, target.unwrap())?;

                    return Ok(code::Stmt::Prim(stmt, Box::new(goto)));
                }

                if let Some(kind) = self.try_classify_atomic_intrinsic(func)? {
                    info!("Translating atomic intrinsic: {kind:?}");

                    // Collect span for per-crate summary warning (Fence is a no-op, no approximation)
                    if !matches!(kind, AtomicIntrinsicKind::Fence) {
                        self.non_sc_atomic_spans.push(term.source_info.span);
                    }

                    let stmts = self.translate_atomic_intrinsic(kind, args, destination)?;
                    let goto = self.translate_goto_like(&loc, target.unwrap())?;

                    return Ok(code::Stmt::Prim(stmts, Box::new(goto)));
                }

                // Check for method call on #[rr::mode(atomic)] type
                if let Some((kind, ot, st)) = self.try_classify_atomic_method(func, args)? {
                    info!("Translating mode(atomic) method: {kind:?}");

                    if !matches!(kind, AtomicIntrinsicKind::Fence) {
                        self.non_sc_atomic_spans.push(term.source_info.span);
                    }

                    let stmts = self.translate_atomic_method(kind, ot, st, args, destination)?;
                    let goto = self.translate_goto_like(&loc, target.unwrap())?;

                    return Ok(code::Stmt::Prim(stmts, Box::new(goto)));
                }

                self.translate_function_call(func, args, destination, *target, loc, endlfts)
            },

            mir::TerminatorKind::Return => {
                // TODO: this requires additional handling for reborrows

                // read from the return place
                // Is this semantics accurate wrt what the intended MIR semantics is?
                // Possibly handle this differently by making the first argument of a function a dedicated
                // return place? See also discussion at https://github.com/rust-lang/rust/issues/71117
                let stmt = code::Stmt::Return(code::Expr::Move {
                    ot: (&self.return_synty).into(),
                    order: lang::Order::Na,
                    e: Box::new(code::Expr::Var(self.return_name.clone())),
                });

                // TODO is this right?
                Ok(code::Stmt::Prim(endlfts, Box::new(stmt)))
            },

            mir::TerminatorKind::SwitchInt { discr, targets } => {
                let (operand, _) = self.translate_operand(discr, true)?;
                let all_targets: &[mir::BasicBlock] = targets.all_targets();

                if self.get_type_of_operand(discr).is_bool() {
                    // we currently special-case this as Caesium has a built-in if and this is more
                    // convenient to handle for the type-checker

                    // implementation detail: the first index is the `false` branch, the second the
                    // `true` branch
                    let true_target = all_targets[1];
                    let false_target = all_targets[0];

                    let true_branch = self.translate_goto_like(&loc, true_target)?;
                    let false_branch = self.translate_goto_like(&loc, false_target)?;

                    let stmt = code::Stmt::If {
                        e: operand,
                        ot: lang::OpType::Bool,
                        s1: Box::new(true_branch),
                        s2: Box::new(false_branch),
                    };

                    // TODO: is this right?
                    return Ok(code::Stmt::Prim(endlfts, Box::new(stmt)));
                }

                //info!("switchint: {:?}", term.kind);
                let (operand, _) = self.translate_operand(discr, true)?;
                let ty = self.get_type_of_operand(discr);

                let mut target_map: BTreeMap<u128, usize> = BTreeMap::new();
                let mut translated_targets: Vec<code::Stmt> = Vec::new();

                for (idx, (tgt, bb)) in targets.iter().enumerate() {
                    let bb: mir::BasicBlock = bb;
                    let translated_target = self.translate_goto_like(&loc, bb)?;

                    target_map.insert(tgt, idx);
                    translated_targets.push(translated_target);
                }

                let translated_default = self.translate_goto_like(&loc, targets.otherwise())?;
                // TODO: need to put endlfts infront of gotos?

                let translated_ty = self.ty_translator.translate_type(ty)?;
                let specs::Type::Int(it) = translated_ty else {
                    return Err(TranslationError::UnknownError(
                        "SwitchInt switching on non-integer type".to_owned(),
                    ));
                };

                Ok(code::Stmt::Switch {
                    e: operand,
                    it,
                    index_map: target_map,
                    bs: translated_targets,
                    def: Box::new(translated_default),
                })
            },

            mir::TerminatorKind::Assert {
                cond,
                expected,
                target,
                ..
            } => {
                // this translation gets stuck on failure
                let (cond_translated, _) = self.translate_operand(cond, true)?;
                let comp = code::Expr::BinOp {
                    o: code::Binop::Eq,
                    ot1: lang::OpType::Bool,
                    ot2: lang::OpType::Bool,
                    e1: Box::new(cond_translated),
                    e2: Box::new(code::Expr::Literal(code::Literal::Bool(*expected))),
                };

                let stmt = self.translate_goto_like(&loc, *target)?;

                // TODO: should we really have this?
                endlfts.insert(0, code::PrimStmt::AssertS(Box::new(comp)));
                Ok(code::Stmt::Prim(endlfts, Box::new(stmt)))
            },

            mir::TerminatorKind::Drop { place, target, .. } => {
                let ty = self.get_type_of_place(place);
                self.register_drop_shim_for(ty.ty);

                let place_translated = self.translate_place(place)?;
                let _drope = code::Expr::DropE(Box::new(place_translated));

                let stmt = self.translate_goto_like(&loc, *target)?;

                Ok(code::Stmt::Prim(endlfts, Box::new(stmt)))
            },

            // just a goto for our purposes
            mir::TerminatorKind::FalseEdge { real_target, .. }
            // this is just a virtual edge for the borrowchecker, we can translate this to a normal goto
            | mir::TerminatorKind::FalseUnwind { real_target, .. } => {
                self.translate_goto_like(&loc, *real_target)
            },

            mir::TerminatorKind::TailCall { .. } => {
                Err(TranslationError::Unimplemented {
                    description: "implement TailCall".to_owned(),
                })
            },

            mir::TerminatorKind::Unreachable => Ok(code::Stmt::Stuck),

            mir::TerminatorKind::UnwindResume => Err(TranslationError::Unimplemented {
                description: "implement UnwindResume".to_owned(),
            }),

            mir::TerminatorKind::UnwindTerminate(_) => Err(TranslationError::Unimplemented {
                description: "implement UnwindTerminate".to_owned(),
            }),

            mir::TerminatorKind::CoroutineDrop
            | mir::TerminatorKind::InlineAsm { .. }
            | mir::TerminatorKind::Yield { .. } => Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "RefinedRust does currently not support this kind of terminator (got: {:?})",
                    term
                ),
            }),
        }
    }
}
