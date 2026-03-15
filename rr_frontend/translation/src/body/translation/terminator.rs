// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::BTreeMap;

use log::{info, trace, warn};
use radium::{code, coq, lang, specs};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::type_ir::TypeFolder as _;

use super::{TX, is_ordering_type};
use rr_rustc_interface::span;

use crate::base::*;
use crate::environment::borrowck::facts;
use crate::{regions, search, types};

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
fn strip_atomic_ordering_suffix(name: &str) -> (&str, Option<lang::RustOrdering>) {
    const SUFFIXES: &[(&str, lang::RustOrdering)] = &[
        ("_seqcst", lang::RustOrdering::SeqCst),
        ("_acqrel", lang::RustOrdering::AcqRel),
        ("_acquire", lang::RustOrdering::Acquire),
        ("_release", lang::RustOrdering::Release),
        ("_relaxed", lang::RustOrdering::Relaxed),
        ("_unordered", lang::RustOrdering::Unordered),
    ];
    for (suffix, ordering) in SUFFIXES {
        if let Some(base) = name.strip_suffix(suffix) {
            return (base, Some(*ordering));
        }
    }
    (name, None)
}


/// Parse a [`lang::SynType`] from its `Display` representation.
///
/// Used to reconstruct the inner field type for remote atomic ADTs from the
/// string stored in [`AdtShimInfo`].
fn parse_syn_type_tag(s: &str) -> Option<lang::SynType> {
    match s {
        "BoolSynType" => Some(lang::SynType::Bool),
        "CharSynType" => Some(lang::SynType::Char),
        "PtrSynType" => Some(lang::SynType::Ptr),
        "FnPtrSynType" => Some(lang::SynType::FnPtr),
        "UnitSynType" => Some(lang::SynType::Unit),
        _ if s.starts_with("(IntSynType ") && s.ends_with(')') => {
            let it_str = &s[12..s.len() - 1];
            let it = match it_str {
                "I8" => lang::IntType::I8,
                "I16" => lang::IntType::I16,
                "I32" => lang::IntType::I32,
                "I64" => lang::IntType::I64,
                "I128" => lang::IntType::I128,
                "U8" => lang::IntType::U8,
                "U16" => lang::IntType::U16,
                "U32" => lang::IntType::U32,
                "U64" => lang::IntType::U64,
                "U128" => lang::IntType::U128,
                "ISize" => lang::IntType::ISize,
                "USize" => lang::IntType::USize,
                _ => return None,
            };
            Some(lang::SynType::Int(it))
        },
        _ => None,
    }
}

/// Classify an atomic intrinsic by name.
///
/// Handles both new-style (`atomic_load`) and old-style (`atomic_load_seqcst`)
/// intrinsic names. Returns the operation kind and the original Rust ordering
/// (if extractable from the suffix). `None` ordering means new-style intrinsic
/// without ordering suffix (implicitly SeqCst).
/// The caller must treat `None` kind as an error if the name starts with `"atomic_"`.
fn classify_atomic_intrinsic(name: &str) -> Option<(AtomicIntrinsicKind, Option<lang::RustOrdering>)> {
    let (name, ordering) = strip_atomic_ordering_suffix(name);
    let kind = match name {
        "atomic_load" => AtomicIntrinsicKind::Load,
        "atomic_store" => AtomicIntrinsicKind::Store,
        "atomic_cxchg" | "atomic_cxchgweak" => AtomicIntrinsicKind::Cxchg,
        "atomic_xchg" => AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::Xchg),
        "atomic_xadd" => AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::Add),
        "atomic_xsub" => AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::Sub),
        "atomic_and" => AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::And),
        "atomic_or" => AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::Or),
        "atomic_xor" => AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::Xor),
        "atomic_nand" => AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::Nand),
        "atomic_max" => AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::MaxSigned),
        "atomic_min" => AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::MinSigned),
        "atomic_umax" => AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::MaxUnsigned),
        "atomic_umin" => AtomicIntrinsicKind::Rmw(lang::AtomicRmwOp::MinUnsigned),
        "atomic_fence" | "atomic_singlethreadfence" => AtomicIntrinsicKind::Fence,
        _ => return None,
    };
    Some((kind, ordering))
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
        if let Some(panic_id_std) = search::try_resolve_did(self.tcx, &["std", "panicking", "begin_panic"]) {
            if Self::check_call_destination(func, panic_id_std) {
                return true;
            }
        } else {
            warn!("Failed to determine DefId of std::panicking::begin_panic");
        }

        if let Some(panic_id_core) = search::try_resolve_did(self.tcx, &["core", "panicking", "panic"]) {
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
            search::try_resolve_did(self.tcx, &["core", "intrinsics", "discriminant_value"])
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
    ) -> Result<Option<(AtomicIntrinsicKind, Option<lang::RustOrdering>)>, TranslationError<'tcx>> {
        let Some(did) = Self::extract_fn_def_id(func) else {
            return Ok(None);
        };

        let Some(intrinsic_def) = self.tcx.intrinsic(did) else {
            return Ok(None);
        };

        let name = intrinsic_def.name.as_str();
        if !name.starts_with("atomic_") {
            return Ok(None);
        }

        match classify_atomic_intrinsic(name) {
            Some((kind, ordering)) => Ok(Some((kind, ordering))),
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

    // ── Shared atomic Caesium emitters (used by both intrinsic and method paths) ──

    /// Filter out `Ordering` arguments from a method's argument list.
    ///
    /// For mode(atomic) user types (no Ordering params), this is a no-op — returns
    /// all args unchanged with `ordering = None`.
    /// For std shim types, removes Ordering args before translation so that
    /// arg indices match the mode(atomic) convention (args[0]=self, args[1]=value, etc.).
    fn filter_ordering_args(
        &self,
        args: &[span::source_map::Spanned<mir::Operand<'tcx>>],
    ) -> (Vec<span::source_map::Spanned<mir::Operand<'tcx>>>, Option<lang::RustOrdering>) {
        let mut filtered = Vec::with_capacity(args.len());
        let mut ordering = None;
        for arg in args {
            let arg_ty = self.get_type_of_operand(&arg.node);
            if is_ordering_type(self.tcx, arg_ty) {
                // TODO: extract actual Ordering variant from MIR operand for precise traceability.
                // For now, conservatively mark as SeqCst (no comment emitted, no warning).
                ordering = Some(lang::RustOrdering::SeqCst);
            } else {
                filtered.push(arg.clone());
            }
        }
        (filtered, ordering)
    }

    /// Generate a Coq comment preserving the original Rust ordering.
    /// Returns `None` for SeqCst (identity mapping) or unknown ordering.
    fn ordering_comment(ordering: Option<lang::RustOrdering>) -> Option<code::PrimStmt> {
        match ordering {
            Some(ord) if ord != lang::RustOrdering::SeqCst => {
                Some(code::PrimStmt::Comment(format!("Rust ordering: {ord} → SC")))
            },
            _ => None,
        }
    }

    /// Emit atomic load: `dest <-{ot, Na} !{ot, ScOrd}(ptr)`
    fn emit_atomic_load(
        ot: lang::OpType,
        ptr_expr: code::Expr,
        dest_place: code::Expr,
        ordering: Option<lang::RustOrdering>,
    ) -> Vec<code::PrimStmt> {
        let deref_expr = code::Expr::Deref {
            ot: ot.clone(),
            order: lang::Order::Sc,
            e: Box::new(ptr_expr),
        };
        let mut stmts = Vec::new();
        stmts.extend(Self::ordering_comment(ordering));
        stmts.push(code::PrimStmt::Assign {
            ot,
            order: lang::Order::Na,
            e1: Box::new(dest_place),
            e2: Box::new(deref_expr),
        });
        stmts
    }

    /// Emit atomic store: `ptr <-{ot, ScOrd} val; dest <-{UnitOp, Na} ZST`
    fn emit_atomic_store(
        ot: lang::OpType,
        ptr_expr: code::Expr,
        val_expr: code::Expr,
        dest_place: code::Expr,
        ordering: Option<lang::RustOrdering>,
    ) -> Vec<code::PrimStmt> {
        let mut stmts = Vec::new();
        stmts.extend(Self::ordering_comment(ordering));
        stmts.push(code::PrimStmt::Assign {
            ot,
            order: lang::Order::Sc,
            e1: Box::new(ptr_expr),
            e2: Box::new(val_expr),
        });
        stmts.push(code::PrimStmt::Assign {
            ot: lang::SynType::Unit.into(),
            order: lang::Order::Na,
            e1: Box::new(dest_place),
            e2: Box::new(code::Expr::Literal(code::Literal::ZST)),
        });
        stmts
    }

    /// Emit atomic RMW: `dest <-{ot, Na} AtomicRMW op ot (ptr) (val)`
    fn emit_atomic_rmw(
        rmw_op: lang::AtomicRmwOp,
        ot: lang::OpType,
        ptr_expr: code::Expr,
        val_expr: code::Expr,
        dest_place: code::Expr,
        ordering: Option<lang::RustOrdering>,
    ) -> Vec<code::PrimStmt> {
        let rmw_expr = code::Expr::AtomicRmw {
            op: rmw_op,
            ot: ot.clone(),
            target: Box::new(ptr_expr),
            arg: Box::new(val_expr),
        };
        let mut stmts = Vec::new();
        stmts.extend(Self::ordering_comment(ordering));
        stmts.push(code::PrimStmt::Assign {
            ot,
            order: lang::Order::Na,
            e1: Box::new(dest_place),
            e2: Box::new(rmw_expr),
        });
        stmts
    }

    /// Emit CAS with (T, bool) tuple return via 10-stmt bridge.
    /// Used by the intrinsic path (`atomic_cxchg` returns `(T, bool)`).
    ///   1.  `local_live __cas_expected`
    ///   2.  `__cas_expected <-{ot} expected_val`
    ///   3.  `local_live __cas_old`
    ///   4.  `__cas_old <-{ot} CAS(ot, target, copy(__cas_expected), desired)`
    ///   5.  `local_live __cas_result`
    ///   6.  `__cas_result <-{BoolOp} (copy __cas_old) =={ot,ot} (copy __cas_expected)`
    ///   7.  `dest <-{sls} StructInit sls [copy(__cas_old), copy(__cas_result)]`
    ///   8.  `local_dead __cas_result`
    ///   9.  `local_dead __cas_old`
    ///   10. `local_dead __cas_expected`
    fn emit_atomic_cas(
        &mut self,
        ot: lang::OpType,
        st: lang::SynType,
        target_ptr: code::Expr,
        expected_val: code::Expr,
        desired_val: code::Expr,
        destination: &mir::Place<'tcx>,
        ordering: Option<lang::RustOrdering>,
    ) -> Result<Vec<code::PrimStmt>, TranslationError<'tcx>> {
        let dest_pty = self.get_type_of_place(destination);
        let dest_lit = self
            .ty_translator
            .generate_structlike_use(dest_pty.ty, dest_pty.variant_index)?;
        let dest_sls = dest_lit.generate_raw_syn_type_term();
        let dest_place = self.translate_place(destination)?;

        let expected_name = "__cas_expected".to_owned();
        let expected_var = code::Expr::Var(expected_name.clone());
        let old_name = "__cas_old".to_owned();
        let old_var = code::Expr::Var(old_name.clone());
        let result_name = "__cas_result".to_owned();
        let result_var = code::Expr::Var(result_name.clone());

        // 1. local_live __cas_expected
        let stmt_live_expected = code::PrimStmt::LocalLive(code::Variable::new(
            expected_name.clone(),
            st.clone(),
        ));

        // 2. __cas_expected <-{ot} expected_val
        let stmt_store_expected = code::PrimStmt::Assign {
            ot: ot.clone(),
            order: lang::Order::Na,
            e1: Box::new(expected_var.clone()),
            e2: Box::new(expected_val),
        };

        // 3. local_live __cas_old
        let stmt_live_old = code::PrimStmt::LocalLive(code::Variable::new(
            old_name.clone(),
            st,
        ));

        // 4. __cas_old <-{ot} CAS(ot, target, copy(__cas_expected), desired)
        let cas_expr = code::Expr::Cas {
            ot: ot.clone(),
            target: Box::new(target_ptr),
            expected: Box::new(code::Expr::Copy {
                ot: ot.clone(),
                order: lang::Order::Na,
                e: Box::new(expected_var.clone()),
            }),
            desired: Box::new(desired_val),
        };
        let stmt_cas = code::PrimStmt::Assign {
            ot: ot.clone(),
            order: lang::Order::Na,
            e1: Box::new(old_var.clone()),
            e2: Box::new(cas_expr),
        };

        // 5. local_live __cas_result
        let stmt_live_result = code::PrimStmt::LocalLive(code::Variable::new(
            result_name.clone(),
            lang::SynType::Bool,
        ));

        // 6. __cas_result <-{BoolOp} (copy __cas_old) =={ot,ot} (copy __cas_expected)
        let eq_expr = code::Expr::BinOp {
            o: code::Binop::Eq,
            ot1: ot.clone(),
            ot2: ot.clone(),
            e1: Box::new(code::Expr::Copy {
                ot: ot.clone(),
                order: lang::Order::Na,
                e: Box::new(old_var.clone()),
            }),
            e2: Box::new(code::Expr::Copy {
                ot: ot.clone(),
                order: lang::Order::Na,
                e: Box::new(expected_var.clone()),
            }),
        };
        let stmt_eq = code::PrimStmt::Assign {
            ot: lang::OpType::Bool,
            order: lang::Order::Na,
            e1: Box::new(result_var.clone()),
            e2: Box::new(eq_expr),
        };

        // 7. dest <-{sls} StructInit sls [(0, copy __cas_old), (1, copy __cas_result)]
        let struct_init = code::Expr::StructInitE {
            sls: coq::term::App::new_lhs(dest_sls.to_string()),
            components: vec![
                (
                    "0".to_owned(),
                    code::Expr::Copy {
                        ot,
                        order: lang::Order::Na,
                        e: Box::new(old_var),
                    },
                ),
                (
                    "1".to_owned(),
                    code::Expr::Copy {
                        ot: lang::OpType::Bool,
                        order: lang::Order::Na,
                        e: Box::new(result_var),
                    },
                ),
            ],
        };
        let stmt_init = code::PrimStmt::Assign {
            ot: lang::OpType::UseOpAlg(coq::term::Term::Literal(dest_sls.to_string())),
            order: lang::Order::Na,
            e1: Box::new(dest_place),
            e2: Box::new(struct_init),
        };

        // 8-10. local_dead
        let stmt_dead_result = code::PrimStmt::LocalDead(result_name);
        let stmt_dead_old = code::PrimStmt::LocalDead(old_name);
        let stmt_dead_expected = code::PrimStmt::LocalDead(expected_name);

        let mut stmts = Vec::new();
        stmts.extend(Self::ordering_comment(ordering));
        stmts.extend([
            stmt_live_expected,
            stmt_store_expected,
            stmt_live_old,
            stmt_cas,
            stmt_live_result,
            stmt_eq,
            stmt_init,
            stmt_dead_result,
            stmt_dead_old,
            stmt_dead_expected,
        ]);
        Ok(stmts)
    }

    /// Emit CAS with `Result<T,T>` return type via IfE + EnumInitE bridge.
    /// Used by the method path (`compare_exchange` returns `Result<T,T>`).
    ///   1.  `local_live __cas_expected`
    ///   2.  `__cas_expected <-{ot} expected_val`
    ///   3.  `local_live __cas_old`
    ///   4.  `__cas_old <-{ot} CAS(ot, target, copy(__cas_expected), desired)`
    ///   5.  `local_live __cas_result`
    ///   6.  `__cas_result <-{BoolOp} (copy __cas_old) =={ot,ot} (copy __cas_expected)`
    ///   7.  `dest <-{els} IfE BoolOp (copy __cas_result)
    ///          (EnumInit els "Ok" rsen (StructInit ok_sls [("0", copy __cas_old)]))
    ///          (EnumInit els "Err" rsen (StructInit err_sls [("0", copy __cas_old)]))`
    ///   8.  `local_dead __cas_result`
    ///   9.  `local_dead __cas_old`
    ///   10. `local_dead __cas_expected`
    fn emit_atomic_cas_result(
        &mut self,
        ot: lang::OpType,
        st: lang::SynType,
        target_ptr: code::Expr,
        expected_val: code::Expr,
        desired_val: code::Expr,
        destination: &mir::Place<'tcx>,
        ordering: Option<lang::RustOrdering>,
    ) -> Result<Vec<code::PrimStmt>, TranslationError<'tcx>> {
        // Resolve destination as Result enum
        let dest_pty = self.get_type_of_place(destination);
        let ty::TyKind::Adt(adt_def, substs) = dest_pty.ty.kind() else {
            return Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "CAS Result destination must be an enum, got {:?}",
                    dest_pty.ty
                ),
            });
        };

        let variants: Vec<_> = adt_def.variants().iter().collect();
        if variants.len() != 2 {
            return Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "CAS Result enum must have exactly 2 variants, got {}",
                    variants.len()
                ),
            });
        }
        let ok_variant = &variants[0];
        let err_variant = &variants[1];

        // Enum use (Result<T,T> layout spec)
        let enum_use = self.ty_translator.generate_enum_use(*adt_def, substs)?;
        let els = enum_use.generate_raw_syn_type_term();
        let enum_def: code::RustEnumDef = enum_use.clone().try_into().map_err(|()| {
            TranslationError::UnknownError("failed to convert enum use to RustEnumDef".to_owned())
        })?;

        // Variant struct layouts
        let ok_use = self
            .ty_translator
            .generate_enum_variant_use(ok_variant.def_id, substs)?;
        let ok_sls = ok_use.generate_raw_syn_type_term();

        let err_use = self
            .ty_translator
            .generate_enum_variant_use(err_variant.def_id, substs)?;
        let err_sls = err_use.generate_raw_syn_type_term();

        let dest_place = self.translate_place(destination)?;

        let expected_name = "__cas_expected".to_owned();
        let expected_var = code::Expr::Var(expected_name.clone());
        let old_name = "__cas_old".to_owned();
        let old_var = code::Expr::Var(old_name.clone());
        let result_name = "__cas_result".to_owned();
        let result_var = code::Expr::Var(result_name.clone());

        // 1. local_live __cas_expected
        let stmt_live_expected = code::PrimStmt::LocalLive(code::Variable::new(
            expected_name.clone(),
            st.clone(),
        ));

        // 2. __cas_expected <-{ot} expected_val
        let stmt_store_expected = code::PrimStmt::Assign {
            ot: ot.clone(),
            order: lang::Order::Na,
            e1: Box::new(expected_var.clone()),
            e2: Box::new(expected_val),
        };

        // 3. local_live __cas_old
        let stmt_live_old = code::PrimStmt::LocalLive(code::Variable::new(
            old_name.clone(),
            st,
        ));

        // 4. __cas_old <-{ot} CAS(ot, target, copy(__cas_expected), desired)
        let cas_expr = code::Expr::Cas {
            ot: ot.clone(),
            target: Box::new(target_ptr),
            expected: Box::new(code::Expr::Copy {
                ot: ot.clone(),
                order: lang::Order::Na,
                e: Box::new(expected_var.clone()),
            }),
            desired: Box::new(desired_val),
        };
        let stmt_cas = code::PrimStmt::Assign {
            ot: ot.clone(),
            order: lang::Order::Na,
            e1: Box::new(old_var.clone()),
            e2: Box::new(cas_expr),
        };

        // 5. local_live __cas_result
        let stmt_live_result = code::PrimStmt::LocalLive(code::Variable::new(
            result_name.clone(),
            lang::SynType::Bool,
        ));

        // 6. __cas_result <-{BoolOp} (copy __cas_old) =={ot,ot} (copy __cas_expected)
        let eq_expr = code::Expr::BinOp {
            o: code::Binop::Eq,
            ot1: ot.clone(),
            ot2: ot.clone(),
            e1: Box::new(code::Expr::Copy {
                ot: ot.clone(),
                order: lang::Order::Na,
                e: Box::new(old_var.clone()),
            }),
            e2: Box::new(code::Expr::Copy {
                ot: ot.clone(),
                order: lang::Order::Na,
                e: Box::new(expected_var.clone()),
            }),
        };
        let stmt_eq = code::PrimStmt::Assign {
            ot: lang::OpType::Bool,
            order: lang::Order::Na,
            e1: Box::new(result_var.clone()),
            e2: Box::new(eq_expr),
        };

        // Helper: copy __cas_old expression
        let copy_old = |ot: &lang::OpType| code::Expr::Copy {
            ot: ot.clone(),
            order: lang::Order::Na,
            e: Box::new(old_var.clone()),
        };

        // 7. dest <-{els} IfE BoolOp (copy __cas_result)
        //      (EnumInit els "Ok" rsen (StructInit ok_sls [("0", copy __cas_old)]))
        //      (EnumInit els "Err" rsen (StructInit err_sls [("0", copy __cas_old)]))
        let ok_init = code::Expr::EnumInitE {
            els: coq::term::App::new_lhs(els.to_string()),
            variant: ok_variant.name.to_string(),
            ty: enum_def.clone(),
            initializer: Box::new(code::Expr::StructInitE {
                sls: coq::term::App::new_lhs(ok_sls.to_string()),
                components: vec![("0".to_owned(), copy_old(&ot))],
            }),
        };

        let err_init = code::Expr::EnumInitE {
            els: coq::term::App::new_lhs(els.to_string()),
            variant: err_variant.name.to_string(),
            ty: enum_def,
            initializer: Box::new(code::Expr::StructInitE {
                sls: coq::term::App::new_lhs(err_sls.to_string()),
                components: vec![("0".to_owned(), copy_old(&ot))],
            }),
        };

        let if_expr = code::Expr::If {
            ot: lang::OpType::Bool,
            e1: Box::new(code::Expr::Copy {
                ot: lang::OpType::Bool,
                order: lang::Order::Na,
                e: Box::new(result_var.clone()),
            }),
            e2: Box::new(ok_init),
            e3: Box::new(err_init),
        };

        let stmt_init = code::PrimStmt::Assign {
            ot: lang::OpType::UseOpAlg(coq::term::Term::Literal(els.to_string())),
            order: lang::Order::Na,
            e1: Box::new(dest_place),
            e2: Box::new(if_expr),
        };

        // 8-10. local_dead
        let stmt_dead_result = code::PrimStmt::LocalDead(result_name);
        let stmt_dead_old = code::PrimStmt::LocalDead(old_name);
        let stmt_dead_expected = code::PrimStmt::LocalDead(expected_name);

        let mut stmts = Vec::new();
        stmts.extend(Self::ordering_comment(ordering));
        stmts.extend([
            stmt_live_expected,
            stmt_store_expected,
            stmt_live_old,
            stmt_cas,
            stmt_live_result,
            stmt_eq,
            stmt_init,
            stmt_dead_result,
            stmt_dead_old,
            stmt_dead_expected,
        ]);
        Ok(stmts)
    }

    /// Emit fence (no-op in SC interleaving model): `dest <-{UnitOp, Na} ZST`
    fn emit_atomic_fence(dest_place: code::Expr, ordering: Option<lang::RustOrdering>) -> Vec<code::PrimStmt> {
        let mut stmts = Vec::new();
        stmts.extend(Self::ordering_comment(ordering));
        stmts.push(code::PrimStmt::Assign {
            ot: lang::SynType::Unit.into(),
            order: lang::Order::Na,
            e1: Box::new(dest_place),
            e2: Box::new(code::Expr::Literal(code::Literal::ZST)),
        });
        stmts
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
        ordering: Option<lang::RustOrdering>,
    ) -> Result<Vec<code::PrimStmt>, TranslationError<'tcx>> {
        match kind {
            AtomicIntrinsicKind::Load => {
                let ot = self.get_pointee_op_type(&args[0].node)?;
                let (ptr_expr, _) = self.translate_operand(&args[0].node, true)?;
                let dest_place = self.translate_place(destination)?;
                Ok(Self::emit_atomic_load(ot, ptr_expr, dest_place, ordering))
            },

            AtomicIntrinsicKind::Store => {
                let ot = self.get_pointee_op_type(&args[0].node)?;
                let (ptr_expr, _) = self.translate_operand(&args[0].node, true)?;
                let (val_expr, _) = self.translate_operand(&args[1].node, true)?;
                let dest_place = self.translate_place(destination)?;
                Ok(Self::emit_atomic_store(ot, ptr_expr, val_expr, dest_place, ordering))
            },

            AtomicIntrinsicKind::Rmw(rmw_op) => {
                let ot = self.get_pointee_op_type(&args[0].node)?;
                let (ptr_expr, _) = self.translate_operand(&args[0].node, true)?;
                let (val_expr, _) = self.translate_operand(&args[1].node, true)?;
                let dest_place = self.translate_place(destination)?;
                Ok(Self::emit_atomic_rmw(rmw_op, ot, ptr_expr, val_expr, dest_place, ordering))
            },

            AtomicIntrinsicKind::Cxchg => {
                let ptr_ty = self.get_type_of_operand(&args[0].node);
                let ty::TyKind::RawPtr(pointee_ty, _) = ptr_ty.kind() else {
                    return Err(TranslationError::UnsupportedFeature {
                        description: format!(
                            "expected raw pointer for atomic CAS target, got {ptr_ty:?}"
                        ),
                    });
                };
                let st = self.ty_translator.translate_type_to_syn_type(*pointee_ty)?;
                let ot: lang::OpType = (&st).into();

                let (target_ptr, _) = self.translate_operand(&args[0].node, true)?;
                let (expected_val, _) = self.translate_operand(&args[1].node, true)?;
                let (desired_val, _) = self.translate_operand(&args[2].node, true)?;

                self.emit_atomic_cas(ot, st, target_ptr, expected_val, desired_val, destination, ordering)
            },

            AtomicIntrinsicKind::Fence => {
                let dest_place = self.translate_place(destination)?;
                Ok(Self::emit_atomic_fence(dest_place, ordering))
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

        let tcx = self.tcx;

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

        // Determine inner type: local registry (user-defined) or remote shim
        let (inner_st, ot, signed);
        if self.ty_translator.translator.is_variant_atomic(variant.def_id) {
            // LOCAL atomic: read field type from struct definition
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
            inner_st = self.ty_translator.translate_type_to_syn_type(inner_ty)?;
            ot = (&inner_st).into();
            signed = matches!(inner_ty.kind(), ty::TyKind::Int(_));
        } else {
            // REMOTE atomic: check shim info for atomic inner type
            let adt_did = adt_def.did();
            let Some(lit) = self.ty_translator.translator.lookup_adt_shim(adt_did) else {
                return Ok(None);
            };
            if !lit.info.is_atomic() {
                return Ok(None);
            }

            if !substs.is_empty() {
                // Generic atomic struct (e.g. AtomicPtr<T> or future Atomic<T>).
                // Derive inner type from field, unwrapping single-data-field wrappers
                // (UnsafeCell, alignment wrappers). If unwrap reaches a non-ADT
                // primitive, use it (covers old-style AtomicPtr<T> where field =
                // UnsafeCell<*mut T>). Otherwise fall back to substs[0] which is the
                // semantic type (covers new-style Atomic<T> where storage may differ
                // from T, e.g. bool stored as Align1<u8>).
                let inner_field = variant.fields.iter().next().ok_or_else(|| TranslationError::UnsupportedFeature {
                    description: format!(
                        "generic atomic {} has no fields",
                        tcx.def_path_str(adt_def.did())
                    ),
                })?;
                let mut unwrapped = inner_field.ty(tcx, substs);
                while let ty::TyKind::Adt(wrapper_def, wrapper_substs) = unwrapped.kind() {
                    let wrapper_variant = wrapper_def.variants().iter().next().unwrap();
                    let data_fields: Vec<_> = wrapper_variant.fields.iter().filter(|f| {
                        let ft = f.ty(tcx, *wrapper_substs);
                        !matches!(ft.kind(), ty::TyKind::Adt(d, _) if d.is_phantom_data())
                            && !ft.is_unit()
                    }).collect();
                    if data_fields.len() != 1 {
                        break;
                    }
                    unwrapped = data_fields[0].ty(tcx, *wrapper_substs);
                }
                let inner_ty = if matches!(unwrapped.kind(),
                    ty::TyKind::Int(_) | ty::TyKind::Uint(_) | ty::TyKind::Bool |
                    ty::TyKind::RawPtr(_, _) | ty::TyKind::Ref(_, _, _))
                {
                    unwrapped
                } else {
                    substs[0].as_type().ok_or_else(|| TranslationError::UnsupportedFeature {
                        description: format!(
                            "expected type argument for generic atomic {}",
                            tcx.def_path_str(adt_def.did())
                        ),
                    })?
                };
                inner_st = self.ty_translator.translate_type_to_syn_type(inner_ty)?;
                ot = (&inner_st).into();
                signed = matches!(inner_ty.kind(), ty::TyKind::Int(_));
            } else {
                // Concrete atomic struct (e.g. AtomicU8 on older nightlies).
                // Inner type from shim's static atomic_inner_st.
                let Some(st_str) = lit.info.atomic_inner_st() else {
                    return Ok(None);
                };
                inner_st = parse_syn_type_tag(st_str).ok_or_else(|| TranslationError::UnsupportedFeature {
                    description: format!(
                        "unrecognized atomic inner type '{st_str}' in shim for {}",
                        tcx.def_path_str(adt_def.did())
                    ),
                })?;
                ot = (&inner_st).into();
                signed = matches!(&inner_st,
                    lang::SynType::Int(lang::IntType::I8 | lang::IntType::I16 | lang::IntType::I32 |
                                       lang::IntType::I64 | lang::IntType::I128 | lang::IntType::ISize));
            }
        }
        let method_name = tcx.item_name(did);

        match classify_atomic_method(method_name.as_str(), signed) {
            Some(kind) => Ok(Some((kind, ot, inner_st))),
            None => {
                if method_name.as_str() == "fetch_update" {
                    return Err(TranslationError::UnsupportedFeature {
                        description: format!(
                            "fetch_update on {} requires closure lowering and is not supported",
                            tcx.def_path_str(adt_def.did())
                        ),
                    });
                }
                Ok(None)
            },
        }
    }

    /// Translate an atomic method call on a `#[rr::mode(atomic)]` type to Caesium primitives.
    ///
    /// Delegates to shared `emit_atomic_*` functions (same code as intrinsic path).
    fn translate_atomic_method(
        &mut self,
        kind: AtomicIntrinsicKind,
        ot: lang::OpType,
        st: lang::SynType,
        args: &[span::source_map::Spanned<mir::Operand<'tcx>>],
        destination: &mir::Place<'tcx>,
        ordering: Option<lang::RustOrdering>,
    ) -> Result<Vec<code::PrimStmt>, TranslationError<'tcx>> {
        match kind {
            AtomicIntrinsicKind::Load => {
                let (ptr_expr, _) = self.translate_operand(&args[0].node, true)?;
                let dest_place = self.translate_place(destination)?;
                Ok(Self::emit_atomic_load(ot, ptr_expr, dest_place, ordering))
            },

            AtomicIntrinsicKind::Store => {
                let (ptr_expr, _) = self.translate_operand(&args[0].node, true)?;
                let (val_expr, _) = self.translate_operand(&args[1].node, true)?;
                let dest_place = self.translate_place(destination)?;
                Ok(Self::emit_atomic_store(ot, ptr_expr, val_expr, dest_place, ordering))
            },

            AtomicIntrinsicKind::Rmw(rmw_op) => {
                let (ptr_expr, _) = self.translate_operand(&args[0].node, true)?;
                let (val_expr, _) = self.translate_operand(&args[1].node, true)?;
                let dest_place = self.translate_place(destination)?;
                Ok(Self::emit_atomic_rmw(rmw_op, ot, ptr_expr, val_expr, dest_place, ordering))
            },

            AtomicIntrinsicKind::Cxchg => {
                let (target_ptr, _) = self.translate_operand(&args[0].node, true)?;
                let (expected_val, _) = self.translate_operand(&args[1].node, true)?;
                let (desired_val, _) = self.translate_operand(&args[2].node, true)?;
                self.emit_atomic_cas_result(ot, st, target_ptr, expected_val, desired_val, destination, ordering)
            },

            AtomicIntrinsicKind::Fence => {
                let dest_place = self.translate_place(destination)?;
                Ok(Self::emit_atomic_fence(dest_place, ordering))
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

                if let Some((kind, ordering)) = self.try_classify_atomic_intrinsic(func)? {
                    info!("Translating atomic intrinsic: {kind:?}");

                    // Warn only for non-SeqCst orderings (SeqCst = identity mapping, no approximation)
                    let is_non_sc = ordering.is_some_and(|o| o != lang::RustOrdering::SeqCst);
                    if is_non_sc && !matches!(kind, AtomicIntrinsicKind::Fence) {
                        self.non_sc_atomic_spans.push(term.source_info.span);
                    }

                    let stmts = self.translate_atomic_intrinsic(kind, args, destination, ordering)?;
                    let goto = self.translate_goto_like(&loc, target.unwrap())?;

                    return Ok(code::Stmt::Prim(stmts, Box::new(goto)));
                }

                // Check for method call on #[rr::mode(atomic)] type
                if let Some((kind, ot, st)) = self.try_classify_atomic_method(func, args)? {
                    info!("Translating mode(atomic) method: {kind:?}");

                    // Filter Ordering args (no-op for mode(atomic), removes for std shim).
                    let (filtered_args, ordering) = self.filter_ordering_args(args);

                    // Warn only for non-SeqCst orderings
                    let is_non_sc = ordering.is_some_and(|o| o != lang::RustOrdering::SeqCst);
                    if is_non_sc && !matches!(kind, AtomicIntrinsicKind::Fence) {
                        self.non_sc_atomic_spans.push(term.source_info.span);
                    }

                    let stmts = self.translate_atomic_method(kind, ot, st, &filtered_args, destination, ordering)?;
                    let goto = self.translate_goto_like(&loc, target.unwrap())?;

                    return Ok(code::Stmt::Prim(stmts, Box::new(goto)));
                }

                self.translate_function_call(func, args, destination, *target, loc, endlfts)
            },

            mir::TerminatorKind::Return => {
                let return_synty = self.ty_translator.translate_type_to_syn_type(self.return_ty)?;

                // compute which lifetimes depend on local borrows
                let mut region_folder = regions::TyRegionCollectFolder::new(self.tcx);
                region_folder.fold_ty(self.return_ty);
                let regions_in_return = region_folder.get_regions();

                let mut lifetimes_to_extend = Vec::new();
                for r in regions_in_return {
                    //let atomic = self.info.mk_atomic_region(r);
                    lifetimes_to_extend.push(self.ty_translator.translate_region_var(r)?);
                }
                let stmt_annots: Vec<_> = lifetimes_to_extend.into_iter().map(code::Annotation::ExtendLft).collect();
                endlfts.insert(0, code::PrimStmt::Annot {
                    a: stmt_annots,
                    why: Some("return".to_owned()),
                });

                // read from the return place
                // Is this semantics accurate wrt what the intended MIR semantics is?
                // Possibly handle this differently by making the first argument of a function a dedicated
                // return place? See also discussion at https://github.com/rust-lang/rust/issues/71117
                let stmt = code::Stmt::Return(code::Expr::Move {
                    ot: (&return_synty).into(),
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
