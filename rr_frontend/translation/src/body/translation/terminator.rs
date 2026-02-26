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
#[derive(Debug)]
enum AtomicIntrinsicKind {
    Load,
    Store,
    Rmw(lang::AtomicRmwOp),
    /// Strong and weak CAS are equivalent in the SC interleaving model.
    Cxchg,
    Fence,
}

/// Classify an atomic intrinsic by its exact name.
///
/// Returns `None` for names not recognized as atomic intrinsics.
/// The caller must treat `None` as an error if the name starts with `"atomic_"`.
fn classify_atomic_intrinsic(name: &str) -> Option<AtomicIntrinsicKind> {
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

    /// Extract DefId from a function call operand.
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

    /// Extract the pointee OpType from a raw pointer operand.
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
                // Caesium CAS returns bool, Rust returns (T, bool).
                // Requires multi-step shim with field projection.
                Err(TranslationError::Unimplemented {
                    description: "atomic compare_exchange translation \
                                  (CAS return type mismatch: Caesium returns bool, \
                                  Rust returns (T, bool))"
                        .to_owned(),
                })
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
                    let stmts = self.translate_atomic_intrinsic(kind, args, destination)?;
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
