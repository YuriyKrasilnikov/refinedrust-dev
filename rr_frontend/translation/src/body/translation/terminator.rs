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
use rr_rustc_interface::type_ir::TypeFolder as _;

use super::TX;
use crate::base::*;
use crate::environment::borrowck::facts;
use crate::{regions, search, types};

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
            e1: Box::new(translated_place),
            e2: Box::new(discriminant_acc),
        };

        Ok(vec![assign])
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

                self.translate_function_call(func, args, destination, *target, loc, endlfts)
            },

            mir::TerminatorKind::Return => {
                let return_synty = self.ty_translator.translate_type_to_syn_type(self.return_ty)?;

                // compute which lifetimes depend on local borrows
                let mut region_folder = regions::TyRegionCollectFolder::new(self.env.tcx());
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
