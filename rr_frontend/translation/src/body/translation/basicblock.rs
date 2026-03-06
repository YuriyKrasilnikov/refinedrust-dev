// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::BTreeSet;

use log::{info, trace};
use radium::{code, lang};
use rr_rustc_interface::middle::{mir, ty};

use super::TX;
use crate::base::*;
use crate::{procedures, regions};

#[expect(clippy::multiple_inherent_impl)]
impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Translate a single basic block.
    pub(crate) fn translate_basic_block(
        &mut self,
        bb_idx: mir::BasicBlock,
        bb: &mir::BasicBlockData<'tcx>,
    ) -> Result<code::Stmt, TranslationError<'tcx>> {
        let mut prim_stmts = Vec::new();

        for (idx, stmt) in bb.statements.iter().enumerate() {
            let loc = mir::Location {
                block: bb_idx,
                statement_index: idx,
            };

            // get all dying loans, and emit endlfts for these.
            // We loop over all predecessor locations, since some loans may end at the start of a
            // basic block (in particular related to NLL stuff)
            let pred = self.get_loc_predecessors(loc);
            let mut dying_loans = BTreeSet::new();
            for p in pred {
                let dying_between = self.info.get_loans_dying_between(p, loc, false);
                for l in &dying_between {
                    dying_loans.insert(*l);
                }
                // also include zombies
                let dying_between = self.info.get_loans_dying_between(p, loc, true);
                for l in &dying_between {
                    dying_loans.insert(*l);
                }
            }
            // we prepend them before the current statement
            prim_stmts.extend(self.generate_endlfts(dying_loans.into_iter().rev()));

            match &stmt.kind {
                mir::StatementKind::Assign(b) => {
                    let (plc, val) = b.as_ref();

                    if (self.is_spec_closure_local(plc.local)?).is_some() {
                        info!("skipping assignment to spec closure local: {:?}", plc);
                    } else {
                        let rhs_ty = val.ty(&self.proc.get_mir().local_decls, self.tcx);

                        let borrow_annots = regions::assignment::get_assignment_loan_annots(
                            &mut self.inclusion_tracker, &self.ty_translator,
                            loc, val);


                        // TODO; maybe move this to rvalue
                        let composite_annots = regions::composite::get_composite_rvalue_creation_annots(
                            self.tcx, &mut self.inclusion_tracker, &self.ty_translator, loc, rhs_ty);

                        let plc_ty = self.get_type_of_place(plc);
                        let plc_strongly_writeable = !self.check_place_below_reference(plc);
                        let assignment_annots =
                            regions::assignment::get_assignment_annots(
                                self.tcx, &mut self.inclusion_tracker, &self.ty_translator,
                                loc, plc_strongly_writeable, plc_ty, rhs_ty);

                        trace!("assignment at point {loc:?}: got assignment_annots={assignment_annots:?}");

                        let (unconstrained_annots, unconstrained_hints) = regions::assignment::make_unconstrained_region_annotations(
                            &mut self.inclusion_tracker, &self.ty_translator, assignment_annots.unconstrained_regions, loc,
                            Some(val))?;
                        for hint in unconstrained_hints {
                            self.translated_fn.add_unconstrained_lft_hint(hint);
                        }


                        prim_stmts.push(code::PrimStmt::Annot{
                            a: unconstrained_annots,
                            why: Some("assignment (unconstrained)".to_owned()),
                        });

                        prim_stmts.push(code::PrimStmt::Annot{
                            a: composite_annots,
                            why: Some("composite".to_owned()),
                        });

                        prim_stmts.push(code::PrimStmt::Annot{
                            a: borrow_annots,
                            why: Some("borrow".to_owned()),
                        });

                        prim_stmts.push(code::PrimStmt::Annot{
                            a: assignment_annots.new_dyn_inclusions,
                            why: Some("assignment".to_owned()),
                        });


                        let (e, _) = self.translate_rvalue(loc, val)?;
                        let translated_val = code::Expr::with_optional_annotation(
                            e,
                            assignment_annots.expr_annot,
                            Some("assignment".to_owned()),
                        );
                        let translated_place = self.translate_place(plc)?;
                        let synty = self.ty_translator.translate_type_to_syn_type(plc_ty.ty)?;
                        prim_stmts.push(code::PrimStmt::Assign {
                            ot: synty.into(),
                            e1: Box::new(translated_place),
                            e2: Box::new(translated_val),
                        });

                        prim_stmts.push(code::PrimStmt::Annot{
                            a: assignment_annots.stmt_annot,
                            why: Some("post-assignment".to_owned()),
                        });
                    }
                },

                mir::StatementKind::FakeRead(b) => {
                    // we can probably ignore this, but I'm not sure
                    info!("Ignoring FakeRead: {:?}", b);
                },

                mir::StatementKind::Intrinsic(intrinsic) => {
                    match intrinsic.as_ref() {
                        mir::NonDivergingIntrinsic::Assume(_) => {
                            // ignore
                            info!("Ignoring Assume: {:?}", intrinsic);
                        },
                        mir::NonDivergingIntrinsic::CopyNonOverlapping(_) => {
                            return Err(TranslationError::UnsupportedFeature {
                                description: "RefinedRust does currently not support the CopyNonOverlapping Intrinsic".to_owned(),
                            });
                        },
                    }
                },

                mir::StatementKind::PlaceMention(place) => {
                    // TODO: this is missed UB
                    info!("Ignoring PlaceMention: {:?}", place);
                },

                mir::StatementKind::SetDiscriminant {
                    place: _place,
                    variant_index: _variant_index,
                } => {
                    // TODO
                    return Err(TranslationError::UnsupportedFeature {
                        description: "RefinedRust does currently not support SetDiscriminant".to_owned(),
                    });
                },

                | mir::StatementKind::StorageLive(l) => {
                    let local_decls = &self.proc.get_mir().local_decls;
                    let local_decl = local_decls.get(*l).unwrap();
                    let ty = local_decl.ty;
                    let translated_ty = self.ty_translator.translate_type(ty)?;
                    let translated_st: lang::SynType = translated_ty.into();

                    if let Some(local_name) = self.variable_map.get(l) {
                        let var = code::Variable::new(local_name.to_owned(), translated_st);
                        prim_stmts.push(code::PrimStmt::LocalLive(var));
                    } else {
                        let ty::TyKind::Closure(did, _) = ty.kind() else {
                            unreachable!()
                        };
                        assert!(self.procedure_registry.lookup_function_mode(*did).is_some_and(procedures::Mode::is_ignore));
                    }
                },

                | mir::StatementKind::StorageDead(l) => {
                    let local_decls = &self.proc.get_mir().local_decls;
                    let local_decl = local_decls.get(*l).unwrap();
                    let ty = local_decl.ty;

                    if let Some(local_name) = self.variable_map.get(l) {
                        prim_stmts.push(code::PrimStmt::LocalDead(local_name.to_owned()));
                    } else {
                        let ty::TyKind::Closure(did, _) = ty.kind() else {
                            unreachable!()
                        };
                        assert!(self.procedure_registry.lookup_function_mode(*did).is_some_and(procedures::Mode::is_ignore));
                    }
                },

                // don't need that info
                | mir::StatementKind::AscribeUserType(_, _)
                // don't need that
                | mir::StatementKind::Coverage(_)
                // no-op
                | mir::StatementKind::ConstEvalCounter
                // ignore
                | mir::StatementKind::Nop
                // just ignore
                | mir::StatementKind::BackwardIncompatibleDropHint { .. }
                // just ignore retags
                | mir::StatementKind::Retag(_, _) => (),
            }
        }

        let idx = bb.statements.len();
        let loc = mir::Location {
            block: bb_idx,
            statement_index: idx,
        };
        let dying = self.info.get_dying_loans(loc);
        // TODO zombie?
        let _dying_zombie = self.info.get_dying_zombie_loans(loc);
        let all_dying_loans: BTreeSet<_> = dying.into_iter().collect();
        let cont_stmt: code::Stmt =
            self.translate_terminator(bb.terminator(), loc, all_dying_loans.into_iter().rev().collect())?;

        let cont_stmt = code::Stmt::Prim(prim_stmts, Box::new(cont_stmt));

        Ok(cont_stmt)
    }

    /// Get predecessors in the CFG.
    fn get_loc_predecessors(&self, loc: mir::Location) -> Vec<mir::Location> {
        if loc.statement_index > 0 {
            let pred = mir::Location {
                block: loc.block,
                statement_index: loc.statement_index - 1,
            };
            vec![pred]
        } else {
            // check for gotos that go to this basic block
            let pred_bbs = self.proc.predecessors(loc.block);
            let basic_blocks = &self.proc.get_mir().basic_blocks;
            pred_bbs
                .iter()
                .map(|bb| {
                    let data = &basic_blocks[*bb];
                    mir::Location {
                        block: *bb,
                        statement_index: data.statements.len(),
                    }
                })
                .collect()
        }
    }
}
