// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use log::{info, trace};
use radium::{code, specs};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::span;

use super::TX;
use crate::base::*;
use crate::environment::mir_analyses::initialization;
use crate::spec_parsers::loop_attr_parser::{LoopAttrParser as _, LoopIteratorInfo, VerboseLoopAttrParser};
use crate::{attrs, environment, search, types};

#[expect(clippy::multiple_inherent_impl)]
impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    fn check_operand_call_dest(&self, op: &mir::Operand<'tcx>) -> Option<DefId> {
        let ty = self.get_type_of_operand(op);
        match ty.kind() {
            ty::TyKind::FnDef(did, _) => Some(*did),
            _ => None,
        }
    }

    fn find_origin_of_mut_bor(&self, var: mir::Local, bb: mir::BasicBlock) -> mir::Local {
        let proc = self.proc;
        let mir = proc.get_mir();
        let bb_data = &mir.basic_blocks[bb];
        let stmts = &bb_data.statements;

        let mut current_var = var;
        for stmt in stmts.iter().rev() {
            if let mir::StatementKind::Assign(assign) = &stmt.kind {
                let plc = &assign.0;
                let val = &assign.1;

                if plc.local != current_var {
                    continue;
                }

                assert!(plc.projection.is_empty());
                // find the RHS
                let mir::Rvalue::Ref(_, _, plc) = val else {
                    unimplemented!();
                };

                // the place might directly refer to the destination variable or be a Deref due to reborrow
                if plc.projection.is_empty() {
                    current_var = plc.local;
                } else if plc.projection.len() == 1 {
                    current_var = plc.local;

                    assert!(matches!(plc.projection[0], mir::ProjectionElem::Deref));
                } else {
                    unimplemented!();
                }
            }
        }

        current_var
    }

    fn check_for_iter_next(
        &self,
        bb: mir::BasicBlock,
    ) -> Result<Option<LoopIteratorInfo<'def>>, TranslationError<'tcx>> {
        let proc = self.proc;
        let mir = proc.get_mir();
        let bb_data = &mir.basic_blocks[bb];
        let term = bb_data.terminator();

        let mir::TerminatorKind::Call { func, args, .. } = &term.kind else {
            return Ok(None);
        };

        let fn_ty = self.get_type_of_operand(func);
        let call_dest = self.check_operand_call_dest(func).unwrap();

        let iterator_did = search::try_resolve_did(self.tcx, &["core", "iter", "Iterator"]).unwrap();
        let iterator_items: &ty::AssocItems = self.tcx.associated_items(iterator_did);
        let next_symbol = span::Symbol::intern("next");
        let next_ident = span::Ident::with_dummy_span(next_symbol);
        let next_item = iterator_items
            .find_by_ident_and_kind(self.tcx, next_ident, ty::AssocTag::Fn, iterator_did)
            .unwrap();

        if next_item.def_id != call_dest {
            return Ok(None);
        }

        // now trace the argument back to before the mutable borrow
        let next_ref_arg = &args[0].node;
        let mir::Operand::Move(plc) = next_ref_arg else {
            return Ok(None);
        };
        assert!(plc.projection.is_empty());
        let next_ref_local = plc.local;

        let iter_variable = self.find_origin_of_mut_bor(next_ref_local, bb);

        trace!("check_for_iter_next: found iterator variable {iter_variable:?}");

        // so: I'm calling next here.
        // I can definitely resolve that method call.
        // I will go either into the UserDefined or the Param path.
        // I want to find the instantiation of the Iterator trait, right?
        // Then I will be able to refer to the attribute term of that.

        let ty::TyKind::FnDef(_, params) = fn_ty.kind() else {
            return Err(TranslationError::UnknownError("not a FnDef type".to_owned()));
        };

        // exploiting that Iterator has the same args as Iterator::next
        let mut scope = self.ty_translator.scope.borrow_mut();
        let mut state = types::STInner::InFunction(&mut scope);
        let trait_spec_term = self.trait_registry.resolve_trait_requirement_in_state(
            &mut state,
            iterator_did,
            params,
            ty::Binder::dummy(()),
            &[],
            specs::TyParamOrigin::Direct,
            &[],
        )?;
        let trait_spec_term = self
            .trait_registry
            .translate_trait_req_inst_in_state(&mut state, trait_spec_term.req_inst)?;
        trace!("trait_spec_term={trait_spec_term:?}");

        Ok(Some(LoopIteratorInfo {
            iterator_variable: iter_variable,
            binder_name: format!("_iter_{}", iter_variable.index()),
            history_name: format!("_iter_hist_{}", iter_variable.index()),
            iter_spec: trait_spec_term,
        }))
    }

    fn check_is_for_loop(
        &self,
        loop_head: mir::BasicBlock,
    ) -> Result<Option<LoopIteratorInfo<'def>>, TranslationError<'tcx>> {
        let proc = self.proc;
        let succs = proc.successors(loop_head);

        if succs.len() == 1 {
            return self.check_for_iter_next(succs[0]);
        }

        Ok(None)
    }

    /// Parse the attributes on spec closure `did` as loop annotations and add it as an invariant
    /// to the generated code.
    pub(crate) fn parse_attributes_on_loop_spec_closure(
        &self,
        loop_head: mir::BasicBlock,
        did: Option<DefId>,
    ) -> Result<specs::LoopSpec, TranslationError<'tcx>> {
        // Note that StorageDead will not help us for determining initialization/ making it invariant, since
        // it only applies to full stack slots, not individual paths. one thing that makes it more
        // complicated in the frontend: initialization may in practice also be path-dependent.
        //  - this does not cause issues with posing a too strong loop invariant,
        //  - but this poses an issue for annotations
        //

        // Plan:
        // - pass the iter variable to the loop parser
        // - if we want to use the Next relation, we need to figure out the appropriate trait info
        // to use here.
        //   maybe we can do that by getting some info from the next call?
        //   But having the attrs available in that place of the function seems a bit difficult.
        //   Maybe if I'm giving names to all parameters of the proof and introduce them
        //   accordingly.
        //   let's try this later.
        //   but for now, let's just give a special name to the iterator state and then see later
        //   for more advanced stuff.
        //
        // One difficulty: when I prove invariant conditions later, I won't have the SL context
        // available. Need to be a bit careful.
        //
        let iterator_info = self.check_is_for_loop(loop_head)?;

        let init_result =
            initialization::compute_definitely_initialized(self.proc.get_id(), self.proc.get_mir(), self.tcx);
        let init_places = init_result.get_before_block(loop_head);

        // get locals
        let mut locals_with_initialization: Vec<(
            mir::Local,
            String,
            code::LocalKind,
            bool,
            specs::Type<'def>,
        )> = Vec::new();

        for (local, kind, name, ty, _) in &self.fn_locals {
            let place = mir::Place::from(*local);
            let initialized = init_places.contains(place);

            locals_with_initialization.push((
                *local,
                name.to_owned(),
                kind.to_owned(),
                initialized,
                ty.to_owned(),
            ));
        }

        let scope = self.ty_translator.scope.borrow();
        let mut parser = VerboseLoopAttrParser::new(locals_with_initialization, &*scope, iterator_info);

        if let Some(did) = did {
            let attrs = environment::get_attributes(self.tcx, did);
            let attrs = attrs::filter_for_tool(attrs);
            info!("attrs for loop {:?}: {:?}", loop_head, attrs);
            parser.parse_loop_attrs(attrs.as_slice()).map_err(TranslationError::LoopSpec)
        } else {
            parser.parse_loop_attrs(&[]).map_err(TranslationError::LoopSpec)
        }
    }

    /// Find the optional `DefId` of the closure giving the invariant for the loop with head `head_bb`.
    pub(crate) fn find_loop_spec_closure(
        &self,
        head_bb: mir::BasicBlock,
    ) -> Result<Option<DefId>, TranslationError<'tcx>> {
        let bodies = self.proc.loop_info().get_loop_body(head_bb);
        let basic_blocks = &self.proc.get_mir().basic_blocks;

        // we go in order through the bodies in order to not stumble upon an annotation for a
        // nested loop!
        for body in bodies {
            // check that we did not go below a nested loop
            if self.proc.loop_info().get_loop_head(*body) == Some(head_bb) {
                // check the statements for an assignment
                let data = basic_blocks.get(*body).unwrap();
                for stmt in &data.statements {
                    if let mir::StatementKind::Assign(box (pl, _)) = stmt.kind
                        && let Some(did) = self.is_spec_closure_local(pl.local)?
                    {
                        return Ok(Some(did));
                    }
                }
            }
        }

        Ok(None)
    }
}
