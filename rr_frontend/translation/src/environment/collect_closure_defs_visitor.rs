use log::trace;
use rr_rustc_interface::hir;
use rr_rustc_interface::hir::def_id::LocalDefId;
use rr_rustc_interface::middle::{self, ty};

use crate::environment;

pub(crate) struct CollectClosureDefsVisitor<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    result: Vec<LocalDefId>,
}

impl<'tcx> CollectClosureDefsVisitor<'tcx> {
    pub(crate) const fn new(tcx: ty::TyCtxt<'tcx>) -> Self {
        CollectClosureDefsVisitor {
            tcx,
            result: Vec::new(),
        }
    }

    pub(crate) fn get_closure_defs(self) -> Vec<LocalDefId> {
        self.result
    }
}

impl<'tcx> hir::intravisit::Visitor<'tcx> for CollectClosureDefsVisitor<'tcx> {
    type NestedFilter = middle::hir::nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, ex: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::Closure(hir::Closure {
            def_id: local_def_id,
            ..
        }) = ex.kind
        {
            let item_def_path = environment::get_item_def_path(self.tcx, local_def_id.to_def_id());
            trace!("Add closure {} to result", item_def_path);
            self.result.push(*local_def_id);
        }

        hir::intravisit::walk_expr(self, ex);
    }
}
