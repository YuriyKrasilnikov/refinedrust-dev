// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use log::trace;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};

use crate::environment::mir_utils::real_edges::RealEdges;
use crate::environment::{Environment, loops};

/// Index of a Basic Block
pub(crate) type BasicBlockIndex = mir::BasicBlock;

/// A facade that provides information about the Rust procedure.
pub(crate) struct Procedure<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    proc_def_id: DefId,
    mir: &'tcx mir::Body<'tcx>,
    real_edges: RealEdges,
    loop_info: loops::ProcedureLoops,
}

impl<'tcx> Procedure<'tcx> {
    /// Builds an implementation of the Procedure interface, given a typing context and the
    /// identifier of a procedure
    pub(crate) fn new(env: &Environment<'tcx>, proc_def_id: DefId) -> Self {
        trace!("Encoding procedure {:?}", proc_def_id);
        let tcx = env.tcx();
        let mir = env.local_mir(proc_def_id.expect_local());
        let real_edges = RealEdges::new(mir);
        let loop_info = loops::ProcedureLoops::new(mir, &real_edges);

        Self {
            tcx,
            proc_def_id,
            mir,
            real_edges,
            loop_info,
        }
    }

    #[must_use]
    pub(crate) const fn loop_info(&self) -> &loops::ProcedureLoops {
        &self.loop_info
    }

    /// Get definition ID of the procedure.
    #[must_use]
    pub(crate) const fn get_id(&self) -> DefId {
        self.proc_def_id
    }

    /// Get the MIR of the procedure
    #[must_use]
    pub(crate) const fn get_mir(&self) -> &mir::Body<'tcx> {
        self.mir
    }

    /// Get the typing context.
    #[must_use]
    pub(crate) const fn get_tcx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    /// Get the predecessors of a basic block.
    #[must_use]
    pub(crate) fn predecessors(&self, bbi: mir::BasicBlock) -> &[mir::BasicBlock] {
        self.real_edges.predecessors(bbi)
    }

    /// Get the successors of a basic block.
    #[must_use]
    pub(crate) fn successors(&self, bbi: mir::BasicBlock) -> &[mir::BasicBlock] {
        self.real_edges.successors(bbi)
    }
}
