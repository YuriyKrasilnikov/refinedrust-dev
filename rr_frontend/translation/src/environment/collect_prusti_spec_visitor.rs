// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use log::trace;
use rr_rustc_interface::hir::def_id::LocalDefId;
use rr_rustc_interface::hir::intravisit::Visitor;
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::{hir, middle};

use crate::environment;

pub(crate) struct CollectPrustiSpecVisitor<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    functions: Vec<LocalDefId>,
    modules: Vec<LocalDefId>,
    statics: Vec<LocalDefId>,
    consts: Vec<LocalDefId>,
    traits: Vec<LocalDefId>,
    trait_impls: Vec<LocalDefId>,
}

impl<'tcx> CollectPrustiSpecVisitor<'tcx> {
    pub(crate) const fn new(tcx: ty::TyCtxt<'tcx>) -> Self {
        CollectPrustiSpecVisitor {
            tcx,
            functions: Vec::new(),
            modules: Vec::new(),
            statics: Vec::new(),
            consts: Vec::new(),
            traits: Vec::new(),
            trait_impls: Vec::new(),
        }
    }

    pub(crate) fn get_results(
        self,
    ) -> (Vec<LocalDefId>, Vec<LocalDefId>, Vec<LocalDefId>, Vec<LocalDefId>, Vec<LocalDefId>) {
        (self.functions, self.modules, self.statics, self.consts, self.traits)
    }

    pub(crate) fn get_trait_impls(self) -> Vec<LocalDefId> {
        self.trait_impls
    }

    pub(crate) fn run(&mut self) {
        let it: &middle::hir::ModuleItems = self.tcx.hir_crate_items(());
        for id in it.free_items() {
            self.visit_item(self.tcx.hir_item(id));
        }
        for id in it.impl_items() {
            self.visit_impl_item(self.tcx.hir_impl_item(id));
        }
        for id in it.trait_items() {
            self.visit_trait_item(self.tcx.hir_trait_item(id));
        }
    }
}

impl<'tcx> Visitor<'tcx> for CollectPrustiSpecVisitor<'tcx> {
    fn visit_item(&mut self, i: &hir::Item<'_>) {
        match i.kind {
            hir::ItemKind::Fn { .. } => {
                let def_id = i.hir_id().owner.def_id;
                trace!(
                    "Add fn item {} to result",
                    environment::get_item_def_path(self.tcx, def_id.to_def_id())
                );
                self.functions.push(def_id);
            },
            hir::ItemKind::Const(_, _, _, _) => {
                let def_id = i.hir_id().owner.def_id;
                trace!(
                    "Add const {} to result",
                    environment::get_item_def_path(self.tcx, def_id.to_def_id())
                );
                self.consts.push(def_id);
            },
            hir::ItemKind::Static(..) => {
                let def_id = i.hir_id().owner.def_id;
                trace!(
                    "Add static {} to result",
                    environment::get_item_def_path(self.tcx, def_id.to_def_id())
                );
                self.statics.push(def_id);
            },
            hir::ItemKind::Mod(..) => {
                let def_id = i.hir_id().owner.def_id;
                trace!(
                    "Add module {} to result",
                    environment::get_item_def_path(self.tcx, def_id.to_def_id())
                );
                self.modules.push(def_id);
            },
            hir::ItemKind::Trait(..) => {
                let def_id = i.hir_id().owner.def_id;
                trace!(
                    "Add trait {} to result",
                    environment::get_item_def_path(self.tcx, def_id.to_def_id())
                );
                self.traits.push(def_id);
            },
            hir::ItemKind::Impl(item) => {
                let def_id = i.hir_id().owner.def_id;
                if item.of_trait.is_some() {
                    trace!(
                        "Add trait impl {} to result",
                        environment::get_item_def_path(self.tcx, def_id.to_def_id())
                    );
                    self.trait_impls.push(def_id);
                }
            },
            _ => (),
        }
    }

    /// Visit trait items which are default impls of methods.
    fn visit_trait_item(&mut self, ti: &hir::TraitItem<'_>) {
        //let attrs = self.tcx.get_attrs(trait_item.def_id.to_def_id());

        // Skip associated types and other non-methods items
        let hir::TraitItemKind::Fn(..) = ti.kind else { return };

        // Skip body-less trait methods
        if let hir::TraitItemKind::Fn(_, hir::TraitFn::Required(_)) = ti.kind {
            return;
        }

        let def_id = ti.hir_id().owner.def_id;

        trace!(
            "Add trait-fn-item {} to result",
            environment::get_item_def_path(self.tcx, def_id.to_def_id())
        );
        self.functions.push(def_id);
    }

    fn visit_impl_item(&mut self, ii: &hir::ImplItem<'_>) {
        //let attrs = self.tcx.get_attrs(ii.def_id.to_def_id());

        // Skip associated types and other non-methods items
        let hir::ImplItemKind::Fn(..) = ii.kind else { return };

        let def_id = ii.hir_id().owner.def_id;

        trace!("Add impl-fn-item {} to result", environment::get_item_def_path(self.tcx, def_id.to_def_id()));
        self.functions.push(def_id);
    }
}
