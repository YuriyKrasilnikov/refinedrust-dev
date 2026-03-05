// From: https://github.com/rust-lang/rust/blob/main/tests/ui-fulldeps/obtain-borrowck.rs
// Hinted by: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_borrowck/consumers/fn.get_bodies_with_borrowck_facts.html

//! This module retrieves MIR bodies with borrowck information.
//!
//! Because of the [stealing mechanism], retrieving MIR bodies with borrowck facts can panic if the bodies are
//! previously stolen.
//!
//! Thread local storage requires all data stored in it to have a `'static` lifetime.
//! Therefore, we transmute the lifetime `'tcx` away when storing the data. To ensure that nothing gets
//! meessed up, we require the client to provide a witness: an instance of type `TyCtxt<'tcx>` that is used to
//! show that the lifetime that the client provided is indeed `'tcx`.
//!
//! See also: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_borrowck/consumers/fn.get_bodies_with_borrowck_facts.html
//!
//! [stealing mechanism]: https://rustc-dev-guide.rust-lang.org/mir/passes.html#stealing

use std::cell::RefCell;
use std::collections::HashMap;
use std::{mem, thread_local};

use rr_rustc_interface::borrowck::{self, consumers};
use rr_rustc_interface::data_structures::fx::FxHashMap;
use rr_rustc_interface::hir::def_id::LocalDefId;
use rr_rustc_interface::middle::{queries, ty, util};

thread_local! {
    pub static MIR_BODIES:
        RefCell<HashMap<LocalDefId, consumers::BodyWithBorrowckFacts<'static>>> =
        RefCell::new(HashMap::new());
}

/// Provider for `mir_borrowck`
///
/// See also: https://github.com/rust-lang/rust/blob/main/tests/ui-fulldeps/obtain-borrowck.rs
///
/// # Safety
///
/// See the module level comment.
pub(crate) fn mir_borrowck(
    tcx: ty::TyCtxt<'_>,
    def_id: LocalDefId,
) -> queries::mir_borrowck::ProvidedValue<'_> {
    let opts = consumers::ConsumerOptions::PoloniusInputFacts;
    let bodies_with_facts = consumers::get_bodies_with_borrowck_facts(tcx, def_id, opts);

    // SAFETY: The reader casts the 'static lifetime to 'tcx before using it.
    let bodies_with_facts: FxHashMap<LocalDefId, consumers::BodyWithBorrowckFacts<'static>> =
        unsafe { mem::transmute(bodies_with_facts) };

    MIR_BODIES.with(|state| {
        let mut map = state.borrow_mut();
        for (def_id, body_with_facts) in bodies_with_facts {
            let res = map.insert(def_id, body_with_facts);
            assert!(res.is_none());
        }
    });

    let mut providers = util::Providers::default();
    borrowck::provide(&mut providers.queries);
    let original_mir_borrowck = providers.queries.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

pub(crate) fn retrieve_mir_body<'tcx>(
    _tcx: ty::TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Option<consumers::BodyWithBorrowckFacts<'tcx>> {
    let body_with_facts: Option<consumers::BodyWithBorrowckFacts<'static>> = MIR_BODIES.with(|state| {
        let mut map = state.borrow_mut();
        map.remove(&def_id)
    });

    // SAFETY: For soundness we need to ensure that the bodies have the same lifetime (`'tcx`), which they had
    // before they were stored in the thread local.
    unsafe { mem::transmute(body_with_facts) }
}
