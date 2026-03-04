#![rr::import("rrstd.spin.theories.once", "once_ghost_state")]
#![rr::include("option")]

use crate::relax::*;

// Point: how can we make this somewhat ergonomic? 
// We should ideally automatically include this in the context (of a function) when we instantiate
// this ADT.
//
// We could factor this into a definition that takes the refinement types as argument. 
// Then we could also include this in the interface definition

#[rr::refined_by("η" : "gname")]
#[rr::context("onceG Σ ({xt_of T})")]
#[rr::export_as(spin::once::Once)]
#[rr::exists("x", "y")]
//#[rr::exists("o" : "option {rt_of T}")]
//#[rr::invariant(#own "once_status_tok η o")]
pub struct Once<T = (), R = Spin> {
    #[rr::field("x")]
    _r: R,
    #[rr::field("y")]
    _d: T,
}

#[rr::only_spec]
#[rr::export_as(spin::once::Once)]
#[rr::context("onceG Σ ({xt_of T})")]
impl<T, R: RelaxStrategy> Once<T, R> {
    #[rr::params("p")]
    #[rr::requires(#iris "{F::Pre} π p f ()")]
    #[rr::requires(#iris "once_status_tok self None")]
    #[rr::exists("x")]
    #[rr::ensures(#iris "{F::Post} π p f () x")]
    #[rr::ensures(#iris "once_status_tok self (Some x)")]
    #[rr::returns("x")]
    pub fn call_once<F: FnOnce() -> T>(&self, f: F) -> &T {
        unimplemented!();
    }
}

#[rr::only_spec]
#[rr::export_as(spin::once::Once)]
#[rr::context("onceG Σ ({xt_of T})")]
impl<T, R> Once<T, R> {
    /// Creates a new [`Once`].
    #[rr::ensures(#iris "once_status_tok ret None")]
    pub const fn new() -> Self {
        unimplemented!();
    }

    /// Creates a new initialized [`Once`].
    #[rr::exists("η")]
    #[rr::ensures(#iris "once_status_tok η (Some data)")]
    #[rr::returns("η")]
    pub const fn initialized(data: T) -> Self {
        unimplemented!();
    }

    /// Returns a reference to the inner value if the [`Once`] has been initialized.
    #[rr::params("o")]
    #[rr::requires(#iris "once_status_tok self o")]
    #[rr::ensures(#iris "once_status_tok self o")]
    #[rr::returns("o")]
    pub fn get(&self) -> Option<&T> {
        unimplemented!();
    }

    #[rr::params("o")]
    #[rr::requires(#iris "once_status_tok self o")]
    #[rr::ensures(#iris "once_status_tok self o")]
    #[rr::returns("bool_decide (is_Some o)")]
    pub fn is_completed(&self) -> bool {
        unimplemented!();
    }

    #[rr::skip]
    #[rr::params("o")]
    #[rr::requires(#iris "once_status_tok self.cur o")]
    #[rr::observe("self.ghost": "self.cur")]
    #[rr::exists("γ'")]
    #[rr::returns("fmap (λ o, (o, γ')) o")]
    // NB The returned mutable reference needs to be able to update the contained value and update
    // the status tok.
    #[rr::ensures(#iris "if bool_decide (is_Some o)
                    then Inherit [{'a}] (∃ x' : {xt_of T}, gvar_obs γ' ($# x') ∗ once_status_tok self.cur (Some x'))
                    else once_status_tok self.cur o")]
    pub fn get_mut<'a>(&'a mut self) -> Option<&'a mut T> {
        unimplemented!();
    }
}
