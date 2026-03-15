#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.result")]
#![rr::import("rrstd.result.theories", "result")]
#![rr::include("clone")]
#![rr::include("closures")]

use std::marker::PhantomData;
use std::hint;

#[rr::export_as(core::result::Result)]
#[rr::refined_by("result (place_rfn {rt_of T}) (place_rfn {rt_of E})")]
#[derive(Copy, Clone)]
pub enum Result<T, E> {
    #[rr::export_as(core::result::Result::Ok)]
    #[rr::pattern("Ok" $ "x")]
    #[rr::refinement("*[x]")]
    Ok(T),
    #[rr::export_as(core::result::Result::Err)]
    #[rr::pattern("Err" $ "x")]
    #[rr::refinement("*[x]")]
    Err(E),
}
use crate::Result::*;

#[rr::only_spec]
#[rr::export_as(core::result::Result)]
impl<T, E> Result<T, E> {

    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::returns("bool_decide (is_Ok x)")]
    pub fn is_ok(&self) -> bool {
        unimplemented!();
    }

    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::returns("bool_decide (is_Err x)")]
    pub fn is_err(&self) -> bool {
        unimplemented!();
    }

    #[rr::requires("destruct_hint self is_Ok")]
    #[rr::ensures("match self with | Ok x => ret = x | Err _ => False end")]
    pub fn unwrap(self) -> T
        where E: Debug,
    {
        match self {
            Ok(t) => t,
            Err(e) => unreachable!(),
                //unwrap_failed("called `Result::unwrap()` on an `Err` value", &e),
        }
    }

    /// # Safety
    /// See stdlib
    #[rr::requires("destruct_hint self is_Ok")]
    #[rr::ensures("match self with | Ok x => ret = x | Err _ => False end")]
    pub unsafe fn unwrap_unchecked(self) -> T {
        match self {
            Ok(t) => t,
            // SAFETY: the safety contract must be upheld by the caller.
            Err(_) => unsafe { hint::unreachable_unchecked() },
        }
    }
}

#[rr::export_as(core::result::Result)]
impl<T, E> Result<T, E> {
    #[rr::params("oparam")]
    #[rr::ensures(#iris "if_iOk self (λ self, ⌜ret = Ok self⌝ ∗ ty_ghost_drop {O} π ($# op))")]
    #[rr::requires(#iris "if_iErr self (λ self, ∃ p, ⌜oparam = Some p⌝ ∗ {O::Pre} π p op *[self])")]
    #[rr::ensures(#iris "if_iErr self (λ self, ∃ p x, ⌜oparam = Some p⌝ ∗ ⌜ret = Err x⌝ ∗ {O::Post} π p op *[self] x)")]
    pub fn map_err<F, O>(self, op: O) -> Result<T, F>
    where
        O: FnOnce(E) -> F,
    {
        match self {
            Ok(t) => Ok(t),
            Err(e) => Err(op(e)),
        }
    }

    #[rr::params("oparam")]
    #[rr::ensures(#iris "if_iErr self (λ self, ⌜ret = Err self⌝ ∗ ty_ghost_drop {F} π ($# op))")]
    #[rr::requires(#iris "if_iOk self (λ self, ∃ p, ⌜oparam = Some p⌝ ∗ {F::Pre} π p op *[self])")]
    #[rr::ensures(#iris "if_iOk self (λ self, ∃ p x, ⌜oparam = Some p⌝ ∗ ⌜ret = Ok x⌝ ∗ {F::Post} π p op *[self] x)")]
    pub fn map<U, F>(self, op: F) -> Result<U, E>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Ok(t) => Ok(op(t)),
            Err(e) => Err(e),
        }
    }
}




#[rr::export_as(core::fmt::Error)]
pub struct Error;

#[rr::export_as(core::fmt::Debug)]
pub trait Debug {
    #[rr::observe("f.ghost": "tt")]
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error>;
}

#[rr::export_as(core::fmt::Formatter)]
#[rr::refined_by("()" : "unit")]
pub struct Formatter<'a> {
    #[rr::field("tt")]
    _marker: PhantomData<&'a mut i32>,
}
