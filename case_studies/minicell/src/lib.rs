#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

use std::mem;
use std::ptr;

mod example;
mod evencell;

/* TODO:
 * 1. Add support for non-atomic invariants (na mode)
 * 2. add support for rr::inline
 * 3. verify ptr::eq intrinsic
 * 4. do the verification :)
 *
 */

// We make UnsafeCell behave the same (in terms of refinements) as a value of T.
#[repr(transparent)]
#[rr::refined_by("x" : "{rt_of T}")]
pub struct UnsafeCell<T> {
    #[rr::field("x")]
    value: T,
}

impl<T> UnsafeCell<T> {
    #[rr::returns("value")]
    pub const fn new(value: T) -> UnsafeCell<T> {
        UnsafeCell { value }
    }

    #[rr::only_spec]
    #[rr::returns("self")]
    pub fn into_inner(self) -> T {
        self.value
    }

    #[rr::skip]
    #[rr::exists("γ'")]
    #[rr::returns("(self.cur, γ')")]
    #[rr::ensures(#iris "Inherit ulft_a InheritGhost (Rel2 γ' self.ghost (@eq (ty_xt T_ty → Prop)))")]
    pub fn get_mut<'a>(&'a mut self) -> &'a mut T {
        &mut self.value
    }

    // TODO: what spec can we give this? We'd like to expose the address of the shared reference we get.
    //
    // Ideally, we'd like to inline the code during verification for low-level ops like this for
    // which nice abstraction barriers are hard/annoying
    // Idea: add annotation to skip spec generation, at call sites add annotation in Coq code to inline.
    // Need new call-inline lemma
    //#[rr::inline]
    #[rr::skip]
    pub const fn get(&self) -> *mut T {
        // TODO: we don't have repr(transparent) currently. We could change the code
        //
        // We can just cast the pointer from `UnsafeCell<T>` to `T` because of
        // #[repr(transparent)]. This exploits std's special status, there is
        // no guarantee for user code that this will work in future versions of the compiler!
        self as *const UnsafeCell<T> as *const T as *mut T

        // NOTE: or do this for now
        //&(self.value) as *const T as *mut T
    }
}

#[rr::refined_by("P" : "{xt_of T} → Prop")]
#[rr::exists("x" : "{xt_of T}")]
#[rr::invariant("P x")]
#[rr::mode(na)]
pub struct Cell<T> {
    #[rr::field("$# x")]
    value: UnsafeCell<T>,
}

impl<T> Cell<T> {
    // // NOTE: calling this function requires manual effort to instantiate P
    #[rr::params("P")]
    #[rr::requires("P (value)")]
    #[rr::returns("P")]
    pub const fn new(value: T) -> Cell<T> {
        Cell {
            value: UnsafeCell::new(value),
        }
    }

    #[rr::only_spec]
    #[rr::requires("self (val)")]
    pub fn set(&self, val: T) {
        let old = self.replace(val);
        drop(old);
    }

    #[rr::only_spec]
    #[rr::requires("∀ x, self (x) ↔ other (x)")]
    pub fn swap(&self, other: &Self) {
        // NOTE: will need to manually verify ptr::eq intrinsic
        if ptr::eq(self, other) {
            return;
        }
        // SAFETY: This can be risky if called from separate threads, but `Cell`
        // is `!Sync` so this won't happen. This also won't invalidate any
        // pointers since `Cell` makes sure nothing else will be pointing into
        // either of these `Cell`s.
        unsafe {
            ptr::swap(self.value.get(), other.value.get());
        }
    }

    #[rr::only_spec]
    #[rr::requires("self val")]
    #[rr::exists("y")]
    #[rr::ensures("self y")]
    #[rr::returns("y")]
    pub fn replace(&self, val: T) -> T {
        // SAFETY: This can cause data races if called from a separate thread,
        // but `Cell` is `!Sync` so this won't happen.
        mem::replace(unsafe { &mut *self.value.get() }, val)
    }

    // TODO: proof fails because we try to refold the (deinitialized) invariant
    #[rr::only_spec]
    #[rr::exists("x")]
    #[rr::returns("x")]
    #[rr::ensures("self x")]
    pub fn into_inner(self) -> T {
        self.value.into_inner()
    }

    #[rr::skip]
    #[rr::params("P", "γ")]
    #[rr::args("(P, γ)")]
    #[rr::exists("x", "γ'")]
    #[rr::ensures("⌜P x⌝")]
    #[rr::returns("(x, γ')" @ "&mut (constrained P T)")]
    #[rr::ensures("inherit {'a} (Rel2 γ' γ eq)")]
    pub fn get_mut<'a>(&'a mut self) -> &'a mut T {
        self.value.get_mut()
    }
}

impl<T: Copy> Cell<T> {
    #[rr::skip]
    #[rr::exists("x")]
    #[rr::returns("x")]
    #[rr::ensures("self x")]
    pub fn get(&self) -> T {
        // SAFETY: This can cause data races if called from a separate thread,
        // but `Cell` is `!Sync` so this won't happen.
        unsafe { *self.value.get() }
    }
}
