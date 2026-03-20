#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.atomic")]
#![rr::export_include("result")]

// Single generic shim for all atomic types.
// On nightly-2026-03-06+, all std atomics are type aliases for Atomic<T>:
//   AtomicU8 = Atomic<u8>, AtomicBool = Atomic<bool>, AtomicPtr<T> = Atomic<*mut T>
//
// Frontend resolves aliases transparently:
//   AtomicPtr<u8>::get_mut → impl<T> AtomicPtr<T> → self_ty = Atomic<*mut u8>
//   AtomicBool::get_mut    → impl AtomicBool      → self_ty = Atomic<bool>
//
// Unified augmentation in calls.rs uses ADT substs from resolved self_ty.

#[rr::export_as(core::sync::atomic::Atomic)]
#[rr::mode(atomic)]
#[repr(transparent)]
pub struct Atomic<T> {
    v: T,
}

#[rr::export_as(core::sync::atomic::Atomic)]
#[rr::only_spec]
impl<T> Atomic<T> {
    pub fn new(v: T) -> Self {
        unimplemented!();
    }

    pub fn into_inner(self) -> T {
        unimplemented!();
    }

    pub fn get_mut(&mut self) -> &mut T {
        unimplemented!();
    }

    pub fn as_ptr(&self) -> *mut T {
        unimplemented!();
    }

    pub unsafe fn from_ptr<'a>(ptr: *mut T) -> &'a Self {
        unimplemented!();
    }
}
