#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]
#![allow(internal_features)]

#![feature(allocator_api)]
#![feature(ptr_internals)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.boxed")]

#![rr::include("alloc")]
#![rr::include("option")]
#![rr::include("rr_internal")]
#![rr::include("mem")]
#![rr::include("ptr")]
#![rr::include("ptr_advanced")]


use std::alloc::{self, Allocator, Global, Layout};
use std::marker::PhantomData;
use std::ptr::dangling;
use core::ptr::{self, Unique};
use std::mem;


// TODO: maybe we should seal this definition at the module boundary so that there's no chance of
// the definition details leaking?

#[rr::export_as(alloc::boxed::Box)]
#[rr::refined_by("x" : "place_rfn {rt_of T}")]
#[rr::exists("l" : "loc", "a" : "{xt_of A}")]
#[rr::inv(#iris "guarded true (l ◁ₗ[π, Owned] x @ ◁ {T})")]
// TODO: for unsized T, will need to use pointer metadata to determine the size.
#[rr::inv(#iris "{A::FreeablePerm} a l (ly_size {ly_of T})")]
#[rr::ty_lfts("ty_lfts {T}")]
#[rr::ty_wf_E("ty_wf_E {T}")]
pub struct Box<T, A: Allocator = Global, >(#[rr::field("l")] Unique<T>, #[rr::field("$# a")] A);

// TODO: should be T: ?Sized
impl<T, A: Allocator> Box<T, A> {
    #[rr::params("b")]
    #[rr::requires(#type "raw" : "($#@{{ {rt_of T} }} b)" @ "{T}")]
    #[rr::requires(#iris "{A::FreeablePerm} alloc raw (ly_size {ly_of T})")]
    #[rr::requires("raw.(loc_a) ≠ 0")]
    #[rr::returns("b")]
    pub unsafe fn from_raw_in(raw: *mut T, alloc: A) -> Self {
        Box(unsafe { Unique::new_unchecked(raw) }, alloc)
    }

    #[rr::only_spec]
    #[rr::exists("l" : "loc", "a")]
    #[rr::ensures(#type "l" : "($#@{{ {rt_of T} }} b)" @ "{T}")]
    #[rr::ensures(#iris "{A::FreeablePerm} a l (ly_size {ly_of T})")]
    // This holds true even for ZSTs.
    #[rr::ensures("l.(loc_a) ≠ 0")]
    #[rr::returns("*[l; a]")]
    pub fn into_raw_with_allocator(b: Self) -> (*mut T, A) {
        // TODO: not sure how to implement since we cannot use the magic box deref here.
        unimplemented!();
        //let mut b = mem::ManuallyDrop::new(b);
        // We carefully get the raw pointer out in a way that Miri's aliasing model understands what
        // is happening: using the primitive "deref" of `Box`. In case `A` is *not* `Global`, we
        // want *no* aliasing requirements here!
        // In case `A` *is* `Global`, this does not quite have the right behavior; `into_raw`
        // works around that.
        //let ptr = &raw mut **b;
        //let alloc = unsafe { ptr::read(&b.1) };
        //(ptr, alloc)
    }
}

// NB: Only works for sized T.
#[rr::returns("x")]
fn box_new<T>(x: T) -> Box<T> {
    if core::mem::size_of::<T>() == 0 {
        let ptr = std::ptr::dangling::<T>() as *mut T;
        unsafe {
            *ptr = x;
        }
        Box(unsafe { Unique::new_unchecked(ptr) }, Global)
    } else {
        let layout = Layout::new::<T>();
        let ptr = unsafe { alloc::alloc(layout) };
        let ptr = ptr as *mut T;
        unsafe {
            *ptr = x;
        };
        Box(unsafe { Unique::new_unchecked(ptr) }, Global)
    }
}

#[rr::export_as(alloc::boxed::Box)]
impl<T> Box<T> {
    #[rr::returns("x")]
    pub fn new(x: T) -> Self {
        box_new(x)
    }
}

#[rr::export_as(alloc::boxed::Box)]
// TODO: should be T: ?Sized
impl<T> Box<T> {
    

    #[rr::only_spec]
    #[rr::exists("l" : "loc")]
    #[rr::ensures(#type "l" : "($#@{{ {rt_of T} }} b)" @ "{T}")]
    #[rr::ensures(#iris "freeable_nz l (ly_size {ly_of T}) 1 HeapAlloc")]
    // This holds true even for ZSTs.
    #[rr::ensures("l.(loc_a) ≠ 0")]
    #[rr::returns("l")]
    pub fn into_raw(b: Self) -> *mut T {
        // TODO: not sure how to implement since we cannot use the magic box deref here.
        unimplemented!();
        // Avoid `into_raw_with_allocator` as that interacts poorly with Miri's Stacked Borrows.
        //let mut b = mem::ManuallyDrop::new(b);
        // We go through the built-in deref for `Box`, which is crucial for Miri to recognize this
        // operation for it's alias tracking.
        //&raw mut **b
    }

    #[rr::params("b")]
    #[rr::requires(#type "raw" : "($#@{{ {rt_of T} }} b)" @ "{T}")]
    #[rr::requires(#iris "freeable_nz raw (ly_size {ly_of T}) 1 HeapAlloc")]
    #[rr::requires("raw.(loc_a) ≠ 0")]
    #[rr::returns("b")]
    pub unsafe fn from_raw(raw: *mut T) -> Self {
        unsafe {
            Box::from_raw_in(raw, Global)
        }
    }
}

