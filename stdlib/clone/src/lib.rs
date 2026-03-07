#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![feature(allocator_api)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.clone")]

#![rr::include("sized")]

use std::marker::PhantomData;

#[rr::export_as(core::clone::Clone)]
pub trait Clone: Sized {
    #[rr::returns("self")]
    fn clone(&self) -> Self;

    #[rr::observe("self.ghost": "($#@{{ {rt_of Self} }} source)")]
    fn clone_from(&mut self, source: &Self)
    {
        *self = source.clone();
    }
}

#[rr::export_as(core::marker::Copy)]
#[rr::semantic("Copyable {Self}")]
pub trait Copy: Clone {
}

macro_rules! impl_clone {
    ($($t:ty)*) => {
        $(
            impl Clone for $t {
                #[rr::default_spec]
                fn clone(&self) -> Self {
                    *self
                }
            }
        )*
    }
}

impl_clone! {
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
    //f16 f32 f64 f128
    bool
    char
}


impl Copy for usize { }
impl Copy for u8 { }
impl Copy for u16 { }
impl Copy for u32 { }
impl Copy for u64 { }
impl Copy for u128 { }
impl Copy for isize { }
impl Copy for i8 { }
impl Copy for i16 { }
impl Copy for i32 { }
impl Copy for i64 { }
impl Copy for i128 { }
impl Copy for bool { }
impl Copy for char { }

#[rr::verify]
impl<T: ?Sized> Clone for *const T {
    fn clone(&self) -> Self {
        *self
    }
}

#[rr::verify]
impl<T: ?Sized> Clone for *mut T {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized> Copy for *mut T { }
impl<T: ?Sized> Copy for *const T { }

impl<T: ?Sized> Copy for PhantomData<T> {}

// TODO: see issue #35
#[rr::only_spec]
impl<T: ?Sized> Clone for PhantomData<T> {
    fn clone(&self) -> Self {
        Self
    }
}

