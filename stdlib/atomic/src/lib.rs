#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.atomic")]
#![rr::export_include("result")]

// --- Integer atomics (10 types) via macro ---

macro_rules! atomic_int_impl {
    ($rust_ty:ident, $inner_ty:ty, $($std_path:tt)*) => {
        #[rr::export_as($($std_path)*)]
        #[rr::mode(atomic)]
        #[repr(transparent)]
        pub struct $rust_ty {
            v: $inner_ty,
        }

        #[rr::export_as($($std_path)*)]
        #[rr::only_spec]
        impl $rust_ty {
            #[rr::params("x")]
            #[rr::args("x")]
            #[rr::returns("()")]
            pub fn new(v: $inner_ty) -> Self {
                unimplemented!();
            }

            #[rr::exists("x" : "Z")]
            #[rr::returns("x")]
            pub fn into_inner(self) -> $inner_ty {
                unimplemented!();
            }

            #[rr::exists("x" : "Z")]
            #[rr::exists("γ" : "gname")]
            #[rr::returns("(x, γ)")]
            pub fn get_mut(&mut self) -> &mut $inner_ty {
                unimplemented!();
            }
        }
    };
}

atomic_int_impl!(AtomicU8, u8, core::sync::atomic::AtomicU8);
atomic_int_impl!(AtomicU16, u16, core::sync::atomic::AtomicU16);
atomic_int_impl!(AtomicU32, u32, core::sync::atomic::AtomicU32);
atomic_int_impl!(AtomicU64, u64, core::sync::atomic::AtomicU64);
atomic_int_impl!(AtomicUsize, usize, core::sync::atomic::AtomicUsize);
atomic_int_impl!(AtomicI8, i8, core::sync::atomic::AtomicI8);
atomic_int_impl!(AtomicI16, i16, core::sync::atomic::AtomicI16);
atomic_int_impl!(AtomicI32, i32, core::sync::atomic::AtomicI32);
atomic_int_impl!(AtomicI64, i64, core::sync::atomic::AtomicI64);
atomic_int_impl!(AtomicIsize, isize, core::sync::atomic::AtomicIsize);

// --- AtomicBool ---

#[rr::export_as(core::sync::atomic::AtomicBool)]
#[rr::mode(atomic)]
#[repr(transparent)]
pub struct AtomicBool {
    v: bool,
}

#[rr::export_as(core::sync::atomic::AtomicBool)]
#[rr::only_spec]
impl AtomicBool {
    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::returns("()")]
    pub fn new(v: bool) -> Self {
        unimplemented!();
    }

    #[rr::exists("x" : "bool")]
    #[rr::returns("x")]
    pub fn into_inner(self) -> bool {
        unimplemented!();
    }

    #[rr::exists("x" : "bool")]
    #[rr::exists("γ" : "gname")]
    #[rr::returns("(x, γ)")]
    pub fn get_mut(&mut self) -> &mut bool {
        unimplemented!();
    }
}

// --- AtomicPtr<T> ---

#[rr::export_as(core::sync::atomic::AtomicPtr)]
#[rr::mode(atomic)]
#[repr(transparent)]
pub struct AtomicPtr<T> {
    v: *mut T,
}

#[rr::export_as(core::sync::atomic::AtomicPtr)]
#[rr::only_spec]
impl<T> AtomicPtr<T> {
    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::returns("()")]
    pub fn new(v: *mut T) -> Self {
        unimplemented!();
    }

    #[rr::exists("x" : "loc")]
    #[rr::returns("x")]
    pub fn into_inner(self) -> *mut T {
        unimplemented!();
    }

    #[rr::exists("x" : "loc")]
    #[rr::exists("γ" : "gname")]
    #[rr::returns("(x, γ)")]
    pub fn get_mut(&mut self) -> &mut *mut T {
        unimplemented!();
    }
}
