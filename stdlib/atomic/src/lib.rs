#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("rrstd.atomic")]

// --- Integer atomics (10 types) via macro ---

macro_rules! atomic_int_impl {
    ($rust_ty:ident, $inner_ty:ty, $($std_path:tt)*) => {
        #[rr::export_as($($std_path)*)]
        #[rr::mode(atomic)]
        #[rr::refined_by("()" : "unit")]
        #[repr(transparent)]
        pub struct $rust_ty {
            #[rr::field("()")]
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

// --- AtomicBool (inner field = bool, not u8) ---

#[rr::export_as(core::sync::atomic::AtomicBool)]
#[rr::mode(atomic)]
#[rr::refined_by("()" : "unit")]
#[repr(transparent)]
pub struct AtomicBool {
    #[rr::field("()")]
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
}

// --- AtomicPtr<T> (generic, inner field = *mut T) ---

#[rr::export_as(core::sync::atomic::AtomicPtr)]
#[rr::mode(atomic)]
#[rr::refined_by("()" : "unit")]
#[repr(transparent)]
pub struct AtomicPtr<T> {
    #[rr::field("()")]
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
}
