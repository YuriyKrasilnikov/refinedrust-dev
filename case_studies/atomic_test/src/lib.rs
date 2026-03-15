#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![rr::include("result")]

// ============================================================
// Macro for integer atomic types — struct + impl
// ============================================================

macro_rules! define_atomic_int {
    ($name:ident, $inner:ty) => {
        #[repr(transparent)]
        #[rr::refined_by("()" : "unit")]
        #[rr::exists("x" : "Z")]
        #[rr::invariant("True")]
        #[rr::mode(atomic)]
        pub struct $name {
            #[rr::field("x")]
            value: $inner,
        }

        impl $name {
            #[rr::only_spec]
            #[rr::returns("()")]
            pub fn new(_value: $inner) -> Self { unimplemented!() }

            #[rr::only_spec]
            #[rr::exists("x" : "Z")]
            #[rr::returns("x")]
            pub fn into_inner(self) -> $inner { unimplemented!() }

            #[rr::only_spec]
            #[rr::exists("x" : "Z")]
            #[rr::exists("γ" : "gname")]
            #[rr::returns("(x, γ)")]
            pub fn get_mut(&mut self) -> &mut $inner { unimplemented!() }

            #[rr::only_spec]
            #[rr::exists("x" : "Z")]
            #[rr::returns("x")]
            pub fn load(&self) -> $inner { unimplemented!() }

            #[rr::only_spec]
            pub fn store(&self, _value: $inner) { unimplemented!() }

            #[rr::only_spec]
            #[rr::exists("x" : "Z")]
            #[rr::returns("x")]
            pub fn swap(&self, _value: $inner) -> $inner { unimplemented!() }

            #[rr::only_spec]
            pub fn compare_exchange(&self, _current: $inner, _new: $inner) -> Result<$inner, $inner> { unimplemented!() }

            #[rr::only_spec]
            pub fn compare_exchange_weak(&self, _current: $inner, _new: $inner) -> Result<$inner, $inner> { unimplemented!() }

            #[rr::only_spec]
            #[rr::exists("x" : "Z")]
            #[rr::returns("x")]
            pub fn fetch_add(&self, _value: $inner) -> $inner { unimplemented!() }

            #[rr::only_spec]
            #[rr::exists("x" : "Z")]
            #[rr::returns("x")]
            pub fn fetch_sub(&self, _value: $inner) -> $inner { unimplemented!() }

            #[rr::only_spec]
            #[rr::exists("x" : "Z")]
            #[rr::returns("x")]
            pub fn fetch_and(&self, _value: $inner) -> $inner { unimplemented!() }

            #[rr::only_spec]
            #[rr::exists("x" : "Z")]
            #[rr::returns("x")]
            pub fn fetch_or(&self, _value: $inner) -> $inner { unimplemented!() }

            #[rr::only_spec]
            #[rr::exists("x" : "Z")]
            #[rr::returns("x")]
            pub fn fetch_xor(&self, _value: $inner) -> $inner { unimplemented!() }

            #[rr::only_spec]
            #[rr::exists("x" : "Z")]
            #[rr::returns("x")]
            pub fn fetch_nand(&self, _value: $inner) -> $inner { unimplemented!() }

            #[rr::only_spec]
            #[rr::exists("x" : "Z")]
            #[rr::returns("x")]
            pub fn fetch_max(&self, _value: $inner) -> $inner { unimplemented!() }

            #[rr::only_spec]
            #[rr::exists("x" : "Z")]
            #[rr::returns("x")]
            pub fn fetch_min(&self, _value: $inner) -> $inner { unimplemented!() }
        }
    };
}

define_atomic_int!(MyAtomicU8, u8);
define_atomic_int!(MyAtomicI8, i8);
define_atomic_int!(MyAtomicU16, u16);
define_atomic_int!(MyAtomicI16, i16);
define_atomic_int!(MyAtomicU32, u32);
define_atomic_int!(MyAtomicI32, i32);
define_atomic_int!(MyAtomicU64, u64);
define_atomic_int!(MyAtomicI64, i64);
define_atomic_int!(MyAtomicUsize, usize);
define_atomic_int!(MyAtomicIsize, isize);

// ============================================================
// Test macro — generates ALL tests for an int atomic type
// Can't use paste, so tests are written per-type below
// ============================================================

// --- MyAtomicU8 ---
#[rr::verify] fn test_u8_load(x: &MyAtomicU8) { let _v = x.load(); }
#[rr::verify] fn test_u8_store(x: &MyAtomicU8) { x.store(42); }
#[rr::verify] fn test_u8_swap(x: &MyAtomicU8) { let _v = x.swap(99); }
#[rr::verify] fn test_u8_cas(x: &MyAtomicU8) { let _r = x.compare_exchange(10, 20); }
#[rr::verify] fn test_u8_cas_weak(x: &MyAtomicU8) { let _r = x.compare_exchange_weak(10, 20); }
#[rr::verify] fn test_u8_fetch_add(x: &MyAtomicU8) { let _v = x.fetch_add(1); }
#[rr::verify] fn test_u8_fetch_sub(x: &MyAtomicU8) { let _v = x.fetch_sub(1); }
#[rr::verify] fn test_u8_fetch_and(x: &MyAtomicU8) { let _v = x.fetch_and(0x0F); }
#[rr::verify] fn test_u8_fetch_or(x: &MyAtomicU8) { let _v = x.fetch_or(0x01); }
#[rr::verify] fn test_u8_fetch_xor(x: &MyAtomicU8) { let _v = x.fetch_xor(0x0F); }
#[rr::verify] fn test_u8_fetch_nand(x: &MyAtomicU8) { let _v = x.fetch_nand(0x0F); }
#[rr::verify] fn test_u8_fetch_max(x: &MyAtomicU8) { let _v = x.fetch_max(42); }
#[rr::verify] fn test_u8_fetch_min(x: &MyAtomicU8) { let _v = x.fetch_min(10); }
#[rr::verify] fn test_u8_new_into_inner() { let a = MyAtomicU8::new(42); let _v = a.into_inner(); }
#[rr::verify] fn test_u8_get_mut() { let mut a = MyAtomicU8::new(10); let r = a.get_mut(); *r = 99; }
#[rr::verify] fn test_u8_new_load() { let a = MyAtomicU8::new(42); let _v = a.load(); }
#[rr::verify] fn test_u8_new_store_into_inner() { let a = MyAtomicU8::new(1); a.store(42); let _v = a.into_inner(); }
#[rr::verify] fn test_u8_new_swap_into_inner() { let a = MyAtomicU8::new(1); let _old = a.swap(42); let _v = a.into_inner(); }
#[rr::verify] fn test_u8_full_lifecycle() { let a = MyAtomicU8::new(1); a.store(2); let _v1 = a.load(); let _v2 = a.swap(3); let _v3 = a.fetch_add(1); let _r = a.compare_exchange(4, 5); let _v4 = a.into_inner(); }

// --- MyAtomicI8 ---
#[rr::verify] fn test_i8_load(x: &MyAtomicI8) { let _v = x.load(); }
#[rr::verify] fn test_i8_store(x: &MyAtomicI8) { x.store(-42); }
#[rr::verify] fn test_i8_swap(x: &MyAtomicI8) { let _v = x.swap(99); }
#[rr::verify] fn test_i8_cas(x: &MyAtomicI8) { let _r = x.compare_exchange(10, 20); }
#[rr::verify] fn test_i8_cas_weak(x: &MyAtomicI8) { let _r = x.compare_exchange_weak(10, 20); }
#[rr::verify] fn test_i8_fetch_add(x: &MyAtomicI8) { let _v = x.fetch_add(1); }
#[rr::verify] fn test_i8_fetch_sub(x: &MyAtomicI8) { let _v = x.fetch_sub(1); }
#[rr::verify] fn test_i8_fetch_and(x: &MyAtomicI8) { let _v = x.fetch_and(0x0F); }
#[rr::verify] fn test_i8_fetch_or(x: &MyAtomicI8) { let _v = x.fetch_or(0x01); }
#[rr::verify] fn test_i8_fetch_xor(x: &MyAtomicI8) { let _v = x.fetch_xor(0x0F); }
#[rr::verify] fn test_i8_fetch_nand(x: &MyAtomicI8) { let _v = x.fetch_nand(0x0F); }
#[rr::verify] fn test_i8_fetch_max(x: &MyAtomicI8) { let _v = x.fetch_max(42); }
#[rr::verify] fn test_i8_fetch_min(x: &MyAtomicI8) { let _v = x.fetch_min(-10); }
#[rr::verify] fn test_i8_new_into_inner() { let a = MyAtomicI8::new(-42); let _v = a.into_inner(); }
#[rr::verify] fn test_i8_get_mut() { let mut a = MyAtomicI8::new(10); let r = a.get_mut(); *r = -99; }
#[rr::verify] fn test_i8_new_load() { let a = MyAtomicI8::new(-42); let _v = a.load(); }
#[rr::verify] fn test_i8_new_store_into_inner() { let a = MyAtomicI8::new(1); a.store(-42); let _v = a.into_inner(); }
#[rr::verify] fn test_i8_new_swap_into_inner() { let a = MyAtomicI8::new(1); let _old = a.swap(-42); let _v = a.into_inner(); }
#[rr::verify] fn test_i8_full_lifecycle() { let a = MyAtomicI8::new(1); a.store(2); let _v1 = a.load(); let _v2 = a.swap(3); let _v3 = a.fetch_add(1); let _r = a.compare_exchange(4, 5); let _v4 = a.into_inner(); }

// --- MyAtomicU16 ---
#[rr::verify] fn test_u16_load(x: &MyAtomicU16) { let _v = x.load(); }
#[rr::verify] fn test_u16_store(x: &MyAtomicU16) { x.store(42); }
#[rr::verify] fn test_u16_swap(x: &MyAtomicU16) { let _v = x.swap(99); }
#[rr::verify] fn test_u16_cas(x: &MyAtomicU16) { let _r = x.compare_exchange(10, 20); }
#[rr::verify] fn test_u16_cas_weak(x: &MyAtomicU16) { let _r = x.compare_exchange_weak(10, 20); }
#[rr::verify] fn test_u16_fetch_add(x: &MyAtomicU16) { let _v = x.fetch_add(1); }
#[rr::verify] fn test_u16_fetch_sub(x: &MyAtomicU16) { let _v = x.fetch_sub(1); }
#[rr::verify] fn test_u16_fetch_and(x: &MyAtomicU16) { let _v = x.fetch_and(0x0F); }
#[rr::verify] fn test_u16_fetch_or(x: &MyAtomicU16) { let _v = x.fetch_or(0x01); }
#[rr::verify] fn test_u16_fetch_xor(x: &MyAtomicU16) { let _v = x.fetch_xor(0x0F); }
#[rr::verify] fn test_u16_fetch_nand(x: &MyAtomicU16) { let _v = x.fetch_nand(0x0F); }
#[rr::verify] fn test_u16_fetch_max(x: &MyAtomicU16) { let _v = x.fetch_max(42); }
#[rr::verify] fn test_u16_fetch_min(x: &MyAtomicU16) { let _v = x.fetch_min(10); }
#[rr::verify] fn test_u16_new_into_inner() { let a = MyAtomicU16::new(42); let _v = a.into_inner(); }
#[rr::verify] fn test_u16_get_mut() { let mut a = MyAtomicU16::new(10); let r = a.get_mut(); *r = 99; }
#[rr::verify] fn test_u16_new_load() { let a = MyAtomicU16::new(42); let _v = a.load(); }
#[rr::verify] fn test_u16_new_store_into_inner() { let a = MyAtomicU16::new(1); a.store(42); let _v = a.into_inner(); }
#[rr::verify] fn test_u16_new_swap_into_inner() { let a = MyAtomicU16::new(1); let _old = a.swap(42); let _v = a.into_inner(); }
#[rr::verify] fn test_u16_full_lifecycle() { let a = MyAtomicU16::new(1); a.store(2); let _v1 = a.load(); let _v2 = a.swap(3); let _v3 = a.fetch_add(1); let _r = a.compare_exchange(4, 5); let _v4 = a.into_inner(); }

// --- MyAtomicI16 ---
#[rr::verify] fn test_i16_load(x: &MyAtomicI16) { let _v = x.load(); }
#[rr::verify] fn test_i16_store(x: &MyAtomicI16) { x.store(-42); }
#[rr::verify] fn test_i16_swap(x: &MyAtomicI16) { let _v = x.swap(99); }
#[rr::verify] fn test_i16_cas(x: &MyAtomicI16) { let _r = x.compare_exchange(10, 20); }
#[rr::verify] fn test_i16_cas_weak(x: &MyAtomicI16) { let _r = x.compare_exchange_weak(10, 20); }
#[rr::verify] fn test_i16_fetch_add(x: &MyAtomicI16) { let _v = x.fetch_add(1); }
#[rr::verify] fn test_i16_fetch_sub(x: &MyAtomicI16) { let _v = x.fetch_sub(1); }
#[rr::verify] fn test_i16_fetch_and(x: &MyAtomicI16) { let _v = x.fetch_and(0x0F); }
#[rr::verify] fn test_i16_fetch_or(x: &MyAtomicI16) { let _v = x.fetch_or(0x01); }
#[rr::verify] fn test_i16_fetch_xor(x: &MyAtomicI16) { let _v = x.fetch_xor(0x0F); }
#[rr::verify] fn test_i16_fetch_nand(x: &MyAtomicI16) { let _v = x.fetch_nand(0x0F); }
#[rr::verify] fn test_i16_fetch_max(x: &MyAtomicI16) { let _v = x.fetch_max(42); }
#[rr::verify] fn test_i16_fetch_min(x: &MyAtomicI16) { let _v = x.fetch_min(-10); }
#[rr::verify] fn test_i16_new_into_inner() { let a = MyAtomicI16::new(-42); let _v = a.into_inner(); }
#[rr::verify] fn test_i16_get_mut() { let mut a = MyAtomicI16::new(10); let r = a.get_mut(); *r = -99; }
#[rr::verify] fn test_i16_new_load() { let a = MyAtomicI16::new(-42); let _v = a.load(); }
#[rr::verify] fn test_i16_new_store_into_inner() { let a = MyAtomicI16::new(1); a.store(-42); let _v = a.into_inner(); }
#[rr::verify] fn test_i16_new_swap_into_inner() { let a = MyAtomicI16::new(1); let _old = a.swap(-42); let _v = a.into_inner(); }
#[rr::verify] fn test_i16_full_lifecycle() { let a = MyAtomicI16::new(1); a.store(2); let _v1 = a.load(); let _v2 = a.swap(3); let _v3 = a.fetch_add(1); let _r = a.compare_exchange(4, 5); let _v4 = a.into_inner(); }

// --- MyAtomicU32 ---
#[rr::verify] fn test_u32_load(x: &MyAtomicU32) { let _v = x.load(); }
#[rr::verify] fn test_u32_store(x: &MyAtomicU32) { x.store(42); }
#[rr::verify] fn test_u32_swap(x: &MyAtomicU32) { let _v = x.swap(99); }
#[rr::verify] fn test_u32_cas(x: &MyAtomicU32) { let _r = x.compare_exchange(10, 20); }
#[rr::verify] fn test_u32_cas_weak(x: &MyAtomicU32) { let _r = x.compare_exchange_weak(10, 20); }
#[rr::verify] fn test_u32_fetch_add(x: &MyAtomicU32) { let _v = x.fetch_add(1); }
#[rr::verify] fn test_u32_fetch_sub(x: &MyAtomicU32) { let _v = x.fetch_sub(1); }
#[rr::verify] fn test_u32_fetch_and(x: &MyAtomicU32) { let _v = x.fetch_and(0x0F); }
#[rr::verify] fn test_u32_fetch_or(x: &MyAtomicU32) { let _v = x.fetch_or(0x01); }
#[rr::verify] fn test_u32_fetch_xor(x: &MyAtomicU32) { let _v = x.fetch_xor(0x0F); }
#[rr::verify] fn test_u32_fetch_nand(x: &MyAtomicU32) { let _v = x.fetch_nand(0x0F); }
#[rr::verify] fn test_u32_fetch_max(x: &MyAtomicU32) { let _v = x.fetch_max(42); }
#[rr::verify] fn test_u32_fetch_min(x: &MyAtomicU32) { let _v = x.fetch_min(10); }
#[rr::verify] fn test_u32_new_into_inner() { let a = MyAtomicU32::new(42); let _v = a.into_inner(); }
#[rr::verify] fn test_u32_get_mut() { let mut a = MyAtomicU32::new(10); let r = a.get_mut(); *r = 99; }
#[rr::verify] fn test_u32_new_load() { let a = MyAtomicU32::new(42); let _v = a.load(); }
#[rr::verify] fn test_u32_new_store_into_inner() { let a = MyAtomicU32::new(1); a.store(42); let _v = a.into_inner(); }
#[rr::verify] fn test_u32_new_swap_into_inner() { let a = MyAtomicU32::new(1); let _old = a.swap(42); let _v = a.into_inner(); }
#[rr::verify] fn test_u32_full_lifecycle() { let a = MyAtomicU32::new(1); a.store(2); let _v1 = a.load(); let _v2 = a.swap(3); let _v3 = a.fetch_add(1); let _r = a.compare_exchange(4, 5); let _v4 = a.into_inner(); }

// --- MyAtomicI32 ---
#[rr::verify] fn test_i32_load(x: &MyAtomicI32) { let _v = x.load(); }
#[rr::verify] fn test_i32_store(x: &MyAtomicI32) { x.store(-42); }
#[rr::verify] fn test_i32_swap(x: &MyAtomicI32) { let _v = x.swap(99); }
#[rr::verify] fn test_i32_cas(x: &MyAtomicI32) { let _r = x.compare_exchange(10, 20); }
#[rr::verify] fn test_i32_cas_weak(x: &MyAtomicI32) { let _r = x.compare_exchange_weak(10, 20); }
#[rr::verify] fn test_i32_fetch_add(x: &MyAtomicI32) { let _v = x.fetch_add(1); }
#[rr::verify] fn test_i32_fetch_sub(x: &MyAtomicI32) { let _v = x.fetch_sub(1); }
#[rr::verify] fn test_i32_fetch_and(x: &MyAtomicI32) { let _v = x.fetch_and(0x0F); }
#[rr::verify] fn test_i32_fetch_or(x: &MyAtomicI32) { let _v = x.fetch_or(0x01); }
#[rr::verify] fn test_i32_fetch_xor(x: &MyAtomicI32) { let _v = x.fetch_xor(0x0F); }
#[rr::verify] fn test_i32_fetch_nand(x: &MyAtomicI32) { let _v = x.fetch_nand(0x0F); }
#[rr::verify] fn test_i32_fetch_max(x: &MyAtomicI32) { let _v = x.fetch_max(42); }
#[rr::verify] fn test_i32_fetch_min(x: &MyAtomicI32) { let _v = x.fetch_min(-10); }
#[rr::verify] fn test_i32_new_into_inner() { let a = MyAtomicI32::new(-42); let _v = a.into_inner(); }
#[rr::verify] fn test_i32_get_mut() { let mut a = MyAtomicI32::new(10); let r = a.get_mut(); *r = -99; }
#[rr::verify] fn test_i32_new_load() { let a = MyAtomicI32::new(-42); let _v = a.load(); }
#[rr::verify] fn test_i32_new_store_into_inner() { let a = MyAtomicI32::new(1); a.store(-42); let _v = a.into_inner(); }
#[rr::verify] fn test_i32_new_swap_into_inner() { let a = MyAtomicI32::new(1); let _old = a.swap(-42); let _v = a.into_inner(); }
#[rr::verify] fn test_i32_full_lifecycle() { let a = MyAtomicI32::new(1); a.store(2); let _v1 = a.load(); let _v2 = a.swap(3); let _v3 = a.fetch_add(1); let _r = a.compare_exchange(4, 5); let _v4 = a.into_inner(); }

// --- MyAtomicU64 ---
#[rr::verify] fn test_u64_load(x: &MyAtomicU64) { let _v = x.load(); }
#[rr::verify] fn test_u64_store(x: &MyAtomicU64) { x.store(42); }
#[rr::verify] fn test_u64_swap(x: &MyAtomicU64) { let _v = x.swap(99); }
#[rr::verify] fn test_u64_cas(x: &MyAtomicU64) { let _r = x.compare_exchange(10, 20); }
#[rr::verify] fn test_u64_cas_weak(x: &MyAtomicU64) { let _r = x.compare_exchange_weak(10, 20); }
#[rr::verify] fn test_u64_fetch_add(x: &MyAtomicU64) { let _v = x.fetch_add(1); }
#[rr::verify] fn test_u64_fetch_sub(x: &MyAtomicU64) { let _v = x.fetch_sub(1); }
#[rr::verify] fn test_u64_fetch_and(x: &MyAtomicU64) { let _v = x.fetch_and(0x0F); }
#[rr::verify] fn test_u64_fetch_or(x: &MyAtomicU64) { let _v = x.fetch_or(0x01); }
#[rr::verify] fn test_u64_fetch_xor(x: &MyAtomicU64) { let _v = x.fetch_xor(0x0F); }
#[rr::verify] fn test_u64_fetch_nand(x: &MyAtomicU64) { let _v = x.fetch_nand(0x0F); }
#[rr::verify] fn test_u64_fetch_max(x: &MyAtomicU64) { let _v = x.fetch_max(100); }
#[rr::verify] fn test_u64_fetch_min(x: &MyAtomicU64) { let _v = x.fetch_min(10); }
#[rr::verify] fn test_u64_new_into_inner() { let a = MyAtomicU64::new(42); let _v = a.into_inner(); }
#[rr::verify] fn test_u64_get_mut() { let mut a = MyAtomicU64::new(10); let r = a.get_mut(); *r = 99; }
#[rr::verify] fn test_u64_new_load() { let a = MyAtomicU64::new(42); let _v = a.load(); }
#[rr::verify] fn test_u64_new_store_into_inner() { let a = MyAtomicU64::new(1); a.store(42); let _v = a.into_inner(); }
#[rr::verify] fn test_u64_new_swap_into_inner() { let a = MyAtomicU64::new(1); let _old = a.swap(42); let _v = a.into_inner(); }
#[rr::verify] fn test_u64_full_lifecycle() { let a = MyAtomicU64::new(1); a.store(2); let _v1 = a.load(); let _v2 = a.swap(3); let _v3 = a.fetch_add(1); let _r = a.compare_exchange(4, 5); let _v4 = a.into_inner(); }

// --- MyAtomicI64 ---
#[rr::verify] fn test_i64_load(x: &MyAtomicI64) { let _v = x.load(); }
#[rr::verify] fn test_i64_store(x: &MyAtomicI64) { x.store(-42); }
#[rr::verify] fn test_i64_swap(x: &MyAtomicI64) { let _v = x.swap(99); }
#[rr::verify] fn test_i64_cas(x: &MyAtomicI64) { let _r = x.compare_exchange(10, 20); }
#[rr::verify] fn test_i64_cas_weak(x: &MyAtomicI64) { let _r = x.compare_exchange_weak(10, 20); }
#[rr::verify] fn test_i64_fetch_add(x: &MyAtomicI64) { let _v = x.fetch_add(1); }
#[rr::verify] fn test_i64_fetch_sub(x: &MyAtomicI64) { let _v = x.fetch_sub(1); }
#[rr::verify] fn test_i64_fetch_and(x: &MyAtomicI64) { let _v = x.fetch_and(0x0F); }
#[rr::verify] fn test_i64_fetch_or(x: &MyAtomicI64) { let _v = x.fetch_or(0x01); }
#[rr::verify] fn test_i64_fetch_xor(x: &MyAtomicI64) { let _v = x.fetch_xor(0x0F); }
#[rr::verify] fn test_i64_fetch_nand(x: &MyAtomicI64) { let _v = x.fetch_nand(0x0F); }
#[rr::verify] fn test_i64_fetch_max(x: &MyAtomicI64) { let _v = x.fetch_max(42); }
#[rr::verify] fn test_i64_fetch_min(x: &MyAtomicI64) { let _v = x.fetch_min(-10); }
#[rr::verify] fn test_i64_new_into_inner() { let a = MyAtomicI64::new(-42); let _v = a.into_inner(); }
#[rr::verify] fn test_i64_get_mut() { let mut a = MyAtomicI64::new(10); let r = a.get_mut(); *r = -99; }
#[rr::verify] fn test_i64_new_load() { let a = MyAtomicI64::new(-42); let _v = a.load(); }
#[rr::verify] fn test_i64_new_store_into_inner() { let a = MyAtomicI64::new(1); a.store(-42); let _v = a.into_inner(); }
#[rr::verify] fn test_i64_new_swap_into_inner() { let a = MyAtomicI64::new(1); let _old = a.swap(-42); let _v = a.into_inner(); }
#[rr::verify] fn test_i64_full_lifecycle() { let a = MyAtomicI64::new(1); a.store(2); let _v1 = a.load(); let _v2 = a.swap(3); let _v3 = a.fetch_add(1); let _r = a.compare_exchange(4, 5); let _v4 = a.into_inner(); }

// --- MyAtomicUsize ---
#[rr::verify] fn test_usize_load(x: &MyAtomicUsize) { let _v = x.load(); }
#[rr::verify] fn test_usize_store(x: &MyAtomicUsize) { x.store(42); }
#[rr::verify] fn test_usize_swap(x: &MyAtomicUsize) { let _v = x.swap(99); }
#[rr::verify] fn test_usize_cas(x: &MyAtomicUsize) { let _r = x.compare_exchange(10, 20); }
#[rr::verify] fn test_usize_cas_weak(x: &MyAtomicUsize) { let _r = x.compare_exchange_weak(10, 20); }
#[rr::verify] fn test_usize_fetch_add(x: &MyAtomicUsize) { let _v = x.fetch_add(1); }
#[rr::verify] fn test_usize_fetch_sub(x: &MyAtomicUsize) { let _v = x.fetch_sub(1); }
#[rr::verify] fn test_usize_fetch_and(x: &MyAtomicUsize) { let _v = x.fetch_and(0x0F); }
#[rr::verify] fn test_usize_fetch_or(x: &MyAtomicUsize) { let _v = x.fetch_or(0x01); }
#[rr::verify] fn test_usize_fetch_xor(x: &MyAtomicUsize) { let _v = x.fetch_xor(0x0F); }
#[rr::verify] fn test_usize_fetch_nand(x: &MyAtomicUsize) { let _v = x.fetch_nand(0x0F); }
#[rr::verify] fn test_usize_fetch_max(x: &MyAtomicUsize) { let _v = x.fetch_max(42); }
#[rr::verify] fn test_usize_fetch_min(x: &MyAtomicUsize) { let _v = x.fetch_min(10); }
#[rr::verify] fn test_usize_new_into_inner() { let a = MyAtomicUsize::new(42); let _v = a.into_inner(); }
#[rr::verify] fn test_usize_get_mut() { let mut a = MyAtomicUsize::new(10); let r = a.get_mut(); *r = 99; }
#[rr::verify] fn test_usize_new_load() { let a = MyAtomicUsize::new(42); let _v = a.load(); }
#[rr::verify] fn test_usize_new_store_into_inner() { let a = MyAtomicUsize::new(1); a.store(42); let _v = a.into_inner(); }
#[rr::verify] fn test_usize_new_swap_into_inner() { let a = MyAtomicUsize::new(1); let _old = a.swap(42); let _v = a.into_inner(); }
#[rr::verify] fn test_usize_full_lifecycle() { let a = MyAtomicUsize::new(1); a.store(2); let _v1 = a.load(); let _v2 = a.swap(3); let _v3 = a.fetch_add(1); let _r = a.compare_exchange(4, 5); let _v4 = a.into_inner(); }

// --- MyAtomicIsize ---
#[rr::verify] fn test_isize_load(x: &MyAtomicIsize) { let _v = x.load(); }
#[rr::verify] fn test_isize_store(x: &MyAtomicIsize) { x.store(-42); }
#[rr::verify] fn test_isize_swap(x: &MyAtomicIsize) { let _v = x.swap(99); }
#[rr::verify] fn test_isize_cas(x: &MyAtomicIsize) { let _r = x.compare_exchange(10, 20); }
#[rr::verify] fn test_isize_cas_weak(x: &MyAtomicIsize) { let _r = x.compare_exchange_weak(10, 20); }
#[rr::verify] fn test_isize_fetch_add(x: &MyAtomicIsize) { let _v = x.fetch_add(1); }
#[rr::verify] fn test_isize_fetch_sub(x: &MyAtomicIsize) { let _v = x.fetch_sub(1); }
#[rr::verify] fn test_isize_fetch_and(x: &MyAtomicIsize) { let _v = x.fetch_and(0x0F); }
#[rr::verify] fn test_isize_fetch_or(x: &MyAtomicIsize) { let _v = x.fetch_or(0x01); }
#[rr::verify] fn test_isize_fetch_xor(x: &MyAtomicIsize) { let _v = x.fetch_xor(0x0F); }
#[rr::verify] fn test_isize_fetch_nand(x: &MyAtomicIsize) { let _v = x.fetch_nand(0x0F); }
#[rr::verify] fn test_isize_fetch_max(x: &MyAtomicIsize) { let _v = x.fetch_max(42); }
#[rr::verify] fn test_isize_fetch_min(x: &MyAtomicIsize) { let _v = x.fetch_min(-10); }
#[rr::verify] fn test_isize_new_into_inner() { let a = MyAtomicIsize::new(-42); let _v = a.into_inner(); }
#[rr::verify] fn test_isize_get_mut() { let mut a = MyAtomicIsize::new(10); let r = a.get_mut(); *r = -99; }
#[rr::verify] fn test_isize_new_load() { let a = MyAtomicIsize::new(-42); let _v = a.load(); }
#[rr::verify] fn test_isize_new_store_into_inner() { let a = MyAtomicIsize::new(1); a.store(-42); let _v = a.into_inner(); }
#[rr::verify] fn test_isize_new_swap_into_inner() { let a = MyAtomicIsize::new(1); let _old = a.swap(-42); let _v = a.into_inner(); }
#[rr::verify] fn test_isize_full_lifecycle() { let a = MyAtomicIsize::new(1); a.store(2); let _v1 = a.load(); let _v2 = a.swap(3); let _v3 = a.fetch_add(1); let _r = a.compare_exchange(4, 5); let _v4 = a.into_inner(); }

// ============================================================
// MyAtomicBool
// ============================================================

#[repr(transparent)]
#[rr::refined_by("()" : "unit")]
#[rr::exists("x" : "bool")]
#[rr::invariant("True")]
#[rr::mode(atomic)]
pub struct MyAtomicBool {
    #[rr::field("x")]
    value: bool,
}

impl MyAtomicBool {
    #[rr::only_spec] #[rr::returns("()")] pub fn new(_value: bool) -> Self { unimplemented!() }
    #[rr::only_spec] #[rr::exists("x" : "bool")] #[rr::returns("x")] pub fn into_inner(self) -> bool { unimplemented!() }
    #[rr::only_spec] #[rr::exists("x" : "bool")] #[rr::exists("γ" : "gname")] #[rr::returns("(x, γ)")] pub fn get_mut(&mut self) -> &mut bool { unimplemented!() }
    #[rr::only_spec] #[rr::exists("x" : "bool")] #[rr::returns("x")] pub fn load(&self) -> bool { unimplemented!() }
    #[rr::only_spec] pub fn store(&self, _value: bool) { unimplemented!() }
    #[rr::only_spec] #[rr::exists("x" : "bool")] #[rr::returns("x")] pub fn swap(&self, _value: bool) -> bool { unimplemented!() }
    #[rr::only_spec] pub fn compare_exchange(&self, _current: bool, _new: bool) -> Result<bool, bool> { unimplemented!() }
    #[rr::only_spec] pub fn compare_exchange_weak(&self, _current: bool, _new: bool) -> Result<bool, bool> { unimplemented!() }
    #[rr::only_spec] #[rr::exists("x" : "bool")] #[rr::returns("x")] pub fn fetch_and(&self, _value: bool) -> bool { unimplemented!() }
    #[rr::only_spec] #[rr::exists("x" : "bool")] #[rr::returns("x")] pub fn fetch_or(&self, _value: bool) -> bool { unimplemented!() }
    #[rr::only_spec] #[rr::exists("x" : "bool")] #[rr::returns("x")] pub fn fetch_xor(&self, _value: bool) -> bool { unimplemented!() }
    #[rr::only_spec] #[rr::exists("x" : "bool")] #[rr::returns("x")] pub fn fetch_nand(&self, _value: bool) -> bool { unimplemented!() }
}

#[rr::verify] fn test_bool_load(x: &MyAtomicBool) { let _v = x.load(); }
#[rr::verify] fn test_bool_store(x: &MyAtomicBool) { x.store(true); }
#[rr::verify] fn test_bool_swap(x: &MyAtomicBool) { let _v = x.swap(false); }
#[rr::verify] fn test_bool_cas(x: &MyAtomicBool) { let _r = x.compare_exchange(true, false); }
#[rr::verify] fn test_bool_cas_weak(x: &MyAtomicBool) { let _r = x.compare_exchange_weak(true, false); }
#[rr::verify] fn test_bool_fetch_and(x: &MyAtomicBool) { let _v = x.fetch_and(true); }
#[rr::verify] fn test_bool_fetch_or(x: &MyAtomicBool) { let _v = x.fetch_or(true); }
#[rr::verify] fn test_bool_fetch_xor(x: &MyAtomicBool) { let _v = x.fetch_xor(true); }
#[rr::verify] fn test_bool_fetch_nand(x: &MyAtomicBool) { let _v = x.fetch_nand(true); }
#[rr::verify] fn test_bool_new_into_inner() { let a = MyAtomicBool::new(true); let _v = a.into_inner(); }
#[rr::verify] fn test_bool_get_mut() { let mut a = MyAtomicBool::new(false); let r = a.get_mut(); *r = true; }
#[rr::verify] fn test_bool_new_load() { let a = MyAtomicBool::new(true); let _v = a.load(); }
#[rr::verify] fn test_bool_new_store_into_inner() { let a = MyAtomicBool::new(false); a.store(true); let _v = a.into_inner(); }
#[rr::verify] fn test_bool_new_swap_into_inner() { let a = MyAtomicBool::new(true); let _old = a.swap(false); let _v = a.into_inner(); }
#[rr::verify] fn test_bool_full_lifecycle() { let a = MyAtomicBool::new(true); a.store(false); let _v1 = a.load(); let _v2 = a.swap(true); let _v3 = a.fetch_and(false); let _r = a.compare_exchange(true, false); let _v4 = a.into_inner(); }

// ============================================================
// MyAtomicPtr
// ============================================================

#[repr(transparent)]
#[rr::refined_by("()" : "unit")]
#[rr::exists("x" : "loc")]
#[rr::invariant("True")]
#[rr::mode(atomic)]
pub struct MyAtomicPtr {
    #[rr::field("x")]
    value: *mut u8,
}

impl MyAtomicPtr {
    #[rr::only_spec] #[rr::returns("()")] pub fn new(_value: *mut u8) -> Self { unimplemented!() }
    #[rr::only_spec] #[rr::exists("x" : "loc")] #[rr::returns("x")] pub fn into_inner(self) -> *mut u8 { unimplemented!() }
    #[rr::only_spec] #[rr::exists("x" : "loc")] #[rr::exists("γ" : "gname")] #[rr::returns("(x, γ)")] pub fn get_mut(&mut self) -> &mut *mut u8 { unimplemented!() }
    #[rr::only_spec] #[rr::exists("x" : "loc")] #[rr::returns("x")] pub fn load(&self) -> *mut u8 { unimplemented!() }
    #[rr::only_spec] pub fn store(&self, _value: *mut u8) { unimplemented!() }
    #[rr::only_spec] #[rr::exists("x" : "loc")] #[rr::returns("x")] pub fn swap(&self, _value: *mut u8) -> *mut u8 { unimplemented!() }
    #[rr::only_spec] pub fn compare_exchange(&self, _current: *mut u8, _new: *mut u8) -> Result<*mut u8, *mut u8> { unimplemented!() }
    #[rr::only_spec] pub fn compare_exchange_weak(&self, _current: *mut u8, _new: *mut u8) -> Result<*mut u8, *mut u8> { unimplemented!() }
}

#[rr::verify] fn test_ptr_load(x: &MyAtomicPtr) { let _v = x.load(); }
#[rr::verify] fn test_ptr_store(x: &MyAtomicPtr, p: *mut u8) { x.store(p); }
#[rr::verify] fn test_ptr_swap(x: &MyAtomicPtr, p: *mut u8) { let _v = x.swap(p); }
#[rr::verify] fn test_ptr_cas(x: &MyAtomicPtr, old: *mut u8, new_val: *mut u8) { let _r = x.compare_exchange(old, new_val); }
#[rr::verify] fn test_ptr_cas_weak(x: &MyAtomicPtr, old: *mut u8, new_val: *mut u8) { let _r = x.compare_exchange_weak(old, new_val); }
#[rr::verify] fn test_ptr_new_into_inner(p: *mut u8) { let a = MyAtomicPtr::new(p); let _v = a.into_inner(); }
#[rr::verify] fn test_ptr_get_mut(p: *mut u8) { let mut a = MyAtomicPtr::new(p); let _r = a.get_mut(); }
#[rr::verify] fn test_ptr_new_load(p: *mut u8) { let a = MyAtomicPtr::new(p); let _v = a.load(); }
#[rr::verify] fn test_ptr_new_store_into_inner(p: *mut u8, q: *mut u8) { let a = MyAtomicPtr::new(p); a.store(q); let _v = a.into_inner(); }
#[rr::verify] fn test_ptr_new_swap_into_inner(p: *mut u8, q: *mut u8) { let a = MyAtomicPtr::new(p); let _old = a.swap(q); let _v = a.into_inner(); }
#[rr::verify] fn test_ptr_full_lifecycle(p: *mut u8, q: *mut u8) { let a = MyAtomicPtr::new(p); a.store(q); let _v1 = a.load(); let _v2 = a.swap(p); let _r = a.compare_exchange(p, q); let _v3 = a.into_inner(); }

// ============================================================
// ============================================================
// Auto-inferred atomics: ONLY mode(atomic) + repr(transparent)
// No refined_by, no exists, no invariant, no field, no only_spec
// Tests all 7 signature patterns × 3 inner types (int, bool, ptr)
// ============================================================

// --- Auto int (u8) ---
#[repr(transparent)]
#[rr::mode(atomic)]
pub struct AutoAtomicU8 {
    value: u8,
}
impl AutoAtomicU8 {
    pub fn new(_value: u8) -> Self { unimplemented!() }
    pub fn into_inner(self) -> u8 { unimplemented!() }
    pub fn get_mut(&mut self) -> &mut u8 { unimplemented!() }
    pub fn load(&self) -> u8 { unimplemented!() }
    pub fn store(&self, _value: u8) { unimplemented!() }
    pub fn swap(&self, _value: u8) -> u8 { unimplemented!() }
}
#[rr::verify] fn test_auto_u8_load(x: &AutoAtomicU8) { let _v = x.load(); }
#[rr::verify] fn test_auto_u8_store(x: &AutoAtomicU8) { x.store(42); }
#[rr::verify] fn test_auto_u8_swap(x: &AutoAtomicU8) { let _v = x.swap(10); }
#[rr::verify] fn test_auto_u8_new_into_inner() { let a = AutoAtomicU8::new(42); let _v = a.into_inner(); }
#[rr::verify] fn test_auto_u8_get_mut(x: &mut AutoAtomicU8) { let _v = x.get_mut(); }

// --- Auto bool ---
#[repr(transparent)]
#[rr::mode(atomic)]
pub struct AutoAtomicBool {
    value: bool,
}
impl AutoAtomicBool {
    pub fn new(_value: bool) -> Self { unimplemented!() }
    pub fn into_inner(self) -> bool { unimplemented!() }
    pub fn get_mut(&mut self) -> &mut bool { unimplemented!() }
    pub fn load(&self) -> bool { unimplemented!() }
    pub fn store(&self, _value: bool) { unimplemented!() }
    pub fn swap(&self, _value: bool) -> bool { unimplemented!() }
}
#[rr::verify] fn test_auto_bool_load(x: &AutoAtomicBool) { let _v = x.load(); }
#[rr::verify] fn test_auto_bool_store(x: &AutoAtomicBool) { x.store(true); }
#[rr::verify] fn test_auto_bool_swap(x: &AutoAtomicBool) { let _v = x.swap(false); }
#[rr::verify] fn test_auto_bool_new_into_inner() { let a = AutoAtomicBool::new(true); let _v = a.into_inner(); }
#[rr::verify] fn test_auto_bool_get_mut(x: &mut AutoAtomicBool) { let _v = x.get_mut(); }

// --- Auto ptr ---
#[repr(transparent)]
#[rr::mode(atomic)]
pub struct AutoAtomicPtr {
    value: *mut u8,
}
impl AutoAtomicPtr {
    pub fn new(_value: *mut u8) -> Self { unimplemented!() }
    pub fn into_inner(self) -> *mut u8 { unimplemented!() }
    pub fn get_mut(&mut self) -> &mut *mut u8 { unimplemented!() }
    pub fn load(&self) -> *mut u8 { unimplemented!() }
    pub fn store(&self, _value: *mut u8) { unimplemented!() }
    pub fn swap(&self, _value: *mut u8) -> *mut u8 { unimplemented!() }
}
#[rr::verify] fn test_auto_ptr_load(x: &AutoAtomicPtr) { let _v = x.load(); }
#[rr::verify] fn test_auto_ptr_store(x: &AutoAtomicPtr, p: *mut u8) { x.store(p); }
#[rr::verify] fn test_auto_ptr_swap(x: &AutoAtomicPtr, p: *mut u8) { let _v = x.swap(p); }
#[rr::verify] fn test_auto_ptr_new_into_inner(p: *mut u8) { let a = AutoAtomicPtr::new(p); let _v = a.into_inner(); }
#[rr::verify] fn test_auto_ptr_get_mut(x: &mut AutoAtomicPtr) { let _v = x.get_mut(); }
