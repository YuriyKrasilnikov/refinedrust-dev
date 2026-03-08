#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![rr::include("result")]

// ============================================================
// MyAtomicU8 (u8)
// ============================================================

#[repr(transparent)]
#[rr::refined_by("()" : "unit")]
#[rr::exists("x" : "Z")]
#[rr::invariant("True")]
#[rr::mode(atomic)]
pub struct MyAtomicU8 {
    #[rr::field("x")]
    value: u8,
}

impl MyAtomicU8 {
    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn load(&self) -> u8 { unimplemented!() }

    #[rr::only_spec]
    pub fn store(&self, _value: u8) { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn swap(&self, _value: u8) -> u8 { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange(&self, _current: u8, _new: u8) -> Result<u8, u8> { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange_weak(&self, _current: u8, _new: u8) -> Result<u8, u8> { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_add(&self, _value: u8) -> u8 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_sub(&self, _value: u8) -> u8 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_and(&self, _value: u8) -> u8 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_or(&self, _value: u8) -> u8 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_xor(&self, _value: u8) -> u8 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_nand(&self, _value: u8) -> u8 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_max(&self, _value: u8) -> u8 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_min(&self, _value: u8) -> u8 { unimplemented!() }

}

#[rr::verify]
fn test_u8_load(x: &MyAtomicU8) { let _v = x.load(); }

#[rr::verify]
fn test_u8_store(x: &MyAtomicU8) { x.store(42); }

#[rr::verify]
fn test_u8_swap(x: &MyAtomicU8) { let _v = x.swap(99); }

#[rr::verify]
fn test_u8_cas(x: &MyAtomicU8) { let _r = x.compare_exchange(10, 20); }

#[rr::verify]
fn test_u8_cas_weak(x: &MyAtomicU8) { let _r = x.compare_exchange_weak(10, 20); }

#[rr::verify]
fn test_u8_fetch_add(x: &MyAtomicU8) { let _v = x.fetch_add(1); }

#[rr::verify]
fn test_u8_fetch_sub(x: &MyAtomicU8) { let _v = x.fetch_sub(1); }

#[rr::verify]
fn test_u8_fetch_and(x: &MyAtomicU8) { let _v = x.fetch_and(0x0F); }

#[rr::verify]
fn test_u8_fetch_or(x: &MyAtomicU8) { let _v = x.fetch_or(0x01); }

#[rr::verify]
fn test_u8_fetch_xor(x: &MyAtomicU8) { let _v = x.fetch_xor(0x0F); }

#[rr::verify]
fn test_u8_fetch_nand(x: &MyAtomicU8) { let _v = x.fetch_nand(0x0F); }

#[rr::verify]
fn test_u8_fetch_max(x: &MyAtomicU8) { let _v = x.fetch_max(42); }

#[rr::verify]
fn test_u8_fetch_min(x: &MyAtomicU8) { let _v = x.fetch_min(10); }

// ============================================================
// MyAtomicI8 (i8)
// ============================================================

#[repr(transparent)]
#[rr::refined_by("()" : "unit")]
#[rr::exists("x" : "Z")]
#[rr::invariant("True")]
#[rr::mode(atomic)]
pub struct MyAtomicI8 {
    #[rr::field("x")]
    value: i8,
}

impl MyAtomicI8 {
    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn load(&self) -> i8 { unimplemented!() }

    #[rr::only_spec]
    pub fn store(&self, _value: i8) { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn swap(&self, _value: i8) -> i8 { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange(&self, _current: i8, _new: i8) -> Result<i8, i8> { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange_weak(&self, _current: i8, _new: i8) -> Result<i8, i8> { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_add(&self, _value: i8) -> i8 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_sub(&self, _value: i8) -> i8 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_and(&self, _value: i8) -> i8 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_or(&self, _value: i8) -> i8 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_xor(&self, _value: i8) -> i8 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_nand(&self, _value: i8) -> i8 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_max(&self, _value: i8) -> i8 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_min(&self, _value: i8) -> i8 { unimplemented!() }

}

#[rr::verify]
fn test_i8_load(x: &MyAtomicI8) { let _v = x.load(); }

#[rr::verify]
fn test_i8_store(x: &MyAtomicI8) { x.store(-42); }

#[rr::verify]
fn test_i8_swap(x: &MyAtomicI8) { let _v = x.swap(99); }

#[rr::verify]
fn test_i8_cas(x: &MyAtomicI8) { let _r = x.compare_exchange(10, 20); }

#[rr::verify]
fn test_i8_cas_weak(x: &MyAtomicI8) { let _r = x.compare_exchange_weak(10, 20); }

#[rr::verify]
fn test_i8_fetch_add(x: &MyAtomicI8) { let _v = x.fetch_add(1); }

#[rr::verify]
fn test_i8_fetch_sub(x: &MyAtomicI8) { let _v = x.fetch_sub(1); }

#[rr::verify]
fn test_i8_fetch_and(x: &MyAtomicI8) { let _v = x.fetch_and(0x0F); }

#[rr::verify]
fn test_i8_fetch_or(x: &MyAtomicI8) { let _v = x.fetch_or(0x01); }

#[rr::verify]
fn test_i8_fetch_xor(x: &MyAtomicI8) { let _v = x.fetch_xor(0x0F); }

#[rr::verify]
fn test_i8_fetch_nand(x: &MyAtomicI8) { let _v = x.fetch_nand(0x0F); }

#[rr::verify]
fn test_i8_fetch_max(x: &MyAtomicI8) { let _v = x.fetch_max(42); }

#[rr::verify]
fn test_i8_fetch_min(x: &MyAtomicI8) { let _v = x.fetch_min(-10); }

// ============================================================
// MyAtomicU16 (u16)
// ============================================================

#[repr(transparent)]
#[rr::refined_by("()" : "unit")]
#[rr::exists("x" : "Z")]
#[rr::invariant("True")]
#[rr::mode(atomic)]
pub struct MyAtomicU16 {
    #[rr::field("x")]
    value: u16,
}

impl MyAtomicU16 {
    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn load(&self) -> u16 { unimplemented!() }

    #[rr::only_spec]
    pub fn store(&self, _value: u16) { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn swap(&self, _value: u16) -> u16 { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange(&self, _current: u16, _new: u16) -> Result<u16, u16> { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange_weak(&self, _current: u16, _new: u16) -> Result<u16, u16> { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_add(&self, _value: u16) -> u16 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_sub(&self, _value: u16) -> u16 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_and(&self, _value: u16) -> u16 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_or(&self, _value: u16) -> u16 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_xor(&self, _value: u16) -> u16 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_nand(&self, _value: u16) -> u16 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_max(&self, _value: u16) -> u16 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_min(&self, _value: u16) -> u16 { unimplemented!() }

}

#[rr::verify]
fn test_u16_load(x: &MyAtomicU16) { let _v = x.load(); }

#[rr::verify]
fn test_u16_store(x: &MyAtomicU16) { x.store(42); }

#[rr::verify]
fn test_u16_swap(x: &MyAtomicU16) { let _v = x.swap(99); }

#[rr::verify]
fn test_u16_cas(x: &MyAtomicU16) { let _r = x.compare_exchange(10, 20); }

#[rr::verify]
fn test_u16_cas_weak(x: &MyAtomicU16) { let _r = x.compare_exchange_weak(10, 20); }

#[rr::verify]
fn test_u16_fetch_add(x: &MyAtomicU16) { let _v = x.fetch_add(1); }

#[rr::verify]
fn test_u16_fetch_sub(x: &MyAtomicU16) { let _v = x.fetch_sub(1); }

#[rr::verify]
fn test_u16_fetch_and(x: &MyAtomicU16) { let _v = x.fetch_and(0x0F); }

#[rr::verify]
fn test_u16_fetch_or(x: &MyAtomicU16) { let _v = x.fetch_or(0x01); }

#[rr::verify]
fn test_u16_fetch_xor(x: &MyAtomicU16) { let _v = x.fetch_xor(0x0F); }

#[rr::verify]
fn test_u16_fetch_nand(x: &MyAtomicU16) { let _v = x.fetch_nand(0x0F); }

#[rr::verify]
fn test_u16_fetch_max(x: &MyAtomicU16) { let _v = x.fetch_max(42); }

#[rr::verify]
fn test_u16_fetch_min(x: &MyAtomicU16) { let _v = x.fetch_min(10); }

// ============================================================
// MyAtomicI16 (i16)
// ============================================================

#[repr(transparent)]
#[rr::refined_by("()" : "unit")]
#[rr::exists("x" : "Z")]
#[rr::invariant("True")]
#[rr::mode(atomic)]
pub struct MyAtomicI16 {
    #[rr::field("x")]
    value: i16,
}

impl MyAtomicI16 {
    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn load(&self) -> i16 { unimplemented!() }

    #[rr::only_spec]
    pub fn store(&self, _value: i16) { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn swap(&self, _value: i16) -> i16 { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange(&self, _current: i16, _new: i16) -> Result<i16, i16> { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange_weak(&self, _current: i16, _new: i16) -> Result<i16, i16> { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_add(&self, _value: i16) -> i16 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_sub(&self, _value: i16) -> i16 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_and(&self, _value: i16) -> i16 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_or(&self, _value: i16) -> i16 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_xor(&self, _value: i16) -> i16 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_nand(&self, _value: i16) -> i16 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_max(&self, _value: i16) -> i16 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_min(&self, _value: i16) -> i16 { unimplemented!() }

}

#[rr::verify]
fn test_i16_load(x: &MyAtomicI16) { let _v = x.load(); }

#[rr::verify]
fn test_i16_store(x: &MyAtomicI16) { x.store(-42); }

#[rr::verify]
fn test_i16_swap(x: &MyAtomicI16) { let _v = x.swap(99); }

#[rr::verify]
fn test_i16_cas(x: &MyAtomicI16) { let _r = x.compare_exchange(10, 20); }

#[rr::verify]
fn test_i16_cas_weak(x: &MyAtomicI16) { let _r = x.compare_exchange_weak(10, 20); }

#[rr::verify]
fn test_i16_fetch_add(x: &MyAtomicI16) { let _v = x.fetch_add(1); }

#[rr::verify]
fn test_i16_fetch_sub(x: &MyAtomicI16) { let _v = x.fetch_sub(1); }

#[rr::verify]
fn test_i16_fetch_and(x: &MyAtomicI16) { let _v = x.fetch_and(0x0F); }

#[rr::verify]
fn test_i16_fetch_or(x: &MyAtomicI16) { let _v = x.fetch_or(0x01); }

#[rr::verify]
fn test_i16_fetch_xor(x: &MyAtomicI16) { let _v = x.fetch_xor(0x0F); }

#[rr::verify]
fn test_i16_fetch_nand(x: &MyAtomicI16) { let _v = x.fetch_nand(0x0F); }

#[rr::verify]
fn test_i16_fetch_max(x: &MyAtomicI16) { let _v = x.fetch_max(42); }

#[rr::verify]
fn test_i16_fetch_min(x: &MyAtomicI16) { let _v = x.fetch_min(-10); }

// ============================================================
// MyAtomicU32 (u32)
// ============================================================

#[repr(transparent)]
#[rr::refined_by("()" : "unit")]
#[rr::exists("x" : "Z")]
#[rr::invariant("True")]
#[rr::mode(atomic)]
pub struct MyAtomicU32 {
    #[rr::field("x")]
    value: u32,
}

impl MyAtomicU32 {
    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn load(&self) -> u32 { unimplemented!() }

    #[rr::only_spec]
    pub fn store(&self, _value: u32) { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn swap(&self, _value: u32) -> u32 { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange(&self, _current: u32, _new: u32) -> Result<u32, u32> { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange_weak(&self, _current: u32, _new: u32) -> Result<u32, u32> { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_add(&self, _value: u32) -> u32 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_sub(&self, _value: u32) -> u32 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_and(&self, _value: u32) -> u32 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_or(&self, _value: u32) -> u32 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_xor(&self, _value: u32) -> u32 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_nand(&self, _value: u32) -> u32 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_max(&self, _value: u32) -> u32 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_min(&self, _value: u32) -> u32 { unimplemented!() }

}

#[rr::verify]
fn test_u32_load(x: &MyAtomicU32) { let _v = x.load(); }

#[rr::verify]
fn test_u32_store(x: &MyAtomicU32) { x.store(42); }

#[rr::verify]
fn test_u32_swap(x: &MyAtomicU32) { let _v = x.swap(99); }

#[rr::verify]
fn test_u32_cas(x: &MyAtomicU32) { let _r = x.compare_exchange(10, 20); }

#[rr::verify]
fn test_u32_cas_weak(x: &MyAtomicU32) { let _r = x.compare_exchange_weak(10, 20); }

#[rr::verify]
fn test_u32_fetch_add(x: &MyAtomicU32) { let _v = x.fetch_add(1); }

#[rr::verify]
fn test_u32_fetch_sub(x: &MyAtomicU32) { let _v = x.fetch_sub(1); }

#[rr::verify]
fn test_u32_fetch_and(x: &MyAtomicU32) { let _v = x.fetch_and(0x0F); }

#[rr::verify]
fn test_u32_fetch_or(x: &MyAtomicU32) { let _v = x.fetch_or(0x01); }

#[rr::verify]
fn test_u32_fetch_xor(x: &MyAtomicU32) { let _v = x.fetch_xor(0x0F); }

#[rr::verify]
fn test_u32_fetch_nand(x: &MyAtomicU32) { let _v = x.fetch_nand(0x0F); }

#[rr::verify]
fn test_u32_fetch_max(x: &MyAtomicU32) { let _v = x.fetch_max(42); }

#[rr::verify]
fn test_u32_fetch_min(x: &MyAtomicU32) { let _v = x.fetch_min(10); }

// ============================================================
// MyAtomicI32 (i32)
// ============================================================

#[repr(transparent)]
#[rr::refined_by("()" : "unit")]
#[rr::exists("x" : "Z")]
#[rr::invariant("True")]
#[rr::mode(atomic)]
pub struct MyAtomicI32 {
    #[rr::field("x")]
    value: i32,
}

impl MyAtomicI32 {
    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn load(&self) -> i32 { unimplemented!() }

    #[rr::only_spec]
    pub fn store(&self, _value: i32) { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn swap(&self, _value: i32) -> i32 { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange(&self, _current: i32, _new: i32) -> Result<i32, i32> { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange_weak(&self, _current: i32, _new: i32) -> Result<i32, i32> { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_add(&self, _value: i32) -> i32 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_sub(&self, _value: i32) -> i32 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_and(&self, _value: i32) -> i32 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_or(&self, _value: i32) -> i32 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_xor(&self, _value: i32) -> i32 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_nand(&self, _value: i32) -> i32 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_max(&self, _value: i32) -> i32 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_min(&self, _value: i32) -> i32 { unimplemented!() }

}

#[rr::verify]
fn test_i32_load(x: &MyAtomicI32) { let _v = x.load(); }

#[rr::verify]
fn test_i32_store(x: &MyAtomicI32) { x.store(-42); }

#[rr::verify]
fn test_i32_swap(x: &MyAtomicI32) { let _v = x.swap(99); }

#[rr::verify]
fn test_i32_cas(x: &MyAtomicI32) { let _r = x.compare_exchange(10, 20); }

#[rr::verify]
fn test_i32_cas_weak(x: &MyAtomicI32) { let _r = x.compare_exchange_weak(10, 20); }

#[rr::verify]
fn test_i32_fetch_add(x: &MyAtomicI32) { let _v = x.fetch_add(1); }

#[rr::verify]
fn test_i32_fetch_sub(x: &MyAtomicI32) { let _v = x.fetch_sub(1); }

#[rr::verify]
fn test_i32_fetch_and(x: &MyAtomicI32) { let _v = x.fetch_and(0x0F); }

#[rr::verify]
fn test_i32_fetch_or(x: &MyAtomicI32) { let _v = x.fetch_or(0x01); }

#[rr::verify]
fn test_i32_fetch_xor(x: &MyAtomicI32) { let _v = x.fetch_xor(0x0F); }

#[rr::verify]
fn test_i32_fetch_nand(x: &MyAtomicI32) { let _v = x.fetch_nand(0x0F); }

#[rr::verify]
fn test_i32_fetch_max(x: &MyAtomicI32) { let _v = x.fetch_max(42); }

#[rr::verify]
fn test_i32_fetch_min(x: &MyAtomicI32) { let _v = x.fetch_min(-10); }

// ============================================================
// MyAtomicU64 (u64)
// ============================================================

#[repr(transparent)]
#[rr::refined_by("()" : "unit")]
#[rr::exists("x" : "Z")]
#[rr::invariant("True")]
#[rr::mode(atomic)]
pub struct MyAtomicU64 {
    #[rr::field("x")]
    value: u64,
}

impl MyAtomicU64 {
    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn load(&self) -> u64 { unimplemented!() }

    #[rr::only_spec]
    pub fn store(&self, _value: u64) { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn swap(&self, _value: u64) -> u64 { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange(&self, _current: u64, _new: u64) -> Result<u64, u64> { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange_weak(&self, _current: u64, _new: u64) -> Result<u64, u64> { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_add(&self, _value: u64) -> u64 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_sub(&self, _value: u64) -> u64 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_and(&self, _value: u64) -> u64 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_or(&self, _value: u64) -> u64 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_xor(&self, _value: u64) -> u64 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_nand(&self, _value: u64) -> u64 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_max(&self, _value: u64) -> u64 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_min(&self, _value: u64) -> u64 { unimplemented!() }

}

#[rr::verify]
fn test_u64_load(x: &MyAtomicU64) { let _v = x.load(); }

#[rr::verify]
fn test_u64_store(x: &MyAtomicU64) { x.store(42); }

#[rr::verify]
fn test_u64_swap(x: &MyAtomicU64) { let _v = x.swap(42); }

#[rr::verify]
fn test_u64_cas(x: &MyAtomicU64) { let _r = x.compare_exchange(10, 20); }

#[rr::verify]
fn test_u64_cas_weak(x: &MyAtomicU64) { let _r = x.compare_exchange_weak(10, 20); }

#[rr::verify]
fn test_u64_fetch_add(x: &MyAtomicU64) { let _v = x.fetch_add(1); }

#[rr::verify]
fn test_u64_fetch_sub(x: &MyAtomicU64) { let _v = x.fetch_sub(1); }

#[rr::verify]
fn test_u64_fetch_and(x: &MyAtomicU64) { let _v = x.fetch_and(0x0F); }

#[rr::verify]
fn test_u64_fetch_or(x: &MyAtomicU64) { let _v = x.fetch_or(0x01); }

#[rr::verify]
fn test_u64_fetch_xor(x: &MyAtomicU64) { let _v = x.fetch_xor(0x0F); }

#[rr::verify]
fn test_u64_fetch_nand(x: &MyAtomicU64) { let _v = x.fetch_nand(0x0F); }

#[rr::verify]
fn test_u64_fetch_max(x: &MyAtomicU64) { let _v = x.fetch_max(100); }

#[rr::verify]
fn test_u64_fetch_min(x: &MyAtomicU64) { let _v = x.fetch_min(10); }

// ============================================================
// MyAtomicI64 (i64)
// ============================================================

#[repr(transparent)]
#[rr::refined_by("()" : "unit")]
#[rr::exists("x" : "Z")]
#[rr::invariant("True")]
#[rr::mode(atomic)]
pub struct MyAtomicI64 {
    #[rr::field("x")]
    value: i64,
}

impl MyAtomicI64 {
    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn load(&self) -> i64 { unimplemented!() }

    #[rr::only_spec]
    pub fn store(&self, _value: i64) { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn swap(&self, _value: i64) -> i64 { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange(&self, _current: i64, _new: i64) -> Result<i64, i64> { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange_weak(&self, _current: i64, _new: i64) -> Result<i64, i64> { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_add(&self, _value: i64) -> i64 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_sub(&self, _value: i64) -> i64 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_and(&self, _value: i64) -> i64 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_or(&self, _value: i64) -> i64 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_xor(&self, _value: i64) -> i64 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_nand(&self, _value: i64) -> i64 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_max(&self, _value: i64) -> i64 { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_min(&self, _value: i64) -> i64 { unimplemented!() }

}

#[rr::verify]
fn test_i64_load(x: &MyAtomicI64) { let _v = x.load(); }

#[rr::verify]
fn test_i64_store(x: &MyAtomicI64) { x.store(-42); }

#[rr::verify]
fn test_i64_swap(x: &MyAtomicI64) { let _v = x.swap(99); }

#[rr::verify]
fn test_i64_cas(x: &MyAtomicI64) { let _r = x.compare_exchange(10, 20); }

#[rr::verify]
fn test_i64_cas_weak(x: &MyAtomicI64) { let _r = x.compare_exchange_weak(10, 20); }

#[rr::verify]
fn test_i64_fetch_add(x: &MyAtomicI64) { let _v = x.fetch_add(1); }

#[rr::verify]
fn test_i64_fetch_sub(x: &MyAtomicI64) { let _v = x.fetch_sub(1); }

#[rr::verify]
fn test_i64_fetch_and(x: &MyAtomicI64) { let _v = x.fetch_and(0x0F); }

#[rr::verify]
fn test_i64_fetch_or(x: &MyAtomicI64) { let _v = x.fetch_or(0x01); }

#[rr::verify]
fn test_i64_fetch_xor(x: &MyAtomicI64) { let _v = x.fetch_xor(0x0F); }

#[rr::verify]
fn test_i64_fetch_nand(x: &MyAtomicI64) { let _v = x.fetch_nand(0x0F); }

#[rr::verify]
fn test_i64_fetch_max(x: &MyAtomicI64) { let _v = x.fetch_max(42); }

#[rr::verify]
fn test_i64_fetch_min(x: &MyAtomicI64) { let _v = x.fetch_min(-10); }

// ============================================================
// MyAtomicUsize (usize)
// ============================================================

#[repr(transparent)]
#[rr::refined_by("()" : "unit")]
#[rr::exists("x" : "Z")]
#[rr::invariant("True")]
#[rr::mode(atomic)]
pub struct MyAtomicUsize {
    #[rr::field("x")]
    value: usize,
}

impl MyAtomicUsize {
    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn load(&self) -> usize { unimplemented!() }

    #[rr::only_spec]
    pub fn store(&self, _value: usize) { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn swap(&self, _value: usize) -> usize { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange(&self, _current: usize, _new: usize) -> Result<usize, usize> { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange_weak(&self, _current: usize, _new: usize) -> Result<usize, usize> { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_add(&self, _value: usize) -> usize { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_sub(&self, _value: usize) -> usize { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_and(&self, _value: usize) -> usize { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_or(&self, _value: usize) -> usize { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_xor(&self, _value: usize) -> usize { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_nand(&self, _value: usize) -> usize { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_max(&self, _value: usize) -> usize { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_min(&self, _value: usize) -> usize { unimplemented!() }

}

#[rr::verify]
fn test_usize_load(x: &MyAtomicUsize) { let _v = x.load(); }

#[rr::verify]
fn test_usize_store(x: &MyAtomicUsize) { x.store(42); }

#[rr::verify]
fn test_usize_swap(x: &MyAtomicUsize) { let _v = x.swap(99); }

#[rr::verify]
fn test_usize_cas(x: &MyAtomicUsize) { let _r = x.compare_exchange(10, 20); }

#[rr::verify]
fn test_usize_cas_weak(x: &MyAtomicUsize) { let _r = x.compare_exchange_weak(10, 20); }

#[rr::verify]
fn test_usize_fetch_add(x: &MyAtomicUsize) { let _v = x.fetch_add(1); }

#[rr::verify]
fn test_usize_fetch_sub(x: &MyAtomicUsize) { let _v = x.fetch_sub(1); }

#[rr::verify]
fn test_usize_fetch_and(x: &MyAtomicUsize) { let _v = x.fetch_and(0x0F); }

#[rr::verify]
fn test_usize_fetch_or(x: &MyAtomicUsize) { let _v = x.fetch_or(0x01); }

#[rr::verify]
fn test_usize_fetch_xor(x: &MyAtomicUsize) { let _v = x.fetch_xor(0x0F); }

#[rr::verify]
fn test_usize_fetch_nand(x: &MyAtomicUsize) { let _v = x.fetch_nand(0x0F); }

#[rr::verify]
fn test_usize_fetch_max(x: &MyAtomicUsize) { let _v = x.fetch_max(42); }

#[rr::verify]
fn test_usize_fetch_min(x: &MyAtomicUsize) { let _v = x.fetch_min(10); }

// ============================================================
// MyAtomicIsize (isize)
// ============================================================

#[repr(transparent)]
#[rr::refined_by("()" : "unit")]
#[rr::exists("x" : "Z")]
#[rr::invariant("True")]
#[rr::mode(atomic)]
pub struct MyAtomicIsize {
    #[rr::field("x")]
    value: isize,
}

impl MyAtomicIsize {
    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn load(&self) -> isize { unimplemented!() }

    #[rr::only_spec]
    pub fn store(&self, _value: isize) { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn swap(&self, _value: isize) -> isize { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange(&self, _current: isize, _new: isize) -> Result<isize, isize> { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange_weak(&self, _current: isize, _new: isize) -> Result<isize, isize> { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_add(&self, _value: isize) -> isize { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_sub(&self, _value: isize) -> isize { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_and(&self, _value: isize) -> isize { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_or(&self, _value: isize) -> isize { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_xor(&self, _value: isize) -> isize { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_nand(&self, _value: isize) -> isize { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_max(&self, _value: isize) -> isize { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn fetch_min(&self, _value: isize) -> isize { unimplemented!() }

}

#[rr::verify]
fn test_isize_load(x: &MyAtomicIsize) { let _v = x.load(); }

#[rr::verify]
fn test_isize_store(x: &MyAtomicIsize) { x.store(-42); }

#[rr::verify]
fn test_isize_swap(x: &MyAtomicIsize) { let _v = x.swap(99); }

#[rr::verify]
fn test_isize_cas(x: &MyAtomicIsize) { let _r = x.compare_exchange(10, 20); }

#[rr::verify]
fn test_isize_cas_weak(x: &MyAtomicIsize) { let _r = x.compare_exchange_weak(10, 20); }

#[rr::verify]
fn test_isize_fetch_add(x: &MyAtomicIsize) { let _v = x.fetch_add(1); }

#[rr::verify]
fn test_isize_fetch_sub(x: &MyAtomicIsize) { let _v = x.fetch_sub(1); }

#[rr::verify]
fn test_isize_fetch_and(x: &MyAtomicIsize) { let _v = x.fetch_and(0x0F); }

#[rr::verify]
fn test_isize_fetch_or(x: &MyAtomicIsize) { let _v = x.fetch_or(0x01); }

#[rr::verify]
fn test_isize_fetch_xor(x: &MyAtomicIsize) { let _v = x.fetch_xor(0x0F); }

#[rr::verify]
fn test_isize_fetch_nand(x: &MyAtomicIsize) { let _v = x.fetch_nand(0x0F); }

#[rr::verify]
fn test_isize_fetch_max(x: &MyAtomicIsize) { let _v = x.fetch_max(42); }

#[rr::verify]
fn test_isize_fetch_min(x: &MyAtomicIsize) { let _v = x.fetch_min(-10); }

// ============================================================
// MyAtomicBool (bool)
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
    #[rr::only_spec]
    #[rr::exists("x" : "bool")]
    #[rr::returns("x")]
    pub fn load(&self) -> bool { unimplemented!() }

    #[rr::only_spec]
    pub fn store(&self, _value: bool) { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "bool")]
    #[rr::returns("x")]
    pub fn swap(&self, _value: bool) -> bool { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange(&self, _current: bool, _new: bool) -> Result<bool, bool> { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange_weak(&self, _current: bool, _new: bool) -> Result<bool, bool> { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "bool")]
    #[rr::returns("x")]
    pub fn fetch_and(&self, _value: bool) -> bool { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "bool")]
    #[rr::returns("x")]
    pub fn fetch_or(&self, _value: bool) -> bool { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "bool")]
    #[rr::returns("x")]
    pub fn fetch_xor(&self, _value: bool) -> bool { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "bool")]
    #[rr::returns("x")]
    pub fn fetch_nand(&self, _value: bool) -> bool { unimplemented!() }
}

#[rr::verify]
fn test_bool_load(x: &MyAtomicBool) { let _v = x.load(); }

#[rr::verify]
fn test_bool_store(x: &MyAtomicBool) { x.store(true); }

#[rr::verify]
fn test_bool_swap(x: &MyAtomicBool) { let _v = x.swap(false); }

#[rr::verify]
fn test_bool_cas(x: &MyAtomicBool) { let _r = x.compare_exchange(true, false); }

#[rr::verify]
fn test_bool_cas_weak(x: &MyAtomicBool) { let _r = x.compare_exchange_weak(true, false); }

#[rr::verify]
fn test_bool_fetch_and(x: &MyAtomicBool) { let _v = x.fetch_and(true); }

#[rr::verify]
fn test_bool_fetch_or(x: &MyAtomicBool) { let _v = x.fetch_or(true); }

#[rr::verify]
fn test_bool_fetch_xor(x: &MyAtomicBool) { let _v = x.fetch_xor(true); }

#[rr::verify]
fn test_bool_fetch_nand(x: &MyAtomicBool) { let _v = x.fetch_nand(true); }

// ============================================================
// MyAtomicPtr (*mut u8 as proxy for *mut T)
// ============================================================
// alias_ptr_t: refinement = loc, op_type = PtrOp
// Phase A: load, store, swap (RmwXchg), compare_exchange, compare_exchange_weak

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
    #[rr::only_spec]
    #[rr::exists("x" : "loc")]
    #[rr::returns("x")]
    pub fn load(&self) -> *mut u8 { unimplemented!() }

    #[rr::only_spec]
    pub fn store(&self, _value: *mut u8) { unimplemented!() }

    #[rr::only_spec]
    #[rr::exists("x" : "loc")]
    #[rr::returns("x")]
    pub fn swap(&self, _value: *mut u8) -> *mut u8 { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange(&self, _current: *mut u8, _new: *mut u8) -> Result<*mut u8, *mut u8> { unimplemented!() }

    #[rr::only_spec]
    pub fn compare_exchange_weak(&self, _current: *mut u8, _new: *mut u8) -> Result<*mut u8, *mut u8> { unimplemented!() }
}

#[rr::verify]
fn test_ptr_load(x: &MyAtomicPtr) { let _v = x.load(); }

#[rr::verify]
fn test_ptr_store(x: &MyAtomicPtr, p: *mut u8) { x.store(p); }

#[rr::verify]
fn test_ptr_swap(x: &MyAtomicPtr, p: *mut u8) { let _v = x.swap(p); }

#[rr::verify]
fn test_ptr_cas(x: &MyAtomicPtr, old: *mut u8, new_val: *mut u8) { let _r = x.compare_exchange(old, new_val); }

#[rr::verify]
fn test_ptr_cas_weak(x: &MyAtomicPtr, old: *mut u8, new_val: *mut u8) { let _r = x.compare_exchange_weak(old, new_val); }

