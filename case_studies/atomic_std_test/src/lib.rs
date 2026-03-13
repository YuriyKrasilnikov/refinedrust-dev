#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![rr::include("atomic")]
#![rr::include("clone")]
#![rr::include("result")]

use std::sync::atomic::AtomicBool;
use std::sync::atomic::AtomicI8;
use std::sync::atomic::AtomicI16;
use std::sync::atomic::AtomicI32;
use std::sync::atomic::AtomicI64;
use std::sync::atomic::AtomicIsize;
use std::sync::atomic::AtomicPtr;
use std::sync::atomic::AtomicU8;
use std::sync::atomic::AtomicU16;
use std::sync::atomic::AtomicU32;
use std::sync::atomic::AtomicU64;
use std::sync::atomic::AtomicUsize;
use std::sync::atomic::Ordering;

// ============================================================
// AtomicU8
// ============================================================

#[rr::verify]
fn test_u8_load(x: &AtomicU8) {
    let _v = x.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_u8_store(x: &AtomicU8) {
    x.store(42, Ordering::SeqCst);
}

#[rr::verify]
fn test_u8_swap(x: &AtomicU8) {
    let _v = x.swap(99, Ordering::SeqCst);
}

#[rr::verify]
fn test_u8_fetch_add(x: &AtomicU8) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_u8_cas(x: &AtomicU8) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

// ============================================================
// AtomicU16
// ============================================================

#[rr::verify]
fn test_u16_load(x: &AtomicU16) {
    let _v = x.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_u16_store(x: &AtomicU16) {
    x.store(42, Ordering::SeqCst);
}

#[rr::verify]
fn test_u16_swap(x: &AtomicU16) {
    let _v = x.swap(99, Ordering::SeqCst);
}

#[rr::verify]
fn test_u16_fetch_add(x: &AtomicU16) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_u16_cas(x: &AtomicU16) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

// ============================================================
// AtomicU32
// ============================================================

#[rr::verify]
fn test_u32_load(x: &AtomicU32) {
    let _v = x.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_u32_store(x: &AtomicU32) {
    x.store(42, Ordering::SeqCst);
}

#[rr::verify]
fn test_u32_swap(x: &AtomicU32) {
    let _v = x.swap(99, Ordering::SeqCst);
}

#[rr::verify]
fn test_u32_fetch_add(x: &AtomicU32) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_u32_cas(x: &AtomicU32) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

// ============================================================
// AtomicU64
// ============================================================

#[rr::verify]
fn test_u64_load(x: &AtomicU64) {
    let _v = x.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_u64_store(x: &AtomicU64) {
    x.store(42, Ordering::SeqCst);
}

#[rr::verify]
fn test_u64_swap(x: &AtomicU64) {
    let _v = x.swap(99, Ordering::SeqCst);
}

#[rr::verify]
fn test_u64_fetch_add(x: &AtomicU64) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_u64_cas(x: &AtomicU64) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

// ============================================================
// AtomicUsize
// ============================================================

#[rr::verify]
fn test_usize_load(x: &AtomicUsize) {
    let _v = x.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_usize_store(x: &AtomicUsize) {
    x.store(42, Ordering::SeqCst);
}

#[rr::verify]
fn test_usize_swap(x: &AtomicUsize) {
    let _v = x.swap(99, Ordering::SeqCst);
}

#[rr::verify]
fn test_usize_fetch_add(x: &AtomicUsize) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_usize_cas(x: &AtomicUsize) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

// ============================================================
// AtomicI8
// ============================================================

#[rr::verify]
fn test_i8_load(x: &AtomicI8) {
    let _v = x.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_i8_store(x: &AtomicI8) {
    x.store(-42, Ordering::SeqCst);
}

#[rr::verify]
fn test_i8_swap(x: &AtomicI8) {
    let _v = x.swap(99, Ordering::SeqCst);
}

#[rr::verify]
fn test_i8_fetch_add(x: &AtomicI8) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_i8_cas(x: &AtomicI8) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

// ============================================================
// AtomicI16
// ============================================================

#[rr::verify]
fn test_i16_load(x: &AtomicI16) {
    let _v = x.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_i16_store(x: &AtomicI16) {
    x.store(-42, Ordering::SeqCst);
}

#[rr::verify]
fn test_i16_swap(x: &AtomicI16) {
    let _v = x.swap(99, Ordering::SeqCst);
}

#[rr::verify]
fn test_i16_fetch_add(x: &AtomicI16) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_i16_cas(x: &AtomicI16) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

// ============================================================
// AtomicI32
// ============================================================

#[rr::verify]
fn test_i32_load(x: &AtomicI32) {
    let _v = x.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_i32_store(x: &AtomicI32) {
    x.store(-42, Ordering::SeqCst);
}

#[rr::verify]
fn test_i32_swap(x: &AtomicI32) {
    let _v = x.swap(99, Ordering::SeqCst);
}

#[rr::verify]
fn test_i32_fetch_add(x: &AtomicI32) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_i32_cas(x: &AtomicI32) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

// ============================================================
// AtomicI64
// ============================================================

#[rr::verify]
fn test_i64_load(x: &AtomicI64) {
    let _v = x.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_i64_store(x: &AtomicI64) {
    x.store(-42, Ordering::SeqCst);
}

#[rr::verify]
fn test_i64_swap(x: &AtomicI64) {
    let _v = x.swap(99, Ordering::SeqCst);
}

#[rr::verify]
fn test_i64_fetch_add(x: &AtomicI64) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_i64_cas(x: &AtomicI64) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

// ============================================================
// AtomicIsize
// ============================================================

#[rr::verify]
fn test_isize_load(x: &AtomicIsize) {
    let _v = x.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_isize_store(x: &AtomicIsize) {
    x.store(-42, Ordering::SeqCst);
}

#[rr::verify]
fn test_isize_swap(x: &AtomicIsize) {
    let _v = x.swap(99, Ordering::SeqCst);
}

#[rr::verify]
fn test_isize_fetch_add(x: &AtomicIsize) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_isize_cas(x: &AtomicIsize) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

// ============================================================
// AtomicBool (no fetch_add — not in std API)
// ============================================================

#[rr::verify]
fn test_bool_load(x: &AtomicBool) {
    let _v = x.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_bool_store(x: &AtomicBool) {
    x.store(true, Ordering::SeqCst);
}

#[rr::verify]
fn test_bool_swap(x: &AtomicBool) {
    let _v = x.swap(false, Ordering::SeqCst);
}

#[rr::verify]
fn test_bool_cas(x: &AtomicBool) {
    let _r = x.compare_exchange(true, false, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_bool_fetch_and(x: &AtomicBool) {
    let _v = x.fetch_and(true, Ordering::SeqCst);
}

// ============================================================
// AtomicPtr<u8> (no fetch_add — not in std API for ptrs)
// ============================================================

#[rr::verify]
fn test_ptr_load(x: &AtomicPtr<u8>) {
    let _v = x.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_ptr_store(x: &AtomicPtr<u8>, p: *mut u8) {
    x.store(p, Ordering::SeqCst);
}

#[rr::verify]
fn test_ptr_swap(x: &AtomicPtr<u8>, p: *mut u8) {
    let _v = x.swap(p, Ordering::SeqCst);
}

#[rr::verify]
fn test_ptr_cas(x: &AtomicPtr<u8>, old: *mut u8, new_val: *mut u8) {
    let _r = x.compare_exchange(old, new_val, Ordering::SeqCst, Ordering::SeqCst);
}
