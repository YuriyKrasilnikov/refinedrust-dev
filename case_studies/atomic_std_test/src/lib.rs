#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![rr::include("stdlib")]

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

// Store with `let _ = ...` binding — verifies both MIR patterns work
#[rr::verify]
fn test_u8_store_let(x: &AtomicU8) {
    let _ = x.store(42, Ordering::SeqCst);
}

// Non-SeqCst orderings: expected to fail translation (SC model only)
#[rr::skip]
fn test_u8_load_relaxed(x: &AtomicU8) {
    let _v = x.load(Ordering::Relaxed);
}

#[rr::skip]
fn test_u8_store_release(x: &AtomicU8) {
    x.store(42, Ordering::Release);
}

#[rr::skip]
fn test_u8_load_acquire(x: &AtomicU8) {
    let _v = x.load(Ordering::Acquire);
}

#[rr::verify]
fn test_u8_swap(x: &AtomicU8) {
    let _v = x.swap(99, Ordering::SeqCst);
}

#[rr::verify]
fn test_u8_cas(x: &AtomicU8) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_u8_cas_weak(x: &AtomicU8) {
    let _r = x.compare_exchange_weak(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_u8_fetch_add(x: &AtomicU8) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_u8_fetch_sub(x: &AtomicU8) {
    let _v = x.fetch_sub(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_u8_fetch_and(x: &AtomicU8) {
    let _v = x.fetch_and(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_u8_fetch_or(x: &AtomicU8) {
    let _v = x.fetch_or(0x01, Ordering::SeqCst);
}

#[rr::verify]
fn test_u8_fetch_xor(x: &AtomicU8) {
    let _v = x.fetch_xor(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_u8_fetch_nand(x: &AtomicU8) {
    let _v = x.fetch_nand(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_u8_fetch_max(x: &AtomicU8) {
    let _v = x.fetch_max(42, Ordering::SeqCst);
}

#[rr::verify]
fn test_u8_fetch_min(x: &AtomicU8) {
    let _v = x.fetch_min(10, Ordering::SeqCst);
}

#[rr::verify]
fn test_u8_get_mut() {
    let mut a = AtomicU8::new(10);
    let r = a.get_mut();
    *r = 99;
}

#[rr::verify]
fn test_u8_new_into_inner() {
    let a = AtomicU8::new(42);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_u8_new_load() {
    let a = AtomicU8::new(42);
    let _v = a.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_u8_new_store_into_inner() {
    let a = AtomicU8::new(1);
    a.store(42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_u8_new_swap_into_inner() {
    let a = AtomicU8::new(1);
    let _old = a.swap(42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_u8_full_lifecycle() {
    let a = AtomicU8::new(1);
    a.store(2, Ordering::SeqCst);
    let _v1 = a.load(Ordering::SeqCst);
    let _v2 = a.swap(3, Ordering::SeqCst);
    let _v3 = a.fetch_add(1, Ordering::SeqCst);
    let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst);
    let _v4 = a.into_inner();
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
fn test_i8_cas(x: &AtomicI8) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_i8_cas_weak(x: &AtomicI8) {
    let _r = x.compare_exchange_weak(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_i8_fetch_add(x: &AtomicI8) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_i8_fetch_sub(x: &AtomicI8) {
    let _v = x.fetch_sub(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_i8_fetch_and(x: &AtomicI8) {
    let _v = x.fetch_and(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_i8_fetch_or(x: &AtomicI8) {
    let _v = x.fetch_or(0x01, Ordering::SeqCst);
}

#[rr::verify]
fn test_i8_fetch_xor(x: &AtomicI8) {
    let _v = x.fetch_xor(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_i8_fetch_nand(x: &AtomicI8) {
    let _v = x.fetch_nand(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_i8_fetch_max(x: &AtomicI8) {
    let _v = x.fetch_max(42, Ordering::SeqCst);
}

#[rr::verify]
fn test_i8_fetch_min(x: &AtomicI8) {
    let _v = x.fetch_min(-10, Ordering::SeqCst);
}

#[rr::verify]
fn test_i8_get_mut() {
    let mut a = AtomicI8::new(10);
    let r = a.get_mut();
    *r = -99;
}

#[rr::verify]
fn test_i8_new_into_inner() {
    let a = AtomicI8::new(-42);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_i8_new_load() {
    let a = AtomicI8::new(-42);
    let _v = a.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_i8_new_store_into_inner() {
    let a = AtomicI8::new(1);
    a.store(-42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_i8_new_swap_into_inner() {
    let a = AtomicI8::new(1);
    let _old = a.swap(-42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_i8_full_lifecycle() {
    let a = AtomicI8::new(1);
    a.store(2, Ordering::SeqCst);
    let _v1 = a.load(Ordering::SeqCst);
    let _v2 = a.swap(3, Ordering::SeqCst);
    let _v3 = a.fetch_add(1, Ordering::SeqCst);
    let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst);
    let _v4 = a.into_inner();
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
fn test_u16_cas(x: &AtomicU16) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_u16_cas_weak(x: &AtomicU16) {
    let _r = x.compare_exchange_weak(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_u16_fetch_add(x: &AtomicU16) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_u16_fetch_sub(x: &AtomicU16) {
    let _v = x.fetch_sub(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_u16_fetch_and(x: &AtomicU16) {
    let _v = x.fetch_and(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_u16_fetch_or(x: &AtomicU16) {
    let _v = x.fetch_or(0x01, Ordering::SeqCst);
}

#[rr::verify]
fn test_u16_fetch_xor(x: &AtomicU16) {
    let _v = x.fetch_xor(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_u16_fetch_nand(x: &AtomicU16) {
    let _v = x.fetch_nand(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_u16_fetch_max(x: &AtomicU16) {
    let _v = x.fetch_max(42, Ordering::SeqCst);
}

#[rr::verify]
fn test_u16_fetch_min(x: &AtomicU16) {
    let _v = x.fetch_min(10, Ordering::SeqCst);
}

#[rr::verify]
fn test_u16_get_mut() {
    let mut a = AtomicU16::new(10);
    let r = a.get_mut();
    *r = 99;
}

#[rr::verify]
fn test_u16_new_into_inner() {
    let a = AtomicU16::new(42);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_u16_new_load() {
    let a = AtomicU16::new(42);
    let _v = a.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_u16_new_store_into_inner() {
    let a = AtomicU16::new(1);
    a.store(42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_u16_new_swap_into_inner() {
    let a = AtomicU16::new(1);
    let _old = a.swap(42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_u16_full_lifecycle() {
    let a = AtomicU16::new(1);
    a.store(2, Ordering::SeqCst);
    let _v1 = a.load(Ordering::SeqCst);
    let _v2 = a.swap(3, Ordering::SeqCst);
    let _v3 = a.fetch_add(1, Ordering::SeqCst);
    let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst);
    let _v4 = a.into_inner();
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
fn test_i16_cas(x: &AtomicI16) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_i16_cas_weak(x: &AtomicI16) {
    let _r = x.compare_exchange_weak(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_i16_fetch_add(x: &AtomicI16) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_i16_fetch_sub(x: &AtomicI16) {
    let _v = x.fetch_sub(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_i16_fetch_and(x: &AtomicI16) {
    let _v = x.fetch_and(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_i16_fetch_or(x: &AtomicI16) {
    let _v = x.fetch_or(0x01, Ordering::SeqCst);
}

#[rr::verify]
fn test_i16_fetch_xor(x: &AtomicI16) {
    let _v = x.fetch_xor(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_i16_fetch_nand(x: &AtomicI16) {
    let _v = x.fetch_nand(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_i16_fetch_max(x: &AtomicI16) {
    let _v = x.fetch_max(42, Ordering::SeqCst);
}

#[rr::verify]
fn test_i16_fetch_min(x: &AtomicI16) {
    let _v = x.fetch_min(-10, Ordering::SeqCst);
}

#[rr::verify]
fn test_i16_get_mut() {
    let mut a = AtomicI16::new(10);
    let r = a.get_mut();
    *r = -99;
}

#[rr::verify]
fn test_i16_new_into_inner() {
    let a = AtomicI16::new(-42);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_i16_new_load() {
    let a = AtomicI16::new(-42);
    let _v = a.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_i16_new_store_into_inner() {
    let a = AtomicI16::new(1);
    a.store(-42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_i16_new_swap_into_inner() {
    let a = AtomicI16::new(1);
    let _old = a.swap(-42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_i16_full_lifecycle() {
    let a = AtomicI16::new(1);
    a.store(2, Ordering::SeqCst);
    let _v1 = a.load(Ordering::SeqCst);
    let _v2 = a.swap(3, Ordering::SeqCst);
    let _v3 = a.fetch_add(1, Ordering::SeqCst);
    let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst);
    let _v4 = a.into_inner();
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
fn test_u32_cas(x: &AtomicU32) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_u32_cas_weak(x: &AtomicU32) {
    let _r = x.compare_exchange_weak(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_u32_fetch_add(x: &AtomicU32) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_u32_fetch_sub(x: &AtomicU32) {
    let _v = x.fetch_sub(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_u32_fetch_and(x: &AtomicU32) {
    let _v = x.fetch_and(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_u32_fetch_or(x: &AtomicU32) {
    let _v = x.fetch_or(0x01, Ordering::SeqCst);
}

#[rr::verify]
fn test_u32_fetch_xor(x: &AtomicU32) {
    let _v = x.fetch_xor(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_u32_fetch_nand(x: &AtomicU32) {
    let _v = x.fetch_nand(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_u32_fetch_max(x: &AtomicU32) {
    let _v = x.fetch_max(42, Ordering::SeqCst);
}

#[rr::verify]
fn test_u32_fetch_min(x: &AtomicU32) {
    let _v = x.fetch_min(10, Ordering::SeqCst);
}

#[rr::verify]
fn test_u32_get_mut() {
    let mut a = AtomicU32::new(10);
    let r = a.get_mut();
    *r = 99;
}

#[rr::verify]
fn test_u32_new_into_inner() {
    let a = AtomicU32::new(42);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_u32_new_load() {
    let a = AtomicU32::new(42);
    let _v = a.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_u32_new_store_into_inner() {
    let a = AtomicU32::new(1);
    a.store(42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_u32_new_swap_into_inner() {
    let a = AtomicU32::new(1);
    let _old = a.swap(42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_u32_full_lifecycle() {
    let a = AtomicU32::new(1);
    a.store(2, Ordering::SeqCst);
    let _v1 = a.load(Ordering::SeqCst);
    let _v2 = a.swap(3, Ordering::SeqCst);
    let _v3 = a.fetch_add(1, Ordering::SeqCst);
    let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst);
    let _v4 = a.into_inner();
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
fn test_i32_cas(x: &AtomicI32) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_i32_cas_weak(x: &AtomicI32) {
    let _r = x.compare_exchange_weak(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_i32_fetch_add(x: &AtomicI32) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_i32_fetch_sub(x: &AtomicI32) {
    let _v = x.fetch_sub(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_i32_fetch_and(x: &AtomicI32) {
    let _v = x.fetch_and(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_i32_fetch_or(x: &AtomicI32) {
    let _v = x.fetch_or(0x01, Ordering::SeqCst);
}

#[rr::verify]
fn test_i32_fetch_xor(x: &AtomicI32) {
    let _v = x.fetch_xor(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_i32_fetch_nand(x: &AtomicI32) {
    let _v = x.fetch_nand(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_i32_fetch_max(x: &AtomicI32) {
    let _v = x.fetch_max(42, Ordering::SeqCst);
}

#[rr::verify]
fn test_i32_fetch_min(x: &AtomicI32) {
    let _v = x.fetch_min(-10, Ordering::SeqCst);
}

#[rr::verify]
fn test_i32_get_mut() {
    let mut a = AtomicI32::new(10);
    let r = a.get_mut();
    *r = -99;
}

#[rr::verify]
fn test_i32_new_into_inner() {
    let a = AtomicI32::new(-42);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_i32_new_load() {
    let a = AtomicI32::new(-42);
    let _v = a.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_i32_new_store_into_inner() {
    let a = AtomicI32::new(1);
    a.store(-42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_i32_new_swap_into_inner() {
    let a = AtomicI32::new(1);
    let _old = a.swap(-42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_i32_full_lifecycle() {
    let a = AtomicI32::new(1);
    a.store(2, Ordering::SeqCst);
    let _v1 = a.load(Ordering::SeqCst);
    let _v2 = a.swap(3, Ordering::SeqCst);
    let _v3 = a.fetch_add(1, Ordering::SeqCst);
    let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst);
    let _v4 = a.into_inner();
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
fn test_u64_cas(x: &AtomicU64) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_u64_cas_weak(x: &AtomicU64) {
    let _r = x.compare_exchange_weak(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_u64_fetch_add(x: &AtomicU64) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_u64_fetch_sub(x: &AtomicU64) {
    let _v = x.fetch_sub(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_u64_fetch_and(x: &AtomicU64) {
    let _v = x.fetch_and(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_u64_fetch_or(x: &AtomicU64) {
    let _v = x.fetch_or(0x01, Ordering::SeqCst);
}

#[rr::verify]
fn test_u64_fetch_xor(x: &AtomicU64) {
    let _v = x.fetch_xor(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_u64_fetch_nand(x: &AtomicU64) {
    let _v = x.fetch_nand(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_u64_fetch_max(x: &AtomicU64) {
    let _v = x.fetch_max(100, Ordering::SeqCst);
}

#[rr::verify]
fn test_u64_fetch_min(x: &AtomicU64) {
    let _v = x.fetch_min(10, Ordering::SeqCst);
}

#[rr::verify]
fn test_u64_get_mut() {
    let mut a = AtomicU64::new(10);
    let r = a.get_mut();
    *r = 99;
}

#[rr::verify]
fn test_u64_new_into_inner() {
    let a = AtomicU64::new(42);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_u64_new_load() {
    let a = AtomicU64::new(42);
    let _v = a.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_u64_new_store_into_inner() {
    let a = AtomicU64::new(1);
    a.store(42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_u64_new_swap_into_inner() {
    let a = AtomicU64::new(1);
    let _old = a.swap(42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_u64_full_lifecycle() {
    let a = AtomicU64::new(1);
    a.store(2, Ordering::SeqCst);
    let _v1 = a.load(Ordering::SeqCst);
    let _v2 = a.swap(3, Ordering::SeqCst);
    let _v3 = a.fetch_add(1, Ordering::SeqCst);
    let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst);
    let _v4 = a.into_inner();
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
fn test_i64_cas(x: &AtomicI64) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_i64_cas_weak(x: &AtomicI64) {
    let _r = x.compare_exchange_weak(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_i64_fetch_add(x: &AtomicI64) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_i64_fetch_sub(x: &AtomicI64) {
    let _v = x.fetch_sub(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_i64_fetch_and(x: &AtomicI64) {
    let _v = x.fetch_and(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_i64_fetch_or(x: &AtomicI64) {
    let _v = x.fetch_or(0x01, Ordering::SeqCst);
}

#[rr::verify]
fn test_i64_fetch_xor(x: &AtomicI64) {
    let _v = x.fetch_xor(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_i64_fetch_nand(x: &AtomicI64) {
    let _v = x.fetch_nand(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_i64_fetch_max(x: &AtomicI64) {
    let _v = x.fetch_max(42, Ordering::SeqCst);
}

#[rr::verify]
fn test_i64_fetch_min(x: &AtomicI64) {
    let _v = x.fetch_min(-10, Ordering::SeqCst);
}

#[rr::verify]
fn test_i64_get_mut() {
    let mut a = AtomicI64::new(10);
    let r = a.get_mut();
    *r = -99;
}

#[rr::verify]
fn test_i64_new_into_inner() {
    let a = AtomicI64::new(-42);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_i64_new_load() {
    let a = AtomicI64::new(-42);
    let _v = a.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_i64_new_store_into_inner() {
    let a = AtomicI64::new(1);
    a.store(-42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_i64_new_swap_into_inner() {
    let a = AtomicI64::new(1);
    let _old = a.swap(-42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_i64_full_lifecycle() {
    let a = AtomicI64::new(1);
    a.store(2, Ordering::SeqCst);
    let _v1 = a.load(Ordering::SeqCst);
    let _v2 = a.swap(3, Ordering::SeqCst);
    let _v3 = a.fetch_add(1, Ordering::SeqCst);
    let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst);
    let _v4 = a.into_inner();
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
fn test_usize_cas(x: &AtomicUsize) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_usize_cas_weak(x: &AtomicUsize) {
    let _r = x.compare_exchange_weak(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_usize_fetch_add(x: &AtomicUsize) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_usize_fetch_sub(x: &AtomicUsize) {
    let _v = x.fetch_sub(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_usize_fetch_and(x: &AtomicUsize) {
    let _v = x.fetch_and(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_usize_fetch_or(x: &AtomicUsize) {
    let _v = x.fetch_or(0x01, Ordering::SeqCst);
}

#[rr::verify]
fn test_usize_fetch_xor(x: &AtomicUsize) {
    let _v = x.fetch_xor(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_usize_fetch_nand(x: &AtomicUsize) {
    let _v = x.fetch_nand(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_usize_fetch_max(x: &AtomicUsize) {
    let _v = x.fetch_max(42, Ordering::SeqCst);
}

#[rr::verify]
fn test_usize_fetch_min(x: &AtomicUsize) {
    let _v = x.fetch_min(10, Ordering::SeqCst);
}

#[rr::verify]
fn test_usize_get_mut() {
    let mut a = AtomicUsize::new(10);
    let r = a.get_mut();
    *r = 99;
}

#[rr::verify]
fn test_usize_new_into_inner() {
    let a = AtomicUsize::new(42);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_usize_new_load() {
    let a = AtomicUsize::new(42);
    let _v = a.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_usize_new_store_into_inner() {
    let a = AtomicUsize::new(1);
    a.store(42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_usize_new_swap_into_inner() {
    let a = AtomicUsize::new(1);
    let _old = a.swap(42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_usize_full_lifecycle() {
    let a = AtomicUsize::new(1);
    a.store(2, Ordering::SeqCst);
    let _v1 = a.load(Ordering::SeqCst);
    let _v2 = a.swap(3, Ordering::SeqCst);
    let _v3 = a.fetch_add(1, Ordering::SeqCst);
    let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst);
    let _v4 = a.into_inner();
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
fn test_isize_cas(x: &AtomicIsize) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_isize_cas_weak(x: &AtomicIsize) {
    let _r = x.compare_exchange_weak(10, 20, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_isize_fetch_add(x: &AtomicIsize) {
    let _v = x.fetch_add(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_isize_fetch_sub(x: &AtomicIsize) {
    let _v = x.fetch_sub(1, Ordering::SeqCst);
}

#[rr::verify]
fn test_isize_fetch_and(x: &AtomicIsize) {
    let _v = x.fetch_and(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_isize_fetch_or(x: &AtomicIsize) {
    let _v = x.fetch_or(0x01, Ordering::SeqCst);
}

#[rr::verify]
fn test_isize_fetch_xor(x: &AtomicIsize) {
    let _v = x.fetch_xor(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_isize_fetch_nand(x: &AtomicIsize) {
    let _v = x.fetch_nand(0x0F, Ordering::SeqCst);
}

#[rr::verify]
fn test_isize_fetch_max(x: &AtomicIsize) {
    let _v = x.fetch_max(42, Ordering::SeqCst);
}

#[rr::verify]
fn test_isize_fetch_min(x: &AtomicIsize) {
    let _v = x.fetch_min(-10, Ordering::SeqCst);
}

#[rr::verify]
fn test_isize_get_mut() {
    let mut a = AtomicIsize::new(10);
    let r = a.get_mut();
    *r = -99;
}

#[rr::verify]
fn test_isize_new_into_inner() {
    let a = AtomicIsize::new(-42);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_isize_new_load() {
    let a = AtomicIsize::new(-42);
    let _v = a.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_isize_new_store_into_inner() {
    let a = AtomicIsize::new(1);
    a.store(-42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_isize_new_swap_into_inner() {
    let a = AtomicIsize::new(1);
    let _old = a.swap(-42, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_isize_full_lifecycle() {
    let a = AtomicIsize::new(1);
    a.store(2, Ordering::SeqCst);
    let _v1 = a.load(Ordering::SeqCst);
    let _v2 = a.swap(3, Ordering::SeqCst);
    let _v3 = a.fetch_add(1, Ordering::SeqCst);
    let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst);
    let _v4 = a.into_inner();
}

// ============================================================
// AtomicBool
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
fn test_bool_cas_weak(x: &AtomicBool) {
    let _r = x.compare_exchange_weak(true, false, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_bool_fetch_and(x: &AtomicBool) {
    let _v = x.fetch_and(true, Ordering::SeqCst);
}

#[rr::verify]
fn test_bool_fetch_or(x: &AtomicBool) {
    let _v = x.fetch_or(true, Ordering::SeqCst);
}

#[rr::verify]
fn test_bool_fetch_xor(x: &AtomicBool) {
    let _v = x.fetch_xor(true, Ordering::SeqCst);
}

#[rr::verify]
fn test_bool_fetch_nand(x: &AtomicBool) {
    let _v = x.fetch_nand(true, Ordering::SeqCst);
}

#[rr::verify]
fn test_bool_get_mut() {
    let mut a = AtomicBool::new(false);
    let r = a.get_mut();
    *r = true;
}

#[rr::verify]
fn test_bool_new_into_inner() {
    let a = AtomicBool::new(true);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_bool_new_load() {
    let a = AtomicBool::new(true);
    let _v = a.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_bool_new_store_into_inner() {
    let a = AtomicBool::new(false);
    a.store(true, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_bool_new_swap_into_inner() {
    let a = AtomicBool::new(true);
    let _old = a.swap(false, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_bool_full_lifecycle() {
    let a = AtomicBool::new(true);
    a.store(false, Ordering::SeqCst);
    let _v1 = a.load(Ordering::SeqCst);
    let _v2 = a.swap(true, Ordering::SeqCst);
    let _v3 = a.fetch_and(false, Ordering::SeqCst);
    let _r = a.compare_exchange(true, false, Ordering::SeqCst, Ordering::SeqCst);
    let _v4 = a.into_inner();
}

// ============================================================
// AtomicPtr
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

#[rr::verify]
fn test_ptr_cas_weak(x: &AtomicPtr<u8>, old: *mut u8, new_val: *mut u8) {
    let _r = x.compare_exchange_weak(old, new_val, Ordering::SeqCst, Ordering::SeqCst);
}

#[rr::verify]
fn test_ptr_get_mut(p: *mut u8) {
    let mut a = AtomicPtr::new(p);
    let _r = a.get_mut();
}

#[rr::verify]
fn test_ptr_new_into_inner(p: *mut u8) {
    let a = AtomicPtr::new(p);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_ptr_new_load(p: *mut u8) {
    let a = AtomicPtr::new(p);
    let _v = a.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_ptr_new_store_into_inner(p: *mut u8, q: *mut u8) {
    let a = AtomicPtr::new(p);
    a.store(q, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_ptr_new_swap_into_inner(p: *mut u8, q: *mut u8) {
    let a = AtomicPtr::new(p);
    let _old = a.swap(q, Ordering::SeqCst);
    let _v = a.into_inner();
}

#[rr::verify]
fn test_ptr_full_lifecycle(p: *mut u8, q: *mut u8) {
    let a = AtomicPtr::new(p);
    a.store(q, Ordering::SeqCst);
    let _v1 = a.load(Ordering::SeqCst);
    let _v2 = a.swap(p, Ordering::SeqCst);
    let _r = a.compare_exchange(p, q, Ordering::SeqCst, Ordering::SeqCst);
    let _v3 = a.into_inner();
}

// ============================================================
// Pattern coverage tests
// ============================================================

// Owned atomic: create, store, load through implicit shared ref
#[rr::verify]
fn test_owned_store_load() {
    let a = AtomicU8::new(10);
    a.store(42, Ordering::SeqCst);
    let _v = a.load(Ordering::SeqCst);
}

// CAS result destructuring — match on Ok/Err branches
#[rr::verify]
fn test_cas_match(x: &AtomicU8) {
    match x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst) {
        Ok(_old) => {},
        Err(_cur) => {},
    }
}

// CAS in loop — requires loop invariant annotation for proof automation
#[rr::skip]
fn test_cas_loop(x: &AtomicU8) {
    let mut current = x.load(Ordering::SeqCst);
    loop {
        match x.compare_exchange_weak(current, current + 1, Ordering::SeqCst, Ordering::SeqCst) {
            Ok(_) => break,
            Err(c) => current = c,
        }
    }
}

// Load result used in arithmetic — proof automation cannot resolve existential + binop
#[rr::skip]
fn test_load_in_expr(x: &AtomicU8) {
    let _v = x.load(Ordering::SeqCst) + 1;
}

// Result of one atomic feeds into another
#[rr::verify]
fn test_swap_into_store(x: &AtomicU8, y: &AtomicU8) {
    let old = x.swap(42, Ordering::SeqCst);
    y.store(old, Ordering::SeqCst);
}

// AtomicPtr<T> where T is not u8
#[rr::verify]
fn test_ptr_u32_load(x: &AtomicPtr<u32>) {
    let _v = x.load(Ordering::SeqCst);
}

// Two loads + arithmetic — proof automation cannot resolve two existentials + binop
#[rr::skip]
fn test_two_atomics(x: &AtomicU8, y: &AtomicU8) {
    let a = x.load(Ordering::SeqCst);
    let b = y.load(Ordering::SeqCst);
    let _sum = a + b;
}

// Chained data-dependent atomic operations
#[rr::verify]
fn test_fetch_chain(x: &AtomicU8, y: &AtomicU8) {
    let a = x.fetch_add(1, Ordering::SeqCst);
    let _b = y.fetch_sub(a, Ordering::SeqCst);
}

// Nested atomic pointer — AtomicPtr pointing to AtomicU8
#[rr::verify]
fn test_nested_atomic_ptr(x: &AtomicPtr<AtomicU8>) {
    let _v = x.load(Ordering::SeqCst);
}

// Atomic as struct field — field projection produces &AtomicU8
struct Counter {
    count: AtomicU8,
}
#[rr::verify]
fn test_struct_field_load(c: &Counter) {
    let _v = c.count.load(Ordering::SeqCst);
}

#[rr::verify]
fn test_struct_field_store(c: &Counter) {
    c.count.store(42, Ordering::SeqCst);
}

// Standalone fence — not registered as atomic method or intrinsic
#[rr::skip]
fn test_fence() {
    std::sync::atomic::fence(Ordering::SeqCst);
}

// Ordering through a local variable — MIR walk-back does not resolve across basic blocks
#[rr::skip]
fn test_ordering_via_variable(x: &AtomicU8) {
    let ord = Ordering::SeqCst;
    let _v = x.load(ord);
}

// CAS with mixed orderings — SC model rejects non-SeqCst failure ordering
#[rr::skip]
fn test_cas_mixed_ordering(x: &AtomicU8) {
    let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::Acquire);
}

// as_ptr — not an atomic operation, no shim support
#[rr::skip]
fn test_as_ptr(x: &AtomicU8) {
    let _p = x.as_ptr();
}

// from_ptr — unsafe, nightly-only, no shim support
#[rr::skip]
unsafe fn test_from_ptr(p: *mut u8) {
    let _a = unsafe { AtomicU8::from_ptr(p) };
}
