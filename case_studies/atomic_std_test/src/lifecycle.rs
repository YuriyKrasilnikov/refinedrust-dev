use std::sync::atomic::*;

// ============================================================
// Integer atomics — lifecycle (new, get_mut, into_inner, sequences)
// ============================================================

#[rr::verify] fn test_u8_get_mut() { let mut a = AtomicU8::new(10); let r = a.get_mut(); *r = 99; }
#[rr::verify] fn test_u8_new_into_inner() { let a = AtomicU8::new(42); let _v = a.into_inner(); }
#[rr::verify] fn test_u8_new_load() { let a = AtomicU8::new(42); let _v = a.load(Ordering::SeqCst); }
#[rr::verify] fn test_u8_new_store_into_inner() { let a = AtomicU8::new(1); a.store(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_u8_new_swap_into_inner() { let a = AtomicU8::new(1); let _old = a.swap(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_u8_full_lifecycle() { let a = AtomicU8::new(1); a.store(2, Ordering::SeqCst); let _v1 = a.load(Ordering::SeqCst); let _v2 = a.swap(3, Ordering::SeqCst); let _v3 = a.fetch_add(1, Ordering::SeqCst); let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst); let _v4 = a.into_inner(); }

#[rr::verify] fn test_i8_get_mut() { let mut a = AtomicI8::new(10); let r = a.get_mut(); *r = 99; }
#[rr::verify] fn test_i8_new_into_inner() { let a = AtomicI8::new(42); let _v = a.into_inner(); }
#[rr::verify] fn test_i8_new_load() { let a = AtomicI8::new(42); let _v = a.load(Ordering::SeqCst); }
#[rr::verify] fn test_i8_new_store_into_inner() { let a = AtomicI8::new(1); a.store(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_i8_new_swap_into_inner() { let a = AtomicI8::new(1); let _old = a.swap(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_i8_full_lifecycle() { let a = AtomicI8::new(1); a.store(2, Ordering::SeqCst); let _v1 = a.load(Ordering::SeqCst); let _v2 = a.swap(3, Ordering::SeqCst); let _v3 = a.fetch_add(1, Ordering::SeqCst); let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst); let _v4 = a.into_inner(); }

#[rr::verify] fn test_u16_get_mut() { let mut a = AtomicU16::new(10); let r = a.get_mut(); *r = 99; }
#[rr::verify] fn test_u16_new_into_inner() { let a = AtomicU16::new(42); let _v = a.into_inner(); }
#[rr::verify] fn test_u16_new_load() { let a = AtomicU16::new(42); let _v = a.load(Ordering::SeqCst); }
#[rr::verify] fn test_u16_new_store_into_inner() { let a = AtomicU16::new(1); a.store(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_u16_new_swap_into_inner() { let a = AtomicU16::new(1); let _old = a.swap(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_u16_full_lifecycle() { let a = AtomicU16::new(1); a.store(2, Ordering::SeqCst); let _v1 = a.load(Ordering::SeqCst); let _v2 = a.swap(3, Ordering::SeqCst); let _v3 = a.fetch_add(1, Ordering::SeqCst); let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst); let _v4 = a.into_inner(); }

#[rr::verify] fn test_i16_get_mut() { let mut a = AtomicI16::new(10); let r = a.get_mut(); *r = 99; }
#[rr::verify] fn test_i16_new_into_inner() { let a = AtomicI16::new(42); let _v = a.into_inner(); }
#[rr::verify] fn test_i16_new_load() { let a = AtomicI16::new(42); let _v = a.load(Ordering::SeqCst); }
#[rr::verify] fn test_i16_new_store_into_inner() { let a = AtomicI16::new(1); a.store(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_i16_new_swap_into_inner() { let a = AtomicI16::new(1); let _old = a.swap(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_i16_full_lifecycle() { let a = AtomicI16::new(1); a.store(2, Ordering::SeqCst); let _v1 = a.load(Ordering::SeqCst); let _v2 = a.swap(3, Ordering::SeqCst); let _v3 = a.fetch_add(1, Ordering::SeqCst); let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst); let _v4 = a.into_inner(); }

#[rr::verify] fn test_u32_get_mut() { let mut a = AtomicU32::new(10); let r = a.get_mut(); *r = 99; }
#[rr::verify] fn test_u32_new_into_inner() { let a = AtomicU32::new(42); let _v = a.into_inner(); }
#[rr::verify] fn test_u32_new_load() { let a = AtomicU32::new(42); let _v = a.load(Ordering::SeqCst); }
#[rr::verify] fn test_u32_new_store_into_inner() { let a = AtomicU32::new(1); a.store(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_u32_new_swap_into_inner() { let a = AtomicU32::new(1); let _old = a.swap(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_u32_full_lifecycle() { let a = AtomicU32::new(1); a.store(2, Ordering::SeqCst); let _v1 = a.load(Ordering::SeqCst); let _v2 = a.swap(3, Ordering::SeqCst); let _v3 = a.fetch_add(1, Ordering::SeqCst); let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst); let _v4 = a.into_inner(); }

#[rr::verify] fn test_i32_get_mut() { let mut a = AtomicI32::new(10); let r = a.get_mut(); *r = 99; }
#[rr::verify] fn test_i32_new_into_inner() { let a = AtomicI32::new(42); let _v = a.into_inner(); }
#[rr::verify] fn test_i32_new_load() { let a = AtomicI32::new(42); let _v = a.load(Ordering::SeqCst); }
#[rr::verify] fn test_i32_new_store_into_inner() { let a = AtomicI32::new(1); a.store(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_i32_new_swap_into_inner() { let a = AtomicI32::new(1); let _old = a.swap(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_i32_full_lifecycle() { let a = AtomicI32::new(1); a.store(2, Ordering::SeqCst); let _v1 = a.load(Ordering::SeqCst); let _v2 = a.swap(3, Ordering::SeqCst); let _v3 = a.fetch_add(1, Ordering::SeqCst); let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst); let _v4 = a.into_inner(); }

#[rr::verify] fn test_u64_get_mut() { let mut a = AtomicU64::new(10); let r = a.get_mut(); *r = 99; }
#[rr::verify] fn test_u64_new_into_inner() { let a = AtomicU64::new(42); let _v = a.into_inner(); }
#[rr::verify] fn test_u64_new_load() { let a = AtomicU64::new(42); let _v = a.load(Ordering::SeqCst); }
#[rr::verify] fn test_u64_new_store_into_inner() { let a = AtomicU64::new(1); a.store(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_u64_new_swap_into_inner() { let a = AtomicU64::new(1); let _old = a.swap(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_u64_full_lifecycle() { let a = AtomicU64::new(1); a.store(2, Ordering::SeqCst); let _v1 = a.load(Ordering::SeqCst); let _v2 = a.swap(3, Ordering::SeqCst); let _v3 = a.fetch_add(1, Ordering::SeqCst); let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst); let _v4 = a.into_inner(); }

#[rr::verify] fn test_i64_get_mut() { let mut a = AtomicI64::new(10); let r = a.get_mut(); *r = 99; }
#[rr::verify] fn test_i64_new_into_inner() { let a = AtomicI64::new(42); let _v = a.into_inner(); }
#[rr::verify] fn test_i64_new_load() { let a = AtomicI64::new(42); let _v = a.load(Ordering::SeqCst); }
#[rr::verify] fn test_i64_new_store_into_inner() { let a = AtomicI64::new(1); a.store(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_i64_new_swap_into_inner() { let a = AtomicI64::new(1); let _old = a.swap(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_i64_full_lifecycle() { let a = AtomicI64::new(1); a.store(2, Ordering::SeqCst); let _v1 = a.load(Ordering::SeqCst); let _v2 = a.swap(3, Ordering::SeqCst); let _v3 = a.fetch_add(1, Ordering::SeqCst); let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst); let _v4 = a.into_inner(); }

#[rr::verify] fn test_usize_get_mut() { let mut a = AtomicUsize::new(10); let r = a.get_mut(); *r = 99; }
#[rr::verify] fn test_usize_new_into_inner() { let a = AtomicUsize::new(42); let _v = a.into_inner(); }
#[rr::verify] fn test_usize_new_load() { let a = AtomicUsize::new(42); let _v = a.load(Ordering::SeqCst); }
#[rr::verify] fn test_usize_new_store_into_inner() { let a = AtomicUsize::new(1); a.store(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_usize_new_swap_into_inner() { let a = AtomicUsize::new(1); let _old = a.swap(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_usize_full_lifecycle() { let a = AtomicUsize::new(1); a.store(2, Ordering::SeqCst); let _v1 = a.load(Ordering::SeqCst); let _v2 = a.swap(3, Ordering::SeqCst); let _v3 = a.fetch_add(1, Ordering::SeqCst); let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst); let _v4 = a.into_inner(); }

#[rr::verify] fn test_isize_get_mut() { let mut a = AtomicIsize::new(10); let r = a.get_mut(); *r = 99; }
#[rr::verify] fn test_isize_new_into_inner() { let a = AtomicIsize::new(42); let _v = a.into_inner(); }
#[rr::verify] fn test_isize_new_load() { let a = AtomicIsize::new(42); let _v = a.load(Ordering::SeqCst); }
#[rr::verify] fn test_isize_new_store_into_inner() { let a = AtomicIsize::new(1); a.store(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_isize_new_swap_into_inner() { let a = AtomicIsize::new(1); let _old = a.swap(42, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_isize_full_lifecycle() { let a = AtomicIsize::new(1); a.store(2, Ordering::SeqCst); let _v1 = a.load(Ordering::SeqCst); let _v2 = a.swap(3, Ordering::SeqCst); let _v3 = a.fetch_add(1, Ordering::SeqCst); let _r = a.compare_exchange(4, 5, Ordering::SeqCst, Ordering::SeqCst); let _v4 = a.into_inner(); }

// ============================================================
// AtomicBool — lifecycle
// ============================================================

#[rr::verify] fn test_bool_get_mut() { let mut a = AtomicBool::new(true); let r = a.get_mut(); *r = false; }
#[rr::verify] fn test_bool_new_into_inner() { let a = AtomicBool::new(true); let _v = a.into_inner(); }
#[rr::verify] fn test_bool_new_load() { let a = AtomicBool::new(false); let _v = a.load(Ordering::SeqCst); }
#[rr::verify] fn test_bool_new_store_into_inner() { let a = AtomicBool::new(true); a.store(false, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_bool_new_swap_into_inner() { let a = AtomicBool::new(true); let _old = a.swap(false, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_bool_full_lifecycle() { let a = AtomicBool::new(true); a.store(false, Ordering::SeqCst); let _v1 = a.load(Ordering::SeqCst); let _v2 = a.swap(true, Ordering::SeqCst); let _r = a.compare_exchange(true, false, Ordering::SeqCst, Ordering::SeqCst); let _v3 = a.into_inner(); }

// ============================================================
// AtomicPtr — lifecycle
// ============================================================

#[rr::verify] fn test_ptr_get_mut(p: *mut u8) { let mut a = AtomicPtr::new(p); let r = a.get_mut(); let _v = *r; }
#[rr::verify] fn test_ptr_new_into_inner(p: *mut u8) { let a = AtomicPtr::new(p); let _v = a.into_inner(); }
#[rr::verify] fn test_ptr_new_load(p: *mut u8) { let a = AtomicPtr::new(p); let _v = a.load(Ordering::SeqCst); }
#[rr::verify] fn test_ptr_new_store_into_inner(p: *mut u8, q: *mut u8) { let a = AtomicPtr::new(p); a.store(q, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_ptr_new_swap_into_inner(p: *mut u8, q: *mut u8) { let a = AtomicPtr::new(p); let _old = a.swap(q, Ordering::SeqCst); let _v = a.into_inner(); }
#[rr::verify] fn test_ptr_full_lifecycle(p: *mut u8, q: *mut u8) { let a = AtomicPtr::new(p); a.store(q, Ordering::SeqCst); let _v1 = a.load(Ordering::SeqCst); let _v2 = a.swap(p, Ordering::SeqCst); let _r = a.compare_exchange(p, q, Ordering::SeqCst, Ordering::SeqCst); let _v3 = a.into_inner(); }
