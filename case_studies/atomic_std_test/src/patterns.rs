use std::sync::atomic::*;

// ============================================================
// Ownership and sharing patterns
// ============================================================

// Owned atomic: create, store, load through implicit shared ref
#[rr::verify]
fn test_owned_store_load() {
    let a = AtomicU8::new(10);
    a.store(42, Ordering::SeqCst);
    let _v = a.load(Ordering::SeqCst);
}

// Owned atomic passed as shared ref to another function
#[rr::verify]
fn load_via_shared_ref(x: &AtomicU8) {
    let _v = x.load(Ordering::SeqCst);
}
#[rr::verify]
fn test_explicit_sharing() {
    let a = AtomicU8::new(42);
    a.store(10, Ordering::SeqCst);
    load_via_shared_ref(&a);
}

// Store with `let _ = ...` binding — verifies both MIR patterns work
#[rr::verify]
fn test_store_let_binding(x: &AtomicU8) {
    let _ = x.store(42, Ordering::SeqCst);
}

// Store inside a conditional branch
#[rr::verify]
fn test_store_in_branch(x: &AtomicU8, cond: bool) {
    if cond {
        x.store(42, Ordering::SeqCst);
    }
}

// ============================================================
// CAS patterns
// ============================================================

// CAS result destructuring — match on Ok/Err branches
#[rr::verify]
fn test_cas_match(x: &AtomicU8) {
    match x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::SeqCst) {
        Ok(_old) => {},
        Err(_cur) => {},
    }
}

// ============================================================
// Value chaining
// ============================================================

// Result of one atomic feeds into another
#[rr::verify]
fn test_swap_into_store(x: &AtomicU8, y: &AtomicU8) {
    let old = x.swap(42, Ordering::SeqCst);
    y.store(old, Ordering::SeqCst);
}

// Chained data-dependent atomic operations
#[rr::verify]
fn test_fetch_chain(x: &AtomicU8, y: &AtomicU8) {
    let a = x.fetch_add(1, Ordering::SeqCst);
    let _b = y.fetch_sub(a, Ordering::SeqCst);
}

// ============================================================
// Arithmetic on atomic load results
// ============================================================

// Wrapping add on atomic load result — u8::wrapping_add not in stdlib shim
#[rr::skip]
fn test_wrapping_add(x: &AtomicU8) {
    let v = x.load(Ordering::SeqCst);
    let _w = v.wrapping_add(1);
}

// Saturating add on atomic load result — u8::saturating_add not in stdlib shim
#[rr::skip]
fn test_saturating_add(x: &AtomicU8) {
    let v = x.load(Ordering::SeqCst);
    let _w = v.saturating_add(1);
}

// Checked add with runtime guard — verifier proves overflow impossible in branch
#[rr::verify]
fn test_guarded_add(x: &AtomicU8) {
    let v = x.load(Ordering::SeqCst);
    if v < 255 {
        let _w = v + 1;
    }
}

// Bitwise OR on atomic load result — always within bounds
#[rr::verify]
fn test_bitwise_or(x: &AtomicU8) {
    let v = x.load(Ordering::SeqCst);
    let _w = v | 1;
}

// ============================================================
// Type variations
// ============================================================

// AtomicPtr<T> where T is not u8
#[rr::verify]
fn test_ptr_u32_load(x: &AtomicPtr<u32>) {
    let _v = x.load(Ordering::SeqCst);
}

// Nested atomic pointer — AtomicPtr pointing to AtomicU8
#[rr::verify]
fn test_nested_atomic_ptr(x: &AtomicPtr<AtomicU8>) {
    let _v = x.load(Ordering::SeqCst);
}

// Multiple atomics in one function
#[rr::verify]
fn test_two_loads(x: &AtomicU8, y: &AtomicU8) {
    let _a = x.load(Ordering::SeqCst);
    let _b = y.load(Ordering::SeqCst);
}

// ============================================================
// Struct field access
// ============================================================

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
