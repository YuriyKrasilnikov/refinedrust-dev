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

// Checked subtraction with runtime guard — verifier proves underflow impossible
#[rr::verify]
fn test_guarded_sub(x: &AtomicU8) {
    let v = x.load(Ordering::SeqCst);
    if v > 0 {
        let _w = v - 1;
    }
}

// Bitwise OR on atomic load result — always within bounds
#[rr::verify]
fn test_bitwise_or(x: &AtomicU8) {
    let v = x.load(Ordering::SeqCst);
    let _w = v | 1;
}

// ============================================================
// Group of related functions — shared protocol
// ============================================================

// SafeCounter: group of functions that together maintain a valid state.
// Each function verified standalone — correct for any input.
struct SafeCounter {
    count: AtomicU8,
}

// --- Standalone verification: each fn correct for all inputs ---

// Self-contained: always returns valid SafeCounter
#[rr::verify]
fn safe_counter_new() -> SafeCounter {
    SafeCounter { count: AtomicU8::new(0) }
}

// Self-contained: runtime guard prevents overflow for any input
#[rr::verify]
fn safe_counter_increment(c: &SafeCounter) {
    let v = c.count.load(Ordering::SeqCst);
    if v < 255 {
        c.count.store(v + 1, Ordering::SeqCst);
    }
}

// Self-contained: load always safe
#[rr::verify]
fn safe_counter_get(c: &SafeCounter) -> u8 {
    c.count.load(Ordering::SeqCst)
}

// --- Composition: function calls other verified functions ---

// Inline protocol (no cross-function calls)
#[rr::verify]
fn safe_counter_inline_use() {
    let c = SafeCounter { count: AtomicU8::new(0) };
    let v = c.count.load(Ordering::SeqCst);
    if v < 255 {
        c.count.store(v + 1, Ordering::SeqCst);
    }
    let _result = c.count.load(Ordering::SeqCst);
}

// Composition via calls — uses specs of new/increment/get (GAP 33: verify as group)
#[rr::skip]
fn safe_counter_composed_use() {
    let c = safe_counter_new();
    safe_counter_increment(&c);
    safe_counter_increment(&c);
    let _v = safe_counter_get(&c);
}

// --- Functions that are NOT self-contained (depend on group context) ---

// Unsafe increment without guard — panics at 255.
// Standalone: proof MUST fail (correctly finds bug).
// In group context with new() guaranteeing 0: would need max-call-count proof.
#[rr::skip]
fn unsafe_counter_increment(c: &SafeCounter) {
    let v = c.count.load(Ordering::SeqCst);
    c.count.store(v + 1, Ordering::SeqCst);  // no guard!
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

// ============================================================
// Pointer conversion (as_ptr / from_ptr)
// ============================================================

// as_ptr + dereference returned raw pointer
#[rr::skip]
unsafe fn test_as_ptr_deref(x: &AtomicU8) {
    let p = x.as_ptr();
    let _v = unsafe { *p };
}

// from_ptr + load through returned reference
#[rr::verify]
unsafe fn test_from_ptr_load(p: *mut u8) {
    let a = unsafe { AtomicU8::from_ptr(p) };
    let _v = a.load(Ordering::SeqCst);
}

// as_ptr → from_ptr roundtrip
#[rr::verify]
unsafe fn test_as_ptr_from_ptr_roundtrip(x: &AtomicU8) {
    let p = x.as_ptr();
    let a = unsafe { AtomicU8::from_ptr(p) };
    let _v = a.load(Ordering::SeqCst);
}

// Explicit lifetime annotation on let binding — annotation ordering issue
// get_initial_closure_constraints generates CopyLftName from local PlaceRegion
// BEFORE it's defined by assignment annotations. Needs topological sort of bb0 annotations.
#[rr::skip]
unsafe fn test_from_ptr_static(p: *mut u8) {
    let _a: &'static AtomicU8 = unsafe { AtomicU8::from_ptr(p) };
}

#[rr::skip]
fn test_explicit_static_ref(x: &'static AtomicU8) {
    let _v: &'static AtomicU8 = x;
}

#[rr::skip]
fn test_explicit_lifetime_ref<'a>(x: &'a AtomicU8) {
    let _v: &'a AtomicU8 = x;
}

// ============================================================
// AtomicPtr extended operations
// ============================================================

// AtomicPtr store + load roundtrip
#[rr::verify]
fn test_ptr_store_load(x: &AtomicPtr<u8>, p: *mut u8) {
    x.store(p, Ordering::SeqCst);
    let _v = x.load(Ordering::SeqCst);
}

// AtomicPtr swap
#[rr::verify]
fn test_ptr_swap_val(x: &AtomicPtr<u8>, p: *mut u8) {
    let _old = x.swap(p, Ordering::SeqCst);
}

// ============================================================
// Unsupported std atomic API — documented
// ============================================================

// fetch_update — requires closure, cannot map to single Caesium primitive
#[rr::skip]
fn test_fetch_update(x: &AtomicU8) {
    let _r = x.fetch_update(Ordering::SeqCst, Ordering::SeqCst, |v| {
        if v < 200 { Some(v + 1) } else { None }
    });
}

// ============================================================
// Composition — verifying cross-function calls
// ============================================================

// Verifier should use specs of new/increment/get to prove this safe
#[rr::skip]
fn test_composed_counter_use() {
    let c = safe_counter_new();
    safe_counter_increment(&c);
    safe_counter_increment(&c);
    let _v = safe_counter_get(&c);
}

// ============================================================
// Higher-order — callback preserves safety
// ============================================================

// Callback operates on atomic value — verifier needs closure spec propagation
#[rr::skip]
fn test_apply_callback(f: fn(u8) -> u8, x: &AtomicU8) {
    let v = x.load(Ordering::SeqCst);
    x.store(f(v), Ordering::SeqCst);
}

// ============================================================
// Non-U8 type with guarded arithmetic
// ============================================================

// Same pattern as test_guarded_add but on AtomicU32
#[rr::verify]
fn test_u32_guarded_add(x: &AtomicU32) {
    let v = x.load(Ordering::SeqCst);
    if v < u32::MAX {
        let _w = v + 1;
    }
}

// Signed type: guarded add on AtomicI8 (range -128..127)
#[rr::verify]
fn test_i8_guarded_add(x: &AtomicI8) {
    let v = x.load(Ordering::SeqCst);
    if v < i8::MAX {
        let _w = v + 1;
    }
}

// Signed type: guarded subtraction on AtomicI8
#[rr::verify]
fn test_i8_guarded_sub(x: &AtomicI8) {
    let v = x.load(Ordering::SeqCst);
    if v > i8::MIN {
        let _w = v - 1;
    }
}
