use std::sync::atomic::*;

// Tests that document known limitations.
// All marked #[rr::skip] — they fail at frontend or Coq level.
// Each documents the expected error in its comment.

// ============================================================
// Non-SeqCst orderings — SC model rejects
// ============================================================

#[rr::skip] fn test_load_relaxed(x: &AtomicU8) { let _v = x.load(Ordering::Relaxed); }
#[rr::skip] fn test_store_release(x: &AtomicU8) { x.store(42, Ordering::Release); }
#[rr::skip] fn test_load_acquire(x: &AtomicU8) { let _v = x.load(Ordering::Acquire); }
#[rr::skip] fn test_cas_mixed_ordering(x: &AtomicU8) { let _r = x.compare_exchange(10, 20, Ordering::SeqCst, Ordering::Acquire); }

// ============================================================
// Ordering resolution
// ============================================================

// Ordering through a local variable — MIR walk-back does not resolve across basic blocks
#[rr::skip]
fn test_ordering_via_variable(x: &AtomicU8) {
    let ord = Ordering::SeqCst;
    let _v = x.load(ord);
}

// ============================================================
// Unsupported operations
// ============================================================

// Standalone fence — not dispatched as atomic method
#[rr::skip] fn test_fence() { std::sync::atomic::fence(Ordering::SeqCst); }

// as_ptr — not an atomic operation, no shim
#[rr::verify] fn test_as_ptr(x: &AtomicU8) { let _p = x.as_ptr(); }

// from_ptr — constructs atomic reference from raw pointer (unsafe)
#[rr::verify] unsafe fn test_from_ptr(p: *mut u8) { let _a = unsafe { AtomicU8::from_ptr(p) }; }

// ============================================================
// Automation limits — frontend passes, Coq proof incomplete
// ============================================================

// Checked add on atomic load — overflow sidecondition unprovable without precondition
#[rr::skip] fn test_checked_add(x: &AtomicU8) { let _v = x.load(Ordering::SeqCst) + 1; }

// Two loads + checked add — same overflow issue, two existentials
#[rr::skip]
fn test_two_loads_add(x: &AtomicU8, y: &AtomicU8) {
    let a = x.load(Ordering::SeqCst);
    let b = y.load(Ordering::SeqCst);
    let _sum = a + b;
}

// CAS in loop with checked add — overflow + loop invariant needed
#[rr::skip]
fn test_cas_loop_add(x: &AtomicU8) {
    let mut current = x.load(Ordering::SeqCst);
    loop {
        match x.compare_exchange_weak(current, current + 1, Ordering::SeqCst, Ordering::SeqCst) {
            Ok(_) => break,
            Err(c) => current = c,
        }
    }
}

// CAS loop with bitwise OR (no overflow) — loop invariant still needed
#[rr::skip]
fn test_cas_loop_bitor(x: &AtomicU8) {
    let mut current = x.load(Ordering::SeqCst);
    loop {
        match x.compare_exchange_weak(current, current | 0x80, Ordering::SeqCst, Ordering::SeqCst) {
            Ok(_) => break,
            Err(c) => current = c,
        }
    }
}
