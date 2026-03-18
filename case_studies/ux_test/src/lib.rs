// Test: UX without boilerplate.
// This file intentionally omits:
//   #![feature(register_tool)]
//   #![register_tool(rr)]
//   #![feature(custom_inner_attributes)]
// refinedrust-rustc auto-injects them via -Zcrate-attr.
// If this test fails to compile, the injection is broken.

#![rr::include("stdlib")]

use std::sync::atomic::{AtomicU8, Ordering};

#[rr::verify]
fn test_load(x: &AtomicU8) {
    let _v = x.load(Ordering::SeqCst);
}
