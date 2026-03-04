#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

/// Minimal atomic type for integration testing.
///
/// Tests the full pipeline: Rust annotations → frontend mode(atomic) method
/// mapping → Caesium Deref ScOrd → Coq TypedAtomicLoadVal instance.
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
    /// Spec-only: body not verified. Calls are intercepted by mode(atomic)
    /// method mapping and translated to Deref ScOrd.
    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn load(&self) -> u8 {
        unimplemented!()
    }

    /// Spec-only: intercepted by mode(atomic) → Assign ScOrd.
    #[rr::only_spec]
    pub fn store(&self, _value: u8) {
        unimplemented!()
    }

    /// Spec-only: intercepted by mode(atomic) → AtomicRMW RmwXchg.
    #[rr::only_spec]
    #[rr::exists("x" : "Z")]
    #[rr::returns("x")]
    pub fn swap(&self, _value: u8) -> u8 {
        unimplemented!()
    }
}

#[rr::verify]
fn test_load(x: &MyAtomicU8) {
    let _v = x.load();
}

#[rr::verify]
fn test_store(x: &MyAtomicU8) {
    x.store(42);
}

#[rr::verify]
fn test_swap(x: &MyAtomicU8) {
    let _v = x.swap(99);
}
