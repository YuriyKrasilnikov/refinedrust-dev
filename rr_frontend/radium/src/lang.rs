use derive_more::Display;

use crate::coq;

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Display)]
pub enum IntType {
    #[display("I8")]
    I8,

    #[display("I16")]
    I16,

    #[display("I32")]
    I32,

    #[display("I64")]
    I64,

    #[display("I128")]
    I128,

    #[display("U8")]
    U8,

    #[display("U16")]
    U16,

    #[display("U32")]
    U32,

    #[display("U64")]
    U64,

    #[display("U128")]
    U128,

    #[display("ISize")]
    ISize,

    #[display("USize")]
    USize,
}

// NOTE: see ty::layout::layout_of_uncached for the rustc description of this.
pub(crate) static BOOL_REPR: IntType = IntType::U8;

/// A syntactic `RefinedRust` type.
///
/// Every semantic `RefinedRust` type has a corresponding syntactic type that determines its
/// representation in memory.
///
/// A syntactic type does not necessarily specify a concrete [layout]. A [layout] is only fixed once
/// a specific layout algorithm that resolves the non-deterministic choice of the compiler.
#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug, Display)]
pub enum SynType {
    #[display("BoolSynType")]
    Bool,

    #[display("CharSynType")]
    Char,

    #[display("(IntSynType {})", _0)]
    Int(IntType),

    #[display("PtrSynType")]
    Ptr,

    #[display("FnPtrSynType")]
    FnPtr,

    #[display("(UntypedSynType {})", _0)]
    Untyped(Layout),

    #[display("UnitSynType")]
    Unit,

    #[display("UnitSynType")]
    Never,

    #[display("(ArraySynType {} {})", _0, _1)]
    Array(Box<Self>, u128),

    /// A Coq term, in case of generics.
    ///
    /// This Coq term is required to have type `syn_type`.
    #[display("{}", _0)]
    Literal(String),
    // no struct or enums - these are specified through literals.
}

/// Representation of Caesium's optypes.
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum OpType {
    #[display("IntOp {}", _0)]
    Int(IntType),

    #[display("BoolOp")]
    Bool,

    #[display("CharOp")]
    Char,

    #[display("PtrOp")]
    Ptr,

    // a term for the struct_layout, and optypes for the individual fields
    #[display("StructOp unit_sl []")]
    Struct,

    #[display("UntypedOp ({})", _0)]
    Untyped(Layout),

    #[display("(use_op_alg' {})", _0)]
    UseOpAlg(coq::term::Term),
}

/// A representation of Caesium layouts we are interested in.
#[derive(Clone, Eq, PartialEq, Hash, Ord, PartialOrd, Debug, Display)]
pub enum Layout {
    // in the case of 32bits
    #[display("void*")]
    Ptr,

    // layout specified by the int type
    #[display("(it_layout {})", _0)]
    Int(IntType),

    // size 1, similar to u8/i8
    #[display("bool_layout")]
    Bool,

    // size 4, similar to u32
    #[display("char_layout")]
    Char,

    // guaranteed to have size 0 and alignment 1.
    #[display("(layout_of unit_sl)")]
    Unit,

    /// used for variable layout terms, e.g. for struct layouts or generics
    #[display("(use_layout_alg' {})", _0)]
    UseLayoutAlg(coq::term::Term),

    /// padding of a given number of bytes
    #[display("(Layout {}%nat 0%nat)", _0)]
    Pad(u32),

    #[display("(mk_array_layout {} {})", _0, _1)]
    Array(Box<Self>, u128),
}

impl From<SynType> for Layout {
    fn from(x: SynType) -> Self {
        Self::from(&x)
    }
}

impl From<&SynType> for Layout {
    /// Get a Coq term for the layout of this syntactic type.
    /// This may call the Coq-level layout algorithm that we assume.
    fn from(x: &SynType) -> Self {
        match x {
            SynType::Bool => Self::Bool,
            SynType::Char => Self::Char,
            SynType::Int(it) => Self::Int(*it),

            SynType::Ptr | SynType::FnPtr => Self::Ptr,

            SynType::Array(st, len) => Self::Array(Box::new(st.as_ref().to_owned().into()), *len),
            SynType::Untyped(ly) => ly.clone(),
            SynType::Unit | SynType::Never => Self::Unit,

            SynType::Literal(rhs) => Self::UseLayoutAlg(coq::term::Term::Literal(rhs.clone())),
        }
    }
}

impl From<SynType> for OpType {
    fn from(x: SynType) -> Self {
        Self::from(&x)
    }
}

impl From<&SynType> for OpType {
    /// Determine the optype used to access a value of this syntactic type.
    /// Note that we may also always use `UntypedOp`, but this here computes the more specific
    /// `op_type` that triggers more UB on invalid values.
    fn from(x: &SynType) -> Self {
        match x {
            SynType::Bool => Self::Bool,
            SynType::Char => Self::Char,
            SynType::Int(it) => Self::Int(*it),

            SynType::Ptr | SynType::FnPtr => Self::Ptr,

            SynType::Untyped(ly) => Self::Untyped(ly.clone()),
            SynType::Unit => Self::Struct,
            SynType::Never => Self::Untyped(Layout::Unit),

            SynType::Array(_, _) => Self::Untyped(x.to_owned().into()),

            SynType::Literal(rhs) => Self::UseOpAlg(coq::term::Term::Literal(rhs.clone())),
        }
    }
}

/// Memory access ordering (maps to Caesium `order`).
///
/// All Rust atomic orderings (`SeqCst`, `Acquire`, `Release`, `Relaxed`) map to `Sc`
/// (sequentially consistent). This is a sound over-approximation in the
/// interleaving semantics model.
#[derive(Copy, Clone, Eq, PartialEq, Debug, Display)]
pub enum Order {
    /// Sequentially consistent — atomic, single-step access.
    #[display("ScOrd")]
    Sc,
    /// Non-atomic — default two-phase access (`Na1Ord`/`Na2Ord`).
    #[display("Na1Ord")]
    Na,
}

impl Order {
    /// Caesium notation suffix for memory access operations.
    /// `Na1Ord` is the default in Caesium notation and is omitted.
    /// `ScOrd` requires an explicit suffix: `, ScOrd`.
    #[must_use]
    pub const fn suffix(self) -> &'static str {
        match self {
            Self::Sc => ", ScOrd",
            Self::Na => "",
        }
    }
}

/// Atomic read-modify-write operation (maps to Caesium `atomic_rmw_op`).
///
/// All operations follow the same pattern: atomically read old value,
/// compute `new = f(old, arg)`, write new, return old.
#[derive(Copy, Clone, Eq, PartialEq, Debug, Display)]
pub enum AtomicRmwOp {
    /// `f(old, arg) = arg` — atomic exchange
    #[display("RmwXchg")]
    Xchg,
    /// `f(old, arg) = old + arg`
    #[display("RmwAdd")]
    Add,
    /// `f(old, arg) = old - arg`
    #[display("RmwSub")]
    Sub,
    /// `f(old, arg) = old & arg`
    #[display("RmwAnd")]
    And,
    /// `f(old, arg) = old | arg`
    #[display("RmwOr")]
    Or,
    /// `f(old, arg) = old ^ arg`
    #[display("RmwXor")]
    Xor,
    /// `f(old, arg) = !(old & arg)`
    #[display("RmwNand")]
    Nand,
    /// `f(old, arg) = max(old, arg)` — signed
    #[display("RmwMaxS")]
    MaxSigned,
    /// `f(old, arg) = min(old, arg)` — signed
    #[display("RmwMinS")]
    MinSigned,
    /// `f(old, arg) = max(old, arg)` — unsigned
    #[display("RmwMaxU")]
    MaxUnsigned,
    /// `f(old, arg) = min(old, arg)` — unsigned
    #[display("RmwMinU")]
    MinUnsigned,
}
