// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

/// Provides the Coq AST for code and specifications as well as utilities for
/// constructing them.
use std::collections::{BTreeMap, HashSet};
use std::fmt::Write as _;
use std::io::Write as _;
use std::{fmt, io};

use derive_more::{Constructor, Display};
use indent_write::indentable::Indentable as _;
use indent_write::io::IndentWriter;
use indoc::{formatdoc, writedoc};
use log::{info, trace};
use typed_arena::Arena;

use crate::specs::*;
use crate::{BASE_INDENT, coq, fmt_list, lang, make_indent, model};

fn fmt_comment(o: Option<&String>) -> String {
    match o {
        None => String::new(),
        Some(comment) => format!(" (* {} *)", comment),
    }
}

fn fmt_option<T: fmt::Display>(o: Option<&T>) -> String {
    match o {
        None => "None".to_owned(),
        Some(x) => format!("Some ({})", x),
    }
}

fn make_map_string(sep: &str, els: &Vec<(String, String)>) -> String {
    let mut out = String::with_capacity(100);
    for (key, value) in els {
        out.push_str(sep);

        out.push_str(format!("<[\n    \"{key}\" :=\n{value}\n    ]>%E $").as_str());
    }
    out.push_str(sep);
    out.push('∅');
    out
}

fn make_lft_map_string(els: &Vec<(coq::Ident, coq::Ident)>) -> String {
    let mut out = String::with_capacity(100);
    for (key, value) in els {
        out.push_str(format!("named_lft_update \"{}\" {} $ ", key, value).as_str());
    }
    out.push('∅');
    out
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum LitTerm {
    #[display("TypeRt {}", _0)]
    TypeRt(RustType),
    #[display("AppDef [{}] [{}]", fmt_list!(_0, "; "), fmt_list!(_1, "; "))]
    AppDef(Vec<String>, Vec<Self>),
}

impl LitTerm {
    fn from_trait_req_inst(x: &traits::ReqInst<'_>) -> Self {
        match &x.spec {
            traits::ReqInstSpec::Specialized(s) => {
                let mut args = Vec::new();

                for ty in s.impl_inst.get_direct_ty_params_with_assocs() {
                    let t = Self::TypeRt(RustType::of_type(&ty));
                    args.push(t);
                }
                // get the attr terms this depends on
                for req in s.impl_inst.get_direct_trait_requirements() {
                    args.push(Self::from_trait_req_inst(req));
                }

                Self::AppDef(vec![format!("\"{}\"", s.impl_ref.spec_attrs_record())], args)
            },
            traits::ReqInstSpec::Quantified(s) => {
                let s = s.trait_ref.borrow();
                let s = s.as_ref().unwrap();
                Self::AppDef(vec![format!("\"{}\"", s.make_spec_attrs_use())], vec![])
            },
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display, Default)]
#[display("RSTScopeInst [{}] [{}] [{}]", fmt_list!(lfts, "; ", |x| format!("\"{x}\"")), fmt_list!(apps, "; "), fmt_list!(trait_attrs, "; "))]
pub struct RustScopeInst {
    apps: Vec<RustType>,
    lfts: Vec<Lft>,
    trait_attrs: Vec<LitTerm>,
}
impl From<&GenericScopeInst<'_>> for RustScopeInst {
    fn from(scope_inst: &GenericScopeInst<'_>) -> Self {
        let typarams: Vec<_> = scope_inst
            .get_all_ty_params_with_assocs()
            .iter()
            .map(|ty| RustType::of_type(ty))
            .collect();
        let lfts = scope_inst.get_lfts().to_owned();

        let mut trait_attrs = Vec::new();
        for x in scope_inst
            .get_surrounding_trait_requirements()
            .iter()
            .chain(scope_inst.get_direct_trait_requirements().iter())
        {
            trait_attrs.push(LitTerm::from_trait_req_inst(x));
        }

        Self {
            apps: typarams,
            lfts,
            trait_attrs,
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("RSTEnumDef [{}] ({})", fmt_list!(path, "; ", "\"{}\""), inst)]
pub struct RustEnumDef {
    path: Vec<String>,
    inst: RustScopeInst,
}
impl TryFrom<types::LiteralUse<'_>> for RustEnumDef {
    type Error = ();

    fn try_from(other: types::LiteralUse<'_>) -> Result<Self, ()> {
        let scope_inst = &other.scope_inst.ok_or(())?;
        let enum_name = other.def.info.enum_name().ok_or(())?;

        let inst: RustScopeInst = scope_inst.into();
        Ok(Self {
            path: vec![enum_name.clone()],
            inst,
        })
    }
}

/// A representation of syntactic Rust types that we can use in annotations for the `RefinedRust`
/// type system.
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum RustType {
    #[display("RSTLitType [{}] ({})", fmt_list!(_0, "; ", "\"{}\""), _1)]
    Lit(Vec<String>, RustScopeInst),

    #[display("RSTTyVar \"{}\"", _0)]
    TyVar(String),

    #[display("RSTInt {}", _0)]
    Int(lang::IntType),

    #[display("RSTBool")]
    Bool,

    #[display("RSTChar")]
    Char,

    #[display("RSTUnit")]
    Unit,

    #[display("RSTAliasPtr")]
    AliasPtr,

    #[display("RSTRef Mut \"{}\" ({})", _1, &_0)]
    MutRef(Box<Self>, Lft),

    #[display("RSTRef Shr \"{}\" ({})", _1, &_0)]
    ShrRef(Box<Self>, Lft),

    #[display("RSTBox ({})", &_0)]
    PrimBox(Box<Self>),

    #[display("RSTStruct ({}) [{}]", _0, fmt_list!(_1, "; "))]
    Struct(String, Vec<Self>),

    #[display("RSTArray {} ({})", _0, &_1)]
    Array(u128, Box<Self>),
}

impl RustType {
    #[must_use]
    pub fn of_type(ty: &Type<'_>) -> Self {
        info!("Translating rustType: {:?}", ty);
        match ty {
            Type::Int(it) => Self::Int(*it),
            Type::Bool => Self::Bool,
            Type::Char => Self::Char,

            Type::MutRef(ty, lft) => {
                let ty = Self::of_type(ty);
                Self::MutRef(Box::new(ty), lft.clone())
            },

            Type::ShrRef(ty, lft) => {
                let ty = Self::of_type(ty);
                Self::ShrRef(Box::new(ty), lft.clone())
            },

            Type::Struct(as_use) => {
                let is_raw = as_use.is_raw();

                let Some(def) = as_use.def else {
                    return Self::Unit;
                };

                let def = def.borrow();
                let def = def.as_ref().unwrap();

                // translate type parameter instantiations
                let inst: RustScopeInst = (&as_use.scope_inst).into();
                let ty_name = if is_raw { def.plain_ty_name().to_owned() } else { def.public_type_name() };

                Self::Lit(vec![ty_name], inst)
            },

            Type::Enum(ae_use) => {
                let inst: RustScopeInst = (&ae_use.scope_inst).into();

                let def = ae_use.def.borrow();
                let def = def.as_ref().unwrap();
                Self::Lit(vec![def.public_type_name().to_owned()], inst)
            },

            Type::LiteralParam(lit) => Self::TyVar(lit.rust_name.clone()),

            Type::Array(ty, len) => Self::Array(*len, Box::new(Self::of_type(ty.as_ref()))),

            Type::Literal(lit) => {
                if let Some(scope_inst) = lit.scope_inst.as_ref() {
                    let inst: RustScopeInst = scope_inst.into();
                    Self::Lit(vec![lit.def.type_term.clone()], inst)
                } else {
                    Self::Lit(vec![lit.def.type_term.clone()], RustScopeInst::default())
                }
            },

            Type::Uninit(_) => {
                panic!("RustType::of_type: uninit is not a Rust type");
            },

            Type::Unit => Self::Unit,

            Type::Never => {
                panic!("RustType::of_type: cannot translate Never type");
            },

            Type::RawPtr => Self::AliasPtr,
        }
    }
}

/**
 * Caesium literals.
 *
 * This is much more constrained than the Coq version of values, as we do not need to represent
 * runtime values.
 */
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Literal {
    #[display("i2v ({}) {}", _0, lang::IntType::I8)]
    I8(i8),

    #[display("i2v ({}) {}", _0, lang::IntType::I16)]
    I16(i16),

    #[display("i2v ({}) {}", _0, lang::IntType::I32)]
    I32(i32),

    #[display("i2v ({}) {}", _0, lang::IntType::I64)]
    I64(i64),

    #[display("i2v ({}) {}", _0, lang::IntType::I128)]
    I128(i128),

    #[display("i2v ({}) {}", _0, lang::IntType::ISize)]
    ISize(i64),

    #[display("i2v ({}) {}", _0, lang::IntType::U8)]
    U8(u8),

    #[display("i2v ({}) {}", _0, lang::IntType::U16)]
    U16(u16),

    #[display("i2v ({}) {}", _0, lang::IntType::U32)]
    U32(u32),

    #[display("i2v ({}) {}", _0, lang::IntType::U64)]
    U64(u64),

    #[display("i2v ({}) {}", _0, lang::IntType::U128)]
    U128(u128),

    #[display("i2v ({}) {}", _0, lang::IntType::USize)]
    USize(u64),

    #[display("val_of_bool {}", _0)]
    Bool(bool),

    #[display("i2v ({}) CharIt", *_0 as u32)]
    Char(char),

    /// name of the loc
    #[display("{}", _0)]
    Loc(String),

    /// dummy literal for ZST values (e.g. ())
    #[display("zst_val")]
    ZST,
}

/**
 * Caesium expressions
 */
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Expr {
    #[display("\"{}\"", _0)]
    Var(String),

    /// a Coq-level parameter with a given Coq name
    #[display("{}", _0)]
    MetaParam(String),

    #[display("{}", _0)]
    Literal(Literal),

    #[display("UnOp ({}) ({}) ({})", o, ot, &e)]
    UnOp {
        o: Unop,
        ot: lang::OpType,
        e: Box<Self>,
    },

    #[display("({}) {} ({})", &e1, o.caesium_fmt(ot1, ot2), &e2)]
    BinOp {
        o: Binop,
        ot1: lang::OpType,
        ot2: lang::OpType,
        e1: Box<Self>,
        e2: Box<Self>,
    },

    #[display("({}) {} ({})", &e1, o.caesium_checked_fmt(ot1, ot2), &e2)]
    CheckBinOp {
        o: Binop,
        ot1: lang::OpType,
        ot2: lang::OpType,
        e1: Box<Self>,
        e2: Box<Self>,
    },

    /// dereference an lvalue
    #[display("!{{ {}{} }} ( {} )", ot, order.suffix(), &e)]
    Deref {
        ot: lang::OpType,
        order: lang::Order,
        e: Box<Self>,
    },

    /// dereference a box using the compiler magic
    #[display("!box{{ {}, {} }} ( {} )", tst, ast, &e)]
    MagicBoxDeref {
        tst: lang::SynType,
        ast: lang::SynType,
        e: Box<Self>,
    },

    /// lvalue to rvalue conversion (move)
    #[display("move{{ {}{} }} ({})", ot, order.suffix(), &e)]
    Move {
        ot: lang::OpType,
        order: lang::Order,
        e: Box<Self>,
    },

    /// lvalue to rvalue conversion (copy)
    #[display("copy{{ {}{} }} ({})", ot, order.suffix(), &e)]
    Copy {
        ot: lang::OpType,
        order: lang::Order,
        e: Box<Self>,
    },

    /// the borrow-operator to get a reference
    #[display("&ref{{ {}, {}, \"{}\" }} ({})", bk, fmt_option(ty.as_ref()), lft, &e)]
    Borrow {
        lft: Lft,
        bk: BorKind,
        ty: Option<RustType>,
        e: Box<Self>,
    },

    /// the address-of operator to get a raw pointer
    #[display("&raw{{ {} }} ({})", mt, &e)]
    AddressOf { mt: Mutability, e: Box<Self> },

    #[display("CallE {} [{}] [{}] [@{{expr}} {}]", &f, fmt_list!(lfts, "; ", "\"{}\""), fmt_list!(tys, "; ", "{}"), fmt_list!(args, "; "))]
    Call {
        f: Box<Self>,
        lfts: Vec<Lft>,
        tys: Vec<RustType>,
        args: Vec<Self>,
    },

    #[display("IfE ({}) ({}) ({}) ({})", ot, &e1, &e2, &e3)]
    If {
        ot: lang::OpType,
        e1: Box<Self>,
        e2: Box<Self>,
        e3: Box<Self>,
    },

    #[display("({}) at{{ {} }} \"{}\"", &e, sls, name)]
    FieldOf {
        e: Box<Self>,
        sls: String,
        name: String,
    },

    /// an annotated expression
    #[display("AnnotExpr{} {} ({}) ({})", fmt_comment(why.as_ref()), a.needs_laters(), a, &e)]
    Annot {
        a: Annotation,
        why: Option<String>,
        e: Box<Self>,
    },

    #[display("StructInit {} [{}]", sls, fmt_list!(components, "; ", |(name, e)| format!("(\"{name}\", {e} : expr)")))]
    StructInitE {
        sls: coq::term::App<String, String>,
        components: Vec<(String, Self)>,
    },

    #[display("EnumInit {} \"{}\" ({}) ({})", els, variant, ty, &initializer)]
    EnumInitE {
        els: coq::term::App<String, String>,
        variant: String,
        ty: RustEnumDef,
        initializer: Box<Self>,
    },

    #[display("AnnotExpr 0 DropAnnot ({})", &_0)]
    DropE(Box<Self>),

    /// a box expression for creating a box of a particular type
    #[display("box{{{}}}", &_0)]
    BoxE(lang::SynType),

    /// access the discriminant of an enum
    #[display("EnumDiscriminant ({}) ({})", els, &e)]
    EnumDiscriminant { els: String, e: Box<Self> },

    /// access to the data of an enum
    #[display("EnumData ({}) \"{}\" ({})", els, variant, &e)]
    EnumData {
        els: String,
        variant: String,
        e: Box<Self>,
    },

    /// compare-and-swap (always atomic, single step)
    #[display("CAS ({}) ({}) ({}) ({})", ot, &target, &expected, &desired)]
    Cas {
        ot: lang::OpType,
        target: Box<Self>,
        expected: Box<Self>,
        desired: Box<Self>,
    },

    /// atomic read-modify-write (single step)
    #[display("AtomicRMW {} ({}) ({}) ({})", op, ot, &target, &arg)]
    AtomicRmw {
        op: lang::AtomicRmwOp,
        ot: lang::OpType,
        target: Box<Self>,
        arg: Box<Self>,
    },
}

impl Expr {
    #[must_use]
    pub fn with_optional_annotation(e: Self, a: Option<Annotation>, why: Option<String>) -> Self {
        match a {
            Some(a) => Self::Annot {
                a,
                e: Box::new(e),
                why,
            },
            None => e,
        }
    }
}

/// for unique/shared pointers
#[derive(Copy, Clone, Eq, PartialEq, Debug, Display)]
pub enum Mutability {
    #[display("Mut")]
    Mut,

    #[display("Shr")]
    Shared,
}

/**
 * Borrows allowed in Caesium
 */
#[derive(Copy, Clone, Eq, PartialEq, Debug, Display)]
pub enum BorKind {
    #[display("Mut")]
    Mutable,

    #[display("Shr")]
    Shared,
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Annotation {
    /// Start a lifetime as a sublifetime of the intersection of a few other lifetimes
    #[display("StartLftAnnot \"{}\" [{}]", _0, fmt_list!(_1, "; ", "\"{}\""))]
    StartLft(Lft, Vec<Lft>),

    /// End this lifetime
    #[display("EndLftAnnot \"{}\"", _0)]
    EndLft(Lft),

    /// Extend this lifetime by making the directly owned part static
    #[display("ExtendLftAnnot \"{}\"", _0)]
    ExtendLft(Lft),

    /// Dynamically include a lifetime in another lifetime
    #[display("DynIncludeLftAnnot \"{}\" \"{}\"", _0, _1)]
    DynIncludeLft(Lft, Lft),

    /// Copy a lft name map entry from lft1 to lft2
    #[display("CopyLftNameAnnot \"{}\" \"{}\"", _1, _0)]
    CopyLftName(Lft, Lft),

    /// Creation an annotation for introducing an unconstrained lifetime
    #[display("UnconstrainedLftAnnot \"{}\"", _0)]
    UnconstrainedLft(Lft),

    /// Create an alias for an intersection of lifetimes
    #[display("AliasLftAnnot \"{}\" [{}]", _0, fmt_list!(_1, "; ", "\"{}\""))]
    AliasLftIntersection(Lft, Vec<Lft>),

    /// Stratify the context
    #[display("StratifyContextAnnot")]
    StratifyContext,
}

impl Annotation {
    const fn needs_laters(&self) -> u32 {
        if matches!(self, Self::EndLft(_)) { 2 } else { 1 }
    }
}

type BlockLabel = usize;

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum PrimStmt {
    #[display("{} <-{{ {}{} }} {};\n", e1, ot, order.suffix(), e2)]
    Assign {
        ot: lang::OpType,
        order: lang::Order,
        e1: Box<Expr>,
        e2: Box<Expr>,
    },

    #[display("expr: {};\n", _0)]
    ExprS(Box<Expr>),

    #[display("assert{{ {} }}: {};\n", lang::OpType::Bool, _0)]
    AssertS(Box<Expr>),

    #[display("local_live{{ {} }} \"{}\";\n", _0.1, _0.0)]
    LocalLive(Variable),

    #[display("local_dead \"{}\";\n", _0)]
    LocalDead(String),

    #[display("{}", fmt_list!(a, "", |x| { format!("annot{{ {} }}: {x};{}\n", x.needs_laters(), fmt_comment(why.as_ref()))}))]
    Annot {
        a: Vec<Annotation>,
        why: Option<String>,
    },

    #[display("(* {} *)\n", _0)]
    Comment(String),
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Stmt {
    #[display("Goto \"_bb{}\"", _0)]
    GotoBlock(BlockLabel),

    #[display("return ({})", _0)]
    Return(Expr),

    #[display(
        "if{{ {} }}: {} then\n{}\nelse\n{}",
        ot,
        e,
        &s1.indented(&make_indent(1)),
        &s2.indented(&make_indent(1))
    )]
    If {
        ot: lang::OpType,
        e: Expr,
        s1: Box<Self>,
        s2: Box<Self>,
    },

    #[display(
        "Switch ({}: int_type) ({}) ({}∅) ([{}]) ({})",
        it,
        e,
        fmt_list!(index_map, "", |(k, v)| format!("<[ {k}%Z := {v}%nat ]> $ ")),
        fmt_list!(bs, "; "),
        &def
    )]
    Switch {
        // e needs to evaluate to an integer/variant index used as index to bs
        e: Expr,
        it: lang::IntType,
        index_map: BTreeMap<u128, usize>,
        bs: Vec<Self>,
        def: Box<Self>,
    },

    #[display("{}{}", fmt_list!(_0, ""), *_1)]
    Prim(Vec<PrimStmt>, Box<Self>),

    #[display("StuckS")]
    Stuck,
}

#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Unop {
    #[display("NegOp")]
    Neg,

    #[display("NotBoolOp")]
    NotBool,

    #[display("NotIntOp")]
    NotInt,

    #[display("CastOp ({})", _0)]
    Cast(lang::OpType),
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Binop {
    //arithmetic
    Add,
    Sub,
    Mul,
    Div,
    Mod,

    // logical
    And,
    Or,

    //bitwise
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,

    // unchecked variants
    AddUnchecked,
    SubUnchecked,
    MulUnchecked,
    ShlUnchecked,
    ShrUnchecked,

    // comparison
    Eq,
    Ne,
    Lt,
    Gt,
    Le,
    Ge,

    // pointer operations
    PtrOffset(lang::Layout),
    PtrNegOffset(lang::Layout),
    PtrDiff(lang::Layout),
}

impl Binop {
    fn caesium_fmt(&self, ot1: &lang::OpType, ot2: &lang::OpType) -> String {
        let format_prim = |st: &str| format!("{} {} , {} }}", st, ot1, ot2);
        let format_bool = |st: &str| format!("{} {} , {} , {} }}", st, ot1, ot2, lang::BOOL_REPR);

        match self {
            Self::Add => format_prim("+{"),
            Self::Sub => format_prim("-{"),
            Self::Mul => format_prim("×{"),
            Self::Div => format_prim("/{"),
            Self::Mod => format_prim("%{"),
            Self::And => format_bool("&&{"),
            Self::Or => format_bool("||{"),
            Self::BitAnd => format_prim("&b{"),
            Self::BitOr => format_prim("|{"),
            Self::BitXor => format_prim("^{"),
            Self::Shl => format_prim("<<{"),
            Self::Shr => format_prim(">>{"),

            Self::AddUnchecked => format_prim("+unchecked{"),
            Self::SubUnchecked => format_prim("-unchecked{"),
            Self::MulUnchecked => format_prim("×unchecked{"),
            Self::ShlUnchecked => format_prim("<<unchecked{"),
            Self::ShrUnchecked => format_prim(">>unchecked{"),

            Self::Eq => format_bool("= {"),
            Self::Ne => format_bool("!= {"),
            Self::Lt => format_bool("<{"),
            Self::Gt => format_bool(">{"),
            Self::Le => format_bool("≤{"),
            Self::Ge => format_bool("≥{"),
            Self::PtrOffset(ly) => format!("at_offset{{ {} , {} , {} }}", ly, ot1, ot2),
            Self::PtrNegOffset(ly) => format!("at_neg_offset{{ {} , {} , {} }}", ly, ot1, ot2),
            Self::PtrDiff(ly) => format!("sub_ptr{{ {} , {} , {} }}", ly, ot1, ot2),
        }
    }

    fn caesium_checked_fmt(&self, ot1: &lang::OpType, ot2: &lang::OpType) -> String {
        let format_prim = |st: &str| format!("{} {} , {} }}", st, ot1, ot2);

        match self {
            Self::Add => format_prim("+c{"),
            Self::Sub => format_prim("-c{"),
            Self::Mul => format_prim("×c{"),
            Self::Div => format_prim("/c{"),
            Self::Mod => format_prim("%c{"),
            Self::Shl => format_prim("<<c{"),
            Self::Shr => format_prim(">>c{"),
            _ => unimplemented!(),
        }
    }
}

/**
 * A variable in the Caesium code, composed of a name and a type.
 */
#[derive(Clone, Eq, PartialEq, Debug, Constructor)]
pub struct Variable(String, lang::SynType);

/**
 * Maintain necessary info to map MIR places to Caesium stack variables.
 */
struct StackMap {
    args: Vec<Variable>,
    used_names: HashSet<String>,
}

impl StackMap {
    #[must_use]
    fn new() -> Self {
        Self {
            args: Vec::new(),
            used_names: HashSet::new(),
        }
    }

    fn insert_arg(&mut self, name: String, st: lang::SynType) -> bool {
        if self.used_names.contains(&name) {
            return false;
        }
        self.used_names.insert(name.clone());
        self.args.push(Variable::new(name, st));
        true
    }
}

/// Representation of a Caesium function's source code
#[expect(clippy::module_name_repetitions)]
pub struct FunctionCode {
    name: String,
    code_name: String,

    def: FunctionCodeDef,

    /// Coq parameters that the function is parameterized over
    required_parameters: coq::binder::BinderList,
}

impl FunctionCode {
    fn new(
        code_name: &str,
        function_name: &str,
        def: FunctionCodeDef,
        typarams: &TyParamList,
        used_functions: &[UsedProcedure<'_>],
        used_statics: &[StaticMeta<'_>],
    ) -> Self {
        // generate location parameters for other functions used by this one, as well as syntypes
        // These are parameters that the code gets
        let mut parameters: Vec<coq::binder::Binder> = used_functions
            .iter()
            .map(|f_inst| coq::binder::Binder::new(Some(f_inst.loc_name.clone()), model::Type::Loc))
            .collect();

        // generate location parameters for statics used by this function
        for s in used_statics {
            parameters.push(coq::binder::Binder::new(Some(s.loc_name.clone()), model::Type::Loc));
        }

        // add generic syntype parameters for generics that this function uses.
        let mut gen_st_parameters = typarams.get_coq_ty_st_params();
        parameters.append(&mut gen_st_parameters.0);

        Self {
            code_name: code_name.to_owned(),
            name: function_name.to_owned(),
            def,
            required_parameters: coq::binder::BinderList::new(parameters),
        }
    }

    fn get_args(&self) -> &[Variable] {
        &self.def.stack_layout.args
    }
}

impl fmt::Display for FunctionCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut doc = coq::Document::default();

        let def = coq::command::Definition {
            name: self.code_name.clone(),
            params: self.required_parameters.clone(),
            ty: Some(coq::term::RocqType::UserDefined(model::Type::Function)),
            body: coq::command::DefinitionBody::Term(coq::term::RocqTerm::Literal(self.def.to_string())),
            program_mode: true,
        };
        doc.push(def);

        let proof = coq::ltac::LTac::UserDefined(model::LTac::SolveFnVarNoDup);
        let obligation_proof = coq::command::ObligationProof {
            content: coq::ProofDocument::new(vec![coq::Vernac::LTac(proof.into())]),
            terminator: coq::proof::Terminator::Qed,
        };
        doc.push(coq::command::Command::NextObligation(obligation_proof));

        write!(f, "{doc}\n")
    }
}

pub struct FunctionCodeDef {
    stack_layout: StackMap,
    basic_blocks: BTreeMap<usize, Stmt>,
}

impl FunctionCodeDef {
    #[must_use]
    fn new() -> Self {
        Self {
            stack_layout: StackMap::new(),
            basic_blocks: BTreeMap::new(),
        }
    }

    pub fn add_argument(&mut self, name: &str, st: lang::SynType) {
        self.stack_layout.insert_arg(name.to_owned(), st);
    }

    pub fn add_basic_block(&mut self, index: usize, bb: Stmt) {
        self.basic_blocks.insert(index, bb);
    }
}

impl fmt::Display for FunctionCodeDef {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fn fmt_variable(Variable(name, ty): &Variable) -> String {
            format!("(\"{}\", {} : layout)", name, lang::Layout::from(ty))
        }

        fn fmt_blocks((name, bb): (&usize, &Stmt)) -> String {
            formatdoc!(
                r#"<[
                   "_bb{}" :=
                    {}
                   ]>%E $"#,
                name,
                bb.indented_skip_initial(&make_indent(1))
            )
        }

        let args = fmt_list!(&self.stack_layout.args, ";\n", fmt_variable);
        let blocks = fmt_list!(&self.basic_blocks, "\n", fmt_blocks);

        writedoc!(
            f,
            r#"{{|
                f_args := [
                 {}
                ];
                f_code :=
                 {}
                 ∅;
                f_init := "_bb0";
               |}}"#,
            args.indented_skip_initial(&make_indent(1)),
            blocks.indented_skip_initial(&make_indent(1))
        )?;
        Ok(())
    }
}

/// Classifies the kind of a local variable similar to `mir::LocalKind`,
/// but distinguishes user-specified locals from compiler-generated temporaries.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum LocalKind {
    Arg,
    Local,
    CompilerTemp,
}

impl LocalKind {
    #[must_use]
    pub fn mk_local_name(self, name: &str) -> String {
        match self {
            Self::Arg => {
                format!("arg_{name}")
            },
            Self::CompilerTemp | Self::Local => {
                format!("local_{name}")
            },
        }
    }
}

#[derive(Clone, Debug, Display)]
#[display("({}PolyNil)", fmt_list!(_0, "",
    |(bb, spec)| format!("PolyCons (\"_bb{}\", {}) $ ", bb, spec))
)]
struct InvariantMap(BTreeMap<usize, LoopSpec>);

/// A Caesium function bundles up the Caesium code itself as well as the generated specification
/// for it.
#[expect(clippy::partial_pub_fields)]
pub struct Function<'def> {
    pub code: FunctionCode,
    pub spec: &'def functions::Spec<'def, functions::InnerSpec<'def>>,

    /// Other functions that are used by this one.
    other_functions: Vec<UsedProcedure<'def>>,
    /// Syntypes that we assume to be layoutable in the typing proof
    layoutable_syntys: Vec<lang::SynType>,
    /// Custom tactics for the generated proof
    manual_tactics: Vec<String>,
    /// used statics
    used_statics: Vec<StaticMeta<'def>>,
    /// unconstrained lfts used by the function
    unconstrained_lfts: Vec<Lft>,

    /// invariants for loop head bbs
    loop_invariants: InvariantMap,

    /// Extra linktime assumptions
    extra_link_assum: Vec<String>,
}

impl Function<'_> {
    /// Get the name of the function.
    #[must_use]
    pub fn name(&self) -> &str {
        &self.code.name
    }

    pub fn generate_lemma_statement<F>(&self, f: &mut F, is_default_trait_impl: bool) -> Result<(), io::Error>
    where
        F: io::Write,
    {
        // indent
        let mut writer = IndentWriter::new_skip_initial(BASE_INDENT, &mut *f);
        let f = &mut writer;

        writeln!(f, "Definition {}_lemma (π : thread_id) : Prop :=", self.name())?;

        let include_self_req =
            if is_default_trait_impl { IncludeSelfReq::AttrsSpec } else { IncludeSelfReq::Attrs };

        // write coq parameters
        let mut params = self.spec.get_all_lemma_coq_params(include_self_req);
        // don't want implicit generalizing binders here
        params.make_implicit(coq::binder::Kind::Explicit);

        let has_params =
            !params.0.is_empty() || !self.other_functions.is_empty() || !self.used_statics.is_empty();
        if has_params {
            write!(f, "∀ ")?;
            for param in &params.0 {
                write!(f, "{} ", param)?;
            }

            // assume locations for other functions
            for proc_use in &self.other_functions {
                write!(f, "({} : loc) ", proc_use.loc_name)?;
            }

            // assume locations for statics
            for s in &self.used_statics {
                write!(f, "({} : loc) ", s.loc_name)?;
            }
            writeln!(f, ", ")?;
        }

        // assume link-time Coq assumptions
        // layoutable
        for st in &self.layoutable_syntys {
            write!(f, "syn_type_is_layoutable ({}) →\n", st)?;
        }
        // statics are registered
        for s in &self.used_statics {
            write!(f, "static_is_registered \"{}\" {} (existT _ {}) →\n", s.ident, s.loc_name, s.ty)?;
        }

        // write extra link-time assumptions
        if !self.extra_link_assum.is_empty() {
            write!(f, "(* extra link-time assumptions *)\n")?;
            for s in &self.extra_link_assum {
                write!(f, "{s} →\n")?;
            }
        }

        // write iris assums
        if self.other_functions.is_empty() && self.used_statics.is_empty() {
            write!(f, "⊢ ")?;
        } else {
            for s in &self.used_statics {
                write!(f, "initialized π \"{}\" -∗\n", s.ident)?;
            }

            for proc_use in &self.other_functions {
                info!("Using other function: {:?} with insts: {:?}", proc_use.spec_term, proc_use.scope_inst);

                let arg_syntys: Vec<String> =
                    proc_use.syntype_of_all_args.iter().map(ToString::to_string).collect();

                write!(
                    f,
                    "{} ◁ᵥ{{π, MetaNone}} {} @ function_ptr [{}] {} -∗\n",
                    proc_use.loc_name,
                    proc_use.loc_name,
                    arg_syntys.join("; "),
                    proc_use,
                )?;
            }
        }

        write!(f, "typed_function π ")?;
        write!(f, "({} ", self.code.code_name)?;

        // add arguments for the code definition
        let mut code_params: Vec<_> =
            self.other_functions.iter().map(|proc_use| proc_use.loc_name.clone()).collect();
        for s in &self.used_statics {
            code_params.push(s.loc_name.clone());
        }

        let ty_params = self.spec.generics.get_all_ty_params_with_assocs();
        for names in ty_params.get_coq_ty_st_params().make_using_terms() {
            code_params.push(format!("{names}"));
        }
        for x in &code_params {
            write!(f, "{}  ", x)?;
        }

        write!(f, ") (<tag_type> ")?;

        // write the specification term
        let mut scope_str = String::new();
        self.spec.generics.format(&mut scope_str, false, &[]).unwrap();

        write!(f, "{scope_str} fn_spec_add_late_pre ({} ", self.spec.get_spec_name())?;

        // write type args (passed to the type definition)
        let spec_params = self.spec.get_all_spec_coq_params();
        for param in &spec_params.0 {
            if !param.is_implicit() {
                write!(f, "{} ", param.get_name())?;
            }
        }

        // instantiate semantic args
        write!(f, "{}", self.spec.generics.identity_instantiation_term())?;

        // I know which generics i'm quantifying over here. I should add the validity requirements
        // for all of them.

        let trait_late_pre = {
            let trait_req_incl_name = &self.spec.trait_req_incl_name;
            let args = self.spec.get_all_trait_req_coq_params().make_using_terms();
            let term = coq::term::App::new(trait_req_incl_name.to_owned(), args);

            let mut term = term.to_string();
            // instantiate semantic args
            write!(term, "{}", self.spec.generics.identity_instantiation_term()).unwrap();

            term
        };
        let params_late_pre = self.spec.generics.generate_validity_term_for_generics();

        let prop = coq::iris::IProp::Sep(vec![
            params_late_pre,
            coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(trait_late_pre))),
        ]);
        // TODO: don't require that _all_ of them are sized
        //let prop = coq::iris::IProp::Exists(self.spec.generics.generate_sized_requirements(),
        // Box::new(prop));

        write!(f, ") (λ π, {prop})")?;

        write!(f, ").\n")
    }

    pub fn generate_proof_prelude<F>(&self, f: &mut F, is_default_trait_impl: bool) -> Result<(), io::Error>
    where
        F: io::Write,
    {
        // indent
        let mut writer = IndentWriter::new_skip_initial(BASE_INDENT, &mut *f);
        let f = &mut writer;

        let include_self_req =
            if is_default_trait_impl { IncludeSelfReq::AttrsSpec } else { IncludeSelfReq::Attrs };

        write!(f, "Ltac {}_prelude :=\n", self.name())?;

        write!(f, "unfold {}_lemma;\n", self.name())?;
        write!(f, "set (FN_NAME := FUNCTION_NAME \"{}\");\n", self.name())?;

        // intros spec params
        let params = self.spec.get_all_lemma_coq_params(include_self_req);
        if !params.0.is_empty() {
            write!(f, "intros")?;
            for param in &params.0 {
                if param.is_implicit() {
                    write!(f, " ?")?;
                } else {
                    write!(f, " {}", param.get_name())?;
                }
            }
            writeln!(f, ";")?;
        }

        write!(f, "intros;\n")?;
        write!(f, "iStartProof;\n")?;

        // intro pattern for the function lifetime
        write!(f, "let ϝ := fresh \"ϝ\" in\n")?;

        // generate intro pattern for lifetimes
        let mut lft_pattern = String::with_capacity(100);
        // pattern is right-associative
        for lft in self.spec.generics.get_lfts() {
            write!(lft_pattern, "[{} ", lft).unwrap();
            write!(f, "let {} := fresh \"{}\" in\n", lft, lft)?;
        }
        write!(lft_pattern, "[]").unwrap();
        for _ in 0..self.spec.generics.get_num_lifetimes() {
            write!(lft_pattern, " ]").unwrap();
        }

        // generate intro pattern for typarams
        let mut typaram_pattern = String::with_capacity(100);
        let all_ty_params = self.spec.generics.get_all_ty_params_with_assocs();
        // pattern is right-associative
        for param in &all_ty_params.params {
            write!(typaram_pattern, "[{} ", param.type_term()).unwrap();
            write!(f, "let {} := fresh \"{}\" in\n", param.type_term(), param.type_term())?;
        }
        write!(typaram_pattern, "[]").unwrap();
        for _ in 0..(all_ty_params.params.len()) {
            write!(typaram_pattern, " ]").unwrap();
        }

        // Prepare the intro pattern for specification-level parameters
        let mut ip_params = String::with_capacity(100);

        let params = self.spec.spec.get_params();

        if let Some(params) = params {
            if params.is_empty() {
                // no params, but still need to provide something to catch the unit
                // (and no empty intropatterns are allowed)
                ip_params.push('?');
            } else {
                for param in params {
                    write!(f, "let {} := fresh \"{}\" in\n", param.get_name(), param.get_name())?;
                }

                // product is left-associative
                for _ in 0..(params.len() - 1) {
                    ip_params.push_str("[ ");
                }

                let mut p_count = 0;
                for param in params {
                    if p_count > 1 {
                        ip_params.push_str(" ]");
                    }
                    ip_params.push(' ');
                    p_count += 1;
                    ip_params.push_str(&param.get_name());
                }

                if p_count > 1 {
                    ip_params.push_str(" ]");
                }
            }
        } else {
            ip_params.push('?');
        }

        write!(
            f,
            "start_function \"{}\" ϝ ( {} ) ( {} ) ( {} ) ( ",
            self.name(),
            lft_pattern.as_str(),
            typaram_pattern.as_str(),
            ip_params.as_str()
        )?;
        if let Some(params) = params {
            for param in params {
                write!(f, " {}", param.get_name())?;
            }
        }
        write!(f, " );\n")?;

        // intro stack locations
        write!(f, "intros")?;

        for Variable(arg, _) in self.code.get_args() {
            write!(f, " {}", LocalKind::Arg.mk_local_name(arg))?;
        }
        write!(f, ";\n")?;

        write!(f, "let π := get_π in\n")?;
        write!(f, "let Σ := get_Σ in\n")?;

        write!(f, "specialize (pose_bb_inv {}) as loop_map;\n", self.loop_invariants)?;

        // initialize lifetimes
        let mut lfts: Vec<_> = self
            .spec
            .generics
            .get_lfts()
            .iter()
            .map(|n| (n.lft().to_owned(), n.lft().to_owned()))
            .collect();
        lfts.push((coq::Ident::new("_flft"), coq::Ident::new("ϝ")));
        lfts.push((coq::Ident::new("static"), coq::Ident::new("static")));
        let formatted_lifetimes = make_lft_map_string(&lfts);
        write!(f, "init_lfts ({} );\n", formatted_lifetimes.as_str())?;

        // initialize tyvars
        let formatted_tyvars = make_map_string(
            " ",
            &all_ty_params
                .params
                .iter()
                .map(|names| (names.rust_name.clone(), format!("existT _ ({})", names.type_term())))
                .collect(),
        );

        write!(f, "init_tyvars ({} );\n", formatted_tyvars.as_str())?;
        for lft in &self.unconstrained_lfts {
            write!(f, "check_unconstrained_lft \"{lft}\";\n")?;
        }
        write!(f, "unfold_generic_inst; simpl.\n")
    }

    pub fn generate_proof<F>(&self, f: &mut F, admit_proofs: bool) -> Result<(), io::Error>
    where
        F: io::Write,
    {
        writeln!(f, "Lemma {}_proof (π : thread_id) :", self.name())?;

        {
            // indent
            let mut writer = IndentWriter::new(BASE_INDENT, &mut *f);
            let f = &mut writer;

            write!(f, "{}_lemma π.", self.name())?;
        }
        write!(f, "\n")?;
        write!(f, "Proof.\n")?;

        {
            let mut writer = IndentWriter::new(BASE_INDENT, &mut *f);
            let f = &mut writer;

            write!(f, "{}_prelude.\n\n", self.name())?;

            write!(f, "rep <-! liRStep; liShow.\n\n")?;
            write!(f, "all: print_remaining_goal.\n")?;
            write!(f, "Unshelve. all: sidecond_solver.\n")?;
            write!(f, "Unshelve. all: sidecond_hammer.\n")?;

            // add custom tactics specified in annotations
            for tac in &self.manual_tactics {
                if tac.starts_with("all:") {
                    write!(f, "{}\n", tac)?;
                } else {
                    write!(f, "{{ {} all: shelve. }}\n", tac)?;
                }
            }

            write!(f, "Unshelve. all: print_remaining_sidecond.\n")?;
        }

        if admit_proofs {
            write!(f, "Admitted. (* admitted due to admit_proofs config flag *)\n")?;
        } else {
            write!(f, "Qed.\n")?;
        }
        Ok(())
    }
}

/// Information on a used static variable
#[derive(Clone, Debug)]
pub struct StaticMeta<'def> {
    pub ident: String,
    pub loc_name: String,
    pub ty: Type<'def>,
}

/// The specification of the procedure we call.
#[derive(Clone, Debug)]
pub enum UsedProcedureSpec<'def> {
    /// A direct specification term.
    Literal(String, String),
    /// A method of a trait impl we quantify over.
    TraitMethod(traits::QuantifiedImpl<'def>, String),
}

impl UsedProcedureSpec<'_> {
    const fn needs_surrounding_trait_reqs(&self) -> bool {
        match *self {
            Self::Literal(_, _) => true,
            // symbolic trait method uses don't need the surrounding trait requirements
            Self::TraitMethod(_, _) => false,
        }
    }
}

impl fmt::Display for UsedProcedureSpec<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Literal(lit, _) => {
                write!(f, "{lit} (RRGS:=RRGS)")
            },
            Self::TraitMethod(spec_use, method_name) => {
                let spec = spec_use.trait_ref.borrow();
                let spec = spec.as_ref().unwrap();

                write!(
                    f,
                    "({} (RRGS:=RRGS) ({}))",
                    spec.trait_ref.make_spec_method_name(method_name),
                    spec_use.get_spec_term(),
                )
            },
        }
    }
}

/// Information about another procedure this function uses
#[derive(Constructor, Clone, Debug)]
#[expect(clippy::partial_pub_fields)]
pub struct UsedProcedure<'def> {
    /// The name to use for the location parameter
    pub loc_name: String,
    /// The term for the specification definition
    spec_term: UsedProcedureSpec<'def>,

    /// Type parameters to quantify over
    /// This includes:
    /// - types this function spec needs to be generic over (in particular type variables of the calling
    ///   function)
    /// - additional lifetimes that the generic instantiation introduces, as well as all lifetime parameters
    ///   of this function
    quantified_scope: GenericScope<'def, traits::LiteralSpecUseRef<'def>>,

    /// specialized specs for the trait assumptions of this procedure
    scope_inst: GenericScopeInst<'def>,

    /// The syntactic types of all arguments
    syntype_of_all_args: Vec<lang::SynType>,
}

impl UsedProcedure<'_> {
    fn get_trait_req_incl_term(&self) -> Result<String, fmt::Error> {
        let mut term = String::new();
        match &self.spec_term {
            UsedProcedureSpec::Literal(_, trait_req_incl_name) => {
                let all_tys = self.scope_inst.get_all_ty_params_with_assocs();
                write!(term, "{trait_req_incl_name} ")?;

                // instantiate with rts and sts etc.
                let mut gen_rfn_type_inst = Vec::new();
                for p in &all_tys {
                    gen_rfn_type_inst.push(format!("({})", p.get_rfn_type()));
                }
                // instantiate syntypes
                for p in &all_tys {
                    let st = lang::SynType::from(p);
                    gen_rfn_type_inst.push(format!("({})", st));
                }
                write!(term, "{} ", gen_rfn_type_inst.join(" "))?;

                for x in self
                    .scope_inst
                    .get_surrounding_trait_requirements()
                    .iter()
                    .chain(self.scope_inst.get_direct_trait_requirements())
                {
                    write!(term, "{} ", x.get_attr_term())?;
                    write!(term, "{} ", x.get_spec_term())?;
                }

                // instantiate semantics args
                write!(term, "{}", self.scope_inst.instantiation(true, true))?;
            },

            UsedProcedureSpec::TraitMethod(_trait_spec, _method_name) => {
                /*
                let trait_ref = trait_spec.trait_ref.borrow();
                let trait_ref = trait_ref.as_ref().unwrap();

                let incl_name = &trait_ref.trait_ref.method_trait_incl_decls[method_name];

                let direct_tys = self.scope_inst.get_direct_ty_params_with_assocs();
                let trait_tys = trait_ref.get_ordered_params_inst();
                let trait_inst = &trait_ref.trait_inst;

                // how do I instantiate the requirements of the trait?
                // - I guess I need an inst of that function's scope: scope_inst

                write!(term, "{incl_name} ")?;

                // TODO first instantiate with the trait's args.
                // then with the functions' args.
                // use trait_tys.

                let mut gen_rfn_type_inst = Vec::new();
                for p in trait_tys.iter().chain(direct_tys.iter()) {
                    gen_rfn_type_inst.push(format!("({})", p.get_rfn_type()));
                }
                // instantiate syntypes
                for p in trait_tys.iter().chain(direct_tys.iter()) {
                    let st = lang::SynType::from(p);
                    gen_rfn_type_inst.push(format!("({})", st));
                }
                write!(term, "{} ", gen_rfn_type_inst.join(" "))?;

                for x in trait_inst
                    .get_direct_trait_requirements()
                    .iter()
                    .chain(self.scope_inst.get_direct_trait_requirements())
                {
                    write!(term, "{} ", x.get_attr_term())?;
                    write!(term, "{} ", x.get_spec_term())?;
                }

                // instantiate lifetimes
                for lft in trait_inst.get_lfts().iter().chain(self.scope_inst.get_lfts().iter()) {
                    write!(term, " <LFT> {lft}")?;
                }

                // instantiate type variables
                for ty in trait_tys.iter().chain(direct_tys.iter()) {
                    write!(term, " <TY> {ty}")?;
                }

                write!(term, " <INST!>")?;
                */

                write!(term, "True")?;
            },
        }
        Ok(term)
    }
}

impl fmt::Display for UsedProcedure<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // quantify
        write!(f, "(<tag_type> {} ", self.quantified_scope)?;

        let spec_needs_surrounding_trait_reqs = self.spec_term.needs_surrounding_trait_reqs();

        // instantiate refinement types
        let mut gen_rfn_type_inst = Vec::new();
        let all_tys = if spec_needs_surrounding_trait_reqs {
            self.scope_inst.get_all_ty_params_with_assocs()
        } else {
            self.scope_inst.get_direct_ty_params_with_assocs()
        };

        for p in &all_tys {
            let rfn = p.get_rfn_type();
            gen_rfn_type_inst.push(format!("({})", rfn));
        }
        // instantiate syntypes
        for p in &all_tys {
            let st = lang::SynType::from(p);
            gen_rfn_type_inst.push(format!("({})", st));
        }

        trace!(
            "using procedure {} with rfn_inst={gen_rfn_type_inst:?} and scope_inst={:?}",
            self.loc_name, self.scope_inst
        );

        write!(f, "fn_spec_add_late_pre ({} {} ", self.spec_term, gen_rfn_type_inst.join(" "))?;

        // TODO: add the trait incls this can assume.
        // well, but I don't even know which trait spec this assumes....
        // (problem: closure stuff where I need a specific pre and post!!)
        // How does this work then?
        // think more about that... Maybe I need to keep track of that in the frontend?
        // I guess in the end it's a linking thing, so yeah, it makes sense that this isn't in the
        // spec term. Also what we assume in general about other functions is a thing the frontend
        // needs to take care of.
        // I think this really means we should have automatic adequacy instantiation.
        //
        // Why do I not just put the specialized spec here directly? Then the adequacy proof
        // becomes more difficult, because I need to subsume - that will make automation hard.
        //
        // I guess for every function, I should have the list of specs it assumes.
        //
        // Having that error put up at link time only also seems annoying.
        //  If I assume something about a closure, then call that function, and I can't satisfy
        //  that requirement about the closure, I want to be told at that point, not when I'm
        //  eventually linking the whole program.
        // => I should verify a function always against the specs its verification assumes, in order
        //    to get reasonable errors. The verification I do should always ensure that linking
        //    succeeds.
        //
        // We currently do this for functions. But for trait requirements that functions have, we
        // need to do the same.
        //
        // Why is this the case?
        // Well, I link against some specification of a trait function (I'll later instantiate this with the
        // canonical specification, I guess) I might assume/need a different specification.
        // So in the verification of a function, I assume that the canonical specification (that is
        // actually verified for that function) implies the specification I need.
        // Now, where do I dispatch that requirement?
        //   - when I link against a function with trait requirements, I need to make sure that I instantiate
        //     it with the right trait spec that I've actually proved. And then I need to add the obligation
        //     that this satisfies the trait spec that the proof for that function assumes.
        //   - what happens when I call a function of a trait that I'm generic about? I don't actually know
        //     what the proof of the impl I link against eventually assumes. Maybe impls need to always be
        //     generic about their trait assumptions. Otherwise, I cannot ensure that everything always links
        //     well? Yeah, that makes sense => Otherwise, it might not imply the default spec for the trait.
        //     Maybe the default spec for a trait should encode that. i.e. some part of our encoding should
        //     semantically make sure of that, I think. TODO; which part enforces that?
        //
        //       I guess before we did that. But then we have the cylicity issues.
        //       There seems to be a tradeoff here. We need to move these safeguards more to the
        //       linking theorem in order to allow all this cyclicity.
        //
        //    For every function I use, I need to determine its trait requirements (I'm already doing that).
        //    For each of these requirements, i need to know what specification it assumes for that.
        //    I can export the spec term of that
        //    However, then I need to agree on a common set of generics this depends on. It cannot
        //    be "generics of the trait", that is too general and will rule out some specializations.
        //    I could do "generics of the function".
        //    Then I need to introduce a definition with the inclusions.
        //
        //    How does this help to break the cycle then? What is the difference to inlining it in
        //    the specification?
        //    - I guess in default specs this isn't included.
        //
        //
        //    Problematic case: impls of two traits having a requirement for the other trait.
        //    Then the impl's spec would be parametric in the spec of the other traits.
        //    If I actually want to call a function and use these impls to dispatch the
        //    requirements, I will run around a cycle.
        //    Now: I guess the impl spec isn't parametric in the spec of the other trait anymore.
        //      I shift the cycle into the step-indexed mutual recursion.
        //
        //    Specs in general are not parametric in the spec record anymore, which seems like a win.
        //
        //    I guess by separating it out like this, I break the cycle: the spec records are not
        //    parametric in other spec records anymore.
        //
        // For trait impls that I assume, I do not have such a record. Instead, I will
        // say that it needs the default specs.
        // This will match the verification site as I won't allow overrides on those.
        // TODO Q: Can I do something more specific? I could parameterize over
        // that condition... maybe I'm kicking the can down the road then and will run
        // into the same problem again.

        let surrounding_trait_reqs = if spec_needs_surrounding_trait_reqs {
            self.scope_inst.get_surrounding_trait_requirements()
        } else {
            &[]
        };
        let direct_trait_reqs = self.scope_inst.get_direct_trait_requirements();
        // apply to trait specs
        for x in surrounding_trait_reqs.iter().chain(direct_trait_reqs) {
            write!(f, "{} ", x.get_attr_term())?;
            //write!(f, "{} ", x.get_spec_term())?;
        }

        // instantiate semantic terms
        write!(f, "{})", self.scope_inst.instantiation(spec_needs_surrounding_trait_reqs, true))?;

        let trait_req_term = self.get_trait_req_incl_term()?;
        let generics_term = self.quantified_scope.generate_validity_term_for_generics();

        let prop = coq::iris::IProp::Sep(vec![
            generics_term,
            coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(trait_req_term))),
        ]);
        // TODO: don't require that _all_ of them are sized
        //let prop = coq::iris::IProp::Exists(self.quantified_scope.generate_sized_requirements(),
        // Box::new(prop));
        write!(f, " (λ π, {prop})%I)")
    }
}

/// Function's code and specs builder.
///
/// It allows to incrementally construct the functions's code and the spec at the same time. It ensures that
/// both definitions line up in the right way (for instance, by ensuring that other functions are linked up in
/// a consistent way).
#[expect(clippy::partial_pub_fields)]
pub struct FunctionBuilder<'def> {
    pub code: FunctionCodeDef,
    code_name: String,

    /// optionally, a specification, if one has been created
    pub spec: functions::Spec<'def, Option<functions::InnerSpec<'def>>>,

    /// a sequence of other functions used by this function
    /// (Note that there may be multiple assumptions here with the same spec, if they are
    /// monomorphizations of the same function!)
    other_functions: Vec<UsedProcedure<'def>>,

    /// Syntypes we assume to be layoutable in the typing proof
    layoutable_syntys: Vec<lang::SynType>,
    /// used statics
    used_statics: Vec<StaticMeta<'def>>,

    /// unconstrained lfts used by the annotations
    unconstrained_lfts: Vec<Lft>,

    /// manually specified tactics that will be emitted in the typing proof
    tactics: Vec<String>,

    /// maps loop head bbs to loop specifications
    loop_invariants: InvariantMap,

    /// Extra link-time assumptions
    extra_link_assum: Vec<String>,

    /// Do we already have a generic scope?
    has_generic_scope: bool,
}

impl<'def> FunctionBuilder<'def> {
    #[must_use]
    pub fn new(name: &str, code_name: &str, spec_name: &str, trait_req_incl_name: &str) -> Self {
        let code_builder = FunctionCodeDef::new();
        let spec = functions::Spec::empty(
            spec_name.to_owned(),
            trait_req_incl_name.to_owned(),
            name.to_owned(),
            None,
        );
        FunctionBuilder {
            other_functions: Vec::new(),
            code: code_builder,
            code_name: code_name.to_owned(),
            spec,
            layoutable_syntys: Vec::new(),
            loop_invariants: InvariantMap(BTreeMap::new()),
            tactics: Vec::new(),
            used_statics: Vec::new(),
            unconstrained_lfts: Vec::new(),
            extra_link_assum: Vec::new(),
            has_generic_scope: false,
        }
    }

    /// Require another function to be available.
    pub fn require_function(&mut self, proc_use: UsedProcedure<'def>) {
        self.other_functions.push(proc_use);
    }

    /// Require a static variable to be in scope.
    pub fn require_static(&mut self, s: StaticMeta<'def>) {
        info!("Requiring static {:?}", s);
        self.used_statics.push(s);
    }

    /// Add a manual tactic used for a sidecondition proof.
    pub fn add_manual_tactic(&mut self, tac: String) {
        self.tactics.push(tac);
    }

    /// Add a hint request for an unconstrained lifetime.
    pub fn add_unconstrained_lft_hint(&mut self, lft: Lft) {
        self.unconstrained_lfts.push(lft);
    }

    /// Add the assumption that a particular syntype is layoutable to the typing proof.
    pub fn assume_synty_layoutable(&mut self, st: lang::SynType) {
        self.layoutable_syntys.push(st);
    }

    /// Register a loop invariant for the basic block `bb`.
    /// Should only be called once per bb.
    pub fn register_loop_invariant(&mut self, bb: usize, spec: LoopSpec) {
        if self.loop_invariants.0.insert(bb, spec).is_some() {
            panic!("registered loop invariant multiple times");
        }
    }

    /// Add a Coq-level param that comes before the type parameters.
    pub fn add_early_coq_param(&mut self, param: coq::binder::Binder) {
        self.spec.add_early_coq_param(param);
    }

    /// Add a Coq-level param that comes after the type parameters.
    pub fn add_late_coq_param(&mut self, param: coq::binder::Binder) {
        self.spec.add_late_coq_param(param);
    }

    /// Set this function's generic scope.
    pub fn provide_generic_scope(&mut self, scope: GenericScope<'def, traits::LiteralSpecUseRef<'def>>) {
        if self.has_generic_scope {
            panic!("Logic error: Function's generic scope has been initialized twice!");
        }
        self.spec.generics = scope;
        self.has_generic_scope = true;
    }

    /// Add an extra link-time assumption.
    pub fn add_linktime_assumption(&mut self, assumption: String) {
        self.extra_link_assum.push(assumption);
    }

    /// Add a default function spec.
    pub fn add_trait_function_spec(&mut self, spec: traits::InstantiatedFunctionSpec<'def>) {
        assert!(self.spec.spec.is_none(), "Overriding specification of FunctionBuilder");
        self.spec.spec = Some(functions::InnerSpec::TraitDefault(spec));
    }

    /// Add a functon specification from a specification builder.
    pub fn add_function_spec_from_builder(&mut self, spec_builder: functions::LiteralSpecBuilder<'def>) {
        assert!(self.spec.spec.is_none(), "Overriding specification of FunctionBuilder");
        let lit_spec = spec_builder.into_function_spec();
        self.spec.spec = Some(functions::InnerSpec::Lit(lit_spec));
    }

    pub fn into_function(
        mut self,
        arena: &'def Arena<functions::Spec<'def, functions::InnerSpec<'def>>>,
    ) -> Function<'def> {
        assert!(self.spec.spec.is_some(), "No specification provided");

        // sort parameters for code
        self.other_functions.sort_by(|a, b| a.loc_name.cmp(&b.loc_name));
        self.used_statics.sort_by(|a, b| a.ident.cmp(&b.ident));

        let typarams = self.spec.generics.get_all_ty_params_with_assocs();
        let code = FunctionCode::new(
            &self.code_name,
            &self.spec.function_name,
            self.code,
            &typarams,
            &self.other_functions,
            &self.used_statics,
        );

        // assemble the spec
        let lit_spec = self.spec.spec.take().unwrap();
        let spec = self.spec.replace_spec(lit_spec);
        let spec_ref = arena.alloc(spec);

        Function {
            code,
            spec: spec_ref,
            other_functions: self.other_functions,
            layoutable_syntys: self.layoutable_syntys,
            loop_invariants: self.loop_invariants,
            manual_tactics: self.tactics,
            used_statics: self.used_statics,
            unconstrained_lfts: self.unconstrained_lfts,
            extra_link_assum: self.extra_link_assum,
        }
    }
}

impl<'def> TryFrom<FunctionBuilder<'def>> for functions::Spec<'def, functions::InnerSpec<'def>> {
    type Error = String;

    fn try_from(mut builder: FunctionBuilder<'def>) -> Result<Self, String> {
        let spec = builder.spec.spec.take().ok_or_else(|| "No specification was provided".to_owned())?;
        Ok(builder.spec.replace_spec(spec))
    }
}
