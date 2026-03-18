// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Provides the Spec AST and utilities for interfacing with it.

use std::collections::BTreeSet;
use std::fmt;
use std::fmt::Write as _;
use std::marker::PhantomData;

use derive_more::{Constructor, Display};

use crate::{BASE_INDENT, coq, fmt_list, lang, model, push_str_list, write_list};

pub mod enums;
pub mod functions;
pub mod invariants;
pub mod structs;
pub mod traits;
pub mod types;

/// Representation of (semantic) `RefinedRust` types.
/// 'def is the lifetime of the frontend for referencing ADT definitions.
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum Type<'def> {
    #[display("bool_t")]
    Bool,

    #[display("char_t")]
    Char,

    #[display("(int {})", _0)]
    Int(lang::IntType),

    #[display("(mut_ref {} {})", _1, _0)]
    MutRef(Box<Self>, Lft),

    #[display("(shr_ref {} {})", _1, _0)]
    ShrRef(Box<Self>, Lft),

    #[display("(array_t {} {})", _1, _0)]
    Array(Box<Self>, u128),

    /// a struct type, potentially instantiated with some type parameters
    /// the boolean indicates
    #[display("{}", _0.generate_type_term())]
    Struct(structs::AbstractUse<'def>),

    /// an enum type, potentially instantiated with some type parameters
    #[display("{}", _0.generate_type_term())]
    Enum(enums::AbstractUse<'def>),

    /// literal types (defined outside of the current module) embedded as strings
    #[display("{}", _0.generate_type_term())]
    Literal(types::LiteralUse<'def>),

    /// literal type parameters
    #[display("{}", _0.type_term())]
    LiteralParam(LiteralTyParam),

    /// the uninit type given to uninitialized values
    #[display("(uninit ({}))", _0)]
    Uninit(lang::SynType),

    /// the unit type
    #[display("unit_t")]
    Unit,

    /// the Never type
    #[display("never_t")]
    Never,

    /// dummy type that should be overridden by an annotation
    #[display("alias_ptr_t")]
    RawPtr,
}

impl<'def> From<Type<'def>> for lang::SynType {
    fn from(x: Type<'def>) -> Self {
        Self::from(&x)
    }
}

impl<'def> From<&Type<'def>> for lang::SynType {
    /// Get the layout of a type.
    fn from(x: &Type<'def>) -> Self {
        match x {
            Type::Bool => Self::Bool,
            Type::Char => Self::Char,
            Type::Int(it) => Self::Int(*it),

            Type::MutRef(..) | Type::ShrRef(..) | Type::RawPtr => Self::Ptr,

            Type::Struct(s) => s.generate_syn_type_term(),
            Type::Enum(s) => s.generate_syn_type_term(),

            Type::Literal(lit) => lit.generate_syn_type_term(),
            Type::Uninit(st) => st.clone(),
            Type::Array(ty, len) => Self::Array(Box::new(ty.as_ref().to_owned().into()), *len),

            Type::Unit => Self::Unit,
            // NOTE: for now, just treat Never as a ZST
            Type::Never => Self::Never,

            Type::LiteralParam(lit) => Self::Literal(lit.syn_type()),
        }
    }
}

impl Type<'_> {
    /// Make the first type in the type tree having an invariant not use the invariant.
    pub fn make_raw(&mut self) {
        match self {
            Self::Struct(su) => su.make_raw(),
            Self::MutRef(box ty, _) | Self::ShrRef(box ty, _) => ty.make_raw(),
            _ => (),
        }
    }

    /// Determines the type this type is refined by.
    #[must_use]
    pub fn get_rfn_type(&self) -> coq::term::Type {
        match self {
            Self::Bool => coq::term::Type::Bool,
            Self::Char | Self::Int(_) => coq::term::Type::Z,

            Self::MutRef(box ty, _) => coq::term::Type::Prod(vec![
                model::Type::PlaceRfn(Box::new(ty.get_rfn_type())).into(),
                model::Type::Gname.into(),
            ]),

            Self::ShrRef(box ty, _) => model::Type::PlaceRfn(Box::new(ty.get_rfn_type())).into(),

            Self::RawPtr => model::Type::Loc.into(),

            Self::LiteralParam(lit) => coq::term::Type::Literal(lit.refinement_type()),
            Self::Literal(lit) => coq::term::Type::Literal(lit.get_rfn_type()),

            Self::Struct(su) => {
                // NOTE: we don't need to subst, due to our invariant that the instantiations for
                // struct uses are already fully substituted
                coq::term::Type::Literal(su.get_rfn_type())
            },
            Self::Enum(su) => {
                // similar to structs, we don't need to subst
                coq::term::Type::Literal(su.get_rfn_type())
            },

            Self::Array(ty, _) => coq::term::Type::List(Box::new(ty.get_rfn_type())),

            Self::Unit | Self::Never | Self::Uninit(_) => {
                // NOTE: could also choose to use an uninhabited type for Never
                coq::term::Type::Unit
            },
        }
    }

    /// Determines the surface refinement type.
    #[must_use]
    pub fn get_xt_type(&self) -> coq::term::Type {
        let app =
            coq::term::App::new(coq::term::Term::Literal("RT_xt".to_owned()), vec![coq::term::Term::Type(
                Box::new(self.get_rfn_type()),
            )]);
        let app = coq::term::Term::App(Box::new(app));
        coq::term::Type::Term(Box::new(app))
    }
}

/// Encodes a RR type with an accompanying refinement.
#[derive(Clone, Eq, PartialEq, Debug, Display, Constructor)]
#[display("{} :@: {}", _1, _0)]
pub struct TypeWithRef<'def>(pub Type<'def>, pub String);

impl TypeWithRef<'_> {
    #[must_use]
    fn make_unit() -> Self {
        TypeWithRef(Type::Unit, "()".to_owned())
    }
}

pub type Lft = coq::Ident;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum LftParamOrigin {
    SurroundingTrait,
    SurroundingImpl,
    LocalEarlyBound,
    LocalLateBound,
    ForBinder,
    /// RefinedRust-specific: a re-bound binder for a generic function
    FunctionRebound,
}

#[derive(Clone, Debug, Constructor, Display, PartialEq, Eq)]
#[display("{}", lft)]
pub struct LftParam {
    lft: coq::Ident,
    origin: LftParamOrigin,
}
impl From<LftParam> for Lft {
    fn from(x: LftParam) -> Self {
        x.lft
    }
}

impl LftParam {
    #[must_use]
    pub const fn lft(&self) -> &Lft {
        &self.lft
    }
}

/// A universal lifetime that is not locally owned.
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum UniversalLft {
    #[display("ϝ")]
    Function,

    #[display("static")]
    Static,

    #[display("{}", _0)]
    Local(Lft),

    #[display("{}", _0)]
    External(Lft),
}

/// Meta information from parsing type annotations
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TypeAnnotMeta {
    /// Used lifetime variables
    escaped_lfts: BTreeSet<Lft>,
    /// Used type variables
    escaped_tyvars: BTreeSet<LiteralTyParam>,
}

impl TypeAnnotMeta {
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.escaped_lfts.is_empty() && self.escaped_tyvars.is_empty()
    }

    #[must_use]
    pub const fn empty() -> Self {
        Self {
            escaped_lfts: BTreeSet::new(),
            escaped_tyvars: BTreeSet::new(),
        }
    }

    pub fn join(&mut self, s: &Self) {
        let lfts: BTreeSet<_> = self.escaped_lfts.union(&s.escaped_lfts).cloned().collect();
        let tyvars: BTreeSet<_> = self.escaped_tyvars.union(&s.escaped_tyvars).cloned().collect();

        self.escaped_lfts = lfts;
        self.escaped_tyvars = tyvars;
    }

    pub fn add_lft(&mut self, lft: Lft) {
        self.escaped_lfts.insert(lft);
    }

    pub fn add_type(&mut self, ty: &Type<'_>) {
        if let Type::LiteralParam(lit) = ty {
            self.escaped_tyvars.insert(lit.to_owned());
        }
        // TODO: handle the case that it is unknown
    }
}

fn format_extra_context_items<F>(
    items: &[coq::binder::Binder],
    f: &mut F,
) -> Result<(Vec<String>, Vec<String>), fmt::Error>
where
    F: fmt::Write,
{
    let mut context_names = Vec::new();
    let mut context_names_without_sigma = Vec::new();
    let mut counter = 0;

    // write coq parameters
    if !items.is_empty() {
        write!(f, "{} (* Additional parameters *)\n", BASE_INDENT)?;
        write!(f, "{}Context ", BASE_INDENT)?;

        for it in items {
            let name = format!("_CTX{}", counter);
            counter += 1;

            write!(f, "{}", it.clone().set_name(name.clone()))?;

            if !it.is_dependent_on_sigma() {
                context_names_without_sigma.push(name.clone());
            }
            context_names.push(name);
        }
        write!(f, ".\n")?;
    }
    write!(f, "\n")?;

    Ok((context_names, context_names_without_sigma))
}

/// The origin of a type parameter.
#[derive(Clone, Copy, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub enum TyParamOrigin {
    /// Declared in a surrounding trait declaration.
    SurroundingTrait,
    /// Declared in a surrounding trait impl
    SurroundingImpl,
    /// A direct parameter of a method or impl.
    Direct,
    /// An associated type in the trait being declared.
    AssocInDecl,
}

#[derive(Clone, Eq, PartialEq, Ord, PartialOrd, Debug)]
#[expect(clippy::partial_pub_fields)]
pub struct LiteralTyParam {
    /// Rust name
    pub rust_name: String,

    /// the declaration site of this type parameter
    origin: TyParamOrigin,
}

impl LiteralTyParam {
    #[must_use]
    pub fn new(rust_name: &str) -> Self {
        Self {
            rust_name: rust_name.to_owned(),
            origin: TyParamOrigin::Direct,
        }
    }

    #[must_use]
    pub fn new_with_origin(rust_name: &str, origin: TyParamOrigin) -> Self {
        let mut x = Self::new(rust_name);
        x.origin = origin;
        x
    }

    pub const fn set_origin(&mut self, origin: TyParamOrigin) {
        self.origin = origin;
    }

    /// Rocq name of the type
    #[must_use]
    pub(crate) fn type_term(&self) -> String {
        format!("{}_ty", self.rust_name)
    }

    /// The refinement type
    #[must_use]
    pub(crate) fn refinement_type(&self) -> String {
        format!("{}_rt", self.rust_name)
    }

    /// The syntactic type
    #[must_use]
    pub fn syn_type(&self) -> String {
        format!("{}_st", self.rust_name)
    }

    #[must_use]
    fn make_refinement_param(&self) -> coq::binder::Binder {
        coq::binder::Binder::new(Some(self.refinement_type()), coq::term::Type::RT)
    }

    #[must_use]
    fn make_syntype_param(&self) -> coq::binder::Binder {
        coq::binder::Binder::new(Some(self.syn_type()), model::Type::SynType)
    }

    #[must_use]
    fn make_semantic_param(&self) -> coq::binder::Binder {
        coq::binder::Binder::new(
            Some(self.type_term()),
            model::Type::Ttype(Box::new(coq::term::Type::Literal(self.refinement_type()))),
        )
    }
}

/// Specification for location ownership of a type.
#[derive(Clone, PartialEq, Eq, Debug, Constructor)]
pub struct TyOwnSpec {
    loc: String,
    rfn: String,
    /// type, with generics already fully substituted
    ty: String,
    with_later: bool,
    /// literal lifetimes and types escaped in the annotation parser
    annot_meta: TypeAnnotMeta,
}

impl TyOwnSpec {
    #[must_use]
    pub fn fmt_owned(&self, tid: &str) -> String {
        if self.with_later {
            format!("guarded true ({} ◁ₗ[{}, Owned] #({}) @ (◁ {}))", self.loc, tid, self.rfn, self.ty)
        } else {
            format!("{} ◁ₗ[{}, Owned] #({}) @ (◁ {})", self.loc, tid, self.rfn, self.ty)
        }
    }

    #[must_use]
    fn fmt_shared(&self, tid: &str, lft: &str) -> String {
        if self.with_later {
            format!(
                "guarded false ({} ◁ₗ[{}, Shared {}] #({}) @ (◁ {}))",
                self.loc, tid, lft, self.rfn, self.ty
            )
        } else {
            format!("{} ◁ₗ[{}, Shared {}] #({}) @ (◁ {})", self.loc, tid, lft, self.rfn, self.ty)
        }
    }
}

/// Representation of a loop invariant
#[derive(Clone, Constructor, Debug)]
pub struct LoopSpec {
    /// the functional invariant as a predicate on the refinement of local variables.
    func_predicate: coq::term::Term,
    inv_locals: Vec<String>,
    preserved_locals: Vec<String>,
    uninit_locals: Vec<String>,
    iterator_local: Option<String>,
}

impl fmt::Display for LoopSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "([{}], [{}], [{}], wrap_inv ({}), wrap_inv (λ (L : llctx), True%I : iProp Σ), {})",
            fmt_list!(&self.inv_locals, "; ", |x| format!("\"{x}\"")),
            fmt_list!(&self.preserved_locals, "; ", |x| format!("\"{x}\"")),
            fmt_list!(&self.uninit_locals, "; ", |x| format!("\"{x}\"")),
            self.func_predicate,
            if let Some(var) = &self.iterator_local { format!("Some \"{var}\"") } else { "None".to_owned() },
        )?;

        Ok(())
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Constructor)]
pub struct TyParamList {
    pub params: Vec<LiteralTyParam>,
}

impl TyParamList {
    #[must_use]
    const fn empty() -> Self {
        Self { params: vec![] }
    }

    fn append(&mut self, mut other: Vec<LiteralTyParam>) {
        self.params.append(&mut other);
    }

    fn merge(&mut self, other: Self) {
        self.append(other.params);
    }

    /// Get the Coq parameters that need to be in scope for the type parameters of this function.
    #[must_use]
    pub(crate) fn get_coq_ty_st_params(&self) -> coq::binder::BinderList {
        let mut ty_coq_params = Vec::new();
        for names in &self.params {
            ty_coq_params.push(names.make_syntype_param());
        }
        coq::binder::BinderList::new(ty_coq_params)
    }

    #[must_use]
    fn get_coq_ty_rt_params(&self) -> coq::binder::BinderList {
        let mut ty_coq_params = Vec::new();
        for names in &self.params {
            ty_coq_params.push(names.make_refinement_param());
        }
        coq::binder::BinderList::new(ty_coq_params)
    }

    #[must_use]
    fn get_coq_ty_params(&self) -> coq::binder::BinderList {
        let mut rt_params = self.get_coq_ty_rt_params();
        let st_params = self.get_coq_ty_st_params();
        rt_params.append(st_params.0);
        rt_params
    }

    #[must_use]
    fn get_semantic_ty_params(&self) -> coq::binder::BinderList {
        let mut ty_coq_params = Vec::new();
        for names in &self.params {
            ty_coq_params.push(names.make_semantic_param());
        }
        coq::binder::BinderList::new(ty_coq_params)
    }
}

/// An instantiation of a scope of generics `GenericScope`.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct GenericScopeInst<'def> {
    direct_tys: Vec<Type<'def>>,
    surrounding_tys: Vec<Type<'def>>,

    direct_trait_requirements: Vec<traits::ReqInst<'def, Type<'def>>>,
    surrounding_trait_requirements: Vec<traits::ReqInst<'def, Type<'def>>>,

    // TODO maybe also separate into direct and surrounding?
    lfts: Vec<Lft>,
}

impl<'def> GenericScopeInst<'def> {
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            direct_tys: Vec::new(),
            surrounding_tys: Vec::new(),
            direct_trait_requirements: Vec::new(),
            surrounding_trait_requirements: Vec::new(),
            lfts: Vec::new(),
        }
    }

    pub fn add_direct_ty_param(&mut self, ty: Type<'def>) {
        self.direct_tys.push(ty);
    }

    pub fn add_surrounding_ty_param(&mut self, ty: Type<'def>) {
        self.surrounding_tys.push(ty);
    }

    pub fn clear_surrounding(&mut self) {
        self.surrounding_tys.clear();
        self.surrounding_trait_requirements.clear();
    }

    pub fn add_lft_param(&mut self, lft: Lft) {
        self.lfts.push(lft);
    }

    /// Add a trait requirement.
    pub fn add_trait_requirement(&mut self, req: traits::ReqInst<'def, Type<'def>>) {
        if req.get_origin() == TyParamOrigin::Direct {
            self.direct_trait_requirements.push(req);
        } else {
            self.surrounding_trait_requirements.push(req);
        }
    }

    #[must_use]
    fn get_surrounding_ty_params(&self) -> &[Type<'def>] {
        &self.surrounding_tys
    }

    #[must_use]
    pub fn get_direct_ty_params(&self) -> &[Type<'def>] {
        &self.direct_tys
    }

    #[must_use]
    fn get_direct_assoc_ty_params(&self) -> Vec<Type<'def>> {
        let ty_params = self.direct_trait_requirements.iter().map(|x| x.get_assoc_ty_inst().to_vec());

        ty_params.flatten().collect()
    }

    #[must_use]
    fn get_surrounding_assoc_ty_params(&self) -> Vec<Type<'def>> {
        let ty_params = self.surrounding_trait_requirements.iter().map(|x| x.get_assoc_ty_inst().to_vec());

        ty_params.flatten().collect()
    }

    #[must_use]
    pub fn get_direct_ty_params_with_assocs(&self) -> Vec<Type<'def>> {
        let mut direct = self.get_direct_ty_params().to_vec();
        direct.append(&mut self.get_direct_assoc_ty_params());
        direct
    }

    #[must_use]
    fn get_surrounding_ty_params_with_assocs(&self) -> Vec<Type<'def>> {
        let mut surrounding = self.get_surrounding_ty_params().to_vec();
        surrounding.append(&mut self.get_surrounding_assoc_ty_params());
        surrounding
    }

    #[must_use]
    pub fn get_all_ty_params_with_assocs(&self) -> Vec<Type<'def>> {
        let mut params = self.get_surrounding_ty_params_with_assocs();
        let mut direct = self.get_direct_ty_params_with_assocs();
        params.append(&mut direct);
        params
    }

    /// Generate an instantiation of a term with the identity
    #[must_use]
    pub(crate) fn instantiation(&self, include_surrounding_reqs: bool, fully: bool) -> String {
        let mut out = String::new();

        if include_surrounding_reqs {
            for ty in self.get_surrounding_ty_params_with_assocs() {
                out.push_str(&format!(" <TY> {}", ty));
            }
        }
        for ty in self.get_direct_ty_params_with_assocs() {
            out.push_str(&format!(" <TY> {}", ty));
        }
        for lft in self.get_lfts() {
            out.push_str(&format!(" <LFT> {}", lft));
        }
        if fully {
            out.push_str(" <INST!>");
        }

        out
    }

    #[must_use]
    pub fn get_lfts(&self) -> &[Lft] {
        &self.lfts
    }

    #[must_use]
    pub(crate) fn get_direct_trait_requirements(&self) -> &[traits::ReqInst<'def, Type<'def>>] {
        &self.direct_trait_requirements
    }

    #[must_use]
    pub(crate) fn get_surrounding_trait_requirements(&self) -> &[traits::ReqInst<'def, Type<'def>>] {
        &self.surrounding_trait_requirements
    }
}

/// How to handle the Self trait requirement in the context of a trait declaration.
#[derive(Debug, Eq, PartialEq, Clone, Copy)]
pub enum IncludeSelfReq {
    // Do not include the self requirement at all
    Dont,
    // only include the attributes
    Attrs,
    // include both the attribute and specification
    AttrsSpec,
}

impl IncludeSelfReq {
    #[must_use]
    pub fn include_attrs(self) -> bool {
        self == Self::Attrs || self == Self::AttrsSpec
    }

    #[must_use]
    pub fn include_spec(self) -> bool {
        self == Self::AttrsSpec
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LftConstr<'def> {
    LftOutlives(UniversalLft, UniversalLft),
    TypeOutlives(Type<'def>, UniversalLft),
}

/// A context of lifetime constraints
#[derive(Clone, Debug, Eq, PartialEq, Default)]
pub struct Elctx<'def> {
    constrs: Vec<LftConstr<'def>>,
}

/// A scope of generics.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct GenericScope<'def, T = traits::LiteralSpecUseRef<'def>> {
    /// generics quantified on this object.
    direct_tys: TyParamList,
    /// generics quantified by a surrounding scope.
    surrounding_tys: TyParamList,

    /// trait requirements quantified on this object.
    direct_trait_requirements: Vec<T>,
    /// trait requirements quantified by a surrounding scope.
    surrounding_trait_requirements: Vec<T>,

    pub(crate) lfts: Vec<LftParam>,

    /// lifetime constraints
    lft_constraints: Elctx<'def>,

    _phantom: PhantomData<&'def ()>,
}

impl<'def, T: traits::ReqInfo> GenericScope<'def, T> {
    /// Create an empty scope.
    #[must_use]
    pub fn empty() -> Self {
        Self {
            direct_tys: TyParamList::empty(),
            surrounding_tys: TyParamList::empty(),
            direct_trait_requirements: Vec::new(),
            surrounding_trait_requirements: Vec::new(),
            lfts: Vec::new(),
            lft_constraints: Elctx::default(),
            _phantom: PhantomData {},
        }
    }

    fn format_elctx(&self) -> String {
        let mut out = String::with_capacity(100);

        out.push_str("λ ϝ, [");

        // implied bounds on inputs/outputs
        let lft_outlives: Vec<_> = self
            .lft_constraints
            .constrs
            .iter()
            .filter_map(|constr| match constr {
                LftConstr::LftOutlives(lft1, lft2) => Some(format!("({lft1}, {lft2})")),
                LftConstr::TypeOutlives(_, _) => None,
            })
            .collect();
        push_str_list!(out, &lft_outlives, "; ");

        // all lifetime parameters outlive this function
        if !lft_outlives.is_empty() && !self.lfts.is_empty() {
            out.push_str("; ");
        }
        push_str_list!(out, &self.lfts, "; ", |lft| format!("(ϝ, {lft})"));

        out.push(']');

        // type outlives constraints
        let ty_outlives: Vec<_> = self
            .lft_constraints
            .constrs
            .iter()
            .filter_map(|constr| match constr {
                LftConstr::TypeOutlives(ty, lft) => Some(format!("ty_outlives_E ({ty}) {lft}")),
                _ => None,
            })
            .collect();
        if !ty_outlives.is_empty() {
            out.push_str(" ++ ");
            push_str_list!(out, ty_outlives, " ++ ");
        }

        out
    }

    /// Get the validity term for a generic on a function.
    #[must_use]
    pub(crate) fn generate_validity_term_for_generics(&self) -> coq::iris::IProp {
        let mut props = Vec::new();
        for ty in self.get_all_ty_params_with_assocs().params {
            props.push(Self::generate_validity_term_for_typaram(&ty));
        }
        coq::iris::IProp::Sep(props)
    }

    #[must_use]
    fn generate_validity_term_for_typaram(ty: &LiteralTyParam) -> coq::iris::IProp {
        let prop = format!("typaram_wf {} {} {}", ty.refinement_type(), ty.syn_type(), ty.type_term());
        coq::iris::IProp::Atom(prop)
    }

    /// Get type parameters quantified by a surrounding scope.
    #[must_use]
    const fn get_surrounding_ty_params(&self) -> &TyParamList {
        &self.surrounding_tys
    }

    /// Get type parameters quantified on this object.
    #[must_use]
    pub const fn get_direct_ty_params(&self) -> &TyParamList {
        &self.direct_tys
    }

    /// Get associated type parameters of trait requirements on this object.
    #[must_use]
    pub fn get_direct_assoc_ty_params(&self) -> TyParamList {
        let ty_params = self.direct_trait_requirements.iter().map(traits::ReqInfo::get_assoc_ty_params);

        TyParamList::new(ty_params.flatten().collect())
    }

    /// Get associated type parameters of trait requirements quantified by a surrounding scope.
    #[must_use]
    pub fn get_surrounding_assoc_ty_params(&self) -> TyParamList {
        let ty_params = self.surrounding_trait_requirements.iter().map(traits::ReqInfo::get_assoc_ty_params);

        TyParamList::new(ty_params.flatten().collect())
    }

    /// Get direct type parameters and associated type parameters.
    #[must_use]
    pub fn get_direct_ty_params_with_assocs(&self) -> TyParamList {
        let mut direct = self.get_direct_ty_params().clone();
        direct.merge(self.get_direct_assoc_ty_params());
        direct
    }

    /// Get type parameters and associated type parameters quantified by a surrounding scope.
    #[must_use]
    pub fn get_surrounding_ty_params_with_assocs(&self) -> TyParamList {
        let mut surrounding = self.get_surrounding_ty_params().clone();
        surrounding.merge(self.get_surrounding_assoc_ty_params());
        surrounding
    }

    /// Get all type parameters and associated type parameters.
    #[must_use]
    pub fn get_all_ty_params_with_assocs(&self) -> TyParamList {
        let mut params = self.get_surrounding_ty_params_with_assocs();
        let direct = self.get_direct_ty_params_with_assocs();
        params.merge(direct);
        params
    }

    /// Generate an instantiation of a term with the identity
    #[must_use]
    pub(crate) fn identity_instantiation_term(&self) -> String {
        let mut out = String::new();

        for ty in self.get_all_ty_params_with_assocs().params {
            out.push_str(&format!(" <TY> {}", ty.type_term()));
        }
        for lft in self.get_lfts() {
            out.push_str(&format!(" <LFT> {}", lft));
        }
        out.push_str(" <INST!>");

        out
    }

    #[must_use]
    fn get_spec_all_type_term(&self, spec: Box<coq::term::Type>) -> coq::term::Type {
        let params = self.get_all_ty_params_with_assocs();

        coq::term::Type::UserDefined(model::Type::SpecWith(
            self.get_num_lifetimes(),
            // TODO: `LiteralTyParam` should take `Type` instead of `String`
            params.params.iter().map(|x| coq::term::Type::Literal(x.refinement_type())).collect(),
            spec,
        ))
    }

    #[must_use]
    #[deprecated(note = "Use `get_spec_all_type_term` instead")]
    fn get_all_type_term(&self) -> String {
        let mut out = String::new();

        out.push_str(&format!("spec_with {} [", self.get_num_lifetimes()));
        let tys = self.get_all_ty_params_with_assocs();
        push_str_list!(out, &tys.params, "; ", LiteralTyParam::refinement_type);
        out.push(']');

        out
    }

    #[must_use]
    pub fn get_lfts(&self) -> &[LftParam] {
        &self.lfts
    }

    /// Get trait requirements declared on the object.
    #[must_use]
    pub fn get_direct_trait_requirements(&self) -> &[T] {
        &self.direct_trait_requirements
    }

    /// Get trait requirements surrounding the object.
    #[must_use]
    pub fn get_surrounding_trait_requirements(&self) -> &[T] {
        &self.surrounding_trait_requirements
    }

    pub fn add_ty_param(&mut self, ty: LiteralTyParam) {
        if ty.origin == TyParamOrigin::Direct {
            self.direct_tys.params.push(ty);
        } else {
            self.surrounding_tys.params.push(ty);
        }
    }

    pub fn add_lft_param(&mut self, lft: LftParam) {
        self.lfts.push(lft);
    }

    pub fn add_lft_constr(&mut self, constr: LftConstr<'def>) {
        self.lft_constraints.constrs.push(constr);
    }

    pub fn remove_lft_param(&mut self, lft: &Lft) {
        if let Some(p) = self.lfts.iter().position(|x| x.lft() == lft) {
            self.lfts.remove(p);
        }
    }

    /// Add a trait requirement.
    pub fn add_trait_requirement(&mut self, req: T) {
        if req.get_origin() == TyParamOrigin::Direct {
            self.direct_trait_requirements.push(req);
        } else {
            self.surrounding_trait_requirements.push(req);
        }
    }

    #[must_use]
    pub(crate) const fn get_num_lifetimes(&self) -> usize {
        self.lfts.len()
    }

    #[must_use]
    pub(crate) fn get_num_direct_lifetimes(&self) -> usize {
        self.lfts
            .iter()
            .filter(|x| {
                x.origin == LftParamOrigin::LocalEarlyBound
                    || x.origin == LftParamOrigin::LocalLateBound
                    || x.origin == LftParamOrigin::ForBinder
            })
            .count()
    }

    /// Format this generic scope.
    pub(crate) fn format<F>(
        &self,
        f: &mut F,
        only_core_as_fn: bool,
        direct_extra_tys: &[LiteralTyParam],
    ) -> fmt::Result
    where
        F: fmt::Write,
    {
        let mut lft_pattern = String::with_capacity(100);
        write!(lft_pattern, "( *[")?;
        write_list!(lft_pattern, &self.lfts, "; ")?;
        write!(lft_pattern, "])")?;

        let mut all_params = self.get_surrounding_ty_params().clone();
        all_params.merge(self.get_surrounding_assoc_ty_params());
        all_params.merge(self.get_direct_ty_params().clone());
        all_params.append(direct_extra_tys.to_vec());
        all_params.merge(self.get_direct_assoc_ty_params());

        let mut typarams_pattern = String::with_capacity(100);

        write!(typarams_pattern, "( *[")?;
        write_list!(typarams_pattern, &all_params.params, "; ", LiteralTyParam::type_term)?;
        write!(typarams_pattern, "])")?;

        let mut typarams_ty_list = String::with_capacity(100);
        write!(typarams_ty_list, "[")?;
        write_list!(typarams_ty_list, &all_params.params, "; ", |x| {
            if only_core_as_fn {
                format!("({}, {})", x.refinement_type(), x.syn_type())
            } else {
                x.refinement_type()
            }
        })?;
        write!(typarams_ty_list, "]")?;

        if only_core_as_fn {
            write!(
                f,
                "{lft_pattern} : {} | {typarams_pattern} : ({typarams_ty_list} : list (RT * syn_type)%type)",
                self.lfts.len()
            )
        } else {
            write!(
                f,
                "spec! {lft_pattern} : {} | {typarams_pattern} : ({typarams_ty_list} : list RT),",
                self.lfts.len()
            )
        }
    }
}

impl<T: traits::ReqInfo + Clone> GenericScope<'_, T> {
    pub fn append(&mut self, other: &Self) {
        self.direct_tys.merge(other.direct_tys.clone());
        self.surrounding_tys.merge(other.surrounding_tys.clone());
        for lft in &other.lfts {
            self.lfts.push(lft.to_owned());
        }
        self.direct_trait_requirements.extend(other.direct_trait_requirements.iter().cloned());
        self.surrounding_trait_requirements
            .extend(other.surrounding_trait_requirements.iter().cloned());
    }
}

impl<T: traits::ReqInfo> fmt::Display for GenericScope<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format(f, false, &[])
    }
}

impl<'def> GenericScope<'def, traits::LiteralSpecUseRef<'def>> {
    #[must_use]
    fn get_direct_attr_trait_parameters(&self, include_self: IncludeSelfReq) -> coq::binder::BinderList {
        self.get_trait_req_parameters(false, true, include_self, false)
    }

    #[must_use]
    fn get_all_trait_parameters(&self, include_self: IncludeSelfReq) -> coq::binder::BinderList {
        self.get_trait_req_parameters(true, true, include_self, true)
    }

    #[must_use]
    fn get_all_attr_trait_parameters(&self, include_self: IncludeSelfReq) -> coq::binder::BinderList {
        self.get_trait_req_parameters(true, true, include_self, false)
    }

    fn get_trait_req_parameters(
        &self,
        include_surrounding: bool,
        include_direct: bool,
        include_self: IncludeSelfReq,
        include_spec: bool,
    ) -> coq::binder::BinderList {
        let mut params = Vec::new();

        // add trait reqs
        let trait_reqs =
            if include_surrounding { self.get_surrounding_trait_requirements().iter() } else { [].iter() };

        let trait_reqs = if include_direct {
            trait_reqs.chain(self.get_direct_trait_requirements().iter())
        } else {
            trait_reqs.chain(&[])
        };

        for trait_use in trait_reqs {
            let trait_use = trait_use.borrow();
            let trait_use = trait_use.as_ref().unwrap();

            if !trait_use.is_used_in_self_trait || include_self.include_attrs() {
                params.push(trait_use.get_attr_param());
            }

            // if we're not in the same trait declaration, add the spec
            if include_spec && (!trait_use.is_used_in_self_trait || include_self.include_spec()) {
                params.push(trait_use.get_spec_param());
            }
        }

        coq::binder::BinderList::new(params)
    }

    #[must_use]
    pub fn identity_instantiation(&self) -> GenericScopeInst<'def> {
        let direct_tys: Vec<_> =
            self.direct_tys.params.iter().map(|x| Type::LiteralParam(x.to_owned())).collect();
        let surrounding_tys: Vec<_> =
            self.surrounding_tys.params.iter().map(|x| Type::LiteralParam(x.to_owned())).collect();

        let direct_trait_requirements = self
            .direct_trait_requirements
            .iter()
            .map(|x| traits::ReqInst::new_as_identity(x))
            .collect();
        let surrounding_trait_requirements = self
            .surrounding_trait_requirements
            .iter()
            .map(|x| traits::ReqInst::new_as_identity(x))
            .collect();

        GenericScopeInst {
            direct_tys,
            surrounding_tys,
            direct_trait_requirements,
            surrounding_trait_requirements,
            lfts: self.lfts.iter().map(|x| x.lft().to_owned()).collect(),
        }
    }
}
