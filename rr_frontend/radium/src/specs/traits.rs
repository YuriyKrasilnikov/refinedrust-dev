// © 2025, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::cell::RefCell;
use std::collections::BTreeMap;
use std::fmt;
use std::fmt::Write as _;

use derive_more::Constructor;
use log::trace;

use crate::specs::{
    GenericScope, GenericScopeInst, IncludeSelfReq, Lft, LiteralTyParam, TyParamList, TyParamOrigin, Type,
    functions,
};
use crate::{coq, fmt_list, lang, model, push_str_list, write_list};

/// A specification for a method of a trait impl.
#[derive(Clone, Debug)]
pub enum InstanceMethodSpec<'def> {
    /// This has its own specification.
    Defined(&'def functions::Spec<'def, functions::InnerSpec<'def>>),
    /// This uses a default impl for which we cannot create a separate `functions::Spec`.
    DefaultSpec(Box<InstantiatedFunctionSpec<'def>>, GenericScope<'def>, String),
}

impl<'def> InstanceMethodSpec<'def> {
    fn get_spec_name(&self) -> &str {
        match self {
            Self::Defined(spec) => &spec.spec_name,
            Self::DefaultSpec(_, _, name) => name,
        }
    }

    const fn get_direct_scope(&self) -> &GenericScope<'def> {
        match self {
            Self::Defined(spec) => &spec.generics,
            Self::DefaultSpec(_, direct_scope, _) => direct_scope,
        }
    }

    fn surrounding_scope_instantiation(
        &self,
        surrounding_scope: &GenericScope<'def>,
    ) -> GenericScopeInst<'def> {
        match self {
            Self::Defined(_spec) => surrounding_scope.identity_instantiation(),
            Self::DefaultSpec(spec, _, _) => spec.trait_ref.trait_inst.clone(),
        }
    }

    fn self_assoc_types_inst(&self, assoc_quantifiers: &[LiteralTyParam]) -> Vec<Type<'def>> {
        let mut tys = Vec::new();
        match self {
            Self::Defined(_) => {
                for x in assoc_quantifiers {
                    tys.push(Type::LiteralParam(x.to_owned()));
                }
            },
            Self::DefaultSpec(spec, _, _) => {
                for x in &spec.trait_ref.assoc_types_inst {
                    tys.push(x.to_owned());
                }
            },
        }
        tys
    }

    fn self_trait_attr_inst(&self) -> Option<coq::term::Term> {
        if let Self::DefaultSpec(spec, _, _) = self {
            Some(coq::term::Term::App(Box::new(spec.trait_ref.get_attr_record_term())))
        } else {
            None
        }
    }
}

/// A specification for a particular instance of a trait
#[derive(Constructor, Clone, Debug)]
pub struct InstanceSpec<'def> {
    /// a map from the identifiers to the method specs
    pub methods: BTreeMap<String, InstanceMethodSpec<'def>>,
}

/// Specification attribute declaration of a trait
#[derive(Constructor, Clone, Debug)]
pub struct SpecAttrsDecl {
    /// a map of attributes and their types
    attrs: Option<BTreeMap<String, coq::term::Type>>,
    /// optionally, a semantic interpretation (like `Copy`) of the trait in terms of semantic types
    semantic_interp: Option<String>,
}

#[derive(Clone, Debug)]
pub enum SpecAttrInst {
    /// attribute is implemented with a term
    Term(coq::term::Term),
    /// attribute is implemented with an Ltac proof
    Proof(String),
}

/// Implementation of the attributes of a trait
#[derive(Constructor, Clone, Debug)]
pub struct SpecAttrsInst {
    /// a map of attributes and their implementation
    pub attrs: BTreeMap<String, SpecAttrInst>,
}

/// A using occurrence of a trait spec.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct LiteralSpec {
    /// Name of the trait
    pub name: String,

    /// Associated types
    pub assoc_tys: Vec<String>,

    /// The optional name of the Rocq definition for the traits's semantic interpretation
    pub has_semantic_interp: bool,

    /// Whether the attrs record is dependent on the attrs of trait dependencies.
    pub attrs_dependent: bool,

    /// declared attributes of the trait
    pub declared_attrs: Vec<String>,

    /// maps each trait method to its canonical trait inclusion assumption definition
    pub method_trait_incl_decls: BTreeMap<String, String>,
}

pub type LiteralSpecRef<'def> = &'def LiteralSpec;

impl LiteralSpec {
    /// The name of the Rocq definition for the spec information
    #[must_use]
    fn spec_record(&self) -> String {
        format!("{}_spec", self.name)
    }

    #[must_use]
    fn spec_record_constructor_name(&self) -> String {
        format!("mk_{}_spec", self.name)
    }

    #[must_use]
    pub(crate) fn spec_attrs_record(&self) -> String {
        format!("{}_spec_attrs", self.name)
    }

    #[must_use]
    fn spec_semantic(&self) -> Option<String> {
        self.has_semantic_interp.then(|| format!("{}_semantic_interp", self.name))
    }

    /// The basic specification annotated on the trait definition
    ///
    /// NOTE: Rocq def has self, type parameters, as well as associated types
    #[must_use]
    fn base_spec(&self) -> String {
        format!("{}_base_spec", self.name)
    }

    /// The subsumption relation between specs
    ///
    /// NOTE: Rocq def has no parameters
    #[must_use]
    fn spec_incl_name(&self) -> String {
        format!("{}_spec_incl", self.name)
    }

    #[must_use]
    fn spec_incl_preorder_name(&self) -> String {
        format!("{}_preorder", self.spec_incl_name())
    }

    /// Make the name for the method spec field of the spec record.
    #[must_use]
    pub(crate) fn make_spec_method_name(&self, method: &str) -> String {
        format!("{}_{}_spec", self.name, method)
    }

    #[must_use]
    pub fn make_spec_attr_name(&self, attr: &str) -> String {
        format!("{}_{}", self.name, attr)
    }

    #[must_use]
    fn make_spec_attr_sig_name(&self, attr: &str) -> String {
        format!("{}_{}_sig", self.name, attr)
    }

    #[must_use]
    pub(crate) fn spec_record_attrs_constructor_name(&self) -> String {
        format!("mk_{}", self.spec_attrs_record())
    }
}

/// A reference to a trait instantiated with its parameters in the verification of a function.
#[derive(Clone, Eq, PartialEq, Debug, Constructor)]
#[expect(clippy::partial_pub_fields)]
pub struct LiteralSpecUse<'def> {
    pub trait_ref: LiteralSpecRef<'def>,

    /// scope to quantify over HRTB requirements
    pub scope: ReqScope,

    /// the instantiation of the trait's scope
    pub trait_inst: GenericScopeInst<'def>,

    /// optionally, an override for the trait attr specification we assume
    pub overridden_attrs: Option<String>,

    /// the name including the generic args
    pub mangled_base: String,

    /// whether this is a usage in the scope of a trait decl of the same trait
    pub is_used_in_self_trait: bool,

    /// optional constraints for each associated type
    pub assoc_ty_constraints: Vec<Option<Type<'def>>>,

    /// origin of this trait assumption
    origin: TyParamOrigin,
}

/// As trait uses may reference other trait uses, we put them below optional `RefCell`s,
/// in order to allow cycles during construction.
pub type LiteralSpecUseCell<'def> = RefCell<Option<LiteralSpecUse<'def>>>;
pub type LiteralSpecUseRef<'def> = &'def LiteralSpecUseCell<'def>;

impl ReqInfo for LiteralSpecUseRef<'_> {
    /// Get the associated types we need to quantify over.
    fn get_assoc_ty_params(&self) -> Vec<LiteralTyParam> {
        let b = self.borrow();
        let b = b.as_ref().unwrap();
        b.get_assoc_ty_params()
    }

    fn get_origin(&self) -> TyParamOrigin {
        let b = self.borrow();
        let b = b.as_ref().unwrap();
        b.origin
    }

    fn set_origin(&mut self, origin: TyParamOrigin) {
        let mut b = self.borrow_mut();
        let b = b.as_mut().unwrap();
        b.origin = origin;
    }
}

impl<'def> LiteralSpecUse<'def> {
    fn get_assoc_ty_params(&self) -> Vec<LiteralTyParam> {
        let mut assoc_tys = Vec::new();

        for (idx, _) in self.trait_ref.assoc_tys.iter().enumerate() {
            if self.assoc_ty_constraints[idx].is_none() {
                assoc_tys.push(self.make_assoc_type_lit(idx));
            }
        }
        assoc_tys
    }

    /// Get the name for a spec parameter for this trait instance.
    #[must_use]
    fn make_spec_param_name(&self) -> String {
        format!("{}_spec", self.mangled_base)
    }

    /// Get the name for a spec attrs parameter for this trait instance.
    #[must_use]
    fn make_spec_attrs_param_name(&self) -> String {
        format!("{}_spec_attrs", self.mangled_base)
    }

    /// Get the term for the spec attrs of this use.
    #[must_use]
    pub(crate) fn make_spec_attrs_use(&self) -> String {
        self.overridden_attrs.clone().unwrap_or_else(|| self.make_spec_attrs_param_name())
    }

    /// Get the term for accessing a particular attribute in a context where the attribute record
    /// is quantified.
    #[must_use]
    pub fn make_attr_item_term_in_spec(&self, attr_name: &str) -> coq::term::Term {
        coq::term::Term::RecordProj(
            // Note: we are not using `make_spec_attrs_use`, as we want to specifically refer to
            // the quantified parameter.
            Box::new(coq::term::Term::Literal(self.make_spec_attrs_param_name())),
            self.trait_ref.make_spec_attr_name(attr_name),
        )
    }

    /// Get the instantiation of associated types.
    #[must_use]
    pub fn get_assoc_ty_inst(&self) -> Vec<Type<'def>> {
        let mut assoc_tys = Vec::new();
        for (idx, _) in self.trait_ref.assoc_tys.iter().enumerate() {
            let ty = self.make_assoc_type_use(idx);
            assoc_tys.push(ty.clone());
        }
        assoc_tys
    }

    /// Get the instantiation of the trait spec's parameters, in the same order as
    /// `get_ordered_params`.
    #[must_use]
    fn get_ordered_params_inst(&self) -> Vec<Type<'def>> {
        let mut params = self.trait_inst.get_direct_ty_params().to_vec();
        params.append(&mut self.get_assoc_ty_inst());
        params.append(&mut self.trait_inst.get_direct_assoc_ty_params());

        params
    }

    /// Get the binder for the attribute parameter.
    #[must_use]
    pub(crate) fn get_attr_param(&self) -> coq::binder::Binder {
        let ordered_params = self.get_ordered_params_inst();
        let all_args: Vec<_> = ordered_params.iter().map(Type::get_rfn_type).collect();

        // also attrs of trait deps
        let mut attr_args = Vec::new();
        if self.trait_ref.attrs_dependent {
            for x in self.trait_inst.get_direct_trait_requirements() {
                attr_args.push(x.get_attr_term());
            }
        }

        let mut attr_param_ty = format!("{} (RRGS:=RRGS) ", self.trait_ref.spec_attrs_record());
        push_str_list!(attr_param_ty, &all_args, " ");
        attr_param_ty.push(' ');
        push_str_list!(attr_param_ty, &attr_args, " ");

        // add the attributes
        coq::binder::Binder::new(
            Some(self.make_spec_attrs_param_name()),
            coq::term::Type::Literal(attr_param_ty),
        )
    }

    /// Get the binder for the spec record parameter.
    #[must_use]
    pub(crate) fn get_spec_param(&self) -> coq::binder::Binder {
        let ordered_params = self.get_ordered_params_inst();
        let all_args: Vec<_> = ordered_params.iter().map(Type::get_rfn_type).collect();

        let mut spec_param_ty = format!(
            "spec_with {} [] ({} (RRGS:=RRGS) ",
            self.scope.quantified_lfts.len(),
            self.trait_ref.spec_record()
        );
        push_str_list!(spec_param_ty, &all_args, " ");
        spec_param_ty.push(')');

        coq::binder::Binder::new(Some(self.make_spec_param_name()), coq::term::Type::Literal(spec_param_ty))
    }

    /// Get the optional specialized semantic term for this trait assumption.
    #[must_use]
    pub fn make_semantic_spec_term(&self) -> Option<String> {
        if let Some(semantic_def) = &self.trait_ref.spec_semantic() {
            let inst = &self.trait_inst;
            let args = inst.get_all_ty_params_with_assocs();

            let mut specialized_semantic = format!("{} ", semantic_def.to_owned());
            push_str_list!(specialized_semantic, &args, " ", |x| { format!("{}", x.get_rfn_type()) });
            specialized_semantic.push(' ');
            push_str_list!(specialized_semantic, &args, " ", |x| { x.to_string() });
            Some(specialized_semantic)
        } else {
            None
        }
    }

    /// Make the precondition on the spec parameter we need to require.
    #[must_use]
    pub(crate) fn make_spec_param_precond(&self) -> coq::term::Term {
        // the spec we have to require for this verification
        let spec_to_require = self.trait_ref.base_spec();

        let all_args = self.get_ordered_params_inst();

        let mut specialized_spec = String::new();
        specialized_spec.push_str(&format!("({} {} ", self.scope, spec_to_require));
        // specialize to rts
        push_str_list!(specialized_spec, &all_args, " ", |x| { format!("{}", x.get_rfn_type()) });
        // specialize to sts
        specialized_spec.push(' ');
        push_str_list!(specialized_spec, &all_args, " ", |x| { format!("{}", lang::SynType::from(x)) });

        // specialize to further args
        for req in self.trait_inst.get_direct_trait_requirements() {
            // get attrs + spec term
            specialized_spec.push_str(&format!(" {}", req.get_attr_term()));
            //specialized_spec.push_str(&format!(" {}", req.get_spec_term()));
        }
        specialized_spec.push_str(&format!(" {}", self.make_spec_attrs_use()));

        // specialize to semtys
        push_str_list!(specialized_spec, &all_args, " ", |x| { format!("<TY> {}", x) });
        // specialize to lfts
        push_str_list!(specialized_spec, self.trait_inst.get_lfts(), " ", |x| { format!("<LFT> {}", x) });
        specialized_spec.push_str(" <INST!>)");

        let spec = format!(
            "trait_incl_marker (lift_trait_incl {} {} {specialized_spec})",
            self.trait_ref.spec_incl_name(),
            self.make_spec_param_name(),
        );

        coq::term::Term::Literal(spec)
    }

    /// Make the name for the location parameter of a use of a method of this trait parameter.
    #[must_use]
    pub fn make_loc_name(&self, mangled_method_name: &str) -> String {
        format!("{}_{}_loc", self.mangled_base, mangled_method_name)
    }

    /// Make the names for the Coq-level parameters for an associated type of this instance.
    /// Warning: If you are making a using occurrence, use `make_assoc_type_use` instead.
    #[must_use]
    fn make_assoc_type_lit(&self, idx: usize) -> LiteralTyParam {
        let name = &self.trait_ref.assoc_tys[idx];
        let rust_name = if self.is_used_in_self_trait {
            name.to_owned()
        } else {
            format!("{}_{}", self.mangled_base, name)
        };
        LiteralTyParam::new_with_origin(&rust_name, self.origin)
    }

    /// Make a using occurrence of a particular associated type.
    #[must_use]
    pub fn make_assoc_type_use(&self, idx: usize) -> Type<'def> {
        if let Some(cstr) = self.assoc_ty_constraints.get(idx).unwrap_or(&None) {
            cstr.to_owned()
        } else {
            Type::LiteralParam(self.make_assoc_type_lit(idx))
        }
    }
}

/// A scope of quantifiers for HRTBs on trait requirements.
#[derive(Clone, Eq, PartialEq, Debug, Constructor)]
pub struct ReqScope {
    pub quantified_lfts: Vec<super::LftParam>,
}

impl ReqScope {
    #[must_use]
    pub const fn empty() -> Self {
        Self {
            quantified_lfts: vec![],
        }
    }

    #[must_use]
    pub fn identity_instantiation(&self) -> ReqScopeInst {
        ReqScopeInst::new(self.quantified_lfts.iter().map(|x| x.lft().to_owned()).collect())
    }
}

impl<T: ReqInfo> From<ReqScope> for GenericScope<'_, T> {
    fn from(scope: ReqScope) -> Self {
        let mut generic_scope: GenericScope<'_, T> = GenericScope::empty();
        for lft in scope.quantified_lfts {
            generic_scope.add_lft_param(lft);
        }
        generic_scope
    }
}
impl fmt::Display for ReqScope {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // just a special case of `GenericScope`
        let scope: GenericScope<'_, LiteralSpecUseRef<'_>> = self.clone().into();
        write!(f, "{scope}")
    }
}

/// An instantiation for a `ReqScope`.
#[derive(Clone, Eq, PartialEq, Debug, Constructor)]
pub struct ReqScopeInst {
    pub lft_insts: Vec<Lft>,
}

impl fmt::Display for ReqScopeInst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_list!(f, &self.lft_insts, "", |x| format!(" <LFT> {x}"))
    }
}

/// Instantiation of a trait requirement by specializing an impl.
#[derive(Clone, Eq, PartialEq, Debug, Constructor)]
pub struct SpecializedImpl<'def> {
    pub(crate) impl_ref: LiteralImplRef<'def>,
    pub(crate) impl_inst: GenericScopeInst<'def>,
}

impl SpecializedImpl<'_> {
    #[must_use]
    fn get_spec_term(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("{} ", self.impl_ref.spec_record()));

        // specialize to rts
        push_str_list!(out, self.impl_inst.get_direct_ty_params_with_assocs(), " ", |x| {
            format!("{}", x.get_rfn_type())
        });
        // specialize to sts
        out.push(' ');
        push_str_list!(out, self.impl_inst.get_direct_ty_params_with_assocs(), " ", |x| {
            format!("{}", lang::SynType::from(x))
        });

        // add trait requirements
        for req in self.impl_inst.get_direct_trait_requirements() {
            // get attrs
            out.push_str(&format!(" {}", req.get_attr_term()));
        }

        // specialize to semtys
        push_str_list!(out, self.impl_inst.get_direct_ty_params_with_assocs(), " ", |x| {
            format!("<TY> {}", x)
        });
        // specialize to lfts
        push_str_list!(out, self.impl_inst.get_lfts(), " ", |x| { format!("<LFT> {}", x) });
        out.push_str(" <INST!>");

        out
    }
}

/// Instantiation of a trait requirement by instantiating with (a specialization of) a quantified
/// trait requirement.
#[derive(Clone, Eq, PartialEq, Debug, Constructor)]
pub struct QuantifiedImpl<'def> {
    pub(crate) trait_ref: LiteralSpecUseRef<'def>,

    /// instantiation of the HRTB requirements this trait use is generic over
    scope_inst: ReqScopeInst,
}

impl QuantifiedImpl<'_> {
    #[must_use]
    pub(crate) fn get_spec_term(&self) -> String {
        let mut out = String::new();
        let spec = self.trait_ref.borrow();
        let spec = spec.as_ref().unwrap();
        out.push_str(&spec.make_spec_param_name());
        // instantiate
        out.push_str(&self.scope_inst.to_string());
        out.push_str(" <INST!>");

        out
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum ReqInstSpec<'def> {
    /// A specialized trait impl (i.e., an instantiated declaration)
    Specialized(SpecializedImpl<'def>),
    /// A quantified trait impl (i.e., introduced by a `where` clause)
    Quantified(QuantifiedImpl<'def>),
}

/// Instantiation of a trait requirement.
/// The representation of the associated type instantiation is generic.
#[derive(Clone, Eq, PartialEq, Debug, Constructor)]
pub struct ReqInst<'def, T = Type<'def>> {
    /// the spec instantiation for this requirement
    pub spec: ReqInstSpec<'def>,
    /// the origin of the trait requirement
    pub origin: TyParamOrigin,
    /// instantiation of associated types, excluding the associated types which are already
    /// determined by constraints between associated types at the declaration site of this
    /// requirement
    pub assoc_ty_inst: Vec<T>,

    pub of_trait: LiteralSpecRef<'def>,

    /// The scope to quantify over for this instantiation.
    /// This is non-empty if the trait requirement we are fulfilling is higher-ranked,
    /// i.e., it quantifies over some lifetimes (`for<'a> ...`), HRTBs.
    pub scope: ReqScope,
}

impl<T> ReqInst<'_, T> {
    #[must_use]
    pub(crate) const fn get_origin(&self) -> TyParamOrigin {
        self.origin
    }

    #[must_use]
    pub(crate) fn get_assoc_ty_inst(&self) -> &[T] {
        &self.assoc_ty_inst
    }

    #[must_use]
    pub(crate) fn get_spec_term(&self) -> String {
        let mut out = String::new();
        out.push('(');
        out.push_str(&self.scope.to_string());
        out.push(' ');
        match &self.spec {
            ReqInstSpec::Specialized(s) => {
                out.push_str(&s.get_spec_term());
            },
            ReqInstSpec::Quantified(s) => {
                out.push_str(&s.get_spec_term());
            },
        }
        out.push(')');
        out
    }

    #[must_use]
    pub fn get_attr_term(&self) -> String {
        match &self.spec {
            ReqInstSpec::Specialized(s) => {
                // instantiate the attrs suitably
                let mut args = Vec::new();
                for ty in s.impl_inst.get_direct_ty_params_with_assocs() {
                    args.push(format!("{}", ty.get_rfn_type()));
                }
                // get the attr terms this depends on
                for req in s.impl_inst.get_direct_trait_requirements() {
                    args.push(req.get_attr_term());
                }

                let attr_term = format!("{}", coq::term::App::new(s.impl_ref.spec_attrs_record(), args));
                attr_term
            },
            ReqInstSpec::Quantified(s) => {
                let s = s.trait_ref.borrow();
                let s = s.as_ref().unwrap();
                s.make_spec_attrs_use()
            },
        }
    }
}

impl<'def> ReqInst<'def, Type<'def>> {
    pub(crate) fn new_as_identity(req: LiteralSpecUseRef<'def>) -> Self {
        let trait_use = req.borrow();
        let trait_use = trait_use.as_ref().unwrap();

        // We will just re-quantify over the HRTBs, i.e., the instantiation is still generic in them.
        let hrtb_scope = &trait_use.scope;
        let hrtb_scope_inst = hrtb_scope.identity_instantiation();

        let spec = ReqInstSpec::Quantified(QuantifiedImpl {
            trait_ref: req,
            scope_inst: hrtb_scope_inst,
        });

        let assoc_ty_inst = trait_use.get_assoc_ty_params().into_iter().map(Type::LiteralParam).collect();

        Self::new(spec, trait_use.origin, assoc_ty_inst, trait_use.trait_ref, hrtb_scope.to_owned())
    }
}

/// Info about a trait requirement.
pub trait ReqInfo {
    fn get_assoc_ty_params(&self) -> Vec<LiteralTyParam>;
    fn get_origin(&self) -> TyParamOrigin;
    fn set_origin(&mut self, origin: TyParamOrigin);
}

/// Generate the record instances for a trait impl.
/// - `scope` quantifies the generics of this instance
/// - `assoc_types` has the associated types of this trait that we quantify over in the spec record decl (for
///   the declaration of the base instance)
/// - `params_inst` is the instantiation of the trait's type parameters, including its associated types and
///   its dependencies
/// - `spec` is the specification of all the functions
/// - `of_trait` gives the trait of which we make an instance
/// - `is_base_spec` should be true if this is the base instance of the trait
/// - `spec_record_name` is the name of the record decl
fn make_trait_instance<'def>(
    scope: &GenericScope<'def, LiteralSpecUseRef<'def>>,
    assoc_types: &[LiteralTyParam],
    param_inst: &[Type<'def>],
    spec: &InstanceSpec<'def>,
    of_trait: LiteralSpecRef<'def>,
    is_base_spec: bool,
    spec_record_name: &str,
    mut extra_context_items: coq::binder::BinderList,
    extra_let_binders: Vec<(String, coq::term::Term)>,
) -> Result<coq::Document, fmt::Error> {
    let mut document = coq::Document::default();

    // there should be no surrounding params, as this is the scope of a top-level `impl`
    assert!(scope.surrounding_tys.params.is_empty());
    assert!(scope.surrounding_trait_requirements.is_empty());

    let ty_params = scope.get_direct_ty_params();
    let assoc_params = scope.get_direct_assoc_ty_params();

    // Get all parameters
    // The assoc_types for the Self trait should come before other associated types
    let mut def_params = Vec::new();
    // all rts
    for param in ty_params.params.iter().chain(assoc_types).chain(assoc_params.params.iter()) {
        let rt_param = coq::binder::Binder::new(Some(param.refinement_type()), coq::term::Type::RT);
        def_params.push(rt_param);
    }
    // all sts
    for param in ty_params.params.iter().chain(assoc_types).chain(assoc_params.params.iter()) {
        let rt_param = coq::binder::Binder::new(Some(param.syn_type()), model::Type::SynType);
        def_params.push(rt_param);
    }

    let param_inst_rts: Vec<_> = param_inst.iter().map(Type::get_rfn_type).collect();

    // also quantify over all trait deps
    let mut trait_params = scope.get_all_attr_trait_parameters(IncludeSelfReq::Dont);
    def_params.append(&mut trait_params.0);

    // for the base spec, we quantify over the attrs
    // Otherwise, we do not have to quantify over the attrs, as we fix one particular attrs record for
    // concrete impls.
    if is_base_spec {
        // assemble the type
        // TODO: for trait deps, also instantiate with deps?
        let mut attrs_params: Vec<_> =
            param_inst_rts.iter().map(|x| coq::term::Term::Type(Box::new(x.to_owned()))).collect();

        if of_trait.attrs_dependent {
            attrs_params
                .append(&mut scope.get_all_attr_trait_parameters(IncludeSelfReq::Dont).make_using_terms());
        }
        let attrs_type = coq::term::App::new(of_trait.spec_attrs_record(), attrs_params);
        let attrs_type = coq::term::Type::Literal(format!("{attrs_type}"));
        def_params.push(coq::binder::Binder::new(Some("_ATTRS".to_owned()), attrs_type));
    }

    def_params.append(&mut extra_context_items.0);

    let def_params = coq::binder::BinderList::new(def_params);

    // for this, we assume that the semantic type parameters are all in scope
    let body_term = if spec.methods.is_empty() {
        // special-case this, as we cannot use record constructor syntax for empty records
        // implicitly inst rrgs
        let t = coq::term::App::new(
            format!("@{} _ _", of_trait.spec_record_constructor_name()),
            param_inst_rts.clone(),
        );
        coq::term::Term::Literal(t.to_string())
    } else {
        let mut components = Vec::new();

        // order doesn't matter for Coq records
        for (item_name, spec) in &spec.methods {
            let record_item_name = of_trait.make_spec_method_name(item_name);

            let direct_scope = spec.get_direct_scope();
            let direct_params = direct_scope.get_direct_ty_params_with_assocs();
            let direct_trait_params = direct_scope.get_direct_attr_trait_parameters(IncludeSelfReq::Dont);

            // now just need to generalize over the surrounding scope inst.
            // maybe compute a "surrounding_scope_inst" of the fn spec term
            let surrounding_inst = spec.surrounding_scope_instantiation(scope);

            let self_assoc_inst = spec.self_assoc_types_inst(assoc_types);

            // get the param uses for rt + st for all params, including the params of the impl/trait
            //let mut params = scope.get_direct_ty_params_with_assocs();
            let mut params = surrounding_inst.get_direct_ty_params_with_assocs();
            params.append(&mut self_assoc_inst.clone());
            params
                .append(&mut direct_params.params.iter().map(|x| Type::LiteralParam(x.to_owned())).collect());

            let mut param_uses = Vec::new();
            for x in &params {
                let rt = x.get_rfn_type();
                param_uses.push(coq::term::Term::Literal(rt.to_string()));
            }
            for x in params {
                let st: lang::SynType = x.into();
                param_uses.push(coq::term::Term::Literal(st.to_string()));
            }

            let mut body = String::with_capacity(100);

            // first instantiate with all rt + st
            let app_body = coq::term::App::new(spec.get_spec_name().to_owned(), param_uses);
            write!(body, "{app_body}")?;

            // instantiate with surrounding trait specs
            for x in surrounding_inst.get_direct_trait_requirements() {
                write!(body, " {}", x.get_attr_term())?;
            }

            // This comes after other surrounding trait requirement's attrs, as the Self requirement is always
            // shuffled last
            if is_base_spec {
                write!(body, " _ATTRS")?;
            } else if let Some(inst) = spec.self_trait_attr_inst() {
                write!(body, " {inst}")?;
            }

            let trait_params = direct_trait_params.make_using_terms();
            write!(body, " {}", fmt_list!(trait_params, " "))?;

            write!(body, "\n")?;

            // instantiate with the scope's types
            write!(body, "{}", surrounding_inst.instantiation(false, false))?;
            // The associated types of this trait always come last.
            for x in &self_assoc_inst {
                write!(body, " <TY> {}", x)?;
            }
            // we leave the direct type parameters and associated types of the function uninstantiated

            // provide type annotation
            trace!("computing local lifetimes for {record_item_name}: {:?}", direct_scope.lfts);
            let num_direct_lifetimes = direct_scope.get_num_direct_lifetimes();
            write!(body, " : (spec_with {num_direct_lifetimes} [")?;
            write_list!(body, &direct_params.params, "; ", LiteralTyParam::refinement_type)?;

            write!(body, "] fn_spec)")?;

            // get the direct parameters (rt + st) of this function.
            // We quantify over these at the record item level.
            let mut direct_params = direct_params.get_coq_ty_params();
            // also quantify over direct trait requirements
            direct_params.append(direct_trait_params.0);

            let item = coq::term::RecordBodyItem {
                name: record_item_name,
                params: direct_params,
                term: coq::term::Term::Literal(body),
            };
            components.push(item);
        }
        let record_body = coq::term::RecordBody { items: components };
        let mut term = coq::term::Term::RecordBody(record_body);

        for (name, bind_term) in extra_let_binders {
            term = coq::term::Term::LetIn(name, Box::new(bind_term), Box::new(term));
        }
        term
    };
    // add the surrounding quantifiers over the semantic types
    let mut term_with_specs = String::with_capacity(100);
    scope.format(&mut term_with_specs, false, assoc_types)?;
    write!(term_with_specs, " {body_term}")?;

    let mut ty_annot = String::with_capacity(100);
    let spec_record_type = coq::term::App::new(of_trait.spec_record(), param_inst_rts);
    write!(ty_annot, "spec_with _ _ {}", spec_record_type)?;

    document.push(coq::command::Definition {
        program_mode: false,
        name: spec_record_name.to_owned(),
        params: def_params,
        ty: Some(coq::term::Type::Literal(ty_annot)),
        body: coq::command::DefinitionBody::Term(coq::term::Term::Literal(term_with_specs)),
    });

    Ok(document)
}

/// This bundles all components of a trait in a trait declaration.
#[derive(Constructor, Clone, Debug)]
#[expect(clippy::partial_pub_fields)]
pub struct SpecDecl<'def> {
    /// A reference to all the Coq definition names we should generate.
    pub lit: LiteralSpecRef<'def>,

    /// The generics this trait uses
    generics: GenericScope<'def, LiteralSpecUseRef<'def>>,

    /// associated types
    assoc_types: Vec<LiteralTyParam>,

    /// The default specification from the trait declaration
    default_spec: InstanceSpec<'def>,

    /// the spec attributes
    attrs: SpecAttrsDecl,
}

impl SpecDecl<'_> {
    // Get the ordered parameters that definitions of the trait are parametric over
    fn get_ordered_params(&self) -> TyParamList {
        let mut params = self.generics.get_direct_ty_params().to_owned();
        params.append(self.assoc_types.clone());
        params.append(self.generics.get_direct_assoc_ty_params().params);
        params
    }

    #[must_use]
    pub fn make_attr_record_decl(&self) -> coq::Document {
        let Some(attrs) = self.attrs.attrs.as_ref() else {
            return coq::Document::default();
        };

        // this is parametric in the params and associated types
        let ordered_params = self.get_ordered_params();
        let mut params = ordered_params.get_coq_ty_rt_params();

        if self.lit.attrs_dependent {
            // also depend on other attrs
            params.append(self.generics.get_all_attr_trait_parameters(IncludeSelfReq::Dont).0);
        }

        params.0.insert(0, coq::binder::Binder::new_rrgs());

        // the individual fields depend on each other, progressively
        let mut field_params = params.clone();

        // we first generate definitions for the type signature of each attribute
        let mut sig_decls: Vec<coq::Sentence> = Vec::new();

        // write attr record
        let mut record_items = Vec::new();
        for (item_name, item_ty) in attrs {
            let record_item_name = self.lit.make_spec_attr_name(item_name);
            let record_item_sig_name = self.lit.make_spec_attr_sig_name(item_name);

            let sig_defn = coq::command::Definition {
                program_mode: false,
                name: record_item_sig_name.clone(),
                params: field_params.clone(),
                ty: None,
                body: coq::command::DefinitionBody::Term(coq::term::RocqTerm::Type(Box::new(
                    item_ty.to_owned(),
                ))),
            };
            sig_decls.push(sig_defn.into());

            let record_item_ty = coq::term::App::new(
                coq::term::Term::Ident(coq::Ident::new(&record_item_sig_name)),
                field_params.make_using_terms(),
            );
            let ty = coq::term::RocqType::Term(Box::new(coq::term::Term::App(Box::new(record_item_ty))));

            // add a new field binder for the next fields
            let field_binder = coq::binder::Binder::new(Some(record_item_name.clone()), ty.clone());
            field_params.0.push(field_binder);

            let item = coq::term::RecordDeclItem {
                name: record_item_name,
                params: coq::binder::BinderList::empty(),
                ty,
            };
            record_items.push(item);
        }

        params.make_implicit(coq::binder::Kind::MaxImplicit);

        let record_decl = coq::term::Record {
            name: self.lit.spec_attrs_record(),
            params,
            ty: coq::term::Type::Type,
            constructor: Some(self.lit.spec_record_attrs_constructor_name()),
            body: record_items,
        };
        sig_decls.push(record_decl.into());

        sig_decls.push(
            coq::command::CommandAttrs::new(coq::command::Arguments {
                name: self.lit.spec_attrs_record(),
                arguments_string: ": clear implicits".to_owned(),
            })
            .attributes("global")
            .into(),
        );
        sig_decls.push(
            coq::command::CommandAttrs::new(coq::command::Arguments {
                name: self.lit.spec_attrs_record(),
                arguments_string: "{_ _}".to_owned(),
            })
            .attributes("global")
            .into(),
        );

        let mut attrs_string = String::new();
        // first two are for refinedrustGS, then all the RT + st parameters, then attrs for trait deps
        let attr_param_count = 2
            + self.get_ordered_params().params.len()
            + (if self.lit.attrs_dependent {
                self.generics.get_direct_trait_requirements().len()
            } else {
                0
            });
        for _ in 0..attr_param_count {
            write!(attrs_string, " {{_}}").unwrap();
        }
        sig_decls.push(
            coq::command::CommandAttrs::new(coq::command::Arguments {
                name: self.lit.spec_record_attrs_constructor_name(),
                arguments_string: attrs_string,
            })
            .attributes("global")
            .into(),
        );

        coq::Document::new(sig_decls)
    }

    /// Make the definition for the semantic declaration.
    #[must_use]
    pub fn make_semantic_decl(&self) -> Option<coq::command::Command> {
        if let Some(semantic_interp) = &self.attrs.semantic_interp {
            let def_name = self.lit.spec_semantic().unwrap();

            let ordered_params = self.get_ordered_params();
            let mut params = ordered_params.get_coq_ty_rt_params();
            params.0.insert(0, coq::binder::Binder::new_rrgs());
            params.append(ordered_params.get_semantic_ty_params().0);

            let body = semantic_interp.to_owned();

            Some(coq::command::Command::Definition(coq::command::Definition {
                program_mode: false,
                name: def_name,
                params,
                ty: Some(coq::term::Type::Prop),
                body: coq::command::DefinitionBody::Term(coq::term::Term::Literal(body)),
            }))
        } else {
            None
        }
    }

    /// Make the spec record declaration.
    #[must_use]
    pub fn make_spec_record_decl(&self) -> coq::Document {
        let mut record_items = Vec::new();
        for (item_name, item_spec) in &self.default_spec.methods {
            let record_item_name = self.lit.make_spec_method_name(item_name);

            let direct_scope = item_spec.get_direct_scope();

            // get number of lifetime parameters of the function
            let num_lifetimes = direct_scope.get_num_lifetimes();

            let rt_param_uses =
                direct_scope.get_direct_ty_params_with_assocs().get_coq_ty_rt_params().make_using_terms();
            let mut ty_term = String::with_capacity(100);
            ty_term.push_str(&format!("spec_with {num_lifetimes} ["));
            push_str_list!(ty_term, &rt_param_uses, "; ");
            ty_term.push_str("] fn_spec");

            // params are the rt and st of the direct type parameters
            let mut params = direct_scope.get_direct_ty_params_with_assocs().get_coq_ty_params();
            // also quantify over the trait specs etc.
            let trait_params = direct_scope.get_direct_attr_trait_parameters(IncludeSelfReq::Dont);
            params.append(trait_params.0);

            let item = coq::term::RecordDeclItem {
                name: record_item_name,
                params,
                ty: coq::term::Type::Literal(ty_term),
            };
            record_items.push(item);
        }

        // this is parametric in the params and associated types
        let ordered_params = self.get_ordered_params();
        let mut params = ordered_params.get_coq_ty_rt_params();
        params.make_implicit(coq::binder::Kind::MaxImplicit);
        params.0.insert(0, coq::binder::Binder::new_rrgs());

        let record = coq::term::Record {
            name: self.lit.spec_record(),
            params,
            ty: coq::term::Type::Type,
            constructor: Some(self.lit.spec_record_constructor_name()),
            body: record_items,
        };
        let mut decls: Vec<coq::Sentence> = vec![record.into()];

        // clear the implicit argument
        decls.push(
            coq::command::CommandAttrs::new(coq::command::Arguments {
                name: self.lit.spec_record(),
                arguments_string: ": clear implicits".to_owned(),
            })
            .attributes("global")
            .into(),
        );

        // make rrgs implicit again
        decls.push(
            coq::command::CommandAttrs::new(coq::command::Arguments {
                name: self.lit.spec_record(),
                arguments_string: "{_ _}".to_owned(),
            })
            .attributes("global")
            .into(),
        );

        coq::Document::new(decls)
    }

    fn make_spec_incl_preorder(&self) -> coq::command::Instance {
        let name = self.lit.spec_incl_preorder_name();

        let spec_params = self.get_ordered_params();
        let spec_rt_params = spec_params.get_coq_ty_rt_params();
        let spec_rt_inst_terms = spec_rt_params.make_implicit_inst_terms();

        // the spec incl relation first takes the rt params
        let mut spec_incl_params = spec_rt_params;
        spec_incl_params.make_implicit(coq::binder::Kind::MaxImplicit);

        let ty = format!("PreOrder ({} {})", self.lit.spec_incl_name(), fmt_list!(spec_rt_inst_terms, " "));

        let body = coq::proof::Proof::new(coq::proof::Terminator::Qed, |doc| {
            doc.push(coq::ltac::Attrs::new(coq::ltac::RocqLTac::Split));
            doc.push(
                coq::ltac::Attrs::new(coq::ltac::RocqLTac::Apply(coq::term::Term::Type(Box::new(
                    coq::term::RocqType::Infer,
                ))))
                .scope(coq::ltac::Scope::All),
            );
        });

        coq::command::Instance {
            name: Some(name),
            params: spec_incl_params,
            ty: coq::term::Type::Literal(ty),
            body,
        }
    }

    fn make_spec_incl_decl(&self) -> coq::command::Definition {
        let spec_incl_name = self.lit.spec_incl_name();
        let spec_param_name1 = "spec1".to_owned();
        let spec_param_name2 = "spec2".to_owned();

        let spec_params = self.get_ordered_params();
        let spec_rt_params = spec_params.get_coq_ty_rt_params();
        let spec_rt_using_terms = spec_rt_params.make_using_terms();

        // the spec incl relation first takes the rt params
        let mut spec_incl_params = spec_rt_params;
        spec_incl_params.make_implicit(coq::binder::Kind::MaxImplicit);

        // compute the type of the two spec params
        let spec_param_type = coq::term::App::new(self.lit.spec_record(), spec_rt_using_terms).to_string();

        // add the two spec params
        spec_incl_params.0.push(coq::binder::Binder::new(
            Some(spec_param_name1.clone()),
            coq::term::Type::Literal(spec_param_type.clone()),
        ));
        spec_incl_params.0.push(coq::binder::Binder::new(
            Some(spec_param_name2.clone()),
            coq::term::Type::Literal(spec_param_type),
        ));

        let mut incls = Vec::new();
        for (name, decl) in &self.default_spec.methods {
            let mut param_decls =
                decl.get_direct_scope().get_direct_ty_params_with_assocs().get_coq_ty_params();
            // also quantify over the trait specs etc.
            let trait_params = decl.get_direct_scope().get_direct_attr_trait_parameters(IncludeSelfReq::Dont);
            param_decls.append(trait_params.0);

            let param_uses = param_decls.make_using_terms();

            let record_item_name = self.lit.make_spec_method_name(name);
            let incl_term = coq::term::Term::All(
                param_decls,
                Box::new(coq::term::Term::App(Box::new(coq::term::App::new(
                    coq::term::Term::Literal("function_subtype".to_owned()),
                    vec![
                        coq::term::Term::App(Box::new(coq::term::App::new(
                            coq::term::Term::RecordProj(
                                Box::new(coq::term::Term::Literal(spec_param_name1.clone())),
                                record_item_name.clone(),
                            ),
                            param_uses.clone(),
                        ))),
                        coq::term::Term::App(Box::new(coq::term::App::new(
                            coq::term::Term::RecordProj(
                                Box::new(coq::term::Term::Literal(spec_param_name2.clone())),
                                record_item_name.clone(),
                            ),
                            param_uses.clone(),
                        ))),
                    ],
                )))),
            );
            incls.push(incl_term);
        }
        let body = coq::term::Term::Infix("∧".to_owned(), incls);

        coq::command::Definition {
            program_mode: false,
            name: spec_incl_name,
            params: spec_incl_params,
            ty: Some(coq::term::Type::Prop),
            body: coq::command::DefinitionBody::Term(body),
        }
    }

    #[must_use]
    pub fn make_trait_req_incls(&self) -> coq::Document {
        let mut decls: Vec<coq::Sentence> = Vec::new();

        // write the trait_req_incls for the functions
        for item_spec in self.default_spec.methods.values() {
            if let InstanceMethodSpec::Defined(spec) = item_spec {
                decls.append(&mut spec.generate_trait_req_incl_def().0);
            } else {
                unreachable!();
            }
        }

        let sec = coq::section::Section::new(format!("{}_trait_req_incls", self.lit.name), |pdoc| {
            pdoc.push(coq::command::Context::refinedrust());
            pdoc.append(&mut decls);
        });

        coq::Document::new(vec![coq::command::Command::Section(sec)])
    }
}

// TODO: Deprecated: Generate a coq::Document instead.
impl fmt::Display for SpecDecl<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Section {}.\n", self.lit.name)?;

        write!(f, "Context `{{RRGS : !refinedrustGS Σ}}.\n")?;

        // write spec incl relation
        let spec_incl_def = self.make_spec_incl_decl();
        write!(f, "{spec_incl_def}\n")?;

        // prove that it is a preorder
        let spec_incl_preorder = self.make_spec_incl_preorder();
        write!(f, "{spec_incl_preorder}\n")?;

        // write the individual function specs
        for item_spec in self.default_spec.methods.values() {
            if let InstanceMethodSpec::Defined(spec) = item_spec {
                write!(f, "{spec}\n")?;
            } else {
                unreachable!();
            }
        }

        // use the identity instantiation of the trait
        let param_inst = self.get_ordered_params();
        let param_inst: Vec<_> = param_inst.params.into_iter().map(Type::LiteralParam).collect();

        // write the bundled records
        let base_decls = make_trait_instance(
            &self.generics,
            &self.assoc_types,
            &param_inst,
            &self.default_spec,
            self.lit,
            true,
            &self.lit.base_spec(),
            coq::binder::BinderList::empty(),
            vec![],
        )?;
        write!(f, "{base_decls}\n")?;

        write!(f, "End {}.\n", self.lit.name)
    }
}

/// Rocq names used for the specification of a trait impl.
#[derive(Clone, Eq, PartialEq, Debug, Constructor)]
pub struct LiteralImpl {
    /// The Rocq name of the specification
    name: String,

    /// Whether is there a Rocq definition name for the trait's semantic interpretation.
    has_semantic_interp: bool,
}

pub type LiteralImplRef<'def> = &'def LiteralImpl;

impl LiteralImpl {
    /// The Rocq name of the specification record instance
    #[must_use]
    pub fn spec_record(&self) -> String {
        format!("{}_spec", self.name)
    }

    /// The Rocq name of the specification attributes record instance
    #[must_use]
    pub fn spec_attrs_record(&self) -> String {
        format!("{}_spec_attrs", self.name)
    }

    /// The optional Rocq definition name for the trait's semantic interpretation
    #[must_use]
    pub fn spec_semantic(&self) -> Option<String> {
        self.has_semantic_interp.then(|| format!("{}_semantic_interp", self.name))
    }

    /// The Rocq lemma name of the proof that the base spec is implied by the more specific spec
    #[must_use]
    pub fn spec_subsumption_proof(&self) -> String {
        format!("{}_spec_subsumption_correct", self.name)
    }

    /// The Rocq name of the definition for the lemma statement
    #[must_use]
    pub fn spec_subsumption_statement(&self) -> String {
        format!("{}_spec_subsumption", self.name)
    }
}

/// A full instantiation of a trait spec, e.g. for an impl of a trait,
/// which may itself be generic in a `GenericScope`.
#[derive(Constructor, Clone, Debug)]
#[expect(clippy::partial_pub_fields)]
pub struct RefInst<'def> {
    /// literals of the trait this implements
    pub of_trait: LiteralSpecRef<'def>,
    /// the literals for the impl
    pub impl_ref: LiteralImplRef<'def>,

    /// generic scope for this impl, with trait requirements
    generics: GenericScope<'def, LiteralSpecUseRef<'def>>,

    /// instantiation of the trait's scope
    /// Invariant: no surrounding instantiation
    trait_inst: GenericScopeInst<'def>,

    /// the implementation of the associated types
    assoc_types_inst: Vec<Type<'def>>,

    /// the spec attribute instantiation
    attrs: SpecAttrsInst,
}

impl<'def> RefInst<'def> {
    /// Get the instantiation of the trait's parameters in the same order as the trait's declaration
    /// (`get_ordered_params`).
    #[must_use]
    fn get_ordered_params_inst(&self) -> Vec<Type<'def>> {
        let mut params: Vec<_> = self
            .trait_inst
            .get_direct_ty_params()
            .iter()
            .chain(self.assoc_types_inst.iter())
            .cloned()
            .collect();

        params.append(&mut self.trait_inst.get_direct_assoc_ty_params());

        params
    }

    /// Get the term for referring to the attr record of this impl
    /// The parameters are expected to be in scope.
    #[must_use]
    fn get_attr_record_term(&self) -> coq::term::App<coq::term::Term, coq::term::Term> {
        let attr_record = &self.impl_ref.spec_attrs_record();

        // get all type parameters
        let mut binders = self.generics.get_all_ty_params_with_assocs().get_coq_ty_rt_params();
        // add all dependent attrs
        binders.append(self.generics.get_all_attr_trait_parameters(IncludeSelfReq::Dont).0);
        let args = binders.make_using_terms();

        coq::term::App::new(coq::term::Term::Literal(attr_record.to_owned()), args)
    }

    /// Get the term for referring to the spec record of this impl
    /// The parameters are expected to be in scope.
    #[must_use]
    fn get_spec_record_term(&self) -> coq::term::Term {
        let spec_record = &self.impl_ref.spec_record();

        // specialize to all type parameters
        let tys = self.generics.get_all_ty_params_with_assocs();
        let mut binders = tys.get_coq_ty_params();
        // specialize to all attribute records
        binders.append(self.generics.get_all_attr_trait_parameters(IncludeSelfReq::Dont).0);
        let args = binders.make_using_terms();

        let mut specialized_spec = coq::term::App::new(spec_record.to_owned(), args).to_string();

        // specialize to semtys
        specialized_spec.push_str(&self.generics.identity_instantiation_term());

        coq::term::Term::Literal(specialized_spec)
        //coq::term::Term::App(Box::new(coq::term::App::new(coq::term::Term::Literal(spec_record.
        // to_owned()), args)))
    }

    #[must_use]
    fn get_base_spec_term(&self) -> coq::term::Term {
        let spec_record = &self.of_trait.base_spec();

        let all_args = self.get_ordered_params_inst();

        let mut specialized_spec = String::new();
        specialized_spec.push_str(&format!("({spec_record} "));
        // specialize to rts
        push_str_list!(specialized_spec, &all_args, " ", |x| { format!("{}", x.get_rfn_type()) });
        // specialize to sts
        specialized_spec.push(' ');
        push_str_list!(specialized_spec, &all_args, " ", |x| { format!("{}", lang::SynType::from(x)) });

        // specialize to further args:
        // first the dependent attrs
        for req in self.trait_inst.get_direct_trait_requirements() {
            // get attrs
            specialized_spec.push_str(&format!(" {}", req.get_attr_term()));
        }
        // then the attrs of this impl
        specialized_spec.push_str(&format!(" {}", self.get_attr_record_term()));

        // specialize to semtys
        push_str_list!(specialized_spec, &all_args, " ", |x| { format!("<TY> {}", x) });
        // specialize to lfts
        push_str_list!(specialized_spec, self.trait_inst.get_lfts(), " ", |x| { format!("<LFT> {}", x) });
        specialized_spec.push_str(" <INST!>)");

        coq::term::Term::Literal(specialized_spec)
    }

    /// Get the term for referring to an item of the attr record of this impl.
    /// The parameters are expected to be in scope.
    #[must_use]
    pub fn get_attr_record_item_term(&self, attr: &str) -> coq::term::Term {
        let item_name = self.of_trait.make_spec_attr_name(attr);
        coq::term::Term::RecordProj(Box::new(Box::new(self.get_attr_record_term()).into()), item_name)
    }
}

/// The bundled specification of a trait impl.
#[derive(Constructor, Clone, Debug)]
pub struct ImplSpec<'def> {
    /// the instantiation of the trait
    pub trait_ref: RefInst<'def>,

    /// the name of the Coq def of the method definitions and all type parameters they need
    pub methods: InstanceSpec<'def>,

    /// extra coq binders
    pub extra_context_items: coq::binder::BinderList,
}

impl ImplSpec<'_> {
    /// Generate the definition of the attribute record of this trait impl.
    #[must_use]
    pub fn generate_attr_decl(&self) -> coq::Document {
        let attrs = &self.trait_ref.attrs;
        let attrs_name = &self.trait_ref.impl_ref.spec_attrs_record();
        let of_trait = &self.trait_ref.of_trait;

        let mut def_rts_params = self.extra_context_items.clone();
        def_rts_params.0.insert(0, coq::binder::Binder::new_rrgs());

        // get all type parameters + assoc types
        def_rts_params
            .append(self.trait_ref.generics.get_all_ty_params_with_assocs().get_coq_ty_rt_params().0);

        // add other attrs
        def_rts_params.append(self.trait_ref.generics.get_all_attr_trait_parameters(IncludeSelfReq::Dont).0);

        // instantiate the type of the attr record
        let attrs_type_rts: Vec<coq::term::Type> =
            self.trait_ref.get_ordered_params_inst().iter().map(Type::get_rfn_type).collect();
        let mut attrs_type_terms: Vec<_> =
            attrs_type_rts.iter().map(|x| coq::term::Term::Type(Box::new(x.to_owned()))).collect();

        // also add dependent attrs
        if self.trait_ref.of_trait.attrs_dependent {
            for x in self.trait_ref.trait_inst.get_direct_trait_requirements() {
                attrs_type_terms.push(coq::term::Term::Literal(x.get_attr_term()));
            }
        }
        let mut obligation_terms = Vec::new();

        let attrs_type = coq::term::App::new(of_trait.spec_attrs_record(), attrs_type_terms.clone());
        let attrs_type = coq::term::Type::Literal(format!("{attrs_type}"));

        // write the attr record decl
        let attr_record_term = if attrs.attrs.is_empty() {
            coq::term::Term::Literal(of_trait.spec_record_attrs_constructor_name())
        } else {
            let mut components = Vec::new();
            for (attr_name, inst) in &attrs.attrs {
                // create an item for every attr
                let record_item_name = of_trait.make_spec_attr_name(attr_name);

                let item_ty = coq::term::App::new(
                    coq::term::Term::Ident(coq::Ident::new(&of_trait.make_spec_attr_sig_name(attr_name))),
                    attrs_type_terms.clone(),
                );

                // add a placeholder for the dependency of the next attrs
                attrs_type_terms.push(coq::term::RocqTerm::Infer);

                let inst_term = match inst {
                    SpecAttrInst::Term(term) => term.to_owned(),
                    SpecAttrInst::Proof(proof) => {
                        let lit = coq::ltac::RocqLTac::Literal(proof.to_owned());
                        let proof = coq::ProofDocument::new(vec![lit]);
                        obligation_terms.push(coq::command::Command::NextObligation(
                            coq::command::ObligationProof {
                                content: proof,
                                terminator: coq::proof::Terminator::Qed,
                            },
                        ));
                        coq::term::Term::Infer
                    },
                };

                let annot_term = coq::term::Term::AsType(
                    Box::new(inst_term),
                    Box::new(coq::term::Type::Term(Box::new(coq::term::Term::App(Box::new(item_ty))))),
                );

                let item = coq::term::RecordBodyItem {
                    name: record_item_name,
                    params: coq::binder::BinderList::empty(),
                    term: annot_term,
                };
                components.push(item);
            }
            let record_body = coq::term::RecordBody { items: components };
            coq::term::Term::RecordBody(record_body)
        };

        let def = coq::command::Definition {
            program_mode: true,
            name: attrs_name.to_owned(),
            params: def_rts_params,
            ty: Some(attrs_type),
            body: coq::command::DefinitionBody::Term(attr_record_term),
        };
        obligation_terms.insert(0, coq::command::Command::Definition(def));
        coq::Document::new(obligation_terms)
    }

    /// Make the definition for the semantic declaration.
    fn make_semantic_decl(&self) -> Option<coq::Document> {
        if let Some(def_name) = &self.trait_ref.impl_ref.spec_semantic() {
            let base_name = self.trait_ref.of_trait.spec_semantic().unwrap();

            let generics = &self.trait_ref.generics;

            // build params
            let all_tys = generics.get_all_ty_params_with_assocs();
            let mut params = all_tys.get_coq_ty_rt_params();
            params.append(all_tys.get_semantic_ty_params().0);

            params.append(self.extra_context_items.0.clone());

            // add semantic assumptions for all trait requirements
            for x in generics
                .get_surrounding_trait_requirements()
                .iter()
                .chain(generics.get_direct_trait_requirements().iter())
            {
                let y = x.borrow();
                let x = y.as_ref().unwrap();
                if let Some(term) = x.make_semantic_spec_term() {
                    params.0.push(coq::binder::Binder::new(None, coq::term::Type::Literal(term)));
                }
            }

            let trait_inst = &self.trait_ref.trait_inst;
            let inst_args = trait_inst.get_all_ty_params_with_assocs();

            // type
            let mut specialized_semantic = format!("{} ", base_name);
            push_str_list!(specialized_semantic, &inst_args, " ", |x| { format!("{}", x.get_rfn_type()) });
            specialized_semantic.push(' ');
            push_str_list!(specialized_semantic, &inst_args, " ", |x| { x.to_string() });

            let body = coq::proof::Proof::new(coq::proof::Terminator::Qed, |doc| {
                let vernac: coq::Vernac =
                    coq::ltac::LTac::Literal(format!("unfold {base_name} in *; apply _")).into();
                doc.push(vernac);
            });
            let commands = vec![
                coq::command::Command::Lemma(coq::command::Lemma {
                    name: def_name.to_owned(),
                    params,
                    ty: coq::term::Type::Literal(specialized_semantic),
                    body,
                })
                .into(),
            ];

            Some(coq::Document(commands))
        } else {
            None
        }
    }

    #[must_use]
    fn generate_lemma_statement(&self) -> coq::Document {
        let mut doc = coq::Document::default();

        let spec_name = &self.trait_ref.impl_ref.spec_subsumption_statement();

        // generate the lemma statement
        // get parameters
        // this is parametric in the rts, sts, semtys, attrs of all trait deps.
        let ty_params = self.trait_ref.generics.get_all_ty_params_with_assocs();
        let mut params = self.extra_context_items.clone();
        params.append(ty_params.get_coq_ty_params().0);
        params.append(self.trait_ref.generics.get_all_attr_trait_parameters(IncludeSelfReq::Dont).0);

        // instantiation of the trait
        let incl_name = self.trait_ref.of_trait.spec_incl_name();
        let own_spec = self.trait_ref.get_spec_record_term();
        let base_spec = self.trait_ref.get_base_spec_term();

        let scope = &self.trait_ref.generics;
        let mut ty_term = format!("trait_incl_marker (lift_trait_incl {incl_name} (");
        scope.format(&mut ty_term, false, &[]).unwrap();
        ty_term.push_str(&format!(" {own_spec}) ("));
        scope.format(&mut ty_term, false, &[]).unwrap();
        ty_term.push_str(&format!(" {base_spec}))"));

        let body = coq::term::Term::Literal(ty_term);

        // don't want implicit generalizing binders here
        params.make_implicit(coq::binder::Kind::Explicit);
        let body = coq::term::Term::All(params, Box::new(body));

        let lem = coq::command::Definition {
            program_mode: false,
            name: spec_name.to_owned(),
            params: coq::binder::BinderList::empty(),
            ty: None,
            body: coq::command::DefinitionBody::Term(body),
        };
        doc.push(coq::command::Command::Definition(lem));

        doc
    }

    #[must_use]
    pub fn generate_proof(&self) -> coq::Document {
        let mut doc = coq::Document::default();

        let lemma_name = &self.trait_ref.impl_ref.spec_subsumption_proof();

        doc.push(coq::command::Lemma {
            name: lemma_name.to_owned(),
            params: coq::binder::BinderList::empty(),
            ty: coq::term::Type::Literal(self.trait_ref.impl_ref.spec_subsumption_statement()),
            body: coq::proof::Proof::new(coq::proof::Terminator::Qed, |proof| {
                proof.push(model::LTac::SolveTraitInclPrelude(
                    self.trait_ref.impl_ref.spec_subsumption_statement(),
                ));
                proof.push(model::LTac::RepeatLiRStep.scope(coq::ltac::Scope::All));
                proof.push(model::LTac::PrintRemainingTraitGoal.scope(coq::ltac::Scope::All));
                proof.push(model::LTac::Unshelve);
                proof.push(model::LTac::SidecondSolver.scope(coq::ltac::Scope::All));
                proof.push(model::LTac::Unshelve);
                proof.push(model::LTac::SidecondHammer.scope(coq::ltac::Scope::All));
            }),
        });

        doc
    }
}

impl fmt::Display for ImplSpec<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let section = coq::section::Section::new(self.trait_ref.impl_ref.spec_record(), |section| {
            section.push(coq::command::Context::refinedrust());

            // Instantiate with the parameter and associated types
            let params_inst = self.trait_ref.get_ordered_params_inst();

            // NOTE: HACK because we don't compute the correct direct scope for default fns for now:
            // dependencies on other surrounding params/assocs are not instantiated correctly.
            // Hence we manually introduce the binders necessary here as let binders.
            let mut extra_let_binders = Vec::new();
            for (name, inst) in
                self.trait_ref.of_trait.assoc_tys.iter().zip(self.trait_ref.assoc_types_inst.iter())
            {
                let assoc_param = LiteralTyParam::new(name);
                extra_let_binders.push((
                    assoc_param.refinement_type(),
                    coq::term::Term::Type(Box::new(inst.get_rfn_type())),
                ));
            }

            // This relies on all the impl's functions already having been printed
            let mut instance = make_trait_instance(
                &self.trait_ref.generics,
                &Vec::new(),
                &params_inst,
                &self.methods,
                self.trait_ref.of_trait,
                false,
                &self.trait_ref.impl_ref.spec_record(),
                self.extra_context_items.clone(),
                extra_let_binders,
            )
            .unwrap();

            section.append(&mut instance.0);

            section.append(&mut self.generate_lemma_statement().0);

            if let Some(mut doc) = self.make_semantic_decl() {
                section.append(&mut doc);
            }
        });

        write!(f, "{section}\n")
    }
}

/// Function specification that arises from the instantiation of the default spec of a trait.
/// The surrounding `GenericScope` should have:
/// - the impl's generics
/// - the function's generics, marked as direct
#[derive(Clone, Constructor, Debug)]
pub struct InstantiatedFunctionSpec<'def> {
    /// the trait we are instantiating
    trait_ref: RefInst<'def>,
    /// name of the trait method we are instantiating
    trait_method_name: String,
}

impl<'def> InstantiatedFunctionSpec<'def> {
    pub(crate) fn write_spec_term<F>(
        &self,
        f: &mut F,
        scope: &GenericScope<'def, LiteralSpecUseRef<'def>>,
    ) -> fmt::Result
    where
        F: fmt::Write,
    {
        // write the scope of the impl
        // (this excludes the function's own direct scope, as that is already quantified in the
        // base spec we are going to instantiate)
        //write!(f, "spec!")?;
        self.trait_ref.generics.format(f, false, &[])?;
        //write!(f, ",\n ")?;

        let all_ty_params = self.trait_ref.get_ordered_params_inst();

        // apply the trait's base spec
        let mut params = Vec::new();
        // add rt params
        for ty in &all_ty_params {
            params.push(format!("{}", ty.get_rfn_type()));
        }

        // add syntype params
        for ty in &all_ty_params {
            params.push(format!("{}", lang::SynType::from(ty)));
        }

        // instantiate with the attrs of trait requirements
        for trait_req in self.trait_ref.trait_inst.get_direct_trait_requirements() {
            params.push(trait_req.get_attr_term());
            //params.push(trait_req.get_spec_term());
        }

        // also instantiate with the attrs that are quantified on the outside
        let attr_term = self.trait_ref.get_attr_record_term();
        params.push(attr_term.to_string());

        let mut applied_base_spec = String::with_capacity(100);
        write!(applied_base_spec, "{}\n", coq::term::App::new(&self.trait_ref.of_trait.base_spec(), params))?;

        // now add the semantic components
        // instantiate semantic types
        for ty in &all_ty_params {
            write!(applied_base_spec, " <TY> {ty}")?;
        }
        // instantiate lifetimes
        for lft in self.trait_ref.trait_inst.get_lfts() {
            write!(applied_base_spec, " <LFT> {lft}")?;
        }
        write!(applied_base_spec, " <INST!>")?;

        // now we need to project out the concrete function specification
        // we pass as parameters the direct rts and sts of the function
        // for that, look in the generic scope for direct parameters
        let spec_params = scope.get_direct_ty_params_with_assocs().get_coq_ty_params();
        let spec_params = spec_params.make_using_terms();

        // also instantiate the direct trait requirements of the function, which should be
        // quantified in the same way in the surrounding scope
        let trait_params_inst =
            scope.get_direct_attr_trait_parameters(IncludeSelfReq::Dont).make_using_terms();

        write!(
            f,
            "({applied_base_spec}).({}) {} {} <MERGE!>",
            self.trait_ref.of_trait.make_spec_method_name(&self.trait_method_name),
            fmt_list!(spec_params, " "),
            fmt_list!(trait_params_inst, " ")
        )?;

        Ok(())
    }
}
