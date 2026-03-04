// © 2025, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashSet;
use std::fmt;
use std::fmt::Write as _;

use derive_more::Constructor;
use indent_write::fmt::IndentWriter;

use crate::specs::{GenericScope, GenericScopeInst, IncludeSelfReq, Type, TypeWithRef, traits};
use crate::{BASE_INDENT, coq, push_str_list};

/// A finished inner function specification.
#[derive(Clone, Debug)]
pub enum InnerSpec<'def> {
    /// A specification declared via attributes
    Lit(LiteralSpec<'def>),
    /// Use the default specification of a trait
    TraitDefault(traits::InstantiatedFunctionSpec<'def>),
}

impl<'def> InnerSpec<'def> {
    /// Generate extra definitions needed for the specification.
    fn generate_extra_definitions(
        &self,
        scope: &GenericScope<'def, traits::LiteralSpecUseRef<'def>>,
    ) -> coq::Document {
        match self {
            Self::Lit(lit) => lit.generate_extra_definitions(scope),
            Self::TraitDefault(_) => coq::Document::default(),
        }
    }

    fn write_spec_term<F>(
        &self,
        f: &mut F,
        scope: &GenericScope<'def, traits::LiteralSpecUseRef<'def>>,
    ) -> fmt::Result
    where
        F: fmt::Write,
    {
        match self {
            Self::Lit(lit) => lit.write_spec_term(f, scope),
            Self::TraitDefault(def) => def.write_spec_term(f, scope),
        }
    }

    #[must_use]
    pub(crate) fn get_params(&self) -> Option<&[coq::binder::Binder]> {
        match self {
            Self::Lit(lit) => Some(&lit.params.0),
            Self::TraitDefault(_) => None,
        }
    }
}

/// A Radium function specification.
#[derive(Clone, Debug)]
#[expect(clippy::partial_pub_fields)]
pub struct Spec<'def, T = InnerSpec<'def>> {
    /// The name of the spec
    pub spec_name: String,
    pub function_name: String,

    /// The name of the trait incl definition
    pub trait_req_incl_name: String,

    /// Generics
    pub(crate) generics: GenericScope<'def, traits::LiteralSpecUseRef<'def>>,

    /// Coq-level parameters the typing statement needs
    pub early_coq_params: coq::binder::BinderList,
    pub late_coq_params: coq::binder::BinderList,

    pub(crate) spec: T,
}

impl<'def, T> Spec<'def, T> {
    pub(crate) fn replace_spec<U>(self, new_spec: U) -> Spec<'def, U> {
        Spec {
            spec: new_spec,
            trait_req_incl_name: self.trait_req_incl_name,
            spec_name: self.spec_name,
            function_name: self.function_name,
            generics: self.generics,
            early_coq_params: self.early_coq_params,
            late_coq_params: self.late_coq_params,
        }
    }

    #[must_use]
    pub(crate) fn empty(
        spec_name: String,
        trait_req_incl_name: String,
        function_name: String,
        spec: T,
    ) -> Self {
        Self {
            spec_name,
            trait_req_incl_name,
            function_name,
            generics: GenericScope::empty(),
            early_coq_params: coq::binder::BinderList::empty(),
            late_coq_params: coq::binder::BinderList::empty(),
            spec,
        }
    }

    /// Get the spec's `GenericScope`.
    pub const fn get_generics(&self) -> &GenericScope<'def> {
        &self.generics
    }

    #[must_use]
    pub(crate) fn get_spec_name(&self) -> &str {
        &self.spec_name
    }

    /// Add a coq parameter that comes before type parameters.
    pub(crate) fn add_early_coq_param(&mut self, param: coq::binder::Binder) {
        self.early_coq_params.0.push(param);
    }

    /// Add a coq parameter that comes after type parameters.
    pub(crate) fn add_late_coq_param(&mut self, param: coq::binder::Binder) {
        self.late_coq_params.0.push(param);
    }
}

impl<'def> Spec<'def, InnerSpec<'def>> {
    /// Get all Coq binders for the Coq spec definition.
    #[must_use]
    pub(crate) fn get_all_spec_coq_params(&self) -> coq::binder::BinderList {
        // Important: early parameters should always be first, as they include trait specs.
        // Important: the type parameters should be introduced before late parameters to ensure they are in
        // scope.
        let mut params = self.early_coq_params.clone();

        let typarams = self.generics.get_all_ty_params_with_assocs();
        params.append(typarams.get_coq_ty_params().0);

        params.append(self.late_coq_params.0.clone());

        // finally, the trait spec parameters
        let trait_params = self.generics.get_all_attr_trait_parameters(IncludeSelfReq::Attrs);

        params.append(trait_params.0);

        params
    }

    /// Get all Coq binders for the Coq trait incl definition.
    #[must_use]
    pub(crate) fn get_all_trait_req_coq_params(&self) -> coq::binder::BinderList {
        let mut params = self.early_coq_params.clone();

        let typarams = self.generics.get_all_ty_params_with_assocs();
        params.append(typarams.get_coq_ty_params().0);
        params.append(self.late_coq_params.0.clone());

        // finally, the trait spec parameters
        let trait_params = self.generics.get_all_trait_parameters(IncludeSelfReq::AttrsSpec);

        params.append(trait_params.0);

        params
    }

    /// Get all Coq binders for the Coq lemma definition.
    #[must_use]
    pub(crate) fn get_all_lemma_coq_params(&self, self_req: IncludeSelfReq) -> coq::binder::BinderList {
        // Important: early parameters should always be first, as they include trait specs.
        // Important: the type parameters should be introduced before late parameters to ensure they are in
        // scope.
        let mut params = self.early_coq_params.clone();

        let typarams = self.generics.get_all_ty_params_with_assocs();
        params.append(typarams.get_coq_ty_params().0);

        params.append(self.late_coq_params.0.clone());

        // finally, the trait spec parameters
        let trait_params = self.generics.get_all_trait_parameters(self_req);

        params.append(trait_params.0);

        params
    }

    /// Check whether this spec is complete.
    #[must_use]
    pub const fn is_complete(&self) -> bool {
        match &self.spec {
            InnerSpec::Lit(lit) => lit.has_spec,
            InnerSpec::TraitDefault(_) => true,
        }
    }

    #[must_use]
    pub fn generate_trait_req_incl_def(&self) -> coq::Document {
        // first add the needed extra definitions
        let mut doc = self.spec.generate_extra_definitions(&self.generics);

        let params = self.get_all_trait_req_coq_params();

        let mut late_pre = Vec::new();
        for trait_use in self
            .generics
            .get_surrounding_trait_requirements()
            .iter()
            .chain(self.generics.get_direct_trait_requirements().iter())
        {
            let trait_use = trait_use.borrow();
            let trait_use = trait_use.as_ref().unwrap();
            // TODO?
            //if !trait_use.is_used_in_self_trait {
            let spec_precond = trait_use.make_spec_param_precond();
            late_pre.push(spec_precond);
            //}
        }
        let term = coq::term::Term::Infix("∧".to_owned(), late_pre);

        // quantify over the generic scope
        let mut quantified_term = String::new();
        self.generics.format(&mut quantified_term, false, &[]).unwrap();
        quantified_term.push_str(&format!(" ({term})"));

        let name = self.trait_req_incl_name.clone();
        doc.push(coq::command::Definition {
            program_mode: false,
            name,
            params,
            ty: Some(coq::term::Type::Literal("spec_with _ _ Prop".to_owned())),
            body: coq::command::DefinitionBody::Term(coq::term::Term::Literal(quantified_term)),
        });

        doc
    }
}

// TODO: Deprecated: Generate a coq::Document instead.
impl<'def> fmt::Display for Spec<'def, InnerSpec<'def>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut doc = coq::Document::default();

        let params = self.get_all_spec_coq_params();

        let mut term = String::with_capacity(100);
        self.spec.write_spec_term(&mut term, &self.generics)?;

        let coq_def = coq::command::Definition {
            program_mode: false,
            name: self.spec_name.clone(),
            params,
            ty: None,
            body: coq::command::DefinitionBody::Term(coq::term::Term::Literal(term)),
        };
        doc.push(coq::command::Command::Definition(coq_def));

        write!(f, "{doc}")
    }
}

/// Holds a specialized trait specification that a function assumes.
/// This declares an attribute instantiation in the scope of the function.
// Note: similar to `TraitRefInst`
#[derive(Clone, Constructor, Debug)]
pub struct SpecTraitReqSpecialization<'def> {
    /// literals of the trait this implements
    of_trait: traits::LiteralSpecRef<'def>,

    /// instantiation of the trait's scope
    /// Invariant: no surrounding instantiation
    trait_inst: GenericScopeInst<'def>,

    /// the implementation of the associated types
    assoc_types_inst: Vec<Type<'def>>,

    /// the spec attribute instantiation
    attrs: traits::SpecAttrsInst,

    /// the Rocq definition name for this specialization
    name: String,
}

impl<'def> SpecTraitReqSpecialization<'def> {
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

    /// Generate the definition of the attribute record.
    #[must_use]
    fn generate_attr_decl(
        &self,
        generics: &GenericScope<'def, traits::LiteralSpecUseRef<'def>>,
    ) -> coq::command::Definition {
        let attrs = &self.attrs;
        let of_trait = &self.of_trait;

        // get all type parameters + assoc types
        let mut def_rts_params = generics.get_all_ty_params_with_assocs().get_coq_ty_rt_params();
        def_rts_params.make_implicit(coq::binder::Kind::MaxImplicit);
        def_rts_params.0.insert(0, coq::binder::Binder::new_rrgs());

        // add other attrs
        //def_rts_params.append(generics.get_all_attr_trait_parameters(IncludeSelfReq::Dont).0);

        // instantiate the type of the attrs record
        let mut attrs_type_params: Vec<coq::term::Term> = self
            .get_ordered_params_inst()
            .iter()
            .map(|x| coq::term::Term::Type(Box::new(x.get_rfn_type())))
            .collect();

        if of_trait.attrs_dependent {
            // also attrs
            for x in self.trait_inst.get_direct_trait_requirements() {
                attrs_type_params.push(coq::term::Term::Literal(x.get_attr_term()));
            }
        }

        let attrs_type = coq::term::App::new(of_trait.spec_attrs_record(), attrs_type_params);
        let attrs_type = coq::term::Type::Literal(format!("{attrs_type}"));

        // write the attr record decl
        let attr_record_term = if attrs.attrs.is_empty() {
            coq::term::Term::Literal(of_trait.spec_record_attrs_constructor_name())
        } else {
            let mut components = Vec::new();
            for (attr_name, inst) in &attrs.attrs {
                // create an item for every attr
                let record_item_name = of_trait.make_spec_attr_name(attr_name);

                let traits::SpecAttrInst::Term(term) = inst else {
                    unimplemented!("trait req specialization should not assume proofs");
                };

                let item = coq::term::RecordBodyItem {
                    name: record_item_name,
                    params: coq::binder::BinderList::empty(),
                    term: term.to_owned(),
                };
                components.push(item);
            }
            let record_body = coq::term::RecordBody { items: components };
            coq::term::Term::RecordBody(record_body)
        };

        coq::command::Definition {
            name: self.name.clone(),
            params: def_rts_params,
            ty: Some(attrs_type),
            body: coq::command::DefinitionBody::Term(attr_record_term),
            program_mode: false,
        }
    }
}

/// A function specification below generics.
#[derive(Clone, Debug)]
pub struct LiteralSpec<'def> {
    params: coq::binder::BinderList,

    // extra elctx constraints added via unsafe annotations
    extra_elctx: Vec<String>,

    /// precondition as a separating conjunction
    pre: coq::iris::IProp,
    /// argument types including refinements
    args: Vec<TypeWithRef<'def>>,
    /// existential quantifiers for the postcondition
    existentials: coq::binder::BinderList,
    /// return type
    ret: TypeWithRef<'def>,
    /// postcondition as a separating conjunction
    post: coq::iris::IProp,

    /// specialized attributes of traits
    specialized_trait_attrs: Vec<SpecTraitReqSpecialization<'def>>,

    // TODO remove
    has_spec: bool,
}

impl<'def> LiteralSpec<'def> {
    /// Generate extra definitions needed for the specification.
    fn generate_extra_definitions(
        &self,
        scope: &GenericScope<'def, traits::LiteralSpecUseRef<'def>>,
    ) -> coq::Document {
        let mut doc = coq::Document::default();
        for spec in &self.specialized_trait_attrs {
            let def = spec.generate_attr_decl(scope);
            doc.push(coq::Sentence::CommandAttrs(coq::command::CommandAttrs::new(def)));
        }

        doc
    }

    /// Format the external lifetime contexts, consisting of constraints between lifetimes.
    fn format_elctx(&self, scope: &GenericScope<'def, traits::LiteralSpecUseRef<'def>>) -> String {
        let mut out = scope.format_elctx();

        // extra constraints
        if !self.extra_elctx.is_empty() {
            out.push_str(" ++ ");
            push_str_list!(out, &self.extra_elctx, " ++ ");
        }

        out
    }

    fn format_args(&self) -> String {
        let mut out = String::with_capacity(100);

        push_str_list!(out, &self.args, ", ");

        out
    }

    /// Write the core spec term. Assumes that the coq parameters for the type parameters (as given by
    /// `get_coq_ty_params`) are in scope.
    fn write_spec_term<F>(
        &self,
        f: &mut F,
        scope: &GenericScope<'def, traits::LiteralSpecUseRef<'def>>,
    ) -> Result<(), fmt::Error>
    where
        F: fmt::Write,
    {
        /* fn(∀ [lft_pat] : [lft_count] | | [param_pat] : [param_type]; [elctx]; [args]; [pre]; [trait_reqs])
               → ∃ [exist_pat] : [exist_type], [ret_type]; [post]
        */
        let mut f2 = IndentWriter::new_skip_initial(BASE_INDENT, &mut *f);

        // introduce generics
        write!(f2, "fn(∀ ")?;
        scope.format(&mut f2, true, &[])?;
        write!(f2, " | \n")?;

        // introduce parameters
        let param = self.params.uncurry();
        write!(f2, "(* params....... *) {} : {},\n", param.0, param.1)?;

        // elctx
        write!(f2, "(* elctx........ *) ({});\n", self.format_elctx(scope).as_str())?;

        // args
        if !self.args.is_empty() {
            write!(f2, "(* args......... *) {};\n", self.format_args().as_str())?;
        }

        // precondition
        let mut f3 = IndentWriter::new_skip_initial(BASE_INDENT, &mut f2);
        write!(f3, "(* precondition. *) (λ π : thread_id, {}) |\n", self.pre)?;

        // late precondition with trait requirements
        let mut late_pre = Vec::new();
        for trait_use in scope
            .get_surrounding_trait_requirements()
            .iter()
            .chain(scope.get_direct_trait_requirements().iter())
        {
            let trait_use = trait_use.borrow();
            let trait_use = trait_use.as_ref().unwrap();
            if !trait_use.is_used_in_self_trait
                && let Some(spec_precond) = trait_use.make_semantic_spec_term()
            {
                //let spec_precond = trait_use.make_spec_param_precond();
                late_pre.push(coq::iris::IProp::Pure(Box::new(coq::term::Term::Literal(spec_precond))));
            }
        }
        let mut f3 = IndentWriter::new_skip_initial(BASE_INDENT, &mut f2);
        write!(f3, "(* trait reqs... *) (λ π : thread_id, {})) →\n", coq::iris::IProp::Sep(late_pre))?;

        // existential + post
        let existential = self.existentials.uncurry();
        write!(
            f2,
            "(* existential.. *) ∃ {} : {}, {} @ {};\n",
            existential.0, existential.1, self.ret.1, self.ret.0
        )?;
        write!(f2, "(* postcondition *) (λ π : thread_id, {})", self.post)?;

        Ok(())
    }
}

#[derive(Debug)]
pub struct LiteralSpecBuilder<'def> {
    params: Vec<coq::binder::Binder>,

    extra_elctx: Vec<String>,

    pre: coq::iris::IProp,
    args: Vec<TypeWithRef<'def>>,
    existential: Vec<coq::binder::Binder>,
    ret: Option<TypeWithRef<'def>>,
    post: coq::iris::IProp,

    coq_names: HashSet<String>,

    specialized_trait_attrs: Vec<SpecTraitReqSpecialization<'def>>,

    /// true iff there are any annotations
    has_spec: bool,
}

impl<'def> LiteralSpecBuilder<'def> {
    #[must_use]
    pub fn new() -> Self {
        Self {
            params: Vec::new(),
            extra_elctx: Vec::new(),
            pre: coq::iris::IProp::Sep(Vec::new()),
            args: Vec::new(),
            existential: Vec::new(),
            ret: None,
            post: coq::iris::IProp::Sep(Vec::new()),
            coq_names: HashSet::new(),
            specialized_trait_attrs: Vec::new(),
            has_spec: false,
        }
    }

    #[expect(clippy::ref_option)]
    fn push_coq_name(&mut self, name: &Option<String>) {
        if let Some(name) = &name {
            self.coq_names.insert(name.to_owned());
        }
    }

    /// Adds a (universally-quantified) parameter with a given Coq name for the spec.
    pub fn add_param(&mut self, binder: coq::binder::Binder) -> Result<(), String> {
        self.ensure_coq_not_bound(binder.get_name_ref())?;
        self.push_coq_name(binder.get_name_ref());
        self.params.push(binder);
        Ok(())
    }

    #[expect(clippy::ref_option)]
    fn ensure_coq_not_bound(&self, name: &Option<String>) -> Result<(), String> {
        if let Some(name) = &name
            && self.coq_names.contains(name)
        {
            return Err(format!("Coq name is already bound: {}", name));
        }

        Ok(())
    }

    /// Provide specialized specification attributes for trait requirements.
    pub fn provide_specialized_trait_attrs(&mut self, specs: Vec<SpecTraitReqSpecialization<'def>>) {
        self.specialized_trait_attrs = specs;
    }

    /// Add a literal elctx.
    pub fn add_literal_lifetime_constraint(&mut self, elctx: String) {
        self.extra_elctx.push(elctx);
    }

    /// Add a new function argument.
    pub fn add_arg(&mut self, arg: TypeWithRef<'def>) {
        self.args.push(arg);
    }

    /// Add a new (separating) conjunct to the function's precondition.
    pub fn add_precondition(&mut self, pre: coq::iris::IProp) {
        assert!(matches!(self.pre, coq::iris::IProp::Sep(_)));

        let coq::iris::IProp::Sep(v) = &mut self.pre else {
            unreachable!("An incorrect parameter has been given");
        };

        v.push(pre);
    }

    /// Add a new (separating) conjunct to the function's postcondition.
    pub fn add_postcondition(&mut self, post: coq::iris::IProp) {
        assert!(matches!(self.post, coq::iris::IProp::Sep(_)));

        let coq::iris::IProp::Sep(v) = &mut self.post else {
            unreachable!("An incorrect parameter has been given");
        };

        v.push(post);
    }

    /// Set the return type of the function
    pub fn set_ret_type(&mut self, ret: TypeWithRef<'def>) -> Result<(), String> {
        if self.ret.is_some() {
            return Err("Re-definition of return type".to_owned());
        }
        self.ret = Some(ret);
        Ok(())
    }

    /// Add an existentially-quantified variable to the postcondition.
    pub fn add_existential(&mut self, binder: coq::binder::Binder) -> Result<(), String> {
        self.ensure_coq_not_bound(binder.get_name_ref())?;
        self.existential.push(binder);
        // TODO: if we add some kind of name analysis to postcondition, we need to handle the
        // existential
        Ok(())
    }

    /// Add the information that attributes have been provided for this function.
    pub const fn have_spec(&mut self) {
        self.has_spec = true;
    }

    /// Check whether a valid specification has been added.
    #[must_use]
    pub const fn has_spec(&self) -> bool {
        self.has_spec
    }

    /// Generate an actual function spec.
    pub(crate) fn into_function_spec(self) -> LiteralSpec<'def> {
        LiteralSpec {
            params: coq::binder::BinderList::new(self.params),
            extra_elctx: self.extra_elctx,
            pre: self.pre,
            args: self.args,
            existentials: coq::binder::BinderList::new(self.existential),
            ret: self.ret.unwrap_or_else(TypeWithRef::make_unit),
            post: self.post,
            specialized_trait_attrs: self.specialized_trait_attrs,
            has_spec: self.has_spec,
        }
    }
}
