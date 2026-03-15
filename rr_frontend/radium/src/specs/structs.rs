// © 2025, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::cell::RefCell;
use std::fmt;
use std::fmt::Write as _;

use crate::specs::{
    GenericScope, GenericScopeInst, LiteralTyParam, Type, format_extra_context_items, invariants, traits,
    types,
};
use crate::{coq, fmt_list, lang, model, push_str_list};

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum TypeIsRaw {
    Yes,
    No,
}

/// Representation options for structs.
///
/// Struct representation options supported by Radium
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Repr {
    Rust,
    C,
    Transparent,
}

impl fmt::Display for Repr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Rust => write!(f, "StructReprRust"),
            Self::C => write!(f, "StructReprC"),
            Self::Transparent => write!(f, "StructReprTransparent"),
        }
    }
}

/// Description of a variant of a struct or enum.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct AbstractVariant<'def> {
    /// the fields, closed under a surrounding scope
    fields: Vec<(String, Type<'def>)>,
    /// the struct representation mode
    repr: Repr,
    /// the struct's name
    name: String,
    /// the Coq def name for the struct's plain tydef alias (without the optional invariant wrapper)
    pub(crate) plain_ty_name: String,
    /// the Coq def name for the struct's layout spec definition (of type `struct_layout_spec`)
    sls_def_name: String,
    st_def_name: String,
    /// the Coq def name for the struct's refinement type
    /// (used for using occurrences, but not for the definition itself)
    pub(crate) plain_rt_def_name: String,
}

impl<'def> AbstractVariant<'def> {
    /// Get the name of this variant
    #[must_use]
    fn name(&self) -> &str {
        &self.name
    }

    fn rfn_type(&self) -> coq::term::Type {
        model::Type::PList(
            "place_rfnRT".to_owned(),
            self.fields.iter().map(|(_, t)| t.get_rfn_type()).collect(),
            "RT".to_owned(),
        )
        .into()
    }

    /// The core of generating the sls definition, without the section + context intro.
    /// `opt_enum_name` is the optional name of a surrounding enum, to make recursive references working.
    #[must_use]
    pub(crate) fn generate_coq_sls_def_core(
        &self,
        typarams: &coq::binder::BinderList,
        opt_enum_name: Option<&str>,
    ) -> String {
        let mut out = String::with_capacity(200);
        let indent = "  ";

        // intro to main def
        write!(out, "{indent}Definition {} {typarams} : struct_layout_spec :=\n", self.sls_def_name).unwrap();

        // for recursive uses
        write!(out, "{indent}{indent}let {} {typarams} := UnitSynType in\n", self.st_def_name).unwrap();
        if let Some(enum_name) = opt_enum_name {
            write!(out, "{indent}{indent}let {enum_name} {typarams} := UnitSynType in\n").unwrap();
        }

        write!(out, "{indent}{indent}mk_sls \"{}\" [", self.name).unwrap();

        push_str_list!(out, &self.fields, ";", |(name, ty)| {
            let synty: lang::SynType = ty.into();

            format!("\n{indent}{indent}(\"{name}\", {synty})")
        });

        write!(out, "] {}.\n", self.repr).unwrap();

        // also generate a definition for the syntype
        write!(
            out,
            "{indent}Definition {} {typarams} : syn_type := {} {}.\n",
            self.st_def_name,
            self.sls_def_name.clone(),
            fmt_list!(typarams.make_using_terms(), " "),
        )
        .unwrap();

        out
    }

    /// Generate a Coq definition for the struct layout spec.
    #[must_use]
    fn generate_coq_sls_def(&self, scope: &GenericScope<'def>) -> String {
        let mut out = String::with_capacity(200);

        let indent = "  ";
        write!(out, "Section {}.\n", self.sls_def_name).unwrap();
        write!(out, "{}Context `{{RRGS : !refinedrustGS Σ}}.\n", indent).unwrap();

        // add syntype parameters
        let typarams = scope.get_all_ty_params_with_assocs().get_coq_ty_st_params();
        out.push('\n');

        write!(out, "{}", self.generate_coq_sls_def_core(&typarams, None)).unwrap();

        // finish
        write!(out, "End {}.\n", self.sls_def_name).unwrap();
        out
    }

    #[must_use]
    #[deprecated(note = "Use `get_coq_type_term` instead")]
    fn generate_coq_type_term(&self, sls_app: Vec<String>) -> String {
        let mut out = String::with_capacity(200);

        out.push_str(&format!("struct_t {} +[", coq::term::App::new(&self.sls_def_name, sls_app)));
        push_str_list!(out, &self.fields, ";", |(_, ty)| ty.to_string());
        out.push(']');

        out
    }

    #[must_use]
    fn get_coq_type_term(&self, sls_app: Vec<coq::term::Term>) -> coq::term::Type {
        let sls = coq::term::App::new(coq::term::Term::Literal(self.sls_def_name.clone()), sls_app);

        let tys = self.fields.iter().map(|(_, ty)| coq::term::Type::Literal(ty.to_string())).collect();

        model::Type::StructT(Box::new(sls).into(), tys).into()
    }

    #[must_use]
    pub(crate) fn generate_coq_type_def_core(
        &self,
        ty_params: &GenericScope<'def>,
        ty_context_names: &[String],
        rt_context_names: &[String],
    ) -> coq::Document {
        let mut document = coq::Document::default();

        let all_ty_params = ty_params.get_all_ty_params_with_assocs();

        // Generate terms to apply the sls app to
        let sls_app: Vec<_> = all_ty_params
            .params
            .iter()
            .map(|names| {
                coq::term::Term::App(Box::new(coq::term::App::new(
                    coq::term::Term::RecordProj(
                        Box::new(coq::term::Term::Literal(names.type_term())),
                        "ty_syn_type".to_owned(),
                    ),
                    vec![coq::term::Term::Literal("MetaNone".to_owned())],
                )))
            })
            .collect();

        // Intro to main def
        document.push(coq::command::Definition {
            program_mode: false,
            name: self.plain_ty_name.clone(),
            params: coq::binder::BinderList::empty(),
            ty: Some(
                ty_params
                    .get_spec_all_type_term(Box::new(model::Type::Ttype(Box::new(self.rfn_type()))).into()),
            ),
            body: coq::command::DefinitionBody::Proof(coq::proof::Proof::new_using(
                ty_context_names.join(" "),
                coq::proof::Terminator::Defined,
                |proof| {
                    proof.push(coq::ltac::LTac::Exact(coq::term::Term::App(Box::new(coq::term::App::new(
                        // TODO: `ty_params` must create a specific Coq object.
                        coq::term::Term::Literal(ty_params.to_string()),
                        vec![coq::term::Term::Literal(self.get_coq_type_term(sls_app).to_string())],
                    )))));
                },
            )),
        });

        // Generate the refinement type definition
        let rt_params = all_ty_params.get_coq_ty_rt_params();
        let using =
            format!("{} {}", fmt_list!(rt_params.make_using_terms(), " "), rt_context_names.join(" "));

        document.push(coq::command::Definition {
            program_mode: false,
            name: self.plain_rt_def_name.clone(),
            params: coq::binder::BinderList::empty(),
            ty: Some(coq::term::Type::RT),
            body: coq::command::DefinitionBody::Proof(coq::proof::Proof::new_using(
                using,
                coq::proof::Terminator::Defined,
                |proof| {
                    proof.push(coq::ltac::LetIn::new(
                        "__a",
                        coq::term::App::new(
                            coq::term::Term::Literal("normalized_rt_of_spec_ty".to_owned()),
                            vec![coq::term::Term::Literal(self.plain_ty_name.clone())],
                        ),
                        coq::ltac::LTac::Exact(coq::term::Term::Literal("__a".to_owned())),
                    ));
                },
            )),
        });

        // Make it Typeclasses Transparent
        let typeclasses_ty = coq::command::Command::TypeclassesTransparent(self.plain_ty_name.clone());
        let typeclasses_rt = coq::command::Command::TypeclassesTransparent(self.plain_rt_def_name.clone());

        document.push(coq::command::CommandAttrs::new(typeclasses_ty).attributes("global"));
        document.push(coq::command::CommandAttrs::new(typeclasses_rt).attributes("global"));

        document
    }

    /// Generate a Coq definition for the struct type alias.
    /// TODO: maybe we should also generate a separate alias def for the refinement type to make
    /// things more readable?
    #[must_use]
    fn generate_coq_type_def(
        &self,
        scope: &GenericScope<'def>,
        extra_context: &[coq::binder::Binder],
    ) -> String {
        let mut out = String::with_capacity(200);
        let indent = "  ";
        // the write_str impl will always return Ok.
        write!(out, "Section {}.\n", self.plain_ty_name).unwrap();
        write!(out, "{}Context `{{RRGS : !refinedrustGS Σ}}.\n", indent).unwrap();

        let all_ty_params = scope.get_all_ty_params_with_assocs();

        // add type parameters, and build a list of terms to apply the sls def to
        if !all_ty_params.params.is_empty() {
            // first push the (implicit) refinement type parameters
            write!(out, "{}Context", indent).unwrap();
            for names in &all_ty_params.params {
                write!(out, " ({} : RT)", names.refinement_type()).unwrap();
            }
            out.push_str(".\n");
        }
        out.push('\n');

        // write coq parameters
        let (context_names, context_names_without_sigma) =
            format_extra_context_items(extra_context, &mut out).unwrap();

        write!(
            out,
            "{}",
            self.generate_coq_type_def_core(scope, &context_names, &context_names_without_sigma)
        )
        .unwrap();

        write!(out, "End {}.\n", self.plain_ty_name).unwrap();
        write!(out, "Global Arguments {} : clear implicits.\n", self.plain_rt_def_name).unwrap();
        if !context_names_without_sigma.is_empty() {
            //let dep_sigma_str = if dep_sigma { "{_} " } else { "" };
            let dep_sigma_str = "";

            write!(
                out,
                "Global Arguments {} {}{} {{{}}}.\n",
                self.plain_rt_def_name,
                dep_sigma_str,
                "_ ".repeat(all_ty_params.params.len()),
                "_ ".repeat(context_names_without_sigma.len())
            )
            .unwrap();
        }
        out
    }
}

/// Description of a struct type.
// TODO: mechanisms for resolving mutually recursive types.
#[derive(Clone, Eq, PartialEq)]
pub struct Abstract<'def> {
    /// an optional invariant/ existential abstraction for this struct
    pub(crate) invariant: Option<invariants::Spec>,

    /// the actual definition of the variant
    pub(crate) variant_def: AbstractVariant<'def>,

    /// scope this is generic over
    pub(crate) scope: GenericScope<'def>,

    /// true iff this is recursive
    is_recursive: bool,
}

impl fmt::Debug for Abstract<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "AbstractStruct<name={}>", self.variant_def.name)
    }
}

pub type AbstractRef<'def> = &'def RefCell<Option<Abstract<'def>>>;

impl<'def> Abstract<'def> {
    #[must_use]
    pub const fn new(variant_def: AbstractVariant<'def>, scope: GenericScope<'def>) -> Self {
        Abstract {
            invariant: None,
            variant_def,
            scope,
            is_recursive: false,
        }
    }

    /// Create a struct representation of a tuple with `num_fields`, all of which are generic.
    #[must_use]
    pub fn new_from_tuple(num_fields: usize) -> Self {
        let name = format!("tuple{}", num_fields);

        let mut scope = GenericScope::empty();
        let mut builder = VariantBuilder::new(name, Repr::Rust);

        for i in 0..num_fields {
            let param_name = format!("T{}", i);
            let lit = LiteralTyParam::new(&param_name);
            scope.add_ty_param(lit.clone());

            builder.add_field(&i.to_string(), Type::LiteralParam(lit));
        }

        builder.finish_as_struct(scope)
    }

    /// Register that this type is recursive.
    pub const fn set_is_recursive(&mut self) {
        self.is_recursive = true;
    }

    /// Check if an invariant has been declared on this type.
    #[must_use]
    pub const fn has_invariant(&self) -> bool {
        self.invariant.is_some()
    }

    /// Check if this type has `#[rr::mode(atomic)]`.
    #[must_use]
    pub fn is_atomic(&self) -> bool {
        self.invariant.as_ref().is_some_and(invariants::Spec::is_atomic)
    }

    /// Get the name of this struct
    #[must_use]
    fn name(&self) -> &str {
        self.variant_def.name()
    }

    #[must_use]
    fn sls_def_name(&self) -> &str {
        &self.variant_def.sls_def_name
    }

    #[must_use]
    pub(crate) fn st_def_name(&self) -> &str {
        &self.variant_def.st_def_name
    }

    #[must_use]
    pub(crate) fn plain_ty_name(&self) -> &str {
        &self.variant_def.plain_ty_name
    }

    /// Get the name of the struct, or an ADT defined on it, if available.
    #[must_use]
    pub(crate) fn public_type_name(&self) -> String {
        match &self.invariant {
            Some(inv) => inv.type_name(),
            None => self.plain_ty_name().to_owned(),
        }
    }

    #[must_use]
    pub fn plain_rt_def_name(&self) -> &str {
        &self.variant_def.plain_rt_def_name
    }

    #[must_use]
    pub(crate) fn public_rt_def_name(&self) -> String {
        match &self.invariant {
            Some(inv) => inv.rt_def_name(),
            None => self.plain_rt_def_name().to_owned(),
        }
    }

    /// Add an invariant specification to this type.
    pub fn add_invariant(&mut self, spec: invariants::Spec) {
        if self.invariant.is_some() {
            panic!("already specified an invariant for type {}", self.name());
        }
        self.invariant = Some(spec);
    }

    /// Generate a Coq definition for the struct layout spec.
    #[must_use]
    pub fn generate_coq_sls_def(&self) -> String {
        self.variant_def.generate_coq_sls_def(&self.scope)
    }

    /// Generate a Coq definition for the struct type alias.
    #[must_use]
    pub fn generate_coq_type_def(&self) -> String {
        if self.is_recursive {
            self.generate_recursive_type_def()
        } else {
            let extra_context = if let Some(inv) = &self.invariant { inv.coq_params.as_slice() } else { &[] };

            // the raw type
            let mut out = self.variant_def.generate_coq_type_def(&self.scope, extra_context);

            // the invariant
            if let Some(spec) = self.invariant.as_ref() {
                // For mode(atomic) + repr(transparent) + single non-ZST field:
                // use the inner field's type directly as base type of at_ex_plain_t,
                // bypassing the struct_t wrapper. This ensures ty_has_op_type delegates
                // to the field type (e.g. IntOp for int) rather than StructOp.
                let transparent_inner = (spec.is_atomic()
                    && self.variant_def.repr == Repr::Transparent
                    && self.variant_def.fields.len() == 1)
                    .then(|| {
                        let (_, inner_ty) = &self.variant_def.fields[0];
                        (inner_ty.to_string(), inner_ty.get_rfn_type().to_string())
                    });

                let s = spec.generate_coq_type_def(
                    self.plain_ty_name(),
                    self.plain_rt_def_name(),
                    &self.scope,
                    transparent_inner.as_ref().map(|(ty, rt)| (ty.as_str(), rt.as_str())),
                );
                out.push_str(&s);
            }

            out
        }
    }

    /// Generate a type definition in case this type is a recursive type.
    fn generate_recursive_type_def(&self) -> String {
        let mut out = String::with_capacity(200);

        // we need an invariant, otherwise we cannot define a recursive type
        if let Some(inv) = self.invariant.as_ref() {
            let all_ty_params = self.scope.get_all_ty_params_with_assocs();

            let Some(_) = &inv.abstracted_refinement else {
                panic!("no abstracted refinement");
            };

            let indent = "  ";
            // the write_str impl will always return Ok.
            write!(out, "Section {}.\n", inv.type_name()).unwrap();
            write!(out, "{}Context `{{RRGS : !refinedrustGS Σ}}.\n", indent).unwrap();

            // add type parameters
            if !all_ty_params.params.is_empty() {
                // first push the (implicit) refinement type parameters
                write!(out, "{}Context", indent).unwrap();
                for names in &all_ty_params.params {
                    write!(out, " ({} : RT)", names.refinement_type()).unwrap();
                }
                out.push_str(".\n");
            }

            let (_context_names, context_names_without_sigma) =
                format_extra_context_items(&inv.coq_params, &mut out).unwrap();

            // generate terms to apply the sls app to
            let mut sls_app = Vec::new();
            for names in &all_ty_params.params {
                // TODO this is duplicated with the same processing for Type::Literal...
                let term = format!("(ty_syn_type {} MetaNone)", names.type_term());
                sls_app.push(term);
            }

            // generate the raw rt def
            // we introduce a let binding for the recursive rt type
            write!(out, "{indent}Definition {} : RT :=\n", self.variant_def.plain_rt_def_name).unwrap();
            let ty_rt_uses = fmt_list!(all_ty_params.get_coq_ty_rt_params().make_using_terms(), " ");
            write!(out, "{indent}{indent}let {} {}", inv.rt_def_name(), ty_rt_uses).unwrap();
            write!(out, " := {} in\n", inv.rfn_type).unwrap();
            write!(out, "{indent}{indent}{}.\n", self.variant_def.rfn_type()).unwrap();

            // invariant def
            write!(
                out,
                "{}",
                inv.generate_coq_invariant_def(&self.scope, &self.variant_def.plain_rt_def_name)
            )
            .unwrap();

            // generate the functor itself
            let type_name = inv.type_name();
            let rfn_type = &inv.rfn_type;
            let spec_name = inv.spec_name();

            write!(
                out,
                "{indent}Definition {type_name}_rec {} ({type_name}_rec' : type ({rfn_type})) : type ({rfn_type}) :=\n",
                all_ty_params.get_semantic_ty_params(),
                ).unwrap();
            write!(
                out,
                "{indent}{indent}let {type_name} {ty_rt_uses} := {} {type_name}_rec' in\n",
                self.scope,
            )
            .unwrap();
            write!(out, "{indent}{indent}let {type_name}_rt {ty_rt_uses} := {rfn_type} in\n").unwrap();
            #[expect(deprecated)]
            write!(
                out,
                "{indent}{indent}ex_plain_t _ _ ({spec_name} {}) ({}).\n",
                self.scope.identity_instantiation_term(),
                self.variant_def.generate_coq_type_term(sls_app)
            )
            .unwrap();

            // write the fixpoint
            #[expect(deprecated)]
            write!(
                out,
                "{indent}Definition {type_name} : {} (type ({rfn_type})) := {} type_fixpoint ({type_name}_rec {}).\n",
                self.scope.get_all_type_term(),
                self.scope,
                fmt_list!(all_ty_params.get_semantic_ty_params().make_using_terms(), " "),
            )
            .unwrap();

            write!(out, "{indent}Global Typeclasses Transparent {}.\n", type_name).unwrap();
            write!(out, "{indent}Definition {}_rt : RT.\n", type_name).unwrap();
            write!(
                out,
                "{indent}Proof using {ty_rt_uses} {}. let __a := normalized_rt_of_spec_ty {} in exact __a. Defined.\n",
                context_names_without_sigma.join(" "),
                type_name
            )
            .unwrap();
            write!(out, "{indent}Global Typeclasses Transparent {}_rt.\n", type_name).unwrap();

            // finish
            write!(out, "End {}.\n", inv.type_name()).unwrap();
            write!(out, "Global Arguments {} : clear implicits.\n", inv.rt_def_name()).unwrap();
            if !context_names_without_sigma.is_empty() {
                //let dep_sigma_str = if dep_sigma { "{_} " } else { "" };
                let dep_sigma_str = "";

                write!(
                    out,
                    "Global Arguments {} {}{} {{{}}}.\n",
                    inv.rt_def_name(),
                    dep_sigma_str,
                    "_ ".repeat(all_ty_params.params.len()),
                    "_ ".repeat(context_names_without_sigma.len())
                )
                .unwrap();
            }
        } else {
            panic!("Recursive types need an invariant");
        }
        out
    }

    /// Make a literal type.
    #[must_use]
    pub fn make_literal_type(&self) -> types::Literal {
        let atomic_inner_st = (self.is_atomic()
            && self.variant_def.repr == Repr::Transparent
            && self.variant_def.fields.len() == 1)
            .then(|| {
                let (_, inner_ty) = &self.variant_def.fields[0];
                let synty: lang::SynType = inner_ty.into();
                synty.to_string()
            });

        let info = types::AdtShimInfo::new(None, self.has_invariant(), atomic_inner_st.clone());

        // For mode(atomic) + repr(transparent) + single field, use the inner
        // field's syn_type instead of the struct's sls. This ensures that
        // local_live allocations match at_ex_plain_t's ty_syn_type delegation.
        let syn_type = if let Some(ref inner_st) = atomic_inner_st {
            lang::SynType::Literal(inner_st.clone())
        } else {
            lang::SynType::Literal(self.sls_def_name().to_owned())
        };

        types::Literal {
            rust_name: Some(self.name().to_owned()),
            type_term: self.public_type_name(),
            refinement_type: coq::term::Type::Literal(self.public_rt_def_name()),
            syn_type,
            info,
        }
    }
}

/// A builder for ADT variants without fancy invariants etc.
pub struct VariantBuilder<'def> {
    /// the fields
    fields: Vec<(String, Type<'def>)>,
    /// the variant's representation mode
    repr: Repr,
    /// the variants's name
    name: String,
}

impl<'def> VariantBuilder<'def> {
    /// Initialize a struct builder.
    /// `ty_params` are the user-facing type parameter names in the Rust code.
    #[must_use]
    pub const fn new(name: String, repr: Repr) -> Self {
        VariantBuilder {
            fields: Vec::new(),
            name,
            repr,
        }
    }

    #[must_use]
    pub fn finish(self) -> AbstractVariant<'def> {
        let sls_def_name: String = format!("{}_sls", &self.name);
        let st_def_name: String = format!("{}_st", &self.name);
        let plain_ty_name: String = format!("{}_ty", &self.name);
        let plain_rt_def_name: String = format!("{}_rt", &self.name);

        AbstractVariant {
            fields: self.fields,
            repr: self.repr,
            name: self.name,
            plain_ty_name,
            sls_def_name,
            st_def_name,
            plain_rt_def_name,
        }
    }

    /// Finish building the struct type and generate an abstract struct definition.
    #[must_use]
    pub fn finish_as_struct(self, scope: GenericScope<'def>) -> Abstract<'def> {
        let variant = self.finish();
        Abstract {
            variant_def: variant,
            invariant: None,
            scope,
            is_recursive: false,
        }
    }

    /// Append a field to the struct def.
    pub fn add_field(&mut self, name: &str, ty: Type<'def>) {
        self.fields.push((name.to_owned(), ty));
    }
}

/// A usage of an `Abstract` that instantiates its type parameters.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct AbstractUse<'def> {
    /// reference to the struct's definition, or None if unit
    pub(crate) def: Option<AbstractRef<'def>>,

    /// Instantiations for type parameters
    pub(crate) scope_inst: GenericScopeInst<'def>,

    /// does this refer to the raw type without invariants?
    raw: TypeIsRaw,
}

impl<'def> AbstractUse<'def> {
    #[must_use]
    pub const fn new(s: AbstractRef<'def>, scope_inst: GenericScopeInst<'def>, raw: TypeIsRaw) -> Self {
        AbstractUse {
            def: Some(s),
            scope_inst,
            raw,
        }
    }

    /// Creates a new use of unit.
    #[must_use]
    pub const fn new_unit() -> Self {
        AbstractUse {
            def: None,
            scope_inst: GenericScopeInst::empty(),
            raw: TypeIsRaw::Yes,
        }
    }

    #[must_use]
    pub(crate) fn is_raw(&self) -> bool {
        self.raw == TypeIsRaw::Yes
    }

    pub(crate) const fn make_raw(&mut self) {
        self.raw = TypeIsRaw::Yes;
    }

    /// Get the refinement type of a struct usage.
    /// This requires that all type parameters of the struct have been instantiated.
    #[must_use]
    pub(crate) fn get_rfn_type(&self) -> String {
        let Some(def) = self.def.as_ref() else {
            return coq::term::Type::Unit.to_string();
        };

        let rfn_instantiations: Vec<_> =
            self.scope_inst.get_all_ty_params_with_assocs().iter().map(Type::get_rfn_type).collect();

        let def = def.borrow();
        let def = def.as_ref().unwrap();
        let inv = &def.invariant.as_ref();

        if self.is_raw() || inv.is_none() {
            let rfn_type = def.plain_rt_def_name().to_owned();
            let applied = coq::term::App::new(rfn_type, rfn_instantiations);
            applied.to_string()
        } else {
            let rfn_type = inv.unwrap().rt_def_name();
            let applied = coq::term::App::new(rfn_type, rfn_instantiations);
            applied.to_string()
        }
    }

    /// Get the `syn_type` term for this struct use.
    #[must_use]
    pub(crate) fn generate_syn_type_term(&self) -> lang::SynType {
        let Some(def) = self.def.as_ref() else {
            return lang::SynType::Unit;
        };

        // first get the syntys for the type params
        let param_sts: Vec<lang::SynType> =
            self.scope_inst.get_all_ty_params_with_assocs().iter().map(Into::into).collect();

        let def = def.borrow();
        let def = def.as_ref().unwrap();

        // For mode(atomic) + repr(transparent) + single field, use the inner
        // field's syn_type. This matches at_ex_plain_t's ty_syn_type delegation.
        if def.is_atomic()
            && def.variant_def.repr == Repr::Transparent
            && def.variant_def.fields.len() == 1
        {
            let (_, inner_ty) = &def.variant_def.fields[0];
            return inner_ty.into();
        }

        let specialized_spec = coq::term::App::new(def.st_def_name().to_owned(), param_sts);
        lang::SynType::Literal(specialized_spec.to_string())
    }

    /// Generate a string representation of this struct use.
    #[must_use]
    pub(crate) fn generate_type_term(&self) -> String {
        let Some(def) = self.def.as_ref() else {
            return Type::Unit.to_string();
        };

        let rt_inst = self
            .scope_inst
            .get_all_ty_params_with_assocs()
            .iter()
            .map(|ty| format!("({})", ty.get_rfn_type()))
            .collect::<Vec<_>>()
            .join(" ");

        let def = def.borrow();
        let def = def.as_ref().unwrap();
        if !self.is_raw() && def.invariant.is_some() {
            let Some(inv) = &def.invariant else {
                unreachable!();
            };

            let attrs = fmt_list!(
                self.scope_inst.get_direct_trait_requirements().iter().map(traits::ReqInst::get_attr_term),
                " "
            );

            format!("({} {rt_inst} {attrs} {})", inv.type_name(), self.scope_inst.instantiation(true, true))
        } else {
            format!("({} {rt_inst} {})", def.plain_ty_name(), self.scope_inst.instantiation(true, true))
        }
    }
}
