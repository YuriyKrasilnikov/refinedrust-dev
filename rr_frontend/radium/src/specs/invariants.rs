// © 2025, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::fmt::Write as _;

use derive_more::Constructor;

use crate::specs::{GenericScope, IncludeSelfReq, TyOwnSpec, format_extra_context_items};
use crate::{coq, fmt_list};

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum SpecFlags {
    /// fully persistent and timeless invariant
    Persistent,
    /// invariant with own sharing predicate,
    Plain,
    NonAtomic,
    Atomic,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum Mode {
    All,
    OnlyShared,
    OnlyOwned,
}

#[derive(Clone, PartialEq, Eq, Debug, Constructor)]
pub struct Spec {
    /// the name of the definition
    name: String,

    flags: SpecFlags,

    /// the refinement type of this struct
    pub(crate) rfn_type: coq::term::Type,

    /// the binding pattern for the refinement of this type
    rfn_pat: coq::binder::Pattern,

    /// existentials that are introduced in the invariant
    existentials: Vec<coq::binder::Binder>,

    /// an optional invariant as a separating conjunction,
    invariants: Vec<(coq::iris::IProp, Mode)>,

    /// additional type ownership
    ty_own_invariants: Vec<TyOwnSpec>,

    // additional ty_lfts
    ty_lfts: Vec<String>,

    // additional ty_wf_elctx
    ty_wf_elctx: Vec<String>,

    /// the specification of the abstracted refinement under a context where `rfn_pat` is bound
    pub(crate) abstracted_refinement: Option<coq::binder::Pattern>,

    // TODO add stuff for non-atomic/atomic invariants
    /// name, type, implicit or not
    pub(crate) coq_params: Vec<coq::binder::Binder>,
}

impl Spec {
    #[must_use]
    pub fn is_atomic(&self) -> bool {
        self.flags == SpecFlags::Atomic
    }

    #[must_use]
    pub fn type_name(&self) -> String {
        format!("{}_inv_t", self.name)
    }

    #[must_use]
    pub(crate) fn rt_def_name(&self) -> String {
        format!("{}_rt", self.type_name())
    }

    #[must_use]
    pub(crate) fn spec_name(&self) -> String {
        format!("{}_inv_spec", self.type_name())
    }

    /// Add the abstracted refinement, if it was not already provided.
    pub fn provide_abstracted_refinement(&mut self, abstracted_refinement: coq::binder::Pattern) {
        if self.abstracted_refinement.is_some() {
            panic!("abstracted refinement for {} already provided", self.type_name());
        }
        self.abstracted_refinement = Some(abstracted_refinement);
    }

    fn make_existential_binders(&self) -> String {
        if self.existentials.is_empty() {
            return String::new();
        }

        format!("∃ {}, ", fmt_list!(&self.existentials, " "))
    }

    /// Assemble the owned invariant predicate for the plain mode.
    fn assemble_plain_owned_invariant(&self) -> String {
        let mut out = String::with_capacity(200);

        let ex = self.make_existential_binders();
        write!(
            out,
            "λ π inner_rfn (_ty_rfn : RT_rt ({}%type : RT)),
            let '{} := _ty_rfn in {}⌜inner_rfn = {}⌝ ∗ ",
            self.rfn_type,
            self.rfn_pat,
            ex,
            self.abstracted_refinement.as_ref().unwrap()
        )
        .unwrap();

        for own in &self.ty_own_invariants {
            write!(out, "{} ∗ ", coq::iris::IProp::Atom(own.fmt_owned("π"))).unwrap();
        }

        for (inv, mode) in &self.invariants {
            match mode {
                Mode::All | Mode::OnlyOwned => {
                    write!(out, "{} ∗ ", inv).unwrap();
                },
                _ => (),
            }
        }
        write!(out, "True").unwrap();

        out
    }

    /// Assemble the sharing invariant predicate for the plain mode.
    fn assemble_plain_shared_invariant(&self) -> String {
        let mut out = String::with_capacity(200);

        let ex = self.make_existential_binders();
        write!(
            out,
            "λ π κ inner_rfn (_ty_rfn : RT_rt ({}%type : RT)),
            let '{} := _ty_rfn in {}⌜inner_rfn = {}⌝ ∗ ",
            self.rfn_type,
            self.rfn_pat,
            ex,
            self.abstracted_refinement.as_ref().unwrap()
        )
        .unwrap();
        for own in &self.ty_own_invariants {
            write!(out, "{} ∗ ", coq::iris::IProp::Atom(own.fmt_shared("π", "κ"))).unwrap();
        }
        for (inv, mode) in &self.invariants {
            match mode {
                Mode::All | Mode::OnlyShared => {
                    write!(out, "{} ∗ ", inv).unwrap();
                },
                _ => (),
            }
        }
        write!(out, "True").unwrap();

        out
    }

    /// Assemble the list of lifetimes the invariant requires to be alive.
    fn assemble_ty_lfts(&self) -> String {
        let mut out = String::with_capacity(200);

        write!(out, "[]").unwrap();

        // go over all the types and concat their lfts
        for spec in &self.ty_own_invariants {
            for ty in &spec.annot_meta.escaped_tyvars {
                write!(out, " ++ (ty_lfts ({}))", ty.type_term()).unwrap();
            }
            for lft in &spec.annot_meta.escaped_lfts {
                write!(out, " ++ [{}]", lft).unwrap();
            }
        }
        for x in &self.ty_lfts {
            write!(out, " ++ {x}").unwrap();
        }

        out
    }

    /// Assemble the lifetime constraints that this type requires.
    fn assemble_ty_wf_elctx(&self) -> String {
        let mut out = String::with_capacity(200);
        write!(out, "[]").unwrap();

        // go over all the types and concat their lfts
        for spec in &self.ty_own_invariants {
            for ty in &spec.annot_meta.escaped_tyvars {
                write!(out, " ++ (ty_wf_E ({}))", ty.type_term()).unwrap();
            }
        }
        for x in &self.ty_wf_elctx {
            write!(out, " ++ {x}").unwrap();
        }

        out
    }

    /// Assemble the invariant for the persistent mode.
    fn assemble_pers_invariant(&self) -> String {
        let mut out = String::with_capacity(200);

        let ex = self.make_existential_binders();
        // TODO: maybe use some other formulation, the destructing let will make the
        // persistence/timeless inference go nuts.
        write!(
            out,
            "λ inner_rfn (_rfn_binder : RT_rt ({}%type : RT)),
            let '{} := _rfn_binder in {}⌜inner_rfn = {}⌝ ∗ ",
            self.rfn_type,
            self.rfn_pat,
            ex,
            self.abstracted_refinement.as_ref().unwrap()
        )
        .unwrap();
        for (inv, _) in &self.invariants {
            write!(out, "{} ∗ ", inv).unwrap();
        }
        write!(out, "True").unwrap();

        out
    }

    pub(crate) fn generate_coq_invariant_def(&self, scope: &GenericScope<'_>, base_rfn_type: &str) -> String {
        if self.flags == SpecFlags::Persistent {
            assert!(self.invariants.iter().all(|it| it.1 == Mode::All) && self.ty_own_invariants.is_empty());
        }

        let mut out = String::with_capacity(200);
        let indent = "  ";

        // generate the spec definition
        let spec_name = self.spec_name();

        let attr_binders = scope.get_all_attr_trait_parameters(IncludeSelfReq::Dont);

        match self.flags {
            SpecFlags::NonAtomic => {
                #[expect(deprecated)]
                write!(
                    out,
                    "{indent}Program Definition {} {} : {} (na_ex_inv_def ({})%type ({})%type) := ",
                    spec_name,
                    attr_binders,
                    scope.get_all_type_term(),
                    base_rfn_type,
                    self.rfn_type,
                )
                .unwrap();
            },
            SpecFlags::Atomic => {
                #[expect(deprecated)]
                write!(
                    out,
                    "{indent}Program Definition {} {} : {} (at_ex_inv_def ({})%type ({})%type) := ",
                    spec_name,
                    attr_binders,
                    scope.get_all_type_term(),
                    base_rfn_type,
                    self.rfn_type,
                )
                .unwrap();
            },
            _ => {
                #[expect(deprecated)]
                write!(
                    out,
                    "{indent}Program Definition {} {} : {} (ex_inv_def ({})%type ({})%type) := ",
                    spec_name,
                    attr_binders,
                    scope.get_all_type_term(),
                    base_rfn_type,
                    self.rfn_type,
                )
                .unwrap();
            },
        }

        match self.flags {
            SpecFlags::Persistent => {
                let inv = self.assemble_pers_invariant();
                write!(
                    out,
                    "{scope} mk_pers_ex_inv_def\n\
                       {indent}{indent}({inv})%I _ _\n\
                       {indent}.\n",
                )
                .unwrap();
                write!(out, "{indent}Next Obligation. ex_t_solve_persistent. Qed.\n").unwrap();
                write!(out, "{indent}Next Obligation. ex_t_solve_timeless. Qed.\n").unwrap();
            },
            SpecFlags::Plain => {
                let own_inv = self.assemble_plain_owned_invariant();
                let shr_inv = self.assemble_plain_shared_invariant();
                let lft_outlives = self.assemble_ty_lfts();
                let lft_wf_elctx = self.assemble_ty_wf_elctx();

                let attr_intro = if attr_binders.0.is_empty() {
                    String::new()
                } else {
                    format!("intros{}; ", " ?".repeat(attr_binders.0.len()))
                };

                // If there are no specific invariants given just for owned/shared ownership, use
                // automatic inference of the sharing predicate
                if self.invariants.iter().all(|(_, mode)| *mode == Mode::All) {
                    write!(
                        out,
                        "{scope} mk_auto_ex_inv_def\n\
                        {indent}{indent}({own_inv})%I\n\
                        {indent}{indent}({lft_outlives})\n\
                        {indent}{indent}({lft_wf_elctx})\n\
                        {indent}{indent}_ _ _\n\
                        {indent}.\n",
                    )
                    .unwrap();
                    write!(out, "{indent}Next Obligation. ex_plain_t_solve_shr_auto. Defined.\n").unwrap();
                    write!(out, "{indent}Next Obligation. ex_t_solve_persistent. Qed.\n").unwrap();
                    write!(out, "{indent}Next Obligation. {attr_intro}ex_plain_t_solve_shr_mono. Qed.\n")
                        .unwrap();
                } else {
                    write!(
                        out,
                        "{scope} mk_ex_inv_def\n\
                        {indent}{indent}({own_inv})%I\n\
                        {indent}{indent}({shr_inv})%I\n\
                        {indent}{indent}({lft_outlives})\n\
                        {indent}{indent}({lft_wf_elctx})\n\
                        {indent}{indent}_ _ _\n\
                        {indent}.\n",
                    )
                    .unwrap();
                    write!(out, "{indent}Next Obligation. ex_t_solve_persistent. Qed.\n").unwrap();
                    write!(out, "{indent}Next Obligation. {attr_intro}ex_plain_t_solve_shr_mono. Qed.\n")
                        .unwrap();
                    write!(out, "{indent}Next Obligation. {attr_intro}ex_plain_t_solve_shr. Qed.\n").unwrap();
                }
            },
            SpecFlags::NonAtomic => {
                let own_inv = self.assemble_plain_owned_invariant();
                let lft_outlives = self.assemble_ty_lfts();
                let lft_wf_elctx = self.assemble_ty_wf_elctx();

                write!(
                    out,
                    "{scope} na_mk_ex_inv_def\n\
                    {indent}{indent}({own_inv})%I\n\
                    {indent}{indent}({lft_outlives})\n\
                    {indent}{indent}({lft_wf_elctx})\n\
                    {indent}.\n",
                )
                .unwrap();
            },
            SpecFlags::Atomic => {
                let own_inv = self.assemble_plain_owned_invariant();
                let lft_outlives = self.assemble_ty_lfts();
                let lft_wf_elctx = self.assemble_ty_wf_elctx();

                write!(
                    out,
                    "{scope} at_mk_ex_inv_def\n\
                    {indent}{indent}({own_inv})%I\n\
                    {indent}{indent}({lft_outlives})\n\
                    {indent}{indent}({lft_wf_elctx})\n\
                    {indent}.\n",
                )
                .unwrap();
            },
        }
        write!(out, "\n").unwrap();

        out
    }

    /// Generate the Coq definition of the type, without the surrounding context assumptions.
    pub(crate) fn generate_coq_type_def_core(
        &self,
        base_type: &str,
        base_rfn_type: &str,
        generics_rts: &Vec<coq::term::Term>,
        scope: &GenericScope<'_>,
        context_names: &[String],
    ) -> String {
        let mut out = String::with_capacity(200);
        let indent = "  ";

        // generate the spec definition
        let spec_name = self.spec_name();

        write!(out, "{}", self.generate_coq_invariant_def(scope, base_rfn_type)).unwrap();

        let attr_binders = scope.get_all_attr_trait_parameters(IncludeSelfReq::Dont);
        let attr_binders_uses = attr_binders.make_using_terms();

        // generate the definition itself.
        match self.flags {
            SpecFlags::NonAtomic => {
                #[expect(deprecated)]
                write!(
                    out,
                    "{indent}Definition {} {attr_binders} : {} (type ({})%type) :=\n\
                    {indent}{indent}{scope} na_ex_plain_t _ _ ({spec_name} {} {}) {}.\n",
                    self.type_name(),
                    scope.get_all_type_term(),
                    self.rfn_type,
                    fmt_list!(attr_binders_uses, " "),
                    scope.identity_instantiation_term(),
                    base_type
                )
                .unwrap();
            },
            SpecFlags::Atomic => {
                #[expect(deprecated)]
                write!(
                    out,
                    "{indent}Definition {} {attr_binders} : {} (type ({})%type) :=\n\
                    {indent}{indent}{scope} at_ex_plain_t _ _ ({spec_name} {} {}) {}.\n",
                    self.type_name(),
                    scope.get_all_type_term(),
                    self.rfn_type,
                    fmt_list!(attr_binders_uses, " "),
                    scope.identity_instantiation_term(),
                    base_type
                )
                .unwrap();
            },
            SpecFlags::Persistent | SpecFlags::Plain => {
                #[expect(deprecated)]
                write!(
                    out,
                    "{indent}Definition {} {attr_binders} : {} (type ({})%type) :=\n\
                    {indent}{indent}{scope} ex_plain_t _ _ ({spec_name} {} {}) {}.\n",
                    self.type_name(),
                    scope.get_all_type_term(),
                    self.rfn_type,
                    fmt_list!(attr_binders_uses, " "),
                    scope.identity_instantiation_term(),
                    base_type
                )
                .unwrap();
            },
        }
        write!(out, "{indent}Global Typeclasses Transparent {}.\n", self.type_name()).unwrap();
        write!(out, "{indent}Definition {}_rt : RT.\n", self.type_name()).unwrap();
        write!(
            out,
            "{indent}Proof using {} {}. let __a := normalized_rt_of_spec_ty {} in exact __a. Defined.\n",
            fmt_list!(generics_rts, " "),
            context_names.join(" "),
            self.type_name()
        )
        .unwrap();
        write!(out, "{indent}Global Typeclasses Transparent {}_rt.\n", self.type_name()).unwrap();

        out
    }

    /// Generate the definition of the Coq type, including introduction of type parameters to the
    /// context.
    pub(crate) fn generate_coq_type_def(
        &self,
        base_type_name: &str,
        base_rfn_type: &str,
        scope: &GenericScope<'_>,
        transparent_inner_override: Option<(&str, &str)>,
    ) -> String {
        let mut out = String::with_capacity(200);

        assert!(self.abstracted_refinement.is_some());

        let indent = "  ";
        // the write_str impl will always return Ok.
        write!(out, "Section {}.\n", self.type_name()).unwrap();
        write!(out, "{}Context `{{RRGS : !refinedrustGS Σ}}.\n", indent).unwrap();

        let all_ty_params = scope.get_all_ty_params_with_assocs();

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
            format_extra_context_items(&self.coq_params, &mut out).unwrap();

        let rt_instantiations = all_ty_params.get_coq_ty_rt_params().make_using_terms();

        let attr_binders = scope.get_all_attr_trait_parameters(IncludeSelfReq::Dont);
        let attr_binders_uses = attr_binders.make_using_terms();

        // For transparent atomic single-field structs, use the inner field type directly
        // as at_ex_plain_t base type. Otherwise, apply the struct type/rfn definitions
        // with trait attribute parameters.
        let (applied_base_rt_str, applied_base_type) =
            if let Some((inner_ty, inner_rt)) = transparent_inner_override {
                debug_assert!(
                    attr_binders_uses.is_empty(),
                    "atomic transparent type should not have trait attribute parameters"
                );
                (inner_rt.to_owned(), format!("({})", inner_ty))
            } else {
                let applied_base_rt = coq::term::App::new(base_rfn_type, rt_instantiations.clone());
                let applied_base_type = coq::term::App::new(
                    coq::term::Term::App(Box::new(coq::term::App::new(
                        coq::term::Term::Literal(base_type_name.to_owned()),
                        rt_instantiations.clone(),
                    ))),
                    attr_binders_uses,
                );
                let applied_base_type =
                    format!("({applied_base_type} {})", scope.identity_instantiation_term());
                (applied_base_rt.to_string(), applied_base_type)
            };

        write!(
            out,
            "{}",
            self.generate_coq_type_def_core(
                &applied_base_type,
                &applied_base_rt_str,
                &rt_instantiations,
                scope,
                &context_names_without_sigma,
            )
        )
        .unwrap();

        // finish
        write!(out, "End {}.\n", self.type_name()).unwrap();
        write!(out, "Global Arguments {} : clear implicits.\n", self.rt_def_name()).unwrap();
        if !context_names_without_sigma.is_empty() {
            //let dep_sigma_str = if dep_sigma { "{_} " } else { "" };
            let dep_sigma_str = "";

            write!(
                out,
                "Global Arguments {} {}{} {{{}}}.\n",
                self.rt_def_name(),
                dep_sigma_str,
                "_ ".repeat(all_ty_params.params.len()),
                "_ ".repeat(context_names_without_sigma.len())
            )
            .unwrap();
        }

        out
    }
}
