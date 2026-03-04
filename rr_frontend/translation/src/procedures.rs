// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::{BTreeMap, btree_map};

use derive_more::{Constructor, Display};
use radium::{code, coq, specs};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;

use crate::base::*;
use crate::{error, regions};

#[derive(Copy, Clone, Eq, PartialEq, Debug, Display)]
pub(crate) enum Mode {
    #[display("prove")]
    Prove,

    #[display("only_spec")]
    OnlySpec,

    #[display("trust_me")]
    TrustMe,

    #[display("shim")]
    Shim,

    #[display("code_shim")]
    CodeShim,

    #[display("ignore")]
    Ignore,
}

#[allow(clippy::allow_attributes)]
impl Mode {
    pub(crate) fn is_prove(self) -> bool {
        self == Self::Prove
    }

    pub(crate) fn is_only_spec(self) -> bool {
        self == Self::OnlySpec
    }

    pub(crate) fn is_trust_me(self) -> bool {
        self == Self::TrustMe
    }

    pub(crate) fn is_shim(self) -> bool {
        self == Self::Shim
    }

    pub(crate) fn is_code_shim(self) -> bool {
        self == Self::CodeShim
    }

    pub(crate) fn is_ignore(self) -> bool {
        self == Self::Ignore
    }

    pub(crate) fn is_assumed(self) -> bool {
        self.is_only_spec() || self.is_trust_me()
    }

    pub(crate) fn needs_proof(self) -> bool {
        self.is_prove() || self.is_code_shim()
    }

    pub(crate) fn needs_def(self) -> bool {
        self.is_prove() || self.is_trust_me()
    }

    pub(crate) fn needs_spec(self) -> bool {
        self.is_prove() || self.is_trust_me() || self.is_only_spec() || self.is_code_shim()
    }
}

#[derive(Clone, Eq, PartialEq, Debug, Constructor)]
pub(crate) struct Meta {
    /// name for the specification
    spec_name: String,
    /// name for the code
    code_name: String,
    /// name for the trait inclusion def
    trait_req_incl_name: String,
    /// mangled name of the function
    name: String,
    /// what should `RefinedRust` do with this function?
    mode: Mode,
    /// true if this is a default trait impl
    is_default_trait_impl: bool,
    /// true if this is a closure
    is_closure: bool,
}

impl Meta {
    pub(crate) fn get_spec_name(&self) -> &str {
        &self.spec_name
    }

    pub(crate) fn get_trait_req_incl_name(&self) -> &str {
        &self.trait_req_incl_name
    }

    pub(crate) fn get_name(&self) -> &str {
        &self.name
    }

    pub(crate) fn get_code_name(&self) -> &str {
        &self.code_name
    }

    pub(crate) const fn get_mode(&self) -> Mode {
        self.mode
    }

    pub(crate) const fn is_trait_default(&self) -> bool {
        self.is_default_trait_impl
    }
}

/// Extra info required to create a closure impl.
/// This is created by the translation for the closure body.
#[derive(Debug, Clone, Constructor)]
pub(crate) struct ClosureImplInfo<'tcx, 'def> {
    // the most general closure kind this implements
    _closure_kind: ty::ClosureKind,

    // the generic scope of this impl
    pub(crate) scope: specs::GenericScope<'def>,
    /// if this is a Fn/FnMut closure, the lifetime of the closure self arg inside `scope`
    pub(crate) _closure_lifetime: Option<specs::Lft>,

    pub(crate) region_map: regions::EarlyLateRegionMap<'def>,

    // types of the closure trait
    // this is the type of the self variable in the closure, i.e. wrapped in references for
    // Fn/FnMut
    pub(crate) self_ty: ty::Ty<'tcx>,
    pub(crate) args_ty: ty::Ty<'tcx>,

    pub(crate) tl_self_var_ty: specs::Type<'def>,
    pub(crate) tl_args_ty: specs::Type<'def>,
    pub(crate) tl_args_tys: Vec<specs::Type<'def>>,
    pub(crate) tl_output_ty: specs::Type<'def>,

    // the encoded pre and postconditions
    pub(crate) params_encoded: coq::term::Term,
    pub(crate) pre_encoded: coq::term::Term,
    pub(crate) post_encoded: coq::term::Term,
    pub(crate) post_mut_encoded: coq::term::Term,
}

pub(crate) struct ClosureInfo<'tcx, 'rcx> {
    pub(crate) info: ClosureImplInfo<'tcx, 'rcx>,

    pub(crate) generated_functions: Vec<code::Function<'rcx>>,
    pub(crate) generated_impls: Vec<specs::traits::ImplSpec<'rcx>>,
}

/**
 * Tracks the functions we translated and the Coq names they are available under.
 * To account for dependencies between functions, we may register translated names before we have
 * actually translated the function.
 */
pub(crate) struct Scope<'tcx, 'def> {
    tcx: ty::TyCtxt<'tcx>,
    /// maps the defid to meta data
    name_map: BTreeMap<OrderedDefId, Meta>,
    /// track the actually translated functions
    translated_functions: BTreeMap<OrderedDefId, code::Function<'def>>,
    /// track the functions with just a specification (`rr::only_spec`)
    specced_functions:
        BTreeMap<OrderedDefId, &'def specs::functions::Spec<'def, specs::functions::InnerSpec<'def>>>,

    /// store info of closures we translated to emit closure trait impls
    pub(crate) closure_info: BTreeMap<OrderedDefId, ClosureInfo<'tcx, 'def>>,
}

impl<'tcx, 'def> Scope<'tcx, 'def> {
    pub(crate) const fn new(tcx: ty::TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            name_map: BTreeMap::new(),
            translated_functions: BTreeMap::new(),
            specced_functions: BTreeMap::new(),
            closure_info: BTreeMap::new(),
        }
    }

    fn get_ordered_did(&self, did: DefId) -> OrderedDefId {
        OrderedDefId::new(self.tcx, did)
    }

    pub(crate) fn lookup_closure_info(&self, did: DefId) -> Option<&ClosureImplInfo<'tcx, 'def>> {
        self.closure_info.get(&self.get_ordered_did(did)).map(|x| &x.info)
    }

    /// Lookup the meta information of a function.
    pub(crate) fn lookup_function(&self, did: DefId) -> Option<Meta> {
        self.name_map.get(&self.get_ordered_did(did)).cloned()
    }

    /// Lookup a translated function spec
    pub(crate) fn lookup_function_spec(
        &'_ self,
        did: DefId,
    ) -> Option<&'def specs::functions::Spec<'def, specs::functions::InnerSpec<'def>>> {
        let ordered_did = self.get_ordered_did(did);
        if let Some(translated_fn) = self.translated_functions.get(&ordered_did) {
            Some(translated_fn.spec)
        } else if let Some(translated_spec) = self.specced_functions.get(&ordered_did) {
            Some(translated_spec)
        } else {
            None
        }
    }

    /// Lookup the mode for a function.
    pub(crate) fn lookup_function_mode(&self, did: DefId) -> Option<Mode> {
        self.name_map.get(&self.get_ordered_did(did)).map(Meta::get_mode)
    }

    /// Register a function.
    pub(crate) fn register_function(&mut self, did: DefId, meta: Meta) -> Result<(), TranslationError<'tcx>> {
        if rrconfig::no_assumption() && meta.mode.is_assumed() {
            self.tcx
                .dcx()
                .span_err(self.tcx.def_span(did), error::Message::NoAssumptionAllowed(meta.mode));
        }

        if self.name_map.insert(self.get_ordered_did(did), meta).is_some() {
            Err(TranslationError::ProcedureRegistry(format!(
                "function for defid {:?} has already been registered",
                did
            )))
        } else {
            Ok(())
        }
    }

    /// For a function which is a trait member's default impl, provide the overridden spec names
    /// from the trait registry.
    pub(crate) fn override_trait_default_impl_names(
        &mut self,
        did: DefId,
        spec_name: &str,
        trait_req_incl_name: &str,
    ) {
        if let Some(names) = self.name_map.get_mut(&self.get_ordered_did(did)) {
            assert!(names.is_default_trait_impl);
            spec_name.clone_into(&mut names.spec_name);
            trait_req_incl_name.clone_into(&mut names.trait_req_incl_name);
        }
    }

    /// Provide the code for a translated function.
    pub(crate) fn provide_translated_function(&mut self, did: DefId, trf: code::Function<'def>) {
        let ordered_did = self.get_ordered_did(did);
        let meta = &self.name_map[&ordered_did];
        assert!(meta.get_mode().needs_def() || meta.get_mode().is_code_shim());
        assert!(self.translated_functions.insert(ordered_did, trf).is_none());
    }

    /// Provide the specification for an `only_spec` function.
    pub(crate) fn provide_specced_function(
        &mut self,
        did: DefId,
        spec: &'def specs::functions::Spec<'def, specs::functions::InnerSpec<'def>>,
    ) {
        let ordered_did = self.get_ordered_did(did);
        let meta = &self.name_map[&ordered_did];
        assert!(meta.get_mode().is_only_spec());
        assert!(self.specced_functions.insert(ordered_did, spec).is_none());
    }

    /// Iterate over the functions we have generated code for.
    pub(crate) fn iter_code(&self) -> btree_map::Iter<'_, OrderedDefId, code::Function<'def>> {
        self.translated_functions.iter()
    }

    /// Iterate over the functions we have generated only specs for.
    pub(crate) fn iter_only_spec(
        &self,
    ) -> btree_map::Iter<
        '_,
        OrderedDefId,
        &'def specs::functions::Spec<'def, specs::functions::InnerSpec<'def>>,
    > {
        self.specced_functions.iter()
    }
}
