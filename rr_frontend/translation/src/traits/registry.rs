// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, HashMap, btree_map};

use log::{info, trace};
use radium::{coq, specs};
use rr_rustc_interface::hir::def_id::{DefId, LocalDefId};
use rr_rustc_interface::middle::ty;
use traits::{Error, TraitResult, resolution};
use typed_arena::Arena;

use crate::base::*;
use crate::body::signature;
use crate::environment::Environment;
use crate::regions::region_bi_folder::RegionBiFolder;
use crate::spec_parsers::propagate_method_attr_from_impl;
use crate::spec_parsers::trait_attr_parser::{
    TraitAttrParser as _, VerboseTraitAttrParser, get_declared_trait_attrs,
};
use crate::spec_parsers::trait_impl_attr_parser::{TraitImplAttrParser as _, VerboseTraitImplAttrParser};
use crate::traits::requirements;
use crate::types::scope;
use crate::{attrs, error, procedures, search, traits, types};

#[derive(Debug)]
pub(crate) struct ResolvedTraitReq<'tcx, 'def> {
    pub(crate) req_inst: specs::traits::ReqInst<'def, ty::Ty<'tcx>>,
    pub(crate) args: ty::GenericArgsRef<'tcx>,
}

/// A using occurrence of a trait in the signature of the function.
#[derive(Debug, Clone)]
pub(crate) struct GenericTraitUse<'tcx, 'def> {
    /// the `DefId` of the trait
    pub did: DefId,
    pub trait_ref: ty::TraitRef<'tcx>,
    /// the Coq-level trait use
    pub trait_use: specs::traits::LiteralSpecUseRef<'def>,
    /// quantifiers for HRTBs
    pub bound_regions: Vec<ty::BoundRegionKind<'tcx>>,
    /// this is a trait use of the trait itself in a trait declaration
    pub is_self_use: bool,
}

impl<'tcx, 'def> GenericTraitUse<'tcx, 'def> {
    /// Get the associated type instantiation of an associated type given by [did] for this instantiation.
    /// This is used in the translation of symbolic `TyKind::Alias`.
    pub(crate) fn get_associated_type_use(
        &self,
        env: &Environment<'tcx>,
        did: DefId,
    ) -> Result<specs::Type<'def>, Error<'tcx>> {
        let type_name = env.get_assoc_item_name(did).ok_or(Error::NotAnAssocType(did))?;
        let type_idx = env.get_trait_associated_type_index(did).ok_or(Error::NotAnAssocType(did))?;

        // this is an associated type of the trait that is currently being declared
        // so make a symbolic reference
        if self.is_self_use {
            // make a literal
            let lit = specs::LiteralTyParam::new_with_origin(&type_name, specs::TyParamOrigin::AssocInDecl);
            Ok(specs::Type::LiteralParam(lit))
        } else {
            let trait_use_ref = self.trait_use.borrow();
            let trait_use = trait_use_ref.as_ref().unwrap();

            Ok(trait_use.make_assoc_type_use(type_idx))
        }
    }

    pub(crate) fn get_associated_types(&self, env: &Environment<'_>) -> Vec<(String, specs::Type<'def>)> {
        let mut assoc_tys = Vec::new();

        // get associated types
        let assoc_types = env.get_trait_assoc_types(self.did);
        for (idx, ty_did) in assoc_types.iter().enumerate() {
            let ty_name = env.get_assoc_item_name(*ty_did).unwrap();
            let trait_use_ref = self.trait_use.borrow();
            let trait_use = trait_use_ref.as_ref().unwrap();
            let lit = trait_use.make_assoc_type_use(idx);
            assoc_tys.push((ty_name.clone(), lit));
        }
        assoc_tys
    }
}

pub(crate) struct TR<'tcx, 'def> {
    /// environment
    env: &'def Environment<'tcx>,
    type_translator: Cell<Option<&'def types::TX<'def, 'tcx>>>,

    /// trait declarations
    trait_decls: RefCell<BTreeMap<OrderedDefId, specs::traits::SpecDecl<'def>>>,
    /// trait literals for using occurrences, including shims we import
    trait_literals: RefCell<BTreeMap<OrderedDefId, specs::traits::LiteralSpecRef<'def>>>,

    /// for the trait instances in scope, the names for their Coq definitions
    /// (to enable references to them when translating functions)
    impl_literals: RefCell<BTreeMap<OrderedDefId, specs::traits::LiteralImplRef<'def>>>,

    /// for all closures we process and all the closure traits they will implement, the names for
    /// the Coq definitions, as well as the meta information for the impl method
    closure_impls:
        RefCell<HashMap<(DefId, ty::ClosureKind), (specs::traits::LiteralImplRef<'def>, procedures::Meta)>>,

    /// arena for allocating trait literals
    trait_arena: &'def Arena<specs::traits::LiteralSpec>,
    /// arena for allocating impl literals
    impl_arena: &'def Arena<specs::traits::LiteralImpl>,
    /// arena for allocating trait use references
    trait_use_arena: &'def Arena<specs::traits::LiteralSpecUseCell<'def>>,
    /// arena for function specifications
    fn_spec_arena: &'def Arena<specs::functions::Spec<'def, specs::functions::InnerSpec<'def>>>,
}

impl<'tcx, 'def> TR<'tcx, 'def> {
    pub(crate) const fn type_translator(&self) -> &'def types::TX<'def, 'tcx> {
        self.type_translator.get().unwrap()
    }

    /// Create an empty trait registry.
    pub(crate) fn new(
        env: &'def Environment<'tcx>,
        trait_arena: &'def Arena<specs::traits::LiteralSpec>,
        impl_arena: &'def Arena<specs::traits::LiteralImpl>,
        trait_use_arena: &'def Arena<specs::traits::LiteralSpecUseCell<'def>>,
        fn_spec_arena: &'def Arena<specs::functions::Spec<'def, specs::functions::InnerSpec<'def>>>,
    ) -> Self {
        Self {
            env,
            type_translator: Cell::new(None),
            trait_arena,
            impl_arena,
            trait_use_arena,
            fn_spec_arena,
            trait_decls: RefCell::new(BTreeMap::new()),
            trait_literals: RefCell::new(BTreeMap::new()),
            impl_literals: RefCell::new(BTreeMap::new()),
            closure_impls: RefCell::new(HashMap::new()),
        }
    }

    pub(crate) fn provide_type_translator(&self, ty_translator: &'def types::TX<'def, 'tcx>) {
        self.type_translator.set(Some(ty_translator));
    }

    /// Get registered trait declarations in the local crate.
    pub(crate) fn get_trait_decls(&self) -> BTreeMap<OrderedDefId, specs::traits::SpecDecl<'def>> {
        let decls = self.trait_decls.borrow();
        decls.clone()
    }

    /// Get a set of other (different) traits that this trait depends on.
    pub(crate) fn get_deps_of_trait(&self, did: DefId) -> BTreeSet<OrderedDefId> {
        let param_env: ty::ParamEnv<'tcx> = self.env.tcx().param_env(did);

        let mut deps = BTreeSet::new();
        for clause in param_env.caller_bounds() {
            let kind = clause.kind().skip_binder();
            if let ty::ClauseKind::Trait(pred) = kind {
                let other_did = pred.trait_ref.def_id;

                if other_did != did {
                    deps.insert(OrderedDefId::new(self.env.tcx(), other_did));
                }
            }
        }

        deps
    }

    /// Order the given traits according to their dependencies.
    pub(crate) fn get_trait_deps(
        &self,
        traits: &[LocalDefId],
    ) -> BTreeMap<OrderedDefId, BTreeSet<OrderedDefId>> {
        let mut dep_map = BTreeMap::new();

        for trait_decl in traits {
            let deps = self.get_deps_of_trait(trait_decl.to_def_id());
            dep_map.insert(OrderedDefId::new(self.env.tcx(), trait_decl.to_def_id()), deps);
        }

        dep_map
    }

    /// Get a map of dependencies between traits.
    pub(crate) fn get_registered_trait_deps(&self) -> BTreeMap<OrderedDefId, BTreeSet<OrderedDefId>> {
        let mut dep_map = BTreeMap::new();

        let decls = self.trait_decls.borrow();
        for trait_decl in decls.keys() {
            let deps = self.get_deps_of_trait(trait_decl.def_id);
            dep_map.insert(trait_decl.to_owned(), deps);
        }

        dep_map
    }

    /// Get the names of associated types of this trait.
    pub(crate) fn get_associated_type_names(&self, did: DefId) -> Vec<String> {
        let mut assoc_tys = Vec::new();

        // get associated types
        let assoc_types = self.env.get_trait_assoc_types(did);
        for ty_did in &assoc_types {
            let ty_name = self.env.get_assoc_item_name(*ty_did).unwrap();
            assoc_tys.push(ty_name);
        }

        assoc_tys
    }

    /// Generate names for a trait.
    fn make_literal_trait_spec(
        &self,
        did: DefId,
        name: String,
        declared_attrs: Vec<String>,
        has_semantic_interp: bool,
        attrs_dependent: bool,
    ) -> Result<specs::traits::LiteralSpec, Error<'tcx>> {
        let mut method_trait_incl_decls = BTreeMap::new();

        let items: &ty::AssocItems = self.env.tcx().associated_items(did);
        let items = traits::sort_assoc_items(self.env, items);
        for c in items {
            if let ty::AssocKind::Fn { .. } = c.kind {
                // get function name
                let method_name =
                    self.env.get_assoc_item_name(c.def_id).ok_or(Error::NotATraitMethod(c.def_id))?;
                let method_name = strip_coq_ident(&method_name);

                let trait_incl_decl = format!("trait_incl_of_{name}_{method_name}");
                method_trait_incl_decls.insert(method_name, trait_incl_decl);
            }
        }

        Ok(specs::traits::LiteralSpec {
            name,
            assoc_tys: self.get_associated_type_names(did),
            has_semantic_interp,
            attrs_dependent,
            declared_attrs,
            method_trait_incl_decls,
        })
    }

    /// Pre-register trait to account for mutually recursive traits.
    pub(crate) fn preregister_trait(&'def self, did: LocalDefId) -> Result<(), TranslationError<'tcx>> {
        {
            let scope = self.trait_decls.borrow();
            let ordered_did = OrderedDefId::new(self.env.tcx(), did.to_def_id());
            if scope.get(&ordered_did).is_some() {
                return Ok(());
            }
        }

        // first register the shim so we can handle recursive traits
        let trait_name = strip_coq_ident(&self.env.get_absolute_item_name(did.to_def_id()));
        let trait_attrs = attrs::filter_for_tool(self.env.get_attributes(did.into()));

        let has_semantic_interp = self.env.has_tool_attribute(did.into(), "semantic");
        let attrs_dependent = !self.env.has_tool_attribute(did.into(), "nondependent");

        // get the declared attributes that are allowed on impls
        let valid_attrs: Vec<String> =
            get_declared_trait_attrs(&trait_attrs).map_err(|e| Error::TraitSpec(did.into(), e))?;

        // make the literal we are going to use
        let lit_trait_spec = self.make_literal_trait_spec(
            did.to_def_id(),
            trait_name,
            valid_attrs,
            has_semantic_interp,
            attrs_dependent,
        )?;
        // already register it for use
        // In particular, this is also needed to be able to register the methods of this trait
        // below, as they need to be able to access the associated types of this trait already.
        // (in fact, their environment contains their self instance)
        self.register_shim(did.to_def_id(), lit_trait_spec)?;
        Ok(())
    }

    /// Register a new annotated trait in the local crate with the registry.
    pub(crate) fn register_trait(
        &'def self,
        did: LocalDefId,
        proc_registry: &mut procedures::Scope<'tcx, 'def>,
    ) -> Result<(), TranslationError<'tcx>> {
        trace!("enter TR::register_trait for did={did:?}");

        let ordered_did = OrderedDefId::new(self.env.tcx(), did.to_def_id());
        {
            let scope = self.trait_decls.borrow();
            if scope.get(&ordered_did).is_some() {
                return Ok(());
            }
        }

        // lookup the pre-registered literal
        let lit_trait_spec_ref =
            self.lookup_trait(did.to_def_id()).ok_or_else(|| Error::NotATrait(did.to_def_id()))?;

        let trait_name = strip_coq_ident(&self.env.get_absolute_item_name(did.to_def_id()));
        let trait_attrs = attrs::filter_for_tool(self.env.get_attributes(did.into()));

        let mut cont = || -> Result<(), TranslationError<'tcx>> {
            // get generics
            let trait_generics: &'tcx ty::Generics = self.env.tcx().generics_of(did.to_def_id());
            let mut param_scope = scope::Params::from(trait_generics.own_params.as_slice());
            param_scope.add_param_env(did.to_def_id(), self.env, self.type_translator(), self)?;

            let param_env: ty::ParamEnv<'tcx> = self.env.tcx().param_env(did.to_def_id());
            trace!("param env is {:?}", param_env);

            // parse trait spec
            // As different attributes of the spec may depend on each other, we need to pass a closure
            // determining under which Coq name we are going to introduce them
            // Note: This needs to match up with `specs::LiteralTraitSpec.make_spec_attr_name`!
            let mut attr_parser =
                VerboseTraitAttrParser::new(&param_scope, |id| format!("{trait_name}_{id}"));
            let trait_spec =
                attr_parser.parse_trait_attrs(&trait_attrs).map_err(|e| Error::TraitSpec(did.into(), e))?;

            // get items
            let mut methods = BTreeMap::new();
            let mut assoc_types = Vec::new();
            let items: &ty::AssocItems = self.env.tcx().associated_items(did);
            let items = traits::sort_assoc_items(self.env, items);
            for c in items {
                if ty::AssocTag::Fn == c.tag() {
                    // get attributes
                    let attrs =
                        self.env.get_attributes_of_function(c.def_id, &propagate_method_attr_from_impl);

                    // get function name
                    let method_name =
                        self.env.get_assoc_item_name(c.def_id).ok_or(Error::NotATraitMethod(c.def_id))?;
                    let method_name = strip_coq_ident(&method_name);

                    let name = format!("{trait_name}_{method_name}");
                    let spec_name = format!("{name}_base_spec");

                    let trait_incl_name = &lit_trait_spec_ref.method_trait_incl_decls[&method_name];

                    // get spec
                    let spec = signature::TX::spec_for_trait_method(
                        self.env,
                        c.def_id,
                        &name,
                        &spec_name,
                        trait_incl_name,
                        attrs.as_slice(),
                        self.type_translator(),
                        self,
                    )?;
                    let spec_ref = self.fn_spec_arena.alloc(spec);

                    // override the names in the procedure registry
                    proc_registry.override_trait_default_impl_names(c.def_id, &spec_name, trait_incl_name);

                    methods.insert(method_name, specs::traits::InstanceMethodSpec::Defined(&*spec_ref));
                } else if let ty::AssocKind::Type { .. } = c.kind {
                    // get name
                    let type_name =
                        self.env.get_assoc_item_name(c.def_id).ok_or(Error::NotAnAssocType(c.def_id))?;
                    let type_name = strip_coq_ident(&type_name);
                    let lit = specs::LiteralTyParam::new(&type_name);
                    assoc_types.push(lit);
                } else {
                    return Err(Error::AssocConstNotSupported.into());
                }
            }

            let base_instance_spec = specs::traits::InstanceSpec::new(methods);
            let decl = specs::traits::SpecDecl::new(
                lit_trait_spec_ref,
                param_scope.into(),
                assoc_types,
                base_instance_spec,
                trait_spec.attrs,
            );

            let mut scope = self.trait_decls.borrow_mut();
            scope.insert(ordered_did, decl);
            Ok(())
        };

        if let Err(err) = cont() {
            // if there is an error, rollback the registration of the shim
            let mut trait_literals = self.trait_literals.borrow_mut();
            trait_literals.remove(&ordered_did);
            trace!("leave TR::register_trait (failed)");
            return Err(err);
        }

        trace!("leave TR::register_trait");
        Ok(())
    }

    /// Register a shim with the trait registry.
    ///
    /// Errors:
    /// - NotATrait(did) if did is not a trait
    /// - TraitAlreadyExists(did) if this trait has already been registered
    pub(crate) fn register_shim(
        &self,
        did: DefId,
        spec: specs::traits::LiteralSpec,
    ) -> TraitResult<'tcx, specs::traits::LiteralSpecRef<'def>> {
        if !self.env.tcx().is_trait(did) {
            return Err(Error::NotATrait(did));
        }

        let ordered_did = OrderedDefId::new(self.env.tcx(), did);
        let mut trait_literals = self.trait_literals.borrow_mut();
        if trait_literals.get(&ordered_did).is_some() {
            return Err(Error::TraitAlreadyExists(did));
        }

        let spec = self.trait_arena.alloc(spec);
        trait_literals.insert(ordered_did, &*spec);

        Ok(spec)
    }

    /// Register a shim for a trait impl.
    pub(crate) fn register_impl_shim(
        &self,
        did: DefId,
        spec: specs::traits::LiteralImpl,
    ) -> TraitResult<'tcx, specs::traits::LiteralImplRef<'def>> {
        if !self.env.tcx().impl_is_of_trait(did) {
            return Err(Error::NotATraitImpl(did));
        }

        let ordered_did = OrderedDefId::new(self.env.tcx(), did);
        let mut impl_literals = self.impl_literals.borrow_mut();
        if impl_literals.get(&ordered_did).is_some() {
            return Err(Error::ImplAlreadyExists(did));
        }

        let spec = self.impl_arena.alloc(spec);
        impl_literals.insert(ordered_did, &*spec);

        Ok(spec)
    }

    /// Register a shim for a closure impl.
    pub(crate) fn register_closure_impl(
        &self,
        closure_did: DefId,
        closure_kind: ty::ClosureKind,
        spec: specs::traits::LiteralImpl,
        fn_lit: procedures::Meta,
    ) -> TraitResult<'tcx, specs::traits::LiteralImplRef<'def>> {
        let spec = self.impl_arena.alloc(spec);

        let mut impl_literals = self.closure_impls.borrow_mut();
        if impl_literals.get(&(closure_did, closure_kind)).is_some() {
            return Err(Error::ClosureImplAlreadyExists(closure_did, closure_kind));
        }

        impl_literals.insert((closure_did, closure_kind), (&*spec, fn_lit));

        Ok(spec)
    }

    /// Lookup a trait.
    pub(crate) fn lookup_trait(&self, trait_did: DefId) -> Option<specs::traits::LiteralSpecRef<'def>> {
        let trait_literals = self.trait_literals.borrow();
        let ordered_did = OrderedDefId::new(self.env.tcx(), trait_did);
        trait_literals.get(&ordered_did).copied()
    }

    /// Lookup the spec for an impl.
    pub(crate) fn lookup_impl(&self, impl_did: DefId) -> Option<specs::traits::LiteralImplRef<'def>> {
        let impl_literals = self.impl_literals.borrow();
        let ordered_did = OrderedDefId::new(self.env.tcx(), impl_did);
        impl_literals.get(&ordered_did).copied()
    }

    /// Lookup the spec for a closure impl.
    pub(crate) fn lookup_closure_impl(
        &self,
        closure_did: DefId,
        kind: ty::ClosureKind,
    ) -> Option<(specs::traits::LiteralImplRef<'def>, procedures::Meta)> {
        let impl_literals = self.closure_impls.borrow();
        impl_literals.get(&(closure_did, kind)).cloned()
    }

    /// Get the term for the specification of a trait impl (applied to the given arguments of the trait),
    /// as well as the list of associated types.
    pub(crate) fn get_impl_spec_term(
        &self,
        state: types::ST<'_, '_, 'def, 'tcx>,
        impl_did: DefId,
        impl_args: &[ty::GenericArg<'tcx>],
        trait_args: &[ty::GenericArg<'tcx>],
    ) -> Result<(specs::traits::SpecializedImpl<'def>, Vec<ty::Ty<'tcx>>), TranslationError<'tcx>> {
        trace!(
            "enter TR::get_impl_spec_term for impl_did={impl_did:?} impl_args={impl_args:?} trait_args={trait_args:?}"
        );
        let trait_did = self.env.tcx().impl_trait_id(impl_did);

        self.lookup_trait(trait_did).ok_or(Error::NotATrait(trait_did))?;

        let mut assoc_args = Vec::new();
        // get associated types of this impl
        // Since we know the concrete impl, we can directly resolve all of the associated types
        let items: &'tcx ty::AssocItems = self.env.tcx().associated_items(impl_did);
        let items = traits::sort_assoc_items(self.env, items);
        for it in items {
            if let ty::AssocKind::Type { .. } = it.kind {
                let item_did = it.def_id;
                let item_ty: ty::EarlyBinder<'_, ty::Ty<'tcx>> = self.env.tcx().type_of(item_did);
                let subst_ty = item_ty.instantiate(self.env.tcx(), impl_args);

                assoc_args.push(subst_ty);
            }
        }

        // check if there's a more specific impl spec
        let term = if let Some(impl_spec) = self.lookup_impl(impl_did) {
            let scope_inst =
                self.compute_scope_inst_in_state(state, impl_did, self.env.tcx().mk_args(impl_args))?;

            specs::traits::SpecializedImpl::new(impl_spec, scope_inst)
        } else {
            return Err(TranslationError::TraitTranslation(Error::UnregisteredImpl(impl_did, trait_did)));
        };

        trace!("leave TR::get_impl_spec_term");
        Ok((term, assoc_args))
    }

    pub(crate) fn compute_closure_late_bound_inst(
        &self,
        state: types::ST<'_, '_, 'def, 'tcx>,
        closure_args: ty::ClosureArgs<ty::TyCtxt<'tcx>>,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Vec<ty::Region<'tcx>> {
        let sig = closure_args.sig();
        let late_bounds_to_unify = sig.bound_vars();
        let mut late_regions = Vec::new();
        for k in late_bounds_to_unify {
            let r = k.expect_region();
            late_regions.push(r);
        }

        let inputs = sig.inputs();
        let inputs = inputs.skip_binder();
        // only argument is a tuple
        assert!(inputs.len() == 1);
        let input = inputs[0];

        let args_tuple = args[1];
        let args_tuple = args_tuple.as_type().unwrap();
        trace!(
            "compute_closure_late_bound_inst: trying to unify input={input:?} with args_tuple={args_tuple:?}"
        );

        let typing_env = state.get_typing_env(self.env.tcx());
        let mut unifier = LateBoundUnifier::new(self.env.tcx(), typing_env, late_regions.as_slice());
        unifier.map_tys(input, args_tuple);
        let (inst, _) = unifier.get_result();

        inst
    }

    pub(crate) fn compute_closure_extern_inst(
        &self,
        state: types::ST<'_, '_, 'def, 'tcx>,
        closure_did: DefId,
        closure_args: ty::ClosureArgs<ty::TyCtxt<'tcx>>,
    ) -> Vec<ty::Region<'tcx>> {
        // Also instantiate the external regions for the upvars and closure inputs
        // Important: needs to be in the same order as in `compute_closure_meta`!
        // First upvars, then the inputs.
        let mut unifier = RegionUnifier::new(self.env.tcx(), state.get_typing_env(self.env.tcx()));
        let decl_args = self.env.get_closure_args(closure_did);

        let decl_upvars_tys = decl_args.upvar_tys();
        let upvars_tys = closure_args.upvar_tys();
        unifier.map_ty_slices(decl_upvars_tys.as_slice(), upvars_tys.as_slice());

        // TODO: is skipping the late bound binder okay?
        let decl_sig = decl_args.sig();
        let decl_inputs = decl_sig.inputs();
        let decl_inputs = decl_inputs.skip_binder();
        let sig = closure_args.sig();
        let inputs = sig.inputs();
        let inputs = inputs.skip_binder();
        unifier.map_ty_slices(decl_inputs, inputs);

        let (regions, map) = unifier.get_result();
        let mut scope_inst = Vec::new();
        for r in regions {
            let r2 = map[&r];
            scope_inst.push(r2);
        }

        scope_inst
    }

    /// Get the term for the specification of a trait impl of `trait_did` for closure `closure_did` (applied
    /// to `closure_args`), as well as the list of associated types.
    pub(crate) fn get_closure_impl_spec_term(
        &self,
        state: types::ST<'_, '_, 'def, 'tcx>,
        closure_did: DefId,
        trait_did: DefId,
        closure_args: ty::ClosureArgs<ty::TyCtxt<'tcx>>,
        trait_args: ty::GenericArgsRef<'tcx>,
    ) -> Result<(specs::traits::SpecializedImpl<'def>, Vec<ty::Ty<'tcx>>), TranslationError<'tcx>> {
        let closure_kind = search::get_closure_kind_of_trait_did(self.env.tcx(), trait_did)
            .ok_or(Error::NotAClosureTrait(trait_did))?;

        let (closure_impl, _) = self
            .lookup_closure_impl(closure_did, closure_kind)
            .ok_or(Error::NotAClosureTraitImpl(closure_did, closure_kind))?;

        // compute associated type instantiation
        let mut assoc_args = Vec::new();
        if closure_kind == ty::ClosureKind::FnOnce {
            // compute the instantiation of the associated type

            let sig = closure_args.sig();
            let output = sig.output();

            // TODO: instantiate first?
            assoc_args.push(output.skip_binder());
        }

        let args = closure_args.parent_args();
        trace!(
            "get_closure_impl_spec_term: trying to find instantiation with trait_args={trait_args:?}, args={args:?}, closure_args={closure_args:?}"
        );
        let mut scope_inst =
            self.compute_scope_inst_in_state(state, closure_did, self.env.tcx().mk_args(args))?;

        // We also need to compute the lifetime instantiation, in the following order (mirroring
        // the declaration site):
        // - late bounds
        // - external regions in the upvars
        // - external regions in the inputs

        // Late bounds, by comparing the closure argument tuple type
        let inst = self.compute_closure_late_bound_inst(state, closure_args, trait_args);
        trace!("get_closure_impl_spec_term: found late bound unification {inst:?}");
        for region in inst {
            let translated_region = types::TX::translate_region(state, region)?;
            scope_inst.add_lft_param(translated_region);
        }

        let extern_inst = self.compute_closure_extern_inst(state, closure_did, closure_args);
        for r in extern_inst {
            let lft = types::TX::translate_region(state, r)?;
            scope_inst.add_lft_param(lft);
        }

        trace!("get_closure_impl_spec_term: computed scope_inst={scope_inst:?}");

        let term = specs::traits::SpecializedImpl::new(closure_impl, scope_inst);

        Ok((term, assoc_args))
    }

    /// Resolve a single trait requirement.
    pub(crate) fn resolve_trait_requirement_in_state(
        &self,
        state: types::ST<'_, '_, 'def, 'tcx>,
        trait_did: DefId,
        trait_args: ty::GenericArgsRef<'tcx>,
        below_binders: ty::Binder<'tcx, ()>,
        bound_regions: &[ty::BoundRegionKind<'tcx>],
        origin: specs::TyParamOrigin,
        assoc_constraints: &[Option<ty::Ty<'tcx>>],
    ) -> Result<ResolvedTraitReq<'tcx, 'def>, TranslationError<'tcx>> {
        let current_typing_env: ty::TypingEnv<'tcx> = state.get_typing_env(self.env.tcx());

        let trait_spec = self.lookup_trait(trait_did).ok_or(Error::NotATrait(trait_did))?;

        if let Some((impl_did, impl_args, kind)) = resolution::resolve_trait(
            self.env.tcx(),
            current_typing_env,
            trait_did,
            trait_args,
            below_binders,
        ) {
            trace!("resolved trait impl as {impl_did:?} with {trait_args:?} {kind:?}");

            // register dependency on the resolved impl
            state.register_dep_on(OrderedDefId::new(self.env.tcx(), impl_did));

            // compute the new scope including the bound regions for HRTBs introduced by this requirement
            // We are resolving the trait requirement itself under these binders
            let mut scope = state.get_param_scope();
            let binders = scope.translate_bound_regions(self.env.tcx(), bound_regions);
            let mut quantified_state = state.setup_trait_state(self.env.tcx(), scope);

            let req_inst = match kind {
                resolution::TraitResolutionKind::UserDefined => {
                    // we can resolve it to a concrete implementation of the trait that the
                    // call links up against
                    // therefore, we specialize it to the specification for this implementation
                    //
                    // This is sound, as the compiler will make the same choice when resolving
                    // the trait reference in codegen

                    let (spec_term, assoc_tys) = self.get_impl_spec_term(
                        &mut quantified_state,
                        impl_did,
                        impl_args.as_slice(),
                        trait_args.as_slice(),
                    )?;

                    // filter out the associated types which are constrained -- these are
                    // not required in our encoding
                    let assoc_tys: Vec<_> = assoc_tys
                        .into_iter()
                        .zip(assoc_constraints)
                        .filter_map(|(ty, constr)| if constr.is_some() { None } else { Some(ty) })
                        .collect();

                    specs::traits::ReqInst::new(
                        specs::traits::ReqInstSpec::Specialized(spec_term),
                        origin,
                        assoc_tys,
                        trait_spec,
                        binders,
                    )
                },
                resolution::TraitResolutionKind::Param => {
                    // Lookup in our current parameter environment to satisfy this trait
                    // assumption
                    let assoc_types_did = self.env.get_trait_assoc_types(trait_did);
                    let mut assoc_types = Vec::new();
                    for (did, constr) in assoc_types_did.into_iter().zip(assoc_constraints) {
                        // filter out the associated types which are constrained -- these are
                        // not required in our encoding
                        if constr.is_none() {
                            let alias = ty::AliasTy::new(self.env.tcx(), did, trait_args);
                            let tykind = ty::TyKind::Alias(ty::AliasTyKind::Projection, alias);
                            let ty = self.env.tcx().mk_ty_from_kind(tykind);
                            assoc_types.push(ty);
                        }
                    }
                    info!("Param associated types: {:?}", assoc_types);

                    let trait_use = quantified_state.lookup_trait_use(
                        self.env.tcx(),
                        trait_did,
                        trait_args.as_slice(),
                    )?;
                    let trait_use_ref = trait_use.trait_use;

                    trace!(
                        "need to compute HRTB instantiation for {:?}, by unifying {:?} to {:?}",
                        trait_use.bound_regions, trait_use.trait_ref.args, trait_args
                    );

                    // compute the instantiation of the quantified trait assumption in terms
                    // of the variables introduced by the trait assumption we are proving.
                    let mut unifier =
                        LateBoundUnifier::new(self.env.tcx(), current_typing_env, &trait_use.bound_regions);
                    unifier.map_generic_args(trait_use.trait_ref.args, trait_args);
                    let (inst, _) = unifier.get_result();
                    trace!("computed instantiation: {inst:?}");
                    trace!("mapping instantiation now in state={quantified_state:?}");

                    // lookup the instances in the `binders` scope for the new trait assumption
                    let mut mapped_inst = Vec::new();
                    for region in inst {
                        let translated_region = types::TX::translate_region(&mut quantified_state, region)?;
                        mapped_inst.push(translated_region);
                    }
                    let mapped_inst = specs::traits::ReqScopeInst::new(mapped_inst);
                    trace!("mapped instantiation: {mapped_inst:?}");

                    let trait_impl = specs::traits::QuantifiedImpl::new(trait_use_ref, mapped_inst);
                    specs::traits::ReqInst::new(
                        specs::traits::ReqInstSpec::Quantified(trait_impl),
                        origin,
                        assoc_types,
                        trait_spec,
                        binders,
                    )
                },
                resolution::TraitResolutionKind::Closure => {
                    let closure_did = impl_did;
                    let closure_args = impl_args.as_closure();

                    let (spec_term, assoc_tys) = self.get_closure_impl_spec_term(
                        &mut quantified_state,
                        closure_did,
                        trait_did,
                        closure_args,
                        trait_args,
                    )?;

                    // filter out the associated types which are constrained -- these are
                    // not required in our encoding
                    let assoc_tys: Vec<_> = assoc_tys
                        .into_iter()
                        .zip(assoc_constraints)
                        .filter_map(|(ty, constr)| if constr.is_some() { None } else { Some(ty) })
                        .collect();

                    specs::traits::ReqInst::new(
                        specs::traits::ReqInstSpec::Specialized(spec_term),
                        origin,
                        assoc_tys,
                        trait_spec,
                        binders,
                    )
                },
            };

            let resolved = ResolvedTraitReq {
                req_inst,
                args: impl_args,
            };

            Ok(resolved)
        } else {
            Err(TranslationError::TraitResolution(
                "could not resolve trait required for method call".to_owned(),
            ))
        }
    }

    /// Resolve the trait requirements of a [did] substituted with [params].
    /// [did] should have been resolved as much as possible,
    /// as the requirements can be different depending on which impl we consider.
    /// The requirements are sorted stably across compilations, and consistently with the
    /// declaration order.
    pub(crate) fn resolve_trait_requirements_in_state(
        &self,
        state: types::ST<'_, '_, 'def, 'tcx>,
        did: DefId,
        params: ty::GenericArgsRef<'tcx>,
        include_self: bool,
    ) -> Result<Vec<ResolvedTraitReq<'tcx, 'def>>, TranslationError<'tcx>> {
        trace!(
            "Enter resolve_trait_requirements_in_state with did={did:?} and params={params:?}, in state={state:?}"
        );

        let current_typing_env: ty::TypingEnv<'tcx> = state.get_typing_env(self.env.tcx());
        trace!("current typing env: {current_typing_env:?}");

        let target_typing_env = ty::TypingEnv::post_analysis(self.env.tcx(), did);
        trace!("target typing env {target_typing_env:?}");

        // Get the trait requirements of the target
        let target_requirements = requirements::get_trait_requirements_with_origin(self.env, did);
        trace!("non-trivial target requirements: {target_requirements:?}");
        trace!("substituting with args {:?}", params);

        // For each trait requirement, resolve to a trait spec that we can provide

        // separate direct and indirect origins
        // (indirect = surrounding scope)
        // (direct = directly on this item)
        let mut direct_trait_spec_terms = Vec::new();
        let mut indirect_trait_spec_terms = Vec::new();

        for req in &target_requirements {
            if req.is_self_in_trait_decl && !include_self {
                continue;
            }

            // substitute the args with the arg instantiation of the target at this call site
            // in order to get the args of this trait instance
            let args = req.trait_ref.args;
            let mut subst_args = Vec::new();
            for arg in args {
                let bound = ty::EarlyBinder::bind(arg);
                let bound = bound.instantiate(self.env.tcx(), params.as_slice());
                subst_args.push(bound);
            }

            // Check if the target is a method of the same trait with the same args
            // Since this happens in the same ParamEnv, this is the assumption of the trait method
            // for its own trait, so we skip it, except if instructed otherwise (by `include_self`)
            if self.env.is_method_did(did) {
                if let Some(trait_did) = self.env.tcx().trait_of_assoc(did) {
                    // Get the params of the trait we're calling
                    let calling_trait_params =
                        types::LocalTX::split_trait_method_args(self.env, trait_did, params).0;
                    if !include_self
                        && req.trait_ref.def_id == trait_did
                        && subst_args == calling_trait_params.as_slice()
                    {
                        // if they match, this is the Self assumption, so skip
                        continue;
                    }
                } else if let Some(_impl_did) = self.env.trait_impl_of_method(did) {
                    // TODO
                }
            }

            // build the new args
            let trait_args = self.env.tcx().mk_args(subst_args.as_slice());

            // try to infer an instance for this
            trace!(
                "Trying to resolve requirement def_id={:?} with args = {trait_args:?}",
                req.trait_ref.def_id
            );
            let resolved = self.resolve_trait_requirement_in_state(
                state,
                req.trait_ref.def_id,
                trait_args,
                req.binders,
                req.bound_regions.as_slice(),
                req.origin,
                req.assoc_constraints.as_slice(),
            )?;

            if resolved.req_inst.origin == specs::TyParamOrigin::Direct {
                direct_trait_spec_terms.push(resolved);
            } else {
                indirect_trait_spec_terms.push(resolved);
            }
        }
        indirect_trait_spec_terms.extend(direct_trait_spec_terms);
        let trait_spec_terms = indirect_trait_spec_terms;

        info!("collected spec terms: {trait_spec_terms:?}");

        trace!("Leave resolve_trait_requirements_in_state with trait_spec_terms={trait_spec_terms:?}");
        Ok(trait_spec_terms)
    }

    /// TODO: handle surrounding params
    pub(crate) fn compute_scope_inst_in_state_without_traits(
        &self,
        state: types::ST<'_, '_, 'def, 'tcx>,
        params_inst: ty::GenericArgsRef<'tcx>,
    ) -> Result<specs::GenericScopeInst<'def>, TranslationError<'tcx>> {
        let mut scope_inst = specs::GenericScopeInst::empty();

        // pass the args for this specific impl
        for arg in params_inst {
            if let ty::GenericArgKind::Type(ty) = arg.kind() {
                let ty = self.type_translator().translate_type_in_state(ty, state)?;
                scope_inst.add_direct_ty_param(ty);
            } else if let Some(lft) = arg.as_region() {
                let lft = types::TX::translate_region(state, lft)?;
                scope_inst.add_lft_param(lft);
            }
        }

        Ok(scope_inst)
    }

    pub(crate) fn translate_trait_req_inst_in_state(
        &self,
        state: types::ST<'_, '_, 'def, 'tcx>,
        trait_req: specs::traits::ReqInst<'def, ty::Ty<'tcx>>,
    ) -> Result<specs::traits::ReqInst<'def>, TranslationError<'tcx>> {
        let mut assoc_inst = Vec::new();
        for ty in trait_req.assoc_ty_inst {
            let ty = self.type_translator().translate_type_in_state(ty, state)?;
            assoc_inst.push(ty);
        }
        Ok(specs::traits::ReqInst::new(
            trait_req.spec,
            trait_req.origin,
            assoc_inst,
            trait_req.of_trait,
            trait_req.scope,
        ))
    }

    fn resolve_radium_trait_requirements_in_state(
        &self,
        state: types::ST<'_, '_, 'def, 'tcx>,
        did: DefId,
        params_inst: ty::GenericArgsRef<'tcx>,
    ) -> Result<Vec<specs::traits::ReqInst<'def, specs::Type<'def>>>, TranslationError<'tcx>> {
        let mut trait_reqs = Vec::new();
        for trait_req in self.resolve_trait_requirements_in_state(state, did, params_inst, false)? {
            // compute the new scope including the bound regions.
            let mut scope = state.get_param_scope();
            scope.add_trait_req_scope(&trait_req.req_inst.scope);
            let mut state = state.setup_trait_state(self.env.tcx(), scope);

            let trait_req = self.translate_trait_req_inst_in_state(&mut state, trait_req.req_inst)?;
            trait_reqs.push(trait_req);
        }
        Ok(trait_reqs)
    }

    /// Compute the instantiation of the generic scope for a particular instantiation of an object.
    /// This assumes the object to instantiate does not have late bounds.
    /// If it has late bounds, their instantiation will have to be computed separately.
    pub(crate) fn compute_scope_inst_in_state(
        &self,
        state: types::ST<'_, '_, 'def, 'tcx>,
        did: DefId,
        params_inst: ty::GenericArgsRef<'tcx>,
    ) -> Result<specs::GenericScopeInst<'def>, TranslationError<'tcx>> {
        let mut scope_inst = self.compute_scope_inst_in_state_without_traits(state, params_inst)?;

        for trait_req in self.resolve_radium_trait_requirements_in_state(state, did, params_inst)? {
            scope_inst.add_trait_requirement(trait_req);
        }

        Ok(scope_inst)
    }

    /// Get information on the trait impl for closure kind `kind` for a given closure
    /// `closure_did`.
    pub(crate) fn get_closure_trait_impl_info(
        &self,
        closure_did: DefId,
        kind: ty::ClosureKind,
        info: &procedures::ClosureImplInfo<'tcx, 'def>,
        closure_args: ty::ClosureArgs<ty::TyCtxt<'tcx>>,
    ) -> Result<specs::traits::RefInst<'def>, TranslationError<'tcx>> {
        trace!(
            "enter get_closure_trait_impl_info for closure_did={closure_did:?} and kind={kind:?} with info={info:?}"
        );
        let trait_did = search::get_closure_trait_did(self.env.tcx(), kind)
            .ok_or(Error::CouldNotFindClosureTrait(kind))?;

        let self_ty = info.self_ty;
        //self.env.tcx().mk_ty_from_kind(ty::TyKind::Closure(closure_did, closure_args.args));
        let args_ty = info.args_ty;
        //closure_args.tupled_upvars_ty();
        let trait_args: Vec<ty::GenericArg<'_>> = vec![self_ty.into(), args_ty.into()];
        let trait_args = self.env.tcx().mk_args(&trait_args);

        //let trait_args =
        //ty::TyKind::Closure((), ())
        //closure_args.capture()
        // if I want the trait args, I would first need the Self type.
        //let trait_args

        // check if we registered this impl previously
        let trait_spec_ref = self.lookup_trait(trait_did).ok_or(Error::NotATrait(trait_did))?;
        let (impl_ref, _) = self
            .lookup_closure_impl(closure_did, kind)
            .ok_or(Error::NotAClosureTraitImpl(closure_did, kind))?;

        // This should be computable directly from the closure's scope
        // - includes the generics of the parent
        // - includes the lifetimes introduced for captures
        // - includes the lifetimes for HRTBs
        // All of these are already computed by the closure body generation.
        // Let's take the same generic scope for the instance here.
        // Minus: the outer parameter!
        let generics = info.scope.clone();
        //tl.closure_lifetime

        // this should be computable from the info
        // - Self
        // - Args
        //
        // Problem: we also need to insert dep instantiation on the traits this trait depends on:
        // FnMut : FnOnce
        // Fn : FnMut
        // This should be computable by looking up the respective impls.
        // i.e. similar to the closure requirement resolution
        //
        /*
        let mut trait_inst = specs::GenericScopeInst::empty();
        trait_inst.add_direct_ty_param(info.self_ty.clone());
        trait_inst.add_direct_ty_param(info.args_ty.clone());
        if kind == ty::ClosureKind::FnMut {
            // resolve the `FnOnce` assumption

        } else if kind == ty::ClosureKind::Fn {
            // resolve the `FnMut` and `FnOnce` assumption
            // TODO: what is the order of the two requirements? this may be system-dependent...
        }
        */

        // NOTE: of course, this doesn't have bindings for the closure lifetimes.
        let parent_args = closure_args.parent_args();
        let mut param_scope =
            scope::Params::new_from_generics(self.env.tcx(), self.env.tcx().mk_args(parent_args), None);
        param_scope.add_param_env(closure_did, self.env, self.type_translator(), self)?;

        let typing_env = ty::TypingEnv::post_analysis(self.env.tcx(), closure_did);
        let state = types::TraitState::new(param_scope.clone(), typing_env, None, Some(&info.region_map));
        let mut state = types::STInner::TraitReqs(Box::new(state));

        trace!(
            "get_closure_trait_impl_info ({closure_did:?}, {kind:?}): computing trait inst in state={state:?} for args={trait_args:?}"
        );
        let trait_inst = self.compute_scope_inst_in_state(&mut state, trait_did, trait_args)?;

        // only if we're implementing FnOnce
        // - Output
        let mut assoc_types_inst = Vec::new();
        if kind == ty::ClosureKind::FnOnce {
            assoc_types_inst.push(info.tl_output_ty.clone());
        }

        // get this from Info
        let mut attrs = BTreeMap::new();
        if kind == ty::ClosureKind::FnOnce {
            attrs.insert("Params".to_owned(), specs::traits::SpecAttrInst::Term(info.params_encoded.clone()));
            attrs.insert("Pre".to_owned(), specs::traits::SpecAttrInst::Term(info.pre_encoded.clone()));
            attrs.insert("Post".to_owned(), specs::traits::SpecAttrInst::Term(info.post_encoded.clone()));
            attrs.insert(
                "PostMut".to_owned(),
                specs::traits::SpecAttrInst::Term(info.post_mut_encoded.clone()),
            );
        }

        trace!("leave get_closure_trait_impl_info for closure_did={closure_did:?} and kind={kind:?}");

        Ok(specs::traits::RefInst::new(
            trait_spec_ref,
            impl_ref,
            generics,
            trait_inst,
            assoc_types_inst,
            specs::traits::SpecAttrsInst::new(attrs),
        ))
    }

    /// Check for a specification for `derive`d traits on a trait impl for an ADT, and parse it.
    pub(crate) fn check_for_derive_trait_attrs(
        &self,
        trait_impl_did: DefId,
    ) -> Result<Option<(specs::traits::SpecAttrsInst, coq::binder::BinderList)>, TranslationError<'tcx>> {
        let subject = self.env.tcx().impl_trait_header(trait_impl_did);
        let trait_ref = subject.trait_ref.skip_binder();

        let trait_spec_ref = self.lookup_trait(trait_ref.def_id).ok_or(Error::NotATrait(trait_ref.def_id))?;

        let self_ty = trait_ref.self_ty();
        let ty::TyKind::Adt(def, _) = self_ty.kind() else {
            return Ok(None);
        };

        let impl_generics: &'tcx ty::Generics = self.env.tcx().generics_of(trait_impl_did);
        let mut param_scope = scope::Params::from(impl_generics.own_params.as_slice());
        param_scope.add_param_env(trait_impl_did, self.env, self.type_translator(), self)?;

        let adt_attrs = attrs::filter_for_tool(self.env.get_attributes(def.did()));
        let mut attr_parser = VerboseTraitImplAttrParser::new(&param_scope);

        let res = attr_parser
            .parse_derive_trait_impl_attrs(&adt_attrs)
            .map_err(|e| Error::TraitImplSpec(trait_impl_did, e))?;

        if let Ok(attrs) = res.filter_for_attrs(&trait_spec_ref.declared_attrs) {
            Ok(Some((attrs, res.context_items)))
        } else {
            Ok(None)
        }
    }

    /// Get the expected signature for a trait impl function.
    pub(crate) fn get_expected_sig_for_impl_fn(
        &self,
        did: DefId,
    ) -> Result<ty::PolyFnSig<'tcx>, TranslationError<'tcx>> {
        let impl_did = self.env.tcx().impl_of_assoc(did).ok_or(Error::NotATraitMethod(did))?;

        let subject = self.env.tcx().impl_trait_header(impl_did);
        let trait_ref = subject.trait_ref.skip_binder();

        let assoc_item = self.env.tcx().associated_item(did);
        let trait_item_did = assoc_item.trait_item_def_id().unwrap();

        let impl_ty = self.env.tcx().type_of(did).instantiate_identity();
        let ty::TyKind::FnDef(_, impl_item_params) = impl_ty.kind() else { unreachable!() };

        let item_ty = self.env.tcx().type_of(trait_item_did).instantiate_identity();
        let ty::TyKind::FnDef(_, item_params) = item_ty.kind() else { unreachable!() };

        trace!("impl_item_params = {impl_item_params:?}");
        trace!("item_params = {item_params:?}");
        trace!("trait ref args = {:?}", trait_ref.args);

        //let trait_generics = self.env.tcx().generics_of(trait_ref.def_id);
        let impl_generics = self.env.tcx().generics_of(impl_did);
        //item_params.iter().map(|x| { } );

        //ty::GenericArgKind
        let new_args = trait_ref.args.iter().chain(impl_item_params.iter().skip(impl_generics.count()));
        let method_args = self.env.tcx().mk_args_from_iter(new_args);
        trace!("method args = {method_args:?}");

        let subst_fn_ty = self.env.tcx().mk_ty_from_kind(ty::TyKind::FnDef(trait_item_did, method_args));
        let fn_sig = subst_fn_ty.fn_sig(self.env.tcx());

        Ok(fn_sig)
    }

    /// Get information on a trait implementation and create its Radium encoding.
    /// Also return the trait impls this impl depends on.
    pub(crate) fn get_trait_impl_info(
        &self,
        trait_impl_did: DefId,
    ) -> Result<
        (specs::traits::RefInst<'def>, BTreeSet<OrderedDefId>, coq::binder::BinderList),
        TranslationError<'tcx>,
    > {
        let trait_did = self.env.tcx().impl_trait_id(trait_impl_did);

        // check if we registered this impl previously
        let trait_spec_ref = self.lookup_trait(trait_did).ok_or(Error::NotATrait(trait_did))?;
        let impl_ref = self.lookup_impl(trait_impl_did).ok_or(Error::NotATraitImpl(trait_impl_did))?;

        // get all associated items
        let assoc_items: &'tcx ty::AssocItems = self.env.tcx().associated_items(trait_impl_did);
        let trait_assoc_items: &'tcx ty::AssocItems = self.env.tcx().associated_items(trait_did);

        // figure out the parameters this impl gets and make a scope
        let impl_generics: &'tcx ty::Generics = self.env.tcx().generics_of(trait_impl_did);
        let mut param_scope = scope::Params::from(impl_generics.own_params.as_slice());
        param_scope.add_param_env(trait_impl_did, self.env, self.type_translator(), self)?;

        // parse specification
        let trait_impl_attrs = attrs::filter_for_tool(self.env.get_attributes(trait_impl_did));
        let (impl_spec, context_items) = if !trait_impl_attrs.is_empty() {
            let mut attr_parser = VerboseTraitImplAttrParser::new(&param_scope);
            let res = attr_parser
                .parse_trait_impl_attrs(&trait_impl_attrs)
                .map_err(|e| Error::TraitImplSpec(trait_impl_did, e))?;
            (res.attrs, res.context_items)
        } else if super::is_derive_trait_with_no_annotations(self.env.tcx(), trait_did) == Some(true)
            || super::is_derive_trait_with_annotations(self.env.tcx(), trait_did) == Some(true)
        {
            let Some((attrs, context_items)) = self.check_for_derive_trait_attrs(trait_impl_did)? else {
                let err = error::Message::TraitTranslation(Error::TraitImplSpec(
                    trait_impl_did,
                    "No specification provided".to_owned(),
                ));
                return Err(self
                    .env
                    .tcx()
                    .dcx()
                    .span_err(self.env.tcx().def_span(trait_impl_did), err)
                    .into());
            };
            (attrs, context_items)
        } else if trait_spec_ref.declared_attrs.is_empty() {
            (specs::traits::SpecAttrsInst::new(BTreeMap::new()), coq::binder::BinderList::empty())
        } else {
            let err = error::Message::TraitTranslation(Error::TraitImplSpec(
                trait_impl_did,
                "No specification provided".to_owned(),
            ));
            return Err(self.env.tcx().dcx().span_err(self.env.tcx().def_span(trait_impl_did), err).into());
        };

        // figure out the trait ref for this
        let header = self.env.tcx().impl_trait_header(trait_impl_did);
        let trait_ref = header.trait_ref.skip_binder();

        // set up scope
        let typing_env = ty::TypingEnv::post_analysis(self.env.tcx(), trait_impl_did);
        let mut deps = BTreeSet::new();

        // using the ADT translation state to track dependencies on other impls and ADTs
        let state = types::AdtState::new(&mut deps, &param_scope, &typing_env);
        let mut state = types::STInner::TranslateAdt(state);

        let scope_inst = self.compute_scope_inst_in_state(&mut state, trait_ref.def_id, trait_ref.args)?;
        //trace!("Determined trait requirements in impl: {trait_reqs:?}");
        //trace!("get_trait_impl_info: have deps={deps:?}");

        // get instantiation for the associated types
        let mut assoc_types_inst = Vec::new();

        let items = traits::sort_assoc_items(self.env, trait_assoc_items);
        for x in items {
            if let ty::AssocKind::Type { .. } = x.kind {
                let ty_item = assoc_items
                    .filter_by_name_unhygienic_and_kind(x.ident(self.env.tcx()).name, ty::AssocTag::Type)
                    .find(|y| y.trait_item_def_id() == Some(x.def_id));

                if let Some(ty_item) = ty_item {
                    let ty_did = ty_item.def_id;
                    let ty = self.env.tcx().type_of(ty_did);
                    let translated_ty =
                        self.type_translator().translate_type_in_state(ty.skip_binder(), &mut state)?;
                    assoc_types_inst.push(translated_ty);
                } else {
                    unreachable!("trait impl does not have required item");
                }
            }
        }

        Ok((
            specs::traits::RefInst::new(
                trait_spec_ref,
                impl_ref,
                param_scope.into(),
                scope_inst,
                assoc_types_inst,
                impl_spec,
            ),
            deps,
            context_items,
        ))
    }

    /// Allocate an empty trait use reference.
    pub(crate) fn make_empty_trait_use(
        &self,
        trait_ref: ty::TraitRef<'tcx>,
        bound_regions: &[ty::BoundRegionKind<'tcx>],
    ) -> GenericTraitUse<'tcx, 'def> {
        let dummy_trait_use = RefCell::new(None);
        let trait_use = self.trait_use_arena.alloc(dummy_trait_use);

        let did = trait_ref.def_id;

        GenericTraitUse {
            did,
            trait_ref,
            trait_use,
            bound_regions: bound_regions.to_vec(),
            is_self_use: false,
        }
    }

    /// Make a trait use for the identity trait use in a trait declaration.
    pub(crate) fn make_trait_self_use(&self, trait_ref: ty::TraitRef<'tcx>) -> GenericTraitUse<'tcx, 'def> {
        let dummy_trait_use = RefCell::new(None);
        let trait_use = self.trait_use_arena.alloc(dummy_trait_use);

        let did = trait_ref.def_id;

        GenericTraitUse {
            did,
            trait_ref,
            trait_use,
            bound_regions: vec![],
            is_self_use: true,
        }
    }

    /// For a builtin trait, get the default attribute that should be assumed.
    ///
    /// Currently, we use this to assume the trivial specification for closure arguments.
    #[expect(dead_code)]
    fn get_builtin_trait_attr_override(&self, did: DefId) -> Option<String> {
        let fn_did = search::try_resolve_did(self.env.tcx(), &["core", "ops", "Fn"])?;
        if did == fn_did {
            return Some("Fn_default_attrs".to_owned());
        }
        let fnmut_did = search::try_resolve_did(self.env.tcx(), &["core", "ops", "FnMut"])?;
        if did == fnmut_did {
            return Some("FnMut_default_attrs".to_owned());
        }
        let fnonce_did = search::try_resolve_did(self.env.tcx(), &["core", "ops", "FnOnce"])?;
        if did == fnonce_did {
            return Some("FnOnce_default_attrs".to_owned());
        }

        None
    }

    /// Fills an existing trait use.
    /// Does not compute the dependencies on other traits yet,
    /// these have to be filled later.
    pub(crate) fn fill_trait_use(
        trait_use: &GenericTraitUse<'tcx, 'def>,
        trait_ref: ty::TraitRef<'tcx>,
        spec_ref: specs::traits::LiteralSpecRef<'def>,
        is_used_in_self_trait: bool,
        assoc_ty_constraints: Vec<Option<specs::Type<'def>>>,
        origin: specs::TyParamOrigin,
    ) {
        trace!("Enter fill_trait_use with trait_ref = {trait_ref:?}, spec_ref = {spec_ref:?}");

        // compute an override for the attributes assumed here
        // This does not include user annotations (e.g., on functions), as the attributes for those
        // are not available here.
        //let attr_override = self.get_builtin_trait_attr_override(trait_ref.def_id);
        let attr_override = None;

        // create a name for this instance by including the args
        let mangled_base = types::mangle_name_with_args(&spec_ref.name, trait_ref.args.as_slice());
        let spec_use = specs::traits::LiteralSpecUse::new(
            spec_ref,
            // dummy for now
            specs::traits::ReqScope::empty(),
            // dummy for now
            specs::GenericScopeInst::empty(),
            attr_override,
            mangled_base,
            is_used_in_self_trait,
            assoc_ty_constraints,
            origin,
        );

        let mut trait_ref = trait_use.trait_use.borrow_mut();
        trait_ref.replace(spec_use);

        trace!(
            "Leave fill_trait_use with trait_ref = {trait_ref:?}, spec_ref = {spec_ref:?} with trait_use = {trait_use:?}"
        );
    }

    /// Finalize a trait use by computing the dependencies on other traits.
    pub(crate) fn finalize_trait_use(
        &self,
        trait_use: &GenericTraitUse<'tcx, 'def>,
        scope: &scope::Params<'tcx, 'def>,
        typing_env: ty::TypingEnv<'tcx>,
        //state: types::ST<'_, '_, 'def, 'tcx>,
        trait_ref: ty::TraitRef<'tcx>,
    ) -> Result<(), TranslationError<'tcx>> {
        trace!("enter finalize_trait_use for {:?}", trait_use.did);
        trace!("current scope={scope:?}");

        let mut scope = scope.clone();
        let quantified_regions = scope.translate_bound_regions(self.env.tcx(), &trait_use.bound_regions);
        trace!("new trait scope={scope:?}");
        //let mut state = state.setup_trait_state(self.env.tcx(), scope);
        let mut state =
            types::STInner::TraitReqs(Box::new(types::TraitState::new(scope, typing_env, None, None)));

        let mut scope_inst = self.compute_scope_inst_in_state_without_traits(&mut state, trait_ref.args)?;

        let trait_reqs =
            self.resolve_radium_trait_requirements_in_state(&mut state, trait_ref.def_id, trait_ref.args)?;
        trace!("finalize_trait_use for {:?}: determined trait requirements: {trait_reqs:?}", trait_use.did);

        for trait_req in trait_reqs {
            scope_inst.add_trait_requirement(trait_req);
        }

        let mut trait_use_ref = trait_use.trait_use.borrow_mut();
        let lit_trait_use = trait_use_ref.as_mut().unwrap();

        lit_trait_use.trait_inst = scope_inst;
        lit_trait_use.scope = quantified_regions;

        trace!("enter finalize_trait_use for {:?}", trait_use.did);

        Ok(())
    }
}

/// Unifier to compute the instantiation of given binders by comparing the uninstantiated and the
/// instantiated terms.
pub(crate) struct LateBoundUnifier<'tcx, 'a> {
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    binders_to_unify: &'a [ty::BoundRegionKind<'tcx>],
    instantiation: BTreeMap<usize, ty::Region<'tcx>>,
    early_instantiation: BTreeMap<usize, ty::Region<'tcx>>,
}
impl<'tcx, 'a> LateBoundUnifier<'tcx, 'a> {
    pub(crate) const fn new(
        tcx: ty::TyCtxt<'tcx>,
        typing_env: ty::TypingEnv<'tcx>,
        binders_to_unify: &'a [ty::BoundRegionKind<'tcx>],
    ) -> Self {
        Self {
            tcx,
            typing_env,
            binders_to_unify,
            instantiation: BTreeMap::new(),
            early_instantiation: BTreeMap::new(),
        }
    }

    pub(crate) fn get_result(mut self) -> (Vec<ty::Region<'tcx>>, BTreeMap<usize, ty::Region<'tcx>>) {
        trace!("computed latebound unification map {:?}", self.instantiation);
        let mut res = Vec::new();
        for i in 0..self.binders_to_unify.len() {
            let r = self.instantiation.remove(&i).unwrap();
            res.push(r);
        }
        (res, self.early_instantiation)
    }
}
impl<'tcx> RegionBiFolder<'tcx> for LateBoundUnifier<'tcx, '_> {
    fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn typing_env(&self) -> &ty::TypingEnv<'tcx> {
        &self.typing_env
    }

    fn map_regions(&mut self, r1: ty::Region<'tcx>, r2: ty::Region<'tcx>) {
        if let ty::RegionKind::ReBound(_, b1) = r1.kind() {
            trace!("trying to unify region {r1:?} with {r2:?}");
            // only unify if this is in the range of binders to unify
            let index1 = b1.var.index();
            if index1 < self.binders_to_unify.len() {
                if let Some(r1_l) = self.instantiation.get(&index1) {
                    assert!(*r1_l == r2);
                } else {
                    self.instantiation.insert(index1, r2);
                }
            }
        } else if let ty::RegionKind::ReEarlyParam(e1) = r1.kind() {
            trace!("trying to unify region {r1:?} with {r2:?}");
            let idx = e1.index as usize;
            if let Some(r1_l) = self.early_instantiation.get(&idx) {
                assert!(*r1_l == r2);
            } else {
                self.early_instantiation.insert(idx, r2);
            }
        }
    }
}

/// Unifier to compute a mapping between two sets of Polonius variables by comparing two terms.
pub(crate) struct RegionUnifier<'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    typing_env: ty::TypingEnv<'tcx>,
    instantiation: BTreeMap<ty::RegionVid, ty::Region<'tcx>>,
    term_order: Vec<ty::RegionVid>,
    ignore_aliases: bool,
}
impl<'tcx> RegionUnifier<'tcx> {
    pub(crate) const fn new(tcx: ty::TyCtxt<'tcx>, typing_env: ty::TypingEnv<'tcx>) -> Self {
        Self {
            tcx,
            typing_env,
            instantiation: BTreeMap::new(),
            term_order: Vec::new(),
            ignore_aliases: false,
        }
    }

    pub(crate) const fn ignore_aliases(&mut self) {
        self.ignore_aliases = true;
    }

    pub(crate) fn get_result(self) -> (Vec<ty::RegionVid>, BTreeMap<ty::RegionVid, ty::Region<'tcx>>) {
        trace!("computed region unification map {:?}", self.instantiation);
        (self.term_order, self.instantiation)
    }
}
impl<'tcx> RegionBiFolder<'tcx> for RegionUnifier<'tcx> {
    fn tcx(&self) -> ty::TyCtxt<'tcx> {
        self.tcx
    }

    fn typing_env(&self) -> &ty::TypingEnv<'tcx> {
        &self.typing_env
    }

    fn examine_ty(&mut self, ty1: ty::Ty<'tcx>, ty2: ty::Ty<'tcx>) -> bool {
        if !self.ignore_aliases {
            return true;
        }

        !matches!(ty1.kind(), ty::TyKind::Alias(_, _)) && !matches!(ty2.kind(), ty::TyKind::Alias(_, _))
    }

    fn map_regions(&mut self, r1: ty::Region<'tcx>, r2: ty::Region<'tcx>) {
        if let ty::RegionKind::ReVar(v1) = r1.kind() {
            trace!("trying to unify region {r1:?} with {r2:?}");

            if let btree_map::Entry::Vacant(e) = self.instantiation.entry(v1) {
                e.insert(r2);
                self.term_order.push(v1);
            }
        }
        // otherwise, this can be a late-bound region, which we don't care to unify here.
    }
}
