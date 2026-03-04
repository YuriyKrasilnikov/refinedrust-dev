// © 2024, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! A wrapper around a `translator::TX` for the case we are translating the body of a function.

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap};

use log::{info, trace};
use radium::{code, coq, lang, specs};
use rr_rustc_interface::abi;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;
use rr_rustc_interface::middle::ty::TypeFolder as _;
use rr_rustc_interface::type_ir::TypeFoldable as _;

use crate::base::*;
use crate::environment::borrowck::facts;
use crate::environment::{Environment, polonius_info};
use crate::regions::TyRegionCollectFolder;
use crate::regions::region_bi_folder::RegionBiFolder as _;
use crate::traits;
use crate::traits::registry::ResolvedTraitReq;
use crate::traits::resolution;
use crate::types::translator::{FunctionState, STInner, TX};
use crate::types::tyvars::TyVarFolder;
use crate::types::{self, scope};

/// Information we compute when calling a function from another function.
/// Determines how to specialize the callee's generics in our spec assumption.
#[derive(Debug)]
pub(crate) struct AbstractedGenerics<'def> {
    /// the scope with new generics to quantify over for the function's specialized spec
    pub scope: specs::GenericScope<'def, specs::traits::LiteralSpecUseRef<'def>>,
    /// instantiations for the specialized spec hint
    pub callee_lft_param_inst: Vec<specs::Lft>,
    pub callee_ty_param_inst: Vec<specs::Type<'def>>,
    /// num latebounds
    pub num_of_latebounds: usize,
    /// instantiations for the function use
    pub fn_scope_inst: specs::GenericScopeInst<'def>,
}

/// Type translator bundling the function scope
pub(crate) struct LocalTX<'def, 'tcx> {
    pub translator: &'def TX<'def, 'tcx>,
    pub scope: RefCell<FunctionState<'tcx, 'def>>,
}

impl<'def, 'tcx> LocalTX<'def, 'tcx> {
    pub(crate) const fn new(translator: &'def TX<'def, 'tcx>, scope: FunctionState<'tcx, 'def>) -> Self {
        Self {
            translator,
            scope: RefCell::new(scope),
        }
    }

    /// Translate a MIR type to the Radium syntactic type we need when storing an element of the type,
    /// substituting all generics.
    pub(crate) fn translate_type_to_syn_type(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> Result<lang::SynType, TranslationError<'tcx>> {
        let mut scope = self.scope.borrow_mut();
        let mut state = STInner::InFunction(&mut scope);
        self.translator.translate_type_to_syn_type(ty, &mut state)
    }

    /// Translate a region in the scope of the current function.
    pub(crate) fn translate_region(
        &self,
        region: ty::Region<'tcx>,
    ) -> Result<specs::Lft, TranslationError<'tcx>> {
        let mut scope = self.scope.borrow_mut();
        let mut scope = STInner::InFunction(&mut scope);
        TX::translate_region(&mut scope, region)
    }

    /// Translate a Polonius region variable in the scope of the current function.
    pub(crate) fn translate_region_var(
        &self,
        region: facts::Region,
    ) -> Result<specs::Lft, TranslationError<'tcx>> {
        let mut scope = self.scope.borrow_mut();
        let scope = STInner::InFunction(&mut scope);
        scope.lookup_polonius_var(region)
    }

    /// Translate type.
    pub(crate) fn translate_type(
        &self,
        ty: ty::Ty<'tcx>,
    ) -> Result<specs::Type<'def>, TranslationError<'tcx>> {
        let mut scope = self.scope.borrow_mut();
        self.translator.translate_type(ty, &mut scope)
    }

    /// Assumes that the current state of the ADT registry is consistent, i.e. we are not currently
    /// registering a new ADT.
    pub(crate) fn generate_structlike_use(
        &self,
        ty: ty::Ty<'tcx>,
        variant: Option<abi::VariantIdx>,
    ) -> Result<Option<specs::types::LiteralUse<'def>>, TranslationError<'tcx>> {
        let mut scope = self.scope.borrow_mut();
        self.translator.generate_structlike_use(ty, variant, &mut scope)
    }

    /// Assumes that the current state of the ADT registry is consistent, i.e. we are not currently
    /// registering a new ADT.
    pub(crate) fn generate_enum_use(
        &self,
        adt_def: ty::AdtDef<'tcx>,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<specs::types::LiteralUse<'def>, TranslationError<'tcx>> {
        let mut scope = self.scope.borrow_mut();
        self.translator.generate_enum_use(adt_def, args, &mut scope)
    }

    /// Generate a struct use.
    /// Returns None if this should be unit.
    /// Assumes that the current state of the ADT registry is consistent, i.e. we are not currently
    /// registering a new ADT.
    pub(crate) fn generate_struct_use(
        &self,
        variant_id: DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<Option<specs::types::LiteralUse<'def>>, TranslationError<'tcx>> {
        let mut scope = self.scope.borrow_mut();
        self.translator.generate_struct_use(variant_id, args, &mut scope)
    }

    /// Generate a struct use.
    /// Returns None if this should be unit.
    pub(crate) fn generate_enum_variant_use(
        &self,
        variant_id: DefId,
        args: ty::GenericArgsRef<'tcx>,
    ) -> Result<specs::types::LiteralUse<'def>, TranslationError<'tcx>> {
        let mut scope = self.scope.borrow_mut();
        self.translator.generate_enum_variant_use(variant_id, args, &mut scope)
    }

    /// Make a tuple use.
    /// Hack: This does not take the translation state but rather a direct reference to the tuple
    /// use map so that we can this function when parsing closure specifications.
    pub(crate) fn make_tuple_use(
        &self,
        translated_tys: Vec<specs::Type<'def>>,
        uses: Option<&mut HashMap<Vec<lang::SynType>, specs::types::LiteralUse<'def>>>,
    ) -> specs::Type<'def> {
        self.translator.make_tuple_use(translated_tys, uses)
    }

    pub(crate) fn generate_tuple_use<F>(
        &self,
        tys: F,
    ) -> Result<specs::types::LiteralUse<'def>, TranslationError<'tcx>>
    where
        F: IntoIterator<Item = ty::Ty<'tcx>>,
    {
        let mut scope = self.scope.borrow_mut();
        self.translator.generate_tuple_use(tys, &mut STInner::InFunction(&mut scope))
    }

    /// Format the Coq representation of an atomic region.
    pub(crate) fn format_atomic_region(&self, r: polonius_info::AtomicRegion) -> coq::Ident {
        let scope = self.scope.borrow();
        scope.lifetime_scope.translate_atomic_region(r)
    }

    /// Split the params of a trait method into params of the trait and params of the method
    /// itself.
    pub(crate) fn split_trait_method_args(
        env: &Environment<'tcx>,
        trait_did: DefId,
        ty_params: ty::GenericArgsRef<'tcx>,
    ) -> (ty::GenericArgsRef<'tcx>, ty::GenericArgsRef<'tcx>) {
        // split args
        let trait_generics: &'tcx ty::Generics = env.tcx().generics_of(trait_did);
        let trait_generic_count = trait_generics.own_params.len();

        let trait_args = &ty_params.as_slice()[..trait_generic_count];
        let method_args = &ty_params.as_slice()[trait_generic_count..];

        (env.tcx().mk_args(trait_args), env.tcx().mk_args(method_args))
    }

    /// Register a procedure use of a trait method.
    /// The given `ty_params` need to include the args to both the trait and the method.
    /// Returns:
    /// - the parameter name for the method loc
    /// - the spec term for the method spec
    /// - the arguments of the method
    pub(crate) fn register_use_trait_procedure(
        &self,
        env: &Environment<'tcx>,
        trait_method_did: DefId,
        ty_params: ty::GenericArgsRef<'tcx>,
    ) -> Result<
        (
            String,
            (code::UsedProcedureSpec<'def>, specs::traits::ReqScope, specs::traits::ReqScopeInst),
            BTreeMap<specs::Lft, usize>,
            ty::GenericArgsRef<'tcx>,
        ),
        TranslationError<'tcx>,
    > {
        let trait_did = env
            .tcx()
            .trait_of_assoc(trait_method_did)
            .ok_or(traits::Error::NotATrait(trait_method_did))?;

        // get name of the method
        let method_name = env.get_assoc_item_name(trait_method_did).unwrap();

        // split args
        let (trait_args, method_args) = Self::split_trait_method_args(env, trait_did, ty_params);

        // restrict the scope of the borrow
        let (trait_use_ref, bound_regions_inst, mapped_early_regions) = {
            let mut scope = self.scope.borrow_mut();
            let entry = scope.generic_scope.trait_scope().lookup_trait_use(
                env.tcx(),
                trait_did,
                trait_args.as_slice(),
            )?;
            let trait_use_ref = entry.trait_use;

            let typing_env = ty::TypingEnv::post_analysis(env.tcx(), scope.did);

            // compute the instantiation of this trait use's params by unifying the args
            // this instantiation will be used as the instantiation hint in the function
            let mut unifier =
                traits::registry::LateBoundUnifier::new(env.tcx(), typing_env, &entry.bound_regions);
            unifier.map_generic_args(entry.trait_ref.args, trait_args);
            let (bound_regions_inst, early_regions_inst) = unifier.get_result();

            // we use the constraints between early regions to restore some information that
            // Polonius doesn't get
            let mut mapped_early_regions = BTreeMap::new();
            for (early, polonius) in early_regions_inst {
                let mut scope = STInner::InFunction(&mut scope);
                let polonius_lft = TX::translate_region(&mut scope, polonius)?;
                mapped_early_regions.insert(polonius_lft, early);
            }

            //trace!("register_use_trait_procedure: mapped {:?} with {:?}; early_regions_inst =
            // {mapped_early_regions:?}", entry.trait_ref.args, trait_args);

            (trait_use_ref, bound_regions_inst, mapped_early_regions)
        };

        let mut mapped_inst = Vec::new();
        for region in bound_regions_inst {
            let translated_region = self.translate_region(region)?;
            mapped_inst.push(translated_region);
        }
        let mapped_inst = specs::traits::ReqScopeInst::new(mapped_inst);
        trace!("using trait procedure with mapped instantiation: {mapped_inst:?}");

        let trait_spec_use = trait_use_ref.borrow();
        let trait_spec_use = trait_spec_use.as_ref().unwrap();

        let lifted_scope = trait_spec_use.scope.clone();
        let quantified_impl =
            specs::traits::QuantifiedImpl::new(trait_use_ref, lifted_scope.identity_instantiation());

        // get spec. the spec takes the generics of the method as arguments
        let method_spec_term = code::UsedProcedureSpec::TraitMethod(quantified_impl, method_name.clone());

        let mangled_method_name =
            types::mangle_name_with_args(&strip_coq_ident(&method_name), method_args.as_slice());
        let method_loc_name = trait_spec_use.make_loc_name(&mangled_method_name);

        Ok((
            method_loc_name,
            (method_spec_term, lifted_scope, mapped_inst),
            mapped_early_regions,
            method_args,
        ))
    }

    /// Abstract over the generics of a function and partially instantiate them.
    /// Assumption: `trait_reqs` is appropriately sorted, i.e. surrounding requirements come first.
    /// `with_surrounding_deps` determines whether we should distinguish surrounding and direct
    /// params.
    pub(crate) fn get_generic_abstraction_for_procedure(
        &self,
        callee_did: DefId,
        method_params: ty::GenericArgsRef<'tcx>,
        late_bounds: &[ty::BoundVariableKind<'tcx>],
        trait_reqs: Vec<ResolvedTraitReq<'tcx, 'def>>,
        with_surrounding_deps: bool,
    ) -> Result<AbstractedGenerics<'def>, TranslationError<'tcx>> {
        trace!(
            "enter get_generic_abstraction_for_procedure with callee_did={callee_did:?} and method_params={method_params:?}"
        );

        // STEP 1: get all the regions and type variables appearing in the instantiation of generics
        let mut tyvar_folder = TyVarFolder::new(self.translator.env());
        let mut lft_folder = TyRegionCollectFolder::new(self.translator.env().tcx());
        // HACK(see #32): We typically don't want lifetimes which just appear in the closure input/output
        // signature, but not in the closure upvars, since these lifetimes often are locally
        // universally quantified.
        lft_folder.ignore_closure_args(true);
        // also count the number of (early) regions of the function itself
        let mut num_param_regions = 0;

        let mut callee_lft_param_inst: Vec<specs::Lft> = Vec::new();
        let mut callee_ty_param_inst = Vec::new();
        for v in method_params {
            if let Some(ty) = v.as_type() {
                tyvar_folder.fold_ty(ty);
                lft_folder.fold_ty(ty);
            }
            if let Some(region) = v.as_region() {
                num_param_regions += 1;

                let lft_name = self.translate_region(region)?;
                callee_lft_param_inst.push(lft_name);
            }
        }
        // also find generics in the associated types
        for req in &trait_reqs {
            for ty in &req.req_inst.assoc_ty_inst {
                tyvar_folder.fold_ty(*ty);
                lft_folder.fold_ty(*ty);
            }
        }

        // also find generics in trait requirement impl args.
        // HACK(see #32): If this function has any closure requirements, this will contain the args of the
        // closure requirement (but not discernable as a closure ty), so we will correctly abstract
        // the closure argument lifetimes.
        for req in &trait_reqs {
            req.args.fold_with(&mut lft_folder);
            req.args.fold_with(&mut tyvar_folder);
        }

        let (tyvars, projections) = tyvar_folder.get_result();
        let regions = lft_folder.get_regions();

        // the new scope that we quantify over in the assumed spec
        let mut scope = specs::GenericScope::empty();
        // instantiations for the function spec's parameters, using variables quantified in `scope`
        let mut fn_inst = specs::GenericScopeInst::empty();

        // STEP 2: Bind & instantiate lifetimes

        // Re-bind the function's (early) lifetime parameters
        for i in 0..num_param_regions {
            let lft_name = coq::Ident::new(&format!("ulft_{}", i));
            scope.add_lft_param(specs::LftParam::new(
                lft_name.clone(),
                specs::LftParamOrigin::FunctionRebound,
            ));
            fn_inst.add_lft_param(lft_name);
        }

        // Bind the additional lifetime parameters which are mentioned as part of the instantiation
        // of type parameters and associated types.
        // All of these are turned into quantified lifetimes.
        for (next_lft, region) in (num_param_regions..).zip(regions) {
            // Use the name the region has inside the function as the binder name, so that the
            // names work out when translating the types below
            let lft_name = self
                .translate_region_var(region)
                .unwrap_or_else(|_| coq::Ident::new(&format!("ulft_{}", next_lft)));
            scope.add_lft_param(specs::LftParam::new(
                lft_name.clone(),
                specs::LftParamOrigin::FunctionRebound,
            ));

            // Note: since these are not formal parameters of the function, we do not add them to
            // `fn_inst`.

            callee_lft_param_inst.push(lft_name);
        }

        // Also need to re-bind late bound regions of the function.
        for (late_bound_idx, late_bound) in late_bounds.iter().enumerate() {
            match late_bound {
                ty::BoundVariableKind::Region(r) => {
                    let name = r.get_name(self.translator.env().tcx()).map_or_else(
                        || coq::Ident::new(&format!("late_lft_{}", late_bound_idx)),
                        |x| coq::Ident::new(&format!("lft_{}", x)),
                    );

                    // push this to the context.
                    scope.add_lft_param(specs::LftParam::new(
                        name.clone(),
                        specs::LftParamOrigin::FunctionRebound,
                    ));
                    fn_inst.add_lft_param(name);

                    // Note: we cannot add an instantiation for the callee_lft_param_inst.
                    // We do not know the concrete instantiation by just looking at the
                    // function pointer.
                },
                _ => {
                    unimplemented!("late bound is not a region");
                },
            }
        }

        // STEP 3: Bind type parameters

        // Bind the generics we use.
        for param in &tyvars {
            // NOTE: this should have the same name as the using occurrences
            let lit = specs::LiteralTyParam::new(param.name.as_str());
            callee_ty_param_inst.push(specs::Type::LiteralParam(lit.clone()));
            scope.add_ty_param(lit);
        }
        // Also bind associated types of the trait requirements of the function (they are translated as
        // generics)
        for req in &trait_reqs {
            for ty in &req.req_inst.assoc_ty_inst {
                // we should check if it there is a parameter in the current scope for it
                let translated_ty = self.translate_type(*ty)?;
                if let specs::Type::LiteralParam(mut lit) = translated_ty {
                    lit.set_origin(specs::TyParamOrigin::Direct);
                    //lit.set_origin(req.origin);

                    scope.add_ty_param(lit.clone());
                    callee_ty_param_inst.push(specs::Type::LiteralParam(lit.clone()));
                }
            }
        }
        // Also bind surrounding associated types we use
        for alias_ty in projections {
            let env = self.translator.env();
            let trait_did = env.tcx().parent(alias_ty.def_id);
            let param_scope = self.scope.borrow().make_params_scope();
            let entry = param_scope.trait_scope().lookup_trait_use(env.tcx(), trait_did, alias_ty.args)?;
            let assoc_type = entry.get_associated_type_use(env, alias_ty.def_id)?;
            if let specs::Type::LiteralParam(mut lit) = assoc_type {
                lit.set_origin(specs::TyParamOrigin::Direct);
                scope.add_ty_param(lit.clone());
                callee_ty_param_inst.push(specs::Type::LiteralParam(lit.clone()));
            }
        }

        // STEP 4: Instantiate type parameters

        // NOTE: we need to be careful with the order here.
        // - the method_params are all the generics the function has.
        // - the trait_reqs are also all the trait requirements the function has
        // We need to distinguish these between direct and surrounding, as our encoding does that.
        //
        // TODO: probably we should make the same distinction also for lifetimes?
        let num_surrounding_params =
            scope::Params::determine_number_of_surrounding_params(callee_did, self.translator.env().tcx());
        info!("num_surrounding_params={num_surrounding_params:?}, method_params={method_params:?}");

        // figure out instantiation for the function's generics
        // first the surrounding parameters
        if with_surrounding_deps {
            for v in &method_params.as_slice()[..num_surrounding_params] {
                if let Some(ty) = v.as_type() {
                    let translated_ty = self.translate_type(ty)?;
                    fn_inst.add_surrounding_ty_param(translated_ty);
                }
            }

            // now the direct parameters
            for v in &method_params.as_slice()[num_surrounding_params..] {
                if let Some(ty) = v.as_type() {
                    let translated_ty = self.translate_type(ty)?;
                    fn_inst.add_direct_ty_param(translated_ty);
                }
            }
        } else {
            // just instantiate all the params
            for v in method_params {
                if let Some(ty) = v.as_type() {
                    let translated_ty = self.translate_type(ty)?;
                    fn_inst.add_direct_ty_param(translated_ty);
                }
            }
        }

        // STEP 5: add trait requirements
        for req in trait_reqs {
            // translate type in scope with HRTB binders
            let mut scope = self.scope.borrow_mut();

            let tcx = self.translator.env().tcx();

            let mut params = scope.make_params_scope();
            params.add_trait_req_scope(&req.req_inst.scope);
            let sc = STInner::InFunction(&mut scope);
            let mut state = sc.setup_trait_state(tcx, params);

            // TODO: we need to lift up the HRTB lifetimes here.

            let mut assoc_inst = Vec::new();
            for ty in req.req_inst.assoc_ty_inst {
                let ty = TX::translate_type_in_state(self.translator, ty, &mut state)?;
                assoc_inst.push(ty);
            }
            let trait_req = specs::traits::ReqInst::new(
                req.req_inst.spec,
                req.req_inst.origin,
                assoc_inst,
                req.req_inst.of_trait,
                req.req_inst.scope,
            );
            fn_inst.add_trait_requirement(trait_req);
        }

        info!("Abstraction scope: {:?}", scope);
        info!("Fn instantiation: {fn_inst:?}");
        info!("Callee instantiation: {:?}, {:?}", callee_lft_param_inst, callee_ty_param_inst);

        let res = AbstractedGenerics {
            scope,
            callee_lft_param_inst,
            callee_ty_param_inst,
            num_of_latebounds: late_bounds.len(),
            fn_scope_inst: fn_inst,
        };

        Ok(res)
    }
}

/// Normalize a type in the given function environment.
pub(crate) fn normalize_in_function<'tcx, T>(
    function_did: DefId,
    tcx: ty::TyCtxt<'tcx>,
    ty: T,
) -> Result<T, TranslationError<'tcx>>
where
    T: ty::TypeFoldable<ty::TyCtxt<'tcx>>,
{
    let typing_env = ty::TypingEnv::post_analysis(tcx, function_did);
    info!("Normalizing type {ty:?} in env {typing_env:?}");

    resolution::normalize_type(tcx, typing_env, ty)
        .map_err(|e| TranslationError::TraitResolution(format!("normalization error: {:?}", e)))
}
