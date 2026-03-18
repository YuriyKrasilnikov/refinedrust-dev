// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Part of the function translation responsible for translating the signature and specification.

use std::collections::HashMap;

use log::{info, trace};
use radium::{code, coq, specs};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::{mir, ty};
use rr_rustc_interface::{hir, span};
use typed_arena::Arena;

use crate::base::*;
use crate::body::translation;
use crate::environment::dump_borrowck_info;
use crate::environment::polonius_info::PoloniusInfo;
use crate::environment::procedure::Procedure;
use crate::regions::inclusion_tracker::InclusionTracker;
use crate::regions::region_bi_folder::RegionBiFolder as _;
use crate::spec_parsers::verbose_function_spec_parser::{
    ClosureMetaInfo, ClosureSpecInfo, FunctionRequirements, FunctionSpecParser as _,
    VerboseFunctionSpecParser,
};
use crate::traits::registry::{self, RegionUnifier};
use crate::{consts, environment, procedures, regions, types};

pub(crate) struct TX<'a, 'def, 'tcx> {
    tcx: ty::TyCtxt<'tcx>,
    /// this needs to be annotated with the right borrowck things
    proc: &'def Procedure<'tcx>,
    /// the Caesium function buildder
    translated_fn: code::FunctionBuilder<'def>,
    /// tracking lifetime inclusions for the generation of lifetime inclusions
    inclusion_tracker: InclusionTracker<'a, 'tcx>,

    /// registry of other procedures
    procedure_registry: &'a procedures::Scope<'tcx, 'def>,
    /// registry of consts
    const_registry: &'a consts::Scope<'def>,
    /// attributes on this function
    attrs: &'a [&'a hir::AttrItem],
    /// polonius info for this function
    info: &'a PoloniusInfo<'a, 'tcx>,
    /// translator for types
    ty_translator: types::LocalTX<'def, 'tcx>,
    /// trait registry in the current scope
    trait_registry: &'def registry::TR<'tcx, 'def>,
    /// argument types (from the signature, with generics substituted)
    inputs: Vec<ty::Ty<'tcx>>,
    /// accumulator for non-SeqCst atomic operation spans (crate-level summary warning)
    non_sc_atomic_spans: &'a mut Vec<span::Span>,
}

#[expect(clippy::multiple_inherent_impl)]
impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Generate a spec for a trait method.
    pub(crate) fn spec_for_trait_method(
        tcx: ty::TyCtxt<'tcx>,
        proc_did: DefId,
        name: &str,
        spec_name: &str,
        trait_req_incl_name: &str,
        attrs: &'a [&'a hir::AttrItem],
        ty_translator: &'def types::TX<'def, 'tcx>,
        trait_registry: &'def registry::TR<'tcx, 'def>,
    ) -> Result<specs::functions::Spec<'def, specs::functions::InnerSpec<'def>>, TranslationError<'tcx>> {
        // use a dummy name as we're never going to use the code.
        let mut translated_fn = code::FunctionBuilder::new(name, "dummy", spec_name, trait_req_incl_name);

        let ty: ty::EarlyBinder<'_, ty::Ty<'tcx>> = tcx.type_of(proc_did);
        let ty = ty.instantiate_identity();
        // substs are the generic args of this function (including lifetimes)
        // sig is the function signature
        let sig = match ty.kind() {
            ty::TyKind::FnDef(_def, _args) => {
                assert!(ty.is_fn());
                ty.fn_sig(tcx)
            },
            _ => panic!("can not handle non-fns"),
        };
        info!("Function signature: {:?}", sig);

        let params = Self::get_proc_ty_params(tcx, proc_did);
        info!("Function generic args: {:?}", params);

        let num_late_bounds = sig.bound_vars().len();
        let num_early_bounds =
            params.iter().filter(|x| matches!(x.kind(), ty::GenericArgKind::Lifetime(_))).count();
        // + 1 for static, + 1 for function lifetime
        let num_universal_regions = num_late_bounds + num_early_bounds + 2;
        let (inputs, output, region_substitution) = regions::init::replace_fnsig_args_with_polonius_vars(
            tcx,
            params,
            proc_did,
            num_universal_regions,
            num_early_bounds,
            num_late_bounds,
            sig,
        );
        info!("inputs: {:?}, output: {:?}", inputs, output);

        let type_scope = Self::setup_local_scope(
            tcx,
            ty_translator,
            trait_registry,
            proc_did,
            params.as_slice(),
            &mut translated_fn,
            region_substitution,
            None,
        )?;
        let type_translator = types::LocalTX::new(ty_translator, type_scope);

        // get argument names
        let arg_names: &'tcx [Option<span::symbol::Ident>] = tcx.fn_arg_idents(proc_did);
        let arg_names: Vec<_> = arg_names
            .iter()
            .enumerate()
            .map(|(i, maybe_name)| maybe_name.map_or_else(|| format!("_arg_{i}"), |x| x.as_str().to_owned()))
            .collect();
        info!("arg names: {arg_names:?}");

        let spec_builder = if attrs.is_empty()
            && crate::is_method_on_atomic_type(tcx, proc_did)
        {
            Self::auto_infer_atomic_method_spec(
                tcx, proc_did, &type_translator, inputs.as_slice(), output,
            )?
        } else {
            Self::process_attrs(
                attrs,
                &type_translator,
                &mut translated_fn,
                &arg_names,
                inputs.as_slice(),
                output,
            )?
        };
        translated_fn.add_function_spec_from_builder(spec_builder);

        translated_fn.try_into().map_err(TranslationError::AttributeError)
    }

    /// Compute meta information for a closure we are processing.
    /// Adds all universal regions for closure captures to the region map.
    /// Returns the upvar types with normalized regions as well as the optional region for the
    /// capture.
    fn compute_closure_meta(
        clos_args: ty::ClosureArgs<ty::TyCtxt<'tcx>>,
        closure_arg: &mir::LocalDecl<'tcx>,
        input_tuple_ty: ty::Ty<'tcx>,
        region_substitution: &mut regions::EarlyLateRegionMap<'def>,
        info: &PoloniusInfo<'def, 'tcx>,
        tcx: ty::TyCtxt<'tcx>,
    ) -> (ty::Ty<'tcx>, Vec<ty::Ty<'tcx>>, ty::Ty<'tcx>, Option<specs::LftParam>) {
        // Process the lifetime parameters that come from the captures
        // Sideeffect: adds the regions that come from the captures (which may be local to the
        // surrounding function) to the region map, so that they appear as region parameters of the
        // function.
        let upvars_tys = clos_args.upvar_tys();
        let mut fixed_upvars_tys = Vec::new();
        for ty in upvars_tys {
            let fixed_ty =
                regions::arg_folder::rename_closure_capture_regions(ty, tcx, region_substitution, info);
            fixed_upvars_tys.push(fixed_ty);
        }

        // Do the same for the arguments of the closure -- this may contain external Polonius
        // regions in lieu of early bounds.
        let fixed_closure_args = regions::arg_folder::rename_closure_capture_regions(
            input_tuple_ty,
            tcx,
            region_substitution,
            info,
        );

        // Do the same to the whole closure arg, which will add the optional lifetime for the
        // capture reference
        // NOTE: we rely on adding this lifetime last when generating the `call_*` fn shims.
        let fixed_closure_arg_ty = regions::arg_folder::rename_closure_capture_regions(
            closure_arg.ty,
            tcx,
            region_substitution,
            info,
        );

        // find the optional lifetime for the outer reference
        let mut maybe_outer_lifetime = None;
        if let ty::TyKind::Ref(r, _, _) = fixed_closure_arg_ty.kind() {
            if let ty::RegionKind::ReVar(r) = r.kind() {
                let name = &region_substitution.region_names[&r.into()];
                maybe_outer_lifetime = Some(name.to_owned());
            } else {
                unreachable!();
            }
        }

        (fixed_closure_arg_ty, fixed_upvars_tys, fixed_closure_args, maybe_outer_lifetime)
    }

    /// Create a translation instance for a closure.
    pub(crate) fn new_closure(
        tcx: ty::TyCtxt<'tcx>,
        meta: &procedures::Meta,
        proc: Procedure<'tcx>,
        attrs: &'a [&'a hir::AttrItem],
        ty_translator: &'def types::TX<'def, 'tcx>,
        trait_registry: &'def registry::TR<'tcx, 'def>,
        proc_registry: &'a procedures::Scope<'tcx, 'def>,
        const_registry: &'a consts::Scope<'def>,
        non_sc_atomic_spans: &'a mut Vec<span::Span>,
    ) -> Result<(Self, procedures::ClosureImplInfo<'tcx, 'def>), TranslationError<'tcx>> {
        let mut translated_fn = code::FunctionBuilder::new(
            meta.get_name(),
            meta.get_code_name(),
            meta.get_spec_name(),
            meta.get_trait_req_incl_name(),
        );

        // TODO can we avoid the leak
        let proc: &'def Procedure<'_> = &*Box::leak(Box::new(proc));
        let body = proc.get_mir();
        Self::dump_body(body);

        let clos_args = environment::get_closure_args(tcx, proc.get_id());
        let closure_kind = clos_args.kind();
        let tupled_upvars_tys = clos_args.tupled_upvars_ty();
        let parent_args = clos_args.parent_args();
        let unnormalized_sig = clos_args.sig();
        let sig = unnormalized_sig;
        // Note: `captures` contains the late bounds of this closure, i.e., lifetimes that just this
        // closure is generic over.
        let captures = tcx.closure_captures(proc.get_id().as_local().unwrap());
        info!("closure sig: {:?}", sig);
        info!("Closure has captures: {:?}", captures);
        info!("Closure arg upvar_tys: {:?}", tupled_upvars_tys);
        info!("Function signature: {:?}", sig);
        info!("Closure generic args: {:?}", parent_args);

        let local_decls = &body.local_decls;
        // the closure arg, containing the captures
        let closure_arg = local_decls.get(mir::Local::from_usize(1)).unwrap();

        let info = PoloniusInfo::new(proc);

        // TODO: avoid leak
        let info: &'def PoloniusInfo<'_, '_> = &*Box::leak(Box::new(info));

        // For closures, we only handle the parent's args here!
        // We add the lifetime parameters arising from the captures of the closure (which may be
        // local to the parent) below in `Self::compute_closure_meta`.
        let params = parent_args;
        info!("Function generic args: {:?}", params);

        if rrconfig::dump_borrowck_info() {
            dump_borrowck_info(tcx, proc.get_id(), info);
        }

        // Note: this only treats the formal arguments of the closure, but not the closure captures
        let num_universals = info.borrowck_in_facts.universal_region.len();
        let mut num_late_bounds = sig.bound_vars().len();
        let num_early_bounds =
            params.iter().filter(|x| matches!(x.kind(), ty::GenericArgKind::Lifetime(_))).count();
        // closures don't have early bounds: only late bounds and external lifetimes from the
        // surrounding scope.
        assert!(num_early_bounds == 0);
        if let ty::TyKind::Ref(_, _, _) = closure_arg.ty.kind() {
            // add 1 for the closure arg
            num_late_bounds += 1;
        }
        let (tupled_inputs, output, mut region_substitution) =
            regions::init::replace_fnsig_args_with_polonius_vars(
                tcx,
                params,
                proc.get_id(),
                num_universals,
                num_early_bounds,
                num_late_bounds,
                sig,
            );

        // detuple the inputs
        assert!(tupled_inputs.len() == 1);
        let input_tuple_ty = tupled_inputs[0];

        info!("region substitution: {region_substitution:?}");

        // fix the regions in the closure args (esp the captures) and add the regions for the
        // captures to the region map (i.e., external regions).
        let (fixed_closure_arg_ty, upvars_tys, input_tuple_ty, maybe_outer_lifetime) =
            Self::compute_closure_meta(
                clos_args,
                closure_arg,
                input_tuple_ty,
                &mut region_substitution,
                info,
                tcx,
            );
        let maybe_outer_lifetime = maybe_outer_lifetime.map(|x| x.lft().to_owned());

        trace!(
            "fixed_closure_arg_ty={fixed_closure_arg_ty:?}, upvars_tys={upvars_tys:?}, input_tuple_ty={input_tuple_ty:?}, region_substitution={region_substitution:?}"
        );

        let mut inputs = Vec::new();
        if let ty::TyKind::Tuple(args) = input_tuple_ty.kind() {
            inputs.extend(args.iter());
        }

        info!("inputs({}): {:?}, output: {:?}", inputs.len(), inputs, output);

        let type_scope = Self::setup_local_scope(
            tcx,
            ty_translator,
            trait_registry,
            proc.get_id(),
            params,
            &mut translated_fn,
            region_substitution.clone(),
            Some(info),
        )?;

        let inclusion_tracker = regions::init::initialize_inclusion_tracker(&type_scope.lifetime_scope, info);

        let type_translator = types::LocalTX::new(ty_translator, type_scope);

        info!("tupled closure upvars: {fixed_closure_arg_ty:?}");
        let mut all_inputs = inputs.clone();
        all_inputs.insert(0, fixed_closure_arg_ty);

        let mut t = Self {
            tcx,
            proc,
            info,
            translated_fn,
            inclusion_tracker,
            procedure_registry: proc_registry,
            attrs,
            ty_translator: type_translator,
            trait_registry,
            const_registry,
            inputs: all_inputs,
            non_sc_atomic_spans,
        };

        // compute meta information needed to generate the spec
        let mut translated_upvars_types = Vec::new();
        for ty in upvars_tys {
            let translated_ty = t.ty_translator.translate_type(ty)?;
            translated_upvars_types.push(translated_ty);
        }
        let meta = ClosureMetaInfo {
            kind: closure_kind,
            captures,
            capture_tys: &translated_upvars_types,
            closure_lifetime: maybe_outer_lifetime.clone(),
        };

        // get argument names
        let arg_names: &'tcx [Option<span::symbol::Ident>] = tcx.fn_arg_idents(proc.get_id());
        let arg_names: Vec<_> = arg_names
            .iter()
            .enumerate()
            .map(|(i, maybe_name)| {
                maybe_name
                    .and_then(|x| if x.as_str() == "_" { None } else { Some(x.as_str().to_owned()) })
                    .unwrap_or_else(|| format!("_arg_{i}"))
            })
            .collect();
        info!("arg names: {arg_names:?}");

        // process attributes
        let spec_info = t.process_closure_attrs(&inputs, output, &arg_names, meta)?;

        // compute the info needed to assemble the trait impls for this closure
        let self_var_ty = t.ty_translator.translate_type(fixed_closure_arg_ty)?;
        let self_ty = environment::get_closure_self_ty_from_var_ty(fixed_closure_arg_ty, closure_kind);
        let args_ty = t.ty_translator.translate_type(input_tuple_ty)?;
        let output_ty = t.ty_translator.translate_type(output)?;
        let mut args_tys: Vec<specs::Type<'def>> = Vec::new();
        for arg in inputs {
            let translated: specs::Type<'def> = t.ty_translator.translate_type(arg)?;
            args_tys.push(translated);
        }

        let mut generics = t.translated_fn.spec.get_generics().to_owned();
        // remove the direct lifetime param, which is a latebound of the function, not the impl
        if let Some(lft) = &maybe_outer_lifetime {
            generics.remove_lft_param(lft);
        }

        let info = procedures::ClosureImplInfo::new(
            closure_kind,
            generics,
            maybe_outer_lifetime,
            region_substitution,
            self_ty,
            input_tuple_ty,
            self_var_ty,
            args_ty,
            args_tys,
            output_ty,
            spec_info.params_encoded,
            spec_info.pre_encoded,
            spec_info.post_encoded,
            spec_info.post_mut_encoded,
        );

        Ok((t, info))
    }

    fn function_has_nontrivial_annotations(tcx: ty::TyCtxt<'tcx>, did: DefId) -> bool {
        environment::has_tool_attribute(tcx, did, "params")
            || environment::has_tool_attribute(tcx, did, "ensures")
            || environment::has_tool_attribute(tcx, did, "requires")
            || environment::has_tool_attribute(tcx, did, "returns")
            || environment::has_tool_attribute(tcx, did, "observe")
            || environment::has_tool_attribute(tcx, did, "args")
    }

    /// Translate the body of a function.
    pub(crate) fn new(
        tcx: ty::TyCtxt<'tcx>,
        meta: &procedures::Meta,
        proc: Procedure<'tcx>,
        attrs: &'a [&'a hir::AttrItem],
        ty_translator: &'def types::TX<'def, 'tcx>,
        trait_registry: &'def registry::TR<'tcx, 'def>,
        proc_registry: &'a procedures::Scope<'tcx, 'def>,
        const_registry: &'a consts::Scope<'def>,
        non_sc_atomic_spans: &'a mut Vec<span::Span>,
    ) -> Result<Self, TranslationError<'tcx>> {
        let mut translated_fn = code::FunctionBuilder::new(
            meta.get_name(),
            meta.get_code_name(),
            meta.get_spec_name(),
            meta.get_trait_req_incl_name(),
        );

        // TODO can we avoid the leak
        let proc: &'def Procedure<'_> = &*Box::leak(Box::new(proc));

        let body = proc.get_mir();
        Self::dump_body(body);

        let ty: ty::EarlyBinder<'_, ty::Ty<'tcx>> = tcx.type_of(proc.get_id());
        info!("Function type: {ty:?}");

        let params = Self::get_proc_ty_params(tcx, proc.get_id());
        info!("Function generic args: {:?}", params);

        let ty = ty.instantiate_identity();
        // substs are the generic args of this function (including lifetimes)
        // sig is the function signature
        assert!(ty.is_fn());
        let sig = ty.fn_sig(tcx);
        info!("sig: {sig:?}");

        let info = PoloniusInfo::new(proc);
        // TODO: avoid leak
        let info: &'def PoloniusInfo<'_, '_> = &*Box::leak(Box::new(info));

        if rrconfig::dump_borrowck_info() {
            dump_borrowck_info(tcx, proc.get_id(), info);
        }

        let (inputs, output, region_substitution) = if let Some(impl_did) = tcx.impl_of_assoc(proc.get_id())
            && tcx.impl_is_of_trait(impl_did)
        {
            // If this is a function in a trait impl, we need to do some extra fixing up, because
            // lifetime elision behaves strangely.

            // We compute the expected signature this function *should* have
            let expected_sig = trait_registry.get_expected_sig_for_impl_fn(proc.get_id())?;
            info!("expected sig: {expected_sig:?}");

            // Important: use the fn's sig here.
            let num_universals = info.borrowck_in_facts.universal_region.len();
            let num_late_bounds = sig.bound_vars().len();
            let num_early_bounds =
                params.iter().filter(|x| matches!(x.kind(), ty::GenericArgKind::Lifetime(_))).count();

            let (direct_inputs, direct_output, _) = regions::init::replace_fnsig_args_with_polonius_vars(
                tcx,
                params,
                proc.get_id(),
                num_universals,
                num_early_bounds,
                num_late_bounds,
                sig,
            );

            info!("direct signature: {direct_inputs:?} -> {direct_output:?}");

            let (inputs, output, mut mapping) = regions::init::replace_fnsig_args_with_polonius_vars(
                tcx,
                params,
                proc.get_id(),
                num_universals,
                num_early_bounds,
                num_late_bounds,
                expected_sig,
            );

            // Now unify the two signatures.
            let typing_env = ty::TypingEnv::post_analysis(tcx, proc.get_id());
            let mut unifier = RegionUnifier::new(tcx, typing_env);
            // Since we cannot reliably normalize here without erasing regions, ignore aliases for now.
            unifier.ignore_aliases();

            unifier.map_ty_slices(&direct_inputs, &inputs);
            unifier.map_tys(direct_output, output);
            let (_, vid_mapping) = unifier.get_result();

            info!("region mapping: {vid_mapping:?}");
            for (from, to) in vid_mapping {
                let to = to.as_var();
                if from != to {
                    mapping.insert_vid_fixup(from.into(), to.into());
                }
            }
            // TODO: also add the equality constraints to the inclusion tracker?

            (inputs, output, mapping)
        } else {
            let num_universals = info.borrowck_in_facts.universal_region.len();
            let num_late_bounds = sig.bound_vars().len();
            let num_early_bounds =
                params.iter().filter(|x| matches!(x.kind(), ty::GenericArgKind::Lifetime(_))).count();

            regions::init::replace_fnsig_args_with_polonius_vars(
                tcx,
                params,
                proc.get_id(),
                num_universals,
                num_early_bounds,
                num_late_bounds,
                sig,
            )
        };
        info!("normalized signature: {inputs:?} -> {output:?}");

        let type_scope = Self::setup_local_scope(
            tcx,
            ty_translator,
            trait_registry,
            proc.get_id(),
            params.as_slice(),
            &mut translated_fn,
            region_substitution,
            Some(info),
        )?;

        let inclusion_tracker = regions::init::initialize_inclusion_tracker(&type_scope.lifetime_scope, info);

        let type_translator = types::LocalTX::new(ty_translator, type_scope);

        // get argument names
        let arg_names: &'tcx [Option<span::symbol::Ident>] = tcx.fn_arg_idents(proc.get_id());
        let arg_names: Vec<_> = arg_names
            .iter()
            .enumerate()
            .map(|(i, maybe_name)| maybe_name.map_or_else(|| format!("_arg_{i}"), |x| x.as_str().to_owned()))
            .collect();
        info!("arg names: {arg_names:?}");

        let mut t = Self {
            tcx,
            proc,
            info,
            translated_fn,
            inclusion_tracker,
            procedure_registry: proc_registry,
            attrs,
            ty_translator: type_translator,
            trait_registry,
            const_registry,
            inputs: inputs.clone(),
            non_sc_atomic_spans,
        };

        // If this is an impl of a trait, and there are no explicit annotations, use the default specification
        // of the trait (instead of the Rust implied safety contract)
        if environment::trait_impl_of_method(tcx, proc.get_id()).is_some()
            && !Self::function_has_nontrivial_annotations(tcx, proc.get_id())
        {
            // Use the default spec annotated on the trait
            let spec = t.make_trait_instance_spec()?;
            if let Some((spec, context_items)) = spec {
                t.translated_fn.add_trait_function_spec(spec);
                for binder in context_items.0 {
                    t.translated_fn.add_late_coq_param(binder);
                }
            } else {
                return Err(TranslationError::AttributeError(
                    "No valid specification provided for trait impl".to_owned(),
                ));
            }
        } else {
            // process attributes
            let spec_builder = if attrs.is_empty()
                && crate::is_method_on_atomic_type(tcx, proc.get_id())
            {
                Self::auto_infer_atomic_method_spec(
                    tcx, proc.get_id(), &t.ty_translator, inputs.as_slice(), output,
                )?
            } else {
                Self::process_attrs(
                    attrs,
                    &t.ty_translator,
                    &mut t.translated_fn,
                    &arg_names,
                    inputs.as_slice(),
                    output,
                )?
            };

            if spec_builder.has_spec() {
                t.translated_fn.add_function_spec_from_builder(spec_builder);
            } else {
                return Err(TranslationError::AttributeError("No valid specification provided".to_owned()));
            }
        }

        Ok(t)
    }

    /// Translate the body of the function.
    pub(crate) fn translate(
        self,
        spec_arena: &'def Arena<specs::functions::Spec<'def, specs::functions::InnerSpec<'def>>>,
    ) -> Result<code::Function<'def>, TranslationError<'tcx>> {
        let translator = translation::TX::new(
            self.tcx,
            self.procedure_registry,
            self.const_registry,
            self.trait_registry,
            self.ty_translator,
            self.proc,
            self.info,
            &self.inputs,
            self.inclusion_tracker,
            self.translated_fn,
            self.non_sc_atomic_spans,
        )?;
        translator.translate(spec_arena)
    }

    /// Translation that only generates a specification.
    pub(crate) fn generate_spec(
        self,
    ) -> Result<specs::functions::Spec<'def, specs::functions::InnerSpec<'def>>, TranslationError<'tcx>> {
        self.translated_fn.try_into().map_err(TranslationError::AttributeError)
    }
}

impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Get type parameters of the given procedure.
    fn get_proc_ty_params(tcx: ty::TyCtxt<'tcx>, did: DefId) -> ty::GenericArgsRef<'tcx> {
        let ty = tcx.type_of(did).instantiate_identity();
        match ty.kind() {
            ty::TyKind::FnDef(_, params) => params,
            _ => panic!("Procedure::new called on a procedure whose type is not TyKind::FnDef!"),
        }
    }

    /// Set up the local generic scope of the function, including type parameters, lifetime
    /// parameters, and trait constraints.
    fn setup_local_scope(
        tcx: ty::TyCtxt<'tcx>,
        ty_translator: &'def types::TX<'def, 'tcx>,
        trait_registry: &'def registry::TR<'tcx, 'def>,
        proc_did: DefId,
        params: &[ty::GenericArg<'tcx>],
        translated_fn: &mut code::FunctionBuilder<'def>,
        region_substitution: regions::EarlyLateRegionMap<'def>,
        info: Option<&'def PoloniusInfo<'def, 'tcx>>,
    ) -> Result<types::FunctionState<'tcx, 'def>, TranslationError<'tcx>> {
        // enter the procedure
        let type_scope = types::FunctionState::new_with_traits(
            proc_did,
            tcx,
            tcx.mk_args(params),
            region_substitution,
            ty_translator,
            trait_registry,
            info,
        )?;

        // add generic args to the fn
        let generics = type_scope.make_params_scope();
        translated_fn.provide_generic_scope(generics.into());

        Ok(type_scope)
    }

    /// Process extra requirements annotated on a function spec.
    fn process_function_requirements(
        fn_builder: &mut code::FunctionBuilder<'def>,
        requirements: FunctionRequirements,
    ) {
        for e in requirements.early_coq_params {
            fn_builder.add_early_coq_param(e);
        }
        for e in requirements.late_coq_params {
            fn_builder.add_late_coq_param(e);
        }
        for e in requirements.proof_info.linktime_assumptions {
            fn_builder.add_linktime_assumption(e);
        }
        for e in requirements.proof_info.sidecond_tactics {
            fn_builder.add_manual_tactic(e);
        }
    }

    /// Parse and process attributes of this closure.
    fn process_closure_attrs(
        &mut self,
        inputs: &[ty::Ty<'tcx>],
        output: ty::Ty<'tcx>,
        arg_names: &[String],
        meta: ClosureMetaInfo<'_, 'tcx, 'def>,
    ) -> Result<ClosureSpecInfo, TranslationError<'tcx>> {
        trace!("entering process_closure_attrs");
        let v = self.attrs;

        // Translate signature
        info!("inputs: {:?}, output: {:?}", inputs, output);
        let mut translated_arg_types: Vec<specs::Type<'def>> = Vec::new();
        for arg in inputs {
            let translated: specs::Type<'def> = self.ty_translator.translate_type(*arg)?;
            translated_arg_types.push(translated);
        }
        let translated_ret_type: specs::Type<'def> = self.ty_translator.translate_type(output)?;
        info!("translated function type: {:?} → {}", translated_arg_types, translated_ret_type);

        let ret_is_option = self.ty_translator.translator.is_builtin_option_type(output);
        let ret_is_result = self.ty_translator.translator.is_builtin_result_type(output);

        // Determine parser
        let parser = rrconfig::attribute_parser();
        if parser.as_str() != "verbose" {
            trace!("leaving process_closure_attrs");
            return Err(TranslationError::UnknownAttributeParser(parser));
        }

        let mut spec_builder = specs::functions::LiteralSpecBuilder::new();

        let ty_translator = &self.ty_translator;
        // Hack: create indirection by tracking the tuple uses we create in here.
        // (We need a read reference to the scope, so we can't write to it at the same time)
        let mut tuple_uses = HashMap::new();
        let spec_info = {
            let scope = ty_translator.scope.borrow();
            let mut parser = VerboseFunctionSpecParser::new(
                &self.translated_fn.spec.function_name,
                &translated_arg_types,
                &translated_ret_type,
                ret_is_option,
                ret_is_result,
                Some(arg_names),
                &*scope,
                |lit| ty_translator.translator.intern_literal(lit),
            );

            let spec_info = parser
                .parse_closure_spec(v, &mut spec_builder, meta, |x| {
                    ty_translator.make_tuple_use(x, Some(&mut tuple_uses))
                })
                .map_err(TranslationError::AttributeError)?;

            let x = parser.into();
            Self::process_function_requirements(&mut self.translated_fn, x);
            spec_info
        };
        let mut scope = ty_translator.scope.borrow_mut();
        scope.tuple_uses.extend(tuple_uses);
        self.translated_fn.add_function_spec_from_builder(spec_builder);

        trace!("leaving process_closure_attrs");
        Ok(spec_info)
    }

    /// Parse and process attributes of this function.
    fn process_attrs(
        attrs: &[&hir::AttrItem],
        ty_translator: &types::LocalTX<'def, 'tcx>,
        translator: &mut code::FunctionBuilder<'def>,
        arg_names: &[String],
        inputs: &[ty::Ty<'tcx>],
        output: ty::Ty<'tcx>,
    ) -> Result<specs::functions::LiteralSpecBuilder<'def>, TranslationError<'tcx>> {
        info!("inputs: {:?}, output: {:?}", inputs, output);

        let mut translated_arg_types: Vec<specs::Type<'def>> = Vec::new();
        for arg in inputs {
            let translated: specs::Type<'def> = ty_translator.translate_type(*arg)?;
            translated_arg_types.push(translated);
        }
        let translated_ret_type: specs::Type<'def> = ty_translator.translate_type(output)?;
        info!("translated function type: {:?} → {}", translated_arg_types, translated_ret_type);

        let ret_is_option = ty_translator.translator.is_builtin_option_type(output);
        let ret_is_result = ty_translator.translator.is_builtin_result_type(output);

        let mut spec_builder = specs::functions::LiteralSpecBuilder::new();

        let parser = rrconfig::attribute_parser();
        match parser.as_str() {
            "verbose" => {
                {
                    let scope = ty_translator.scope.borrow();
                    let mut parser: VerboseFunctionSpecParser<'_, 'def, _, _> =
                        VerboseFunctionSpecParser::new(
                            &translator.spec.function_name,
                            &translated_arg_types,
                            &translated_ret_type,
                            ret_is_option,
                            ret_is_result,
                            Some(arg_names),
                            &*scope,
                            |lit| ty_translator.translator.intern_literal(lit),
                        );

                    parser
                        .parse_function_spec(attrs, &mut spec_builder)
                        .map_err(TranslationError::AttributeError)?;
                    Self::process_function_requirements(translator, parser.into());
                }

                Ok(spec_builder)
            },
            _ => Err(TranslationError::UnknownAttributeParser(parser)),
        }
    }

    /// Auto-generate spec for a method on a `mode(atomic)` type based on its signature.
    fn auto_infer_atomic_method_spec(
        tcx: ty::TyCtxt<'tcx>,
        proc_did: DefId,
        ty_translator: &types::LocalTX<'def, 'tcx>,
        inputs: &[ty::Ty<'tcx>],
        output: ty::Ty<'tcx>,
    ) -> Result<specs::functions::LiteralSpecBuilder<'def>, TranslationError<'tcx>> {
        let mut builder = specs::functions::LiteralSpecBuilder::new();

        // Get inner field refinement type from Self type
        let assoc_item = tcx.opt_associated_item(proc_did).unwrap();
        let impl_did = assoc_item.container_id(tcx);
        let self_ty = tcx.type_of(impl_did).instantiate_identity();
        let ty::TyKind::Adt(adt_def, substs) = self_ty.kind() else {
            return Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "auto_infer_atomic_method_spec: Self type is not ADT for {}", tcx.def_path_str(proc_did)
                ),
            });
        };
        let field_def = adt_def.variants().iter().next().unwrap().fields.iter().next().unwrap();
        let field_ty = field_def.ty(tcx, substs);
        let translated_field = ty_translator.translate_type(field_ty)?;
        let _inner_rt = translated_field.get_rfn_type();

        // Translate return type
        let translated_ret = ty_translator.translate_type(output)?;

        // Step 1: Default args — same as add_default_spec (verbose_function_spec_parser.rs:1233)
        // Add ALL inputs as params (Type::Infer) + args (translated type + Rust name)
        let arg_idents = tcx.fn_arg_idents(proc_did);
        for (i, input_ty) in inputs.iter().enumerate() {
            let arg_name = arg_idents[i]
                .map_or_else(|| format!("_arg_{i}"), |ident| ident.as_str().to_owned());
            let translated = ty_translator.translate_type(*input_ty)?;
            builder.add_param(
                coq::binder::Binder::new(Some(arg_name.clone()), coq::term::Type::Infer),
            ).map_err(TranslationError::AttributeError)?;
            builder.add_arg(specs::TypeWithRef::new(translated, arg_name));
        }

        // Step 2: Classify receiver for pattern matching
        let has_self = !inputs.is_empty() && (inputs[0].is_ref() || {
            matches!(inputs[0].kind(), ty::TyKind::Adt(def, _) if def.did() == adt_def.did())
        });
        let (is_shared_ref, is_mut_ref, is_by_value) = if has_self {
            match inputs[0].kind() {
                ty::TyKind::Ref(_, _, mutbl) => (mutbl.is_not(), mutbl.is_mut(), false),
                ty::TyKind::Adt(..) => (false, false, true),
                _ => (false, false, false),
            }
        } else {
            (false, false, false)
        };
        let non_self_args = if has_self { inputs.len() - 1 } else { inputs.len() };
        let ret_is_unit = output.is_unit();
        let ret_is_mut_ref = matches!(output.kind(), ty::TyKind::Ref(_, _, mir::Mutability::Mut));

        // Step 3: Pattern-specific existentials + return
        // Patterns with explicit return: add existential x (+ γ for get_mut) and set return
        // Patterns without: implicit return (exists ret : _, ret @ ret_type)
        let has_explicit_return;
        if is_shared_ref && non_self_args == 0 && !ret_is_unit && !ret_is_mut_ref {
            // load: (&self) -> T
            builder.add_existential(
                coq::binder::Binder::new_with_name_hint("x".to_owned(), coq::term::Type::Infer),
            ).map_err(TranslationError::AttributeError)?;
            builder.set_ret_type(specs::TypeWithRef::new(translated_ret.clone(), "x".to_owned()))
                .map_err(TranslationError::AttributeError)?;
            has_explicit_return = true;
        } else if is_shared_ref && non_self_args >= 1 && ret_is_unit {
            // store: (&self, val: T, ...) — no existential, implicit return
            has_explicit_return = false;
        } else if is_shared_ref && non_self_args >= 1 && !ret_is_unit && !ret_is_mut_ref {
            // swap/fetch_*: (&self, val: T, ...) -> T
            builder.add_existential(
                coq::binder::Binder::new_with_name_hint("x".to_owned(), coq::term::Type::Infer),
            ).map_err(TranslationError::AttributeError)?;
            builder.set_ret_type(specs::TypeWithRef::new(translated_ret.clone(), "x".to_owned()))
                .map_err(TranslationError::AttributeError)?;
            has_explicit_return = true;
        } else if !has_self && non_self_args >= 1 {
            // new: (val: T, ...) -> Self — no existential, implicit return
            has_explicit_return = false;
        } else if is_by_value && non_self_args == 0 && !ret_is_unit {
            // into_inner: (self) -> T
            builder.add_existential(
                coq::binder::Binder::new_with_name_hint("x".to_owned(), coq::term::Type::Infer),
            ).map_err(TranslationError::AttributeError)?;
            builder.set_ret_type(specs::TypeWithRef::new(translated_ret.clone(), "x".to_owned()))
                .map_err(TranslationError::AttributeError)?;
            has_explicit_return = true;
        } else if is_mut_ref && non_self_args == 0 && ret_is_mut_ref {
            // get_mut: (&mut self) -> &mut T
            builder.add_existential(
                coq::binder::Binder::new_with_name_hint("x".to_owned(), coq::term::Type::Infer),
            ).map_err(TranslationError::AttributeError)?;
            builder.add_existential(
                coq::binder::Binder::new_with_name_hint(
                    "γ".to_owned(), coq::term::Type::Infer,
                ),
            ).map_err(TranslationError::AttributeError)?;
            builder.set_ret_type(specs::TypeWithRef::new(translated_ret.clone(), "(x, γ)".to_owned()))
                .map_err(TranslationError::AttributeError)?;
            has_explicit_return = true;
        } else {
            return Err(TranslationError::UnsupportedFeature {
                description: format!(
                    "mode(atomic) method {} has unrecognized signature for auto-inference \
                     (shared_ref={is_shared_ref}, mut_ref={is_mut_ref}, by_value={is_by_value}, \
                     args={non_self_args}, ret_unit={ret_is_unit}, ret_mut_ref={ret_is_mut_ref}). \
                     Add explicit #[rr::only_spec] annotations.",
                    tcx.def_path_str(proc_did),
                ),
            });
        }

        // Step 4: Implicit return — same as add_default_spec (verbose_function_spec_parser.rs:1250)
        if !has_explicit_return {
            builder.add_existential(
                coq::binder::Binder::new(Some("ret".to_owned()), coq::term::Type::Infer),
            ).map_err(TranslationError::AttributeError)?;
            builder.set_ret_type(specs::TypeWithRef::new(translated_ret, "ret".to_owned()))
                .map_err(TranslationError::AttributeError)?;
        }

        builder.have_spec();
        Ok(builder)
    }

    /// Make a specification for a method of a trait impl derived from the trait's default spec.
    fn make_trait_instance_spec(
        &self,
    ) -> Result<
        Option<(specs::traits::InstantiatedFunctionSpec<'def>, coq::binder::BinderList)>,
        TranslationError<'tcx>,
    > {
        let did = self.proc.get_id();

        let Some(impl_did) = self.tcx.impl_of_assoc(did) else {
            return Ok(None);
        };

        if !self.tcx.impl_is_of_trait(impl_did) {
            return Ok(None);
        }
        let trait_did = self.tcx.impl_trait_id(impl_did);

        self.trait_registry
            .lookup_trait(trait_did)
            .ok_or_else(|| TranslationError::TraitResolution(format!("{trait_did:?}")))?;

        let fn_name = strip_coq_ident(self.tcx.item_name(self.proc.get_id()).as_str());

        let (trait_info, _, context_items) = self.trait_registry.get_trait_impl_info(impl_did)?;
        Ok(Some((specs::traits::InstantiatedFunctionSpec::new(trait_info, fn_name), context_items)))
    }

    fn dump_body(body: &mir::Body<'_>) {
        let basic_blocks = &body.basic_blocks;
        for (bb_idx, bb) in basic_blocks.iter_enumerated() {
            Self::dump_basic_block(bb_idx, bb);
        }
    }

    /// Dump a basic block as info debug output.
    fn dump_basic_block(bb_idx: mir::BasicBlock, bb: &mir::BasicBlockData<'_>) {
        info!("Basic block {:?}:", bb_idx);
        let mut i = 0;
        for s in &bb.statements {
            info!("{}\t{:?}", i, s);
            i += 1;
        }
        info!("{}\t{:?}", i, bb.terminator());
    }
}
