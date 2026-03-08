// © 2025, The RefinedRust Develcpers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use log::{info, trace};
use radium::specs::traits::ReqInfo as _;
use radium::{code, coq, lang, specs};
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::ty;
use typed_arena::Arena;

use crate::traits::registry::TR;
use crate::types::{TX, scope};
use crate::{base, body, environment, procedures, search};

pub(crate) struct ClosureImplGenerator<'tcx, 'def> {
    tcx: ty::TyCtxt<'tcx>,
    trait_registry: &'def TR<'tcx, 'def>,
    ty_translator: &'def TX<'def, 'tcx>,

    /// the arena to intern function specs into
    fn_arena: &'def Arena<specs::functions::Spec<'def, specs::functions::InnerSpec<'def>>>,

    /// specs for the three closure traits
    fnmut_spec: specs::traits::LiteralSpecRef<'def>,
    fn_spec: specs::traits::LiteralSpecRef<'def>,
    fnonce_spec: specs::traits::LiteralSpecRef<'def>,
}

#[derive(Clone, PartialEq, Eq)]
enum ShimRefSelf {
    /// don't ref
    NoRef,
    /// make into &mut
    RefMut,
    /// make into &shr
    RefShr,
    /// self is &mut, make into &shr
    RefMutToShr,
}

impl<'tcx, 'def> ClosureImplGenerator<'tcx, 'def> {
    pub(crate) fn new(
        tcx: ty::TyCtxt<'tcx>,
        trait_registry: &'def TR<'tcx, 'def>,
        ty_translator: &'def TX<'def, 'tcx>,
        fn_arena: &'def Arena<specs::functions::Spec<'def, specs::functions::InnerSpec<'def>>>,
    ) -> Option<Self> {
        let fnmut_did = search::get_closure_trait_did(tcx, ty::ClosureKind::FnMut)?;
        let fn_did = search::get_closure_trait_did(tcx, ty::ClosureKind::Fn)?;
        let fnonce_did = search::get_closure_trait_did(tcx, ty::ClosureKind::FnOnce)?;

        let fnmut_spec = trait_registry.lookup_trait(fnmut_did)?;
        let fn_spec = trait_registry.lookup_trait(fn_did)?;
        let fnonce_spec = trait_registry.lookup_trait(fnonce_did)?;

        Some(Self {
            tcx,
            trait_registry,
            ty_translator,
            fn_arena,
            fnmut_spec,
            fn_spec,
            fnonce_spec,
        })
    }

    /// Generate the `call_...` function shim, pushing it to the given `builder`.
    fn generate_call_shim(
        &self,
        builder: &mut code::FunctionBuilder<'def>,
        info: &procedures::ClosureImplInfo<'tcx, 'def>,
        closure_did: DefId,
        closure_meta: &procedures::Meta,
        closure_spec: &specs::functions::Spec<'def>,
        ref_self: &ShimRefSelf,
    ) -> Result<(), base::TranslationError<'tcx>> {
        let (tupled_upvars_ty, self_is_ref) = match &info.tl_self_var_ty {
            specs::Type::MutRef(ty, _) | specs::Type::ShrRef(ty, _) => ((**ty).clone(), true),
            _ => (info.tl_self_var_ty.clone(), false),
        };

        trace!("tupled_upvars_ty: {tupled_upvars_ty:?}");

        let self_st: lang::SynType = tupled_upvars_ty.into();
        let args_st: lang::SynType = info.tl_args_ty.clone().into();
        let output_st: lang::SynType = info.tl_output_ty.clone().into();

        // the syntype of the self variable this function gets
        //let self_var_st: lang::SynType = info.self_ty.clone().into();
        let self_var_st: lang::SynType = match ref_self {
            ShimRefSelf::NoRef => info.tl_self_var_ty.clone().into(),
            ShimRefSelf::RefMutToShr => lang::SynType::Ptr,
            _ => self_st.clone(),
        };

        trace!("tupled_upvars_st: {self_st:?}, self_var_st: {self_var_st:?}");

        // the syn type that the closure to call expects
        let self_call_st =
            if matches!(ref_self, ShimRefSelf::NoRef) { self_var_st.clone() } else { lang::SynType::Ptr };

        // add arguments: self, args
        builder.code.add_argument("self", self_var_st.clone());
        builder.code.add_argument("args", args_st.clone());

        // compute instantiation hint for the function we're calling
        let mut lft_hints = vec![];
        for lft in info.scope.get_lfts() {
            // TODO: do we need something more elaborate?
            lft_hints.push(lft.lft().to_owned());
        }
        // for the type hints, we have to instantiate all type parameters
        // use the identitity instantiation
        let params = info.scope.get_all_ty_params_with_assocs();
        let mut ty_hints = vec![];
        for param in params.params {
            let ty = specs::Type::LiteralParam(param);
            let rst = code::RustType::of_type(&ty);
            ty_hints.push(rst);
        }

        // add basic blocks
        let mut statements = Vec::new();

        // add locals
        statements.push(code::PrimStmt::LocalLive(code::Variable::new("__0".to_owned(), output_st.clone())));
        statements
            .push(code::PrimStmt::LocalLive(code::Variable::new("__1".to_owned(), self_call_st.clone())));

        // initialize the self argument
        let ref_lft = "_mk_ref_lft";
        if *ref_self == ShimRefSelf::RefShr
            || *ref_self == ShimRefSelf::RefMut
            || *ref_self == ShimRefSelf::RefMutToShr
        {
            lft_hints.push(coq::Ident::new(ref_lft));
        } else if self_is_ref {
            // also add this lifetime as a hint
            lft_hints.push(coq::Ident::new("_ref_lft"));
        }

        match ref_self {
            ShimRefSelf::NoRef => {
                // just move the self argument into __1
                let stmt = code::PrimStmt::Assign {
                    ot: self_var_st.clone().into(),
                    order: lang::Order::Na,
                    e1: Box::new(code::Expr::Var("__1".to_owned())),
                    e2: Box::new(code::Expr::Move {
                        ot: self_var_st.into(),
                        order: lang::Order::Na,
                        e: Box::new(code::Expr::Var("self".to_owned())),
                    }),
                };
                statements.push(stmt);
            },
            ShimRefSelf::RefMut => {
                // start lft
                let annot =
                    code::Annotation::StartLft(coq::Ident::new(ref_lft), vec![coq::Ident::new("_flft")]);
                statements.push(code::PrimStmt::Annot {
                    a: vec![annot],
                    why: None,
                });
                statements.push(code::PrimStmt::Assign {
                    ot: lang::OpType::Ptr,
                    order: lang::Order::Na,
                    e1: Box::new(code::Expr::Var("__1".to_owned())),
                    e2: Box::new(code::Expr::Borrow {
                        lft: coq::Ident::new(ref_lft),
                        bk: code::BorKind::Mutable,
                        ty: None,
                        e: Box::new(code::Expr::Var("self".to_owned())),
                    }),
                });
            },
            ShimRefSelf::RefShr => {
                let annot =
                    code::Annotation::StartLft(coq::Ident::new(ref_lft), vec![coq::Ident::new("_flft")]);
                statements.push(code::PrimStmt::Annot {
                    a: vec![annot],
                    why: None,
                });
                statements.push(code::PrimStmt::Assign {
                    ot: lang::OpType::Ptr,
                    order: lang::Order::Na,
                    e1: Box::new(code::Expr::Var("__1".to_owned())),
                    e2: Box::new(code::Expr::Borrow {
                        lft: coq::Ident::new(ref_lft),
                        bk: code::BorKind::Shared,
                        ty: None,
                        e: Box::new(code::Expr::Var("self".to_owned())),
                    }),
                });
            },
            ShimRefSelf::RefMutToShr => {
                // Note: make sure to remain in the bounds of the lifetime
                // we are reborrowing.
                // which lifetime should we take?
                //
                // Q: should the spec for this impl add that the state is unchanged?
                // - yeah, but that should happen in the spec encoder instead.
                // - i.e., PostMut should state this.
                let annot =
                    code::Annotation::StartLft(coq::Ident::new(ref_lft), vec![coq::Ident::new("_ref_lft")]);
                statements.push(code::PrimStmt::Annot {
                    a: vec![annot],
                    why: None,
                });
                statements.push(code::PrimStmt::Assign {
                    ot: lang::OpType::Ptr,
                    order: lang::Order::Na,
                    e1: Box::new(code::Expr::Var("__1".to_owned())),
                    e2: Box::new(code::Expr::Borrow {
                        lft: coq::Ident::new(ref_lft),
                        bk: code::BorKind::Shared,
                        ty: None,
                        e: Box::new(code::Expr::Deref {
                            ot: lang::OpType::Ptr,
                            order: lang::Order::Na,
                            e: Box::new(code::Expr::Var("self".to_owned())),
                        }),
                    }),
                });
            },
        }

        // call the closure
        let proc_use = self.generate_closure_procedure_use(closure_did, closure_meta, closure_spec)?;

        let tuple_sls = match &info.tl_args_ty {
            specs::Type::Literal(lit) => lit.generate_raw_syn_type_term(),
            specs::Type::Unit => lang::SynType::Unit,
            _ => {
                unreachable!("args should be a tuple type")
            },
        };

        // assemble the arguments, one by one
        let mut closure_args = Vec::new();
        // first the self argument
        let expr = code::Expr::Move {
            ot: self_call_st.into(),
            order: lang::Order::Na,
            e: Box::new(code::Expr::Var("__1".to_owned())),
        };
        closure_args.push(expr);

        // then the args themselves, detupling them
        for (idx, arg_ty) in info.tl_args_tys.iter().enumerate() {
            let arg_st: lang::SynType = arg_ty.clone().into();
            let expr = code::Expr::Move {
                ot: arg_st.into(),
                order: lang::Order::Na,
                e: Box::new(code::Expr::FieldOf {
                    e: Box::new(code::Expr::Var("args".to_owned())),
                    sls: tuple_sls.to_string(),
                    name: format!("{}", idx),
                }),
            };
            closure_args.push(expr);
        }

        let call_expr = code::Expr::Call {
            f: Box::new(code::Expr::Literal(code::Literal::Loc(proc_use.loc_name.clone()))),
            lfts: lft_hints,
            tys: ty_hints,
            args: closure_args,
        };
        statements.push(code::PrimStmt::Assign {
            ot: output_st.clone().into(),
            order: lang::Order::Na,
            e1: Box::new(code::Expr::Var("__0".to_owned())),
            e2: Box::new(call_expr),
        });

        if *ref_self != ShimRefSelf::NoRef {
            // end the lifetime of the created reference
            let annot = code::Annotation::EndLft(coq::Ident::new(ref_lft));
            statements.push(code::PrimStmt::Annot {
                a: vec![annot],
                why: None,
            });
        }

        //if !self_is_ref {
        // TODO: insert drop call
        //}

        // return
        let ret_expr = code::Expr::Move {
            ot: output_st.clone().into(),
            order: lang::Order::Na,
            e: Box::new(code::Expr::Var("__0".to_owned())),
        };
        let stmt = code::Stmt::Prim(statements, Box::new(code::Stmt::Return(ret_expr)));

        builder.code.add_basic_block(0, stmt);

        // require the closure
        builder.require_function(proc_use);

        // require the syntypes to be layoutable
        builder.assume_synty_layoutable(self_st);
        builder.assume_synty_layoutable(args_st);
        builder.assume_synty_layoutable(output_st);

        Ok(())
    }

    /// Make a procedure use for the closure's body.
    fn generate_closure_procedure_use(
        &self,
        closure_did: DefId,
        closure_meta: &procedures::Meta,
        closure_spec: &specs::functions::Spec<'def>,
    ) -> Result<code::UsedProcedure<'def>, base::TranslationError<'tcx>> {
        // explicit instantiation is needed sometimes
        let spec_term = code::UsedProcedureSpec::Literal(
            closure_meta.get_spec_name().to_owned(),
            closure_meta.get_trait_req_incl_name().to_owned(),
        );

        let code_name = closure_meta.get_name();
        let loc_name = format!("{code_name}_loc");

        // The scope is the same as the scope of the closure.
        let typing_env = ty::TypingEnv::post_analysis(self.tcx, closure_did);

        // Note: this does not include all lifetimes
        let clos_args = environment::get_closure_args(self.tcx, closure_did);
        let parent_args = clos_args.parent_args();
        let mut param_scope = scope::Params::new_from_generics(self.tcx, self.tcx.mk_args(parent_args), None);
        param_scope.add_param_env(closure_did, self.tcx, self.ty_translator, self.trait_registry)?;

        trace!("closure assumption generation: param_scope={param_scope:?}");

        // compute the syntypes of the closure's args
        let syntypes = body::get_arg_syntypes_for_procedure_call(
            self.tcx,
            self.ty_translator,
            &param_scope,
            &typing_env,
            closure_did,
            parent_args,
        )?;

        // the assumption should quantify over these
        // this is also the closure's scope -- we just lift out all the parameters
        let quantified_scope: specs::GenericScope<'_> = closure_spec.get_generics().to_owned();

        // now we need to figure out the instantiation of the generics
        // this should be the identity instantiation
        let fn_inst = quantified_scope.identity_instantiation();

        info!(
            "Closure shim: Calling {} of {:?} with {:?} and layouts {:?}",
            loc_name, closure_did, fn_inst, syntypes
        );

        let proc_use = code::UsedProcedure::new(loc_name, spec_term, quantified_scope, fn_inst, syntypes);

        Ok(proc_use)
    }

    /// Get the spec record name for the `call` function of the given closure kind.
    pub(crate) fn get_call_spec_record_entry_name(&self, kind: ty::ClosureKind) -> String {
        match kind {
            ty::ClosureKind::Fn => self.fn_spec.method_trait_incl_decls.keys().next().unwrap().to_owned(),
            ty::ClosureKind::FnMut => {
                self.fnmut_spec.method_trait_incl_decls.keys().next().unwrap().to_owned()
            },
            ty::ClosureKind::FnOnce => {
                self.fnonce_spec.method_trait_incl_decls.keys().next().unwrap().to_owned()
            },
        }
    }

    /// Create the scope for the `call_...` function of the impl.
    fn create_impl_fn_scope(
        info: &procedures::ClosureImplInfo<'tcx, 'def>,
        kind: ty::ClosureKind,
    ) -> specs::GenericScope<'def> {
        // we lift the scope, all the generics below to the trait impl, not to the trait method itself.
        let mut new_scope = specs::GenericScope::empty();

        assert!(info.scope.get_surrounding_ty_params_with_assocs().params.is_empty());
        assert!(info.scope.get_surrounding_trait_requirements().is_empty());

        for ty in &info.scope.get_direct_ty_params().params {
            let mut ty = ty.clone();
            ty.set_origin(specs::TyParamOrigin::SurroundingImpl);
            new_scope.add_ty_param(ty);
        }
        for req in info.scope.get_direct_trait_requirements() {
            let mut req = *req;
            req.set_origin(specs::TyParamOrigin::SurroundingImpl);
            new_scope.add_trait_requirement(req);
        }
        for lft in info.scope.get_lfts() {
            let lft = specs::LftParam::new(lft.lft().to_owned(), specs::LftParamOrigin::SurroundingImpl);
            new_scope.add_lft_param(lft);
        }

        // also add the lifetime for the call function itself as a dummy
        if kind == ty::ClosureKind::Fn || kind == ty::ClosureKind::FnMut {
            new_scope.add_lft_param(specs::LftParam::new(
                coq::Ident::new("_ref_lft"),
                specs::LftParamOrigin::LocalLateBound,
            ));
        }

        new_scope
    }

    // TODO: maybe we should intern the `TraitRefInst`, since we are cloning it in here.
    pub(crate) fn generate_call_function_for(
        &self,
        closure_did: DefId,
        closure_meta: &procedures::Meta,
        fn_meta: &procedures::Meta,
        kind: ty::ClosureKind,
        to_impl: ty::ClosureKind,
        closure_spec: &specs::functions::Spec<'def>,
        impl_info: &specs::traits::RefInst<'def>,
        info: &procedures::ClosureImplInfo<'tcx, 'def>,
    ) -> Result<code::Function<'def>, base::TranslationError<'tcx>> {
        // Assemble the inner spec, using the default spec of the closure traits and the impl info
        // we have already assembled before
        let method_name = match to_impl {
            ty::ClosureKind::FnMut => "call_mut".to_owned(),
            ty::ClosureKind::Fn => "call".to_owned(),
            ty::ClosureKind::FnOnce => "call_once".to_owned(),
        };

        let mut builder = code::FunctionBuilder::new(
            fn_meta.get_name(),
            fn_meta.get_code_name(),
            fn_meta.get_spec_name(),
            fn_meta.get_trait_req_incl_name(),
        );

        // Provide the generic scope of the closure itself
        let fn_generics = Self::create_impl_fn_scope(info, to_impl);
        builder.provide_generic_scope(fn_generics);

        let inner_spec = specs::traits::InstantiatedFunctionSpec::new(impl_info.to_owned(), method_name);
        builder.add_trait_function_spec(inner_spec);

        // replicate the Coq params for extra context items
        for x in &closure_spec.early_coq_params.0 {
            builder.add_early_coq_param(x.to_owned());
        }
        for x in &closure_spec.late_coq_params.0 {
            builder.add_late_coq_param(x.to_owned());
        }

        match (kind, to_impl) {
            (ty::ClosureKind::FnMut, ty::ClosureKind::FnOnce) => {
                // impl FnOnce for a FnMut closure
                self.generate_call_shim(
                    &mut builder,
                    info,
                    closure_did,
                    closure_meta,
                    closure_spec,
                    &ShimRefSelf::RefMut,
                )?;
            },
            (ty::ClosureKind::Fn, ty::ClosureKind::FnOnce) => {
                // impl FnOnce for a Fn closure
                self.generate_call_shim(
                    &mut builder,
                    info,
                    closure_did,
                    closure_meta,
                    closure_spec,
                    &ShimRefSelf::RefShr,
                )?;
            },
            (ty::ClosureKind::FnOnce, ty::ClosureKind::FnOnce)
            | (ty::ClosureKind::Fn, ty::ClosureKind::Fn)
            | (ty::ClosureKind::FnMut, ty::ClosureKind::FnMut) => {
                self.generate_call_shim(
                    &mut builder,
                    info,
                    closure_did,
                    closure_meta,
                    closure_spec,
                    &ShimRefSelf::NoRef,
                )?;
            },
            (ty::ClosureKind::Fn, ty::ClosureKind::FnMut) => {
                // impl FnMut for a Fn closure
                self.generate_call_shim(
                    &mut builder,
                    info,
                    closure_did,
                    closure_meta,
                    closure_spec,
                    &ShimRefSelf::RefMutToShr,
                )?;
            },
            (_, _) => {
                unimplemented!(
                    "cannot implement this closure trait right now: kind={kind:?} and to_impl={to_impl:?}"
                );
            },
        }

        let function = builder.into_function(self.fn_arena);

        Ok(function)
    }
}
