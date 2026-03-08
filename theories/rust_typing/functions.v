From refinedrust Require Export type generics.
From refinedrust Require Import programs uninit.
From refinedrust Require Import options.

(** * Function types *)

(* "entry-point" statement *)
Definition introduce_typed_stmt {Σ} `{!typeGS Σ} (E : elctx) (L : llctx) (f : frame_path) (ϝ : lft) (fn : function) (R : typed_stmt_R_t) : iProp Σ :=
  typed_stmt E L f (Goto fn.(f_init)) fn R ϝ.
Global Typeclasses Opaque introduce_typed_stmt.
Global Arguments introduce_typed_stmt : simpl never.

(* TODO: equip function types with namespace parameters for atomic and non-atomic invariants that need to be active when calling it. *)

Section function.
  Context `{!typeGS Σ}.
  (* function return type and condition *)
  (* this does not take an rtype, since we essentially pull that part out to
     [fp_rtype] and [fp_fr] below, in order to support existential quantifiers *)
  Record fn_ret := mk_FR {
    fr_rt : RT;
    fr_ty : type fr_rt;
    fr_ref : fr_rt;
    fr_R : thread_id → iProp Σ;
  }.

  Record fn_params := FP {
    (** Argument types with refinement.
      We also directly require an inG proof for ghost variables to that type.
      Maybe there is a nicer way to bundle that up?
    *)
    fp_atys : list (@sigT RT (λ rt, type rt * rt)%type);
    (* bundled assume condition *)
    fp_Pa : thread_id → iProp Σ;
    (* bundled sidecondition precondition *)
    fp_Sc : thread_id → iProp Σ;
    (* external lifetimes, parameterized over a lifetime for the function *)
    fp_elctx : lft → elctx;
    (* existential condition for return type *)
    fp_extype : Type;
    (* return type *)
    fp_fr: fp_extype → fn_ret;
  }.
  Definition fn_params_add_pre (pre : iProp Σ) (F : fn_params) : fn_params :=
    FP F.(fp_atys) (λ π, pre ∗ F.(fp_Pa) π)%I F.(fp_Sc) F.(fp_elctx) F.(fp_extype) F.(fp_fr).
  Definition fn_params_add_elctx (E : lft → elctx) (F : fn_params) : fn_params :=
    FP F.(fp_atys) F.(fp_Pa) F.(fp_Sc) (λ ϝ, E ϝ ++ F.(fp_elctx) ϝ) F.(fp_extype) F.(fp_fr).

 (**
     Compute a [fn_params] definition that includes the required lifetime constraints for the
     used argument and return types (according to their typeclass instances).
     This is currently a bit more restrictive than it needs to be:
     We don't allow [retty] to depend on [exty], since [exty] should not quantify over any lifetimes for this computation to work.
     FIXME Maybe we can generalize this with some more typeclass magic.
   *)
  Definition map_rtype : (@sigT RT (λ rt, type rt * rt)%type) → rtype :=
    (λ '(existT rt (ty, _)), {| rt_rty := rt; rt_ty := ty|}).
  Definition FP_wf
      (E : lft → elctx)
      (atys : list (@sigT RT (λ rt, type rt * rt)%type))
   (pa : thread_id → iProp Σ)
      (sc : thread_id → iProp Σ)
     (exty : Type)
      (retrt : RT)
      (retty : type retrt)
      (fr_ref : exty → retrt)
      (fr_R : exty → thread_id → iProp Σ) :=
    FP
      atys
      pa
      sc
      (λ ϝ, E ϝ ++
          tyl_wf_E (map map_rtype atys) ++
          tyl_outlives_E (map map_rtype atys) ϝ ++
          ty_wf_E retty ++
          ty_outlives_E retty ϝ)
      exty
      (λ e, mk_FR retrt retty (fr_ref e) (fr_R e)).

(* TODO: move elctx into this? *)
  Record fn_spec := mk_fn_spec {
    fn_A : Type;
    fn_p : fn_A → fn_params;
  }.
  Definition fn_spec_add_pre (pre : iProp Σ) (F : fn_spec) : fn_spec :=
    mk_fn_spec F.(fn_A) (λ x, fn_params_add_pre pre (F.(fn_p) x)).
  Definition fn_spec_add_elctx (E : lft → elctx) (F : fn_spec) : fn_spec :=
    mk_fn_spec F.(fn_A) (λ x, fn_params_add_elctx E (F.(fn_p) x)).


  (* the return continuation for type-checking the body.
    We need to be able to transform ownership of the return type given by [typed_stmt]
      to the type + ensures condition that the function really needs to return *)
  Definition fn_ret_prop {B} π (fr : B → fn_ret) : val → iProp Σ :=
    (λ v,
    (* there exists an inhabitant of the spec-level existential *)
      ∃ x,
      (* st. the return type is satisfied *)
      v ◁ᵥ{π, MetaNone} (fr x).(fr_ref) @ (fr x).(fr_ty) ∗
      (* and the ensures-condition is satisfied *)
      (fr x).(fr_R) π ∗
      (* for Lithium compatibility *)
      True)%I.

  Definition fn_arg_syntys (atys : list (@sigT RT (λ rt, type rt * rt)%type)) : list syn_type :=
    (λ '(existT rt (ty, _)), ty.(ty_syn_type) MetaNone) <$> atys.

  Definition typaram_wf rt st (ty : type rt) : iProp Σ :=
    (∃ _ : TySized ty,
      ⌜ty_allows_writes ty⌝ ∗ ⌜ty_allows_reads ty⌝ ∗ ⌜ty_syn_type ty MetaNone = st⌝ ∗ ty_sidecond ty)%I.
  (*Definition typarams_wf rts (sts : list syn_type) (tys : plist type rts) : iProp Σ :=*)
    (*[∗ list] x ∈ zip sts (pzipl _ tys), typaram_wf _ x.1 (projT2 x.2).*)

  Definition typaram_elctx ϝ rt : type rt → elctx :=
    λ ty, ty_outlives_E ty ϝ ++ ty_wf_E ty.
  Definition typarams_elctx (ϝ : lft) rts (tys : plist type rts) : elctx :=
    concat (pcmap (typaram_elctx ϝ) tys).

  Definition fn_init_context (fn : function) (fps : fn_params) (π : thread_id) (f : frame_id) (lsa : list loc) (sta : list syn_type) : iProp Σ :=
    (* initial credits from the beta step *)
    credit_store 0 0 ∗
    (* initial mask *)
    na_own π ⊤ ∗
    (* current frame *)
    allocated_locals (π, f) (f_args fn).*1 ∗
    (* arg ownership *)
    ([∗list] l;t∈lsa;fps.(fp_atys), let '(existT rt (ty, r)) := t in l ◁ₗ[π, Owned] #r @ (◁ ty)) ∗
    ([∗ list] xl; synty ∈ zip ((f_args fn).*1) lsa; sta, xl.1 is_live{(π, f), synty} xl.2) ∗
    (* sidecondition *)
    fps.(fp_Sc) π ∗
    (* precondition *)
    fps.(fp_Pa) π.

  (** This definition is not yet contractive, and also not a full type.
    We do this below in a separate definition. *)
  Definition typed_function {lfts : nat} {rts : list RT} (π : thread_id) (fn : function) (fp : eq rts rts * (spec_with lfts rts fn_spec)) : iProp Σ :=
    ( (* for any Coq-level parameters *)
      ∀ κs tys x,
      (* and any duration of the function call *)
      ∀ (ϝ : lft),
      (* for any stack frame *)
      ∀ (f : frame_id),
      □ (
      let lya := fn.(f_args).*2 in
      let fps := (fp.2 κs tys).(fn_p) x in
      let sta := fn_arg_syntys fps.(fp_atys) in
      (* the function arg type layouts match what is given in the function [fn]: this is something we assume here *)
      ⌜Forall2 syn_type_has_layout sta lya⌝ -∗
      ∀ (* for any stack locations that get picked nondeterministically... *)
          (lsa : vec loc (length fps.(fp_atys))),
          (* external lifetime context: can require external lifetimes syntactically outlive the function lifetime, as well as syntactic constraints between universal lifetimes *)
          let E := (fps.(fp_elctx) ϝ) in
          (* local lifetime context: the function needs to be alive *)
          let L := [ϝ ⊑ₗ{0} []] in
          fn_init_context fn fps π f lsa sta -∗ introduce_typed_stmt E L (π, f) ϝ fn (
            λ v L2,
            prove_with_subtype E L2 false ProveDirect (fn_ret_prop π fps.(fp_fr) v) (λ L3 _ R3,
            introduce_with_hooks E L3 R3 (λ L4,
            (* we don't really kill it here, but just need to find it in the context *)
            li_tactic (llctx_find_llft_goal L4 ϝ LlctxFindLftFull) (λ _,
            find_in_context FindCreditStore (λ _,
              find_in_context (FindNaOwn π) (λ mask : coPset, ⌜mask = ⊤⌝ ∗ True))
          )))))
    )%I.

  Global Instance typed_function_persistent {lfts : nat} {rts : list (RT)} π fn fp : Persistent (typed_function (lfts:=lfts) (rts := rts) π fn fp) := _.

  (** function pointer type. Requires that the location stores a function that has suitable layouts for the fn_params.
      Note that the fn_params may contain generics: this means that only for particular choices of types to instantiate this,
      this is actually a valid function pointer at the type. This is why we expose the list of argument syn_types in this type.
      The caller will have to show, when calling the function, that the instantiations validate the layout assumptions.
  *)
  Program Definition function_ptr {lfts : nat} (arg_types : list (syn_type)) {rts : list (RT)} (fp : (rts = rts) * (spec_with lfts rts fn_spec)) : type loc := {|
    st_own π f v := (∃ fn, ⌜v = val_of_loc f⌝ ∗ fntbl_entry f fn ∗
      ⌜Forall2 syn_type_has_layout arg_types fn.(f_args).*2⌝ ∗
      ▷ typed_function π fn fp)%I;
    st_has_op_type ot mt := is_ptr_ot ot;
    st_syn_type := FnPtrSynType;
  |}.
  Next Obligation.
    simpl. iIntros (lfts sta rts fp π r v) "(%fn & -> & _)".
    iPureIntro. eexists. split; first by apply syn_type_has_layout_fnptr.
    done.
  Qed.
  Next Obligation.
    intros ??? ? ot mt Hot. apply is_ptr_ot_layout in Hot. rewrite Hot.
    by apply syn_type_has_layout_fnptr.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    simpl. iIntros (lfts lya rts fp ot mt st π r v Hot).
    destruct mt.
    - eauto.
    - iIntros "(%fn & -> & Hfntbl & %Halg & Hfn)".
      iExists fn. iFrame. iPureIntro. split; last done.
      destruct ot; try done. unfold mem_cast. rewrite val_to_of_loc. done.
    - iApply (mem_cast_compat_loc (λ v, _)); first done.
      iIntros "(%fn & -> & _)". eauto.
  Qed.
  Next Obligation.
    intros ???? mt ly Hst.
    apply syn_type_has_layout_fnptr_inv in Hst as ->.
    done.
  Qed.

  Global Instance copyable_function_ptr {lfts : nat} {rts : list (RT)} fal fp :
    Copyable (function_ptr (lfts:=lfts) fal (rts := rts) fp) := _.

  Global Instance function_ptr_sized {lfts : nat} {rts : list (RT)} fal fp :
    TySized (function_ptr (lfts:=lfts) fal (rts := rts) fp) := _.
End function.



Section call.
  Context `{!typeGS Σ}.
  Import EqNotations.

  Lemma type_call_fnptr E L f π (lfts : nat) (rts : list (RT)) eκs etys l v vl tys eqp m (fp : spec_with lfts rts fn_spec) (sta : list syn_type) (T : typed_call_cont_t) :
    let eκs' := list_to_tup eκs in
    find_in_context (FindNaOwn π) (λ mask : coPset,
      ⌜π = f.1⌝ ∗
      (* TODO: do something to ensure invariants are closed before *)
      ⌜mask = ⊤⌝ ∗
      introduce_with_hooks E L ([∗ list] v;t ∈ vl; tys, let '(existT rt (ty, r)) := t in v ◁ᵥ{π, MetaNone} r @ ty) (λ L',
      (*∃ (Heq : lfts = length eκs),*)
      ∃ (κs : prod_vec lft lfts) tys,
      (* TODO: currently we instantiate evars very early to make the xt injection work. maybe move that down once we have a better design *)
      li_tactic (ensure_evars_instantiated_goal (pzipl _ tys) etys) (λ _,
      ⌜take (min (length eκs) lfts) (tup_to_list _ κs) = take (min (length eκs) lfts) eκs⌝ ∗
      ∃ x,
      (*let κs := (rew <- Heq in eκs') in*)
      let fps := (fp κs tys).(fn_p) x in
      (* ensure that type variable evars have been instantiated now *)
      (* show typing for the function's actual arguments. *)
      prove_with_subtype E L' false ProveDirect ([∗ list] v;t ∈ vl; fps.(fp_atys), let '(existT rt (ty, r)) := t in v ◁ᵥ{π, MetaNone} r @ ty) (λ L1 _ R2,
      R2 -∗
      (* the syntypes of the actual arguments match with the syntypes the function assumes *)
      ⌜sta = fmap (λ '(existT rt (ty, _)), ty.(ty_syn_type) MetaNone) fps.(fp_atys)⌝ ∗
      (* precondition *)
      (* TODO it would be good if we could also stratify.
          However a lot of the subsumption instances relating to values need subsume_full.
          Maybe we should port them to a form of owned_subltype?
          but even the logical step thing is problematic.
        *)
      prove_with_subtype E L1 true ProveDirect (fps.(fp_Pa) π) (λ L2 _ R3,
      (* finally, prove the sidecondition *)
      fps.(fp_Sc) π ∗
      ⌜Forall (lctx_lft_alive E L2) L2.*1.*2⌝ ∗
      (* don't normalize this sidecondition, directly shelve it: term is huge and expensive *)
      ⌜shelve_hint (∀ ϝ, elctx_sat (((λ '(_, κ, _), ϝ ⊑ₑ κ) <$> L2) ++ E) L2 (fps.(fp_elctx) ϝ))⌝ ∗
      (* postcondition *)
      ∀ v x', (* v = retval, x' = post existential *)
      (* also donate some credits we are generating here *)
      introduce_with_hooks E L2 (£ (S num_cred) ∗ tr 2 ∗ na_own π mask ∗ R3 ∗ (fps.(fp_fr) x').(fr_R) π ∗ v ◁ᵥ{π, MetaNone} (fps.(fp_fr) x').(fr_ref) @ (fps.(fp_fr) x').(fr_ty)) (λ L3,
      T L3 v _ (fps.(fp_fr) x').(fr_ty) (fps.(fp_fr) x').(fr_ref)))))))
    ⊢ typed_call E L f eκs etys v (v ◁ᵥ{π, m} l @ function_ptr sta (eqp, fp)) vl tys T.
  Proof.
    simpl. iIntros "HT (-> & %fn & -> & He & %Halg & Hfn) Htys" (Φ) "#CTX #HE HL Hf HΦ".
    rewrite /li_tactic/ensure_evars_instantiated_goal.
    iDestruct "HT" as (mask) "(Hna & -> & -> & HT) /=".
    iMod ("HT" with "[] CTX HE HL Htys") as "(%L' & HL & HT)"; first done.
    iDestruct "HT" as "(%aκs & %stys & %Heq & %x & HP)".
    (*set (aκs := list_to_tup eκs).*)
    cbn.
    set (fps := (fp aκs stys).(fn_p) x).
    iApply fupd_wpe. iMod ("HP" with "[] [] [] CTX HE HL") as "(%L1 & % & %R2 & >(Hvl & R2) & HL & HT)"; [done.. | ].
    iDestruct ("HT" with "R2") as "(-> & HT)".
    iMod ("HT" with "[] [] [] CTX HE HL") as "(%L2 & % & %R3 & Hstep & HL & HT)"; [done.. | ].
    iDestruct ("HT") as "(Hsc & %Hal & %Hsat & Hr)".
    (* initialize the function's lifetime *)
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iApply fupd_wpe. iMod (lctx_lft_alive_tok_noend_list with "HE HL") as "(%q & Htok & HL & HL_cl')";
      [done | apply Hal | ].
    iDestruct "CTX" as "#(LFT & LCTX)".
    iMod (llctx_startlft_extra _ _  _ [] with "LFT LCTX Htok") as "(%ϝ & Hϝ & %Hincl & Hkill)"; [set_solver.. | ].
    iPoseProof (Hsat ϝ with "HL []") as "#HE'".
    { iFrame "HE". iApply big_sepL_intro.
      iIntros "!>" (k [κe1 κe2] Hlook).
      apply list_elem_of_lookup_2 in Hlook. simpl.
      apply list_elem_of_fmap in Hlook as (((i & ?) & κs1) & [= <- <-] & ?).
      iApply lft_incl_trans. { iApply lft_incl_syn_sem. done. }
      iApply lft_intersect_list_elem_of_incl.
      rewrite list_elem_of_fmap. exists (i, κe2). split; first done.
      rewrite list_elem_of_fmap. eexists; split; last done. done.
    }

    simpl.
    iAssert ⌜Forall2 has_layout_val vl fn.(f_args).*2⌝%I as %Hall. {
      iClear "Hfn Hr HL Hstep HL_cl HL_cl' Hϝ Hkill Hsc".
      move: Halg. move: (fp_atys fps) => atys Hl.
      iInduction (fn.(f_args)) as [|[? ly]] "IH" forall (vl atys Hl).
      { move: Hl => /=. intros ->%Forall2_nil_inv_r%map_eq_nil. destruct vl => //=. }
      move: Hl.
      simpl. intros (st & atys' & Hst & ? & Ha)%Forall2_cons_inv_r.
      apply map_eq_cons in Ha as (xa & ? & -> & <- & <-).
      destruct vl => //=. iDestruct "Hvl" as "[Hv Hvl]".
      destruct xa as (rt & (ty & r)).
      iDestruct ("IH" with "[//] Hna He Hf HΦ Hvl") as %?.
      iDestruct (ty_has_layout with "Hv") as "(%ly' & % & %)".
      assert (ly = ly') as ->. { by eapply syn_type_has_layout_inj. }
      iPureIntro. constructor => //.
    }

    iAssert (|={⊤}=> [∗ list] v;t ∈ vl;fp_atys fps, let 'existT rt (ty, r) := t in v ◁ᵥ{f.1, MetaNone} r @ ty)%I with "[Hvl]" as ">Hvl".
    { rewrite -big_sepL2_fupd. iApply (big_sepL2_mono with "Hvl").
      iIntros (?? (rt & (ty & r)) ??) "Hv". eauto with iFrame. }

    (* eliminate the logical step *)
    iModIntro. iModIntro.
    iApply (wp_call with "He Hf") => //.
    { by apply val_to_of_loc. }
    iApply (physical_step_step_upd with "Hstep").
    iMod (tr_zero) as "Hc".
    iApply (physical_step_intro_tr with "Hc").
    iNext. iIntros "Hc Hcred". iModIntro.
    iIntros "(HP & HR)".
    iIntros (lsa Hlya) "Ha Hx Hf Halloc".
    iDestruct (big_sepL2_length with "Ha") as %Hlen1.
    iDestruct (big_sepL2_length with "Hx") as %Hlen2.
    specialize (Forall2_length _ _ _ Hlya) as Hlen3.
    rewrite length_fmap in Hlen3.
    rewrite length_map length_zip length_fmap -Hlen3 Nat.min_idempotent in Hlen2.

    iDestruct ("Hfn" $! aκs stys x ϝ (S f.2) with "[]") as "Hfn".
    { iPureIntro. move: Halg. rewrite Forall2_fmap_l => Halg.
      eapply Forall2_impl; first done. intros (rt & ty & r) ly; done. }

    have [lsa' ?]: (∃ (ls : vec loc (length (fp_atys fps))), lsa = ls).
    { rewrite -Hlen2. eexists (list_to_vec _); symmetry; apply vec_to_list_to_vec. }
    subst lsa. simpl.

    iDestruct ("Hfn" $! lsa') as "Hm". unfold introduce_typed_stmt.

    set (RET_PROP v := (∃ κs' locals,
        llctx_elt_interp (ϝ ⊑ₗ{ 0} κs') ∗
        credit_store 0 0 ∗
        current_frame f.1 (S f.2) ∗
        allocated_locals (f.1, S f.2) locals ∗
        na_own f.1 ⊤ ∗
        ([∗ list] x0 ∈ locals,
          ∃ (ly : layout) (l : loc) (st : syn_type), ⌜syn_type_has_layout st ly⌝ ∗ x0 is_live{ (f.1, S f.2), st} l ∗ l ↦|ly|) ∗
        fn_ret_prop f.1 (fp_fr fps) v)%I).
    unfold fn_init_context.
    (* prove the initial context *)
    iSpecialize ("Hm" with "[Hcred Hc $Hna $Halloc $Hsc $HP Ha Hvl $Hx]").
    { (* we use the certificate + other credit to initialize the new functions credit store *)
      iSplitL "Hcred Hc". { rewrite credit_store_eq /credit_store_def.
        iSplitL "Hcred".
        - iApply lc_weaken; last done. unfold num_laters_per_step; lia.
        - iApply tr_weaken; last done. unfold num_laters_per_step; lia. }
      (* initialize arguments *)
      (* reshape to zip lsa' fps; vl *)
      fold fps.
      iApply big_sepL2_from_zip. { done. }
      iApply (big_sepL2_elim_r vl).
      iApply big_sepL2_from_zip. { rewrite length_zip. lia. }
      (* wand Ha *)
      iPoseProof (big_sepL2_to_zip with "Ha") as "Ha".
      iPoseProof (big_sepL_extend_r (fp_atys fps) with "Ha") as "Ha". { rewrite length_zip. lia. }
      iPoseProof (big_sepL2_to_zip with "Ha") as "Ha".
      iEval (rewrite zip_assoc_l (zip_flip vl (fp_atys fps)) zip_fmap_r zip_assoc_r !big_sepL_fmap) in "Ha".
      iApply (big_sepL_wand with "Ha").
      (* wand Hvl *)
      iPoseProof (big_sepL2_to_zip with "Hvl") as "Hvl".
      rewrite zip_flip big_sepL_fmap.
      iPoseProof (big_sepL_extend_l lsa' with "Hvl") as "Hvl". { rewrite length_zip. lia. }
      iPoseProof (big_sepL2_to_zip with "Hvl") as "Hvl".
      rewrite zip_assoc_r big_sepL_fmap.
      iApply (big_sepL_impl with "Hvl").
      iModIntro. iIntros (k ((l' & ty) & v) Hlook).
      destruct ty as [rt [ty r]]. simpl.
      apply lookup_zip in Hlook as (Hlook1 & Hlook3).
      apply lookup_zip in Hlook1 as (Hlook1 & Hlook2). simpl in *.
      iIntros "Hv Hl".
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      opose proof (Forall2_lookup_l _ _ _ _ _ Hlya _) as (lya & Hlook4 & Hlyl); first done.
      opose proof (Forall2_lookup_lr _ _ _ _ _ _ Hall _ _) as Hlyv; [done.. | ].
      opose proof (Forall2_lookup_lr _ _ _ k _ _ Halg _ _) as Halg'.
      { rewrite list_lookup_fmap Hlook2/=//. }
      { done. }
      iExists _. iR. iR.
      iPoseProof (ty_own_val_sidecond with "Hv") as "#$".
      iPoseProof (heap_pointsto_loc_in_bounds with "Hl") as "#Hlb".
      rewrite Hlyv. iR. iExists _. iR. eauto with iFrame. }

    iExists RET_PROP. iSplitL "Hf Hm Hϝ" => /=.
    - iApply wps_fupd.
      iApply ("Hm" with "[$LFT $LCTX] HE' [$Hϝ//] Hf []").
      iIntros (L5 v locals) "HL Hf Hlocals Hloc HT". simpl.
      iMod ("HT" with "[] [] [] [] HE' HL") as "(%L3 & %κs1 & %R4 & Hp & HL & HT)"; [done.. |  | ].
      { rewrite /rrust_ctx. iFrame "#". }
      iMod "Hp" as "(Hret & HR)".
      iMod ("HT" with "[] [$] HE' HL HR") as "(%L6 & HL & HT)"; first done.
      rewrite /llctx_find_llft_goal.
      iDestruct "HT" as "(%HL6 & %κs' & %Hfind & HT)".
      destruct Hfind as (L9 & L10 & ? & -> & -> & Hoc).
      unfold llctx_find_lft_key_interp in Hoc. subst.
      iDestruct "HL" as "(_ & Hϝ & _)".
      iDestruct "HT" as ([n' m']) "(Hstore & HT)"; simpl.
      iDestruct "HT" as (mask) "(Hna & -> & _)"; simpl.
      subst RET_PROP; simpl.
      iExists _. iFrame.
      iApply (credit_store_mono with "Hstore"); lia.
    - (* handle the postcondition at return *)
      iIntros (v). iDestruct 1 as (κs' locals) "(Hϝ & Hstore & Hf & Hlocals & Hna & Hls & HPr)".
      iFrame.
      simpl.
      iPoseProof (credit_store_borrow with "Hstore") as "(Hcred1 & Hat & _)".
      iApply (physical_step_intro_tr with "Hat").
      iNext. iIntros "Hat Hcred".

      iPoseProof ("Hkill" with "Hϝ") as "(Htok & Hkill)".
      iMod ("HL_cl'" with "Htok HL") as "HL".
      iPoseProof ("HL_cl" with "HL") as "HL".
       (*we currently don't actually kill the lifetime, as we don't conceptually need that. *)
      iDestruct ("HPr") as (?) "(Hty & HR2 & _)".
      iMod ("Hr" with "[] [$] HE HL [Hat Hcred Hna HR2 Hty HR]") as "(%L3 & HL & Hr)"; first done.
      { iFrame. simpl. unfold num_laters_per_step.
        iSplitL "Hcred".
        - iApply lc_weaken; last done. unfold num_cred. lia.
        - iApply tr_weaken; last done. lia. }
      iModIntro. iIntros "Hf".
      iApply ("HΦ" with "HL Hf").
      by iApply ("Hr").
  Qed.
  Definition type_call_fnptr_inst := [instance type_call_fnptr].
  Global Existing Instance type_call_fnptr_inst | 10.

End call.

Global Typeclasses Opaque function_ptr.
Global Typeclasses Opaque typed_function.
(** Unfold once they are applied enough *)
Arguments fn_ret_prop _ _ _ /.
(*Arguments typarams_wf _ _ _ _ _ /.*)
Arguments typaram_wf _ _ _ _ _ /.

(** Instance that works if [A] and [B] are not directly unifiable for TC search.
  Needed to work with the tuple projections of the notations defined below. *)
Global Instance list_lookup_total_2 {A B : Type} :
  Inhabited A →
  TCDone (A = B) →
  LookupTotal nat A (list B).
Proof.
  rewrite /TCDone. intros ? ->. apply _.
Defined.

(** ** Notations *)

(* TODO figure out how to annotate the scope properly *)
Local Set Warnings "-inconsistent-scopes".

(* Hack: in order to make this compatible with Coq argument parsing, we declare a small helper notation for arguments *)
Declare Scope fnarg_scope.
Delimit Scope fnarg_scope with F.
Notation "x ':@:' ty" := (existT _ (ty, (RT_xrt (RT_of ty) x))) (at level 90) : fnarg_scope.
Notation "x ':$@:' ty" := (existT _ (ty, x)) (at level 90) : fnarg_scope.
Close Scope fnarg_scope.

Definition arg_ty_is_xrfn `{!typeGS Σ} (ty : sigT (λ rt : RT, type rt * rt)%type) : Prop :=
  let '(existT _ (ty, r)) := ty in
  ty_is_xrfn ty r.

Notation "'fn(∀' κs ':' n '|' tys ':' rts '|' x ':' A ',' E ';' Pa ')' '→' '∃' y ':' B ',' r '@' rty ';' Pr" :=
  ((fun κs tys =>
    mk_fn_spec (A : Type) (fun x =>
    FP_wf
    (λ ϝ, typarams_elctx ϝ (fmap (A := RT * syn_type) fst rts) tys ++ E ϝ)
    (@nil _)
    Pa%I
    (λ π, (* typarams_wf (fmap (A := Type * syn_type) fst rts) (fmap (A := Type * syn_type) snd rts) tys*) True)%I
    B _
    rty (λ y, RT_xrt (RT_of rty) r%I) (λ y, Pr%I)))
    : spec_with n (fmap (A := RT * syn_type) fst rts) fn_spec)
  (at level 99, Pr at level 200, tys pattern, κs pattern, x pattern, y pattern) : stdpp_scope.

Notation "'fn(∀' κs ':' n '|' tys ':' rts '|' x ':' A ',' E ';' x1 ',' .. ',' xn ';' Pa ')' '→' '∃' y ':' B ',' r '@' rty ';' Pr" :=
  ((fun κs tys =>
    (mk_fn_spec (A : Type) ((fun x =>
    FP_wf
    (λ ϝ, typarams_elctx ϝ (fmap (A := RT * syn_type) fst rts) tys ++ E ϝ)
    (@cons (@sigT RT _) x1%F .. (@cons (@sigT RT _) xn%F (@nil (@sigT RT _))) ..)
    Pa%I
    (λ π, (* typarams_wf (fmap (A := Type * syn_type) fst rts) (fmap (A := Type * syn_type) snd rts) tys *) True)%I
    B _
    rty (λ y, RT_xrt (RT_of rty) r%I) (λ y, Pr%I)) : A → fn_params)))
    : spec_with n (fmap (A := RT * syn_type) fst rts) fn_spec)
  (at level 99, Pr at level 200, κs pattern, tys pattern, x pattern, y pattern) : stdpp_scope.
(** With a late precondition Pb *)
Notation "'fn(∀' κs ':' n '|' tys ':' rts '|' x ':' A ',' E ';' Pa '|' Pb ')' '→' '∃' y ':' B ',' r '@' rty ';' Pr" :=
  ((fun κs tys =>
    mk_fn_spec (A : Type) ((fun x =>
    FP_wf
    (λ ϝ, typarams_elctx ϝ (fmap (A := RT * syn_type) fst rts) tys ++ E ϝ)
    (@nil _)
    Pa%I
    (λ π, (*typarams_wf (fmap (A := Type * syn_type) fst rts) (fmap (A := Type * syn_type) snd rts) tys ∗ *) Pb%I π)%I
    B _
    rty (λ y, RT_xrt (RT_of rty) r%I) (λ y, Pr%I)) : A → fn_params))
    : spec_with n (fmap (A := RT * syn_type) fst rts) fn_spec)
  (at level 99, Pr at level 200, tys pattern, κs pattern, x pattern, y pattern) : stdpp_scope.
Notation "'fn(∀' κs ':' n '|' tys ':' rts '|' x ':' A ',' E ';' x1 ',' .. ',' xn ';' Pa '|' Pb ')' '→' '∃' y ':' B ',' r '@' rty ';' Pr" :=
  ((fun κs tys =>
    mk_fn_spec (A : Type) ((fun x =>
    FP_wf
    (λ ϝ, typarams_elctx ϝ (fmap (A := RT * syn_type) fst rts) tys ++ E ϝ)
    (@cons (@sigT RT _) x1%F .. (@cons (@sigT RT _) xn%F (@nil (@sigT RT _))) ..)
    Pa%I
    (λ π, (* typarams_wf (fmap (A := Type * syn_type) fst rts) (fmap (A := Type * syn_type) snd rts) tys ∗ *) Pb%I π)%I
    B _
    rty (λ y, RT_xrt (RT_of rty) r%I) (λ y, Pr%I)) : A → fn_params))
    : spec_with n (fmap (A := RT * syn_type) fst rts) fn_spec)
  (at level 99, Pr at level 200, κs pattern, tys pattern, x pattern, y pattern) : stdpp_scope.

(** Add a new type parameter *)
(*
Definition fn_spec_add_typaram `{!typeGS Σ} {lfts : nat} (rts : list RT)
  (rt : RT) (st : syn_type)
  (F : type rt → spec_with lfts rts fn_spec) :
  spec_with lfts (rt :: rts) fn_spec :=
  λ κs '(ty *:: tys),
  fn_spec_add_elctx (λ ϝ, typaram_elctx ϝ _ ty) $
  fn_spec_add_pre (typaram_wf _ st ty)%I $
  F ty κs tys.
*)

(** Add a new lifetime parameter *)
Definition spec_add_lftparam `{!typeGS Σ} {SPEC} {lfts : nat} (rts : list RT)
  (F : lft → spec_with lfts rts SPEC) :
  spec_with (S lfts) rts SPEC :=
  λ '(κ *:: κs) tys,
  F κ κs tys.

(*
Definition fn_spec_add_typaram_conditions `{!typeGS Σ} {lfts : nat} {rts : list RT}
  (rts2 : list RT) (sts2 : list syn_type) (tys2 : plist type rts2)
  (F : spec_with lfts rts fn_spec) :
  spec_with lfts rts fn_spec :=
  λ κs tys,
    fn_spec_add_elctx (λ ϝ, typarams_elctx ϝ rts2 tys2) $
    fn_spec_add_pre (typarams_wf rts2 sts2 tys2) $
    F κs tys.
 *)

(** Add the elctx. (We cannot add the typaram conditions, because they require the syntype parameter) *)
Global Instance fn_spec_scope_bindable `{!typeGS Σ} :
  ScopeBindable fn_spec := {|
    scope_add_typarams rts tys s :=
      fn_spec_add_elctx (λ ϝ, typarams_elctx ϝ rts tys) s;
|}.

(** Add a new late precondition to a fn specification *)
Definition fn_params_add_late_pre `{!typeGS Σ} (S : fn_params) (pre : thread_id → iProp Σ) : fn_params :=
  FP S.(fp_atys) S.(fp_Pa) (λ π, S.(fp_Sc) π ∗ pre π)%I S.(fp_elctx) S.(fp_extype) S.(fp_fr).
Definition fn_spec_add_late_pre `{!typeGS Σ} (S : fn_spec) (pre : thread_id → iProp Σ) : fn_spec :=
  mk_fn_spec S.(fn_A) (λ a, fn_params_add_late_pre (S.(fn_p) a) pre).


(** Notation to bundle an [eq_refl] proof for [rts] that helps Coq's type inference *)
Ltac get_rts_of_fntype x :=
  lazymatch x with
  | prod_vec _ _ → plist _ ?rts → fn_spec =>
      constr:(rts)
  end.
Notation "'<tag_type>' x" := (
  ltac:(
    let y := constr:(x%function) in
    match type of y with
    | ?ty =>
        let ty2 := eval unfold spec_with in ty in
        let ty3 := eval simpl in ty2 in
        let A := get_rts_of_fntype ty3 in
        refine (@eq_refl _ A, y)
    end
  )) (left associativity, at level 82, only parsing) : stdpp_scope.

(** ** Function subtyping *)
Section function_subsume.
  Context `{!typeGS Σ}.

  (** Given a function typing proof, we can always specialize it to more specific generics *)
  Lemma typed_function_specialize {lfts lfts2 : nat} {rts rts2 : list RT} (S1 : spec_with lfts rts fn_spec) π fn eqp1 eqp2 Fκ Fty :
    typed_function π fn (eqp1, S1) -∗
    typed_function π fn (eqp2, spec! κs : lfts | tys : rts, S1 (Fκ κs) (Fty κs tys)).
  Proof.
    iIntros "Ha".
    rewrite /typed_function.
    iIntros (κs tys). simpl.
    iApply "Ha".
  Qed.


  (* If I have f ◁ F1, then f ◁ F2. *)
  (* I can strengthen the precondition and weaken the postcondition *)
  (*elctx_sat*)
  (* TODO: think about how closures capture lifetimes in their environment.
     lifetimes in the capture shouldn't really show up in their spec at trait-level (a purely safety spec).
     I guess once I want to know something about the captured values (to reason about their functional correctness), I might need to know about lifetimes. However, even then, they should not pose any constraints -- they should just be satisfied, with us only knowing that they live at least as long as the closure body.

     The point is that I want to say that as long as the closure lifetime is alive, all is fine.


     How does the justification that this is fine work?
     Do I explicitly integrate some existential abstraction?
      i.e. functions can pose the existence of lifetimes, as long as they are alive under the function lifetime


     I don't think I can always just subtype that to use the lifetime of the closure. That would definitely break ghostcell etc. And also not everything might be covariant in the lifetime.
  *)
  (* This variant operates directly on our [typed_function] definition, used to statically prove subtyping. *)
  Lemma subsume_typed_function π fn {lfts : nat} {rts : list RT} (eqp1 eqp2 : eq rts rts) (F1 : spec_with lfts rts fn_spec) (F2 : spec_with lfts rts fn_spec) T :
    subsume (typed_function π fn (eqp1, F1)) (typed_function π fn (eqp2, F2)) T :-
      and:
      | drop_spatial;
        ∀ (κs : prod_vec lft lfts) (tys : plist type rts),
        exhale ⌜∀ a b ϝ, elctx_sat (((F2 κs tys).(fn_p) b).(fp_elctx) ϝ) [ϝ ⊑ₗ{ 0} []] (((F1 κs tys).(fn_p) a).(fp_elctx) ϝ)⌝;
        ∀ (b : _),
        inhale (fp_Pa ((F2 κs tys).(fn_p) b) π);
        inhale (fp_Sc ((F2 κs tys).(fn_p) b) π);
        ls ← iterate: fp_atys ((F2 κs tys).(fn_p) b) with [] {{ ty T ls,
               ∀ l : loc,
                inhale (l ◁ₗ[π, Owned] #(projT2 ty).2 @ ◁ (projT2 ty).1); return T (ls ++ [l]) }};
        ∃ (a : _),
        exhale (⌜Forall2 (λ '(existT _ (ty1, _)) '(existT _ (ty2, _)), ty_syn_type ty1 MetaNone = ty_syn_type ty2 MetaNone) (fp_atys ((F1 κs tys).(fn_p) a)) (fp_atys ((F2 κs tys).(fn_p) b))⌝);
        iterate: zip ls (fp_atys ((F1 κs tys).(fn_p) a)) {{ e T, exhale (e.1 ◁ₗ[π, Owned] #(projT2 e.2).2 @ ◁ (projT2 e.2).1); return T }};
        exhale (fp_Pa ((F1 κs tys).(fn_p) a) π);
        exhale (fp_Sc ((F1 κs tys).(fn_p) a) π);
        (* show that F1.ret implies F2.ret *)
        ∀ (vr : val) a2,
        inhale (((F1 κs tys).(fn_p) a).(fp_fr) a2).(fr_R) π;
        inhale (vr ◁ᵥ{π, MetaNone} (((F1 κs tys).(fn_p) a).(fp_fr) a2).(fr_ref) @ (((F1 κs tys).(fn_p) a).(fp_fr) a2).(fr_ty));
        ∃ b2,
        exhale (vr ◁ᵥ{π, MetaNone} (((F2 κs tys).(fn_p) b).(fp_fr) b2).(fr_ref) @ (((F2 κs tys).(fn_p) b).(fp_fr) b2).(fr_ty));
        exhale (((F2 κs tys).(fn_p) b).(fp_fr) b2).(fr_R) π;
        done
      | return T
    .
  Proof.
    iIntros "[#Ha Hb] #Hf". iFrame "Hb".

    rewrite /typed_function.
    iIntros (κs tys b ϝ f) "!>".
    iIntros (Hargly lsa).
    iIntros "(Hcred & Hna & Hlocals & Hargs & Hx & Hsc & Hpre)".
    iSpecialize ("Ha" $! κs tys).
    iDestruct "Ha" as "(%Helctx & Ha)".
    iSpecialize ("Ha" $! b with "Hpre Hsc").
    simpl in *.

    (* provide the argument ownership *)
    set (INV n ls := (⌜ls = take n lsa⌝ ∗ [∗ list] i ↦ l;'(existT rt (ty, r)) ∈ lsa;fp_atys ((F2 κs tys).(fn_p) b),
        if decide (n ≤ i) then l ◁ₗ[ π, Owned] # r @ (◁ ty) else True)%I).
    iPoseProof (iterate_elim1 INV with "Ha [Hargs] []") as "Hb".
    { unfold INV. iR. iApply (big_sepL2_impl with "Hargs").
      iModIntro. iIntros (?? [? []] ??).
      setoid_rewrite decide_True; last lia. eauto. }
    { unfold INV. iModIntro. iIntros (? [rt [ty r]] ? ? Hlook) "(-> & Hi) Hs".
      specialize (lookup_lt_Some _ _ _ Hlook) as Hlt1.
      edestruct (lookup_lt_is_Some_2 lsa i) as (l1 & Hlook1).
      { rewrite length_vec_to_list. lia. }
      iPoseProof (big_sepL2_delete _ _ _ i with "Hi") as "(Ha & Hi)"; [done.. | ].
      simpl. rewrite decide_True; last lia.
      iExists (take (S i) lsa). rewrite -assoc. iR.
      iPoseProof ("Hs" with "Ha") as "Hs".
      erewrite take_S_r; last done.
      iFrame.
      iApply (big_sepL2_impl with "Hi").
      iModIntro. iIntros (k ? [? [??]] ? ?).
      simpl. case_decide.
      { rewrite decide_False; last lia. eauto. }
      case_decide.
      { rewrite decide_True; last lia. eauto. }
      rewrite decide_False; last lia. eauto. }
    iDestruct "Hb" as "(%lsa' & (-> & _) & %a & %Hsts & Hc)".
    clear INV.
    specialize (Forall2_length _ _ _ Hsts) as Hlen.

    (* take the argument ownership *)
    set (INV n := ([∗ list] i ↦ l;'(existT rt (ty, r)) ∈ lsa;fp_atys ((F1 κs tys).(fn_p) a),
        if decide (i < n) then l ◁ₗ[ π, Owned] # r @ (◁ ty) else True)%I).
    iPoseProof (iterate_elim0 INV with "Hc [] []") as "Hb".
    { unfold INV. iApply big_sepL2_intro.
      { rewrite length_vec_to_list. lia. }
      iModIntro. iIntros (?? [? []] ??).
      setoid_rewrite decide_False; last lia. done. }
    { unfold INV. iModIntro. iIntros (? [l [rt [ty r]]] ? Hlook) "Hi Hs".
      apply lookup_zip in Hlook as (Hlook1 & Hlook2).
      rewrite firstn_all2 in Hlook1; first last.
      { rewrite length_vec_to_list. lia. }
      iDestruct "Hs" as "(Hs & $)". simpl.
      rewrite -(list_insert_id lsa i l); last done.
      rewrite -(list_insert_id (fp_atys ((F1 κs tys).(fn_p) a)) i (r :$@: ty)%F); last done.
      opose proof* (big_sepL2_insert lsa (fp_atys ((F1 κs tys).(fn_p) a)) i l (r :$@: ty)%F
        (λ i0 l0 '(existT rt0 (ty0, r0)), if decide (i0 < S i) then l0 ◁ₗ[ π, Owned] # r0 @ (◁ ty0) else True)%I 0%nat) as Hr.
      { eapply lookup_lt_Some; done. }
      { eapply lookup_lt_Some; done. }
      simpl in Hr. rewrite Hr. clear Hr.
      rewrite decide_True; last lia. iFrame.
      rewrite !list_insert_id; [ | done..].
      iApply (big_sepL2_impl with "Hi").
      iModIntro. iIntros (?? [? []] ??) "Ha".
      destruct (decide (k = i)); first done.
      case_decide.
      { rewrite decide_True; first done. lia. }
      { rewrite decide_False; first done. lia. }
    }
    subst INV. simpl.
    iDestruct "Hb" as "(Hargs & Hpre & Hsc & HT)".

    assert ((fn_arg_syntys (fp_atys (fn_p (F1 κs tys) a))) = (fn_arg_syntys (fp_atys (fn_p (F2 κs tys) b)))) as Heq_st.
    { apply Forall2_eq. apply Forall2_fmap_2. eapply Forall2_impl; first apply Hsts.
      intros [? []] [? []]. simpl.
      intros Ha. apply Ha. }
    iSpecialize ("Hf" $! κs tys a ϝ f with "[]").
    { (* the arg assumptions transfer *)
      iPureIntro. rewrite Heq_st. done. }
    rewrite Hlen.
    rewrite Heq_st.
    iSpecialize ("Hf" $! lsa).
    iSpecialize ("Hf" with "[Hcred Hna Hlocals Hargs Hx Hsc Hpre]").
    { iFrame.
      iApply (big_sepL2_impl with "Hargs").
      iModIntro. iIntros (?? [? []] Hlook1 Hlook2).
      rewrite decide_True; first eauto.
      rewrite length_zip.
      rewrite length_take.
      apply lookup_lt_Some in Hlook1.
      apply lookup_lt_Some in Hlook2.
      lia.
    }
    rewrite /introduce_typed_stmt.
    iIntros (?) "#CTX HE HL Hfr Hrt".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HLcl)".
    iDestruct (Helctx with "HL") as "#HEincl".
    iPoseProof ("HLcl" with "HL") as "HL". simpl.
    iSpecialize ("Hf" with "CTX [HE] HL Hfr").
    { by iApply "HEincl". }
    simpl. iApply "Hf".
    iIntros (L' v locals) "HL Hfr Hlocals Hlocs Hpost". simpl.
    iApply ("Hrt" with "HL Hfr Hlocals Hlocs").
    iIntros (????) "_ HE HL".
    iPoseProof ("HEincl" with "HE") as "HE".
    iMod ("Hpost" with "[//] [//] [//] CTX HE HL") as "(%L2 & %κs2 & %R & Hs & HL & Hintro)".
    iMod "Hs" as "((%x & Hrt & Hpost & _) & HR)".
    iDestruct ("HT" with "Hpost Hrt") as "(%y & Hpost & Hrt & _)".
    (* TODO could also allow prove_with_subtype etc here? *)
    iModIntro.
    simpl. iExists L2, [], R. iFrame.
    iSplitR "Hintro"; first done.
    iIntros (??) "_ HE HL HP".
    iPoseProof ("HEincl" with "HE") as "HE".
    rewrite /llctx_find_llft_goal.
    rewrite /FindCreditStore.
    iMod ("Hintro" with "[//] CTX HE HL HP") as "(%L3 & HL & %L4 & %κs3 & % & % & Hc & HT)".
    simpl.
    iModIntro. iExists L3. iFrame.
    by iExists _, _.
  Qed.
  (* NOTE: Don't use the instance generation, as it will instantiate the equalities with [eq_refl]. *)
  Global Instance subsume_typed_function_inst π fn {lfts : nat} {rts : list RT} (eqp1 eqp2 : eq rts rts) (F1 : spec_with lfts rts fn_spec) (F2 : spec_with lfts rts fn_spec) :
    Subsume (typed_function π fn (eqp1, F1)) (typed_function π fn (eqp2, F2)) | 10 :=
    λ T, i2p (subsume_typed_function π fn eqp1 eqp2 F1 F2 T).

  (* This weaker notion operates on the [function_ptr] indirection *)
  Lemma subsume_function_ptr π v l1 l2 sts1 sts2 {lfts : nat} {rts : list RT} eqp1 eqp2 (F1 : spec_with lfts rts fn_spec) (F2 : spec_with lfts rts fn_spec) T :
    subsume (v ◁ᵥ{π, MetaNone} l1 @ function_ptr sts1 (eqp1, F1)) (v ◁ᵥ{π, MetaNone} l2 @ function_ptr sts2 (eqp2, F2)) T :-
    and:
    | drop_spatial;
        exhale ⌜sts1 = sts2⌝;
        ∀ (κs : prod_vec lft lfts) (tys : plist type rts),
        exhale ⌜∀ a b ϝ, elctx_sat (((F2 κs tys).(fn_p) b).(fp_elctx) ϝ) [ϝ ⊑ₗ{ 0} []] (((F1 κs tys).(fn_p) a).(fp_elctx) ϝ)⌝;
        ∀ (b : _),
        inhale (fp_Pa ((F2 κs tys).(fn_p) b) π);
        inhale (fp_Sc ((F2 κs tys).(fn_p) b) π);
        ls ← iterate: fp_atys ((F2 κs tys).(fn_p) b) with [] {{ ty T ls,
               ∀ l : loc,
                inhale (l ◁ₗ[π, Owned] #(projT2 ty).2 @ ◁ (projT2 ty).1); return T (ls ++ [l]) }};
        ∃ (a : _),
        exhale (⌜Forall2 (λ '(existT _ (ty1, _)) '(existT _ (ty2, _)), ty_syn_type ty1 = ty_syn_type ty2) (fp_atys ((F1 κs tys).(fn_p) a)) (fp_atys ((F2 κs tys).(fn_p) b))⌝);
        iterate: zip ls (fp_atys ((F1 κs tys).(fn_p) a)) {{ e T, exhale (e.1 ◁ₗ[π, Owned] #(projT2 e.2).2 @ ◁ (projT2 e.2).1); return T }};
        exhale (fp_Pa ((F1 κs tys).(fn_p) a) π);
        exhale (fp_Sc ((F1 κs tys).(fn_p) a) π);
        (* show that F1.ret implies F2.ret *)
        ∀ (vr : val) a2,
        inhale (((F1 κs tys).(fn_p) a).(fp_fr) a2).(fr_R) π;
        inhale (vr ◁ᵥ{π, MetaNone} (((F1 κs tys).(fn_p) a).(fp_fr) a2).(fr_ref) @ (((F1 κs tys).(fn_p) a).(fp_fr) a2).(fr_ty));
        ∃ b2,
        exhale (vr ◁ᵥ{π, MetaNone} (((F2 κs tys).(fn_p) b).(fp_fr) b2).(fr_ref) @ (((F2 κs tys).(fn_p) b).(fp_fr) b2).(fr_ty));
        exhale (((F2 κs tys).(fn_p) b).(fp_fr) b2).(fr_R) π;
        done
    | exhale ⌜l1 = l2⌝; return T.
  Proof.
    iIntros "(#Ha & (-> & HT))".
    iIntros "Hv". iFrame.
    iDestruct "Ha" as "(-> & Ha)".
    iEval (rewrite /ty_own_val/=) in "Hv".
    iDestruct "Hv" as "(_ & %fn & -> & Hen & %Halg1 & #Htf)".
    iEval (rewrite /ty_own_val/=).
    iR.
    iExists fn. iR. iFrame.
    iR. iNext.
    iPoseProof (subsume_typed_function _ _ _ _ _ (F2) with "[Ha] Htf") as "(Hb & _)".
    { iSplit; first iModIntro.
      (* TODO: somehow fails  to unify... *)
      (*{ done. }*)
    (*iApply "Hb".*)
  (*Qed.*)
  Abort.
  (*Definition subsume_function_ptr_inst := [instance subsume_function_ptr].*)
  (*Global Existing Instance subsume_function_ptr_inst  | 10.*)
  (* TODO: maybe also make this a subsume_full instance *)



  (* A pure version that we can shelve as a pure sidecondition. *)
  Definition function_subtype `{!typeGS Σ} {lfts : nat} {rts : list RT} (a : spec_with lfts rts fn_spec) (b : spec_with lfts rts fn_spec) : Prop :=
    ⊢ ∀ π fn eqp1 eqp2 κs tys,
    subsume (typed_function π fn (eqp1, spec! ( *[]) : 0 | ( *[]) : [], a κs tys))
      (typed_function π fn (eqp2, spec! ( *[]) : 0 | ( *[]) : [], b κs tys)) (True).

  (** Central lemma: we can lift all generics out *)
  Lemma function_subtype_lift_generics_1 {lfts : nat} {rts : list RT} (S1 : spec_with lfts rts fn_spec) (S2 : spec_with lfts rts fn_spec) :
    (∀ κs tys, function_subtype (spec! ( *[]) : 0 | ( *[]) : [], S1 κs tys) (spec! ( *[]) : 0 | ( *[]) : [], S2 κs tys)) →
    function_subtype S1 S2.
  Proof.
    intros Hsub.
    iIntros (π fn eqp1 eqp2 κs tys) "Hf".
    iPoseProof (Hsub κs tys $! _ _ eqp1 eqp2 -[] -[] with "[Hf]") as "(Ha & _)".
    { rewrite /typed_function. iIntros ([] []). iApply "Hf". }
    iL. simpl. done.
  Qed.
  Lemma function_subtype_lift_generics_2 {lfts : nat} {rts : list RT} (S1 : spec_with lfts rts fn_spec) (S2 : spec_with lfts rts fn_spec) :
    function_subtype S1 S2 →
    (∀ κs tys, function_subtype (spec! ( *[]) : 0 | ( *[]) : [], S1 κs tys) (spec! ( *[]) : 0 | ( *[]) : [], S2 κs tys)).
  Proof.
    iIntros (Hsub κs tys).
    iIntros (π fn eqp1 eqp2 [] []) "Hf".
    iApply Hsub. done.
  Qed.
  Lemma function_subtype_lift_generics {lfts : nat} {rts : list RT} (S1 : spec_with lfts rts fn_spec) (S2 : spec_with lfts rts fn_spec) :
    (∀ κs tys, function_subtype (spec! ( *[]) : 0 | ( *[]) : [], S1 κs tys) (spec! ( *[]) : 0 | ( *[]) : [], S2 κs tys)) ↔
    function_subtype S1 S2.
  Proof.
    split; [apply function_subtype_lift_generics_1 | apply function_subtype_lift_generics_2].
  Qed.

  (* We can lift additional preconditions over the inclusion, needed for trait incl requirements. *)
  Lemma function_subtype_lift_late_pre_2 (S1 S2 : fn_spec) (P : thread_id → iProp Σ) `{!∀ π, Persistent (P π)} :
    function_subtype (lfts:= 0) (rts:=[]) (λ '*[] '*[], S1) (λ '*[] '*[], S2) →
    function_subtype (lfts:=0) (rts:=[]) (λ '*[] '*[], fn_spec_add_late_pre S1 P) (λ '*[] '*[], fn_spec_add_late_pre S2 P).
  Proof.
    intros Hsub.
    iIntros (π fn Heq1 Heq2 [] []).
    iPoseProof (Hsub $! π fn Heq1 Heq2 *[] *[]) as "Hsub".
    iIntros "#HT". iSplitL; last done.
    iEval (unfold typed_function).
    iIntros ([] [] x ϝ f); simpl.
    iModIntro. iIntros (??) "(Hc & Hna & Hlocals & Ha & Hl & [Hsc #HP] & Hpre)".
    iDestruct ("Hsub" with "[]") as "(Hsub' & _)".
    { clear. iEval (rewrite /typed_function).
      iIntros ([] []). simpl. iIntros (x ϝ f).
      iModIntro. iIntros (??).
      iIntros "(? & ? & ? & ? & ? & ? & ?)".
      iEval (rewrite /typed_function) in "HT".
      iApply ("HT" $! *[] *[] x ϝ); [done.. | ].
      iFrame "∗ #". }
    simpl.
    iEval (rewrite /typed_function) in "Hsub'".
    iSpecialize ("Hsub'" $! *[] *[]).
    simpl.
    iApply "Hsub'"; last iFrame; done.
  Qed.


  Definition fn_spec_add_linking_condition `{!typeGS Σ} (S : fn_spec) (pre : thread_id → iProp Σ) (ectx : lft → elctx) : fn_spec :=
  fn_spec_add_late_pre (fn_spec_add_elctx ectx S) pre.
  Lemma function_subtype_lift_linking_2 (S1 S2 : fn_spec) (P : thread_id → iProp Σ) (E : lft → elctx) `{!∀ π, Persistent (P π)} :
    function_subtype (lfts:= 0) (rts:=[]) (λ '*[] '*[], S1) (λ '*[] '*[], S2) →
    function_subtype (lfts:=0) (rts:=[])
      (λ '*[] '*[], fn_spec_add_linking_condition S1 P E) (λ '*[] '*[], fn_spec_add_linking_condition S2 P E).
  Proof.
    intros Hsub.
    iIntros (π fn Heq1 Heq2 [] []).
    iPoseProof (Hsub $! π fn Heq1 Heq2 *[] *[]) as "Hsub".
    iIntros "#HT". iSplitL; last done.
    iEval (unfold typed_function).
    iIntros ([] [] x ϝ f); simpl.
    iModIntro. iIntros (??) "(Hs & Hna & Hlocals & Ha & Hl & [Hsc #HP] & Hpre)".
    iDestruct ("Hsub" with "[]") as "(Hsub' & _)".
    { clear. iEval (rewrite /typed_function).
      iIntros ([] []). simpl. iIntros (x ϝ f).
      iModIntro. iIntros (??).
      iIntros "(? & ? & ? & ? & ? & ? & ?)".
      iEval (rewrite /typed_function) in "HT".
      simpl.

      (*
         What is happening here?
         - I guess this doesn't work. The problem is that the elctx of what I prove up there is different.
           This influences other stuff. I don't know how to deal with that.
           I cannot just lift that out.
           So how does the specialization here work then?
         - Maybe I should handle these lifetime constraints differently.
           Why do they arise?
           If I partially specialize, the original constraints probably always imply the new ones.
           i.e., stuff is nicely recursive. But I should check that this is indeed the case.
           What are the fundamental constraints I need?
           +
         TODO look at an example.
         -

         Constraints I need:
         - all the

         Every function is verified against an actual polymorphic specification.
         This verification assumes that the subjective polymorphic context is well-formed.
         With regards to lifetimes, this means:
         - type variables live long enough
         - lifetimes outlive function lifetime

         When I call the function, I need to ensure that this is true.

         If I verify a function with a specialized trait spec (i.e. an impl):
         - I might verify against more specific parameters. I should use these more specific parameters.
           + If I bake it into the specification, what I assume might be too weak or too strong. Or maybe not? If I impl trait for &'a &'b T, then maybe also the well-formedness for that should be included in our contract
            Q: does 'a subset 'b become a constraint that also materializes in the translation anyways? Currently not. If I
           +
         - How do I ensure that these are actually satisfied then?
           + If baked into the spec, then all is good.
           + I could add constraints at linktime. Then the verification has to assume exactly these constraints.
             Also, I have a problem with the way I handle trait inclusions then, as evidenced by this lemma not working.

         => For now, bake into the spec, until I understand this better or this actually makes somethign unprovable.

       *)

      (*
        This lemma would be needed to lift inclusions for trait assumptions.
         e.g. if I assume a specification for a trait method (trait assumption quantified) and I add elctx assumptions, I have a problem.


         Where exactly do I want to add elctx assumptions?
         How do I figure this out?
         -
         - probably need them


         Point: I'm doing an impl. That impl is for a particular set of generics.
         I should dispatch these assumptions probably at the point where I select an impl.
         At that point I'm doing a subtyping proof.
         I'm not generic anymore in these parameters at that point.

         So I guess I'm not doing these things for abstracted impls anyways.
         Only for concrete impls. Abstracted impls have all the stuff already dispatched.

         For the inclusion, I guess the target of the inclusion needs to imply the constraints there. Yeah, that makes sense.


       *)



      (*iSpecialize ("HT" $! *[] *[] x ϝ). *)
      (*simpl. *)
      (*[done.. | ].*)
      (*iFrame "∗ #". }*)
    (*simpl. *)
    (*iEval (rewrite /typed_function) in "Hsub'".*)
    (*iSpecialize ("Hsub'" $! *[] *[]).*)
    (*simpl. *)
    (*iApply "Hsub'"; last iFrame; done.*)
  (*Qed.*)
  Abort.



  Lemma use_function_subtype {lfts : nat} {rts : list RT} eqp1 eqp2 (a : spec_with lfts rts fn_spec) (b : spec_with lfts rts fn_spec) π v l sts m :
    function_subtype a b →
    v ◁ᵥ{π, m} l @ function_ptr sts (eqp1, a) -∗
    v ◁ᵥ{π, m} l @ function_ptr sts (eqp2, b).
  Proof.
    iIntros (Hincl) "Ha".
    rewrite /ty_own_val/=.
    iDestruct "Ha" as "(-> & %fn & -> & Hfn & %Ha & Hf)".
    iR.
    iExists fn. iFrame.
    iR. iR.
    iNext.
    rewrite {2}/typed_function.
    iIntros (κs tys).
    iPoseProof (Hincl $! _ _ _ _ κs tys with "[Hf]") as "(Hb & _)".
    { rewrite /typed_function. iIntros ([] []). iApply "Hf". }
    rewrite /typed_function.
    iApply ("Hb" $! -[] -[]).
    Unshelve. all: done.
  Qed.

  Global Instance function_subtype_refl {lfts : nat} {rts : list RT} :
    Reflexive (function_subtype (lfts:=lfts) (rts:=rts)).
  Proof.
    intros S1.
    iIntros (π fn eqp1 eqp2 κs tys).
    rewrite (UIP_refl _ _ eqp1).
    rewrite (UIP_refl _ _ eqp2).
    iIntros "Ha". iFrame.
  Qed.
  Global Instance function_subtype_trans {lfts : nat} {rts : list RT} :
    Transitive (function_subtype (lfts:=lfts) (rts:=rts)).
  Proof.
    intros S1 S2 S3.
    rewrite /function_subtype.
    intros Hs1 Hs2.
    iIntros (π fn ? ? κs tys).
    iIntros "Ha".
    iPoseProof (Hs1 with "Ha") as "(Hb & _)".
    by iApply Hs2.
    Unshelve. done.
  Qed.

  Class FunctionSubtype {lfts : nat} {rts : list RT} (a : spec_with lfts rts fn_spec) (b : spec_with lfts rts fn_spec) : Prop := make_function_subtype : function_subtype a b.

  (** Alternative lemma for calling function pointers that simplifies first *)
  Lemma type_call_fnptr_simplify E L π f κs etys v l sta {lfts : nat} {rts : list RT} eqp (S1 : spec_with lfts rts fn_spec) (S2 : spec_with lfts rts fn_spec) vs args m {SH : FunctionSubtype S1 S2} T :
    typed_call E L f κs etys v (v ◁ᵥ{π, m} l @ function_ptr sta (eqp, S2)) vs args T
    ⊢ typed_call E L f κs etys v (v ◁ᵥ{π, m} l @ function_ptr sta (eqp, S1)) vs args T.
  Proof.
    iIntros "Ha". rewrite /typed_call.
    iIntros "Hs".
    iPoseProof (use_function_subtype with "Hs") as "Hs"; first done.
    iApply ("Ha" with "Hs").
  Qed.
  Definition type_call_fnptr_simplify_inst := [instance type_call_fnptr_simplify].
  Global Existing Instance type_call_fnptr_simplify_inst | 1.

  (** Marker for automation to find trait inclusions *)
  Definition trait_incl_def (P : Prop) := P.
  Definition trait_incl_aux (P : Prop) : seal (trait_incl_def P). Proof. by eexists. Qed.
  Definition trait_incl_marker (P : Prop) := (trait_incl_aux P).(unseal).
  Definition trait_incl_marker_unfold (P : Prop) : trait_incl_marker P = P := (trait_incl_aux P).(seal_eq).

  (** Lift trait inclusions to polymorphic contexts *)
  Definition lift_trait_incl {A} (F : A → A → Prop) {lfts : nat} {rts : list RT} (a1 a2 : spec_with lfts rts A) :=
    ∀ lfts tys, F (a1 lfts tys) (a2 lfts tys).

End function_subsume.
(* The last argument might contain evars when we start the search *)
Global Hint Mode FunctionSubtype + + + - + - : typeclass_instances.
Global Typeclasses Opaque function_subtype.
Global Arguments function_subtype : simpl never.
