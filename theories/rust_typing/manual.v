From iris.proofmode Require Import coq_tactics reduction string_ident.
From refinedrust Require Import programs program_rules array.array automation value.
From refinedrust Require Import options.


(** * Proofmode support for manual proofs *)

Section updateable.
  Context `{!typeGS Σ}.

  Definition updateable (E : elctx) (L : llctx) (T : llctx → iProp Σ) : iProp Σ :=
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L ={⊤}=∗
    ∃ L2, llctx_interp L2 ∗ T L2.
  Class Updateable (P : iProp Σ) := {
    updateable_E : elctx;
    updateable_L : llctx;
    updateable_core : elctx → llctx → iProp Σ;
    updateable_prove E L : updateable E L (λ L2, updateable_core E L2) -∗ updateable_core E L;
    updateable_eq : updateable_core updateable_E updateable_L ⊣⊢ P
  }.

  Lemma updateable_mono E L T1 T2 :
    updateable E L T1 -∗
    (∀ L, T1 L -∗ T2 L) -∗
    updateable E L T2.
  Proof.
    iIntros "HT Hw".
    iIntros "#CTX #HE HL".
    iMod ("HT" with "CTX HE HL") as "(%L2 & HL & HT)".
    iSpecialize ("Hw" with "HT").
    iExists L2. by iFrame.
  Qed.
  Lemma updateable_intro E L T :
    T L ⊢ updateable E L T.
  Proof.
    iIntros "HT #CTX HE HL".
    iExists L. by iFrame.
  Qed.

  Lemma add_updateable P `{!Updateable P} :
    updateable updateable_E updateable_L (λ L2, updateable_core updateable_E L2) ⊢ P.
  Proof.
    iIntros "HT".
    iApply updateable_eq.
    iApply updateable_prove.
    iApply (updateable_mono with "HT").
    eauto.
  Qed.

  Global Program Instance updateable_typed_val_expr E L f e T :
    Updateable (typed_val_expr E L f e T) := {|
      updateable_E := E;
      updateable_L := L;
      updateable_core E L := typed_val_expr E L f e T;
  |}.
  Next Obligation.
    iIntros (_ _ ? e T E L).
    rewrite /typed_val_expr.
    iIntros "HT" (?) "#CTX #HE HL Hf Hc".
    iApply fupd_wpe. iMod ("HT" with "CTX HE HL") as "(%L2 & HL & HT)".
    iApply ("HT" with "CTX HE HL Hf Hc").
  Qed.
  Next Obligation.
    simpl. eauto.
  Qed.

  Global Program Instance updateable_typed_call E L f κs etys v (P : iProp Σ) vl tys T :
    Updateable (typed_call E L f κs etys v P vl tys T) := {|
      updateable_E := E;
      updateable_L := L;
      updateable_core E L := typed_call E L f κs etys v P vl tys T;
  |}.
  Next Obligation.
    iIntros (? ? ? ? ? ? ? ? ? ? ? ?).
    rewrite /typed_call.
    iIntros "HT HP Ha".
    iIntros (?) "#CTX #HE HL Hf Hc".
    iApply fupd_wpe. iMod ("HT" with "CTX HE HL") as "(%L2 & HL & HT)".
    iApply ("HT" with "HP Ha CTX HE HL Hf Hc").
  Qed.
  Next Obligation.
    simpl. eauto.
  Qed.


  Global Program Instance updateable_typed_stmt E L f s rf R ϝ :
    Updateable (typed_stmt E L f s rf R ϝ) := {|
      updateable_E := E;
      updateable_L := L;
      updateable_core E L := typed_stmt E L f s rf R ϝ;
  |}.
  Next Obligation.
    iIntros (_ _ ? ? ? ? ? E L).
    iIntros "HT". rewrite /typed_stmt.
    iIntros (?) "#CTX #HE HL Hcont".
    iMod ("HT" with "CTX HE HL") as "(%L2 & HL & HT)".
    iApply ("HT" with "CTX HE HL Hcont").
  Qed.
  Next Obligation.
    simpl. eauto.
  Qed.

  Global Program Instance updateable_updateable E L T :
    Updateable (updateable E L T) := {|
      updateable_E := E;
      updateable_L := L;
      updateable_core E L := updateable E L T;
    |}.
  Next Obligation.
    iIntros (_ _ ? ? ?) "HT".
    rewrite /updateable.
    iIntros "#CTX #HE HL".
    iMod ("HT" with "CTX HE HL") as "(%L2 & HL & HT)".
    iApply ("HT" with "CTX HE HL").
  Qed.
  Next Obligation.
    eauto.
  Qed.

  Lemma fupd_typed_val_expr `{!typeGS Σ} E L f e T :
    (|={⊤}=> typed_val_expr E L f e T) -∗ typed_val_expr E L f e T.
  Proof.
    rewrite /typed_val_expr.
    iIntros "HT" (?) "CTX HE HL Hf Hc".
    iApply fupd_wpe. iMod ("HT") as "HT". iApply ("HT" with "CTX HE HL Hf Hc").
  Qed.
  Lemma fupd_typed_call `{!typeGS Σ} E L f κs etys v (P : iProp Σ) vl tys T :
    (|={⊤}=> typed_call E L f κs etys v P vl tys T) -∗ typed_call E L f κs etys v P vl tys T.
  Proof.
    rewrite /typed_call.
    iIntros "HT HP Ha".
    iIntros (?) "CTX HE HL Hf Hc".
    iApply fupd_wpe. iMod ("HT") as "HT". iApply ("HT" with "HP Ha CTX HE HL Hf Hc").
  Qed.

  Lemma fupd_typed_stmt `{!typeGS Σ} E L f s rf R ϝ :
    ⊢ (|={⊤}=> typed_stmt E L f s rf R ϝ) -∗ typed_stmt E L f s rf R ϝ.
  Proof.
    iIntros "HT". rewrite /typed_stmt. iIntros (?) "CTX HE HL Hf Hcont".
    iMod ("HT") as "HT". iApply ("HT" with "CTX HE HL Hf Hcont").
  Qed.
End updateable.

Section updateable_rules.
  Context `{!typeGS Σ} {P} `{!Updateable P}.

  Lemma updateable_add_fupd :
    (|={⊤}=> updateable_core updateable_E updateable_L)
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "CTX HE HL".
    iMod "HT" as "$". by iFrame.
  Qed.

  (** Access an array element, moving its ownership out *)
  Lemma updateable_typed_array_access l off st :
    find_in_context (FindLoc l) (λ '(existT _ (lt, r, k, π)),
      typed_array_access π updateable_E updateable_L l off st lt r k (λ L2 rt2 ty2 len2 iml2 rs2 k2 rte lte re,
        l ◁ₗ[π, k2] #rs2 @ ArrayLtype ty2 len2 iml2 -∗
        (l offsetst{st}ₗ off) ◁ₗ[π, k2] re @ lte -∗
        updateable_core updateable_E L2))
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    rewrite /FindLoc /find_in_context/=.
    iDestruct "HT" as ([rt [[[lt r] k] π]]) "(Ha & Hb)".
    rewrite /typed_array_access.
    iMod ("Hb" with "[] [] [] CTX HE HL Ha") as "(%L2 & %k2 & %rt2 & %ty2 & %len & %iml & %rs2 & %rte & %re & %lte & Hl & He & HL & HT)";
    [set_solver.. | ].
    iPoseProof ("HT" with "Hl He") as "Ha".
    iModIntro. iExists _. iFrame.
  Qed.

  (* Extract an untyped value *)
  Lemma updateable_extract_value l :
    find_in_context (FindLoc l) (λ '(existT rt (lt, r, bk, π)),
      ∃ ty r', ⌜bk = Owned⌝ ∗ ⌜lt = ◁ty⌝ ∗ ⌜r = #r'⌝ ∗
      li_tactic (compute_layout_goal (ty.(ty_syn_type) MetaNone)) (λ ly,
      (∀ v3, v3 ◁ᵥ{π, MetaNone} r' @ ty -∗
        l ◁ₗ[π, Owned] #v3 @ (◁ value_t (UntypedSynType ly)) -∗
        updateable_core updateable_E updateable_L)))
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    rewrite /FindLoc /find_in_context.
    iDestruct "HT" as ([rt [[[lt r] bk] π]]) "(Ha & Hb)"; simpl.
    iDestruct "Hb" as "(%ty & %r' & -> & -> & -> & HT)".
    rewrite /compute_layout_goal. simpl.
    iDestruct ("HT") as "(%ly & %Hst & HT)".
    iMod (ofty_own_split_value_untyped with "Ha") as "Ha"; [done.. | ].
    iDestruct "Ha" as "(%v & Hv & Hl)".
    iPoseProof ("HT" with "Hv Hl") as "HT".
    iModIntro. iExists _. iFrame.
  Qed.

  (* Extract a typed value *)
  Lemma updateable_extract_typed_value l :
    find_in_context (FindLoc l) (λ '(existT rt (lt, r, bk, π)),
      ∃ ty r', ⌜bk = Owned⌝ ∗ ⌜lt = ◁ty⌝ ∗ ⌜r = #r'⌝ ∗
      (∀ v3, v3 ◁ᵥ{π, MetaNone} r' @ ty -∗
        l ◁ₗ[π, Owned] #v3 @ (◁ value_t (st_of ty MetaNone)) -∗
        updateable_core updateable_E updateable_L))
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    rewrite /FindLoc /find_in_context.
    iDestruct "HT" as ([rt [[[lt r] bk] π]]) "(Ha & Hb)"; simpl.
    iDestruct "Hb" as "(%ty & %r' & -> & -> & -> & HT)".
    (*rewrite /compute_layout_goal. simpl.*)
    iPoseProof (ltype_own_has_layout with "Ha") as "(%ly & %Hst & %Hly)".
    iMod (ofty_own_split_value_untyped with "Ha") as "Ha"; [done.. | ].
    iDestruct "Ha" as "(%v & Hv & Hl)".
    iPoseProof (ofty_value_untyped_make_typed with "Hl") as "Hl"; first done.
    iPoseProof ("HT" with "Hv Hl") as "HT".
    iModIntro. iExists _. iFrame.
  Qed.

  (** Merge a value *)
  Lemma updateable_merge_value l :
    find_in_context (FindLoc l) (λ '(existT rt (lt, r, bk, π)),
      ∃ v st,
        subsume_full updateable_E updateable_L false (l ◁ₗ[π, bk] r @ lt) (l ◁ₗ[π, Owned] #v @ ◁ value_t st)
        (λ L2 R2,
        find_in_context (FindVal v) (λ '(existT rt (ty', r', π', m')),
        ⌜π' = π⌝ ∗ ⌜m' = MetaNone⌝ ∗
        find_tc_inst (TySized ty') (λ _,
        ⌜ty_has_op_type ty' (use_op_alg' (ty'.(ty_syn_type) MetaNone)) MCCopy⌝ ∗
        ⌜ty'.(ty_syn_type) MetaNone = st⌝ ∗
        introduce_with_hooks updateable_E L2 ((l ◁ₗ[π, Owned] #r' @ ◁ ty') ∗ R2)%I (λ L3,
          updateable_core updateable_E L3)))))
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    rewrite /FindLoc /find_in_context.
    iDestruct "HT" as ([rt [[[lt r] bk] π]]) "(Ha & %v & %st & HT)"; simpl.
    rewrite /subsume_full.
    iMod ("HT" with "[] [] [] CTX HE HL Ha") as "(%L2 & %R2 & >(Hl & HR) & HL & HT)"; [done.. | ].
    iDestruct "HT" as ([rt' [[[ty' r'] π'] m']]) "(Hv & -> & -> & % & %Hot & %Heq & HT)" => /=.
    iPoseProof (ltype_own_has_layout with "Hl") as "#(%ly & %Hst &_)".
    iPoseProof (ofty_own_merge_value with "Hv Hl") as "Ha".
    { subst st. destruct (ty_syn_type ty'); try done.
      simp_ltypes in Hst. simpl in Hst.
      specialize (syn_type_has_layout_untyped_inv _ _ Hst) as (-> & _).
      done. }
    rewrite /introduce_with_hooks.
    iMod ("HT" with "[] HE HL [$Ha $HR]") as "(%L3 & HL & HT)"; first done.
    by iFrame.
  Qed.

  (** Split an into two parts *)
  Lemma updateable_split_array l (k : nat) :
    find_in_context (FindLoc l) (λ '(existT rt (lt, r, bk, π)),
    ∃ rt', ⌜rt = listRT (place_rfnRT rt')⌝ ∗
      ∃ rs n (ty : type rt'),
        subsume_full updateable_E updateable_L false (l ◁ₗ[π, bk] r @ lt) (l ◁ₗ[π, Owned] #rs @ ◁ array_t n ty) (λ L2 R2,
        ⌜k ≤ n⌝ ∗
        ((l ◁ₗ[π, Owned] #(take k rs) @ (◁ array_t k ty) -∗
         (l offsetst{st_of ty MetaNone}ₗ k) ◁ₗ[π, Owned] #(drop k rs) @ (◁ array_t (n - k) ty) -∗
         introduce_with_hooks updateable_E L2 R2 (λ L3,
          updateable_core updateable_E L3)))))
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    rewrite /FindLoc /find_in_context.
    iDestruct "HT" as ([rt [[[lt r] bk] π]]) "(Ha & %rt' & -> & %rs & %n & %ty & HT)"; simpl.
    rewrite /subsume_full.
    iMod ("HT" with "[] [] [] CTX HE HL Ha") as "(%L2 & %R2 & >(Hl & HR) & HL & %Hlt & HT)"; [done.. | ].
    iMod (array_t_ofty_split _ _ _ k (n - k) with "Hl") as "(Hl1 & Hl2)"; [done | lia | ].
    unfold introduce_with_hooks.
    iPoseProof  ("HT" with "Hl1 Hl2 [//] HE HL HR") as "HT".
    iMod (fupd_mask_mono with "HT") as "(%L3 & HL & HT)"; first done.
    by iFrame.
  Qed.

  (** Reshape an array *)
  Lemma updateable_reshape_array l num size :
    find_in_context (FindLoc l) (λ '(existT rt (lt, r, bk, π)),
      ∃ rt', ⌜rt = listRT (place_rfnRT rt')⌝ ∗
      ∃ rs n (ty : type rt'),
        subsume_full updateable_E updateable_L false (l ◁ₗ[π, bk] r @ lt) (l ◁ₗ[π, Owned] #rs @ ◁ array_t n ty) (λ L2 R2,
        ⌜n = (num * size)%nat⌝ ∗
        ⌜num ≠ 0%nat⌝ ∗
        (l ◁ₗ[π, Owned] #(<#> reshape (replicate num size) rs) @ (◁ array_t num (array_t size ty)) -∗
         introduce_with_hooks updateable_E L2 R2 (λ L3,
          updateable_core updateable_E L3))))
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    rewrite /FindLoc /find_in_context.
    iDestruct "HT" as ([rt [[[lt r] bk] π]]) "(Ha & %rt' & -> & %rs & %n & %ty & HT)"; simpl.
    rewrite /subsume_full.
    iMod ("HT" with "[] [] [] CTX HE HL Ha") as "(%L2 & %R2 & >(Hl & HR) & HL & -> & % & HT)"; [done.. | ].
    iMod (array_t_ofty_reshape _ _ _ _ _ _ size num with "Hl") as "Hl"; [done | lia | lia | ].
    unfold introduce_with_hooks.
    iPoseProof  ("HT" with "Hl [//] HE HL HR") as "HT".
    iMod (fupd_mask_mono with "HT") as "(%L3 & HL & HT)"; first done.
    by iFrame.
  Qed.


  (** Subtype a location to a given place type *)
  Lemma updateable_subsume_to l {rt2} (lt2 : ltype rt2) (r2 : place_rfn rt2) :
    find_in_context (FindLoc l) (λ '(existT rt (lt, r, bk, π)),
      subsume_full updateable_E updateable_L false (l ◁ₗ[π, bk] r @ lt) (l ◁ₗ[π, bk] r2 @ lt2) (λ L2 R2,
        introduce_with_hooks updateable_E L2 (l ◁ₗ[π, bk] r2 @ lt2 ∗ R2) (λ L3,
          updateable_core updateable_E L3)))
    ⊢ P.
  Proof.
    iIntros "HT".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    rewrite /FindLoc /find_in_context.
    iDestruct "HT" as ([rt [[[lt r] bk] π]]) "(Ha & Hb)"; simpl.
    rewrite /subsume_full.
    iMod ("Hb" with "[] [] [] CTX HE HL Ha") as "(%L2 & %R2 & Hs & HL & HT)"; [done.. | ].
    simpl. iMod "Hs" as "Hs".
    rewrite /introduce_with_hooks.
    iMod ("HT" with "[] HE HL Hs") as "(%L3 & HL & HT)"; first done.
    by iFrame.
  Qed.

  Lemma updateable_subsume_uninit_to l (st : syn_type) :
    find_in_context (FindLoc l) (λ '(existT rt (lt, r, bk, π)),
      subsume_full updateable_E updateable_L false (l ◁ₗ[π, bk] r @ lt) (l ◁ₗ[π, bk] .@ ◁ uninit st) (λ L2 R2,
        introduce_with_hooks updateable_E L2 (l ◁ₗ[π, bk] .@ (◁ uninit st) ∗ R2) (λ L3,
          updateable_core updateable_E L3)))
    ⊢ P.
  Proof.
    iApply updateable_subsume_to.
  Qed.

  (* TODO: add lemma for unfolding / subtyping? *)


  Lemma updateable_copy_lft n1 n2 :
    (∃ M, named_lfts M ∗
      li_tactic (compute_map_lookup_nofail_goal M n2) (λ κ2,
      li_tactic (simplify_lft_map_goal (named_lft_update n1 κ2 (named_lft_delete n1 M))) (λ M',
        named_lfts M' -∗ updateable_core updateable_E updateable_L)))
    ⊢ P.
  Proof.
    rewrite /compute_map_lookup_nofail_goal.
    iIntros "(%M & Hnamed & %κ2 & _ & Hs)".
    unshelve iApply add_updateable; first apply _.
    iIntros "#CTX #HE HL".
    unfold simplify_lft_map_goal. iDestruct "Hs" as "(%M' & _ & Hs)".
    iModIntro. iExists updateable_L.
    iFrame. iApply ("Hs" with "Hnamed").
  Qed.

  Lemma updateable_strip_guards :
    iterate_with_hooks updateable_E updateable_L StripGuarded (λ L _,
      updateable_core updateable_E L)
    ⊢ P.
  Proof.
    iIntros "HT". unshelve iApply add_updateable; first apply _.
    iIntros "#CTX HE HL".
    unfold iterate_with_hooks.
    iMod ("HT" with "[] HE HL") as "(%L2 & % & HL & Ha)"; first done.
    by iFrame.
  Qed.

  (** Discard the opened invariant on an owned location, removing the obligation to re-establish the invariant *)
  Lemma opened_owned_discard (rt_cur rt_inner rt_full : RT) (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Pre Post π l r :
    l ◁ₗ[π, Owned] r @ OpenedLtype lt_cur lt_inner lt_full Pre Post -∗
    l ◁ₗ[π, Owned] r @ lt_cur.
  Proof.
    rewrite ltype_own_opened_unfold.
    iIntros "(%ly & % & % & ? & % & % & Hcur & _)".
    done.
  Qed.

End updateable_rules.

Ltac add_updateable :=
  match goal with
  | |- envs_entails _ ?P =>
      unshelve notypeclasses refine (tac_fast_apply (add_updateable P) _);
      [ apply _ | apply _ | ]
  end.
Tactic Notation "apply_update" uconstr(H) :=
  refine (tac_fast_apply H _).

Section test.
  Context `{!typeGS Σ}.

  Lemma updateable_updateable_b E L (l : loc) (off : Z) (st : syn_type) :
    ⊢ updateable E L (λ _, True).
  Proof.
    iStartProof.
    add_updateable.
    add_updateable.
    unshelve iApply (updateable_typed_array_access l off st).
    idtac.
  Abort.

  Lemma typed_s_updateable E L f s rf R ϝ (l : loc) (off : Z) (st : syn_type) :
    ⊢ typed_stmt E L f s rf R ϝ.
  Proof.
    iStartProof.
    unshelve apply_update (updateable_typed_array_access l off st).
    idtac.
  Abort.
End test.

Section extra_rules.
  Context `{!typeGS Σ}.

  (* TODO: ideally, we could do this anytime, not just at prove_with_subtype, by using logical_step receipts. *)
  Lemma prove_with_subtype_stratify l E L pm Q T :
    find_in_context (FindLoc l) (λ '(existT rt (lt, r, bk, π)),
      stratify_ltype π E L StratMutNone StratNoUnfold StratRefoldFull StratifyUnblockOp l lt r bk (λ L2 R rt' lt' r',
      cast_ltype_to_type E L2 lt' (λ ty,
        prove_with_subtype E L2 true pm (l ◁ₗ[π, bk] r' @ (◁ ty) -∗ R -∗ Q) T)))
    ⊢ prove_with_subtype E L true pm Q T.
  Proof.
    unfold find_in_context,FindLoc. simpl.
    iIntros "(%x & Ha)".
    destruct x as [rt (((lt & r) & bk) & π)].
    iDestruct "Ha" as "(Hl & HT)".
    rewrite /prove_with_subtype.
    iIntros (????) "#CTX #HE HL".
    rewrite /stratify_ltype.
    iMod ("HT" with "[//] [//] [//] CTX HE HL Hl") as "(%L2 & %R & %rt' & %lt' & %r' & HL & %Hst' & Hstep & HT)".
    rewrite /cast_ltype_to_type.
    iDestruct "HT" as "(%ty & %Heqt & HT)".
    iPoseProof (full_eqltype_use F with "CTX HE HL") as "(Hincl & HL)"; first done; first apply Heqt.
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L3 & %κs2 & %R' & Hstep' & HL & HT)".
    simpl. iFrame.
    iApply logical_step_fupd.
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_wand with "Hstep'").
    iModIntro. iIntros "(Ha & $) (Hl & HR)".
    destruct pm.
    - iMod ("Hincl" with "Hl") as "Hl". iApply ("Ha" with "[$] [$]").
    - iMod ("Hincl" with "Hl") as "Hl". iModIntro.
      iIntros "Hdead". iMod ("Ha" with "Hdead") as "Ha".
      iModIntro. iApply ("Ha" with "[$] [$]").
  Qed.

  Lemma prove_with_subtype_inherit_manual E L step pm κ κ' P Q T :
    lctx_lft_incl E L (lft_intersect_list κ') (lft_intersect_list κ) →
    Inherit κ' Q -∗
    (Q -∗ P) -∗
    T L [] True%I -∗
    prove_with_subtype E L step pm (Inherit κ P) T.
  Proof.
    iIntros (Hi1) "Hinh HQP HT".
    rewrite /prove_with_subtype.
    iIntros (????) "#CTX #HE HL".
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl1"; first apply Hi1.
    (*iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl2"; first apply Hi2. *)
    iPoseProof (Inherit_mono with "Hincl1 Hinh") as "Hinh".
    iPoseProof (Inherit_update with "[HQP] Hinh") as "Hinh".
    { iIntros (?) "HQ". iApply ("HQP" with "HQ"). }
    iExists _, _, _. iFrame. iApply maybe_logical_step_intro.
    iModIntro. iL. destruct pm; iFrame. eauto.
  Qed.
End extra_rules.

Section credits.
  Context `{!typeGS Σ}.

  Lemma tac_credit_store_acquire_guard P :
    find_in_context FindCreditStore (λ '(n, m),
      ⌜fast_lia_hint (5 ≤ n)⌝ ∗
      ⌜fast_lia_hint (1 ≤ m)⌝ ∗
      (credit_store (n - 5) (m - 1) -∗ have_creds -∗ P))
    ⊢ P.
  Proof.
    rewrite /FindCreditStore/find_in_context/=.
    iIntros "(%p & Hstore & HT)". destruct p as [n m].
    unfold fast_lia_hint.
    iDestruct "HT" as "(% & % & HT)".
    iPoseProof (credit_store_scrounge 5 with "Hstore") as "(Hcred & Hstore)".
    { done. }
    iPoseProof (credit_store_scrounge_tr 1 with "Hstore") as "(Htr & Hstore)".
    { done. }
    iApply ("HT" with "Hstore").
    iFrame.
  Qed.
End credits.
Tactic Notation "iAcquireCredits" "as" constr(H) :=
  iApply tac_credit_store_acquire_guard;
  repeat (liFindInContext || liSep || liSideCond);
  li_unfold_lets_in_context;
  iIntros "?";
  iIntros H.


Lemma tac_typed_val_expr_bind' `{!typeGS Σ} E L f K e T :
  typed_val_expr E L f (W.to_expr e) (λ L' v m rt ty r,
    introduce_with_hooks E L' (v ◁ᵥ{f.1, m} r @ ty) (λ L2,
      typed_val_expr E L2 f (W.to_expr (W.fill K (W.Val v))) T)) -∗
  typed_val_expr E L f (W.to_expr (W.fill K e)) T.
Proof.
  iIntros "He".
  rewrite /typed_val_expr.
  iIntros (Φ) "#CTX #HE HL Hf Hcont".
  iApply tac_wpe_bind'.
  iApply ("He" with "CTX HE HL Hf").
  iIntros (L' v m rt ty r) "HL Hf Hv Hcont'".
  rewrite /introduce_with_hooks.
  iMod ("Hcont'" with "[] HE HL Hv") as "(%L2 & HL & Hcont')"; first done.
  iApply ("Hcont'" with "CTX HE HL Hf"). done.
Qed.
Lemma tac_typed_val_expr_bind `{!typeGS Σ} E L f e Ks e' T :
  W.find_expr_fill e false = Some (Ks, e') →
  typed_val_expr E L f (W.to_expr e') (λ L' v m rt ty r,
    if Ks is [] then T L' v m rt ty r else
    introduce_with_hooks E L' (v ◁ᵥ{f.1, m} r @ ty) (λ L2,
      typed_val_expr E L2 f (W.to_expr (W.fill Ks (W.Val v))) T)) -∗
  typed_val_expr E L f (W.to_expr e) T.
Proof.
  move => /W.find_expr_fill_correct ->. move: Ks => [|K Ks] //.
  { auto. }
  move: (K::Ks) => {K}Ks. by iApply tac_typed_val_expr_bind'.
Qed.

Tactic Notation "typed_val_expr_bind" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (typed_val_expr ?E ?L ?f ?e ?T) =>
    let e' := W.of_expr e in change (typed_val_expr E L f e T) with (typed_val_expr E L f (W.to_expr e') T);
    iApply tac_typed_val_expr_bind; [done |];
    unfold W.to_expr; simpl
  | _ => fail "typed_val_expr_bind: not a 'typed_val_expr'"
  end.

Lemma tac_typed_stmt_bind `{!typeGS Σ} E L f s e Ks fn ϝ T :
  W.find_stmt_fill s = Some (Ks, e) →
  typed_val_expr E L f (W.to_expr e) (λ L' v m rt ty r,
    introduce_with_hooks E L' (v ◁ᵥ{f.1, m} r @ ty) (λ L2,
      typed_stmt E L2 f (W.to_stmt (W.stmt_fill Ks (W.Val v))) fn T ϝ)) -∗
  typed_stmt E L f (W.to_stmt s) fn T ϝ.
Proof.
  move => /W.find_stmt_fill_correct ->. iIntros "He".
  rewrite /typed_stmt.
  iIntros (?) "#CTX #HE HL Hf Hcont".
  rewrite stmt_wp_eq. iIntros (? rf ?) "Hret".
  have [Ks' HKs']:= W.stmt_fill_correct Ks f.1 rf. rewrite HKs'.
  iApply wp_bind.
  iApply (wp_wand _ _ _ _  with "[He HL Hf]").
  { rewrite /typed_val_expr.
    iApply wp_fupd.
    iSpecialize ("He" with "CTX HE HL Hf").
    rewrite expr_wp_unfold. iApply "He".
    iIntros (L' v m rt ty r) "HL Hf Hv Hcont".
    rewrite /introduce_with_hooks.
    iMod ("Hcont" with "[] HE HL Hv") as "(%L2 & HL & Hcont)"; first done.
    iApply ("Hcont" with "CTX HE HL Hf"). }
  iIntros (v) "HWP".
  rewrite -(HKs' (W.Val _)) /W.to_expr.
  iSpecialize ("HWP" with "Hcont").
  rewrite stmt_wp_eq/stmt_wp_def/=.
  iApply "HWP"; done.
Qed.

Tactic Notation "typed_stmt_bind" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (typed_stmt ?E ?L ?f ?s ?fn ?R ?ϝ) =>
    let s' := W.of_stmt s in change (typed_stmt E L f s fn R ϝ) with (typed_stmt E L f (W.to_stmt s') fn R ϝ);
    iApply tac_typed_stmt_bind; [done |];
    unfold W.to_expr, W.to_stmt; simpl; unfold W.to_expr; simpl
  | _ => fail "typed_stmt_bind: not a 'typed_stmt'"
  end.

Lemma intro_typed_stmt `{!typeGS Σ} rf R π f ϝ E L s Φ :
  rrust_ctx -∗
  elctx_interp E -∗
  llctx_interp L -∗
  current_frame π f -∗
  typed_stmt_post_cond (π, f) rf R Φ -∗
  typed_stmt E L (π, f) s rf R ϝ -∗
  WPs{π} s {{ f_code (rf), Φ }}.
Proof.
  iIntros "#CTX #HE HL Hf Hcont Hs".
  rewrite /typed_stmt.
  iApply ("Hs" with "CTX HE HL Hf Hcont").
Qed.

Ltac to_typed_stmt SPEC :=
  iStartProof;
  lazymatch goal with
  | FN : function |- envs_entails _ (WPs{?π} ?s {{ ?code, ?c }}) =>
    iApply (intro_typed_stmt FN with SPEC)
  end.
