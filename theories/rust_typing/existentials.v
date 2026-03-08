From refinedrust Require Export type ltypes programs.
From refinedrust Require Import uninit int ltype_rules.
From refinedrust Require Import options.

(** * Existential types and invariants *)
Section ex.
  Context `{!typeGS Σ}.
  (* [Y] is the abstract refinement type, [X] is the inner refinement type *)
  Context (X Y : RT)
    (* invariant on the contained refinement *)
    (P : ex_inv_def X Y)
  .

  (** Provide an abstraction over [ty], by accepting a refinement [Y] and existentially quantifying over [X].
     [P] is a predicate specifying an invariant, potentially containing additional ownership.
     [R] determines a relation between the inner and outer refinement. *)
  Program Definition ex_plain_t (ty : type X) : type Y := {|
    ty_xt_inhabited := _;
    ty_metadata_kind := ty.(ty_metadata_kind);
    ty_own_val π r m v :=
      (∃ x : X, P.(inv_P) π x r ∗ ty.(ty_own_val) π x m v)%I;
    ty_shr κ π r m l :=
      (∃ x : X, P.(inv_P_shr) π κ x r ∗ ty.(ty_shr) κ π x m l)%I;
    ty_syn_type := ty.(ty_syn_type);
    _ty_has_op_type ot mt := ty_has_op_type ty ot mt;
    ty_sidecond :=
      ty.(ty_sidecond);
    _ty_ghost_drop π r :=
      (* TODO generalize ghost_drop in the type def *)
      (∃ x, P.(inv_P) π x r ∗ ty_ghost_drop ty π x)%I;
    _ty_lfts := P.(inv_P_lfts) ++ ty_lfts ty;
    _ty_wf_E := P.(inv_P_wf_E) ++ ty_wf_E ty;
  |}.
  Next Obligation.
    intros. apply P.
  Defined.
  Next Obligation.
    iIntros (ty π r m v) "(%x & HP & Hv)".
    by iApply ty_has_layout.
  Qed.
  Next Obligation.
    iIntros (ty ot mt Hot). by eapply ty_op_type_stable.
  Qed.
  Next Obligation.
    iIntros (ty π r m v) "(%x & HP & Hv)". by iApply ty_own_val_sidecond.
  Qed.
  Next Obligation.
    iIntros (ty ? π r m v) "(%x & HP & Hs)". by iApply ty_shr_sidecond.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    iIntros (ty κ π l r m) "(%x & HP & Hv)". by iApply ty_shr_aligned.
  Qed.
  Next Obligation.
    iIntros (ty E κ l ly π r m q ?) "#(LFT & LLCTX) #Hna Htok %Halg %Hly Hlb Hb".
    iApply fupd_logical_step.
    setoid_rewrite bi.sep_exist_l. setoid_rewrite bi_exist_comm.
    iDestruct "Htok" as "(Htok & Htok2)".
    rewrite lft_intersect_list_app.
    rewrite -{1}lft_tok_sep -{1}lft_tok_sep. iDestruct "Htok" as "(Htok & HtokP & Htoki)".
    rewrite lft_intersect_assoc. rewrite -lft_tok_sep. iDestruct "Htok2" as "(Htok2 & Htoki2)".
    iMod (bor_exists_tok with "LFT Hb Htok") as "(%x & Hb & Htok)"; first solve_ndisj.
    iPoseProof (bor_iff _ _ (P.(inv_P) π x r ∗ (∃ a : val, l ↦ a ∗ a ◁ᵥ{ π, m} x @ ty)) with "[] Hb") as "Hb".
    { iNext. iModIntro. iSplit; [iIntros "(% & ? & ? & ?)" | iIntros "(? & (% & ? & ?))"]; eauto with iFrame. }
    iMod (bor_sep with "LFT Hb") as "(HP & Hb)"; first solve_ndisj.
    iPoseProof (P.(inv_P_share) E with "[$LFT $LLCTX] Hna Htok2 HP") as "HP"; first done.
    iCombine "Htok Htoki" as "Htok". rewrite lft_tok_sep.
    rewrite ty_lfts_unfold.
    iPoseProof (ty_share with "[$] Hna Htok [//] [//] Hlb Hb") as "Hb"; first solve_ndisj.
    iModIntro. iApply (logical_step_compose with "HP"). iApply (logical_step_wand with "Hb").
    iIntros "(Hshr & Htok) (HP & Htok2)".
    iSplitL "HP Hshr". { eauto with iFrame. }
    iCombine "Htok2 Htoki2" as "Htok2". rewrite lft_tok_sep -lft_intersect_assoc.
    iCombine "Htok HtokP" as "Htok". rewrite lft_tok_sep -lft_intersect_assoc.
    rewrite [lft_intersect_list (_ty_lfts _ ty) ⊓ lft_intersect_list P.(inv_P_lfts)]lft_intersect_comm.
    iCombine "Htok Htok2" as "$".
  Qed.
  Next Obligation.
    iIntros (ty κ κ' π r m l) "#Hincl (%x & HP & Hshr)".
    iExists x. iSplitL "HP".
    { by iApply P.(inv_P_shr_mono). }
    iApply (ty_shr_mono with "Hincl Hshr").
  Qed.
  Next Obligation.
    iIntros (ty π r m v F ?) "(%x & HP & Ha)".
    iPoseProof (ty_own_ghost_drop with "Ha") as "Ha"; first done.
    iApply (logical_step_compose with "Ha").
    iApply logical_step_intro.
    iIntros "Hdrop". eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (ty ot mt st π r m v Hot) "(%x & HP & Hv)".
    iPoseProof (ty_memcast_compat with "Hv") as "Hm"; first done.
    destruct mt; eauto with iFrame.
  Qed.
  Next Obligation.
    intros ty ly mt Heq Hst. simpl.
    rewrite ty_has_op_type_unfold.
    by apply _ty_has_op_type_untyped.
  Qed.
End ex.

(* Use a smarter solver for persistence here *)
Class ExInvPersistent {Σ} (P : iProp Σ) := ex_inv_pers_proof : Persistent P.
Global Hint Mode ExInvPersistent + + : typeclass_instances.

Ltac ex_t_solve_persistent := fail "implement ex_t_solve_persistent".
Global Hint Extern 10 (ExInvPersistent _) =>
  unfold ExInvPersistent; ex_t_solve_persistent : typeclass_instances.

Section copy.
  Context `{!typeGS Σ}.

  Global Instance ex_plain_t_pers_copy {X Y : RT} ty (P : ex_inv_def X Y)  :
    Copyable ty →
    (∀ π a b, (ExInvPersistent (P.(inv_P) π a b))) →
    (* Alternative: I could also require invariants to have a sharing accessor *)
    TCDone (∀ π κ a b, P.(inv_P) π a b = P.(inv_P_shr) π κ a b) →
    Copyable (ex_plain_t X Y P ty).
  Proof.
    intros Hcopy Hpers Heq. econstructor.
    { unfold ExInvPersistent in *. apply _. }
    iIntros (???? r m q ?).
    iIntros "CTX Hs Htok".
    iDestruct "Hs" as "(%x & Hshr & Hl)".
    unfold TCDone in Heq. rewrite -Heq.
    iMod (copy_shr_acc with "CTX Hl Htok") as "(%ly & >%Hst & >%Hly & %q' & %v & Ha & Hcl)"; first done.
    iExists ly. iR. iR. iFrame. done.
  Qed.
End copy.

Section contr.
  Context `{!typeGS Σ}.

  Global Instance ex_inv_def_contractive {rt X Y : RT}
    (P : type rt → ex_inv_def X Y)
    (F : type rt → type X) :
    ExInvDefContractive P →
    TypeContractive F →
    TypeContractive (λ ty, ex_plain_t X Y (P ty) (F ty)).
  Proof.
    intros HP HF.
    constructor; simpl.
    - apply HF.
    - apply HF.
    - destruct HP as [Hlft _ _].
      destruct HF as [_ _ Hlft' _ _ _ _].
      apply ty_lft_morphism_of_direct.
      apply ty_lft_morphism_to_direct in Hlft'.
      simpl in *.
      rewrite ty_wf_E_unfold.
      rewrite ty_lfts_unfold.
      apply direct_lft_morphism_app; done.
    - rewrite ty_has_op_type_unfold. eapply HF.
    - simpl. eapply HF.
    - intros n ty ty' ?.
      intros π r m v. rewrite /ty_own_val/=.
      do 3 f_equiv.
      { apply HP; done. }
      apply HF; done.
    - intros n ty ty' ?.
      intros ?????. rewrite /ty_shr/=.
      do 3 f_equiv.
      { apply HP. done. }
      apply HF; done.
    - intros n ty ty' ?.
      intros ??. rewrite ty_ghost_drop_unfold /_ty_ghost_drop/=.
      do 3 f_equiv.
      { apply HP; done. }
      apply HF; done.
  Qed.
  (* This should also work if only one of them is actually using the recursive argument. The other argument is trivially contractive, as it is constant. *)

  Global Instance ex_inv_def_ne {rt X Y : RT}
    (P : type rt → ex_inv_def X Y)
    (F : type rt → type X)
    :
    ExInvDefNonExpansive P →
    TypeNonExpansive F →
    TypeNonExpansive (λ ty, ex_plain_t X Y (P ty) (F ty)).
  Proof.
    intros HP HF.
    constructor; simpl.
    - apply HF.
    - apply HF.
    - destruct HP as [Hlft _ _].
      destruct HF as [_ _ Hlft' _ _ _ _].
      apply ty_lft_morphism_of_direct.
      apply ty_lft_morphism_to_direct in Hlft'.
      simpl in *.
      rewrite ty_wf_E_unfold.
      rewrite ty_lfts_unfold.
      apply direct_lft_morphism_app; done.
    - rewrite ty_has_op_type_unfold. intros.
      eapply HF; first done.
      rewrite ty_has_op_type_unfold. done.
    - simpl. eapply HF.
    - intros n ty ty' ?.
      intros π r m v. rewrite /ty_own_val/=.
      do 3 f_equiv.
      { apply HP; done. }
      apply HF; done.
    - intros n ty ty' ?.
      intros ?????. rewrite /ty_shr/=.
      do 3 f_equiv.
      { apply HP; done. }
      apply HF; done.
    - intros n ty ty' ?.
      intros ??. rewrite ty_ghost_drop_unfold /_ty_ghost_drop/=.
      do 3 f_equiv.
      { apply HP; done. }
      apply HF; done.
  Qed.
End contr.

Notation "'∃;' P ',' τ" := (ex_plain_t _ _ P τ) (at level 40) : stdpp_scope.

Section open.
  Context `{!typeGS Σ}.
  Context {rt X : RT} (P : ex_inv_def rt X).

  Global Program Instance learn_from_hyp_val_ex_plain_t ty r :
    LearnFromHypVal (∃; P, ty) r :=
    {| learn_from_hyp_val_Q := ∃ π, boringly (∃ x : rt, P.(inv_P) π x r) |}.
  Next Obligation.
    rewrite /ty_own_val/=.
    iIntros (? r ?? v m ?) "(%x & Hinv & Hv)".
    iPoseProof (boringly_intro with "Hinv") as "#Hinv'".
    iModIntro. iSplitL; first by eauto with iFrame.
    iExists π.
    iApply boringly_exists. eauto.
  Qed.

  Lemma ex_plain_t_destruct_owned F π (ty : type rt) l (x : X) :
    lftE ⊆ F →
    l ◁ₗ[π, Owned] #x @ (◁ (∃; P, ty)) ={F}=∗
    ∃ r : rt, P.(inv_P) π r x ∗
    l ◁ₗ[π, Owned] #r @ (◁ ty).
  Proof.
    iIntros (?) "Hb".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & %x' & Hrfn & Hb)".
    iMod (fupd_mask_mono with "Hb") as "(%v & Hl & Hv)"; first done.
    iDestruct "Hv" as "(%r & HP & Hv)".
    iDestruct "Hrfn" as "<-".
    iModIntro. iExists r. iFrame.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists ly. iFrame "#%".
    iExists r. iSplitR; first done. iModIntro. eauto with iFrame.
  Qed.

  (* We open this into a ShadowedLtype for [Shared].
     In terms of ownership, this doesn't do anything interesting, because we are working with persistent sharing predicates.
     However, we basically "overrride" the type at this place with [◁ ty], in order to not have to eliminate the existentials multiple times on subsequent accesses.
     This allows us to retain more information.

     This is not to be confused with "properly opening" the shared type, which we can only do for types with interior mutability.
  *)
  Lemma ex_plain_t_open_shared F π (ty : type rt) κ l (x : X) :
    lftE ⊆ F →
    l ◁ₗ[π, Shared κ] #x @ (◁ (∃; P, ty)) ={F}=∗
    ∃ r : rt, P.(inv_P_shr) π κ r x ∗
    l ◁ₗ[π, Shared κ] #x @ (ShadowedLtype (◁ ty) #r (◁ (∃; P, ty))).
  Proof.
    iIntros (?) "#Ha". iPoseProof "Ha" as "Hb".
    rewrite {2}ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & %Halg & %Hly & Hsc & Hlb & %r' & -> & #Hb)".
    iMod (fupd_mask_mono with "Hb") as "#Hb'"; first done. iClear "Hb".
    iDestruct "Hb'" as "(%r & HP & Hb)".
    iModIntro. iExists r. iFrame "#".
    rewrite ltype_own_shadowed_unfold /shadowed_ltype_own.
    simp_ltypes. iSplitL; last done.
    iApply ltype_own_ofty_unfold. rewrite /lty_of_ty_own.
    iExists ly. iSplitR; first done. do 3 iR.
    iExists r. iSplitR; first done. iModIntro. done.
  Qed.

  Lemma ex_plain_t_open_uniq F π (ty : type rt) l (x : X) q κ γ κs :
    lftE ⊆ F →
    rrust_ctx -∗
    q.[κ] -∗
    (q.[κ] ={lftE}=∗ llft_elt_toks κs) -∗
    l ◁ₗ[π, Uniq κ γ] #x @ (◁ (∃; P, ty)) ={F}=∗
    ∃ r : rt, P.(inv_P) π r x ∗
    l ◁ₗ[π, Owned] #r @ (◁ ty) ∗
    (∀ rt' (lt' : ltype rt') (r' : place_rfn rt'),
      l ◁ₗ[π, Owned] r' @ lt' -∗
      ⌜ltype_st lt' = ty_syn_type ty MetaNone⌝ -∗
      l ◁ₗ[π, Uniq κ γ] r' @
      (OpenedLtype (lt') (◁ ty) (◁ ∃; P, ty)
        (λ (r : rt) (x : X), P.(inv_P) π r x)
        (λ r x, llft_elt_toks κs)))%I.
  Proof.
    (* TODO duplicated a lot with opened_ltype_create_uniq_simple, mostly due to the different invariant.
        Can we generalize? *)
    iIntros (?) "#(LFT & LLCTX) Htok Hcl_tok Hb".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & (Hcred & Hat) & Hrfn & Hb)".
    iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
    iDestruct "Hcred" as "(Hcred1 & Hcred)".
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod (pinned_bor_acc_strong lftE with "LFT Hb Htok") as "(%κ' & #Hincl & Hb & ? & Hcl_b)"; first done.
    iMod "Hcl_F" as "_".
    iApply (lc_fupd_add_later with "Hcred1"). iNext.
    iDestruct "Hb" as "(%r' & Hauth & Hb)".
    iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
    iPoseProof (gvar_agree with "Hauth Hrfn") as "#->".
    iDestruct "Hb" as "(%v & Hl & %r & HP & Hv)".
    iModIntro. iExists r. iFrame.
    iSplitL "Hl Hv".
    { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly. iFrame "#%".
      iExists r. iSplitR; first done. iModIntro. eauto with iFrame. }
    iIntros (rt' lt' r') "Hb %Hst".
    rewrite ltype_own_opened_unfold /opened_ltype_own.
    iExists ly. rewrite Hst. iSplitR; first done. iSplitR; first done.
    iSplitR; first done. iSplitR; first done. iSplitR; first done.
    iFrame. clear -Hly Halg.
    iApply (logical_step_intro_tr with "Hat").
    iIntros "Hat Hcred'". iModIntro.
    iIntros (own_lt_cur' κs' r0 r') "HP #Hincl' Hown #Hub".
    rewrite ltype_own_core_equiv. simp_ltypes.
    (* update *)
    iMod (gvar_update r' with "Hauth Hrfn") as "(Hauth & $)".

    iAssert (□ ([† κ] ={lftE}=∗ lft_dead_list κs'))%I as "#Hkill".
    { iModIntro. iIntros "#Hdead".
      iApply big_sepL_fupd. iApply big_sepL_intro. iIntros "!>" (?? Hlook).
      iPoseProof (big_sepL_lookup with "Hincl'") as "Ha"; first done.
      iApply (lft_incl_dead with "[] Hdead"); first done.
      done. }
      (*iApply lft_incl_trans; done. }*)

    (* close the borrow *)
    iDestruct "Hcred" as "(Hcred1 & Hcred)".
    set (V := (gvar_auth γ r' ∗ (lft_dead_list κs' ={lftE}=∗ P.(inv_P) π r0 r') ∗ own_lt_cur' π r0 l)%I).
    iMod ("Hcl_b" $! V with "[] Hcred1 [HP Hown Hauth ]") as "(Hb & Htok)".
    { iNext. iIntros "(Hauth & HP & Hb) Hdead".
      iModIntro. iNext. iExists r'. iFrame.
      iMod (lft_incl_dead _ κ with "[] Hdead") as "#Hdead"; [done.. | ].
      iMod ("Hkill" with "Hdead") as "#Hdead'".
      iMod ("HP" with "Hdead'") as "HP".
      iMod ("Hub" with "Hdead' Hb") as "Hown".
      rewrite {2}ltype_own_ofty_unfold /lty_of_ty_own.
      iDestruct "Hown" as "(% &_ & _ & _ & _ &  %r1 & -> & >(%v1 & Hl & Hv))".
      iModIntro. iFrame. }
    { iNext. rewrite /V. iFrame. }
    iMod ("Hcl_tok" with "Htok") as "$".

    (* show that we can shift it back *)
    iModIntro. iIntros "#Hdead Hobs". iModIntro.
    rewrite ltype_own_core_equiv. simp_ltypes.
    rewrite (ltype_own_ofty_unfold _ (Uniq _ _)) /lty_of_ty_own.
    iExists ly. iSplitR; first done. iSplitR; first done. iSplitR; first done.
    iSplitR; first done. iFrame.
    iSplitL "Hat".
    { iApply tr_weaken; last done.
      simpl. unfold num_laters_per_step. lia. }
    iModIntro.
    iApply (pinned_bor_shorten with "Hincl").
    iApply (pinned_bor_impl with "[] Hb").
    iNext. iModIntro. iSplit; first last. { eauto. }
    iIntros "(Hauth & HP & Hcur)".
    iExists r'. iFrame. iMod ("Hub" with "Hdead Hcur") as "Hb".
    iClear "Hub". rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(% & _ & _ & _ & _ &  Hb)".
    iDestruct "Hb" as "(%r1 & -> & >(%v1 & Hl & Hv1))".
    iMod ("HP" with "Hdead") as "HP".
    iModIntro. iFrame.
  Qed.
End open.

Section subtype.
  Context `{!typeGS Σ}.
  Context {rt X : RT}.

  (*Plan:
     - let's have a definition stating inclusion.
     - let's design subtyping instances to just require an instance for the ex_inv_def subtyping.

     These instances should in turn be able to spawn subtyping conditions on other things, of course.

     Steps:
     1. create class
     2. create
  *)

  (* Low priority default instance *)
  Lemma subtype_adt_default E L (P1 P2 : ex_inv_def rt X) T :
    ⌜fast_eq_hint (P1 = P2)⌝ ∗ T ⊢ subtype_adt E L P1 P2 T.
  Proof.
    iIntros "(-> & $)".
    iPureIntro. iApply ex_inv_def_sub_refl.
  Qed.
  Definition subtype_adt_default_inst := [instance @subtype_adt_default].
  Global Existing Instance subtype_adt_default_inst | 1000.

  Lemma full_subtype_ex_plain_t E L (P1 P2 : ex_inv_def rt X) (ty1 ty2 : type rt) :
    full_subtype E L ty1 ty2 →
    ex_inv_def_sub E L P1 P2 →
    full_subtype E L (∃; P1, ty1) (∃; P2, ty2).
  Proof.
    intros Hsub1 Hsub2 ?.
    iIntros (?) "HL HE". unfold type_incl.
    iPoseProof (full_subtype_acc_noend with "HE HL") as "#Hincl"; first apply Hsub1.
    iPoseProof ("Hincl" $! inhabitant) as "(%Hm & #Hsc & #_)".
    iPoseProof (Hsub2 with "HL HE") as "(#HinclP & #HinclPshr)".
    iSplitR. { done. }
    iSplitR. { done. }
    iSplit; iModIntro.
    - iEval (rewrite /ty_own_val/=).
      iIntros (???) "(%x & Hinv & Hv1)".
      iExists x. iSplitL "Hinv".
      + by iApply "HinclP".
      + iDestruct ("Hincl" $! x) as "(_ & _  & Hv & _)". by iApply "Hv".
    - iEval (rewrite /ty_own_val/=).
      iIntros (????) "(%x & Hinv & Hv1)".
      iExists x. iSplitL "Hinv".
      + by iApply "HinclPshr".
      + iDestruct ("Hincl" $! x) as "(_ & _  & _ & Hshr)". by iApply "Hshr".
  Qed.

  Lemma mut_subtype_ex_plain_t E L (P1 P2 : ex_inv_def rt X) (ty1 ty2 : type rt) T :
    mut_subtype E L ty1 ty2 (subtype_adt E L P1 P2 T)
    ⊢ mut_subtype E L (∃; P1, ty1) (∃; P2, ty2) T.
  Proof.
    iIntros "(%Hsub1 & %Hsub2 & $)".
    iPureIntro. by apply full_subtype_ex_plain_t.
  Qed.
  Definition mut_subtype_ex_plain_t_inst := [instance @mut_subtype_ex_plain_t].
  Global Existing Instance mut_subtype_ex_plain_t_inst.

  Lemma mut_eqtype_ex_plain_t E L (P1 P2 : ex_inv_def rt X) (ty1 ty2 : type rt) T :
    mut_eqtype E L ty1 ty2 (subtype_adt E L P1 P2 (subtype_adt E L P2 P1 T))
    ⊢ mut_eqtype E L (∃; P1, ty1) (∃; P2, ty2) T.
  Proof.
    iIntros "(%Heq1 & %Hsub1 & %Hsub2 & $)".
    iPureIntro.
    apply full_subtype_eqtype.
    - apply full_subtype_ex_plain_t; last done.
      by apply full_eqtype_subtype_l.
    - apply full_subtype_ex_plain_t; last done.
      by apply full_eqtype_subtype_r.
  Qed.
  Definition mut_eqtype_ex_plain_t_inst := [instance @mut_eqtype_ex_plain_t].
  Global Existing Instance mut_eqtype_ex_plain_t_inst.
End subtype.

Section resolve.
  Context `{!typeGS Σ}.

  (* Generic lemmas *)
  Lemma resolve_ghost_ofty_adt_owned {rt} (ty : type rt) π E L l r rm T :
    resolve_ghost_adt π E L rm r ty (λ L2 r' R changed, T L2 (# r') R changed)
    ⊢ resolve_ghost π E L rm true l (◁ ty) (Owned ) (# r) T.
  Proof.
    iIntros "Ha" (???) "#CTX #HE HL Hl".

    rewrite ltype_own_ofty_unfold.
    iDestruct "Hl" as "(%ly & %Hst & % & ? & ? & %r'' & <- & Hb)".
    iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
    iDestruct "Hb" as "(%v & Hl & Hv)".
    iMod ("Ha" with "[] [] CTX HE HL Hv") as "(%L2 & %r2 & % & % & Hstep & HL & HT)"; [done.. | ].
    simpl. iFrame.
    iApply (logical_step_wand with "Hstep").
    iModIntro. iIntros "(Hv & $)".
    iEval (rewrite ltype_own_ofty_unfold). iExists _.
    iFrame. iR. iR. iR. done.
  Qed.

  Lemma resolve_ghost_ofty_adt_uniq {rt} (ty : type rt) π E L l r rm κ γ T :
    (li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L2),
      resolve_ghost_adt π E L2 rm r ty (λ L3 r' R changed, T L3 (# r') (llft_elt_toks κs ∗ R) changed)))
    ⊢ resolve_ghost π E L rm true l (◁ ty) (Uniq κ γ) (# r) T.
  Proof.
    iIntros "Ha" (???) "#CTX #HE HL Hl".
    rewrite /lctx_lft_alive_count_goal.
    iDestruct "Ha" as "(%κs & %L2 & %Hal & Ha)".
    iMod (Hal with "HE HL") as "(Htoks & Hcl & HL)"; first done.
    iMod ("Hcl" with "Htoks") as "(%q & Htok & Hcl)".

    rewrite ltype_own_ofty_unfold.
    iDestruct "Hl" as "(%ly & %Hst & % & ? & ? & Hcreds & Hrfn & Hb)".
    iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
    iDestruct "CTX" as "(LFT & LCTX)".
    iMod (pinned_bor_acc with "LFT Hb Htok") as "(Hb & Hb_cl)"; first done.
    iDestruct "Hb" as "(%v & Hl & Hb)".
    iDestruct "Hcreds" as "((Hc1 & Hc) & Ht)".
    iApply (lc_fupd_add_later with "Hc1"). iNext.
    iMod (fupd_mask_mono with "Hb") as "(%v' & Hl' & Hv)"; first done.
    iPoseProof (gvar_agree with "Hl Hrfn") as "->".
    iMod ("Ha" with "[] [] [] HE HL Hv") as "(%L3 & %r2 & % & % & Hstep & HL & HT)"; [done.. | | ].
    { iR. done. }
    simpl. iFrame.
    iApply logical_step_fupd.
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_intro_tr with "Ht").
    iModIntro. iIntros "Ht Hcreds' !> (Hv & $)".
    iDestruct "Hc" as "(Hc1 & Hc)".
    iMod (gvar_update r2 with "Hl Hrfn") as "(Hl & Hrfn)".
    iMod ("Hb_cl" with "[Hv Hl' Hl] Hc1") as "(Hb & Htok)".
    { by iFrame. }
    iMod ("Hcl" with "Htok") as "$".
    iEval (rewrite ltype_own_ofty_unfold). iExists _.
    iFrame. iR. iR. iL.
    iDestruct "Ht" as "(_ & $)".
    done.
  Qed.
End resolve.

Section resolve.
  Context `{!typeGS Σ}.
  Context {rt X : RT} (P : ex_inv_def rt X).

  Lemma resolve_ghost_ofty_adt_ex_owned ty π E L l r rm T :
    resolve_ghost_adt π E L rm r (∃; P, ty) (λ L2 r' R changed, T L2 (# r') R changed)
    ⊢ resolve_ghost π E L rm true l (◁ ∃; P, ty) (Owned) (# r) T.
  Proof. apply resolve_ghost_ofty_adt_owned. Qed.
  Definition resolve_ghost_ofty_adt_ex_owned_inst := [instance @resolve_ghost_ofty_adt_ex_owned].
  Global Existing Instance resolve_ghost_ofty_adt_ex_owned_inst | 8.

  Lemma resolve_ghost_ofty_adt_ex_uniq ty π E L l r rm κ γ T :
    (li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L2),
      resolve_ghost_adt π E L2 rm r (∃; P, ty) (λ L3 r' R changed, T L3 (# r') (llft_elt_toks κs ∗ R) changed)))
    ⊢ resolve_ghost π E L rm true l (◁ ∃; P, ty) (Uniq κ γ) (# r) T.
  Proof. apply resolve_ghost_ofty_adt_uniq. Qed.
  Definition resolve_ghost_ofty_adt_ex_uniq_inst := [instance @resolve_ghost_ofty_adt_ex_uniq].
  Global Existing Instance resolve_ghost_ofty_adt_ex_uniq_inst.

  (** Low priority default instance, in case there are no user-defined instances for this ADT *)
  Lemma resolve_ghost_adt_ex_default ty π E L r rm T :
    T L r True false ⊢ resolve_ghost_adt π E L rm r (∃; P, ty) T.
  Proof.
    iIntros "HT". iIntros (????) "CTX HE HL Hv".
    iFrame. iApply logical_step_intro. by iFrame.
  Qed.
  Definition resolve_ghost_adt_ex_default_inst := [instance @resolve_ghost_adt_ex_default].
  Global Existing Instance resolve_ghost_adt_ex_default_inst | 1000.
End resolve.

Section stratify.
  Context `{!typeGS Σ}.
  Context {rt X : RT} (P : ex_inv_def rt X).

  (** Subsumption rule for introducing an existential *)
  (* TODO could have a more specific instance for persistent invariants with pers = true *)
  Lemma owned_subtype_ex_plain_t π E L (ty : type rt) (r : rt) (r' : X) T :
    (prove_with_subtype E L false ProveDirect (P.(inv_P) π r r') (λ L1 _ R, R -∗ T L1))
    ⊢ owned_subtype π E L false r r' ty (∃; P, ty) T.
  Proof.
    iIntros "HT".
    iIntros (????) "#CTX #HE HL".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L2 & % & %R2 & >(Hinv & HR2) & HL & HT)".
    iExists L2. iFrame. iPoseProof ("HT" with "HR2") as "$". iModIntro.
    iSplitR; last iSplitR.
    - simpl. iPureIntro.
      apply syn_type_size_eq_refl.
    - simpl. eauto.
    - iIntros (v) "Hv0".
      iEval (rewrite /ty_own_val/=).
      eauto with iFrame.
  Qed.
  Global Instance owned_subtype_ex_plain_t_inst π E L (ty : type rt) (r : rt) (r' : X) :
    OwnedSubtype π E L false r r' ty (∃; P, ty) :=
    λ T, i2p (owned_subtype_ex_plain_t π E L ty r r' T).

  Definition owned_subtype_ex_plain_t_refl π E L (ty : type rt) r1 r2 := owned_subtype_id π E L false r1 r2 (∃; P, ty).
  Definition owned_subtype_ex_plain_t_refl_inst := [instance @owned_subtype_ex_plain_t_refl].
  Global Existing Instance owned_subtype_ex_plain_t_refl_inst | 19.

  (* Lower priority instance for subtyping from any type *)
  Lemma owned_subtype_ex_plain_t_strong {rt0 : RT} π E L (ty : type rt0) (ty2 : type rt) (r : rt0) (r' : X) T :
    (∃ r1, owned_subtype π E L false r r1 ty ty2 (λ L2,
    (prove_with_subtype E L2 false ProveDirect (P.(inv_P) π r1 r') (λ L1 _ R,
    R -∗ T L1))))
    ⊢ owned_subtype π E L false r r' ty (∃; P, ty2) T.
  Proof.
    iIntros "HT".
    unfold owned_subtype, prove_with_subtype.
    iIntros (????) "#CTX #HE HL".
    iDestruct "HT" as "(%r1 & HT)".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L0 & Hincl & HL & HT)".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L2 & % & %R2 & >(Hinv & HR2) & HL & HT)".
    iExists L2. iFrame. iPoseProof ("HT" with "HR2") as "$". iModIntro.
    iDestruct "Hincl" as "(%Hst_eq & Hsc & Hv)".
    iSplitR; last iSplitL "Hsc".
    - simpl. iPureIntro. done.
    - simpl. eauto.
    - iIntros (v) "Hv0".
      iEval (rewrite /ty_own_val/=).
      iPoseProof ("Hv" with "Hv0") as "Hv".
      eauto with iFrame.
  Qed.
  Definition owned_subtype_ex_plain_t_strong_inst := [instance @owned_subtype_ex_plain_t_strong].
  Global Existing Instance owned_subtype_ex_plain_t_strong_inst | 20.

  (*
  Lemma owned_subtype_unfold_ex_plain_t π E L (ty : type rt) (r : rt) (r' : X) T :
    (∀ r2 : rt, introduce_with_hooks E L (P.(inv_P) π r2 r') (λ L1,
      owned_subtype π E L1 false r2 r ty ty T)) -∗
    owned_subtype π E L false r' r (∃; P, ty) ty T.
  Proof.
    iIntros "HT".
    iIntros (???) "#CTX #HE HL".

    iMod ("HT" with "[//] [//] CTX HE HL") as "(%L2 & % & %R2 & >(Hinv & HR2) & HL & HT)".
    iExists L2. iFrame. iPoseProof ("HT" with "HR2") as "$". iModIntro.
    iSplitR; last iSplitR.
    - simpl. iPureIntro.
      intros ly1 ly2 Hly1 HLy2. f_equiv. by eapply syn_type_has_layout_inj.
    - simpl. eauto.
    - iIntros (v) "Hv0".
      iEval (rewrite /ty_own_val/=).
      eauto with iFrame.
  Qed.
  Global Instance owned_subtype_ex_plain_t_inst π E L (ty : type rt) (r : rt) (r' : X) :
    OwnedSubtype π E L false r r' ty (∃; P, ty) :=
    λ T, i2p (owned_subtype_ex_plain_t π E L ty r r' T).
   *)



  (** Stratification rules *)

  (* Unfolding by stratification *)
  Lemma stratify_unfold_ex_plain_t_owned {M} π E L smu sa (sm : M) l (ty : type rt) x T :
    (∀ r, P.(inv_P) π r x -∗ stratify_ltype π E L smu StratDoUnfold sa sm l (◁ ty) (#r) (Owned) (λ L2 P _ lt' r',
      (* This should always be satisfiable *)
      T L2 P _ lt' r'))
    ⊢ stratify_ltype π E L smu StratDoUnfold sa sm l (◁ (∃; P, ty)) (#x) (Owned) T.
  Proof.
    iIntros "HT". iIntros (F ???) "#CTX #HE HL Hb".
    iMod (ex_plain_t_destruct_owned with "Hb") as "(%r & HP & Hb )"; first done.
    iMod ("HT" with "HP [//] [//] [//] CTX HE HL Hb") as "Ha".
    iDestruct "Ha" as "(%L2 & %R' & %rt' & %lt' & %r' & HL & %Hst & Hstep & HT)".
    iExists _, _, _, _, _. iFrame.
    iModIntro.
    iPureIntro. simp_ltypes. rewrite -Hst. done.
  Qed.
  (*Global Instance stratify_unfold_ex_plain_t_owned_inst {M} π E L smu sa (sm : M) l (ty : type rt) x wl :*)
  (*StratifyLtype π E L smu StratDoUnfold sa sm l (◁ (∃; P, ty))%I (PlaceIn x) (Owned wl) :=*)
    (*λ T, i2p (stratify_unfold_ex_plain_t_owned π E L smu sa sm l ty x wl T).*)

  Lemma stratify_unfold_ex_plain_t_uniq {M} π E L smu sa (sm : M) l (ty : type rt) x κ γ T :
    li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L'),
    (∀ r, P.(inv_P) π r x -∗ stratify_ltype π E L' smu StratDoUnfold sa sm l (◁ ty) (PlaceIn r) (Owned)
      (λ L2 R' rt' lt' r',
        T L2 R' _ (OpenedLtype lt' (◁ ty) (◁ (∃; P, ty)) (λ (r : rt) (x : X), P.(inv_P) π r x) (λ r x, llft_elt_toks κs)) r')))
    ⊢ stratify_ltype π E L smu StratDoUnfold sa sm l (◁ (∃; P, ty)) (PlaceIn x) (Uniq κ γ) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal. iIntros "(%κs & %L' & %Hal & HT)".
    iIntros (F ???) "#CTX #HE HL Hb".
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as "(%q & Htok & Hcl_tok & HL)"; [done.. | ].
    iMod "Hcl_F" as "_".
    iMod (ex_plain_t_open_uniq with "CTX Htok Hcl_tok Hb") as "(%r & HP & Hb & Hcl)"; first done.
    iMod ("HT" with "HP [//] [//] [//] CTX HE HL Hb") as "Ha".
    iDestruct "Ha" as "(%L2 & %R' & %rt' & %lt' & %r' & HL & %Hst & Hstep & HT)".
    iExists _, _, _, _, _. iFrame.
    iSplitR. { iPureIntro. simp_ltypes. done. }
    iModIntro.
    iApply (logical_step_compose with "Hstep").
    iApply logical_step_intro. iIntros "(Hb & $)".
    iApply ("Hcl" with "Hb []").
    done.
  Qed.
  (*Global Instance stratify_unfold_ex_plain_t_uniq_inst {M} π E L smu sa (sm : M) l (ty : type rt) x κ γ :*)
    (*StratifyLtype π E L smu StratDoUnfold sa sm l (◁ (∃; P, ty))%I (PlaceIn x) (Uniq κ γ) :=*)
    (*λ T, i2p (stratify_unfold_ex_plain_t_uniq π E L smu sa sm l ty x κ γ T).*)


  Lemma stratify_unfold_ex_plain_t_shared {M} π E L smu sa (sm : M) l (ty : type rt) x κ T :
    (∀ r, P.(inv_P_shr) π κ r x -∗ stratify_ltype π E L smu StratDoUnfold sa sm l (◁ ty) (PlaceIn r) (Shared κ)
      (λ L2 R' rt' lt' r',
        ∃ r'', ⌜r' = PlaceIn r''⌝ ∗ T L2 R' _ (ShadowedLtype lt' #r'' (◁ (∃; P, ty))) (PlaceIn x)))
    ⊢ stratify_ltype π E L smu StratDoUnfold sa sm l (◁ (∃; P, ty)) (PlaceIn x) (Shared κ) T.
  Proof.
    iIntros "HT" (F ???) "#CTX #HE HL Hb".
    iMod (ex_plain_t_open_shared with "Hb") as "(%r & HP & Hb)"; first done.
    iPoseProof (shadowed_ltype_acc_cur with "Hb") as "(Hb & Hcl_b)".
    iMod ("HT" with "HP [//] [//] [//] CTX HE HL Hb") as (L2 R' rt' lt' r') "(HL & Hst & Hstep & HT)".
    iDestruct "HT" as "(%r'' & -> & HT)".
    iModIntro. iExists  _, _, _, _, _. iFrame.
    simp_ltypes. iSplitR; first done.
    iApply (logical_step_wand with "Hstep"). iIntros "(Ha & $)".
    iApply ("Hcl_b" with "Hst Ha").
  Qed.
  (*Global Instance stratify_unfold_ex_plain_t_shared_inst {M} π E L smu sa (sm : M) l (ty : type rt) x κ :*)
    (*StratifyLtype π E L smu StratDoUnfold sa sm l (◁ (∃; P, ty))%I (PlaceIn x) (Shared κ) :=*)
    (*λ T, i2p (stratify_unfold_ex_plain_t_shared π E L smu sa sm l ty x κ T).*)

  (** Unfolding by place access *)
  Lemma typed_place_ex_plain_t_owned E L f l (ty : type rt) x K `{!TCDone (K ≠ [])} T :
    (∀ r,
      introduce_with_hooks E L (P.(inv_P) f.1 r x) (λ L2, typed_place E L2 f l (◁ ty) (#r) UpdStrong (Owned) K
      (λ L2 κs li b2 bmin' rti ltyi ri updcx,
        T L2 κs li b2 bmin' rti ltyi ri
          (λ L3 upd cont, updcx L3 upd (λ upd',
            cont (@mkPUpd _ _ _ UpdStrong _
              upd'.(pupd_lt) upd'.(pupd_rfn) upd'.(pupd_R) UpdStrong
              I I))))))
    ⊢ typed_place E L f l (◁ (∃; P, ty))%I (#x) UpdStrong (Owned) K T.
  Proof.
    iIntros "HT". iIntros (F ???) "#CTX #HE HL Hf Hb Hcont".
    iApply fupd_place_to_wp.
    iMod (ex_plain_t_destruct_owned with "Hb") as "(%r & HP & Hb)"; first done.
    (*iPoseProof ("Hcl" with "Hb []") as "Hb"; first done.*)
    iMod ("HT" with "[] CTX HE HL HP") as "(%L2 & HL & HT)"; first done.
    iApply ("HT" with "[//] [//] CTX HE HL Hf Hb").
    iModIntro. iIntros (L' κs l2 b2 bmin0 rti ltyi ri updcx) "Hl Hc".
    iApply ("Hcont" with "Hl").
    iIntros (upd) "#Hincl Hl2 %Hsteq ? ?".
    iMod ("Hc" with "Hincl Hl2 [//] [$] [$]") as "Hc".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hc" with "HL Hf Hcont") as (upd') "(Hl & %Hsteq' & Hcond & ? & ? & ? & ? & ?)".
    iFrame. simp_ltypes. done.
  Qed.
  Definition typed_place_ex_plain_t_owned_inst := [instance @typed_place_ex_plain_t_owned].
  Global Existing Instance typed_place_ex_plain_t_owned_inst | 15.

  Lemma typed_place_ex_plain_t_uniq E L f l (ty : type rt) x κ γ K `{!TCDone (K ≠ [])} T :
    li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L2),
    (∀ r, introduce_with_hooks E L2 (P.(inv_P) f.1 r x) (λ L3, typed_place E L3 f l
      (OpenedLtype (◁ ty) (◁ ty) (◁ (∃; P, ty)) (λ (r : rt) (x : X), P.(inv_P) f.1 r x) (λ r x, llft_elt_toks κs)) (#r) UpdStrong (Uniq κ γ) K
      (λ L4 κs li b2 bmin' rti ltyi ri updcx,
        T L4 κs li b2 bmin' rti ltyi ri
          (λ L3 upd cont, updcx L3 upd (λ upd',
            cont (@mkPUpd _ _ _ UpdStrong _
              upd'.(pupd_lt) upd'.(pupd_rfn) upd'.(pupd_R) UpdStrong
              I I)))
        ))))
    ⊢ typed_place E L f l (◁ (∃; P, ty))%I (#x) UpdStrong (Uniq κ γ) K T.
  Proof.
    iIntros "HT". iIntros (F ???) "#CTX #HE HL Hf Hb Hcont".
    rewrite /lctx_lft_alive_count_goal.
    iDestruct "HT" as "(%κs & %L' & %Hal & HT)".
    iApply fupd_place_to_wp.
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as "(%q & Htok & Hcl_tok & HL)"; [done.. | ].
    iMod "Hcl_F" as "_".
    iMod (ex_plain_t_open_uniq with "CTX Htok Hcl_tok Hb") as "(%r & HP & Hb & Hcl)"; first done.
    iPoseProof ("Hcl" with "Hb []") as "Hb"; first done.
    iMod ("HT" with "[] CTX HE HL HP") as "(%L2 & HL & HT)"; first done.
    iApply ("HT" with "[//] [//] CTX HE HL Hf Hb").
    iModIntro. iIntros (L'' κs' l2 b2 bmin0 rti ltyi ri updcx) "Hl Hc".
    iApply ("Hcont" with "Hl").
    iIntros (upd) "#Hincl Hl2 %Hsteq ? ?".
    iMod ("Hc" with "Hincl Hl2 [//] [$] [$]") as "Hc".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hc" with "HL Hf Hcont") as (upd') "(Hl & %Hsteq' & Hcond & ? & ? & ? & ? & ?)".
    iFrame. simp_ltypes. done.
  Qed.
  Definition typed_place_ex_plain_t_uniq_inst := [instance @typed_place_ex_plain_t_uniq].
  Global Existing Instance typed_place_ex_plain_t_uniq_inst | 15.

  Lemma typed_place_ex_plain_t_shared E L f l (ty : type rt) x κ K `{!TCDone (K ≠ [])} T :
    (∀ r, introduce_with_hooks E L (P.(inv_P_shr) f.1 κ r x) (λ L2,
      typed_place E L2 f l (ShadowedLtype (◁ ty) #r (◁ (∃; P, ty))) (#x) UpdStrong (Shared κ) K
        (λ L3 κs li b2 bmin' rti ltyi ri updcx,
          T L3 κs li b2 bmin' rti ltyi ri
            (λ L3 upd cont, updcx L3 upd (λ upd',
            cont (@mkPUpd _ _ _ UpdStrong _
              upd'.(pupd_lt) upd'.(pupd_rfn) upd'.(pupd_R) UpdStrong
              I I)))
          )))
    ⊢ typed_place E L f l (◁ (∃; P, ty))%I (#x) UpdStrong (Shared κ) K T.
  Proof.
    iIntros "HT". iIntros (F ???) "#CTX #HE HL Hf Hb Hcont".
    iApply fupd_place_to_wp.
    iMod (ex_plain_t_open_shared with "Hb") as "(%r & HP & Hb)"; first done.
    iMod ("HT" with "[] CTX HE HL HP") as "(%L2 & HL & HT)"; first done.
    iApply ("HT" with "[//] [//] CTX HE HL Hf Hb").
    iModIntro. iIntros (L'' κs' l2 b2 bmin0 rti ltyi ri updcx) "Hl Hc".
    iApply ("Hcont" with "Hl").
    iIntros (upd) "#Hincl Hl2 %Hsteq ? ?".
    iMod ("Hc" with "Hincl Hl2 [//] [$] [$]") as "Hc".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hc" with "HL Hf Hcont") as (upd') "(Hl & %Hsteq' & Hcond & ? & ? & ? & ? & ?)".
    iFrame. simp_ltypes. done.
  Qed.
  Definition typed_place_ex_plain_t_shared_inst := [instance @typed_place_ex_plain_t_shared].
  Global Existing Instance typed_place_ex_plain_t_shared_inst | 15.

End stratify.
