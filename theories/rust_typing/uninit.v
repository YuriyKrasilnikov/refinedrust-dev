From refinedrust Require Export type uninit_def.
From refinedrust Require Import programs ltype_rules value.
From refinedrust Require Import options.

(** * Typing rules for the uninit type *)

Section lemmas.
  Context `{!typeGS Σ}.
  Implicit Types (rt : RT).

  (* TODO move *)
  Lemma ofty_owned_subtype_aligned π {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) r1 r2 ly2 l  :
    (* location needs to be suitably aligned for ty2 *)
    syn_type_has_layout (ty_syn_type ty2 MetaNone) ly2 →
    l `has_layout_loc` ly2 →
    owned_type_incl π r1 r2 ty1 ty2
    ⊢ (l ◁ₗ[π, Owned] #r1 @ ◁ ty1) -∗ (l ◁ₗ[π, Owned] #r2 @ ◁ ty2).
  Proof.
    iIntros (Hst2 Hly2) "Hincl Hl".
    rewrite !ltype_own_ofty_unfold/lty_of_ty_own.
    iDestruct "Hl" as "(%ly' & %Halg' & %Hlyl & Hsc1 & Hlb & % & -> & Hl)".
    iExists ly2. iR. iR.
    iDestruct "Hincl" as "(%Hszeq & Hsc & Hvi)".
    assert (ly_size ly' = ly_size ly2) as Hszeq'. {
      by eapply syn_type_size_eq_use. }
    iSplitL "Hsc Hsc1". { by iApply "Hsc". }
    rewrite -Hszeq'. iFrame.
    iExists _. iR. iMod "Hl" as "(%v & Hl & Hv)".
    iModIntro. iExists _. iFrame.
    by iApply "Hvi".
  Qed.
  Lemma ofty_owned_subtype_aligned' π {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) r1 r2 ly2 l  :
    (* location needs to be suitably aligned for ty2 *)
    syn_type_has_layout (ty_syn_type ty2 MetaNone) ly2 →
    l `has_layout_loc` ly2 →
    (∀ r1, owned_type_incl π r1 r2 ty1 ty2)
    ⊢ (l ◁ₗ[π, Owned] r1 @ ◁ ty1) -∗ (l ◁ₗ[π, Owned] #r2 @ ◁ ty2).
  Proof.
    iIntros (Hst2 Hly2) "Hincl Hl".
    rewrite !ltype_own_ofty_unfold/lty_of_ty_own.
    iDestruct "Hl" as "(%ly' & %Halg' & %Hlyl & Hsc1 & Hlb & % & Hrfn & Hl)".
    iExists ly2. iR. iR.
    iDestruct ("Hincl" $! r') as "(%Hszeq & Hsc & Hvi)".
    assert (ly_size ly' = ly_size ly2) as Hszeq'. { by eapply syn_type_size_eq_use; done. }
    iSplitL "Hsc Hsc1". { by iApply "Hsc". }
    rewrite -Hszeq'. iFrame.
    iExists r2. iR. iMod "Hl" as "(%v & Hl & Hv)".
    iModIntro. iExists _. iFrame.
    by iApply "Hvi".
  Qed.

  Lemma owned_type_incl_uninit' π {rt1 : RT} (r1 : rt1) r2 (ty1 : type rt1) st ly :
    syn_type_size_eq (ty_syn_type ty1 MetaNone) st →
    syn_type_has_layout st ly →
    ⊢ owned_type_incl π r1 r2 ty1 (uninit st).
  Proof.
    iIntros (Hst ?). iSplitR; last iSplitR.
    - iPureIntro. intros. simpl. done.
    - simpl. eauto.
    - iIntros (v) "Hv".
      rewrite uninit_own_spec.
      iEval (rewrite /ty_own_val/=).
      iPoseProof (ty_has_layout with "Hv") as "(%ly' & %Hst' & %Hly)".
      iR.
      iExists ly. iR. iPureIntro. rewrite /has_layout_val Hly.
      eapply syn_type_size_eq_use; done.
  Qed.
  Lemma owned_type_incl_uninit π {rt1 : RT} (r1 : rt1) r2 (ty1 : type rt1) st :
    st = ty_syn_type ty1 MetaNone →
    ⊢ owned_type_incl π r1 r2 ty1 (uninit st).
  Proof.
    iIntros (Hst). iSplitR; last iSplitR.
    - iPureIntro.
      simpl. rewrite Hst. apply syn_type_size_eq_refl.
    - simpl. eauto.
    - iIntros (v) "Hv". rewrite uninit_own_spec.
      iPoseProof (ty_has_layout with "Hv") as "(%ly & %Hst' & %Hly)".
      iR.
      iExists ly. subst st. iR. done.
  Qed.
End lemmas.

Section deinit.
  Context `{!typeGS Σ}.

  (** ** Instances for deinitializing a type *)
  (** Types have more specific instances that we generally prefer in [.../deinit.v] *)


  (* Required instances;
     - box (maybe not?)
     - struct
     - enum
     - array
     Maybe:
     - opened (in case we did not re-establish the invariant, but still have the underlying struct etc) *)

  (*
  Lemma owned_subltype_step_array_uninit π E L l {rts} (lts : hlist ltype rts) rs sls st T :
    owned_subltype_step π E L l #rs #() (ArrayLtype def len iml) (◁ uninit st) T :-
    exhale (⌜st = sls⌝);
    L2, R2 ← iterate: zip (hpzipl rts lts rs) sls.(sls_fields) with L, True%I {{ '((existT rt (lt, r)), (field, stf)) T L2 R2,
      return owned_subltype_step π E L2 (l atst{sls}ₗ field) r #() lt (◁ uninit stf) (λ L3 R3,
        T L3 (R2 ∗ R3))
      }};
    return T L2 R2.
  Proof.
    *)

  (* Two low-priority instances that trigger as a fallback for ltypes foldable to a ty (no borrows below) *)
  (* First, if the syntype is equal *)
  Lemma owned_subltype_step_ofty_uninit_eq π E L {rt} (lt : ltype rt) r st l `{Hst : !TCDone (ltype_st lt = st)} T :
    owned_subltype_step π E L l #r #() lt (◁ uninit st) T :-
    return cast_ltype_to_type E L lt (λ ty, T L (ty_ghost_drop ty π r)).
  Proof.
    unfold TCDone in Hst. subst st.
    iDestruct 1 as "(%ty & %Heqt & HT)".
    iIntros (??) "CTX HE HL Hl". simp_ltypes; simpl.

    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hincl"; first apply Heqt.
    iSpecialize ("Hincl" $! (Owned) (#r)).
    iDestruct "Hincl" as "(Hincl & _)". iDestruct "Hincl" as "(%Hst & Hincl & _)".
    iMod (ltype_incl'_use with "Hincl Hl") as "Hl"; first done.
    iExists _, _. iFrame.
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & %Hst' & %)".
    simp_ltypes in Hst'.
    iSplitL.
    { iMod (ofty_own_split_value_untyped with " Hl") as "(%v & Hv & Hl)"; [done.. | ].
      iPoseProof (ty_own_ghost_drop with "Hv") as "Hb"; first done.
      iApply (logical_step_wand with "Hb"). iModIntro. iIntros "$".
      iApply (ofty_owned_subtype_aligned with "[] Hl").
      { simpl. rewrite Hst. done. }
      { done. }
      rewrite Hst.
      iApply owned_type_incl_uninit'.
      - simpl.
        intros ?(-> & _)%syn_type_has_layout_untyped_inv.
        eauto.
      - done. }
    iPureIntro. rewrite Hst. apply syn_type_size_eq_refl.
  Qed.
  Definition owned_subltype_step_ofty_uninit_eq_inst := [instance owned_subltype_step_ofty_uninit_eq].
  Global Existing Instance owned_subltype_step_ofty_uninit_eq_inst | 100.

  (* Otherwise, more complicated: *)
  Lemma owned_subltype_step_ofty_uninit π E L {rt} (lt : ltype rt) r st l T :
    owned_subltype_step π E L l #r #() lt (◁ uninit st) T :-
    return
    cast_ltype_to_type E L lt (λ ty,
    li_tactic (compute_layout_goal (ty_syn_type ty MetaNone)) (λ ly1,
      ⌜syn_type_has_layout (ty_syn_type ty MetaNone) ly1⌝ -∗
      li_tactic (compute_layout_goal st) (λ ly2,
        ⌜syn_type_has_layout st ly2⌝ -∗
        ⌜l `has_layout_loc` ly1⌝ -∗ ⌜l `has_layout_loc` ly2⌝ ∗
        ⌜ly_size ly1 = ly_size ly2⌝ ∗
        T L (ty_ghost_drop ty π r)))).
  Proof.
    iDestruct 1 as "(%ty & %Heqt & HT)".
    rewrite /compute_layout_goal.
    iDestruct "HT" as "(%ly1 & %Hst1 & HT)".
    iDestruct ("HT" with "[//]") as "(%ly2 & %Hst2 & HT)".
    iIntros (??) "CTX HE HL Hl". simp_ltypes; simpl.

    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hincl"; first apply Heqt.
    iSpecialize ("Hincl" $! (Owned) (#r)).
    iDestruct "Hincl" as "(Hincl & _)". iDestruct "Hincl" as "(%Hst & Hincl & _)".
    iMod (ltype_incl'_use with "Hincl Hl") as "Hl"; first done.

    iPoseProof (ltype_own_has_layout' with "Hl") as "%". { simp_ltype. rewrite Heq_lt. done. }
    iDestruct ("HT" with "[//] [//]") as "(%Hly' & %Hsz & HT)".

    iExists _, _. iFrame.
    assert (syn_type_size_eq (ltype_st lt) st) as ?.
    { rewrite Hst ltype_st_ofty. by eapply syn_type_size_eq_prove. }
    iSplitL.
    { iMod (ofty_own_split_value_untyped with "Hl") as "(%v & Hv & Hl)"; [done.. | ].
      iPoseProof (ty_own_ghost_drop with "Hv") as "Hb"; first done.
      iApply (logical_step_wand with "Hb"). iModIntro. iIntros "$".
      iApply (ofty_owned_subtype_aligned with "[] Hl"); [done | | ].
      { done. }
      iApply owned_type_incl_uninit'; last done.
      simpl.
      intros ?(-> & _)%syn_type_has_layout_untyped_inv.
      eauto. }
    iPureIntro. done.
  Qed.
  Definition owned_subltype_step_ofty_uninit_inst := [instance owned_subltype_step_ofty_uninit].
  Global Existing Instance owned_subltype_step_ofty_uninit_inst | 101.
End deinit.

Section deinit_fallback.
  Context `{!typeGS Σ}.

  (** Fallback instances without a logical step -- here, we cannot ghost_drop *)

  (* TODO: maybe restrict this instance more for earlier failure *)
  Lemma uninit_mono π E L l {rt} (ty : type rt) r st T :
    subsume_full E L false
      (l ◁ₗ[π, Owned] #r @ (◁ ty))
      (l ◁ₗ[π, Owned] .@ (◁ (uninit st))) T :-
    ly ← tactic (compute_layout_goal st);
    exhale (⌜syn_type_has_layout (ty.(ty_syn_type) MetaNone) ly⌝);
    ∀ v,
    inhale (v ◁ᵥ{π, MetaNone} r @ ty);
    return T L True%I.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "(%ly & %Halg1 & %Halg2 & HT)".
    iIntros (????) "#CTX #HE HL Hl".
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own. simpl.
    iDestruct "Hl" as "(%ly' & %Halg & %Hly & Hsc & ? & %r' & <- & Hv)".
    iMod (fupd_mask_mono with "Hv") as "(%v & Hl & Hv)"; first done.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%"; first done.
    iExists L, True%I. iPoseProof ("HT" with "Hv") as "$". iFrame "HL".
    rewrite right_id. assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own. simpl.
    iExists ly. iSplitR; first done. iSplitR; first done.
    iSplitR; first done. iFrame. iExists _. iSplitR; first done.
    iModIntro. iModIntro.
    rewrite uninit_own_spec.
    iR.
    iExists ly. done.
  Qed.
  Definition uninit_mono_inst := [instance uninit_mono].
  Global Existing Instance uninit_mono_inst | 40.

  (** We have this instance because it even works when [r1 = PlaceGhost ..] *)
  Lemma weak_subltype_deinit E L {rt1 : RT} (r1 : place_rfn rt1) r2 (ty : type rt1) st T :
    weak_subltype E L (Owned) r1 #r2 (◁ ty) (◁ uninit st) T :-
    exhale (⌜ty_syn_type ty MetaNone = st⌝);
    return T.
  Proof.
    iIntros "(%Hst & HT)".
    iIntros  (??) "#CTX #HE HL". iFrame.
    iModIntro. iModIntro. simp_ltypes. iR.
    rewrite -bi.persistent_sep_dup.
    iModIntro. iIntros (??) "Hl".
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & %Hst' & %Hly)".
    iModIntro. iApply (ofty_owned_subtype_aligned' with "[] Hl").
    { simp_ltypes in Hst'. simpl. subst st. apply Hst'. }
    { done. }
    iIntros. iApply owned_type_incl_uninit. done.
  Qed.
  Definition weak_subltype_deinit_inst := [instance weak_subltype_deinit].
  Global Existing Instance weak_subltype_deinit_inst.

  Lemma owned_subtype_to_uninit π E L pers {rt} (ty1 : type rt) r st2 T :
    owned_subtype π E L pers r () (ty1) (uninit st2) T :-
    ly1 ← tactic (compute_layout_goal (ty_syn_type ty1 MetaNone));
    (* augment context *)
    inhale (⌜enter_cache_hint(syn_type_has_layout (ty_syn_type ty1 MetaNone) ly1)⌝);
    ly2 ← tactic (compute_layout_goal st2);
    (* augment context *)
    inhale (⌜enter_cache_hint(syn_type_has_layout st2 ly2)⌝);
    exhale (⌜ly_size ly1 = ly_size ly2⌝);
    return T L.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "(%ly1 & %Hst1 & HT)".
    iDestruct ("HT" with "[//]") as "(%ly2 & %Hst2 & HT)".
    iDestruct ("HT" with "[//]") as "(%Hsz & HT)".
    iIntros (????) "#CTX #HE HL".
    iModIntro. iExists _. iFrame. iApply bi.intuitionistically_intuitionistically_if.
    iModIntro.
    iSplit; last iSplitR.
    - iPureIntro. simpl.
      by eapply syn_type_size_eq_prove.
    - simpl. eauto.
    - iIntros (v) "Hv".
      rewrite uninit_own_spec.
      iPoseProof (ty_own_val_has_layout with "Hv") as "%Hv"; first done.
      (*iIntros "(%ly & %Hst & %Hly & Hv)".*)
      iR.
      iExists _. iR.
      iPureIntro. move: Hv. rewrite /has_layout_val Hsz//.
  Qed.
  Definition owned_subtype_to_uninit_inst := [instance owned_subtype_to_uninit].
  Global Existing Instance owned_subtype_to_uninit_inst.
End deinit_fallback.

Section evar.
  Context `{!typeGS Σ}.

  (** ** Evar instantiation *)
  Lemma uninit_mono_untyped_evar π E L step l ly1 ly2 `{!IsProtected ly2} T :
    subsume_full E L step
      (l ◁ₗ[π, Owned] .@ (◁ uninit (UntypedSynType ly1)))
      (l ◁ₗ[π, Owned] .@ (◁ uninit (UntypedSynType ly2))) T :-
    exhale (⌜ly1 = ly2⌝);
    return (T L True%I).
  Proof. iIntros "(-> & HT)". iApply subsume_full_subsume. iFrame. eauto. Qed.
  Definition uninit_mono_untyped_evar_inst := [instance uninit_mono_untyped_evar].
  Global Existing Instance uninit_mono_untyped_evar_inst | 10.

  Lemma uninit_mono_untyped_id E L π step l (ly1 ly2 : layout) `{TCDone (ly1 = ly2)} T:
    subsume_full E L step
      (l ◁ₗ[π, Owned] .@ (◁ uninit (UntypedSynType ly1)))
      (l ◁ₗ[π, Owned] .@ (◁ uninit (UntypedSynType ly2))) T :-
    return (T L True%I).
  Proof.
    match goal with
    | H : TCDone _ |- _ => rename H into Heq
    end.
    rewrite /TCDone in Heq. subst. iIntros "HL".
    iApply subsume_full_subsume. iFrame. eauto.
  Qed.
  Definition uninit_mono_untyped_id_inst := [instance uninit_mono_untyped_id].
  Global Existing Instance uninit_mono_untyped_id_inst | 11.
End evar.

Section init.
  Context `{!typeGS Σ}.

  (** ** Subsumption with uninit on the LHS (for initializing) *)
  Lemma subsume_full_ofty_owned_subtype π E L step l {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) r1 r2 T :
    subsume_full E L step
      (l ◁ₗ[π, Owned] #r1 @ ◁ ty1)
      (l ◁ₗ[π, Owned] #r2 @ ◁ ty2) T :-
    ly1 ← tactic (compute_layout_goal (ty_syn_type ty1 MetaNone));
      (* augment context *)
    inhale (⌜enter_cache_hint(syn_type_has_layout (ty_syn_type ty1 MetaNone) ly1)⌝);
    ly2 ← tactic (compute_layout_goal (ty_syn_type ty2 MetaNone));
    (* augment context *)
    inhale (⌜enter_cache_hint(syn_type_has_layout (ty_syn_type ty2 MetaNone) ly2)⌝);
    inhale (⌜l `has_layout_loc` ly1⌝);
    exhale (⌜l `has_layout_loc` ly2⌝);
    return (owned_subtype π E L false r1 r2 ty1 ty2 (λ L', (T L' True%I))).
  Proof.
    rewrite /compute_layout_goal. iIntros "(%ly1 & %Halg1 & HT)".
    iDestruct ("HT" with "[//]") as "(%ly2 & %Halg2 & HT)".
    iIntros (????) "#CTX #HE HL Hl".
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly1' & %Halg1' & %Hlyl)".
    assert (ly1' = ly1) as -> by by eapply syn_type_has_layout_inj.
    iDestruct ("HT" with "[//] [//]") as "(%Hl_ly2 & Hsubt)".
    iMod ("Hsubt" with "[//] [//] [//] CTX HE HL") as "(%L' & Hv & ? & ?)".
    iExists L', True%I. iFrame.
    iApply maybe_logical_step_intro. rewrite right_id.
    iApply (ofty_owned_subtype_aligned with "Hv Hl"); done.
  Qed.
  (** We only declare an instance for this where the LHS is uninit -- generally, we'd rather want to  go via the "full subtyping" judgments,
    because the alignment sidecondition here may be hard to prove explicitly. *)
  Definition subsume_full_ofty_owned_subtype_uninit π E L step l {rt2} (ty2 : type rt2) r2 st :=
    subsume_full_ofty_owned_subtype π E L step l (uninit st) ty2 () r2.
  Definition subsume_full_ofty_owned_subtype_uninit_inst := [instance subsume_full_ofty_owned_subtype_uninit].
  Global Existing Instance subsume_full_ofty_owned_subtype_uninit_inst | 30.
End init.
