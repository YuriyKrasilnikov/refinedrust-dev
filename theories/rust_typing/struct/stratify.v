From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust.struct Require Import def subltype.
From refinedrust Require Import options.

(** ** Stratification instances for structs *)

Section stratify.
  Context `{!typeGS Σ}.

  Definition stratify_ltype_struct_iter_cont_t := llctx → iProp Σ → ∀ rts' : list RT, hlist ltype rts' → plist place_rfnRT rts' → iProp Σ.
  Definition stratify_ltype_struct_iter (π : thread_id) (E : elctx) (L : llctx) (mu : StratifyMutabilityMode) (md : StratifyDescendUnfoldMode) (ma : StratifyAscendMode) {M} (m : M) (l : loc) (i0 : nat) (sls : struct_layout_spec) {rts} (ltys : hlist ltype rts) (rfns : plist place_rfnRT rts) (k : bor_kind) (T : stratify_ltype_struct_iter_cont_t) : iProp Σ :=
    ∀ F sl, ⌜lftE ⊆ F⌝ -∗
    ⌜lft_userE ⊆ F⌝ -∗
    ⌜shrE ⊆ F⌝ -∗
    rrust_ctx -∗
   elctx_interp E -∗
    llctx_interp L -∗
    ⌜struct_layout_spec_has_layout sls sl⌝ -∗
    ⌜i0 ≤ length sls.(sls_fields)⌝ -∗
    ⌜(i0 + length rts = length sls.(sls_fields))%nat⌝ -∗
    ([∗ list] i ↦ p ∈ hpzipl rts ltys rfns, let '(existT rt (lt, r)) := p in
      ∃ name st, ⌜sls.(sls_fields) !! (i + i0)%nat = Some (name, st)⌝ ∗
      (l atst{sls}ₗ name) ◁ₗ[π, k] r @ lt) ={F}=∗
    ∃ (L' : llctx) (R' : iProp Σ) (rts' : list RT) (ltys' : hlist ltype rts') (rfns' : plist place_rfnRT rts'),
      ⌜length rts = length rts'⌝ ∗
      ([∗ list] i ↦ p; p2 ∈ hpzipl rts ltys rfns; hpzipl rts' ltys' rfns',
          let '(existT rt (lt, r)) := p in
          let '(existT rt' (lt', r')) := p2 in
          ⌜ltype_st lt = ltype_st lt'⌝) ∗
      logical_step F (
        ([∗ list] i ↦ p ∈ hpzipl rts' ltys' rfns', let '(existT rt (lt, r)) := p in
          ∃ name st, ⌜sls.(sls_fields) !! (i + i0)%nat = Some (name, st)⌝ ∗
          (l atst{sls}ₗ name) ◁ₗ[π, k] r @ lt) ∗ R') ∗
      llctx_interp L' ∗
      T L' R' rts' ltys' rfns'.

  Lemma stratify_ltype_struct_iter_nil π E L mu md ma {M} (m : M) (l : loc) sls k i0 (T : stratify_ltype_struct_iter_cont_t) :
    T L True [] +[] -[]
  ⊢ stratify_ltype_struct_iter π E L mu md ma m l i0 sls +[] -[] k T.
  Proof.
    iIntros "HT". iIntros (?????) "#CTX #HE HL ??? Hl".
    iModIntro. iExists L, True%I, [], +[], -[].
    iR. iFrame. simpl. iApply logical_step_intro; eauto.
  Qed.

  Lemma stratify_ltype_struct_iter_cons π E L mu mdu ma {M} (m : M) (l : loc) sls i0 {rts rt} (ltys : hlist ltype rts) (rfns : plist place_rfnRT (rt :: rts)) (lty : ltype rt) k T :
    (∃ r rfns0, ⌜rfns = r -:: rfns0⌝ ∗
    stratify_ltype_struct_iter π E L mu mdu ma m l (S i0) sls ltys rfns0 k (λ L2 R2 rts2 ltys2 rs2,
      (∀ name st, ⌜sls.(sls_fields) !! i0 = Some (name, st)⌝ -∗
      stratify_ltype π E L2 mu mdu ma m (l atst{sls}ₗ name) lty r k (λ L3 R3 rt3 lty3 r3,
        T L3 (R3 ∗ R2) (rt3 :: rts2) (lty3 +:: ltys2) (r3 -:: rs2)))))
    ⊢ stratify_ltype_struct_iter π E L mu mdu ma m l i0 sls (lty +:: ltys) (rfns) k T.
  Proof.
    iIntros "(%r &  %rfns0 & -> & HT)". iIntros (?????) "#CTX #HE HL %Halg %Hlen %Hleneq Hl".
    simpl. iDestruct "Hl" as "(Hl & Hl2)". simpl in *.
    iMod ("HT" with "[//] [//] [//] CTX HE HL [//] [] [] [Hl2]") as "(%L2' & %R2' & %rts2' & %ltys2' & %rfns2' & %Hlen' & Hst & Hl2 & HL & HT)".
    { rewrite -Hleneq. iPureIntro. lia. }
    { rewrite -Hleneq. iPureIntro. lia. }
    { iApply (big_sepL_mono with "Hl2"). intros ? [? []] ?. by rewrite Nat.add_succ_r. }
    iDestruct "Hl" as "(%name & %st & %Hlook & Hl)".
(*edestruct (lookup_lt_is_Some_2 sls.(sls_fields) i0) as ([name ?] & Hlook); first by lia.*)
    iMod ("HT" with "[//] [//] [//] [//] CTX HE HL Hl") as "(%L3 & %R3 & %rt' & %lt' & %r' & HL & Hst1 & Hl & HT)".
    iModIntro. iExists L3, (R3 ∗ R2')%I, _, _, _. iFrame.
    iSplitR. { rewrite Hlen'. done. }
    iApply (logical_step_compose with "Hl2"). iApply (logical_step_wand with "Hl").
    iIntros "(Hl & HR1) (Hl2 & HR2)".
    simpl. iFrame "HR1 HR2".
    iSplitL "Hl". { iExists _, _. iFrame. done. }
    iApply (big_sepL_mono with "Hl2"). intros ? [? []] ?. by rewrite Nat.add_succ_r.
  Qed.

  Lemma stratify_ltype_struct_owned {rts} π E L mu mdu ma {M} (m : M) l (lts : hlist ltype rts) (rs : plist place_rfnRT rts) sls (T : stratify_ltype_cont_t) :
    stratify_ltype_struct_iter π E L mu mdu ma m l 0 sls lts rs Owned (λ L2 R2 rts' lts' rs',
      T L2 R2 (plist place_rfnRT rts') (StructLtype lts' sls) (#rs'))
    ⊢ stratify_ltype π E L mu mdu ma m l (StructLtype lts sls) (#rs) (Owned) T.
  Proof.
    iIntros "HT". iIntros (????) "#CTX #HE HL Hl".
    iPoseProof (struct_ltype_acc_owned with "Hl") as "(%sl & %Halg & %Hly & %Hlen & Hlb & >(Hl & Hcl))"; first done.
    iPoseProof (struct_ltype_focus_components with "Hl") as "(Hl & Hlcl)"; [done | done | ].
    iMod ("HT" with "[//] [//] [//] CTX HE HL [//] [] [] [Hl]") as "(%L2 & %R2 & %rts' & %lts' & %rs' & %Hleneq & Hst & Hstep & HL & HT)".
    { iPureIntro. lia. }
    { rewrite Hlen.  done. }
    { iApply (big_sepL_mono with "Hl"). intros ? [? []] ?. rewrite Nat.add_0_r. done. }
    iModIntro. iExists L2, R2, _, _, _. iFrame. simp_ltypes. iR.
    iApply logical_step_fupd.
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_compose with "Hcl").
    iApply logical_step_intro.
    iIntros "Hcl (Ha & $)".
    iPoseProof ("Hlcl" $! rts' lts' rs' with "[//] [Hst] [Ha]") as "Hl".
    { iApply big_sepL2_Forall2.
      iApply (big_sepL2_impl with "Hst"). iModIntro. iIntros (? [? []] [? []] ? ?); done. }
    { iApply (big_sepL_mono with "Ha"). intros ? [? []] ?. rewrite Nat.add_0_r. eauto. }
    iMod ("Hcl" with "[] Hl") as "Hl"; first done.
    by iFrame.
  Qed.
  Definition stratify_ltype_struct_owned_inst := [instance @stratify_ltype_struct_owned].
  Global Existing Instance stratify_ltype_struct_owned_inst.

  Lemma stratify_ltype_struct_uniq {rts} π E L mu mdu ma {M} (m : M) l (lts : hlist ltype rts) (rs : plist place_rfnRT rts) sls κ γ (T : stratify_ltype_cont_t) :
    li_tactic (lctx_lft_alive_count_goal E L κ) (λ '(κs, L1),
      stratify_ltype_struct_iter π E L1 mu mdu ma m l 0 sls lts rs Owned (λ L2 R rts' lts' rs',
        (* validate the update *)
        li.iterate (λ '((existT rt1 lt1), (existT rt2 lt2)) T (upd : place_update_kind),
          prove_place_cond E L2 UpdStrong lt1 lt2 (λ upd', T (place_update_kind_max upd' upd)))
        (λ upd,
            li_tactic (check_llctx_place_update_kind_incl_goal E L2 upd (UpdUniq [κ])) (λ b,
            if b then
              (* update obeys the contract, get a mutable reference *)
              ⌜fast_eq_hint (rts' = rts)⌝ ∗
              match ma with
              | StratRefoldFull =>
                  cast_ltype_to_type E L2 (StructLtype lts' sls) (λ ty',
                  T L2 (llft_elt_toks κs ∗ R) _ (◁ ty')%I (#rs'))
              | _ =>
                  T L2 (llft_elt_toks κs ∗ R) _ (StructLtype lts' sls) (#rs')
              end
            else
              (* unfold to an OpenedLtype *)
              ⌜fast_eq_hint (ma = StratNoRefold)⌝ ∗
              T L2 R _ (OpenedLtype (StructLtype lts' sls) (StructLtype lts sls) (StructLtype lts sls) (λ r1 r2, ⌜r1 = r2⌝) (λ _ _, llft_elt_toks κs)) (#rs')
          )) (zip (hzipl _ lts) (hzipl _ lts')) (UpdUniq []) ))
    ⊢ stratify_ltype π E L mu mdu ma m l (StructLtype lts sls) (#rs) (Uniq κ γ) T.
  Proof.
    iIntros "HT". iIntros (????) "#CTX #HE HL Hl".
    rewrite /lctx_lft_alive_count_goal.
    iDestruct "HT" as "(%κs & %L1 & %Hal & HT)".
    iMod (fupd_mask_subseteq lftE) as "Hm"; first done.
    iMod (lctx_lft_alive_count_tok with "HE HL") as "(%q & Htok & Hcltok & HL)"; [done.. | ].
    iMod ("Hm") as "_".
    iPoseProof (struct_ltype_acc_uniq with "CTX Htok Hcltok Hl") as "(%sl & %Halg & %Hly & %Hlen & Hlb & >(Hl & Hcl))"; first done.
    iPoseProof (struct_ltype_focus_components with "Hl") as "(Hl & Hlcl)"; [done | done | ].
    iMod ("HT" with "[//] [//] [//] CTX HE HL [//] [] [] [Hl]") as "(%L2 & %R2 & %rts' & %lts' & %rs' & %Hleneq & Hst & Hstep & HL & HT)".
    { iPureIntro. lia. }
    { rewrite Hlen.  done. }
    { iApply (big_sepL_mono with "Hl"). intros ? [? []] ?. rewrite Nat.add_0_r. done. }
    iAssert (⌜Forall2 (λ '(existT rt (lt, _)) '(existT rt' (lt', _)), ltype_st lt = ltype_st lt') (hpzipl rts lts rs) (hpzipl rts' lts' rs')⌝)%I as "%Hf".
    { iApply big_sepL2_Forall2. iApply (big_sepL2_impl with "Hst"). iModIntro.
  iIntros (? [? []] [? []] ??). done. }


    set (INV n upd := (llctx_interp L2 ∗ [∗ list] lt; lt' ∈ take n (hzipl rts lts); take n (hzipl rts' lts'), typed_place_cond upd (projT2 lt) (projT2 lt'))%I).
    iMod (iterate_elim1_fupd INV with "HT [HL] []") as "(%upd & Hinv & HT)".
    { (* initialization *)rewrite /INV. iFrame. done. }
    { (* preservation *)
      iModIntro. iIntros (i [[rt1 lt1] [rt2 lt2]] T' upd Hlook) "Hinv".
      apply lookup_zip_Some in Hlook as [Hlook1 Hlook2]. iIntros "Hcond".
      rewrite /INV. iDestruct "Hinv" as "(HL & Hconds)".
      iMod ("Hcond" with "[] CTX HE HL") as "(HL & %upd' & #Hincl & Hcond' & _ & HT)"; first done.
      iFrame.
      replace (S i) with (i + 1) by lia.
      rewrite -!(take_take_drop _ i 1).
      iApply (big_sepL2_app  with "[Hconds]").
      { iApply (big_sepL2_impl with "Hconds").
        iModIntro. iIntros (? [] [] ??) "Hcond".
        iApply typed_place_cond_incl; last done.
        iApply place_update_kind_max_incl_r. }
      opose proof * lookup_lt_Some as Hlt1; first apply Hlook1.
      opose proof * lookup_lt_Some as Hlt2; first apply Hlook2.

      eapply take_drop_middle in Hlook1.
      eapply take_drop_middle in Hlook2.
      rewrite -Hlook1 -Hlook2.
      (* TODO remove base.drop_app_length' *)
      rewrite !drop_app.
      rewrite drop_ge; first last.
      { rewrite length_take. lia. }
      rewrite length_take Nat.min_l; first last.
      { by apply Nat.lt_le_incl. }
      rewrite Nat.sub_diag; simpl.
      rewrite take_0.
      rewrite drop_ge; first last.
      { rewrite length_take. lia. }
      rewrite length_take Nat.min_l; first last.
      { by apply Nat.lt_le_incl. }
      rewrite Nat.sub_diag; simpl.
      iL. iApply typed_place_cond_incl; last done.
      iApply place_update_kind_max_incl_l. }
    iDestruct "Hinv" as "(HL & Hupd)".
    rewrite !firstn_all2; cycle 1.
    { rewrite length_zip !length_hzipl. lia. }
    { rewrite length_zip !length_hzipl. lia. }

    rewrite /check_llctx_place_update_kind_incl_goal.
    iDestruct "HT" as "(%b & %Hb & HT)".
    destruct b; simpl.
    - (* update obeys contract *)
      iDestruct "HT" as "(-> & HT)".
      iPoseProof (lctx_place_update_kind_incl_acc with "HE HL") as "#Hincl"; first apply Hb.
      iAssert (∃ lt', ⌜full_eqltype E L2 (StructLtype lts' sls) lt'⌝ ∗ T L2 (llft_elt_toks κs ∗ R2) (plistRT rts) lt' (#rs'))%I  with "[HT]" as "(%lt' & %Heqt & HT)".
      { destruct ma; [ | iFrame; iPureIntro; reflexivity.. ].
        iDestruct "HT" as "(%ty & %Heqt & HT)". by iFrame. }

      iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hinc"; [ apply Heqt | ].
      iFrame.
      iSplitR. { iSpecialize ("Hinc" $! Owned inhabitant). iApply (ltype_eq_syn_type with "Hinc"). }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply (logical_step_compose with "Hcl").
      iApply logical_step_intro.
      iModIntro. iIntros "Hcl (Helems & HR)".
      iDestruct "Hcl" as "[Hcl _]".
      iPoseProof ("Hlcl" with "[] [] [Helems]") as "Ha".
      3: { iApply (big_sepL_impl with "Helems").
        iModIntro. iIntros (? [? []]?). rewrite Nat.add_0_r. eauto. }
      { done. }
      { iPureIntro. eapply Forall2_impl; first apply Hf.  intros [? []] [?[]]. done. }

      iMod ("Hcl" with "Hincl Ha Hupd") as "(Hl & $ & _)".
      iDestruct ("Hinc" $! (Uniq κ γ) _) as "((_ & #Hinc1 & _) & _)".
      iPoseProof ("Hinc1" with "Hl") as "Hl".
      by iFrame.
    - (* update doesn't obey contract, leave open *)
      iDestruct "HT" as "(-> & HT)".
      iFrame. iR.
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply (logical_step_compose with "Hcl").
      iApply logical_step_intro.
      iModIntro. iIntros "Hcl (Helems & HR)".
      iDestruct "Hcl" as "[_ Hcl]".
      iPoseProof ("Hlcl" with "[] [] [Helems]") as "Ha".
      3: { iApply (big_sepL_impl with "Helems").
        iModIntro. iIntros (? [? []]?). rewrite Nat.add_0_r. eauto. }
      { done. }
      { iPureIntro. eapply Forall2_impl; first apply Hf.  intros [? []] [?[]]. done. }

      iPoseProof ("Hcl" with "[] Ha") as "Hl"; first done.
      by iFrame.
  Qed.
  Definition stratify_ltype_struct_uniq_inst := [instance @stratify_ltype_struct_uniq].
  Global Existing Instance stratify_ltype_struct_uniq_inst.
End stratify.

Global Typeclasses Opaque stratify_ltype_struct_iter.
