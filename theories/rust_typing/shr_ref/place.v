From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust.shr_ref Require Import def subltype unfold.
From refinedrust Require Import options.

(** ** Place access rules for shared references *)

Section place.
  Context `{!typeGS Σ}.

  Lemma typed_place_shr_owned {rto} f κ (lt2 : ltype rto) P E L l r bmin0 (T : place_cont_t (place_rfn rto) bmin0) :
   introduce_with_hooks E L (£1) (λ L1,
     ∀ l', typed_place E L1 f l' lt2 r bmin0 (Shared κ) P
        (λ L' κs l2 b2 bmin rti tyli ri updcx,
          T L' (κs) l2 b2 bmin rti tyli ri
          (λ L2 upd cont, updcx L2 upd (λ upd',
            cont (mkPUpd _ bmin0
            (place_rfn (upd').(pupd_rt))
            (ShrLtype (upd').(pupd_lt) κ)
            (# (upd').(pupd_rfn))
            (upd').(pupd_R)
            (upd').(pupd_performed)
            (opt_place_update_eq_lift place_rfnRT (upd').(pupd_eq_1))
            (opt_place_update_eq_lift place_rfnRT (upd').(pupd_eq_2)))))))
    ⊢ typed_place E L f l (ShrLtype lt2 κ) (#r) bmin0 (Owned) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    iIntros "HR" (Φ F ??).
    iIntros "#(LFT & LLCTX) #HE HL Hf HP HΦ/=".
    iPoseProof (shr_ltype_acc_owned F with "[$LFT $LLCTX] HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
    iApply fupd_wpe. iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iMod "Hb" as "(%l' & Hl & Hb & Hcl)". iMod "HclF" as "_". iModIntro.
    iApply wpe_fupd.
    iApply (wp_deref with "Hl") => //; [solve_ndisj | by apply val_to_of_loc | ].
    iApply physical_step_intro_lc. iIntros "Hcred !> !>".
    iIntros (st) "Hl". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iMod "HclF" as "_". iExists l'.
    iSplitR. { iPureIntro. unfold mem_cast. rewrite val_to_of_loc. done. }
    iMod ("HR" with "[] [$] HE HL [Hcred]") as "(%L1 & HL & HR)"; first done.
    { iApply lc_weaken; last done. unfold num_laters_per_step. lia. }
    iApply ("HR" with "[//] [//] [$LFT $LLCTX] HE HL Hf Hb").
    iModIntro. iIntros (L' κs l2 bmin b2 rti tyli ri updcx) "Hb Hs".
    iApply ("HΦ" $! _ _ _ bmin with "Hb"). simpl.
    iIntros (upd) "Hincl Hl2 %Hsteq HR Hcond".
    iMod ("Hs" with "Hincl Hl2 [//] HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hs" with "HL Hf Hcont") as (upd') "(Hb & %Hsteq' & Hcond & HR & ? & ? & ?)".
    iFrame. simpl.
    iMod ("Hcl" with "Hl Hb") as "Hb".
    iFrame. simp_ltypes. iR.
    by iApply shr_ltype_place_cond.
  Qed.
  Definition typed_place_shr_owned_inst := [instance @typed_place_shr_owned].
  Global Existing Instance typed_place_shr_owned_inst | 30.

  Lemma typed_place_shr_uniq {rto} f κ (lt2 : ltype rto) P E L l r κ' γ bmin0 (T : place_cont_t (place_rfn rto) bmin0) :
    li_tactic (lctx_lft_alive_count_goal E L κ') (λ '(κs, L1),
      introduce_with_hooks E L1 (£1) (λ L2,
      (∀ l', typed_place E L2 f l' lt2 r (bmin0) (Shared κ) P
        (λ L3 κs' l2 b2 bmin rti tyli ri updcx,
          T L3 (κs') l2 b2 bmin rti tyli ri
            (λ L4 upd cont, updcx L4 upd (λ upd',
              li_tactic (check_llctx_place_update_kind_incl_goal E L4 upd'.(pupd_performed) (UpdUniq [κ'])) (λ b,
              if b then
                (* keep ShrLtype *)
                cont (mkPUpd _ bmin0
                  (place_rfn (upd').(pupd_rt))
                  (ShrLtype (upd').(pupd_lt) κ)
                  (# (upd').(pupd_rfn))
                  ((upd').(pupd_R) ∗ llft_elt_toks κs)
                  (upd').(pupd_performed)
                  (opt_place_update_eq_lift place_rfnRT (upd').(pupd_eq_1))
                  (opt_place_update_eq_lift place_rfnRT (upd').(pupd_eq_2)))
              else
                (* fold to OpenedLtype *)
                (* for this, we need to allow strong updates *)
                ⌜bmin0 = UpdStrong⌝ ∗
                cont (mkPUpd _ bmin0
                  (place_rfn (upd').(pupd_rt))
                  (OpenedLtype (ShrLtype upd'.(pupd_lt) κ) (ShrLtype lt2 κ) (ShrLtype lt2 κ) (λ r1 r1', ⌜r1 = r1'⌝) (λ _ _, llft_elt_toks κs))
                  (# (upd').(pupd_rfn))
                  (upd').(pupd_R)
                  UpdStrong
                  I
                  (opt_place_update_eq_lift place_rfnRT (upd').(pupd_eq_2)))
              )))
        ))))
    ⊢ typed_place E L f l (ShrLtype lt2 κ) (#r) bmin0 (Uniq κ' γ) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%κs & %L2 & %Hal & HT)".
    iIntros (Φ F ??). iIntros "#(LFT & LLCTX) #HE HL Hf HP HΦ/=".
    (* get a token *)
    iApply fupd_wpe. iMod (fupd_mask_subseteq lftE) as "HclF"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as (q) "(Hκ' & Hclκ' & HL)"; [done.. | ].
    iMod "HclF" as "_". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iPoseProof (shr_ltype_acc_uniq F with "[$LFT $LLCTX] Hκ' Hclκ' HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
    iMod "Hb" as "(%l' & Hl & Hb & Hcl)". iMod "HclF" as "_". iModIntro.
    iApply wpe_fupd.
    iApply (wpe_logical_step with "Hcl"); [solve_ndisj.. | ].
    iApply (wp_deref with "Hl") => //; [solve_ndisj | by apply val_to_of_loc | ].
    iApply physical_step_intro_lc. iIntros "Hcred !> !>".
    iIntros (st) "Hl Hc". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iMod "HclF" as "_". iExists l'.
    iSplitR. { iPureIntro. unfold mem_cast. rewrite val_to_of_loc. done. }
    iMod ("HT" with "[] [$] HE HL [Hcred]") as "(%L1 & HL & HT)"; first done.
    { iApply lc_weaken; last done. unfold num_laters_per_step. lia. }
    iApply ("HT" with "[//] [//] [$LFT $LLCTX] HE HL Hf Hb").
    iModIntro. iIntros (L' κs' l2 bmin b2 rti tyli ri updcx) "Hb Hs".
    iApply ("HΦ" $! _ _ _ bmin with "Hb").
    simpl. iIntros (upd) "#Hincl Hl2 %Hst ? Hcond".
    iMod ("Hs" with "Hincl Hl2 [//] [$] Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hs" with "HL Hf Hcont") as (upd') "(Hb & %Hsteq & Hcond & ? & ? & ? & HL & Hf & HT)".
    unfold check_llctx_place_update_kind_incl_goal.
    iDestruct "HT" as (b Hb) "HT".
    destruct b; simpl.
    - (* weak *)
      iDestruct "Hc" as "[Hc _]". simpl.
      iPoseProof (lctx_place_update_kind_incl_use with "HE HL") as "#Hincl2"; first apply Hb.
      iPoseProof (pupd_performed_incl_uniq_rt with "Hincl2") as "%Heq".
      destruct upd' as [rt' ? ? ? ? Heq1 ? ]; simpl in *.
      subst rt'.
      iMod ("Hc" with "Hl Hb [] [] Hcond") as "(Hb & ? & Hcond')".
      { done. }
      { done. }
      iFrame. simpl. iFrame.
      done.
    - (* strong *)
      iDestruct "HT" as "(-> & HT)".
      iDestruct "Hc" as "[_ Hc]".
      iMod ("Hc" with "Hl [] Hb") as "Hb".
      { rewrite Hsteq. done. }
      iFrame. simpl. iFrame.
      done.
  Qed.
  Definition typed_place_shr_uniq_inst := [instance @typed_place_shr_uniq].
  Global Existing Instance typed_place_shr_uniq_inst | 30.

  Lemma typed_place_shr_shared {rto} f E L (lt2 : ltype rto) P l r κ κ' bmin0 (T : place_cont_t (place_rfn rto) bmin0) :
    li_tactic (lctx_lft_alive_count_goal E L κ') (λ '(κs, L'),
      introduce_with_hooks E L' (£1) (λ L1,
      (∀ l', typed_place E L1 f l' lt2 r bmin0 (Shared κ) P
        (λ L2 κs' l2 b2 bmin rti tyli ri updcx,
          T L2 κs' l2 b2 bmin rti tyli ri
            (λ L2 upd cont, updcx L2 upd (λ upd',
            cont (mkPUpd _ bmin0
              (place_rfn upd'.(pupd_rt))
              (ShrLtype (upd').(pupd_lt) κ)
              (# (upd').(pupd_rfn))
              ((upd').(pupd_R) ∗ llft_elt_toks κs)
              (upd').(pupd_performed)
              (opt_place_update_eq_lift place_rfnRT (upd').(pupd_eq_1))
              (opt_place_update_eq_lift place_rfnRT (upd').(pupd_eq_2)))
            ))))))
    ⊢ typed_place E L f l (ShrLtype lt2 κ) #r bmin0 (Shared κ') (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    rewrite /lctx_lft_alive_count_goal.
    iIntros "(%κs & %L2 & %Hal & HT)".
    iIntros (Φ F ??). iIntros "#(LFT & LLCTX) #HE HL Hf HP HΦ/=".
    (* get a token *)
    iApply fupd_wpe. iMod (fupd_mask_subseteq lftE) as "HclF"; first done.
    iMod (lctx_lft_alive_count_tok lftE with "HE HL") as (q) "(Hκ' & Hclκ' & HL)"; [done.. | ].
    iMod "HclF" as "_". iMod (fupd_mask_subseteq F) as "HclF"; first done.
    iPoseProof (shr_ltype_acc_shared F with "[$LFT $LLCTX] Hκ' HP") as "(%Hly & Hlb & Hb)"; [done.. | ].
    iMod "Hb" as "(%l' & %q' & Hl & >Hb & Hcl)". iMod "HclF" as "_".
    iModIntro. iApply wpe_fupd.
    iApply (wp_deref with "Hl") => //; [solve_ndisj | by apply val_to_of_loc | ].
    iApply physical_step_intro_lc. iIntros "Hcred !>!>".
    iIntros (st) "Hl". iMod (fupd_mask_mono with "Hb") as "#Hb"; first done.
    iExists l'.
    iSplitR. { iPureIntro. unfold mem_cast. rewrite val_to_of_loc. done. }
    iMod ("HT" with "[] [$] HE HL [Hcred]") as "(%L1 & HL &HT)"; first done.
    { iApply lc_weaken; last done. unfold num_laters_per_step. lia. }
    iApply ("HT" with "[//] [//] [$LFT $LLCTX] HE HL Hf Hb").
    iModIntro. iIntros (L'' κs' l2 bmin b2 rti tyli ri updcx) "Hb' Hs".
    iApply ("HΦ" $! _ _ _ bmin with "Hb'").
    iIntros (upd) "#Hincl Hl2 %Hsteq ? Hcond".
    iMod ("Hs" with "Hincl Hl2 [//] [$] Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hs" with "HL Hf Hcont") as (upd') "(Hl' & %Hsteq2 & Hcond & ? & ? & HL & Hcont)".
    iMod ("Hcl" with "Hl Hl'") as "(Hl & Htok)".
    iMod (fupd_mask_mono with "(Hclκ' Htok)") as "Htoks"; first done.
    iFrame. simpl. iFrame. iR.
    by iApply shr_ltype_place_cond.
  Qed.
  Definition typed_place_shr_shared_inst := [instance @typed_place_shr_shared].
  Global Existing Instance typed_place_shr_shared_inst | 30.

  (** prove_place_cond instances *)
  (* These need to have a lower priority than the ofty_refl instance (level 2) and the unblocking instances (level 5), but higher than the trivial "no" instance *)
  Lemma prove_place_cond_unfold_shr_l E L {rt1 rt2} (ty : type rt1) (lt : ltype rt2) κ k T :
    prove_place_cond E L k (ShrLtype (◁ ty) κ) lt T
    ⊢ prove_place_cond E L k (◁ (shr_ref κ ty)) lt T.
  Proof.
    iApply prove_place_cond_eqltype_l. apply symmetry. apply shr_ref_unfold_full_eqltype; done.
  Qed.
  Definition prove_place_cond_unfold_shr_l_inst := [instance @prove_place_cond_unfold_shr_l].
  Global Existing Instance prove_place_cond_unfold_shr_l_inst | 10.
  Lemma prove_place_cond_unfold_shr_r E L {rt1 rt2} (ty : type rt1) (lt : ltype rt2) κ k T :
    prove_place_cond E L k lt (ShrLtype (◁ ty) κ) T
    ⊢ prove_place_cond E L k lt (◁ (shr_ref κ ty)) T.
  Proof.
    iApply prove_place_cond_eqltype_r. apply symmetry. apply shr_ref_unfold_full_eqltype; done.
  Qed.
  Definition prove_place_cond_unfold_shr_r_inst := [instance @prove_place_cond_unfold_shr_r].
  Global Existing Instance prove_place_cond_unfold_shr_r_inst | 10.

  (* TODO *)
  (*
  Lemma prove_place_cond_ShrLtype E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κ k T :
    prove_place_cond E L (Shared κ ⊓ₖ k) lt1 lt2 (λ upd, T $ access_result_lift place_rfn upd)
    ⊢ prove_place_cond E L k (ShrLtype lt1 κ) (ShrLtype lt2 κ) T.
  Proof.
    (* TODO *)
  Abort.
   *)

End place.
