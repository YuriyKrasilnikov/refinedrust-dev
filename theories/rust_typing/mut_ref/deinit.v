From refinedrust Require Export base type ltypes.
From refinedrust Require Import ltype_rules.
From refinedrust Require Import programs.
From refinedrust.mut_ref Require Import def.
From refinedrust Require Import options.

(** ** Lemmas about deinitializing *)

Section deinit.
  Context `{!typeGS Σ}.

  (* TODO seem to be redundant. Rather use the stronger extractable stuff *)
  Lemma ltype_uniq_deinitializable_deinit_mut F π l st {rt} (lt : ltype rt) r κ γ :
    lftE ⊆ F →
    ltype_uniq_deinitializable lt →
    syn_type_compat PtrSynType st →
    (l ◁ₗ[π, Owned] #(r, γ) @ (MutLtype lt κ)) ={F}=∗
    l ◁ₗ[π, Owned] #() @ (◁ uninit st) ∗ place_rfn_interp_mut r γ.
  Proof.
    iIntros (? Hdeinit Hcompat).
    iIntros "Hl".
    rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & Hlb & %γ' & %r' & %Heq & Hb)".
    injection Heq as <- <-.
    iMod (fupd_mask_mono with "Hb") as "Hc"; first done.
    iDestruct "Hc" as "(%l' & Hl & Hb)".
    iMod (ltype_own_deinit_ghost_drop_uniq with "Hb") as "Hrfn"; [done.. | ].
    iFrame.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own. iExists ly.
    iSplitR. { destruct Hcompat as [<- | (ly1 & Hst' & ->)]; first done.
      simpl. iPureIntro. eapply syn_type_has_layout_make_untyped; last done.
      by eapply syn_type_has_layout_inj. }
    iR. iSplitR. { rewrite /ty_own_val/=//. }
    iSplitL "Hlb"; first by iFrame.
    iExists tt. iR. iModIntro. iExists _. iFrame.
    rewrite uninit_own_spec. iR. iExists ly.
    apply syn_type_has_layout_ptr_inv in Halg as ->. iSplitR; last done.
    iPureIntro. destruct Hcompat as [<- | (ly1 & Hst' & ->)]; first by apply syn_type_has_layout_ptr.
    specialize (syn_type_has_layout_ptr_inv _ Hst') as ->.
    eapply syn_type_has_layout_make_untyped; done.
  Qed.

  (* TODO try to find a good way to unify with previous lemma *)
  Lemma ltype_uniq_deinitializable_deinit_mut' F π l st {rt} (lt : ltype rt) r κ γ :
    lftE ⊆ F →
    ltype_uniq_deinitializable lt →
    syn_type_compat PtrSynType st →
    (l ◁ₗ[π, Owned] #(r, γ) @ (MutLtype lt κ)) ={F}=∗
    l ◁ₗ[π, Owned] #() @ (◁ uninit st) ∗ place_rfn_interp_mut r γ.
  Proof.
    iIntros (? Hdeinit Hcompat).
    iIntros "Hl".
    rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & Hlb & %γ' & %r' & %Heq & Hb)".
    injection Heq as <- <-.
    iMod (fupd_mask_mono with "Hb") as "Hc"; first done.
    iDestruct "Hc" as "(%l' & Hl & Hb)".
    iMod (ltype_own_deinit_ghost_drop_uniq with "Hb") as "Hrfn"; [done.. | ].
    iFrame.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own. iExists ly.
    iSplitR. { destruct Hcompat as [<- | (ly1 & Hst' & ->)]; first done.
      simpl. iPureIntro. eapply syn_type_has_layout_make_untyped; last done.
      by eapply syn_type_has_layout_inj. }
    iR. iSplitR. { rewrite /ty_own_val/=//. }
    iSplitL "Hlb"; first by iFrame.
    iExists tt. iR. iModIntro. iExists _. iFrame.
    rewrite uninit_own_spec. iR. iExists ly.
    apply syn_type_has_layout_ptr_inv in Halg as ->. iSplitR; last done.
    iPureIntro. destruct Hcompat as [<- | (ly1 & Hst' & ->)]; first by apply syn_type_has_layout_ptr.
    specialize (syn_type_has_layout_ptr_inv _ Hst') as ->.
    eapply syn_type_has_layout_make_untyped; done.
  Qed.

  Lemma ltype_uniq_extractable_deinit_mut F π l st {rt} (lt : ltype rt) r κ κm γ :
    lftE ⊆ F →
    ltype_uniq_extractable lt = Some κm →
    syn_type_compat PtrSynType st →
    (l ◁ₗ[π, Owned] #(r, γ) @ (MutLtype lt κ)) ={F}=∗
    l ◁ₗ[π, Owned] #() @ (◁ uninit st) ∗ MaybeInherit κm (place_rfn_interp_mut r γ).
  Proof.
    iIntros (? Hdeinit Hcompat).
    iIntros "Hl".
    rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & Hlb & %γ' & %r' & %Heq & Hb)".
    injection Heq as <- <-.
    iMod (fupd_mask_mono with "Hb") as "Hc"; first done.
    iDestruct "Hc" as "(%l' & Hl & Hb)".
    iMod (ltype_own_extract_ghost_drop_uniq with "Hb") as "Hrfn"; [done.. | ].
    iFrame.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own. iExists ly.
    iSplitR. { destruct Hcompat as [<- | (ly1 & Hst' & ->)]; first done.
      simpl. iPureIntro. eapply syn_type_has_layout_make_untyped; last done.
      by eapply syn_type_has_layout_inj. }
    iR. iSplitR. { rewrite /ty_own_val/=//. }
    iSplitL "Hlb"; first done.
    iExists tt. iR. iModIntro. iExists _. iFrame.
    rewrite uninit_own_spec. iR. iExists ly.
    apply syn_type_has_layout_ptr_inv in Halg as ->. iSplitR; last done.
    iPureIntro. destruct Hcompat as [<- | (ly1 & Hst' & ->)]; first by apply syn_type_has_layout_ptr.
    specialize (syn_type_has_layout_ptr_inv _ Hst') as ->.
    eapply syn_type_has_layout_make_untyped; done.
  Qed.

  (* TODO try to find a good way to unify with previous lemma *)
  Lemma ltype_uniq_extractable_deinit_mut' F π l st {rt} (lt : ltype rt) r κ κm γ :
    lftE ⊆ F →
    ltype_uniq_extractable lt = Some κm →
    syn_type_compat PtrSynType st →
    (l ◁ₗ[π, Owned] #(r, γ) @ (MutLtype lt κ)) ={F}=∗
    l ◁ₗ[π, Owned] #() @ (◁ uninit st) ∗ MaybeInherit κm (place_rfn_interp_mut r γ).
  Proof.
    iIntros (? Hdeinit Hcompat).
    iIntros "Hl".
    rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & Hlb & %γ' & %r' & %Heq & Hb)".
    injection Heq as <- <-.
    iMod (fupd_mask_mono with "Hb") as "Hc"; first done.
    iDestruct "Hc" as "(%l' & Hl & Hb)".
    iMod (ltype_own_extract_ghost_drop_uniq with "Hb") as "Hrfn"; [done.. | ].
    iFrame.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own. iExists ly.
    iSplitR. { destruct Hcompat as [<- | (ly1 & Hst' & ->)]; first done.
      simpl. iPureIntro. eapply syn_type_has_layout_make_untyped; last done.
      by eapply syn_type_has_layout_inj. }
    iR. iSplitR. { rewrite /ty_own_val/=//. }
    iSplitL "Hlb"; first by iFrame.
    iExists tt. iR. iModIntro. iExists _. iFrame.
    rewrite uninit_own_spec. iR. iExists ly.
    apply syn_type_has_layout_ptr_inv in Halg as ->. iSplitR; last done.
    iPureIntro. destruct Hcompat as [<- | (ly1 & Hst' & ->)]; first by apply syn_type_has_layout_ptr.
    specialize (syn_type_has_layout_ptr_inv _ Hst') as ->.
    eapply syn_type_has_layout_make_untyped; done.
  Qed.
End deinit.

Section extract.
  Context `{!typeGS Σ}.

  (* Extract an observation  *)
  Lemma stratify_ltype_extract_ofty_mut π E L {rt} (ty : type rt) r κ γ l (T : stratify_ltype_post_hook_cont_t) :
    T L (place_rfn_interp_mut r γ) _ (◁ uninit PtrSynType)%I (#())
    ⊢ stratify_ltype_post_hook π E L (StratifyExtractOp κ) l (◁ (mut_ref κ ty)) (#(r, γ)) (Owned) T.
  Proof.
    iIntros "HT".
    iIntros (????) "#CTX #HE HL Hl".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists _, _, _, _, _. iFrame.
    iDestruct "Hl" as "(%ly & %Hst & %Hly & Hsc & Hlb & %r' & <- & Hb)".
    iMod (fupd_mask_mono with "Hb") as "Hb"; first done.
    iDestruct "Hb" as "(%v & Hl & Hb)".
    rewrite /ty_own_val/=.
    iDestruct "Hb" as "(% & % & _ & -> & ? & ? & ? & ? & Hb & Hcred' & ?)".
    iFrame.
    iSplitR. { simp_ltypes. done. }
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists _. simpl. iFrame. iR. iR.
    iExists _. iR. iModIntro. iModIntro.
    rewrite uninit_own_spec. iR. iExists _. iR.
    iPureIntro. eapply syn_type_has_layout_ptr_inv in Hst. subst.
    done.
  Qed.
  Definition stratify_ltype_extract_ofty_mut_inst := [instance @stratify_ltype_extract_ofty_mut].
  Global Existing Instance stratify_ltype_extract_ofty_mut_inst | 20.

  (* Extract an observation from the ltype *)
  Lemma stratify_ltype_extract_mutltype π E L {rt} (lt : ltype rt) r κ γ l (T : stratify_ltype_post_hook_cont_t) :
    match ltype_uniq_extractable lt with
    | None =>
        T L True%I _ (MutLtype lt κ) (#(r, γ))
    | Some κm =>
        T L (MaybeInherit κm (place_rfn_interp_mut_extracted r γ)) _ (◁ uninit PtrSynType)%I (#())
    end
    ⊢ stratify_ltype_post_hook π E L (StratifyExtractOp κ) l (MutLtype lt κ) (#(r, γ)) (Owned) T.
  Proof.
    iIntros "HT".
    iIntros (????) "#CTX #HE HL Hl".
    destruct (ltype_uniq_extractable lt) as [ κm | ] eqn:Hextract; first last.
    { iExists L, True%I, _, _, _. iFrame. done. }
    iMod (ltype_uniq_extractable_deinit_mut' with "Hl") as "(Hl & Hrfn)"; [done.. | | ].
    { left. done. }
    iPoseProof (MaybeInherit_update (place_rfn_interp_mut_extracted r γ) with "[] Hrfn") as "Ha".
    { iIntros (?) "Ha". iMod (place_rfn_interp_mut_extract with "Ha") as "?". done. }
    iExists _, _, _, _, _. iFrame.
    iFrame. simp_ltypes. done.
  Qed.
  Definition stratify_ltype_extract_mutltype_inst := [instance @stratify_ltype_extract_mutltype].
  Global Existing Instance stratify_ltype_extract_mutltype_inst.
End extract.

Section rule.
  Context `{!typeGS Σ}.

  Lemma owned_subltype_step_mutltype_uninit π E L {rt} (lt : ltype rt) r γ st κ l T :
    owned_subltype_step π E L l #(r, γ) #() (MutLtype lt κ) (◁ uninit st) T :-
    return match ltype_uniq_extractable lt with
    | None => False
    | Some κm =>
        [{ exhale (⌜syn_type_compat PtrSynType st⌝);
        return T L (MaybeInherit κm (place_rfn_interp_mut_extracted r γ)) }]
    end.
  Proof.
    iIntros "HT".
    iIntros (??) "CTX HE HL Hl". simp_ltypes; simpl.
    destruct (ltype_uniq_extractable lt) eqn:Hextract; last done.
    iDestruct "HT" as "(%Hstcomp & HT)".
    iExists _, _. iFrame.
    iMod (ltype_uniq_extractable_deinit_mut with "Hl") as "(Hl & Hf)"; [done.. | ].
    iPoseProof (MaybeInherit_update (place_rfn_interp_mut_extracted r γ) with "[] Hf") as "Hf".
    { iIntros (?) "Hrfn". iMod (place_rfn_interp_mut_extract with "Hrfn") as "?". done. }
    iModIntro. iSplitL. { iApply logical_step_intro. iFrame. }
    iPureIntro. by apply syn_type_compat_size_eq.
  Qed.
  Definition owned_subltype_step_mutltype_uninit_inst := [instance owned_subltype_step_mutltype_uninit].
  Global Existing Instance owned_subltype_step_mutltype_uninit_inst | 20.
End rule.
