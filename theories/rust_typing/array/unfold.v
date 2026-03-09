From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit_def.
From refinedrust Require Import programs.
From refinedrust.array Require Import def.
From refinedrust Require Import options.

(** ** Unfolding [array_t] into [ArrayLtype]. *)
Section lemmas.
  Context `{!typeGS Σ}.
  (** Learnable *)
  Global Program Instance learn_from_hyp_val_array {rt} (ty : type rt) xs len :
    LearnFromHypVal (array_t len ty) xs :=
    {| learn_from_hyp_val_Q := ⌜length xs = len⌝ |}.
  Next Obligation.
    iIntros (?????????) "Hv".
    iPoseProof (array_t_rfn_length_eq with "Hv") as "%Hlen".
    by iFrame.
  Qed.

  (* TODO: possibly also prove these lemmas for location ownership? *)
End lemmas.

Section split.
  Context `{!typeGS Σ}.

  Lemma array_t_ofty_reshape F l π {rt} (ty : type rt) rs n m k :
    lftE ⊆ F →
    k ≠ 0 →
    n = m * k →
    (l ◁ₗ[π, Owned] #rs @ ◁ array_t n ty)%I ={F}=∗
    l ◁ₗ[π, Owned] #(<#> reshape (replicate k m) rs) @ ◁ array_t k (array_t m ty).
  Proof.
    iIntros (? ? ->) "Hl".
    rewrite ltype_own_ofty_unfold/lty_of_ty_own. simpl.
    iDestruct "Hl" as "(%ly & %Hst & %Hly & Hsc & #Hlb & %rs' & <- & Ha)".
    iMod (fupd_mask_mono with "Ha") as "Ha"; first done.
    iDestruct "Ha" as "(%v & Hl & Hv)".
    iMod (array_t_own_val_reshape with "Hv") as "Hv"; [ | done | ]; first done.
    rewrite ltype_own_ofty_unfold/lty_of_ty_own. simpl.
    apply syn_type_has_layout_array_inv in Hst as (ly' & ? & -> & Hsz).
    rewrite ly_size_mk_array_layout in Hsz.
    iExists (mk_array_layout ly' (m * k)). iSplitR.
    { iPureIntro. eapply syn_type_has_layout_array.
      2: { eapply syn_type_has_layout_array; [done.. | ]. nia. }
      { unfold mk_array_layout, ly_mult; simpl.
        f_equiv. unfold ly_size. lia. }
      { rewrite ly_size_mk_array_layout. lia. } }
    iSplitR. { done. }
    iR. iR.
    iExists _. iR.
    iModIntro. iModIntro. iExists v. iFrame.
  Qed.
  (* TODO: unnesting lemma to reverse this *)

  Lemma ltype_own_array_subtype_strong F l π {rt} (ty : type rt) {rt'} (ty' : type rt') rs n ly' :
    lftE ⊆ F →
    syn_type_size_eq (st_of ty MetaNone) (st_of ty' MetaNone) →
    (* [l] also needs to be well-aligned for the new type *)
    syn_type_has_layout (st_of ty' MetaNone) ly' →
    l `has_layout_loc` ly' →
    (□∀ v r, v ◁ᵥ{π, MetaNone} r @ ty ={F}=∗ ∃ r', v ◁ᵥ{π, MetaNone} r' @ ty') -∗
    (l ◁ₗ[π, Owned] #(<#> rs) @ ◁ array_t n ty) ={F}=∗
    ∃ rs', l ◁ₗ[π, Owned] #(<#> rs') @ ◁ array_t n ty'.
  Proof.
    iIntros (? Hsteq ??) "#Hupd Hl".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Hst & %Hly & Hsc & #Hlb & %r' & <- & Ha)".
    iMod (fupd_mask_mono with "Ha") as "(%v & Hl & Hv)"; first done.
    iMod (ty_own_val_array_subtype_strong with "Hupd Hv") as "(%rs' & Hv)".
    { done. }
    iExists rs'.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own. simpl.
    iExists (mk_array_layout ly' n).
    apply syn_type_has_layout_array_inv in Hst as (ly'' & Hst' & -> & Hsz).
    apply Hsteq in Hst' as (ly2 & Hst2 & Hszeq).
    assert (ly' = ly2) as -> by by eapply syn_type_has_layout_inj.
    rewrite ly_size_mk_array_layout in Hsz.
    iSplitR. { iPureIntro.
      eapply syn_type_has_layout_array; first done; first done.
      lia. }
    iR. iR.
    rewrite !ly_size_mk_array_layout Hszeq.
    iR. iExists _. iR. iModIntro. iModIntro.
    iExists v. iFrame.
  Qed.

  Lemma array_t_ofty_split {rt} (ty : type rt) n rs n1 n2 l π F :
    lftE ⊆ F →
    n = n1 + n2 →
    (l ◁ₗ[π, Owned] #rs @ ◁ array_t n ty) ={F}=∗
    (l ◁ₗ[π, Owned] #(take n1 rs) @ (◁ array_t n1 ty) ∗
     (l offsetst{st_of ty MetaNone}ₗ n1) ◁ₗ[π, Owned] #(drop n1 rs) @ ◁ array_t n2 ty).
  Proof.
    intros ? ->. rewrite !ltype_own_ofty_unfold; simpl.
    iIntros "(%ly & %Hst & %Hly & _ & #Hlb & %r' & <- & Hx)".
    simpl in *.
    iMod (fupd_mask_mono with "Hx") as "Hx"; first done.
    iDestruct "Hx" as "(%v & Hl & Hv)".
    iPoseProof (array_t_rfn_length_eq with "Hv") as "%Hlen".
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    apply syn_type_has_layout_array_inv in Hst as (ly' & Hst & -> & Hsz).

    set (v1 := take (n1 * ly_size ly') v).
    set (v2 := drop (n1 * ly_size ly') v).
    set (rs1 := take n1 rs).
    set (rs2 := drop n1 rs).
    replace v with (v1 ++ v2); last by apply take_drop.
    replace rs with (rs1 ++ rs2); last by apply take_drop.
    rewrite heap_pointsto_app. iDestruct "Hl" as "(Hl1 & Hl2)".
    iPoseProof (array_t_own_val_split with "Hv") as "(Hv1 & Hv2)".
    { subst rs1. rewrite length_take. lia. }
    { subst rs2. rewrite length_drop. lia. }
    { move: Hlyv. subst v1. rewrite length_take.
      rewrite /has_layout_val ly_size_mk_array_layout.
      rewrite /size_of_st.
      erewrite use_layout_alg_eq'; last done.
      lia. }
    { move: Hlyv. subst v2. rewrite length_drop.
      rewrite /has_layout_val ly_size_mk_array_layout.
      rewrite /size_of_st.
      erewrite use_layout_alg_eq'; last done.
      lia. }
    iSplitL "Hl1 Hv1".
    - rewrite /lty_of_ty_own.
      iFrame. iExists (mk_array_layout ly' n1).
      iSplitR. { iPureIntro. eapply syn_type_has_layout_array; try done.
        move: Hsz. rewrite ly_size_mk_array_layout. lia. }
      iR. iL. iApply (loc_in_bounds_offset with "Hlb"); [done.. | ].
      rewrite !ly_size_mk_array_layout. lia.
    - rewrite /lty_of_ty_own.
      iFrame. iExists (mk_array_layout ly' n2).
      iSplitR. { iPureIntro. eapply syn_type_has_layout_array; try done.
        move: Hsz. rewrite ly_size_mk_array_layout. lia. }
      iSplitR. { iPureIntro.
        rewrite /has_layout_loc ly_align_mk_array_layout.
        eapply has_layout_loc_offset_loc'.
        - rewrite /use_layout_alg' Hst//.
        - rewrite /use_layout_alg' Hst//. by eapply use_layout_alg_wf.
        - rewrite /use_layout_alg' Hst//. }
      iSplitR. { iApply (loc_in_bounds_offset with "Hlb"); [ done | | ].
        - rewrite /OffsetLocSt/offset_loc/use_layout_alg' Hst/=. lia.
        - rewrite /OffsetLocSt/offset_loc/use_layout_alg' Hst/=.
          rewrite !ly_size_mk_array_layout. lia. }
      iR. iModIntro. iModIntro.
      rewrite /OffsetLocSt. erewrite use_layout_alg_eq'; last done.
      unfold offset_loc. enough (Z.of_nat $ length v1 = (ly_size ly' * n1)%Z) as -> by done.
      subst v1. rewrite length_take.
      rewrite Hlyv. rewrite ly_size_mk_array_layout. lia.
  Qed.

  Lemma array_t_ofty_split_reshape {rt} (ty : type rt) F π n num size l rs :
    lftE ⊆ F →
    n = num * size →
    (l ◁ₗ[π, Owned] #rs @ ◁ array_t n ty) ={F}=∗
    [∗ list] i ↦ v ∈ (reshape (replicate num size) rs),
    (l offsetst{st_of ty MetaNone}ₗ (i * size)) ◁ₗ[π, Owned] #v @ (◁ array_t size ty).
  Proof.
    intros ? ->.
    rewrite !ltype_own_ofty_unfold; simpl.
    iIntros "(%ly & %Hst & %Hly & _ & #Hlb & %r' & <- & Hx)".
    simpl in *.
    iMod (fupd_mask_mono with "Hx") as "Hx"; first done.
    iDestruct "Hx" as "(%v & Hl & Hv)".
    iPoseProof (array_t_rfn_length_eq with "Hv") as "%Hlen".
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    apply syn_type_has_layout_array_inv in Hst as (ly' & Hst & -> & Hsz).
    iPoseProof (array_t_own_val_split_reshape _ _ _ _ _ num size with "Hv") as "(%Heq & Hv)"; [done.. | ].
    rewrite -{1}Heq.
    iPoseProof (heap_pointsto_mjoin_uniform _ _ (ly_size ly' * size) with "Hl") as "(Hlb' & Hl)".
    { intros v'. intros Hlen'%reshape_replicate_elem_length; first done.
      rewrite Hlyv. rewrite ly_size_mk_array_layout. lia. }
    iPoseProof (big_sepL2_length with "Hv") as "%Hlen_eq".
    iPoseProof (big_sepL_extend_r with "Hl") as "Hl"; first done.
    iPoseProof (big_sepL2_sep with "[$Hv $Hl]") as "Ha".
    iApply big_sepL2_elim_l.
    iApply (big_sepL2_wand with "Ha"). iApply big_sepL2_intro. { done. }
    iModIntro. iModIntro.
    iIntros (? ? ? Hlook1 Hlook2) "(Hv & Hl)".
    rewrite !ltype_own_ofty_unfold; simpl.
    iExists (mk_array_layout ly' size).
    assert (num > 0).
    { destruct num; last lia. simpl in *. naive_solver. }
    iSplitR. { iPureIntro. eapply syn_type_has_layout_array; [done.. | ].
      move: Hsz. rewrite ly_size_mk_array_layout. nia. }
    simpl.
    iSplitR. { iPureIntro.
      rewrite /has_layout_loc ly_align_mk_array_layout.
      rewrite /has_layout_loc ly_align_mk_array_layout in Hly.
      eapply has_layout_loc_offset_loc'.
      - rewrite /use_layout_alg' Hst//.
      - rewrite /use_layout_alg' Hst//. by eapply use_layout_alg_wf.
      - rewrite /use_layout_alg' Hst//. }
    iR. iSplitR.
    { iApply (loc_in_bounds_offset with "Hlb").
      - done.
      - simpl. lia.
      - rewrite /OffsetLocSt/offset_loc/use_layout_alg' Hst/=.
        rewrite !ly_size_mk_array_layout.
        apply lookup_lt_Some in Hlook2.
        move: Hlook2. rewrite length_reshape length_replicate.
        nia. }
    iExists _. iR. iModIntro.
    iExists _. iFrame.
    rewrite /OffsetLocSt /use_layout_alg' Hst/=.
    rewrite /offset_loc.
    assert ((ly_size ly' * (k * size))%Z = ((ly_size ly' * size)%nat * k)%Z) as -> by lia.
    done.
  Qed.

  Local Lemma ofty_owned_array_extract_pointsto π F {rt} (ty : type rt) ly len l rs :
    lftE ⊆ F →
    length rs = len →
    syn_type_has_layout (ty.(ty_syn_type) MetaNone) ly →
    loc_in_bounds l 0 0 -∗
    ([∗ list] k ↦ r ∈ rs, (l offset{ly}ₗ k) ◁ₗ[ π, Owned] r @ (◁ ty)) -∗
    |={F}=> ∃ v, l ↦ v ∗
      ⌜v `has_layout_val` mk_array_layout ly len⌝ ∗
      [∗ list] k ↦ r; v' ∈ rs; reshape (replicate len (ly_size ly)) v, array_own_el_val π ty r v'.
  Proof.
    iIntros (? ? ?) "Hlb Hown".
    setoid_rewrite ltype_own_ofty_unfold. rewrite /lty_of_ty_own.
    simpl. iEval (rewrite /ty_own_val/=).
    iPoseProof (array_own_val_extract_pointsto_fupd with "Hlb [Hown]") as "Ha"; [done.. | | ].
    { iApply (big_sepL_wand with "Hown").
      iApply big_sepL_intro. iModIntro. iIntros (k r Hlook).
      rewrite /array_own_el_loc.
      iIntros "(%ly' & %Hst & %Hly & Hsc & Hlb & %r' & Hrfn & Ha)".
      iMod "Ha" as "(%v & ? & ?)".
      iModIntro. iExists _. eauto with iFrame. }
    iApply (fupd_mask_mono with "Ha"); done.
  Qed.

  Local Lemma ofty_owned_array_join_pointsto π {rt} (ty : type rt) ly len l rs v :
    length rs = len →
    v `has_layout_val` mk_array_layout ly len →
    syn_type_has_layout (ty.(ty_syn_type) MetaNone) ly →
    l `has_layout_loc` ly →
    l ↦ v -∗
    ([∗ list] k ↦ r; v' ∈ rs; reshape (replicate len (ly_size ly)) v, array_own_el_val π ty r v') -∗
    ([∗ list] k ↦ r ∈ rs, (l offset{ly}ₗ k) ◁ₗ[ π, Owned] r @ (◁ ty)).
  Proof.
    iIntros (? ? ? ?) "Hl Ha".
    iPoseProof (array_own_val_join_pointsto with "Hl Ha") as "Ha"; [done.. | ].
    iApply (big_sepL_wand with "Ha").
    iApply big_sepL_intro. iModIntro.
    rewrite /array_own_el_loc.
    iIntros (k r ?) "(%v' & %r' & Hl & Hrfn & Hv)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists _. iR.
    iSplitR. { iPureIntro. apply has_layout_loc_offset_loc; last done. by eapply use_layout_alg_wf. }
    iPoseProof (ty_own_val_sidecond with "Hv") as "#$".
    iPoseProof (heap_pointsto_loc_in_bounds with "Hl") as "#Hlb".
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hv"; first done.
    rewrite Hv. iR. iExists _. by iFrame.
  Qed.

  Lemma array_t_ofty_merge {rt} (ty : type rt) π F (size : nat) (rs : list (list (place_rfn rt))) l :
    lftE ⊆ F →
    length rs > 0 →
    (size_of_st (st_of ty MetaNone) * size * length rs ≤ MaxInt ISize)%Z →
    ([∗ list] i↦v ∈ rs, (l offsetst{st_of ty MetaNone}ₗ (i * size)) ◁ₗ[ π, Owned] # v @ (◁ array_t size ty)) ={F}=∗
    l ◁ₗ[ π, Owned] # (mjoin (M:=list) rs) @ (◁ array_t (length rs * size) ty).
  Proof.
    iIntros (? Hnz Hbound) "Hv".
    setoid_rewrite ltype_own_ofty_unfold; simpl.
    rewrite /lty_of_ty_own/=.
    iPoseProof (big_sepL_exists with "Hv") as "(%lys & Hv)".

    iPoseProof (big_sepL2_sep with "Hv") as "(Hsts & Hv)".
    iPoseProof (big_sepL2_length with "Hsts") as "%Hlen".
    iPoseProof (big_sepL2_elim_l with "Hsts") as "Hsts".
    iPoseProof (big_sepL_Forall with "Hsts") as "%Hsts".
    iClear "Hsts".
    destruct lys as [ | ly lys]; first (simpl in *; lia).
    apply Forall_cons in Hsts as [Hst Hsts].
    assert (lys = replicate (length lys) ly) as ->.
    { clear Hlen. induction lys as [ | ly' lys IH]; simpl; first done.
      apply Forall_cons in Hsts as [Hly' Hsts].
      assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
      f_equiv. by apply IH. }
    rewrite (big_sepL2_replicate_r _ _ _ (S _)); last done.
    clear lys Hlen Hsts.


    iPoseProof (big_sepL_sep with "Hv") as "(Hlyl & Hv)".
    iAssert (⌜l `has_layout_loc` ly⌝)%I with "[Hlyl]" as "%Hlyl".
    { destruct rs; first (simpl in *; lia).
      simpl. iDestruct "Hlyl" as "(%Hlyl & _)". iPureIntro.
      move: Hlyl. rewrite /OffsetLocSt /offset_loc/=.
      rewrite Z.mul_0_l Z.mul_0_r.
      rewrite shift_loc_0. done. }
    iClear "Hlyl".

    opose proof * syn_type_has_layout_array_inv as (ly' & Hst' & Heq & ?); first done.
    subst ly.

    iPoseProof (big_sepL_sep with "Hv") as "(_ & Hv)".
    iPoseProof (big_sepL_sep with "Hv") as "(Hlb & Hv)".
    iAssert (loc_in_bounds l 0 0) with "[Hlb]" as "Hlb".
    { destruct rs; simpl in *; first lia.
      iDestruct "Hlb" as "(Hlb & _)".
      iApply (loc_in_bounds_offset with "Hlb"); simpl; try done; lia. }
    iAssert ([∗ list] i↦r ∈ <#> rs, |={lftE}=> ∃ v : val, array_own_el_loc π 1 v i (mk_array_layout ly' size) (array_t size ty) (r) l)%I with "[Hv]" as "Hv".
    { rewrite big_sepL_fmap. iApply (big_sepL_impl with "Hv").
      iModIntro. iIntros (???) "(% & -> & >(%v & Hl & Hb))".
      iModIntro. iFrame. iL.
      rewrite /OffsetLocSt.
      rewrite /use_layout_alg' Hst'/=.
      rewrite /offset_loc. rewrite ly_size_mk_array_layout.
      eassert (((_ * _)%nat * _) = _)%Z as ->; last done.
      lia. }
    iPoseProof (big_sepL_fupd with "Hv") as "Hv".
    iMod (fupd_mask_mono with "Hv") as "Hv"; first done.
    iPoseProof (array_own_val_extract_pointsto with "Hlb Hv") as "(%vs & Hl & %Hlyv & Hv)".
    { rewrite length_fmap. done. }
    { simpl. done. }
    rewrite ly_size_mk_array_layout.

    move: Hbound. rewrite /size_of_st /use_layout_alg' Hst'/= => Hbound.

    rewrite big_sepL2_flip.
    iPoseProof (array_t_own_val_merge_reshape ty with "[Hv]") as "Hv".
    5: { rewrite big_sepL2_fmap_r. iApply (big_sepL2_impl with "Hv").
      iModIntro. iIntros (?????) "(%r' & -> & Hv)". done. }
    { reflexivity. }
    { done. }
    { rewrite Hlyv. rewrite !ly_size_mk_array_layout. simpl. lia. }
    { rewrite Hlyv. rewrite !ly_size_mk_array_layout. simpl. lia. }

    iModIntro. iExists _.
    iSplitR. { iPureIntro. eapply syn_type_has_layout_array; try done; lia. }
    iSplitR. { iPureIntro. rewrite /has_layout_loc. rewrite ly_align_mk_array_layout. done. }
    iR. iPoseProof (heap_pointsto_loc_in_bounds with "Hl") as "#Hlb".
    iSplitR. { iApply loc_in_bounds_shorten_suf; last done.
      rewrite Hlyv !ly_size_mk_array_layout. lia. }
    iExists _. iR. by iFrame.
  Qed.
End split.

Section unfold.
  Context `{!typeGS Σ}.

  Lemma array_t_unfold_1_owned {rt} (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' (Owned) rs rs (ArrayLtype ty len []) (◁ (array_t len ty)).
  Proof.
    iModIntro. iIntros (π l) "Hl".
    rewrite ltype_own_array_unfold /array_ltype_own/=.
    iDestruct "Hl" as "(%ly & %Hst & %Hsz & % & #Hlb & %r' & Hrfn & Hb)".
    iModIntro. rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists (mk_array_layout ly len). iFrame "% ∗".
    simpl. iSplitR. { iPureIntro. eapply syn_type_has_layout_array; done. }
    iR. iMod "Hb" as "(%Hlen & Hb)".
    rewrite big_sepL2_replicate_l; last done.
    iMod (ofty_owned_array_extract_pointsto with "[Hlb] [Hb]") as "(%v & Hl & % & Ha)"; [done.. | | | ].
    { iApply (loc_in_bounds_shorten_suf with "Hlb"). lia. }
    { iApply (big_sepL_impl with "Hb"). iModIntro. iIntros (k r Hlook). iIntros "(_ & $)". }
    iModIntro. iExists v. iFrame.
    iR. done.
  Qed.

  Lemma array_t_unfold_1_shared {rt} κ (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' (Shared κ) rs rs (ArrayLtype ty len []) (◁ (array_t len ty)).
  Proof.
    iModIntro. iIntros (π l) "Hl".
    rewrite ltype_own_array_unfold /array_ltype_own/=.
    iDestruct "Hl" as "(%ly & %Hst & %Hsz & % & #Hlb & %r' & Hrfn & #Hb)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists (mk_array_layout ly len). simpl.
    iSplitR. { iPureIntro. eapply syn_type_has_layout_array; done. }
    iR. iR. iR. iExists _. iFrame.
    iModIntro. iMod "Hb" as "(%Hlen & Hb)".
    rewrite big_sepL2_replicate_l; last done.
    rewrite /ty_shr/=.
    iExists ly. iR. iR. iR. iR. iR.
    iApply big_sepL_fupd.
    iApply (big_sepL_impl with "Hb").
    iModIntro. iIntros (k r'' Hlook) "(_ & Hl)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly' & %Hst' & %Hloc & Hst & Hlb' & %r2 & Hrfn & #>Ha)".
    iModIntro. rewrite /array_own_el_shr. eauto with iFrame.
  Qed.

  Lemma array_t_unfold_1_uniq {rt} κ γ (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' (Uniq κ γ) rs rs (ArrayLtype ty len []) (◁ (array_t len ty)).
  Proof.
    iModIntro. iIntros (π l) "Hl".
    rewrite ltype_own_array_unfold /array_ltype_own/=.
    iDestruct "Hl" as "(%ly & %Hst & %Hsz & % & #Hlb & Hcreds & Hrfn & Hb)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists (mk_array_layout ly len). iFrame "% ∗".
    simpl. iSplitR. { iPureIntro. eapply syn_type_has_layout_array; done. }
    iR. iMod "Hb".
    (* TODO refactor *)
    set (R := (∃ r', gvar_auth γ r' ∗ (|={lftE}=> ⌜length r' = len⌝ ∗ [∗ list] i↦r'' ∈ r', (l offset{ly}ₗ i) ◁ₗ[ π, Owned] r'' @ ◁ ty))%I).
    iPoseProof (pinned_bor_iff _ _ R _ R with "[] [] Hb") as "Hb".
    { subst R. iNext. iModIntro. iSplit.
      + iIntros "(%r'' & Hauth & Ha)".
        iExists _. iFrame. iMod "Ha" as "(% & Ha)". iR.
        rewrite big_sepL2_replicate_l; last done.
        iApply (big_sepL_impl with "Ha").
        iModIntro. iModIntro. iIntros (k r Hlook). iIntros "(_ & $)".
      + iIntros "(%r'' & Hauth & Ha)".
        iExists _. iFrame. iMod "Ha" as "(% & Ha)". iR.
        rewrite big_sepL2_replicate_l; last done.
        iApply (big_sepL_impl with "Ha").
        iModIntro. iModIntro. iIntros (k r Hlook). iIntros "$".
        simp_ltypes. done.
    }
    { subst R. iNext. iModIntro. iSplit.
      + iIntros "(%r'' & Hauth & Ha)".
        iExists _. iFrame. iMod "Ha" as "(% & Ha)". iR.
        rewrite big_sepL2_replicate_l; last done.
        iApply (big_sepL_impl with "Ha").
        iModIntro. iModIntro. iIntros (k r Hlook).
        rewrite ltype_own_core_equiv ltype_core_ofty. iIntros "(_ & $)".
      + iIntros "(%r'' & Hauth & Ha)".
        iExists _. iFrame. iMod "Ha" as "(% & Ha)". iR.
        rewrite big_sepL2_replicate_l; last done.
        iApply (big_sepL_impl with "Ha").
        iModIntro. iModIntro. iIntros (k r Hlook).
        rewrite ltype_own_core_equiv ltype_core_ofty.
        iIntros "$". simp_ltypes. done.
    }
    iApply (pinned_bor_iff' with "[] Hb").
    iModIntro. iModIntro.
    iSplit.
    { iIntros "(%rs' & Hauth & Ha)".
      iExists _. iFrame. iMod "Ha" as "(%Hlen & Ha)".
      iMod (ofty_owned_array_extract_pointsto with "[Hlb] Ha") as "(%v & Hl & % & Ha)"; [done.. | | ].
      { iApply (loc_in_bounds_shorten_suf with "Hlb"); lia. }
      iModIntro. iExists v. iFrame.
      iR. done.
    }
    { iIntros "(%rs' & Hauth & Ha)".
      iExists _. iFrame.
      iMod "Ha" as "(%v & Hl & Hv)".
      rewrite /ty_own_val/=.
      iDestruct "Hv" as "(%ly' & _ & %Hst' & _ & %Hlen & %Hvly & Ha)".
      assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
      iR. iApply (ofty_owned_array_join_pointsto with "Hl Ha"); done.
    }
  Qed.

  Local Lemma array_t_unfold_1' {rt} k (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' k rs rs (ArrayLtype ty len []) (◁ (array_t len ty)).
  Proof.
    destruct k.
    - by apply array_t_unfold_1_owned.
    - by apply array_t_unfold_1_shared.
    - by apply array_t_unfold_1_uniq.
  Qed.

  Lemma array_t_unfold_1 {rt} k (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl k rs rs (ArrayLtype ty len []) (◁ (array_t len ty)).
  Proof.
    iModIntro.
    iSplitR. { simp_ltypes. rewrite {2}/ty_syn_type /array_t //. }
    iSplitR.
    - by iApply array_t_unfold_1'.
    - simp_ltypes. by iApply array_t_unfold_1'.
  Qed.

  Lemma array_t_unfold_2_owned {rt} (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' (Owned) rs rs (◁ (array_t len ty)) (ArrayLtype ty len []).
  Proof.
    iModIntro. iIntros (π l) "Hl".
    rewrite ltype_own_array_unfold /array_ltype_own/=.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own/=.
    iDestruct "Hl" as "(%ly & %Hst & %Hl & _ & Hlb & %rs' & Hrfn & Ha)".
    apply syn_type_has_layout_array_inv in Hst as (ly' & Hst & -> & Hsz).
    iModIntro. iExists _. iR.
    iSplitR. { iPureIntro. move: Hsz. rewrite ly_size_mk_array_layout MaxInt_eq. lia. }
    iR. rewrite ly_size_mk_array_layout. iFrame.
    iMod "Ha" as "(%v & Hl & Hv)".
    rewrite /ty_own_val /=.
    iDestruct "Hv" as "(%ly & _ & %Hst' & % & %Hlen & %Hvly & Ha)".
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    iR.
    rewrite big_sepL2_replicate_l; last done.
    iPoseProof (ofty_owned_array_join_pointsto with "Hl Ha") as "Ha"; [done.. | ].
    iApply (big_sepL_wand with "Ha"). iApply big_sepL_intro.
    iModIntro. iModIntro. iIntros (k r Hlook) "$".
    simp_ltypes. done.
  Qed.

  Lemma array_t_unfold_2_shared {rt} κ (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' (Shared κ) rs rs (◁ (array_t len ty)) (ArrayLtype ty len []).
  Proof.
    iModIntro. iIntros (π l) "Hl".
    rewrite ltype_own_array_unfold /array_ltype_own/=.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Hst & % & Hsc & #Hlb & %r' & Hrfn & #Hb)".
    apply syn_type_has_layout_array_inv in Hst as (ly' & Hst & -> & Hsz).
    iExists ly'. iR.
    iSplitR. { iPureIntro. move: Hsz. rewrite ly_size_mk_array_layout MaxInt_eq. lia. }
    iR. rewrite ly_size_mk_array_layout. iR.
    iExists _. iFrame.
    iModIntro. iMod "Hb" as "Hb". iModIntro.
    rewrite /ty_shr/=.
    iDestruct "Hb" as "(%ly & _ & %Hst' & % & % & % & Hb)".
    iR.
    rewrite big_sepL2_replicate_l; last done.
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    iApply (big_sepL_wand with "Hb"). iApply big_sepL_intro.
    iModIntro. iIntros (k r'' Hlook) "Hl".
    simp_ltypes. iR.
    rewrite /array_own_el_shr.
    iDestruct "Hl" as "(%r1 & ? & #Hl)".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists _. iR.
    iSplitR. { iPureIntro. apply has_layout_loc_offset_loc; last done. by eapply use_layout_alg_wf. }
    iPoseProof (ty_shr_sidecond with "Hl") as "#Hsc".
    iR. iSplitR. { iApply loc_in_bounds_array_offset; last done. apply lookup_lt_Some in Hlook.
      simpl in *. lia. }
    iExists _. iFrame. eauto.
  Qed.

  Lemma array_t_unfold_2_uniq {rt} κ γ (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' (Uniq κ γ) rs rs (◁ (array_t len ty)) (ArrayLtype ty len []).
  Proof.
    iModIntro. iIntros (π l) "Hl".
    rewrite ltype_own_array_unfold /array_ltype_own/=.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Hst & % & % & #Hlb & Hcreds & Hrfn & Hb)".
    apply syn_type_has_layout_array_inv in Hst as (ly' & Hst & -> & Hsz).
    iExists ly'. iFrame "% ∗".
    rewrite ly_size_mk_array_layout in Hsz.
    iSplitR. { iPureIntro. lia. }
    iR. iMod "Hb".
    set (R := (∃ r', gvar_auth γ r' ∗ (|={lftE}=> ⌜length r' = len⌝ ∗ [∗ list] i↦r'' ∈ r', (l offset{ly'}ₗ i) ◁ₗ[ π, Owned] r'' @ ◁ ty))%I).
    iApply (pinned_bor_iff _ R _ R with "[] []").
    { subst R. iNext. iModIntro. iSplit.
      + iIntros "(%r'' & Hauth & Ha)".
        iExists _. iFrame. iMod "Ha" as "(% & Ha)". iR.
        rewrite big_sepL2_replicate_l; last done.
        iApply (big_sepL_impl with "Ha").
        iModIntro. iModIntro. iIntros (k r Hlook). iIntros "$".
        simp_ltypes. done.
      + iIntros "(%r'' & Hauth & Ha)".
        iExists _. iFrame. iMod "Ha" as "(% & Ha)". iR.
        rewrite big_sepL2_replicate_l; last done.
        iApply (big_sepL_impl with "Ha").
        iModIntro. iModIntro. iIntros (k r Hlook). iIntros "(_ & $)".
    }
    { subst R. iNext. iModIntro. iSplit.
      + iIntros "(%r'' & Hauth & Ha)".
        iExists _. iFrame. iMod "Ha" as "(% & Ha)". iR.
        rewrite big_sepL2_replicate_l; last done.
        iApply (big_sepL_impl with "Ha").
        iModIntro. iModIntro. iIntros (k r Hlook).
        rewrite ltype_own_core_equiv ltype_core_ofty.
        iIntros "$". simp_ltypes. done.
      + iIntros "(%r'' & Hauth & Ha)".
        iExists _. iFrame. iMod "Ha" as "(% & Ha)". iR.
        rewrite big_sepL2_replicate_l; last done.
        iApply (big_sepL_impl with "Ha").
        iModIntro. iModIntro. iIntros (k r Hlook).
        rewrite ltype_own_core_equiv ltype_core_ofty. iIntros "(_ & $)".
    }
    iApply (pinned_bor_iff' with "[] Hb").
    iModIntro. iModIntro.
    iSplit.
    { iIntros "(%rs' & Hauth & Ha)".
      iExists _. iFrame.
      iMod "Ha" as "(%v & Hl & Hv)".
      rewrite /ty_own_val/=.
      iDestruct "Hv" as "(%ly'' & _ & %Hst' & _ & %Hlen & %Hvly & Ha)".
      assert (ly'' = ly') as -> by by eapply syn_type_has_layout_inj.
      iR. iApply (ofty_owned_array_join_pointsto with "Hl Ha"); done.
    }
    { iIntros "(%rs' & Hauth & Ha)".
      iExists _. iFrame. iMod "Ha" as "(%Hlen & Ha)".
      iMod (ofty_owned_array_extract_pointsto with "[Hlb] Ha") as "(%v & Hl & % & Ha)"; [done.. | | ].
      { iApply (loc_in_bounds_shorten_suf with "Hlb"); lia. }
      iModIntro. iExists v. iFrame.
      do 2 iR. iSplitR. { iPureIntro. lia. } iR. done.
    }
  Qed.

  Local Lemma array_t_unfold_2' {rt} k (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl' k rs rs (◁ (array_t len ty)) (ArrayLtype ty len []).
  Proof.
    destruct k.
    - by apply array_t_unfold_2_owned.
    - by apply array_t_unfold_2_shared.
    - by apply array_t_unfold_2_uniq.
  Qed.

  Lemma array_t_unfold_2 {rt} k (ty : type rt) (len : nat) rs :
    ⊢ ltype_incl k rs rs (◁ (array_t len ty)) (ArrayLtype ty len []).
  Proof.
    iModIntro.
    iSplitR. { simp_ltypes. rewrite {2}/ty_syn_type /array_t //. }
    iSplitR.
    - by iApply array_t_unfold_2'.
    - simp_ltypes. by iApply array_t_unfold_2'.
  Qed.

  Lemma array_t_unfold {rt} k (ty : type rt) (len : nat) rs:
    ⊢ ltype_eq k rs rs (◁ (array_t len ty)) (ArrayLtype ty len []).
  Proof.
    iSplit.
    - by iApply array_t_unfold_2.
    - by iApply array_t_unfold_1.
  Qed.

  Lemma array_t_unfold_full_eqltype E L {rt} (ty : type rt) (len : nat) :
    full_eqltype E L (◁ (array_t len ty))%I (ArrayLtype ty len []).
  Proof.
    iIntros (?) "HL CTX HE". iIntros (??). iApply array_t_unfold.
  Qed.
End unfold.

Section place.
  Context `{!typeGS Σ}.

  Lemma typed_place_array_unfold E L f l {rt} (def : type rt) len rs bmin k P T :
    typed_place E L f l (ArrayLtype def len []) rs bmin k P T
    ⊢ typed_place E L f l (◁ array_t len def) rs bmin k P T.
  Proof.
    iIntros "HT". iApply typed_place_eqltype; last done.
    apply array_t_unfold_full_eqltype.
  Qed.
  Definition typed_place_array_unfold_inst := [instance @typed_place_array_unfold].
  Global Existing Instance typed_place_array_unfold_inst | 20.
End place.
