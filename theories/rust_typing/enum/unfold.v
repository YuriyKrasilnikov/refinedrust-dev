From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules.
From refinedrust Require Import programs struct.def struct.subtype.
From refinedrust.enum Require Import def.
From refinedrust Require Import options.

Section unfold.
  Context `{!typeGS Σ}.

  (* NOTE: we can only do this unfolding for PlaceIn -- because the variant we unfold to depends on that.
     I think this should not be a problem.
  *)

  (* TODO move *)
  Lemma ty_own_val_active_union_split π {rt} (ty : type rt) r v uls variant m :
    v ◁ᵥ{π, m} r @ active_union_t ty variant uls -∗
    ∃ ul ly v1 v2, ⌜v = v1 ++ v2⌝ ∗
      ⌜union_layout_spec_has_layout uls ul⌝ ∗
      ⌜syn_type_has_layout (ty_syn_type ty m) ly⌝ ∗
      v1 ◁ᵥ{π, m} r @ ty ∗ v2 ◁ᵥ{π, m} () @ uninit (UntypedSynType (active_union_rest_ly ul ly)).
  Proof.
    iIntros "Hv".
    rewrite {1}/ty_own_val/=.
    iDestruct "Hv" as "(%ul & %ly & -> & %Hul' & %Hly & %Hst' & Hv1 & Hv2)".
    iExists ul, ly.
    iExists (take (ly_size ly) v), (drop (ly_size ly) v).
    rewrite take_drop. iR. iR. iR. iFrame.
  Qed.
  Lemma ty_own_val_active_union_split' π {rt} (ty : type rt) r v uls ul ly variant m :
    union_layout_spec_has_layout uls ul →
    syn_type_has_layout (ty_syn_type ty m) ly →
    v ◁ᵥ{π, m} r @ active_union_t ty variant uls -∗
    ∃ v1 v2, ⌜v = v1 ++ v2⌝ ∗
      v1 ◁ᵥ{π, m} r @ ty ∗ v2 ◁ᵥ{π, m} () @ uninit (UntypedSynType (active_union_rest_ly ul ly)).
  Proof.
    iIntros (Hul Hst) "Hv".
    rewrite {1}/ty_own_val/=.
    iDestruct "Hv" as "(%ul' & %ly' & -> & %Hul' & %Hly & %Hst' & Hv1 & Hv2)".
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
    assert (ul' = ul) as -> by by eapply union_layout_spec_has_layout_inj.
    iExists (take (ly_size ly) v), (drop (ly_size ly) v).
    rewrite take_drop. iR. iFrame.
  Qed.

  (*
  Lemma enum_unfold_1_owned {rt : Type} (en : enum rt) wl r :
    ⊢ ltype_incl' (Owned wl) (#r) (#r) (◁ (enum_t en))%I
      (EnumLtype en (enum_tag' en r) (◁ enum_tag_type' en (enum_tag' en r)) (enum_rfn).
  Proof.
    iModIntro. iIntros (π l) "Hl".
    rewrite ltype_own_ofty_unfold/lty_of_ty_own.
    iDestruct "Hl" as (ly) "(%Hst & %Hly & Hsc & #Hlb & Hcreds & %r' & -> & Ha)".
    rewrite ltype_own_enum_unfold/enum_ltype_own.
    simpl.
    iModIntro.
    destruct (syn_type_has_layout_enum_inv _ _ _ _ _ Hst) as (el & ul & variant_lys & Hul & Hel & -> & Hvariants).
    iExists el.
    iSplitR. { iPureIntro. eapply use_enum_layout_alg_Some; eauto. }
    iR. iFrame "# ∗".
    (*iSplitR. { rewrite enum_tag_ty_Some; done. }*)
    iExists r'. iR.
    iNext. iMod "Ha" as "(%v & Hl & Hv)".
    rewrite /ty_own_val/=.
    iDestruct "Hv" as "(%ly & %tag & Hv)".
    iModIntro.
    (* split up the struct ownership *)
    rewrite /ty_own_val/=.
    iDestruct "Hv" as "(%Hly' & %Htag & %sl & %Halg' & _ & %Hvly & Hv)".

    assert (sl = el) as ->. { admit. }
    assert (ly = el) as ->. { admit. }

    (*assert (syn_type_has_layout (ty_syn_type (enum_tag_type en (enum_tag en r'))) ly0).*)

    (*rewrite heap_pointsto_reshape_sl; last done. iDestruct "Hl" as "(_ & Hl)".*)
    iPoseProof (struct_own_val_join_pointsto with "Hl Hv") as "Hl".
    { done. }
    { done. }
    { done. }
    iPoseProof (pad_struct_focus with "Hl") as "(Hinit & Hpad)".
    { admit. }
    { specialize (sl_nodup el). apply bool_decide_spec. }
    simpl.
    iDestruct "Hinit" as "(Htag & Hdata & _)".
    rewrite /enum_tag' Htag.
    iExists (enum_variant_rt_tag_rt_eq _ _ _ Htag). iR.
    simpl. iSplitR. { edestruct (enum_tag_compat) as (einj & ->); done. }
    iSplitL "Htag".
    { iExists _. iSplitR. { iPureIntro.
      apply syn_type_has_layout_int; first done.
      rewrite MaxInt_eq. apply IntType_to_it_size_bounded. }
      iSplitR. { iPureIntro.
        rewrite /GetMemberLocSt /use_struct_layout_alg' Halg'/=.
        rewrite /offset_of.
        (*erewrite sl_index_of_lookup_2. done.*)
        admit. }
      iSplitR. { admit. }
      iR.
      iDestruct "Htag" as "(%j & %ly' & %n & % & % & %v' & %r'' & %ly'' & <- & % & % & ? & Hl & %Hlyv & Hv)".
      iExists _. iR. iModIntro.
      iExists v'. iFrame.
      rewrite /ty_own_val/=. iFrame.
      admit. }

    iDestruct "Hdata" as "(%j & %ly' & %n & %Hsl & %Hnamed & %v' & Hl)".
    iDestruct "Hl" as "(%r'' & %ly'' & <- & %Hsl' & %Hst' & ? & Hl & %Hlyv & Hv)".
    rewrite Hsl in Hsl'; simpl in Hsl'. injection Hsl' as <-.
    assert (ly' = ul) as ->. { admit. }
    simpl in *.


    iPoseProof (ty_own_val_active_union_split with "Hv") as "(%ul' & %ly & %v1 & %v2 & -> & %Huls & %Hty & Hv1 & Hv2)".
    assert (ul' = ul) as ->. { admit. }
    rewrite heap_pointsto_app. iDestruct "Hl" as "(Hl1 & Hl2)".
    iSplitL "Hl1 Hv1".
    { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly.
      iSplitR. { admit. }
      iSplitR. { admit. }
      iPoseProof (ty_own_val_sidecond with "Hv1") as "#Hsc".
      iSplitR. {
        erewrite enum_tag_type_variant_type_eq.
        (*generalize ((enum_tag_rt_variant_rt_eq _ _ (enum_tag en r') eq_refl)) as Heq.*)
        (*rewrite /enum_variant_type /enum_tag_rt/enum_tag_ty' /enum_variant_rt. simpl.*)
        admit.
        (*intros <-. done. *)
      }
      iSplitR. { admit. }
      iR.
      admit.
    }
    iSplitL "Hl2 Hv2".
    { simp_ltype. iExists v2.
      iPoseProof (ty_has_layout with "Hv2") as "(%lyu & %Hstlyu & %Hvlyu)".
      iSplitL. { admit. }
      iPureIntro.
      rewrite /has_layout_val Hvlyu.
      apply syn_type_has_layout_untyped_inv in Hstlyu as (-> & _).
      rewrite ly_size_active_union_rest_ly ly_size_ly_offset.
      rewrite /els_data_ly/use_union_layout_alg' Huls/=.
      rewrite /size_of_st /use_layout_alg'.
      erewrite enum_tag_type_variant_type_eq.
      (*generalize (enum_tag_rt_variant_rt_eq en r' (enum_tag en r') eq_refl) as Heq.*)
      (*rewrite /enum_variant_type /enum_tag_rt/enum_tag_ty' /enum_variant_rt. simpl.*)
      (*intros <-.*)
      (*rewrite Hty/=//. *)
      admit.
    }
    iApply (big_sepL_impl with "Hpad").
    iModIntro. iIntros (? [lyx | ] ?); simpl; last eauto.
    iIntros "(%v' & %r'' & %ly' & <- & ? & ? & ? & Hl & %Hlyv' & Hv)".
    rewrite /lty_of_ty_own.
    iExists lyx.
  Admitted.
  Lemma enum_unfold_1_shared {rt : Type} (en : enum rt) κ r :
    ⊢ ltype_incl' (Shared κ) (#r) (#r) (◁ (enum_t en))%I (EnumLtype en (enum_tag' en r) (◁ enum_tag_type' en (enum_tag' en r))).
  Proof.
  Abort.
  Lemma enum_unfold_1_uniq {rt : Type} (en : enum rt) κ γ r :
    ⊢ ltype_incl' (Uniq κ γ) (#r) (#r) (◁ (enum_t en))%I (EnumLtype en (enum_tag' en r) (◁ enum_tag_type' en (enum_tag' en r))).
  Proof.
  Abort.

  Local Lemma enum_unfold_1' {rt : Type} (en : enum rt) k r :
    ⊢ ltype_incl' k (#r) (#r) (◁ (enum_t en))%I (EnumLtype en (enum_tag' en r) (◁ enum_tag_type' en (enum_tag' en r))).
  Proof.
    destruct k.
    - iApply enum_unfold_1_owned.
    (*- iApply enum_unfold_1_shared.*)
    (*- iApply enum_unfold_1_uniq.*)
  Abort.
*)

  (* NOTE: Probably this will require PlaceIn, in order to know which variant to unfold to.
  Lemma enum_unfold_1 {rt : Type} (en : enum rt) k r :
    enum_tag_ty_inj en tag = Some sem →
    ⊢ ltype_incl k r r (◁ enum_t en)%I (EnumLtype en tag (◁ sem.(enum_tag_sem_ty)) re).
  Proof.
    iSplitR; first done. iModIntro. iSplit.
    (*+ iApply enum_unfold_1'.*)
    (*+ simp_ltypes. by iApply enum_unfold_1'.*)
  Abort.
  *)

  Lemma enum_unfold_2 {rt} (en : enum rt) sem tag re k r :
    enum_tag_ty_inj en tag = Some sem →
    ⊢ ltype_incl k r r (EnumLtype en tag (◁ sem.(enum_tag_sem_ty)) re) (◁ enum_t en)%I.
  Proof.
  Admitted.
End unfold.

Section cast.
  Context `{!typeGS Σ}.

  Import EqNotations.
  Lemma cast_ltype_enum {rt} E L (en : enum rt) variant {rte} (lte : ltype rte) re T :
    cast_ltype_to_type E L lte (λ tye,
      ∃ sem,
        ⌜enum_tag_ty_inj en variant = Some sem⌝ ∗
        ∃ (Heq : sem.(enum_tag_sem_rt) = rte),
        mut_eqtype E L (rew <- Heq in tye) (sem.(enum_tag_sem_ty)) (T (enum_t en)))
    ⊢ cast_ltype_to_type E L (EnumLtype en variant lte re) T.
  Proof.
  Admitted.
  Definition cast_ltype_enum_inst := [instance @cast_ltype_enum].
  Global Existing Instance cast_ltype_enum_inst.
End cast.
