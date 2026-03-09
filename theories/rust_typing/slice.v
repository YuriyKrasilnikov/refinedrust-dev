From refinedrust Require Export type.
From refinedrust Require Import uninit_def int.
From refinedrust Require Import options.

From refinedrust Require Import array.def.

Section def.
  Context `{!typeGS Σ}.
  Context {rt : RT}.

  (* TODO: this is very similar to array, except for where the length comes from. Can we deduplicate this? *)
  Program Definition slice (ty : type rt) : type (list (place_rfn rt)) := {|
    ty_metadata_kind := MetadataSize;
    ty_own_val π r m v :=
      (∃ len ly,
        ⌜m = MetaSize len⌝ ∗
        ⌜syn_type_has_layout (ty.(ty_syn_type) MetaNone) ly⌝ ∗
        ⌜(ly_size ly * len ≤ MaxInt ISize)%Z⌝ ∗
        ⌜length r = len⌝ ∗
        ⌜v `has_layout_val` (mk_array_layout ly len)⌝ ∗
        [∗ list] r'; v' ∈ r; reshape (replicate len (ly_size ly)) v,
          array_own_el_val π ty r' v')%I;
    ty_shr κ π r m l :=
      (∃ len ly,
        ⌜m = MetaSize len⌝ ∗
        ⌜syn_type_has_layout (ty.(ty_syn_type) MetaNone) ly⌝ ∗
        ⌜(ly_size ly * len ≤ MaxInt ISize)%Z⌝ ∗
        ⌜length r = len⌝ ∗
        ⌜l `has_layout_loc` ly⌝ ∗
        [∗ list] i ↦ r' ∈ r, array_own_el_shr π κ i ly ty r' l)%I;
    ty_syn_type m :=
      match m with
      | MetaSize len =>
          ArraySynType (ty.(ty_syn_type) MetaNone) len
      | _ => UnitSynType
      end;
    _ty_has_op_type ot mt :=
      (* no copies supported since this is unsized *)
      False;
    _ty_ghost_drop π r :=
      (* TODO *)
      True%I;
    ty_sidecond := True;
    _ty_lfts := ty_lfts ty;
    _ty_wf_E := ty_wf_E ty;
  |}.
  Next Obligation.
    iIntros (ty π r m v) "(%ly & %len & -> & %Hst & %Hsz & %Hlen & %Hly & Hv)".
    iExists _.
    iSplitR. { iPureIntro. eapply syn_type_has_layout_array; done. }
    done.
  Qed.
  Next Obligation.
    iIntros (ty ot mt Hot).
    destruct ot; try done.
  Qed.
  Next Obligation.
    iIntros (ty π r m v) "_". done.
  Qed.
  Next Obligation.
    iIntros (ty ? π r m v) "_". done.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    iIntros (ty κ π l m r) "(%len & %ly & -> & %Hst & %Hsz & %Hlen & %Hly & Hv)".
    iExists (mk_array_layout ly len). iSplitR; first done.
    iPureIntro. by eapply syn_type_has_layout_array.
  Qed.
  Next Obligation.
    iIntros (ty E κ l ly π r m q ?).
    iIntros "#(LFT & LCTX) #Hna Htok %Hst %Hly #Hlb Hb".
    rewrite -lft_tok_sep. iDestruct "Htok" as "(Htok & Htok')".
    iApply fupd_logical_step.
    (* reshape the borrow - we must not freeze the existential over v to initiate recursive sharing *)
    iPoseProof (bor_iff _ _ (∃ len ly', ⌜m = MetaSize len⌝ ∗ ⌜syn_type_has_layout (ty_syn_type ty MetaNone) ly'⌝ ∗ ⌜(ly_size ly' * len ≤ MaxInt ISize)%Z⌝ ∗  ⌜length r = len⌝ ∗ [∗ list] i ↦ r' ∈ r, ∃ v, array_own_el_loc π 1%Qp v i ly' ty r' l)%I with "[] Hb") as "Hb".
    { iNext. iModIntro. iSplit.
      - iIntros "(%v & Hl & %len & %ly' & -> & %Hst' & %Hsz & %Hlen & %Hv & Hv)".
        iExists len, ly'. do 4 iR.
        iApply (array_own_val_join_pointsto with "Hl Hv"); done.
      - iIntros "(%len & %ly' & -> & %Hst' & %Hsz & %Hlen & Hl)".
        apply syn_type_has_layout_array_inv in Hst as (ly0 & Hst0 & -> & ?).
        assert (ly0 = ly') as ->. { by eapply syn_type_has_layout_inj. }
        iPoseProof (array_own_val_extract_pointsto with "[Hlb] Hl") as "(%vs & Hl & % & Ha)"; [done.. | | ].
        { iApply (loc_in_bounds_shorten_suf with "Hlb"); lia. }
        iExists vs. iFrame "Hl". iExists len, ly'. do 5 iR. done.
    }

    iMod (bor_exists with "LFT Hb") as "(%len & Hb)"; first done.
    iMod (bor_exists with "LFT Hb") as "(%ly' & Hb)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hst & Hb)"; first done.
    iMod (bor_persistent with "LFT Hst Htok") as "(>-> & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hst & Hb)"; first done.
    iMod (bor_persistent with "LFT Hst Htok") as "(>%Hst' & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hsz & Hb)"; first done.
    iMod (bor_persistent with "LFT Hsz Htok") as "(>%Hsz & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hlen & Hb)"; first done.
    iMod (bor_persistent with "LFT Hlen Htok") as "(>%Hlen & Htok)"; first done.
    iMod (bor_big_sepL with "LFT Hb") as "Hb"; first done.
    iCombine "Htok Htok'" as "Htok". rewrite lft_tok_sep.
    (* fracture the tokens over the big_sep *)
    iPoseProof (Fractional_split_big_sepL (λ q, q.[_]%I) len with "Htok") as "(%qs & %Hlen' & Htoks & Hcl_toks)".
    set (κ' := κ ⊓ foldr meet static (ty_lfts ty)).
    iAssert ([∗ list] i ↦ x; q' ∈ r; qs, &{κ} (∃ v r'', (l offset{ly'}ₗ i) ↦ v ∗ place_rfn_interp_owned x r'' ∗ v ◁ᵥ{π, MetaNone} r'' @ ty) ∗ q'.[κ'])%I with "[Htoks Hb]" as "Hb".
    { iApply big_sepL2_sep_sepL_r; iFrame. iApply big_sepL2_const_sepL_l. iSplitR; last done. rewrite Hlen Hlen' //. }

    eapply syn_type_has_layout_array_inv in Hst as (ly0 & Hst & -> & ?).
    assert (ly0 = ly') as -> by by eapply syn_type_has_layout_inj.
    iAssert ([∗ list] i ↦ x; q' ∈ r; qs, logical_step E (array_own_el_shr π κ i ly' ty x l ∗ q'.[κ']))%I with "[Hb]" as "Hb".
    { iApply (big_sepL2_wand with "Hb"). iApply big_sepL2_intro. { simpl in *. lia. }
      iModIntro. iIntros (k x q0 Hlook1 Hlook2) "(Hb & Htok)".
      rewrite bi_exist_comm.
      iApply fupd_logical_step.
      subst κ'.
      rewrite -{1}lft_tok_sep. iDestruct "Htok" as "(Htok1 & Htok2)".
      iMod (bor_exists_tok with "LFT Hb Htok1") as "(%r' & Ha & Htok1)"; first done.
      iPoseProof (bor_iff _ _ (place_rfn_interp_owned x r' ∗ ∃ a, (l offset{ly'}ₗ k) ↦ a ∗ a ◁ᵥ{ π, MetaNone} r' @ ty)%I with "[] Ha") as "Ha".
      { iNext. iModIntro. iSplit.
        - iIntros "(%a & ? & ? & ?)". eauto with iFrame.
        - iIntros "(? & %a & ? & ?)". eauto with iFrame. }
      iMod (bor_sep with "LFT Ha") as "(Hrfn & Hb)"; first done.
      iMod (place_rfn_interp_owned_share with "LFT Hrfn Htok1") as "(Hrfn & Htok1)"; first done.
      iCombine "Htok1 Htok2" as "Htok". rewrite lft_tok_sep. iModIntro.
      rewrite ty_lfts_unfold.
      iPoseProof (ty_share with "[$LFT $LCTX] Hna Htok [] [] [] Hb") as "Hb"; first done.
      - done.
      - iPureIntro.
        apply has_layout_loc_offset_loc.
        { eapply use_layout_alg_wf. done. }
        {  done. }
      - assert (1 + k ≤ len)%nat as ?.
        { eapply lookup_lt_Some in Hlook1. simpl in *. lia. }
        iApply loc_in_bounds_offset; last done.
        { done. }
        { rewrite /offset_loc. simpl. lia. }
        { rewrite /mk_array_layout /ly_mult {2}/ly_size. rewrite /offset_loc /=. nia. }
      - iApply (logical_step_wand with "Hb"). iIntros "(? & ?)".
        rewrite /array_own_el_shr. eauto with iFrame.
    }
    iPoseProof (logical_step_big_sepL2 with "Hb") as "Hb".
    iModIntro. iApply (logical_step_wand with "Hb"). iIntros "Hb".
    iPoseProof (big_sepL2_sep_sepL_r with "Hb") as "(Hb & Htok)".
    iPoseProof ("Hcl_toks" with "Htok") as "$".
    iPoseProof (big_sepL2_const_sepL_l with "Hb") as "(_ & Hb)".
    iExists _, _. do 5 iR. done.
  Qed.
  Next Obligation.
    iIntros (ty κ κ' π r m l) "#Hincl Hb".
    iDestruct "Hb" as "(%len & %ly & -> & Hst & Hsz & Hlen & Hly & Hb)".
    iExists len, ly. iFrame. iR.
    iApply (big_sepL_wand with "Hb"). iApply big_sepL_intro.
    iIntros "!>" (k x Hlook) "(% & ? & Hb)".
    iExists _; iFrame. iApply ty_shr_mono; done.
  Qed.
  Next Obligation.
    intros. iIntros "_". by iApply logical_step_intro.
  Qed.
  Next Obligation.
    iIntros (ty ot mt st π r m v Hot) "Hb".
    destruct ot as [ | | | | ly' | ]; try done.
  Qed.
  Next Obligation.
    intros ty ly mt ? Hst.
    simpl.
    done.
  Qed.


End def.
