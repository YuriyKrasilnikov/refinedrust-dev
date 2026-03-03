From refinedrust Require Export base type.
From refinedrust Require Import options.

(** * Mutable references *)
Section mut_ref.
  Context `{typeGS Σ}.
  Implicit Types (κ : lft) (γ : gname).

  Program Definition mut_ref  {rt : RT} (κ : lft) (inner : type rt) : type (place_rfn rt * gname)%type := {|
    ty_sidecond := True;
    ty_metadata_kind := MetadataNone;
    ty_own_val π '(r, γ) m v :=
      (∃ (l : loc) (ly : layout), ⌜m = MetaNone⌝ ∗ ⌜v = l⌝ ∗
      ⌜use_layout_alg (inner.(ty_syn_type) MetaNone) = Some ly⌝ ∗
      ⌜l `has_layout_loc` ly⌝ ∗
      loc_in_bounds l 0 ly.(ly_size) ∗
      inner.(ty_sidecond) ∗
      place_rfn_interp_mut r γ ∗
      have_creds ∗
      |={lftE}=> &pin{κ} (∃ r' : rt, gvar_auth γ r' ∗ |={lftE}=> l ↦: inner.(ty_own_val) π r' MetaNone))%I;

    _ty_has_op_type ot mt := is_ptr_ot ot;
    ty_syn_type _ := PtrSynType;

    ty_shr κ' π '(r, γ) m l :=
      (∃ (li : loc) (ly : layout) (r' : rt),
        ⌜m = MetaNone⌝ ∗
        ⌜l `has_layout_loc` void*⌝ ∗
        place_rfn_interp_shared r r' ∗
          &frac{κ'}(λ q', l ↦{q'} li) ∗
          (* needed explicity because there is a later + fupd over the sharing predicate *)
          ⌜use_layout_alg (inner.(ty_syn_type) MetaNone) = Some ly⌝ ∗
          ⌜li `has_layout_loc` ly⌝ ∗
          loc_in_bounds l 0 void*.(ly_size) ∗
          loc_in_bounds li 0 ly.(ly_size) ∗
          inner.(ty_sidecond) ∗
          (* we still need a later for contractiveness *)
          ▷ □ (|={lftE}=> inner.(ty_shr) (κ⊓κ') π r' MetaNone li))%I;
    (* NOTE: we cannot descend below the borrow here to get more information recursively.
       But this is fine, since the observation about γ here already contains all the information we need. *)
    ty_ghost_drop π '(r, γ) :=
      (*place_rfn_interp_mut r γ;*)
      match r with
      | #r' => gvar_pobs γ r'
      | PlaceGhost γ' => RelEq (T:=rt) γ' γ
      end;

    (* We need the inner lifetimes also to initiate sharing *)
    _ty_lfts := [κ] ++ ty_lfts inner;
    _ty_wf_E := ty_wf_E inner ++ ty_outlives_E inner κ;
  |}.
  Next Obligation.
    simpl. apply _.
  Qed.
  Next Obligation.
    iIntros (? κ inner  π [r γ] m v) "(%l & %ly & -> & -> & _)".
    iPureIntro. eexists. split; first by apply syn_type_has_layout_ptr.
    done.
  Qed.
  Next Obligation.
    iIntros (??? ot Hot) => /=. destruct ot => /=//.
    - intros _; by apply syn_type_has_layout_ptr.
    - intros ->; by apply syn_type_has_layout_ptr.
  Qed.
  Next Obligation.
    iIntros (? κ ? π r m v) "_". done.
  Qed.
  Next Obligation.
    iIntros (? κ ? ? π r m v) "_". done.
  Qed.
  Next Obligation.
    unfold TCNoResolve.
    iIntros (? κ ? κ' π l [r γ]). apply _.
  Qed.
  Next Obligation.
    iIntros (??????[r γ] m) "(%li & %ly & %r' & -> & % & ? &  _)".
    iPureIntro. eexists _. split; last by apply syn_type_has_layout_ptr.
    done.
  Qed.
  Next Obligation.
    (* initiate sharing *)
    (*
       Plan:
       - get the borrow containing the credit + atime.
       - open the borrows to obtain the receipts.
       - use the credit (will need more than one) to bring the nested borrow in the right shape.
         will need:
          + 1 credit/later for the fupd_later
          + 1 credit for folding the pinned borrow
            + 1 credit for unfoldign the pinned borrow
          + 1 credit/later for getting rid of the second fupd after unnesting
          + 1 credit/later for unnesting
        - then do recursive sharing and eliminate the logical_step for that.
        - introduce the logical step, using the time receipt.
        - after getting the credits and the receipt back, can close the two borrows
        - can now prove the conclusion.

    *)

    iIntros (? κ ? E κ' l ly π [r γ] m q ?) "#[LFT TIME] #Hna Htok %Hst %Hly _ Hb".
    iApply fupd_logical_step.
    iMod (bor_exists with "LFT Hb") as (v) "Hb"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Hl & Hb)"; first solve_ndisj.
    simpl. rewrite -{1}lft_tok_sep -{1}lft_tok_sep. iDestruct "Htok" as "[Htok_κ' [Htok_κ Htok]]".

    iMod (bor_exists with "LFT Hb") as (l0) "Hb"; first solve_ndisj.
    iMod (bor_exists with "LFT Hb") as (ly0) "Hb"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Ha & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Ha Htok_κ'") as "(>-> & Htok_κ')"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Ha & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Ha Htok_κ'") as "(>-> & Htok_κ')"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Ha & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Ha Htok_κ'") as "(>%Halg & Htok_κ')"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Ha & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Ha Htok_κ'") as "(>%Hly0 & Htok_κ')"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Ha & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Ha Htok_κ'") as "(>#Hlb & Htok_κ')"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Ha & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Ha Htok_κ'") as "(>#Hsc & Htok_κ')"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Hobs & Hb)"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Hcred & Hb)"; first solve_ndisj.
    iDestruct "Htok_κ'" as "(Htok_κ' & Htokc)".
    iMod (bor_acc with "LFT Hcred Htokc") as "(>(Hcred & Hat) & Hclos_c)"; first solve_ndisj.

    (* unnest the pinned borrow *)
    rewrite /num_cred. assert (5 = 2 + 3) as Heq by lia.
    rewrite {1}Heq. iDestruct "Hcred" as "(Hcred1 & Hcred)".
    iMod (pinned_bor_unnest_full with "LFT Hcred1 Htok_κ' Hb") as "Hb"; first done.
    iDestruct "Hcred" as "(Hcred1 & Hcred2 & Hcred)".
    iApply (lc_fupd_add_later with "Hcred1"). iNext.
    iMod "Hb". iMod "Hb".
    iApply (lc_fupd_add_later with "Hcred2"). iNext.
    iMod "Hb" as "(Hb & Htok_κ')".
    rewrite lft_intersect_comm.

    iDestruct "Htok_κ" as "(Htok_κ & Htok_κ2)".
    iCombine "Htok_κ Htok_κ'" as "Htoka". rewrite lft_tok_sep.
    iMod (bor_exists_tok with "LFT Hb Htoka") as "(%r' & Hb & Htoka)"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Hauth & Hb)"; first solve_ndisj.
    iMod (bor_fupd_later with "LFT Hb Htoka") as "Hu"; [done.. | ].
    iApply (lc_fupd_add_later with "Hcred"). iNext. iMod "Hu" as "(Hb & Htoka)".

    (* gain knowledge about the refinement *)
    iMod (place_rfn_interp_mut_share with "LFT [Hobs] Hauth Htoka") as "(#rfn & _ & _ & Htoka)"; first done.
    { iApply bor_shorten; last done. iApply lft_intersect_incl_r. }
    iDestruct "Htoka" as "(Htoka & Htoka2)".
    rewrite -{1}lft_tok_sep. iDestruct "Htoka" as "(Htok_κ & Htok_κ')".

    (* get a loc_in_bounds fact from the pointsto *)
    iMod (bor_acc with "LFT Hl Htok_κ'") as "(>Hl & Hcl_l)"; first solve_ndisj.
    iPoseProof (heap_pointsto_loc_in_bounds with "Hl") as "#Hlb'".
    iMod ("Hcl_l" with "Hl") as "(Hl & Htok_κ')".
    iCombine "Htok_κ Htok_κ'" as "Htoka1". rewrite lft_tok_sep.
    iCombine "Htoka1 Htoka2" as "Htoka".

    (* fracture *)
    iMod (bor_fracture (λ q, l ↦{q} l0)%I with "LFT Hl") as "Hl"; first solve_ndisj.

    (* recursively share *)
    iDestruct "Htok" as "(Htok1 & Htok2)".
    iPoseProof (ty_share _ E with "[$LFT $TIME] Hna [Htok2 Htoka] [//] [//] Hlb Hb") as "Hu"; first solve_ndisj.
    { rewrite ty_lfts_unfold. rewrite -!lft_tok_sep. iFrame. }
    iModIntro. iApply (logical_step_compose with "Hu").
    iApply (logical_step_intro_tr with "Hat").
    iIntros "Hcred Hat".
    iMod ("Hclos_c" with "[Hcred Hat]") as "(_ & Htok_κ'2)".
    { iNext. iFrame.
      iApply tr_weaken; last done.
      simpl. unfold num_laters_per_step; lia. }

    iModIntro. iIntros "(#Hshr & Htok)".
    iCombine "Htok_κ2 Htok_κ'2 Htok1" as "Htok2".
    rewrite !lft_tok_sep.
    rewrite lft_intersect_assoc.
    rewrite ty_lfts_unfold.
    iCombine "Htok Htok2" as "Htok".
    rewrite {2}lft_intersect_comm lft_intersect_assoc.
    iFrame "Htok".
    iExists l0, ly0, r'. iR. iFrame "Hl".
    apply syn_type_has_layout_ptr_inv in Hst as ->.
    iR. iSplitR. { destruct r; simpl; eauto. }
    iSplitR; first done. iSplitR; first done.
    iSplitR; first done.
    iSplitR; first done. iSplitR; first done.
    iNext. iModIntro. iModIntro. done.
  Qed.
  Next Obligation.
    iIntros (? κ inner κ0 κ' π [r γ] m l) "#Hincl".
    iIntros "(%li & %ly & %r' & -> & Hly & Hrfn & Hf & ? & ? & ? & ? & ? & #Hb)".
    iExists li, ly, r'. iR. iFrame.
    iSplitL "Hf". { iApply frac_bor_shorten; done. }
    iNext. iDestruct "Hb" as "#Hb". iModIntro. iMod "Hb". iModIntro.
    iApply ty_shr_mono; last done.
    iApply lft_intersect_mono; last done. iApply lft_incl_refl.
  Qed.
  Next Obligation.
    iIntros (????[r γ]????) "(%l & %ly & -> & -> & _ & _ & _ & _ & Hrfn & Hcred &  _)".
    iApply fupd_logical_step. destruct r as [ r | γ'].
    - iMod (gvar_obs_persist with "Hrfn") as "?".
      iApply logical_step_intro. by iFrame.
    - by iApply logical_step_intro.
  Qed.
  Next Obligation.
    iIntros (??? ot mt st ? [r γ] m ? Hot).
    destruct mt.
    - eauto.
    - iIntros "(%l & %ly & -> & -> & ?)". iExists l, ly. iFrame.
      iR.
      iPureIntro. move: ot Hot => [] /=// _.
      rewrite /mem_cast val_to_of_loc //.
    - iApply (mem_cast_compat_loc (λ v, _)); first done.
      iIntros "(%l & %ly & -> & -> & _)". eauto.
  Qed.
  Next Obligation.
    intros ??? ly mt _ Hst. apply syn_type_has_layout_ptr_inv in Hst as ->.
    done.
  Qed.

  Global Instance mut_ref_sized {rt} (ty : type rt) κ : TySized (mut_ref κ ty).
  Proof.
    econstructor; done.
  Qed.

  Global Instance mut_ref_type_contractive {rt : RT} κ : TypeContractive (mut_ref (rt:=rt) κ).
  Proof.
    constructor; simpl.
    - done.
    - done.
    - eapply ty_lft_morph_make_ref.
      + rewrite {1}ty_lfts_unfold. done.
      + rewrite {1}ty_wf_E_unfold. done.
    - rewrite ty_has_op_type_unfold/=. done.
    - done.
    - intros n ty ty' ?.
      intros π [] v. rewrite /ty_own_val/=.
      solve_type_proper.
    - intros n ty ty' ?.
      intros κ' π [] l. rewrite /ty_shr/=.
      solve_type_proper.
    - intros n ty ty' ?.
      intros. done.
  Qed.

  Global Instance mut_ref_type_ne {rt : RT} κ : TypeNonExpansive (mut_ref (rt:=rt) κ).
  Proof. apply type_contractive_type_ne, _. Qed.
End mut_ref.
Notation "&mut< κ , τ >" := (mut_ref κ τ) (only printing, format "'&mut<' κ , τ '>'") : stdpp_scope.

