From refinedrust Require Export type.
From refinedrust Require Import options.

(** * Shared references *)
Section shr_ref.
  Context `{typeGS Σ}.
  Implicit Types (κ : lft).

  (* this is almost a simple type, but we have to be careful with
    the sharing predicate: we want to obtain the knowledge that l points to
    a location not under a later (to prove the agreement with the ltype unfolding),
     so the simple_type interface doesn't suffice *)
  Program Definition shr_ref {rt : RT} κ (inner : type rt) : type (place_rfn rt) := {|
    ty_sidecond := True;
    ty_metadata_kind := MetadataNone;
    ty_own_val π r m v :=
      (∃ (l : loc) (ly : layout) (r' : rt),
        ⌜m = MetaNone⌝ ∗
        ⌜v = val_of_loc l⌝ ∗
        ⌜use_layout_alg (inner.(ty_syn_type) MetaNone) = Some ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
        loc_in_bounds l 0 ly.(ly_size) ∗
        inner.(ty_sidecond) ∗
        place_rfn_interp_shared r r' ∗
        □ |={lftE}=> inner.(ty_shr) κ π r' MetaNone l)%I;

    _ty_has_op_type ot mt := is_ptr_ot ot;
    ty_syn_type m := PtrSynType;

    ty_shr κ' π r m l :=
      (∃ (li : loc) (ly : layout) (ri : rt),
        ⌜m = MetaNone⌝ ∗
        ⌜l `has_layout_loc` void*⌝ ∗
        (*loc_in_bounds l void*.(ly_size) ∗*)
        ⌜use_layout_alg (inner.(ty_syn_type) MetaNone) = Some ly⌝ ∗
        ⌜li `has_layout_loc` ly⌝ ∗
        loc_in_bounds li 0 ly.(ly_size) ∗
        inner.(ty_sidecond) ∗
        place_rfn_interp_shared r ri ∗
        &frac{κ'} (λ q, l ↦{q} li) ∗ ▷ □ |={lftE}=> inner.(ty_shr) (κ) π ri MetaNone li)%I;
    _ty_ghost_drop _ _ := True%I;
    _ty_lfts := [κ] ++ ty_lfts inner;
    _ty_wf_E := ty_wf_E inner ++ ty_outlives_E inner κ;
  |}.
  Next Obligation.
    intros. simpl. apply _.
  Qed.
  Next Obligation.
    iIntros (???????) "(%l & %ly & %r' & -> & -> & ? & ? & ?)".
    iPureIntro. eexists. split; first by apply syn_type_has_layout_ptr.
    done.
  Qed.
  Next Obligation.
    iIntros (? ?? ot Hot) => /=.
    destruct ot => /=//.
    - intros; by apply syn_type_has_layout_ptr.
    - intros ->; by apply syn_type_has_layout_ptr.
  Qed.
  Next Obligation. iIntros (???????) "_". done. Qed.
  Next Obligation. iIntros (????????) "_". done. Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    iIntros (????????). simpl. iIntros "(%l' & %ly & %r' & % & % & ? & ? & _)".
    iPureIntro. eexists _. split; last by apply syn_type_has_layout_ptr.
    done.
  Qed.
  Next Obligation.
    iIntros (? κ ? E κ' l ly π r m q ?) "#[LFT TIME] #Hna Htok %Halg %Hly _ Hb".
    simpl. rewrite -{1}lft_tok_sep -{1}lft_tok_sep.
    iDestruct "Htok" as "(Htok_κ' & Htok_κ & Htok)".
    iApply fupd_logical_step.
    iMod (bor_exists with "LFT Hb") as "(%v & Hb)"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "[Hl Hb]"; first solve_ndisj.
    iMod (bor_exists with "LFT Hb") as "(%l' & Hb)"; first solve_ndisj.
    iMod (bor_exists with "LFT Hb") as "(%ly' & Hb)"; first solve_ndisj.
    iMod (bor_exists_tok with "LFT Hb Htok_κ'") as "(%r' & Hb & Htok_κ')"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Heq & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Heq Htok_κ'") as "(>-> & Htok_κ')"; first solve_ndisj.
    iMod (bor_sep with "LFT Hb") as "(Heq & Hb)"; first solve_ndisj.
    iMod (bor_persistent with "LFT Heq Htok_κ'") as "(>-> & Htok_κ')"; first solve_ndisj.
    iMod (bor_persistent with "LFT Hb Htok_κ'") as "(Ha & Htok_κ')"; first solve_ndisj.
    iDestruct "Ha" as "(>%Halg' & >%Hly' & >#Hlb & >#Hsc & >Hrfn & Hshr)".
    iMod (bor_fracture (λ q, l ↦{q} l')%I with "LFT Hl") as "Hl"; first solve_ndisj.
    iModIntro.
    iApply logical_step_intro.
    rewrite -!lft_tok_sep. iFrame.
    apply syn_type_has_layout_ptr_inv in Halg as ->.
    iExists ly'.
    iR.
    do 4 iR. iFrame "Hsc".
  Qed.
  Next Obligation.
    iIntros (? ? ? κ' κ'' π r m l) "#Hord H".
    iDestruct "H" as (li ly ri ->) "(? & ? & ? & Hlb & Hsc & Hr & #Hf & #Hown)".
    iExists li, ly, ri. iR. iFrame. iSplit.
    - by iApply (frac_bor_shorten with "Hord").
    - iNext. iDestruct "Hown" as "#Hown". iModIntro. iMod "Hown". iModIntro.
      done.
  Qed.
  Next Obligation.
    intros. iIntros "_". by iApply logical_step_intro.
  Qed.
  Next Obligation.
    iIntros (? ?? ot mt st ? r m ? Hot).
    destruct mt.
    - eauto.
    - iIntros "(%l & %ly & %ri & -> & -> & ? & ? & ?)".
      iExists l, ly, ri. iFrame.
      iPureIntro. split; first done.
      move: ot Hot => [] /= // _.
      rewrite /mem_cast val_to_of_loc //.
    - iApply (mem_cast_compat_loc (λ v, _)); first done.
      iIntros "(%l & %ly & %ri & -> & -> & _)". eauto.
  Qed.
  Next Obligation.
    intros ??? ly mt _ Hst. apply syn_type_has_layout_ptr_inv in Hst as ->.
    done.
  Qed.

  Global Instance shr_ref_sized {rt} (ty : type rt) κ : TySized (shr_ref κ ty).
  Proof.
    econstructor; done.
  Qed.

  Global Instance shr_ref_copyable {rt} (ty : type rt) κ : Copyable (shr_ref κ ty).
  Proof.
    constructor; first apply _.
    iIntros (κ' π E l r ? ? ?) "[LFT TIME] (%li & %ly' & %r' & -> & %Hly' & % & % & #Hlb & #Hsc & #Hr & Hf & #Hown) Hlft".
    iMod (frac_bor_acc with "LFT Hf Hlft") as (q') "[Hmt Hclose]"; first solve_ndisj.
    iModIntro.
    (*apply syn_type_has_layout_ptr_inv in Ha as ->.*)
    (*iSplitR; first done.*)
    iExists _.
    iSplitR. { simpl. iPureIntro. by apply syn_type_has_layout_ptr. }
    iR.
    iExists _, li. iDestruct "Hmt" as "[Hmt1 Hmt2]".
    iSplitL "Hmt1". { iNext. iFrame "Hmt1". iExists li, ly', r'. iFrame "#". iPureIntro. split_and!; try done. }
    iIntros "Hmt1".
    iApply "Hclose". iModIntro. rewrite -{3}(Qp.div_2 q').
    iPoseProof (heap_pointsto_agree with "Hmt1 Hmt2") as "%Heq"; first done.
    rewrite heap_pointsto_fractional. iFrame.
  Qed.

  Global Instance shr_ref_type_contractive {rt : RT} κ : TypeContractive (shr_ref (rt:=rt) κ).
  Proof.
    constructor; simpl.
    - done.
    - done.
    - eapply ty_lft_morph_make_ref.
      + rewrite {1}ty_lfts_unfold; done.
      + rewrite {1}ty_wf_E_unfold; done.
    - rewrite ty_has_op_type_unfold/=. done.
    - done.
    - solve_type_proper.
    - solve_type_proper.
    - rewrite ty_ghost_drop_unfold. solve_type_proper.
  Qed.

  Global Instance shr_ref_type_ne {rt : RT} κ : TypeNonExpansive (shr_ref (rt:=rt) κ).
  Proof. apply type_contractive_type_ne, _. Qed.
End shr_ref.


Notation "&shr< κ , τ >" := (shr_ref τ κ) (only printing, format "'&shr<' κ , τ '>'") : stdpp_scope.
