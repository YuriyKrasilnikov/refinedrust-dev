From refinedrust Require Export type ltypes.
From refinedrust Require Import programs.
From refinedrust Require Import options.

(** * Iterated version of resolve_ghost for arrays *)

Section resolve_ghost.
  Context `{!typeGS Σ}.

  Lemma resolve_ghost_iter_id {rt} π E L m b l st (lts : list (ltype rt)) bk rs idx n (T : resolve_ghost_iter_cont_t rt) :
    T L rs True false ⊢
    resolve_ghost_iter π E L m b l st lts bk rs idx n T.
  Proof.
    iIntros "HT".
    unfold resolve_ghost_iter.
    iIntros (???) "#CTX #HE HL %Hlen Ha".
    iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Lemma resolve_ghost_iter_id_fmap_in {rt} π E L m b l st (lts : list (ltype rt)) bk rs idx n (T : resolve_ghost_iter_cont_t rt) :
    T L (<#> rs) True false ⊢ resolve_ghost_iter π E L m b l st lts bk (<#> rs) idx n T.
  Proof. apply resolve_ghost_iter_id. Qed.
  Definition resolve_ghost_iter_id_fmap_in_inst := [instance @resolve_ghost_iter_id_fmap_in].
  Global Existing Instance resolve_ghost_iter_id_fmap_in_inst.

  Lemma resolve_ghost_iter_id_fmap_xin {rt} π E L m b l st (lts : list (ltype rt)) bk rs idx n (T : resolve_ghost_iter_cont_t rt) :
    T L ((PlaceIn ∘ RT_xrt rt) <$> rs) True false ⊢ resolve_ghost_iter π E L m b l st lts bk ((PlaceIn ∘ RT_xrt rt) <$> rs) idx n T.
  Proof. apply resolve_ghost_iter_id. Qed.
  Definition resolve_ghost_iter_id_fmap_xin_inst := [instance @resolve_ghost_iter_id_fmap_xin].
  Global Existing Instance resolve_ghost_iter_id_fmap_xin_inst.

  Lemma resolve_ghost_iter_id_fmap_in' {rt} π E L m b l st (lts : list (ltype rt)) bk {A} (rs : list A) idx n (f : A → _) (T : resolve_ghost_iter_cont_t rt) :
    T L ((λ x, # (f x)) <$> rs) True false ⊢ resolve_ghost_iter π E L m b l st lts bk ((λ x, # (f x)) <$> rs) idx n T.
  Proof. apply resolve_ghost_iter_id. Qed.
  Definition resolve_ghost_iter_id_fmap_in'_inst := [instance @resolve_ghost_iter_id_fmap_in'].
  Global Existing Instance resolve_ghost_iter_id_fmap_in'_inst.

  Lemma resolve_ghost_iter_cons_not_ignored π E L rm lb l st {rt} (lts : list (ltype rt)) b (r : place_rfn rt) (rs : list (place_rfn rt)) ig (i0 : nat) `{!CanSolve(i0 ∉ ig)} T :
    (∃ lt lts', ⌜lts = lt :: lts'⌝ ∗
      resolve_ghost π E L rm lb (l offsetst{st}ₗ i0) lt b r (λ L2 r' R progress,
        resolve_ghost_iter π E L2 rm lb l st lts' b rs ig (S i0) (λ L3 rs2 R2 progress',
        T L3 (r' :: rs2) (R ∗ R2) (orb progress  progress'))))
    ⊢
    resolve_ghost_iter π E L rm lb l st lts b (r :: rs) ig i0 T.
  Proof.
    rename select (CanSolve _) into Helem.
    rewrite /CanSolve in Helem.
    iIntros "(%lt & %lts' & -> & HT)".
    iIntros (???) "#CTX #HE HL %Hlen (Hx & Hr)".
    rewrite decide_False; last done.
    iMod ("HT" with "[//] [//] CTX HE HL Hx") as "(%L2 & %r' & %R1 & %prog & Hs & HL & HT)".
    iMod ("HT" with "[//] [//] CTX HE HL [] [Hr]") as "Hx".
    { iPureIntro. simpl in *. lia. }
    { iApply (big_sepL2_impl with "Hr"). iModIntro. iIntros (??? ??) "Hx".
      rewrite !Nat.add_succ_r. rewrite -!Nat2Z.inj_add Nat.add_succ_r. done. }
    iDestruct "Hx" as "(%L3 & %rs' & %R2 & %prog' & Hs' & HL & HT)".
    iModIntro. iExists _, _, _, _. iFrame.
    iApply (maybe_logical_step_compose with "Hs").
    iApply (maybe_logical_step_compose with "Hs'").
    iApply maybe_logical_step_intro.
    iIntros "(Hx & $) (Hx2 & $)".
    simpl. rewrite decide_False; last done. iFrame "Hx2".
    iApply (big_sepL2_impl with "Hx"). iModIntro. iIntros (??? ??) "Hx".
      rewrite !Nat.add_succ_r. rewrite -!Nat2Z.inj_add Nat.add_succ_r. done.
  Qed.
  Definition resolve_ghost_iter_cons_not_ignored_inst := [instance @resolve_ghost_iter_cons_not_ignored].
  Global Existing Instance resolve_ghost_iter_cons_not_ignored_inst.

  Lemma resolve_ghost_iter_cons_ignored π E L rm lb l st {rt} (lts : list (ltype rt)) b (r : place_rfn rt) (rs : list (place_rfn rt)) ig (i0 : nat) `{!CanSolve(i0 ∈ ig)} T :
    (∃ lt lts', ⌜lts = lt :: lts'⌝ ∗
      resolve_ghost_iter π E L rm lb l st lts' b rs ig (S i0) (λ L2 rs2 R progress,
        T L2 (r :: rs2) (R) (progress)))
    ⊢
    resolve_ghost_iter π E L rm lb l st lts b (r :: rs) ig i0 T.
  Proof.
    rename select (CanSolve _) into Helem.
    rewrite /CanSolve in Helem.
    iIntros "(%lt & %lts' & -> & HT)".
    iIntros (???) "#CTX #HE HL %Hlen (Hx & Hr)".
    iMod ("HT" with "[//] [//] CTX HE HL [] [Hr]") as "Hr".
    { iPureIntro. simpl in *. lia. }
    { iApply (big_sepL2_impl with "Hr"). iModIntro. iIntros (??? ??) "Hx".
      rewrite !Nat.add_succ_r. rewrite -!Nat2Z.inj_add Nat.add_succ_r. done. }
    iDestruct "Hr" as "(%L2 & %rs' & %R & %prog & Hs' & HL & HT)".
    iModIntro. iExists _, _, _, _. iFrame.
    iApply (maybe_logical_step_wand with "[] Hs'").
    iIntros "(Hx & $)".
    simpl. rewrite decide_True; last done. iR.
    iApply (big_sepL2_impl with "Hx"). iModIntro. iIntros (??? ??) "Hx".
      rewrite !Nat.add_succ_r. rewrite -!Nat2Z.inj_add Nat.add_succ_r. done.
  Qed.
  Definition resolve_ghost_iter_cons_ignored_inst := [instance @resolve_ghost_iter_cons_ignored].
  Global Existing Instance resolve_ghost_iter_cons_ignored_inst.

  Lemma resolve_ghost_iter_insert_ignored π E L rm lb l st {rt} (lts : list (ltype rt)) b r rs ig i0 `{!CanSolve ((i + i0) ∈ ig)} T:
    resolve_ghost_iter π E L rm lb l st lts b rs ig i0 T ⊢
    resolve_ghost_iter π E L rm lb l st lts b (<[i := r]> rs) ig i0 T.
  Proof.
    rename select (CanSolve _) into Helem.
    rewrite /CanSolve in Helem.
    iIntros "HT".
    iIntros (???) "#CTX #HE HL %Hlen Ha".
    iMod ("HT" with "[//] [//] CTX HE HL [] [Ha]") as "Hr".
    { iPureIntro. move: Hlen. rewrite length_insert. done. }
    { destruct (decide (i < length rs)); first last.
      { rewrite list_insert_id'; first done. lia. }
      odestruct (lookup_lt_is_Some_2 lts i _) as (lt & Hlook).
      { rewrite Hlen length_insert. done. }
      rewrite -{1}(list_insert_id lts i lt _); last done.
      set (Φ := (λ i1 r lt, if decide (i1 + i0 ∈ ig) then True else (l offsetst{st}ₗ (i1 + i0)) ◁ₗ[ π, b] r @ lt)%I).
      rewrite (big_sepL2_insert rs lts i r lt Φ 0); [ | lia | by eapply lookup_lt_is_Some_1].
      iDestruct "Ha" as "(_ & Ha)".
      iApply (big_sepL2_impl with "Ha"). iModIntro. iIntros (k ?? ??) "Hx".
      case_decide; last done.
      subst k. rewrite decide_True; done. }
    iDestruct "Hr" as "(%L2 & %rs' & %R & %prog & Hs' & HL & HT)".
    iModIntro. iExists _, _, _, _. iFrame.
  Qed.
  Definition resolve_ghost_iter_insert_ignored_inst := [instance @resolve_ghost_iter_insert_ignored].
  Global Existing Instance resolve_ghost_iter_insert_ignored_inst.

  Lemma resolve_ghost_iter_insert_not_ignored π E L rm lb l st {rt} (lts : list (ltype rt)) b r rs ig i0 `{!CanSolve ((i + i0) ∉ ig)} T:
    (∃ lt, ⌜lts !! i = Some lt⌝ ∗
      resolve_ghost π E L rm lb (l offsetst{st}ₗ (i + i0)) lt b r (λ L2 r' R progress,
        resolve_ghost_iter π E L2 rm lb l st lts b rs ((i + i0) :: ig) i0 (λ L3 rs2 R2 progress',
          T L3 (<[i := r']> rs2) (R ∗ R2) (orb progress  progress')))) ⊢
    resolve_ghost_iter π E L rm lb l st lts b (<[i := r]> rs) ig i0 T.
  Proof.
    rename select (CanSolve _) into Helem.
    rewrite /CanSolve in Helem.
    iIntros "(%lt & %Hlook & HT)".
    iIntros (???) "#CTX #HE HL %Hlen Ha".
    rewrite length_insert in Hlen.
    assert (i < length rs). { rewrite -Hlen. by apply lookup_lt_is_Some_1. }
    rewrite -{2}(list_insert_id lts i lt _); last done.
    set (Φ := (λ i1 r lt, if decide (i1 + i0 ∈ ig) then True else (l offsetst{st}ₗ (i1 + i0)) ◁ₗ[ π, b] r @ lt)%I).
    rewrite (big_sepL2_insert rs lts i r lt Φ 0); [ | lia | by eapply lookup_lt_is_Some_1].
    iDestruct "Ha" as "(Ha & Hb)".

    iMod ("HT" with "[//] [//] CTX HE HL [Ha]") as "Hr".
    { unfold Φ. rewrite decide_False; last done. done. }
    iDestruct "Hr" as "(%L2 & %r2 & %R & % & Hstep & HL & HT)".
    iMod ("HT" with "[//] [//] CTX HE HL [] [Hb]") as "Hr".
    { done. }
    { iApply (big_sepL2_impl with "Hb"). iIntros "!>" (k ?? Hlook1 Hlook2).
      case_decide. { subst k. rewrite decide_True; [eauto | set_solver]. }
      unfold Φ. case_decide.
      - rewrite decide_True; first eauto. set_solver.
      - rewrite decide_False; first eauto.
        intros [ | ]%elem_of_cons; [lia | done]. }
    iDestruct "Hr" as "(%L3 & %rs2 & %R2 & % & Hstep2 & $ & $)".
    iApply (maybe_logical_step_compose with "Hstep").
    iApply (maybe_logical_step_wand with "[] Hstep2").
    iIntros "(Ha & $) (Hb & $)".
    iPoseProof (big_sepL2_length with "Ha") as "%Hlen2".

    rewrite -{2}(list_insert_id lts i lt _); last done.
    rewrite (big_sepL2_insert rs2 lts i r2 lt Φ 0); [ | lia | by eapply lookup_lt_is_Some_1].
    iSplitL "Hb".
    - unfold Φ. case_decide; first done. simpl. by iFrame.
    - iApply (big_sepL2_impl with "Ha"). iIntros "!>" (k ?? Hlook1 Hlook2).
      destruct (decide (k = i)) as [-> | ?]; first by eauto.
      case_decide as Hel.
      + apply elem_of_cons in Hel as [ | Hel]; first lia.
        unfold Φ. rewrite decide_True; last set_solver. eauto.
      + unfold Φ.
        rewrite decide_False; first by eauto.
        contradict Hel. set_solver.
  Qed.
  Definition resolve_ghost_iter_insert_not_ignored_inst := [instance @resolve_ghost_iter_insert_not_ignored].
  Global Existing Instance resolve_ghost_iter_insert_not_ignored_inst.

  Lemma resolve_ghost_iter_nil π E L rm lb l st {rt} (lts : list (ltype rt)) b ig i0 T :
    T L [] True%I false
    ⊢ resolve_ghost_iter π E L rm lb l st lts b [] ig i0 T.
  Proof.
    apply resolve_ghost_iter_id.
  Qed.
  Definition resolve_ghost_iter_nil_inst := [instance @resolve_ghost_iter_nil].
  Global Existing Instance resolve_ghost_iter_nil_inst.
End resolve_ghost.


