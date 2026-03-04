From refinedrust Require Export base type ltypes.
From refinedrust Require Import programs.
From refinedrust.mut_ref Require Import def.
From refinedrust Require Import options.

(** [resolve_ghost] rules for mutable references *)

Section resolve_ghost.
  Context `{!typeGS Σ}.

  (** resolve_ghost *)
  Lemma resolve_ghost_mut_Owned {rt} π E L l (lt : ltype rt) γ rm lb κ T :
    find_observation (place_rfn rt * gname)%type γ FindObsModeDirect (λ or,
        match or with
        | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
        | Some r => T L r True true
        end)
    ⊢ resolve_ghost π E L rm lb l (MutLtype lt κ) (Owned) (PlaceGhost γ) T.
  Proof.
    rewrite /FindOptGvarPobs /=.
    iIntros "HT". iIntros (F ??) "#CTX #HE HL Hb".
    iMod ("HT" with "[//]") as "HT". iDestruct "HT" as "[(%r & Hobs & HT) | (-> & HT)]".
    - rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
      iDestruct "Hb" as "(%ly & %Hst & %Hly & ? & %γ0 & %r'& Hrfn & ?)".
      iPoseProof (place_rfn_interp_owned_find_observation with "Hrfn Hobs") as "Hrfn".
      iModIntro. iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro.
      iL. rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
      iExists _. iFrame. done.
    - iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Definition resolve_ghost_mut_Owned_inst := [instance @resolve_ghost_mut_Owned].
  Global Existing Instance resolve_ghost_mut_Owned_inst | 7.

  Lemma resolve_ghost_mut_Uniq {rt} π E L l (lt : ltype rt) γ rm lb κ κ' γ' T :
    find_observation (place_rfn rt * gname)%type γ FindObsModeDirect (λ or,
        match or with
        | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
        | Some r => T L r True true
        end)
    ⊢ resolve_ghost π E L rm lb l (MutLtype lt κ) (Uniq κ' γ') (PlaceGhost γ) T.
  Proof.
    rewrite /FindOptGvarPobs /=.
    iIntros "HT". iIntros (F ??) "#CTX #HE HL Hb".
    iMod ("HT" with "[//]") as "HT". iDestruct "HT" as "[(%r & Hobs & HT) | (-> & HT)]".
    - rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
      iDestruct "Hb" as "(%ly & %Hst & %Hly & ? & ? & Hrfn & ?)".
      iPoseProof (place_rfn_interp_mut_find_observation with "Hrfn Hobs") as "Hrfn".
      iModIntro. iExists _, _, _,_. iFrame. iApply maybe_logical_step_intro.
      iL. rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
      iExists _. iFrame. done.
    - iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Definition resolve_ghost_mut_Uniq_inst := [instance @resolve_ghost_mut_Uniq].
  Global Existing Instance resolve_ghost_mut_Uniq_inst | 7.

  Lemma resolve_ghost_mut_shared {rt} π E L l (lt : ltype rt) γ rm lb κ κ' T :
    find_observation (place_rfn rt * gname)%type γ FindObsModeDirect (λ or,
        match or with
        | None => ⌜rm = ResolveTry⌝ ∗ T L (PlaceGhost γ) True false
        | Some r => T L r True true
        end)
    ⊢ resolve_ghost π E L rm lb l (MutLtype lt κ) (Shared κ') (PlaceGhost γ) T.
  Proof.
    rewrite /FindOptGvarPobs /=.
    iIntros "HT". iIntros (F ??) "#CTX #HE HL Hb".
    iMod ("HT" with "[//]") as "HT". iDestruct "HT" as "[(%r & Hobs & HT) | (-> & HT)]".
    - rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
      iDestruct "Hb" as "(%ly & %Hst & %Hly & ? & %γ0 & %r'& Hrfn & ?)".
      iPoseProof (place_rfn_interp_shared_find_observation with "Hrfn Hobs") as "Hrfn".
      iModIntro. iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro.
      iL. rewrite ltype_own_mut_ref_unfold /mut_ltype_own.
      iExists _. iFrame. done.
    - iExists _, _, _, _. iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Definition resolve_ghost_mut_shared_inst := [instance @resolve_ghost_mut_shared].
  Global Existing Instance resolve_ghost_mut_shared_inst | 7.
End resolve_ghost.
