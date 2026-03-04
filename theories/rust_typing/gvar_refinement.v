From iris.bi Require Export fractional.
From refinedrust Require Export base.
From refinedrust Require Export ghost_var_dfrac.
From refinedrust Require Import options.

(** * Borrow variables *)

Section sigma.
  Record RT : Type := RT_into {
    RT_rt : Type;
    RT_r : RT_rt;
    }.
  Global Arguments RT_into {_}.

  Import EqNotations.
  Lemma RT_rt_eq (x y : RT) :
    x = y → RT_rt x = RT_rt y.
  Proof.
    inversion 1. done.
  Qed.
  Lemma RT_r_eq (x y : RT) (Heq : x = y) :
    rew Heq in RT_r x = RT_r y.
  Proof.
    inversion Heq. subst. done.
  Qed.

  Lemma RT_into_inj T (x y : T) :
    RT_into x = RT_into y → x = y.
  Proof.
    revert x y.
    enough (∀ a b : RT, a = b → ∀ Heq' : RT_rt a = RT_rt b, rew [id] Heq' in RT_r a = RT_r b) as H.
    { intros x y Heq. by specialize (H _ _ Heq eq_refl). }
    intros a b Heq. destruct Heq. intros Heq.
    specialize (UIP_t _ _ _ Heq eq_refl) as ->. done.
  Qed.

End sigma.


Section ghost_variables.
  Context `{!ghost_varG Σ RT} {T : Type}.
  Implicit Types (γ : gname) (t : T).

  Definition gvar_auth γ t := ghost_var γ (DfracOwn (1/2)) (RT_into t).
  Definition gvar_obs γ t := ghost_var γ (DfracOwn (1/2)) (RT_into t).
  Definition gvar_pobs γ t := ghost_var γ DfracDiscarded (RT_into t).

  Global Instance gvar_pobs_persistent γ t : Persistent (gvar_pobs γ t).
  Proof. apply _. Qed.

  Lemma gvar_alloc t :
    ⊢ |==> ∃ γ, gvar_auth γ t ∗ gvar_obs γ t.
  Proof.
    iMod (ghost_var_alloc (RT_into t)) as "(%γ & (? & ?))".
    iModIntro. iExists γ. iFrame.
  Qed.

  Lemma gvar_update {γ t1 t2} t :
    gvar_auth γ t1 -∗ gvar_obs γ t2 ==∗ gvar_auth γ t ∗ gvar_obs γ t.
  Proof. iApply ghost_var_update_halves. Qed.

  Lemma gvar_obs_persist γ t :
    gvar_obs γ t ==∗ gvar_pobs γ t.
  Proof. iApply ghost_var_discard. Qed.

  Lemma gvar_auth_persist γ t :
    gvar_auth γ t ==∗ gvar_pobs γ t.
  Proof. iApply ghost_var_discard. Qed.

  Lemma gvar_agree γ t1 t2:
    gvar_auth γ t1 -∗ gvar_obs γ t2 -∗ ⌜t1 = t2⌝.
  Proof.
    iIntros "H1 H2".
    iPoseProof (ghost_var_agree with "H1 H2") as "%Heq".
    apply RT_into_inj  in Heq. done.
  Qed.

  Lemma gvar_pobs_agree γ t1 t2:
    gvar_auth γ t1 -∗ gvar_pobs γ t2 -∗ ⌜t1 = t2⌝.
  Proof.
    iIntros "H1 H2".
    iPoseProof (ghost_var_agree with "H1 H2") as "%Heq".
    apply RT_into_inj  in Heq. done.
  Qed.
  Lemma gvar_pobs_agree_2 γ t1 t2:
    gvar_pobs γ t1 -∗ gvar_pobs γ t2 -∗ ⌜t1 = t2⌝.
  Proof.
    iIntros "H1 H2".
    iPoseProof (ghost_var_agree with "H1 H2") as "%Heq".
    apply RT_into_inj  in Heq. done.
  Qed.

  Definition RelEq (γ1 γ2 : gname) : iProp Σ :=
    ∃ v1 v2, gvar_pobs γ1 v1 ∗ gvar_obs γ2 v2 ∗ ⌜v1 = v2⌝.

  Lemma RelEq_use_pobs γ1 γ2 v1 :
    gvar_pobs γ1 v1 -∗ RelEq γ1 γ2 -∗ gvar_obs γ2 v1.
  Proof.
    iIntros "Hobs1 (%v1' & %v2 & Hauth1 & Hobs2 & %HR)".
    iPoseProof (gvar_pobs_agree_2 with "Hauth1 Hobs1") as "->".
    subst. done.
  Qed.

  Lemma RelEq_use_obs γ1 γ2 v1 :
    gvar_obs γ1 v1 -∗ RelEq γ1 γ2 -∗ gvar_obs γ2 v1 ∗ gvar_obs γ1 v1 ∗ gvar_pobs γ1 v1.
  Proof.
    iIntros "Hobs1 (%v1' & %v2 & Hauth1 & Hobs2 & %HR)".
    iDestruct (gvar_pobs_agree with "Hobs1 Hauth1") as %<-.
    subst. iFrame.
  Qed.

  Lemma RelEq_use_trivial γ1 γ2 :
    RelEq γ1 γ2 -∗ ∃ v2, gvar_obs γ2 v2.
  Proof.
    iIntros "(%v1' & %v2 & Hauth1 & Hobs2 & %HR)".
    eauto with iFrame.
  Qed.

  Lemma RelEq_trans_l γ1 γ2 γ3 :
    RelEq γ1 γ2 -∗
    RelEq γ1 γ3 ==∗
    RelEq γ2 γ3.
  Proof.
    iIntros "(%x1 & %x2 & Hobs1 & Hobs2 & <-)".
    iIntros "(%y1 & %y2 & Hobs3 & Hobs4 & <-)".
    iPoseProof (gvar_pobs_agree_2 with "Hobs1 Hobs3") as "<-".
    iMod (gvar_obs_persist with "Hobs2") as "Hobs2".
    iExists _, _. by iFrame.
  Qed.

  Lemma RelEq_trans γ1 γ2 γ3 :
    RelEq γ1 γ2 -∗
    RelEq γ2 γ3 -∗
    RelEq γ1 γ3.
  Proof.
    iIntros "(%x1 & %x2 & Hobs1 & Hobs2 & <-)".
    iIntros "(%y1 & %y2 & Hobs3 & Hobs4 & <-)".
    iPoseProof (gvar_pobs_agree with "Hobs2 Hobs3") as "<-".
    iExists _, _. by iFrame.
  Qed.

  Global Instance RelEq_timeless γ1 γ2 : Timeless (RelEq γ1 γ2).
  Proof. apply _. Qed.
End ghost_variables.
Global Arguments RelEq : simpl never.
Global Typeclasses Opaque RelEq.

Lemma gvar_update_strong `{!ghost_varG Σ RT} {T1 T2 : Type} {γ} {t1 t2 : T1} (t : T2) :
  gvar_auth γ t1 -∗ gvar_obs γ t2 ==∗ gvar_auth γ t ∗ gvar_obs γ t.
Proof. iApply ghost_var_update_halves. Qed.

(** Heterogeneous version *)
Section Rel2.
  Context `{!ghost_varG Σ RT} {T1 T2 : Type}.
  Implicit Types (R : T1 → T2 → Prop).

  Definition Rel2 (γ1 γ2 : gname) (R : T1 → T2 → Prop) : iProp Σ :=
    ∃ v1 v2, gvar_pobs γ1 v1 ∗ gvar_obs γ2 v2 ∗ ⌜R v1 v2⌝.

  Lemma Rel2_use_pobs γ1 γ2 v1 R :
    gvar_pobs (T:=T1) γ1 v1 -∗ Rel2 γ1 γ2 R -∗ ∃ v2 : T2, gvar_obs γ2 v2 ∗ ⌜R v1 v2⌝.
  Proof.
    iIntros "Hobs1 (%v1' & %v2 & Hauth1 & Hobs2 & %HR)".
    iPoseProof (gvar_pobs_agree_2 with "Hauth1 Hobs1") as "->".
    subst. iFrame. done.
  Qed.

  Lemma Rel2_use_obs γ1 γ2 v1 R :
    gvar_obs (T:=T1) γ1 v1 -∗ Rel2 γ1 γ2 R -∗ ∃ v2, gvar_obs γ2 v2 ∗ gvar_obs γ1 v1 ∗ gvar_pobs γ1 v1 ∗ ⌜R v1 v2⌝.
  Proof.
    iIntros "Hobs1 (%v1' & %v2 & Hauth1 & Hobs2 & %HR)".
    iDestruct (gvar_pobs_agree with "Hobs1 Hauth1") as %<-.
    subst. by iFrame.
  Qed.

  Lemma Rel2_use_trivial γ1 γ2 R :
    Rel2 γ1 γ2 R -∗ ∃ v2 : T2, gvar_obs γ2 v2.
  Proof.
    iIntros "(%v1' & %v2 & Hauth1 & Hobs2 & %HR)".
    eauto with iFrame.
  Qed.

  Global Instance Rel2_timeless γ1 γ2 (R : T1 → T2 → Prop) : Timeless (Rel2 γ1 γ2 R).
  Proof. apply _. Qed.
End Rel2.
Section Rel2.
  Context `{!ghost_varG Σ RT}.
  Lemma Rel2_trans {T1 T2 T3} γ1 γ2 γ3 (R1 : T1 → T2 → Prop) (R2 : T2 → T3 → Prop) :
    Rel2 γ1 γ2 R1 -∗
    Rel2 γ2 γ3 R2 -∗
    Rel2 γ1 γ3 (λ a c, ∃ b, R1 a b ∧ R2 b c)%type.
  Proof.
    iIntros "(%x1 & %x2 & Hobs1 & Hobs2 & %Hr1)".
    iIntros "(%y1 & %y2 & Hobs3 & Hobs4 & %Hr2)".
    iPoseProof (gvar_pobs_agree with "Hobs2 Hobs3") as "<-".
    iExists _, _. iFrame.
    iPureIntro. eauto.
  Qed.
End Rel2.
Global Arguments Rel2 : simpl never.
Global Typeclasses Opaque Rel2.
