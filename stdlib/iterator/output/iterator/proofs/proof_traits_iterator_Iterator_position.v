From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_traits_iterator_Iterator_position.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma traits_iterator_Iterator_position_proof (π : thread_id) :
  traits_iterator_Iterator_position_lemma π.
Proof.
  traits_iterator_Iterator_position_prelude.

  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  liInst Hevar_x2 (λ π acc seq it_state '( *[f; counter]),
    ⌜f.ghost = γ⌝ ∗ ⌜counter.ghost = γ0⌝ ∗
    ClosInv π it_state f.cur ∗
    ⌜match acc with
      | inl _ =>
        Forall (λ x, ¬ P x) seq ∧ counter.cur = Z.of_nat (length seq)
      | inr (inl _) =>
          True
      | inr (inr idx) =>
        ∃ e seq', seq = seq' ++ [e] ∧ Forall (λ x, ¬ P x) seq' ∧ P e ∧ counter.cur = Z.of_nat (length seq') ∧ counter.cur = idx
      end⌝
         ∗ True)%I.
  rep <- 40  liRStep; liShow.
  { iRename select (∀ _, _)%I into "Hpres".
    iPoseProof ("Hpres" with "[$] [$]") as "(%pclos & Hpre & ? & Hcl)".
    rep liRStep; liShow.
    liInst Hevar_a pclos.
    rep liRStep; liShow.
    iPoseProof ("Hcl" with "[$]") as "(% & ?)".
    rep liRStep; liShow. }
  rep <-! liRStep; liShow.
  iRevert select (if_iOk _ _). iRevert select (if_iErr _ _).
  rename select (match _ with | inl _ => _ | inr _ => _ end) into Hcase.
  revert Hcase. destruct b as [ | idx]; simpl.
  { rep liRStep; liShow.
    liInst Hevar_x1 x'.
    liInst Hevar_x2 x'0.
    rep liRStep; liShow.
    liInst Hevar_x0 x'1.
    rep liRStep; liShow.
    liInst Hevar_x3 x'2.
    rep liRStep; liShow. }
  { rep <-! liRStep. liShow.
    iRename select (IteratorNextFusedTrans _ _ _ _ _ _) into "Hiter".
    iPoseProof (iterator_next_fused_trans_snoc with "Hiter") as "(%s2 & ? & ?)".
    rep <- 20 liRStep; liShow.
    liInst Hevar_x1 seq'. liInst Hevar_x2 s2.
    rep liRStep; liShow.
    liInst Hevar_e e. liInst Hevar_x0 x'1.
    rep liRStep; liShow.
    liInst Hevar_x3  x'2.
    rep liRStep; liShow. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - rename select (if_Ok _ _) into Hok.
    rename select (if_Err _ _) into Herr.
    destruct ret as [ | idx]; simpl.
    + simpl in *. destruct Hok as (-> & ->).
      split; last lia.
      rewrite Forall_app Forall_singleton. solve_goal.
    + simpl in *. destruct Herr as (-> & -> & ->).
      eexists _, _. split; first done.
      solve_goal.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
