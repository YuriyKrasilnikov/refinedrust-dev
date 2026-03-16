From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_adapters_skip_SkipMIastraits_iterator_Iterator_next.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma adapters_skip_SkipMIastraits_iterator_Iterator_next_proof (π : thread_id) :
  adapters_skip_SkipMIastraits_iterator_Iterator_next_lemma π.
Proof.
  adapters_skip_SkipMIastraits_iterator_Iterator_next_prelude.

  rep <-! liRStep; liShow.
  { (* unfold invariant *)
    iRename select (traits_iterator_Iterator_Inv _ _ _ _) into "Hinv".
    iEval (rewrite /traits_iterator_Iterator_Inv/=) in "Hinv".
    rep <-! liRStep; liShow.
    rep <- 20 liRStep; liShow.
    { liRStep; liShow. liRStep; liShow.
      liRStep; liShow. liRStep; liShow.
      liRStep; liShow. liInst Hevar_s2_inner x'.
      iEval (rewrite /traits_iterator_Iterator_Inv/=).
      rep liRStep; liShow. }
    { rep liRStep; liShow.
      liInst Hevar_seq x'1. liInst Hevar_s2_inner x'.
      rep <- 1 liRStep; liShow.
      iEval (rewrite /traits_iterator_Iterator_Inv/=).
      rep liRStep; liShow. } }
  rep <-! liRStep; liShow.
  { (* unfold invariant *)
    iRename select (traits_iterator_Iterator_Inv _ _ _ _) into "Hinv".
    iEval (rewrite /traits_iterator_Iterator_Inv/=) in "Hinv".
    rep <-! liRStep; liShow.
    rep <- 1 liRStep; liShow.
    { iEval (rewrite /traits_iterator_Iterator_Inv/=).
      rep liRStep; liShow.
      liInst Hevar_seq [].
      rep liRStep; liShow. }
    { iEval (rewrite /traits_iterator_Iterator_Inv/=).
      rep liRStep; liShow.
      liInst Hevar_seq [].
      rep liRStep; liShow. } }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
