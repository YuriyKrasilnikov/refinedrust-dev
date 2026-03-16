From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_traits_iterator_Iterator_take.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma traits_iterator_Iterator_take_proof (π : thread_id) :
  traits_iterator_Iterator_take_lemma π.
Proof.
  traits_iterator_Iterator_take_prelude.

  rep <-1 liRStep; liShow.
  iEval (rewrite /traits_iterator_Iterator_Inv/=).
  rep liRStep;liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
