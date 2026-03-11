From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_iterator_all_zero.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma iterator_all_zero_proof (π : thread_id) :
  iterator_all_zero_lemma π.
Proof.
  iterator_all_zero_prelude.

  repeat liRStep; liShow.
  rewrite snd_zip; last solve_goal.
  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
