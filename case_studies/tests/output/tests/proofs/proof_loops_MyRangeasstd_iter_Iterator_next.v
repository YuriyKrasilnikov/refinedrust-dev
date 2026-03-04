From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_loops_MyRangeasstd_iter_Iterator_next.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma loops_MyRangeasstd_iter_Iterator_next_proof (π : thread_id) :
  loops_MyRangeasstd_iter_Iterator_next_lemma π.
Proof.
  loops_MyRangeasstd_iter_Iterator_next_prelude.

  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
