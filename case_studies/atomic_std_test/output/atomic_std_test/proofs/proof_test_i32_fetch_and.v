From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.atomic_std_test.generated Require Import generated_code_atomic_std_test generated_specs_atomic_std_test generated_template_test_i32_fetch_and.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma test_i32_fetch_and_proof (π : thread_id) :
  test_i32_fetch_and_lemma π.
Proof.
  test_i32_fetch_and_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
