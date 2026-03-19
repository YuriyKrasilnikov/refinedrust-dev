From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.atomic_std_test.generated Require Import generated_code_atomic_std_test generated_specs_atomic_std_test generated_template_lifecycle_test_i16_new_store_into_inner.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma lifecycle_test_i16_new_store_into_inner_proof (π : thread_id) :
  lifecycle_test_i16_new_store_into_inner_lemma π.
Proof.
  lifecycle_test_i16_new_store_into_inner_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
