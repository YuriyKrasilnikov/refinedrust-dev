From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.atomic_test.generated Require Import generated_code_atomic_test generated_specs_atomic_test generated_template_test_u64_new_swap_into_inner.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma test_u64_new_swap_into_inner_proof (π : thread_id) :
  test_u64_new_swap_into_inner_lemma π.
Proof.
  test_u64_new_swap_into_inner_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
