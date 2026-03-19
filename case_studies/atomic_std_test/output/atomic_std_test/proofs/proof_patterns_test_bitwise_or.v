From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.atomic_std_test.generated Require Import generated_code_atomic_std_test generated_specs_atomic_std_test generated_template_patterns_test_bitwise_or.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma patterns_test_bitwise_or_proof (π : thread_id) :
  patterns_test_bitwise_or_lemma π.
Proof.
  patterns_test_bitwise_or_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
