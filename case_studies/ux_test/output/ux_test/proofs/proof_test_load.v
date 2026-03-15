From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.ux_test.generated Require Import generated_code_ux_test generated_specs_ux_test generated_template_test_load.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma test_load_proof (π : thread_id) :
  test_load_lemma π.
Proof.
  test_load_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
