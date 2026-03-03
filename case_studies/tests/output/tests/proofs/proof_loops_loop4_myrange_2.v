From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_loops_loop4_myrange_2.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma loops_loop4_myrange_2_proof (π : thread_id) :
  loops_loop4_myrange_2_lemma π.
Proof.
  loops_loop4_myrange_2_prelude.

  rep liRStep; liShow.
  
  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { simpl.
    admit. }
  Unshelve. all: print_remaining_sidecond.
(*Qed.*)
Admitted.
End proof.
