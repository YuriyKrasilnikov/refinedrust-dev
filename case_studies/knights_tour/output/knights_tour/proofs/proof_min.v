From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.knights_tour.generated Require Import generated_code_knights_tour generated_specs_knights_tour generated_template_min.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma min_proof (π : thread_id) :
  min_lemma π.
Proof.
  min_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - rewrite elem_of_app. right. solve_goal.
  - rewrite elem_of_app. right. solve_goal.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
