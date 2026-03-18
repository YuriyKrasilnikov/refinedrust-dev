From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_examples_max_list_i32.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma examples_max_list_i32_proof (π : thread_id) :
  examples_max_list_i32_lemma π.
Proof.
  examples_max_list_i32_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { unsafe_unfold_common_caesium_defs. simpl. lia. }
  { case_bool_decide as Heq; revert Heq; normalize_and_simpl_goal_step; first [done |
     rewrite max_list_Z_with_def; solve_goal]. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
