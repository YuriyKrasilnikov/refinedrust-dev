From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_examples_max_list.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma examples_max_list_proof (π : thread_id) :
  examples_max_list_lemma π.
Proof.
  examples_max_list_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { case_bool_decide as Heq; revert Heq; normalize_and_simpl_goal_step.
    { rewrite max_list_cmp_def_app max_list_cmp_def_singleton.
      rewrite max_by_r_1.
      { rewrite max_by_r_1; first done.
        apply examples_Min_MIN_minimal. }
      rewrite max_by_r_1; first last.
      { apply examples_Min_MIN_minimal. }
      apply not_ord_gt_iff. by left. }
    { rewrite max_list_cmp_def_app max_list_cmp_def_singleton. simpl.
      rewrite max_by_l_1; first done.
      rewrite max_by_r_1; last apply examples_Min_MIN_minimal.
      done.
    }
  }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
