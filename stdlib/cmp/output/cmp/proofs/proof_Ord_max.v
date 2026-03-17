From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.cmp.cmp.generated Require Import generated_code_cmp generated_specs_cmp generated_template_Ord_max.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Ord_max_proof (π : thread_id) :
  Ord_max_lemma π.
Proof.
  Ord_max_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { destruct (bool_decide (Ord_Ord Ord_Self_spec_attrs a b = Lt)) eqn:Heq.
    - apply bool_decide_eq_true in Heq. 
      apply Ord_Ord_antisym in Heq.
      rewrite bool_decide_false; first done. 
      rewrite Heq; done.
    - apply bool_decide_eq_false in Heq. 
      destruct (Ord_Ord Ord_Self_spec_attrs a b) eqn:Heq'; [ | done | ].
      + apply correct_ord_eq_leibniz' in Heq'. subst. solve_goal.
      + rewrite bool_decide_true; first done. 
        by apply Ord_Ord_antisym. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
