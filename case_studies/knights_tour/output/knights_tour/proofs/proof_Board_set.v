From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.knights_tour.generated Require Import generated_code_knights_tour generated_specs_knights_tour generated_template_Board_set.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Board_set_proof (π : thread_id) :
  Board_set_lemma π.
Proof.
  Board_set_prelude.

  rep <-! liRStep; liShow.
  rep <- 2 liRStep; liShow.
  liInst Hevar_x2 (<[Z.to_nat (wrap_to_it p usize) := (<[Z.to_nat (wrap_to_it p0 usize):= v]> (self0 !!! Z.to_nat (wrap_to_it p usize))) ]> self0).
  rep liRStep. 

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.

  - rewrite Hnestedlen; solve_goal.
  - apply list_subequiv_fmap.
    apply list_subequiv_insert_in_r; first solve_goal.
    done.
  - eexists. split; first solve_goal.
    f_equiv.
    rewrite list_lookup_total_insert_eq; last solve_goal.
    rewrite !list_fmap_insert. done.
  - rewrite list_lookup_total_insert.
    case_decide; first rewrite length_insert.
    all: apply Hnestedlen; solve_goal.
Qed.
End proof.
