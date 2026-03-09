From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.knights_tour.generated Require Import generated_code_knights_tour generated_specs_knights_tour generated_template_Board_set.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma wrap_leq p : 0 ≤ p -> wrap_to_it p usize ≤ p.
Proof.
  unfold wrap_to_it. simpl.
  unfold wrap_unsigned.
  intros H.
  apply Z.mod_le; first apply H.
  unfold int_modulus, bits_per_int, bits_per_byte, bytes_per_int.
  lia.
Qed.

Lemma Board_set_proof (π : thread_id) :
  Board_set_lemma π.
Proof.
  Board_set_prelude.

  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  liInst Hevar_x1 ((fmap (M:= list) Z.of_nat) <$> self0).
  rep <- 2liRStep; liShow.
  liInst Hevar_x2 (<[Z.to_nat (wrap_to_it p usize) := (<[Z.to_nat (wrap_to_it p0 usize):= Z.to_nat v]> (self0 !!! Z.to_nat (wrap_to_it p usize))) ]> self0).
  rep liRStep. 

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve.
  (*assert (Hwrap : p mod int_modulus usize ≤ p).*)

  - assert (Hmod: wrap_to_it p usize ≤ p).
    { apply wrap_leq. solve_goal. }
    lia.
  - Search wrap_to_it.
    rewrite wrap_to_it_id; last solve_goal.
    rewrite wrap_to_it_id; last solve_goal.

    rewrite list_lookup_total_fmap; last solve_goal.
    rewrite length_fmap.
    rewrite H13.
    all : solve_goal.
  - admit.
  - rewrite! wrap_to_it_id; [ | solve_goal..].
    eexists. split; first solve_goal.
    f_equiv.
    rewrite list_lookup_total_fmap; last solve_goal.
    Search lookup_total insert.
    rewrite list_lookup_total_insert_eq; last solve_goal.
    admit.
  - rewrite! wrap_to_it_id; [ | solve_goal..].
    Search lookup_total insert.
    rewrite list_lookup_total_insert.
    case_decide.
    + rewrite length_insert.
      apply H13. solve_goal.
    + apply H13. solve_goal.
Qed.
End proof.
