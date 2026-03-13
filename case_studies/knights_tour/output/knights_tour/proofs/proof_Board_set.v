From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.knights_tour.generated Require Import generated_code_knights_tour generated_specs_knights_tour generated_template_Board_set.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Hint Rewrite -> wrap_to_it_id using can_solve : lithium_rewrite.

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

  - rewrite list_lookup_total_fmap; last solve_goal.
    rewrite length_fmap.
    rewrite Hnestedlen.
    all : solve_goal.
  - rewrite /compose. simpl.
    assert (Hinner :
      ∀ x : list nat,
        ((λ x0 : Z, # x0) <$> (Z.of_nat <$> x)) =
        ((λ y : nat, #(Z.of_nat y)) <$> x)).
    { intros. rewrite -list_fmap_compose. f_equal. }
    setoid_rewrite Hinner.
    apply list_subequiv_fmap.
    apply list_subequiv_insert_in_r; first solve_goal.
    done.
  - eexists. split; first solve_goal.
    f_equiv.
    rewrite list_lookup_total_fmap; last solve_goal.
    rewrite list_lookup_total_insert_eq; last solve_goal.
    rewrite !list_fmap_insert.
    f_equal.
    { rewrite Z2Nat.id; first done. done. }
    rewrite -list_fmap_compose.
    rewrite /compose.
    done.
  - rewrite list_lookup_total_insert.
    case_decide; first rewrite length_insert.
    all: apply Hnestedlen; solve_goal.
Qed.
End proof.
