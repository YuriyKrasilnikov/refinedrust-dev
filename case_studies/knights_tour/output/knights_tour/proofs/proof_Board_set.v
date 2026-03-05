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
  rep liRStep; liShow.
  liInst Hevar_x1 ((fmap (M:= list) Z.of_nat) <$> self0).
  rep <- 2liRStep; liShow.
  liInst Hevar_x2 (<[Z.to_nat (wrap_to_it p usize) := (<[Z.to_nat (wrap_to_it p0 usize):= Z.to_nat v]> (self0 !!! Z.to_nat (wrap_to_it p usize))) ]> self0).
  rep liRStep. 

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
