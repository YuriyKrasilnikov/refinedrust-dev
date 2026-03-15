From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.knights_tour.generated Require Import generated_code_knights_tour generated_specs_knights_tour generated_template_Board_new.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Board_new_proof (π : thread_id) :
  Board_new_lemma π.
Proof.
  Board_new_prelude.

  rep liRStep. liShow.
  {
    liInst Hevar_Inv (λ _ (p : Z * Z) '( *[x]), (⌜(16 * (x))%Z ∈ isize⌝ ∗ ⌜p.2 = size⌝)%I).
    rep liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve.
  { rewrite lookup_total_replicate_2; solve_goal. }
  all: print_remaining_sidecond.
Qed.
End proof.
