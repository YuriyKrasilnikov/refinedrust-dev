From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.knights_tour.generated Require Import generated_code_knights_tour generated_specs_knights_tour generated_template_Board_count_degree.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Board_count_degree_proof (π : thread_id) :
  Board_count_degree_lemma π.
Proof.
  Board_count_degree_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve.
  all: cbn.
  all: rename select (∀ a b : Z, _ -> a ≤ 2 ∧ _) into Hbound.
  - have Hmem : *[x'1; s] ∈ _iter_hist_7 ++ -[x'1; s] :: x'.
    { rewrite elem_of_app. right. rewrite elem_of_cons. left. done. }
    apply Hbound in Hmem. lia.
  - specialize Hbound with x'1 s.
    have Hmem : *[x'1; s] ∈ _iter_hist_7 ++ -[x'1; s] :: x'.
    { rewrite elem_of_app. right. rewrite elem_of_cons. left. done. }
    apply Hbound in Hmem. lia.
Qed.
End proof.
