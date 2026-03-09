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
  - specialize H32 with x'1 s.
    have Hmem : *[x'1; s] ∈ _iter_hist_7 ++ -[x'1; s] :: x'.
    { rewrite elem_of_app. right. rewrite elem_of_cons. left. done. }
    apply H32 in Hmem as Hbnd.
    lia.
  - specialize H32 with x'1 s.
    have Hmem : *[x'1; s] ∈ _iter_hist_7 ++ -[x'1; s] :: x'.
    { rewrite elem_of_app. right. rewrite elem_of_cons. left. done. }
    apply H32 in Hmem as Hbnd.
    lia.
  - rewrite Nat2Z.inj_succ.
    change (count + 1 ≤ Z.of_nat (length _iter_hist_7) + 1).
    lia.
  - rewrite Nat2Z.inj_succ.
    change (count ≤ Z.of_nat (length _iter_hist_7) + 1).
    lia.
  all: print_remaining_sidecond.
Qed.
End proof.
