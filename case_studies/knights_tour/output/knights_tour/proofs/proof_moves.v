From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.knights_tour.generated Require Import generated_code_knights_tour generated_specs_knights_tour generated_template_moves.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma moves_proof (π : thread_id) :
  moves_lemma π.
Proof.
  moves_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: revert select (_ ∈ _); rewrite !elem_of_cons elem_of_nil; intros Helem.
  all: repeat (destruct Helem as  [Heq | Helem]; [injection Heq; lia | ]); done.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
