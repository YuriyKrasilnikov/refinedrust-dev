From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_iterator_test_iterator_2.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma iterator_test_iterator_2_proof (π : thread_id) :
  iterator_test_iterator_2_lemma π.
Proof.
  iterator_test_iterator_2_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { rename select (Forall2 _ _ _) into Hf.
    opose proof* Forall2_length as Hlen; first apply Hf.
    do 11 (try destruct x' as [ | ? x']; simpl in *; first try lia); last lia.
    apply Forall2_Forall2_cb in Hf.
    move: Hf. cbn.
    naive_solver. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
