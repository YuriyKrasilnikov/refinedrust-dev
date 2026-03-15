From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.iterators.generated Require Import generated_code_iterators generated_specs_iterators generated_template_test_iterator_3.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma test_iterator_3_proof (π : thread_id) :
  test_iterator_3_lemma π.
Proof.
  test_iterator_3_prelude.

  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  liInst Hevar_Inv (λ _ '(a, b) (clos : plist _ [_]), let x := clos.:0.cur in ⌜0 ≤ a ≤ 10⌝ ∗ ⌜b = 10⌝ ∗ ⌜(x + (b - a))%Z = 10%Z⌝)%I.
  rep <-! liRStep; liShow.
  do 11 (destruct clos_states as [ | [? []] clos_states]; simpl in *; first done).
  destruct clos_states; simpl in *; last done.
  simpl in *. simplify_eq.
  repeat revert select ( _ = _).
  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - case_bool_decide; last done.
    simplify_eq. lia. 
  - case_bool_decide; last done.
    simplify_eq. lia. 
  - case_bool_decide; last done.
    simplify_eq. lia.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
