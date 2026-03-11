From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_iterator_decuple_range.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma iterator_decuple_range_proof (π : thread_id) :
  iterator_decuple_range_lemma π.
Proof.
  iterator_decuple_range_prelude.

  rep liRStep; liShow.
  liInst Hevar_Inv (λ _ '(a, b) _, ⌜b = 10⌝)%I.
  rep liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
