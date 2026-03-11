From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.tests.generated Require Import generated_code_tests generated_specs_tests generated_template_iterator_decuple_range_closure0.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma iterator_decuple_range_closure0_proof (π : thread_id) :
  iterator_decuple_range_closure0_lemma π.
Proof.
  iterator_decuple_range_closure0_prelude.

  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  unsafe_unfold_common_caesium_defs. simpl. lia.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
