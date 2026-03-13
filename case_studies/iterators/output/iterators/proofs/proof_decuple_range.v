From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.iterators.generated Require Import generated_code_iterators generated_specs_iterators generated_template_decuple_range.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma decuple_range_proof (π : thread_id) :
  decuple_range_lemma π.
Proof.
  decuple_range_prelude.

  repeat liRStep; liShow.
  liInst Hevar_Inv (λ _ '(a, b) _, ⌜b = 10⌝)%I.
  repeat liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
