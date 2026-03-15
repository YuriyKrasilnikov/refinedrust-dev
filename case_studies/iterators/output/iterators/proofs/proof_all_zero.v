From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.iterators.generated Require Import generated_code_iterators generated_specs_iterators generated_template_all_zero.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma all_zero_proof (π : thread_id) :
  all_zero_lemma π.
Proof.
  all_zero_prelude.

  repeat liRStep; liShow.
  { rewrite fmap_app; rep liRStep. } 
  rewrite snd_zip; last solve_goal.
  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
