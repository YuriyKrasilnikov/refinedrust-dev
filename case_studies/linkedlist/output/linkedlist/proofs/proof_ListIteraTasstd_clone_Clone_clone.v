From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_ListIteraTasstd_clone_Clone_clone.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma ListIteraTasstd_clone_Clone_clone_proof (π : thread_id) :
  ListIteraTasstd_clone_Clone_clone_lemma π.
Proof.
  ListIteraTasstd_clone_Clone_clone_prelude.

  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  liInst Hevar_locs locs.
  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
