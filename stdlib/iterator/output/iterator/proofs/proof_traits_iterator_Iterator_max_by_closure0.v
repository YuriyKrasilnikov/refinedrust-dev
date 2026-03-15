From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_traits_iterator_Iterator_max_by_closure0.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma traits_iterator_Iterator_max_by_closure0_proof (π : thread_id) :
  traits_iterator_Iterator_max_by_closure0_lemma π.
Proof.
  traits_iterator_Iterator_max_by_closure0_prelude.

  rep <-! liRStep; liShow.
  apply_update (updateable_copy_lft "vlft6" "plft8").
  rep liRStep; liShow.
  liInst Hevar_x1 pclos.
  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
