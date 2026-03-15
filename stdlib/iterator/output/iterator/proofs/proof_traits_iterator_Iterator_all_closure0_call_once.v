From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_traits_iterator_Iterator_all_closure0_call_once.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma traits_iterator_Iterator_all_closure0_call_once_proof (π : thread_id) :
  traits_iterator_Iterator_all_closure0_call_once_lemma π.
Proof.
  traits_iterator_Iterator_all_closure0_call_once_prelude.

  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  liInst Hevar_x3 pclos.
  rep liRStep; liShow.
  liInst Hevar_capture_f__new x'.
  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: admit. (* TODO: call contract *)
  Unshelve. all: print_remaining_sidecond.
Admitted.
End proof.
