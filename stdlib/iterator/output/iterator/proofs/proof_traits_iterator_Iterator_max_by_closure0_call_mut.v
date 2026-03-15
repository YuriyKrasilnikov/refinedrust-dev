From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_traits_iterator_Iterator_max_by_closure0_call_mut.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma traits_iterator_Iterator_max_by_closure0_call_mut_proof (π : thread_id) :
  traits_iterator_Iterator_max_by_closure0_call_mut_lemma π.
Proof.
  traits_iterator_Iterator_max_by_closure0_call_mut_prelude.

  rep liRStep; liShow.
  liInst Hevar_x3 pclos.
  rep liRStep; liShow.
  liInst Hevar_capture_compare__new x'.
  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. 1-3: sidecond_solver.
  { admit. }  (* TODO call contract *)
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Admitted.
End proof.
