From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.iterators.generated Require Import generated_code_iterators generated_specs_iterators generated_template_counter.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma counter_proof (π : thread_id) :
  counter_lemma π.
Proof.
  counter_prelude.

  rep <-! liRStep; liShow.
  repeat liRStep; liShow.

  (* instantiate inv.
     gets iterator state and closure state
  *)

  liInst Hevar_Inv (λ _ l (x : (plist (RT_xt ∘ place_rfnRT) [(place_rfn Z * gname)%type : RT])),
  ⌜0 ≤ (x.:0).cur⌝ ∗
  ⌜int_elem_of_it ((x.:0).cur + Z.of_nat ( length l))%Z USize⌝)%I.
  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
