From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.hillel.generated Require Import generated_code_hillel generated_specs_hillel generated_template_right_pad.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma right_pad_proof (π : thread_id) :
  right_pad_lemma π.
Proof.
  right_pad_prelude.

  (* !start proof(right_pad) *)
  repeat liRStep.
  liInst Hevar_num 0%nat.
  repeat liRStep.
  liInst Hevar_num (S num).
  repeat liRStep; liShow.
  (* !end proof *)

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  (* !start proof(right_pad) *)
  - unfold size_of_array_in_bytes in *. nia.
  (* !end proof *)

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
