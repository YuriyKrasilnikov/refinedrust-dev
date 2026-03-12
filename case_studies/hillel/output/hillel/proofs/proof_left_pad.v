From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.hillel.generated Require Import generated_code_hillel generated_specs_hillel generated_template_left_pad.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma left_pad_proof (π : thread_id) :
  left_pad_lemma π.
Proof.
  left_pad_prelude.

  (* !start proof(left_pad) *)
  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  liInst Hevar_num 0%nat.
  rep liRStep; liShow.
  { liInst Hevar_num (S num).
    rep liRStep; liShow. }
  rep liRStep; liShow.
  (* !end proof *)

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  (* !start proof(left_pad) *)
  - unfold size_of_array_in_bytes in *. nia.
  - rewrite list_fmap_compose. repeat f_equiv. lia.
  (* !end proof *)

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
