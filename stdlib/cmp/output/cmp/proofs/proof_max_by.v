From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.cmp.cmp.generated Require Import generated_code_cmp generated_specs_cmp generated_template_max_by.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma max_by_proof (π : thread_id) :
  max_by_lemma π.
Proof.
  max_by_prelude.

  rep liRStep; liShow.
  liInst Hevar_x1 p.
  rep liRStep; liShow.
  { liInst Hevar_x1 Lt. rep liRStep; liShow. }
  { rep liRStep; liShow. liInst Hevar_x1 x'. rep liRStep; liShow. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
