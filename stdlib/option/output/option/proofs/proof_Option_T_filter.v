From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.option.option.generated Require Import generated_code_option generated_specs_option generated_template_Option_T_filter.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Option_T_filter_proof (π : thread_id) :
  Option_T_filter_lemma π.
Proof.
  Option_T_filter_prelude.

  rep <-! liRStep; liShow.
  { rep liRStep; liShow.
    liInst Hevar_x1 p.
    repeat liRStep; liShow. }
  repeat liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
