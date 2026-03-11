From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.result.result.generated Require Import generated_code_result generated_specs_result generated_template_Result_TE_map_err.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Result_TE_map_err_proof (π : thread_id) :
  Result_TE_map_err_lemma π.
Proof.
  Result_TE_map_err_prelude.

  rep <-! liRStep; liShow.
  { rep liRStep; liShow.
    liInst Hevar_x1 p.
    rep liRStep; liShow. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
