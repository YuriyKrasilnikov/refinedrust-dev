From refinedrust Require Import typing.
From rrstd.closures.theories Require Export simplification.


Definition FnOnce_Params_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Args_rt: RT) (Output_rt: RT) :=
  (Type).
Definition FnOnce_Pre_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Args_rt: RT) (Output_rt: RT) (FnOnce_Params: (FnOnce_Params_sig (Self_rt) (Args_rt) (Output_rt))) :=
  (thread_id → FnOnce_Params → (RT_xt (Self_rt)) → (RT_xt (Args_rt)) → iProp Σ).
Definition FnOnce_Post_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Args_rt: RT) (Output_rt: RT) (FnOnce_Params: (FnOnce_Params_sig (Self_rt) (Args_rt) (Output_rt))) (FnOnce_Pre: (FnOnce_Pre_sig (Self_rt) (Args_rt) (Output_rt) (FnOnce_Params))) :=
(thread_id → FnOnce_Params → (RT_xt (Self_rt)) → (RT_xt (Args_rt)) → (RT_xt (Output_rt)) → iProp Σ).
Definition FnOnce_PostMut_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Args_rt: RT) (Output_rt: RT) (FnOnce_Params: (FnOnce_Params_sig (Self_rt) (Args_rt) (Output_rt))) (FnOnce_Pre: (FnOnce_Pre_sig (Self_rt) (Args_rt) (Output_rt) (FnOnce_Params))) (FnOnce_Post: (FnOnce_Post_sig (Self_rt) (Args_rt) (Output_rt) (FnOnce_Params) (FnOnce_Pre))) :=
  (thread_id → FnOnce_Params → (RT_xt (Self_rt)) → (RT_xt (Args_rt)) → (RT_xt (Self_rt)) → (RT_xt (Output_rt)) → iProp Σ).
Record FnOnce_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Args_rt : !RT} `{Output_rt : !RT} : Type := mk_FnOnce_spec_attrs {
  FnOnce_Params  : (FnOnce_Params_sig (Self_rt) (Args_rt) (Output_rt));
  FnOnce_Pre  : (FnOnce_Pre_sig (Self_rt) (Args_rt) (Output_rt) (FnOnce_Params));
  FnOnce_Post  : (FnOnce_Post_sig (Self_rt) (Args_rt) (Output_rt) (FnOnce_Params) (FnOnce_Pre));
  FnOnce_PostMut  : (FnOnce_PostMut_sig (Self_rt) (Args_rt) (Output_rt) (FnOnce_Params) (FnOnce_Pre) (FnOnce_Post));
}.

#[global] Arguments FnOnce_spec_attrs : clear implicits.
#[global] Arguments FnOnce_spec_attrs {_ _}.
#[global] Arguments mk_FnOnce_spec_attrs  {_} {_} {_} {_} {_}.

Section closure_props.
  Context `{!refinedrustGS Σ}.
  Context (Clos_rt Args_rt Clos_out_rt : RT).

  Class ClosureHasTrivialPre (fnonce_attrs : FnOnce_spec_attrs Clos_rt Args_rt Clos_out_rt) := closure_has_trivial_pre_proof :
    ∀ π self args, ⊢ ∃ p, FnOnce_Pre fnonce_attrs π p self args.

End closure_props.

Ltac solve_closure_has_trivial_pre :=
  match goal with
  | |- ClosureHasTrivialPre _ _ _ _ =>
    unfold ClosureHasTrivialPre;
    intros ???; prepare_initial_coq_context;
    iStartProof;
    unshelve (repeat liRStep; solve[fail]);
    unshelve (sidecond_solver);
    sidecond_hammer;
    apply inhabitant
  end.

(* TODO: don't have this as hint, but generate instances in the frontend *)
Global Hint Extern 100 (ClosureHasTrivialPre _ _ _ _) =>
  solve_closure_has_trivial_pre : typeclass_instances.
