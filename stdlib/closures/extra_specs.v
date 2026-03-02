
Section extra_specs.
Context `{RRGS : !refinedrustGS Σ}.
Definition FnOnce_default_attrs {Self_rt Args_rt Output_rt : RT} : FnOnce_spec_attrs (RRGS:=RRGS) Self_rt Args_rt Output_rt :=
  mk_FnOnce_spec_attrs unit%type (λ _ _ _ _ _, True%I) (λ _ _ _ _ _ _, True%I) (λ _ _ _ _, True%I).
Definition FnMut_default_attrs {Self_rt Args_rt Output_rt : RT} :
  FnMut_spec_attrs (RRGS:=RRGS) Self_rt Args_rt Output_rt :=
  mk_FnMut_spec_attrs.
Definition Fn_default_attrs {Self_rt Args_rt Output_rt : RT} :
  Fn_spec_attrs (RRGS:=RRGS) Self_rt Args_rt Output_rt :=
  mk_Fn_spec_attrs.
End extra_specs.

(*Global Arguments FnOnce_Post : simpl never.*)
(*Global Typeclasses Opaque FnOnce_Post.*)

(*Global Arguments FnOnce_Pre : simpl never.*)
(*Global Typeclasses Opaque FnOnce_Pre.*)

(*Global Arguments FnMut_PostMut : simpl never.*)
(*Global Typeclasses Opaque FnMut_PostMut.*)
