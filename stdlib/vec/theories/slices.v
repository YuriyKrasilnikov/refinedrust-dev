From refinedrust Require Import typing.

Section slices.
  Context `{!typeGS Σ}.
  Context {rt : RT}.

  (* 
     general way to handle this might be to parameterize ty_syn_type by the metadata.
     i.e., types have a metadata type. 
       for all existing types unit, more complex for others..


     How do we make sure that fat ptrs are always layoutable?
     - have some boundedness requirement on the metadata? 

     What semantic type does metadata have? 
     -> Let's research what kind of metadata we can have.
     -> usually pointer-sized. (usize or a pointer)




     Place types should probably also be parametric in metadata. 
     OfTy should probably only work for stuff without metadata. 
     - if I want to have raw pointers to slices though, I might have to support that.

    
   *)


  Definition FatPtrSynType (meta_st : syn_type) := 
    StructSynType "_fatptr" [("ptr", PtrSynType); ("meta", meta_st)] StructReprRust.

  (*
  Program Definition shr_slice (κ : lft) (ty : type rt) : type (nat * list (place_rfn rt))%type := {|
    ty_own_val π r v := True%I;
    ty_shr κ' π r l := True%I; 
    ty_syn_type := FatPtrSynType (IntSynType usize);
    ty_sidecond := True%I;
    _ty_has_op_type ot mt := True;
    _ty_lfts := [κ] ++ ty_lfts ty;
    _ty_wf_E := ty_wf_E ty ++ ty_outlives_E ty κ;
  |}.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.

  Program Definition mut_slice (κ : lft) (ty : type rt) : type (nat * list (place_rfn rt))%type := {|
    ty_own_val π r v := True%I;
    ty_shr κ' π r l := True%I; 
    ty_syn_type := FatPtrSynType (IntSynType usize);
    ty_sidecond := True%I;
    _ty_has_op_type ot mt := True;
    _ty_lfts := [κ] ++ ty_lfts ty;
    _ty_wf_E := ty_wf_E ty ++ ty_outlives_E ty κ;
  |}.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.
  Next Obligation. Admitted.

  Axiom mut_slice : ∀ (κ : lft) (ty : type rt), type (place_rfn (
    *)


End slices.

