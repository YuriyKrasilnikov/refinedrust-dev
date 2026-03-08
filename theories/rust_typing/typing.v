From caesium Require Export tactics.
From refinedrust Require Export static type program_rules int int_rules unit struct.struct mut_ref.mut_ref shr_ref.shr_ref functions uninit programs enum maybe_uninit alias_ptr fixpoint existentials existentials_na existentials_atomic atomic_int atomic_int_rules atomic_bool_rules array.array value generics xmap.
From refinedrust Require Export automation.loc_eq manual automation.
From iris.proofmode Require Import coq_tactics reduction string_ident.
From refinedrust Require Export automation.simpl.
From refinedrust Require Export options.

(* In my experience, this has led to more problems with [normalize_autorewrite] rewriting below definitions too eagerly. *)
#[export] Unset Keyed Unification.

(* For some reason, we need to declare this instance here for stuff to work, despite exporting [simpl] as the last thing above! So weird! *)
Global Instance simpl_exist_plist_cons' {X : Type} (F : X → Type) (x : X) xs (Q : plist F (x :: xs) → Prop) :
SimplExist (plist F (x :: xs)) Q (∃ p : F x, ∃ ps : plist F xs, Q (p -:: ps)).
Proof.
  (*apply simpl_exist_plist_cons.*)
  intros (p & ps & Hx). exists (p -:: ps). done.
Qed.
Global Instance simpl_forall_plist_cons {X} (F : X → Type) x xs T :
  SimplForall (plist F (x :: xs)) 1 T (∀ (a : F x) (s : plist F xs), T (a -:: s)).
Proof. intros Q [? ?]. apply Q. Qed.
Global Instance simpl_forall_plist_nil {X} (F : X → Type) T :
  SimplForall (plist F []) 0 T (T -[]).
Proof. intros Q []. apply Q. Qed.
Global Instance simpl_forall_hlist_cons {X} (F : X → Type) x xs T :
  SimplForall (hlist F (x :: xs)) 1 T (∀ (a : F x) (s : hlist F xs), T (a +:: s)).
Proof. intros Q a. inv_hlist a. intros. apply Q. Qed.
Global Instance simpl_forall_hlist_nil {X} (F : X → Type) T :
  SimplForall (hlist F []) 0 T (T +[]).
Proof. intros Q a. inv_hlist a. apply Q. Qed.

Global Open Scope Z_scope.

Notation Obs := gvar_pobs.

Hint Extern 10 (Inhabited (RT_xt _)) => simpl; apply ty_xt_inhabited; done : typeclass_instances.

(** extend [solve_type_proper] *)
Ltac solve_type_proper_hook ::=
  match goal with
    | |- ltype_own (OfTy _) ?bk _ _ _ ≡{_}≡ ltype_own (OfTy _) ?bk _ _ _ =>
      match bk with
      | Shared _ => apply ofty_own_ne_shared; try apply _
      | Uniq _ _ => apply ofty_own_contr_uniq; try apply _
      | Owned => apply ofty_own_ne_owned; try apply _
      end
    | |- guarded _ _ ≡{_}≡ guarded _ _ =>
      apply guarded_dist; intros
  end.

(** Bundle for all ghost state we need *)
Class refinedrustGS Σ := {
  refinedrust_typeGS :: typeGS Σ;
  refinedrust_staticGS :: staticGS Σ;
}.

Ltac instantiate_benign_universals term ::=
  lazymatch type of term with
  | ∀ (_ : gFunctors) (_ : refinedrustGS _), _ =>
      instantiate_benign_universals uconstr:(term _ _)
  | ∀ _ : typeGS _, _ =>
      instantiate_benign_universals uconstr:(term ltac:(refine _))
  | ∀ _ : staticGS _, _ =>
      instantiate_benign_universals uconstr:(term ltac:(refine _))
  | ∀ _ : refinedrustGS _, _ =>
      instantiate_benign_universals uconstr:(term ltac:(refine _))
  | _ =>
      constr:(term)
  end.


Notation "x '.ghost'" := (x.2) (at level 8, only parsing).
Notation "x '.cur'" := (x.1) (at level 8, only parsing).

Notation "'i8'" := I8.
Notation "'i16'" := I16.
Notation "'i32'" := I32.
Notation "'i64'" := I64.
Notation "'i128'" := I128.
Notation "'isize'" := ISize.

Notation "'u8'" := U8.
Notation "'u16'" := U16.
Notation "'u32'" := U32.
Notation "'u64'" := U64.
Notation "'u128'" := U128.
Notation "'usize'" := USize.

(*Global Typeclasses Opaque enum_t.*)
(*Global Typeclasses Opaque active_union_t.*)
(*Global Typeclasses Opaque array_t.*)
(*Global Typeclasses Opaque offset_ptr_t.*)


(*Global Typeclasses Opaque shr_ref.*)
(*Global Typeclasses Opaque mut_ref.*)
(*Global Typeclasses Opaque unit_t.*)
(*Global Typeclasses Opaque struct_t.*)
(*Global Typeclasses Opaque int.*)
(*Global Typeclasses Opaque char_t.*)
(*Global Typeclasses Opaque bool_t.*)
(*Global Typeclasses Opaque ex_plain_t.*)
(*Global Typeclasses Opaque bytewise.*)
(*Global Typeclasses Opaque value_t.*)


(*Global Typeclasses Opaque mk_ex_inv_def.*)
(*Global Typeclasses Opaque mk_pers_ex_inv_def.*)
