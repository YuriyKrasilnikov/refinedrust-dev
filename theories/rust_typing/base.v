From lrust.lifetime Require Export lifetime.
From lithium Require Export all.
From caesium Require Export proofmode notation syntypes.
From refinedrust Require Export axioms pinned_borrows.
From refinedrust Require Import options.

Definition rrustN := nroot .@ "rrust".
Definition shrN  := rrustN .@ "shr".

Definition lft_userN : namespace := nroot .@ "lft_usr".

(* The "user mask" of the lifetime logic. This needs to be disjoint with ↑lftN.

   If a client library desires to put invariants in lft_userE, then it is
   encouraged to place it in the already defined lft_userN. On the other hand,
   extensions to the model of RustBelt itself (such as gpfsl for
   the weak-mem extension) can require extending [lft_userE] with the relevant
   namespaces. In that case all client libraries need to be re-checked to
   ensure disjointness of [lft_userE] with their masks is maintained where
   necessary. *)
Definition lft_userE : coPset := ↑lft_userN.

Definition rrustE : coPset := ↑rrustN.
Definition lftE : coPset := ↑lftN.
Definition shrE : coPset := ↑shrN.

(* We want unit to be in Type, not in Set *)
Definition unitt : Type := unit.
Definition ttt : unitt := tt.
Notation "()" := ttt.
Notation "()" := unitt : type_scope.

Create HintDb refinedc_typing.

Ltac solve_typing :=
  (typeclasses eauto with refinedc_typing typeclass_instances core).

Global Hint Constructors Forall Forall2 list_elem_of : refinedc_typing.
Global Hint Resolve submseteq_cons submseteq_inserts_l submseteq_inserts_r
  : refinedc_typing.

(* done is there to handle equalities with constants *)
Global Hint Extern 100 (_ ≤ _) => simpl; first [done|lia] : refinedc_typing.
Global Hint Extern 100 (@eq Z _ _) => simpl; first [done|lia] : refinedc_typing.
Global Hint Extern 100 (@eq nat _ _) => simpl; first [done|lia] : refinedc_typing.

Class CoPsetFact (P : Prop) : Prop := copset_fact : P.
(* clear for performance reasons as there can be many hypothesis and they should not be needed for the goals which occur *)
Local Definition coPset_disjoint_empty_r := disjoint_empty_r (C:=coPset).
Local Definition coPset_disjoint_empty_l := disjoint_empty_l (C:=coPset).
Global Hint Extern 1 (CoPsetFact ?P) => (change P; clear; eauto using coPset_disjoint_empty_r, coPset_disjoint_empty_r with solve_ndisj) : typeclass_instances.


Class LayoutSizeEq (ly1 ly2 : layout) := layout_size_eq_proof : ly_size ly1 = ly_size ly2.
Global Instance layout_size_eq_refl ly : LayoutSizeEq ly ly.
Proof. constructor. Qed.

Class LayoutSizeLe (ly1 ly2 : layout) := layout_size_le_proof : ly_size ly1 ≤ ly_size ly2.
Global Instance layout_size_le_refl ly : LayoutSizeLe ly ly.
Proof. constructor. Qed.

(** Block typeclass resolution for an argument *)
Definition TCNoResolve (P : Type) := P.
Global Typeclasses Opaque TCNoResolve.

(** [TCForall] but for [Type] instead of [Prop] *)
Inductive TCTForall {A} (P : A → Type) : list A → Type :=
  | TCTForall_nil : TCTForall P []
  | TCTForall_cons x xs : P x → TCTForall P xs → TCTForall P (x :: xs).
Existing Class TCTForall.
Global Existing Instance TCTForall_nil.
Global Existing Instance TCTForall_cons.
Global Hint Mode TCTForall ! ! ! : typeclass_instances.

(** Solve a goal with [set_solver] *)
Class TCSetSolver (P : Prop) : Prop := set_solver_proof : P.
Global Hint Extern 1 (TCSetSolver ?P) => (change P; set_solver) : typeclass_instances.

Class TCFastListElemOf (P : Prop) : Prop := simple_list_elem_of_proof : P.

(* Very simple list containment solver. *)
Ltac simple_list_elem_solver :=
  repeat lazymatch goal with
  | |- ?a ∈ ?a :: ?L =>
      apply elem_of_cons; by left
  | |- ?a ∈ _ :: ?L =>
      apply elem_of_cons; right
  | |- ?a ∈ _ ++ ?L =>
      apply elem_of_app; right
  end.
Global Hint Extern 1 (TCFastListElemOf ?P) => (change P; simple_list_elem_solver) : typeclass_instances.

Declare Scope printing_sugar.

(* Hints for unfolding type definitions used by some parts of the automation (e.g. [elctx_simplify]). *)
Create HintDb tyunfold.

(* Marker to prevent Lithium's machinery from simplifying a hypothesis. *)
Definition introduce_direct {Σ} (P : iProp Σ) := P.
Global Arguments introduce_direct : simpl never.
Global Typeclasses Opaque introduce_direct.

(* We override the lifetime logic's version with a direct fixpoint version for nicer unfolding + computation. *)
Fixpoint lft_intersect_list (κs : list lft) : lft :=
    match κs with
    | [] => static
    | κ :: κs => κ ⊓ lft_intersect_list κs
    end.
Lemma lft_intersect_list_iff κs :
  lft_intersect_list κs = lifetime.lft_intersect_list κs.
Proof.
  induction κs as [ | κ κs IH]; simpl; first done.
  destruct κs as [ | κ' κs]; simpl.
  { rewrite right_id //. }
  simpl in IH. rewrite IH //.
Qed.

Lemma lft_intersect_list_elem_of_incl_syn (κs : list lft) κ :
  κ ∈ κs → lft_intersect_list κs ⊑ˢʸⁿ κ.
Proof.
  rewrite lft_intersect_list_iff. apply lft_intersect_list_elem_of_incl_syn.
Qed.
Lemma lft_intersect_list_elem_of_incl `{!invGS Σ} {userE : coPset} `{!lftGS Σ userE} (κs : list lft) κ :
  κ ∈ κs → ⊢ lft_intersect_list κs ⊑ κ.
Proof.
  rewrite lft_intersect_list_iff. apply lft_intersect_list_elem_of_incl.
Qed.

(** * Error handling *)
Notation Ok x := (inl x) (only parsing).
Notation Err x := (inr x) (only parsing).

Notation result A B := (sum A B) (only parsing).

Definition if_Ok {A B} (x : result A B) (ϕ : A → Prop) : Prop :=
  match x with
  | Ok x => ϕ x
  | _ => True
  end.
Definition if_Err {A B} (x : result A B) (ϕ : B → Prop) : Prop :=
  match x with
  | Err x => ϕ x
  | _ => True
  end.

Definition is_Ok {A B} (x : result A B) :=
  ∃ y : A, x = Ok y.
Global Instance is_Ok_dec {A B} (x : result A B) : Decision (is_Ok x).
Proof.
  destruct x.
  - left. eexists _. done.
  - right. intros [y Hx]. naive_solver.
Defined.

Definition is_Err {A B} (x : result A B) :=
  ∃ y : B, x = Err y.
Global Instance is_Err_dec {A B} (x : result A B) : Decision (is_Err x).
Proof.
  destruct x.
  - right. intros [y Hx]. naive_solver.
  - left. eexists _. done.
Defined.


(** The same for Iris *)
Section iris.
Context `{!refinedcG Σ}.

Definition if_iOk {A B} (x : result A B) (ϕ : A → iProp Σ) : iProp Σ :=
  match x with
  | Ok x => ϕ x
  | _ => True
  end.
Definition if_iErr {A B} (x : result A B) (ϕ : B → iProp Σ) : iProp Σ :=
  match x with
  | Err x => ϕ x
  | _ => True
  end.
End iris.


Definition if_Some {A} (x : option A) (ϕ : A → Prop) : Prop :=
  match x with
  | Some x => ϕ x
  | _ => True
  end.
Definition if_None {A} (x : option A) (ϕ : Prop) : Prop :=
  match x with
  | None => ϕ
  | _ => True
  end.

(** The same for Iris *)
Section iris.
Context `{!refinedcG Σ}.

Definition if_iSome {A} (x : option A) (ϕ : A → iProp Σ) : iProp Σ :=
  match x with
  | Some x => ϕ x
  | _ => True
  end.
Definition if_iNone {A} (x : option A) (ϕ : iProp Σ) : iProp Σ :=
  match x with
  | None => ϕ
  | _ => True
  end.
End iris.
Global Typeclasses Opaque if_iSome.
Global Typeclasses Opaque if_iNone.

(* TODO: upstream: overwritten to allow for more parameters *)
Ltac my_f_equiv :=
  (* Simplify away [flip], they would get in the way later. *)
  clean_flip;
  (* Find out what kind of goal we have, and try to make progress. *)
  match goal with
  (* Similar to [f_equal] also handle the reflexivity case. *)
  | |- _ ?x ?x => fast_reflexivity
  (* Making progress on [pointwise_relation] is as simple as introducing the variable. *)
  | |- pointwise_relation _ _ _ _ => intros ?
  (* We support matches on both sides, *if* they concern the same variable, or
     terms in some relation. *)
  | |- ?R (match ?x with _ => _ end) (match ?x with _ => _ end) =>
    destruct x
  | H : ?R ?x ?y |- ?R2 (match ?x with _ => _ end) (match ?y with _ => _ end) =>
     destruct H
  (* First assume that the arguments need the same relation as the result. We
  check the most restrictive pattern first: [(?f _) (?f _)] requires all but the
  last argument to be syntactically equal. *)
  | |- ?R (?f _) (?f _) => simple apply (_ : Proper (R ==> R) f)
  | |- ?R (?f _ _) (?f _ _) => simple apply (_ : Proper (R ==> R ==> R) f)
  | |- ?R (?f _ _ _) (?f _ _ _) => simple apply (_ : Proper (R ==> R ==> R ==> R) f)
  | |- ?R (?f _ _ _ _) (?f _ _ _ _) => simple apply (_ : Proper (R ==> R ==> R ==> R ==> R) f)
  | |- ?R (?f _ _ _ _ _) (?f _ _ _ _ _) => simple apply (_ : Proper (R ==> R ==> R ==> R ==> R ==> R) f)
  (* For the case in which R is polymorphic, or an operational type class,
  like equiv. *)
  | |- (?R _) (?f _) (?f _) => simple apply (_ : Proper (R _ ==> R _) f)
  | |- (?R _ _) (?f _) (?f _) => simple apply (_ : Proper (R _ _ ==> R _ _) f)
  | |- (?R _ _ _) (?f _) (?f _) => simple apply (_ : Proper (R _ _ _ ==> R _ _ _) f)

  | |- (?R _) (?f _ _) (?f _ _) => simple apply (_ : Proper (R _ ==> R _ ==> R _) f)
  | |- (?R _ _) (?f _ _) (?f _ _) => simple apply (_ : Proper (R _ _ ==> R _ _ ==> R _ _) f)
  | |- (?R _ _ _) (?f _ _) (?f _ _) => simple apply (_ : Proper (R _ _ _ ==> R _ _ _ ==> R _ _ _) f)

  | |- (?R _) (?f _ _ _) (?f _ _ _) => simple apply (_ : Proper (R _ ==> R _ ==> R _ ==> R _) f)
  | |- (?R _ _) (?f _ _ _) (?f _ _ _) => simple apply (_ : Proper (R _ _ ==> R _ _ ==> R _ _ ==> R _ _) f)
  | |- (?R _ _ _) (?f _ _ _) (?f _ _ _) => simple apply (_ : Proper (R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _) f)

  | |- (?R _) (?f _ _ _ _) (?f _ _ _ _) => simple apply (_ : Proper (R _ ==> R _ ==> R _ ==> R _ ==> R _) f)
  | |- (?R _ _) (?f _ _ _ _) (?f _ _ _ _) => simple apply (_ : Proper (R _ _ ==> R _ _ ==> R _ _ ==> R _ _ ==> R _ _) f)
  | |- (?R _ _ _) (?f _ _ _ _) (?f _ _ _ _) => simple apply (_ : Proper (R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _) f)

  | |- (?R _) (?f _ _ _ _ _) (?f _ _ _ _ _) => simple apply (_ : Proper (R _ ==> R _ ==> R _ ==> R _ ==> R _ ==> R _) f)
  | |- (?R _ _) (?f _ _ _ _ _) (?f _ _ _ _ _) => simple apply (_ : Proper (R _ _ ==> R _ _ ==> R _ _ ==> R _ _ ==> R _ _ ==> R _ _) f)
  | |- (?R _ _ _) (?f _ _ _ _ _) (?f _ _ _ _ _) => simple apply (_ : Proper (R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _ ==> R _ _ _) f)
  (* In case the function symbol differs, but the arguments are the same, maybe
     we have a relation about those functions in our context that we can simply
     apply. (The case where the arguments differ is a lot more complicated; with
     the way we typically define the relations on function spaces it further
     requires [Proper]ness of [f] or [g]). *)
  | H : _ ?f ?g |- ?R (?f ?x) (?g ?x) => solve [simple apply H]
  | H : _ ?f ?g |- ?R (?f ?x ?y) (?g ?x ?y) => solve [simple apply H]

  (* Fallback case: try to infer the relation, and allow the function to not be
     syntactically the same on both sides. Unfortunately, very often, it will
     turn the goal into a Leibniz equality so we get stuck. Furthermore, looking
     for instances in this order will mean that Coq will try to unify the
     remaining arguments that we have not explicitly generalized, which can be
     very slow -- but if we go for the opposite order, we will hit the Leibniz
     equality fallback instance even more often. *)
  (* TODO: Can we exclude that Leibniz equality instance? *)
  | |- ?R (?f _) _ => simple apply (_ : Proper (_ ==> R) f)
  | |- ?R (?f _ _) _ => simple apply (_ : Proper (_ ==> _ ==> R) f)
  | |- ?R (?f _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _ _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _ _ _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> _ ==> _ ==> _ ==> R) f)
  end;
  (* Similar to [f_equal] immediately solve trivial goals *)
  try fast_reflexivity.
