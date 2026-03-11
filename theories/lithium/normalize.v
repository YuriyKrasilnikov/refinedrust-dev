From lithium Require Export base.
From lithium Require Import hooks pure_definitions.

(** This file provides rewrite-based normalization infrastructure for
pure sideconditions. *)

(** * General normalization infrastructure *)
Lemma tac_normalize_goal (P1 P2 : Prop):
  P2 = P1 → P1 → P2.
Proof. by move => ->. Qed.
Lemma tac_normalize_goal_and (P1 P2 T : Prop):
  P2 = P1 → P1 ∧ T → P2 ∧ T.
Proof. by move => ->. Qed.
Lemma tac_normalize_goal_impl (P1 P2 T : Prop):
  P2 = P1 → (P1 → T) → (P2 → T).
Proof. by move => ->. Qed.

(* TODO: don't do anything if there is no progress? *)
Ltac normalize_goal :=
  notypeclasses refine (tac_normalize_goal _ _ _ _); [normalize_hook|].
Ltac normalize_goal_and :=
  notypeclasses refine (tac_normalize_goal_and _ _ _ _ _); [normalize_hook|].
Ltac normalize_goal_impl :=
  notypeclasses refine (tac_normalize_goal_impl _ _ _ _ _); [normalize_hook|].

(** * First version of normalization based on [autorewrite] *)
Create HintDb lithium_rewrite discriminated.

#[export] Hint Rewrite @drop_0 @take_ge using can_solve : lithium_rewrite.
#[export] Hint Rewrite @take_app_le @drop_app_ge using can_solve : lithium_rewrite.
#[export] Hint Rewrite length_seq length_seqZ @length_insert @length_app @length_fmap @length_rotate @length_replicate @length_drop @length_take : lithium_rewrite.
#[export] Hint Rewrite <- @fmap_take @fmap_drop : lithium_rewrite.
#[export] Hint Rewrite @list_insert_fold : lithium_rewrite.
#[export] Hint Rewrite @list_insert_insert_eq : lithium_rewrite.
#[export] Hint Rewrite @drop_drop : lithium_rewrite.
#[export] Hint Rewrite @tail_replicate @take_replicate @drop_replicate : lithium_rewrite.
#[export] Hint Rewrite <- @app_assoc @cons_middle : lithium_rewrite.
#[export] Hint Rewrite @app_nil_r @rev_involutive : lithium_rewrite.
#[export] Hint Rewrite <- @list_fmap_insert : lithium_rewrite.
#[export] Hint Rewrite -> @list_lookup_fmap : lithium_rewrite.
#[export] Hint Rewrite -> @list_fmap_id : lithium_rewrite.
#[export] Hint Rewrite <- @list_fmap_compose : lithium_rewrite.
#[export] Hint Rewrite -> @lookup_take : lithium_rewrite.
#[export] Hint Rewrite -> @take_take @drop_drop : lithium_rewrite.
#[export] Hint Rewrite Nat.sub_0_r Nat.add_0_r Nat.sub_diag : lithium_rewrite.
#[export] Hint Rewrite Nat2Z.id Nat2Z.inj_add Nat2Z.inj_mul : lithium_rewrite.
#[export] Hint Rewrite Z2Nat.inj_mul Z2Nat.inj_sub Z2Nat.id using can_solve : lithium_rewrite.
#[export] Hint Rewrite Nat.succ_pred_pos using can_solve : lithium_rewrite.
#[export] Hint Rewrite Nat.add_assoc Nat.min_id : lithium_rewrite.
#[export] Hint Rewrite Z.quot_mul using can_solve : lithium_rewrite.
#[export] Hint Rewrite <-Nat.mul_sub_distr_r Z.mul_add_distr_r Z.mul_sub_distr_r : lithium_rewrite.
#[export] Hint Rewrite @bool_decide_eq_x_x_true @if_bool_decide_eq_branches : lithium_rewrite.
#[export] Hint Rewrite @bool_decide_eq_true_2 @bool_decide_eq_false_2 using fast_done : lithium_rewrite.
#[export] Hint Rewrite bool_to_Z_neq_0_bool_decide bool_to_Z_eq_0_bool_decide : lithium_rewrite.
#[export] Hint Rewrite keep_factor2_is_power_of_two keep_factor2_min_eq using can_solve : lithium_rewrite.
#[export] Hint Rewrite keep_factor2_min_1 keep_factor2_twice : lithium_rewrite.
#[export] Hint Rewrite @decide_True using can_solve : lithium_rewrite.
#[export] Hint Rewrite @decide_False using can_solve : lithium_rewrite.

#[export] Hint Rewrite -> Z2Nat.inj_0 : lithium_rewrite.
#[export] Hint Rewrite -> Z.sub_0_r Z.add_0_r Z.sub_0_l Z.add_0_l : lithium_rewrite.
#[export] Hint Rewrite -> Z.add_1_r Z.add_1_l Nat.add_1_r Nat.add_1_l : lithium_rewrite.
#[export] Hint Rewrite Z.mul_1_l Z.mul_1_r Nat.mul_1_l Nat.mul_1_r : lithium_rewrite.

#[export] Hint Rewrite -> Nat.min_l Nat.min_r using lia : lithium_rewrite.
#[export] Hint Rewrite -> Nat.max_l Nat.max_r using lia : lithium_rewrite.
#[export] Hint Rewrite -> Z.min_l Z.min_r using lia : lithium_rewrite.
#[export] Hint Rewrite -> Z.max_l Z.max_r using lia : lithium_rewrite.

#[export] Hint Rewrite Nat.add_sub : lithium_rewrite.

#[export] Hint Rewrite @lookup_total_drop : lithium_rewrite.


(* fmap_app is not a good idea. *)
(*#[export] Hint Rewrite -> @fmap_app : lithium_rewrite.*)
#[export] Hint Rewrite -> @length_zip : lithium_rewrite.
#[export] Hint Rewrite -> @snd_zip using can_solve : lithium_rewrite.
#[export] Hint Rewrite -> @fst_zip using can_solve : lithium_rewrite.


(** Classes for simplifying a particular term *)
Class NormalizeTermProgress {A} (a b : A) := normalize_term_progress_proof : a = b.
Global Hint Mode NormalizeTermProgress + + - : typeclass_instances.

Hint Extern 10 (NormalizeTermProgress ?a ?b) =>
  progress autorewrite with lithium_rewrite; reflexivity : typeclass_instances.

Class NormalizeTerm {A} (a b : A) := normalize_term_proof : a = b.
Global Hint Mode NormalizeTerm + + - : typeclass_instances.

Hint Extern 10 (NormalizeTerm ?a ?b) =>
  autorewrite with lithium_rewrite; reflexivity : typeclass_instances.

(** ** Additional normalization instances *)




Local Definition lookup_insert_gmap A K `{Countable K} := lookup_insert_eq (M := gmap K) (A := A).
#[export] Hint Rewrite lookup_insert_gmap : lithium_rewrite.

(** * Second version of normalization based on typeclasses *)
Class NormalizeWalk {A} (progress : bool) (a b : A) : Prop := normalize_walk: a = b.
Class Normalize {A} (progress : bool) (a b : A) : Prop := normalize: a = b.
Global Hint Mode NormalizeWalk + - + - : typeclass_instances.
Global Hint Mode Normalize + - + - : typeclass_instances.
Global Instance normalize_walk_protected A (x : A) :
  NormalizeWalk false (protected x) (protected x) | 10.
Proof. done. Qed.
(* TODO: This does not go under binders *)
Lemma normalize_walk_app A B (f f' : A → B) x x' r p1 p2 p3
      `{!NormalizeWalk p1 f f'}
      `{!NormalizeWalk p2 x x'} `{!TCEq (p1 || p2) true}
      `{!Normalize p3 (f' x') r}:
  NormalizeWalk true (f x) r.
Proof. unfold NormalizeWalk, Normalize in *. naive_solver. Qed.
Global Hint Extern 50 (NormalizeWalk _ (?f ?x) _) => class_apply normalize_walk_app : typeclass_instances.
Global Instance normalize_walk_end_progress A (x x' : A) `{!Normalize true x x'} :
  NormalizeWalk true x x' | 100.
Proof. done. Qed.
Global Instance normalize_walk_end A (x : A) :
  NormalizeWalk false x x | 101.
Proof. done. Qed.
Global Instance normalize_end A (x : A): Normalize false x x | 100.
Proof. done. Qed.

(*Lemma normalize_take_S_r_total {A} `{!Inhabited A} (l : list A) (n : nat) :*)
  (*CanSolve ((n < length l)%nat) →*)
  (*Normalize true (take (S n) l) (take n l ++ [l !!! n]).*)
(*Proof.*)
  (*unfold CanSolve.*)
  (*intros Hlt. apply take_S_r.*)
  (*by apply list_lookup_lookup_total_lt.*)
(*Qed.*)
(*#[export] Hint Extern 5 (Normalize _ (take (S _) _) _) => class_apply normalize_take_S_r_total : typeclass_instances.*)

Ltac normalize_tc :=
  first [
      lazymatch goal with
      | |- ?a = ?b => change_no_check (NormalizeWalk true a b); solve [typeclasses eauto]
      end
    | exact: eq_refl].

Ltac normalize_autorewrite_tc :=
  autorewrite with lithium_rewrite;
  normalize_tc.
