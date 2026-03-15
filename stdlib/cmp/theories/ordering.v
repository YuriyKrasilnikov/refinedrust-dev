From refinedrust Require Import typing.
From rrstd.cmp.theories Require Export zify.

Notation ordering := comparison (only parsing).
Notation Less := Lt (only parsing).
Notation Greater := Gt (only parsing).
Notation Equal := Eq (only parsing).

Canonical Structure comparisonRT := directRT comparison.

Global Instance comparison_eqdec : EqDecision comparison.
Proof. solve_decision. Defined.

Definition ord_lt {A} (cmp : A → A → ordering) (a b : A) : Prop :=
  cmp a b = Less.
Definition ord_eq {A} (cmp : A → A → ordering) (a b : A) : Prop :=
  cmp a b = Equal.
Definition ord_gt {A} (cmp : A → A → ordering) (a b : A) : Prop :=
  cmp a b = Greater.
Definition ord_le {A} (cmp : A → A → ordering) (a b : A) : Prop :=
  ord_lt cmp a b ∨ ord_eq cmp a b.
Definition ord_ge {A} (cmp : A → A → ordering) (a b : A) : Prop :=
  ord_gt cmp a b ∨ ord_eq cmp a b.

Notation "a '<o{' cmp '}' b" := (ord_lt cmp a b) (at level 42).
Notation "a '>o{' cmp '}' b" := (ord_gt cmp a b) (at level 42).
Notation "a '=o{' cmp '}' b" := (ord_eq cmp a b) (at level 42).
Notation "a '≤o{' cmp '}' b" := (ord_le cmp a b) (at level 42).
Notation "a '≥o{' cmp '}' b" := (ord_ge cmp a b) (at level 42).

Global Instance ord_lt_dec {A} cmp (a b : A) : Decision (a <o{ cmp } b).
Proof. apply comparison_eqdec. Qed.
Global Instance ord_eq_dec {A} cmp (a b : A) : Decision (a =o{ cmp } b).
Proof. apply comparison_eqdec. Qed.
Global Instance ord_gt_dec {A} cmp (a b : A) : Decision (a >o{ cmp } b).
Proof. apply comparison_eqdec. Qed.
Global Instance ord_le_dec {A} cmp (a b : A) : Decision (a ≤o{ cmp } b).
Proof. apply _. Qed.
Global Instance ord_ge_dec {A} cmp (a b : A) : Decision (a ≥o{ cmp } b).
Proof. apply _. Qed.

Global Hint Unfold ord_lt ord_gt ord_eq : solve_goal_unfold.

Global Typeclasses Opaque ord_le ord_ge ord_lt ord_eq ord_gt.

(** Nat *)
Module Nat.
  Lemma ord_lt_iff a b :
    a <o{Nat.compare} b ↔ (a < b)%nat.
  Proof. apply Nat.compare_lt_iff. Qed.
  Lemma ord_gt_iff a b :
    a >o{Nat.compare} b ↔ (a > b)%nat.
  Proof.
    rewrite /ord_gt.
    rewrite Nat.compare_gt_iff. lia.
  Qed.
  Lemma ord_eq_iff a b :
    a =o{Nat.compare} b ↔ a = b.
  Proof. apply Nat.compare_eq_iff. Qed.
  Lemma ord_le_iff a b :
    a ≤o{Nat.compare} b ↔ (a ≤ b)%nat.
  Proof.
    unfold ord_le.
    rewrite ord_lt_iff ord_eq_iff.
    lia.
  Qed.
  Lemma ord_ge_iff a b :
    a ≥o{Nat.compare} b ↔ (a >= b)%nat.
  Proof.
    unfold ord_ge.
    rewrite ord_gt_iff ord_eq_iff.
    lia.
  Qed.
End Nat.
Global Arguments Nat.compare : simpl never.

Global Instance nat_cmp_less_simpl a b :
  SimplBothRel (=) (Nat.compare a b) Less (a < b)%nat.
Proof.
  unfold SimplBothRel. lia.
Qed.
Global Instance nat_cmp_equal_simpl a b :
  SimplBothRel (=) (Nat.compare a b) Equal (a = b).
Proof.
  unfold SimplBothRel. lia.
Qed.
Global Instance nat_cmp_greater_simpl a b :
  SimplBothRel (=) (Nat.compare a b) Greater (a > b)%nat.
Proof.
  unfold SimplBothRel. lia.
Qed.
Global Instance nat_cmp_not_greater_simpl a b :
  SimplBoth (Nat.compare a b ≠ Greater) (a ≤ b)%nat.
Proof.
  unfold SimplBoth. lia.
Qed.
Global Instance nat_cmp_not_less_simpl a b :
  SimplBoth (Nat.compare a b ≠ Less) (a >= b)%nat.
Proof.
  unfold SimplBoth. lia.
Qed.

(** Z *)
Module Z.
  Lemma ord_lt_iff a b :
    a <o{Z.compare} b ↔ a < b.
  Proof. apply Z.compare_lt_iff. Qed.
  Lemma ord_gt_iff a b :
    a >o{Z.compare} b ↔ a > b.
  Proof.
    rewrite /ord_gt. rewrite Z.compare_gt_iff. lia.
  Qed.
  Lemma ord_eq_iff a b :
    a =o{Z.compare} b ↔ a = b.
  Proof. apply Z.compare_eq_iff. Qed.
  Lemma ord_le_iff a b :
    a ≤o{Z.compare} b ↔ a ≤ b.
  Proof.
    unfold ord_le.
    rewrite ord_lt_iff ord_eq_iff.
    lia.
  Qed.
  Lemma ord_ge_iff a b :
    a ≥o{Z.compare} b ↔ a >= b.
  Proof.
    unfold ord_ge.
    rewrite ord_gt_iff ord_eq_iff.
    lia.
  Qed.
End Z.

Global Instance cmp_less_simpl a b :
  SimplBothRel (=) (Z.compare a b) Less (a < b).
Proof.
  unfold SimplBothRel. by rewrite Z.compare_lt_iff.
Qed.
Global Instance cmp_equal_simpl a b :
  SimplBothRel (=) (Z.compare a b) Equal (a = b).
Proof.
  unfold SimplBothRel. by rewrite Z.compare_eq_iff.
Qed.
Global Instance cmp_greater_simpl a b :
  SimplBothRel (=) (Z.compare a b) Greater (a > b).
Proof.
  unfold SimplBothRel. lia.
Qed.
(* [Z.le] and [Z.ge] are *defined* via [Z.compare] *)

Definition max_by {A} (cmp : A → A → ordering) (a b : A) : A :=
  match cmp a b with
  | Greater => a
  | _ => b
  end.
Definition min_by {A} (cmp : A → A → ordering) (a b : A) : A :=
  match cmp a b with
  | Less => a
  | Equal => a
  | Greater => b
  end.


Class CorrectEq {A : Type} (eq : A → A → bool) := {
  correct_eq_refl :: Reflexive (λ a b, Is_true (eq a b));
  correct_eq_sym :: Symmetric (λ a b, Is_true (eq a b));
  correct_eq_trans :: Transitive (λ a b, Is_true (eq a b));
  (* For convenience. Maybe get rid of this at a later point, or make it optional with an extension trait? *)
  correct_eq_leibniz : ∀ x y, eq x y ↔ x = y;
}.

Section correct_eq.
  Context {A : Type} {eq} `{!CorrectEq (A := A) eq}.

  Local Set Default Proof Using "Type*".

  Global Instance correct_eq_true_simpl a b :
    SimplBothRel (=) (eq a b) true (a = b).
  Proof.
    unfold SimplBothRel. rewrite -correct_eq_leibniz Is_true_true//.
  Qed.

  Global Instance correct_eq_false_simpl a b :
    SimplBothRel (=) (eq a b) false (a ≠ b).
  Proof.
    unfold SimplBothRel.
    rewrite -correct_eq_leibniz -Is_true_false//.
  Qed.
End correct_eq.

(* TODO: develop some abstraction for PartialOrd? Let's look at what things we need for that and if we can just lead that back to Ord. *)

Class CorrectOrd {A : Type} (eq : A → A → bool) (cmp : A → A → ordering) := {
  correct_ord_correct_eq :: CorrectEq eq;
  correct_ord_eq_compat : ∀ x y, eq x y ↔ x =o{cmp} y;
  correct_ord_lt_trans :: Transitive (ord_lt cmp);
  correct_ord_gt_trans :: Transitive (ord_gt cmp);
  correct_ord_antisym : ∀ x y, ord_lt cmp x y ↔ ord_gt cmp y x;
}.

Section correct_ord.
  Context {A : Type} {eq cmp} `{!CorrectOrd (A := A) eq cmp}.

  Local Set Default Proof Using "Type*".

  #[export] Instance correct_ord_eq_trans : Transitive (ord_eq cmp).
  Proof.
    intros a b c.
    rewrite -!correct_ord_eq_compat.
    apply correct_eq_trans.
  Qed.
  #[export] Instance correct_ord_eq_sym : Symmetric (ord_eq cmp).
  Proof.
    intros a b.
    rewrite -!correct_ord_eq_compat.
    apply correct_eq_sym.
  Qed.
  #[export] Instance correct_ord_eq_refl : Reflexive (ord_eq cmp).
  Proof.
    intros a.
    rewrite -!correct_ord_eq_compat.
    apply correct_eq_refl.
  Qed.

  Lemma correct_ord_eq_compat' x y : eq x y ↔ cmp x y = Equal.
  Proof.
    specialize (correct_ord_eq_compat x y).
    unfold ord_eq. done.
  Qed.
  Lemma correct_ord_cmp_refl a :
    cmp a a = Equal.
  Proof.
    by rewrite -correct_ord_eq_compat'.
  Qed.

  Lemma correct_ord_eq_leibniz' x y : x =o{cmp} y ↔ x = y.
  Proof.
    rewrite -!correct_ord_eq_compat.
    by rewrite correct_eq_leibniz.
  Qed.
  Lemma correct_ord_cmp_leibniz a b :
    cmp a b = Equal ↔ a = b.
  Proof.
    rewrite -correct_ord_eq_compat'.
    apply correct_eq_leibniz.
  Qed.
  Lemma correct_ord_cmp_equal_sym a b :
    cmp a b = Equal ↔ cmp b a = Equal.
  Proof.
    rewrite -!correct_ord_eq_compat'.
    rewrite !correct_eq_leibniz.
    done.
  Qed.

  Global Instance simpl_correct_ord_eq_leibniz x y :
    SimplBoth (x =o{cmp} y) (x = y).
  Proof. rewrite /SimplBoth correct_ord_eq_leibniz'//. Qed.

  Global Instance ord_le_refl : Reflexive (ord_le cmp).
  Proof. intros ?. by right. Qed.
  Global Instance ord_ge_refl : Reflexive (ord_ge cmp).
  Proof. intros ?. by right. Qed.

  Global Instance ord_le_trans : Transitive (ord_le cmp).
  Proof.
    intros a b c [Hlt1 | ->%correct_ord_eq_leibniz'] [Hlt2 | ->%correct_ord_eq_leibniz'].
    - left. by etrans.
    - left. done.
    - left. done.
    - by right.
  Qed.
  Global Instance ord_ge_trans : Transitive (ord_ge cmp).
  Proof.
    intros a b c [Hlt1 | ->%correct_ord_eq_leibniz'] [Hlt2 | ->%correct_ord_eq_leibniz'].
    - left. by etrans.
    - left. done.
    - left. done.
    - by right.
  Qed.

  Lemma ord_le_antisym a b :
    a ≤o{cmp} b ↔ b ≥o{cmp} a.
  Proof.
    split.
    - intros [Ha | Hb].
      + left. by apply correct_ord_antisym.
      + right. done.
    - intros [Ha | Hb].
      + left. by apply correct_ord_antisym.
      + right. done.
  Qed.

  Lemma not_ord_lt_iff a b :
    (¬ a <o{cmp} b) ↔ (b ≤o{cmp} a).
  Proof.
    unfold ord_lt, ord_le.
    rewrite correct_ord_antisym.
    unfold ord_gt, ord_eq.
    rewrite correct_ord_cmp_equal_sym.
    destruct (cmp a b); naive_solver.
  Qed.
  Lemma not_ord_gt_iff a b :
    (¬ a >o{cmp} b) ↔ a ≤o{cmp} b.
  Proof.
    unfold ord_lt, ord_le.
    unfold ord_gt, ord_lt, ord_eq.
    destruct (cmp a b); naive_solver.
  Qed.
  Lemma not_ord_le_iff a b :
    (¬ a ≤o{cmp} b) ↔ (b <o{cmp} a).
  Proof.
    rewrite -not_ord_lt_iff.
    solve_goal.
  Qed.
  Lemma not_ord_ge_iff a b :
    (¬ a ≥o{cmp} b) ↔ (a <o{cmp} b).
  Proof.
    rewrite -ord_le_antisym.
    rewrite not_ord_le_iff; done.
  Qed.

  (* Normalize to </≤ *)
  Global Instance simpl_both_ord_gt a b :
    SimplBoth (b >o{cmp} a) (a <o{cmp} b).
  Proof. rewrite /SimplBoth correct_ord_antisym//. Qed.
  Global Instance simpl_both_ord_ge a b :
    SimplBoth (b ≥o{cmp} a) (a ≤o{cmp} b).
  Proof. rewrite /SimplBoth ord_le_antisym//. Qed.

  Global Instance simpl_both_not_ord_le a b :
    SimplBoth (¬ a ≤o{cmp} b) (b <o{cmp} a).
  Proof. rewrite /SimplBoth not_ord_le_iff//. Qed.
  Global Instance simpl_both_not_ord_lt a b :
    SimplBoth (¬ a <o{cmp} b) (b ≤o{cmp} a).
  Proof. rewrite /SimplBoth not_ord_lt_iff//. Qed.

  Lemma ord_lt_ord_le_trans a b c :
    a <o{cmp} b → b ≤o{cmp} c → a <o{cmp} c.
  Proof.
    intros Ha [Hb | Heq]; first by etrans.
    apply correct_ord_eq_leibniz' in Heq. by subst.
  Qed.
  Lemma ord_le_ord_lt_trans a b c :
    a ≤o{cmp} b → b <o{cmp} c → a <o{cmp} c.
  Proof.
    intros [Ha | Heq] Hb; first by etrans.
    apply correct_ord_eq_leibniz' in Heq. by subst.
  Qed.
  Lemma ord_gt_ord_ge_trans a b c :
    a >o{cmp} b → b ≥o{cmp} c → a >o{cmp} c.
  Proof.
    intros Ha [Hb | Heq]; first by etrans.
    apply correct_ord_eq_leibniz' in Heq. by subst.
  Qed.
  Lemma ord_ge_ord_gt_trans a b c :
    a ≥o{cmp} b → b >o{cmp} c → a >o{cmp} c.
  Proof.
    intros [Ha | Heq] Hb; first by etrans.
    apply correct_ord_eq_leibniz' in Heq. by subst.
  Qed.

  Lemma ord_lt_irrefl a :
    ¬ a <o{cmp} a.
  Proof.
    unfold ord_lt.
    opose proof (proj2 (correct_ord_eq_leibniz' a a) _) as Ha; first done.
    rewrite Ha. done.
  Qed.
  Lemma ord_gt_irrefl a :
    ¬ a >o{cmp} a.
  Proof.
    unfold ord_gt.
    opose proof (proj2 (correct_ord_eq_leibniz' a a) _) as Ha; first done.
    rewrite Ha. done.
  Qed.

  Global Instance simpl_impl_ord_lt_refl a :
    SimplImpl true (a <o{cmp} a) (λ T, False → T).
  Proof.
    unfold SimplImpl. intros T.
    split.
    - intros H1 H2. apply H1. by eapply ord_lt_irrefl.
    - done.
  Qed.

  Lemma max_by_refl a : max_by cmp a a = a.
  Proof.
    unfold max_by. by rewrite correct_ord_cmp_refl.
  Qed.

  Lemma max_by_max_by a b :
    max_by cmp a (max_by cmp a b) = max_by cmp a b.
  Proof.
    unfold max_by.
    destruct (cmp a b) eqn:Hab; try rewrite Hab; try done.
    by rewrite correct_ord_cmp_refl.
  Qed.
  Lemma max_by_com a b :
    (max_by cmp a b) = (max_by cmp b a).
  Proof.
    unfold max_by.
    destruct (cmp a b) eqn:Hab.
    all: try apply correct_ord_antisym in Hab; try rewrite Hab; try done.
    apply correct_ord_eq_sym in Hab. rewrite Hab.
    apply correct_eq_leibniz.
    by apply correct_ord_eq_compat.
  Qed.
  Lemma max_by_assoc a b c :
    max_by cmp a (max_by cmp b c) = max_by cmp (max_by cmp a b) c.
  Proof.
    unfold max_by.
    destruct (cmp a b) eqn:Hab.
    all: destruct (cmp b c) eqn:Hbc.
    all: destruct (cmp a c) eqn:Hac.
    all: try rewrite Hab.
    all: try done.
    all: repeat match goal with
      | H : cmp _ _ = Equal |- _ =>
          apply correct_ord_cmp_leibniz in H; subst
      | H : cmp ?a ?b = Less, H2 : cmp ?b ?c = Less |- _ =>
          specialize (correct_ord_lt_trans _ _ _ H H2);
          unfold ord_lt; intros ?;
          clear H H2
      | H : cmp ?a ?b = Greater, H2 : cmp ?b ?c = Greater |- _ =>
          specialize (correct_ord_gt_trans _ _ _ H H2);
          unfold ord_gt; intros ?;
          clear H H2
      end; try congruence.
  Qed.

  Lemma max_by_r a b :
    ¬ (a >o{cmp} b) ↔ max_by cmp a b = b.
  Proof.
    unfold max_by, ord_gt.
    destruct (cmp a b) eqn:Heq; try done.
    split; first done. intros ->.
    enough (b =o{ cmp } b).
    { unfold ord_eq in *. congruence. }
    apply correct_ord_eq_compat. done.
  Qed.
  Lemma max_by_r_1 a b :
    ¬ (a >o{cmp} b) → max_by cmp a b = b.
  Proof. apply max_by_r. Qed.
  Lemma max_by_l a b :
    ¬ (a <o{cmp} b) ↔ max_by cmp a b = a.
  Proof.
    unfold max_by, ord_lt.
    destruct (cmp a b) eqn:Heq; try done.
    - apply correct_ord_eq_compat in Heq.
      apply correct_eq_leibniz in Heq as <-.
      done.
    - split; first done. intros ->.
      enough (a =o{ cmp } a).
      { unfold ord_eq in *. congruence. }
      apply correct_ord_eq_compat. done.
  Qed.
  Lemma max_by_l_1 a b :
    ¬ (a <o{cmp} b) → max_by cmp a b = a.
  Proof. apply max_by_l. Qed.

  Lemma min_by_refl a : min_by cmp a a = a.
  Proof.
    unfold min_by. by rewrite correct_ord_cmp_refl.
  Qed.

  Lemma min_by_min_by a b :
    min_by cmp a (min_by cmp a b) = min_by cmp a b.
  Proof.
    unfold min_by.
    destruct (cmp a b) eqn:Hab; try rewrite Hab; try done.
    all: by rewrite correct_ord_cmp_refl.
  Qed.
  Lemma min_by_com a b :
    (min_by cmp a b) = (min_by cmp b a).
  Proof.
    unfold min_by.
    destruct (cmp a b) eqn:Hab.
    all: try apply correct_ord_antisym in Hab; try rewrite Hab; try done.
    apply correct_ord_eq_sym in Hab. rewrite Hab.
    apply correct_eq_leibniz.
    by apply correct_ord_eq_compat.
  Qed.
  Lemma min_by_assoc a b c :
    min_by cmp a (min_by cmp b c) = min_by cmp (min_by cmp a b) c.
  Proof.
    unfold min_by.
    destruct (cmp a b) eqn:Hab.
    all: destruct (cmp b c) eqn:Hbc.
    all: destruct (cmp a c) eqn:Hac.
    all: try rewrite Hab.
    all: try done.
    all: repeat match goal with
      | H : cmp _ _ = Equal |- _ =>
          apply correct_ord_cmp_leibniz in H; subst
      | H : cmp ?a ?b = Less, H2 : cmp ?b ?c = Less |- _ =>
          specialize (correct_ord_lt_trans _ _ _ H H2);
          unfold ord_lt; intros ?;
          clear H H2
      | H : cmp ?a ?b = Greater, H2 : cmp ?b ?c = Greater |- _ =>
          specialize (correct_ord_gt_trans _ _ _ H H2);
          unfold ord_gt; intros ?;
          clear H H2
      end; try congruence.
  Qed.

  Lemma min_by_r a b :
    ¬ (a <o{cmp} b) ↔ min_by cmp a b = b.
  Proof.
    unfold min_by, ord_lt.
    destruct (cmp a b) eqn:Heq; try done.
    - apply correct_ord_eq_compat in Heq.
      apply correct_eq_leibniz in Heq as <-.
      done.
    - split; first done. intros ->.
      enough (b =o{ cmp } b).
      { unfold ord_eq in *. congruence. }
      apply correct_ord_eq_compat. done.
  Qed.
  Lemma min_by_r_1 a b :
    ¬ (a <o{cmp} b) → min_by cmp a b = b.
  Proof. apply min_by_r. Qed.
  Lemma min_by_l a b :
    ¬ (a >o{cmp} b) ↔ min_by cmp a b = a.
  Proof.
    unfold min_by, ord_gt.
    destruct (cmp a b) eqn:Heq; try done.
    split; first done. intros ->.
    enough (a =o{ cmp } a).
    { unfold ord_eq in *. congruence. }
    apply correct_ord_eq_compat. done.
  Qed.
  Lemma min_by_l_1 a b :
    ¬ (a >o{cmp} b) → min_by cmp a b = a.
  Proof. apply min_by_l. Qed.

  Lemma max_by_lub a b x :
    a <o{cmp} x →
    b <o{cmp} x →
    (max_by cmp a b) <o{cmp} x.
  Proof.
    unfold max_by. destruct (cmp a b) eqn:Heq; done.
  Qed.
  Lemma max_by_lt_l x a b :
    x <o{cmp} a →
    x <o{cmp} max_by cmp a b.
  Proof.
    unfold max_by. destruct (cmp a b) eqn:Heq; try done.
    - apply correct_ord_cmp_leibniz in Heq as <-. done.
    - intros ?. eapply correct_ord_lt_trans; done.
  Qed.
  Lemma max_by_lt_r x a b :
    x <o{cmp} b →
    x <o{cmp} max_by cmp a b.
  Proof.
    unfold max_by. destruct (cmp a b) eqn:Heq; try done.
    intros ?. apply correct_ord_antisym in Heq.
    eapply correct_ord_lt_trans; done.
  Qed.

  Lemma min_by_glb a b x :
    x <o{cmp} a →
    x <o{cmp} b →
    x <o{cmp} min_by cmp a b.
  Proof.
    unfold min_by. destruct (cmp a b) eqn:Heq; done.
  Qed.
  Lemma min_by_lt_l x a b :
    a <o{cmp} x →
    min_by cmp a b <o{cmp} x.
  Proof.
    unfold min_by. destruct (cmp a b) eqn:Heq; try done.
    intros ?. apply correct_ord_antisym in Heq.
    eapply correct_ord_lt_trans; done.
  Qed.
  Lemma min_by_lt_r x a b :
    b <o{cmp} x →
    min_by cmp a b <o{cmp} x.
  Proof.
    unfold min_by. destruct (cmp a b) eqn:Heq; try done.
    - apply correct_ord_cmp_leibniz in Heq as <-. done.
    - intros ?. eapply correct_ord_lt_trans; done.
  Qed.
End correct_ord.

(** Instance for [option]: defined here as it is also useful to define [max_list_cmp] and [min_list_cmp] *)
Section option.
  Definition option_partial_eq {A} (A_partial_eq : A → A → bool) (a b : option A) : bool :=
    match a, b with
    | Some a, Some b => A_partial_eq a b
    | None, None => true
    | _, _ => false
    end.

  Global Instance option_correct_eq {A} (A_eq : A → A → bool) `{!CorrectEq A_eq} : CorrectEq (option_partial_eq A_eq).
  Proof.
    econstructor.
    - intros []; last done.
      simpl. apply correct_eq_refl.
    - intros [] []; try done.
      simpl. apply correct_eq_sym.
    - intros [] [] []; try done.
      simpl. apply correct_eq_trans.
    - intros [] []; try done.
      simpl. rewrite correct_eq_leibniz.
      naive_solver.
  Qed.

  (** The canonical comparison used by Rust, making [None < Some x]. *)
  Definition option_partial_cmp {A} (A_partial_cmp : A → A → option ordering) (a b : option A) : option ordering :=
    match a, b with
    | Some a, Some b => A_partial_cmp a b
    | Some _, None => Some Greater
    | None, Some _ => Some Less
    | None, None => Some Equal
    end
  .
  Definition option_cmp {A} (A_cmp : A → A → ordering) (a b : option A) : ordering :=
    match a, b with
    | Some a, Some b => A_cmp a b
    | Some _, None => Greater
    | None, Some _ => Less
    | None, None => Equal
    end
  .

  Global Instance option_correct_ord {A} (A_eq : A → A → bool) (A_cmp : A → A → ordering) `{!CorrectEq A_eq} `{!CorrectOrd A_eq A_cmp} :
    CorrectOrd (option_partial_eq A_eq) (option_cmp A_cmp).
  Proof.
    econstructor.
    - apply _.
    - intros [] []; simpl; try done.
      rewrite correct_ord_eq_compat. done.
    - intros [x | ] [y| ] [z| ]; simpl; try done.
      apply (correct_ord_lt_trans x y z).
    - intros [x | ] [y| ] [z| ]; simpl; try done.
      apply (correct_ord_gt_trans x y z).
    - intros [x | ] [y | ]; simpl; try done.
      apply (correct_ord_antisym x y).
  Qed.

  Section props.
    Context {A : Type}  {eq cmp} `{!CorrectOrd (A := A) eq cmp}.

    Lemma max_by_Some a b :
      max_by (option_cmp cmp) (Some a) (Some b) = Some (max_by cmp a b).
    Proof.
      unfold max_by, option_cmp.
      destruct (cmp a b); done.
    Qed.
    Lemma min_by_Some a b :
      min_by (option_cmp cmp) (Some a) (Some b) = Some (min_by cmp a b).
    Proof.
      unfold min_by, option_cmp.
      destruct (cmp a b); done.
    Qed.

    Lemma max_by_None_l b :
      max_by (option_cmp cmp) None b = b.
    Proof. destruct b; done. Qed.
    Lemma max_by_None_r b :
      max_by (option_cmp cmp) b None = b.
    Proof. destruct b; done. Qed.
    Lemma min_by_None_l b :
      min_by (option_cmp cmp) None b = None.
    Proof. destruct b; done. Qed.
    Lemma min_by_None_r b :
      min_by (option_cmp cmp) b None = None.
    Proof. destruct b; done. Qed.

    Lemma ord_lt_option_Some_iff x y :
      Some x <o{option_cmp cmp} Some y ↔ x <o{cmp} y.
    Proof. solve_goal. Qed.
    Global Instance simpl_both_ord_lt_option_Some x y:
      SimplBoth (Some x <o{option_cmp cmp} Some y) (x <o{cmp} y).
    Proof. rewrite /SimplBoth ord_lt_option_Some_iff//. Qed.

    Lemma ord_eq_option_Some_iff x y :
      Some x =o{option_cmp cmp} Some y ↔ x =o{cmp} y.
    Proof. solve_goal. Qed.
    Global Instance simpl_both_ord_eq_option_Some x y:
      SimplBoth (Some x =o{option_cmp cmp} Some y) (x =o{cmp} y).
    Proof. rewrite /SimplBoth ord_eq_option_Some_iff//. Qed.

    Lemma ord_gt_option_Some_iff x y :
      Some x >o{option_cmp cmp} Some y ↔ x >o{cmp} y.
    Proof. solve_goal. Qed.
    Global Instance simpl_both_ord_gt_option_Some x y:
      SimplBoth (Some x >o{option_cmp cmp} Some y) (x >o{cmp} y).
    Proof. rewrite /SimplBoth ord_gt_option_Some_iff//. Qed.

    Lemma ord_le_option_Some_iff x y :
      Some x ≤o{option_cmp cmp} Some y ↔ x ≤o{cmp} y.
    Proof. solve_goal. Qed.
    Global Instance simpl_both_ord_le_option_Some x y:
      SimplBoth (Some x ≤o{option_cmp cmp} Some y) (x ≤o{cmp} y).
    Proof. rewrite /SimplBoth ord_le_option_Some_iff//. Qed.

    Lemma ord_ge_option_Some_iff x y :
      Some x ≥o{option_cmp cmp} Some y ↔ x ≥o{cmp} y.
    Proof. solve_goal. Qed.
    Global Instance simpl_both_ord_ge_option_Some x y:
      SimplBoth (Some x ≥o{option_cmp cmp} Some y) (x ≥o{cmp} y).
    Proof. rewrite /SimplBoth ord_ge_option_Some_iff//. Qed.

    Lemma ord_lt_None_Some x :
      None <o{option_cmp cmp} Some x.
    Proof. done. Qed.
    Lemma ord_le_None_l oy :
      None ≤o{option_cmp cmp} oy.
    Proof using Type*.
      destruct oy; last by right.
      by left.
    Qed.

    Global Instance simpl_both_ord_le_None_l oy :
      SimplBoth (None ≤o{option_cmp cmp} oy) True.
    Proof using Type*.
      rewrite /SimplBoth.
      split; first done.
      intros _. apply ord_le_None_l.
    Qed.
    Global Instance simpl_both_ord_lt_None_Some y :
      SimplBoth (None <o{option_cmp cmp} Some y) True.
    Proof.
      rewrite /SimplBoth.
      split; first done.
      intros _. apply ord_lt_None_Some.
    Qed.

    Lemma ord_le_option_Some_None x :
      ¬ Some x ≤o{option_cmp cmp} None.
    Proof using Type*. solve_goal. Qed.
    Global Instance simpl_impl_some_le_none x :
      SimplImpl true (Some x ≤o{option_cmp cmp} None) (λ T, False → T).
    Proof using Type*.
      unfold SimplImpl. intros T.
      split; last solve_goal.
      intros H1 H2. apply H1. eapply ord_le_option_Some_None. done.
    Qed.

    Lemma ord_le_option_Some_l x oy :
      Some x ≤o{option_cmp cmp} oy ↔ ∃ y, oy = Some y ∧ x ≤o{cmp} y.
    Proof using Type*.
      destruct oy as [ y | ]; simpl.
      - split; solve_goal.
      - split; solve_goal.
    Qed.
    Global Instance simpl_both_ord_le_option_Some_l x oy :
      SimplBoth (Some x ≤o{option_cmp cmp} oy) (∃ y, oy = Some y ∧ x ≤o{cmp} y).
    Proof using Type*. unfold SimplBoth. rewrite ord_le_option_Some_l//. Qed.

    Lemma ord_lt_option_Some_l x oy :
      Some x <o{option_cmp cmp} oy ↔ ∃ y, oy = Some y ∧ x <o{cmp} y.
    Proof using Type*.
      destruct oy as [ y | ]; simpl.
      - split; solve_goal.
      - split; solve_goal.
    Qed.
    Global Instance simpl_both_ord_lt_option_Some_l x oy :
      SimplBoth (Some x <o{option_cmp cmp} oy) (∃ y, oy = Some y ∧ x <o{cmp} y).
    Proof using Type*. unfold SimplBoth. rewrite ord_lt_option_Some_l//. Qed.
  End props.

  (** The reverse order, making [None > Some x] (used to define [min_list_cmp] below) *)
  Definition option_partial_cmp_rev {A} (A_partial_cmp : A → A → option ordering) (a b : option A) : option ordering :=
    match a, b with
    | Some a, Some b => A_partial_cmp a b
    | Some _, None => Some Less
    | None, Some _ => Some Greater
    | None, None => Some Equal
    end
  .
  Definition option_cmp_rev {A} (A_cmp : A → A → ordering) (a b : option A) : ordering :=
    match a, b with
    | Some a, Some b => A_cmp a b
    | Some _, None => Less
    | None, Some _ => Greater
    | None, None => Equal
    end
  .

  Global Instance option_correct_ord_rev {A} (A_eq : A → A → bool) (A_cmp : A → A → ordering) `{!CorrectEq A_eq} `{!CorrectOrd A_eq A_cmp} :
    CorrectOrd (option_partial_eq A_eq) (option_cmp_rev A_cmp).
  Proof.
    econstructor.
    - apply _.
    - intros [] []; simpl; try done.
      rewrite correct_ord_eq_compat. done.
    - intros [x | ] [y| ] [z| ]; simpl; try done.
      apply (correct_ord_lt_trans x y z).
    - intros [x | ] [y| ] [z| ]; simpl; try done.
      apply (correct_ord_gt_trans x y z).
    - intros [x | ] [y | ]; simpl; try done.
      apply (correct_ord_antisym x y).
  Qed.

  Section props.
    Context {A : Type}  {eq cmp} `{!CorrectOrd (A := A) eq cmp}.
    Lemma max_by_Some_rev a b :
      max_by (option_cmp_rev cmp) (Some a) (Some b) = Some (max_by cmp a b).
    Proof.
      unfold max_by, option_cmp_rev.
      destruct (cmp a b); done.
    Qed.
    Lemma min_by_Some_rev a b :
      min_by (option_cmp_rev cmp) (Some a) (Some b) = Some (min_by cmp a b).
    Proof.
      unfold min_by, option_cmp_rev.
      destruct (cmp a b); done.
    Qed.

    Lemma max_by_None_l_rev b :
      max_by (option_cmp_rev cmp) None b = None.
    Proof. destruct b; done. Qed.
    Lemma max_by_None_r_rev b :
      max_by (option_cmp_rev cmp) b None = None.
    Proof. destruct b; done. Qed.
    Lemma min_by_None_l_rev b :
      min_by (option_cmp_rev cmp) None b = b.
    Proof. destruct b; done. Qed.
    Lemma min_by_None_r_rev b :
      min_by (option_cmp_rev cmp) b None = b.
    Proof. destruct b; done. Qed.
  End props.
End option.

(* Should return the last of all maximum elements *)
Definition max_list_cmp {A} (cmp : A → A → ordering) : list A → option A → option A :=
  fix go l acc :=
  match l with
  | [] => acc
  | x :: l =>
      let a := max_by (option_cmp cmp) acc (Some x) in
      go l a
  end.
Definition max_list_cmp_def {A} (cmp : A → A → ordering) (def : A) (l : list A) : A :=
  default def (max_list_cmp cmp l (Some def)).

(* Should return the first of all minimum elements *)
Definition min_list_cmp {A} (cmp : A → A → ordering) : list A → option A → option A :=
  fix go l acc :=
  match l with
  | [] => acc
  | x :: l =>
      let a := min_by (option_cmp_rev cmp) acc (Some x) in
      go l a
  end.
Definition min_list_cmp_def {A} (cmp : A → A → ordering) (def : A) (l : list A) : A :=
  default def (min_list_cmp cmp l (Some def)).

(** ** Properties of the [max_list_cmp] and [min_list_cmp] functions *)
Section max_list.
  Context {A : Type}  {eq cmp} `{!CorrectOrd (A := A) eq cmp}.
  Implicit Types x y z : A.
  Implicit Types l k : list A.

  Local Set Default Proof Using "Type*".

  Lemma max_list_cmp_by_acc l acc :
    max_list_cmp cmp l acc = max_by (option_cmp cmp) (max_list_cmp cmp l None) acc.
  Proof.
    induction l as [ | x l IH] in acc |-*; simpl.
    { destruct acc; done. }
    rewrite IH.
    rewrite (IH (max_by (option_cmp cmp) None (Some x))).
    rewrite max_by_None_l.
    rewrite -max_by_assoc.
    f_equiv.
    rewrite max_by_com.
    done.
  Qed.
  Lemma max_list_cmp_Some_acc_inv (a b : A) l :
    max_list_cmp cmp l (Some a) = Some b →
    max_by cmp a b = b.
  Proof.
    induction l as [ | x l IH] in a, b |-*; simpl.
    { intros [= <-]. by apply max_by_refl. }
    simpl.
    rewrite max_by_Some.
    intros Hmax%IH.
    apply max_by_r.
    apply max_by_r in Hmax.
    contradict Hmax.
    apply correct_ord_antisym.
    apply max_by_lt_l.
    by apply correct_ord_antisym.
  Qed.

  Lemma max_list_cmp_elem_of xs def :
    max_list_cmp cmp xs def = def ∨ ∃ x, max_list_cmp cmp xs def = Some x ∧ x ∈ xs.
  Proof.
  induction xs as [ | x xs IH] in def |-*; simpl; first by left.
    destruct (IH (max_by (option_cmp cmp) def (Some x))) as [Hdef | (y & Hmax & Hel)].
    - rewrite Hdef. destruct def as [def | ]; simpl.
      + rewrite max_by_Some.
        unfold max_by. destruct (cmp def x); last by left.
        all: right; set_solver.
      + right. rewrite max_by_None_l. set_solver.
    - rewrite Hmax. right. set_solver.
  Qed.
  Lemma min_list_cmp_elem_of xs def :
    min_list_cmp cmp xs def = def ∨ ∃ x, min_list_cmp cmp xs def = Some x ∧ x ∈ xs.
  Proof.
  induction xs as [ | x xs IH] in def |-*; simpl; first by left.
    destruct (IH (min_by (option_cmp_rev cmp) def (Some x))) as [Hdef | (y & Hmax & Hel)].
    - rewrite Hdef. destruct def as [def | ]; simpl.
      + rewrite min_by_Some_rev.
        unfold min_by. destruct (cmp def x); [by left .. | ].
        right; set_solver.
      + right. rewrite min_by_None_l_rev. set_solver.
    - rewrite Hmax. right. set_solver.
  Qed.

  Lemma min_list_cmp_by_acc l acc :
    min_list_cmp cmp l acc = min_by (option_cmp_rev cmp) (min_list_cmp cmp l None) acc.
  Proof.
    induction l as [ | x l IH] in acc |-*; simpl.
    { destruct acc; done. }
    rewrite IH.
    rewrite (IH (min_by (option_cmp_rev cmp) None (Some x))).
    rewrite min_by_None_l_rev.
    rewrite -min_by_assoc.
    f_equiv.
    rewrite min_by_com.
    done.
  Qed.
  Lemma min_list_cmp_Some_acc_inv (a b : A) l :
    min_list_cmp cmp l (Some a) = Some b →
    min_by cmp a b = b.
  Proof.
    induction l as [ | x l IH] in a, b |-*; simpl.
    { intros [= <-]. by apply min_by_refl. }
    simpl.
    rewrite min_by_Some_rev.
    intros Hmin%IH.
    apply min_by_r.
    apply min_by_r in Hmin.
    contradict Hmin.
    by apply min_by_lt_l.
  Qed.

  Lemma max_list_cmp_by_def def l :
    max_list_cmp_def cmp def l =
      max_by cmp def (max_list_cmp_def cmp def l).
  Proof.
    unfold max_list_cmp_def.
    destruct (max_list_cmp cmp l (Some def)) eqn:Heq; simpl; first last.
    { rewrite max_by_refl//. }
    apply max_list_cmp_Some_acc_inv in Heq.
    done.
  Qed.
  Lemma min_list_cmp_by_def def l :
    min_list_cmp_def cmp def l =
      min_by cmp def (min_list_cmp_def cmp def l).
  Proof.
    unfold min_list_cmp_def.
    destruct (min_list_cmp cmp l (Some def)) eqn:Heq; simpl; first last.
    { rewrite min_by_refl//. }
    apply min_list_cmp_Some_acc_inv in Heq.
    done.
  Qed.

  Lemma max_list_cmp_app l k acc :
    max_list_cmp cmp (l ++ k) acc = max_list_cmp cmp k (max_list_cmp cmp l acc).
  Proof.
    induction l as [ | x l IH] in acc |-*; simpl; first done.
    rewrite IH. done.
  Qed.
  Lemma max_list_cmp_def_app def l k :
    max_list_cmp_def cmp def (l ++ k) =
      max_by cmp (max_list_cmp_def cmp def l) (max_list_cmp_def cmp def k).
  Proof.
    rewrite /max_list_cmp_def.
    rewrite max_list_cmp_app.
    rewrite max_list_cmp_by_acc.
    rewrite !(max_list_cmp_by_acc _ (Some _)).

    destruct (max_list_cmp cmp l None) as [a | ], (max_list_cmp cmp k None) as [b | ]; simpl.
    all: rewrite ?max_by_Some ?max_by_None_l ?max_by_None_r/=.
    - rewrite max_by_assoc.
      rewrite max_by_assoc.
      rewrite (max_by_com _ b).
      rewrite max_by_assoc.
      rewrite -(max_by_assoc _ def def).
      rewrite max_by_refl.
      done.
    - rewrite -max_by_assoc max_by_refl//.
    - rewrite {2}max_by_com max_by_assoc max_by_refl.
      rewrite max_by_com//.
    - rewrite max_by_refl//.
  Qed.

  Lemma min_list_cmp_app l k acc :
    min_list_cmp cmp (l ++ k) acc = min_list_cmp cmp k (min_list_cmp cmp l acc).
  Proof.
    induction l as [ | x l IH] in acc |-*; simpl; first done.
    rewrite IH. done.
  Qed.
  Lemma min_list_cmp_def_app def l k :
    min_list_cmp_def cmp def (l ++ k) =
      min_by cmp (min_list_cmp_def cmp def l) (min_list_cmp_def cmp def k).
  Proof.
    rewrite /min_list_cmp_def.
    rewrite min_list_cmp_app.
    rewrite min_list_cmp_by_acc.
    rewrite !(min_list_cmp_by_acc _ (Some _)).

    destruct (min_list_cmp cmp l None) as [a | ], (min_list_cmp cmp k None) as [b | ]; simpl.
    all: rewrite ?min_by_Some_rev ?min_by_None_l_rev ?min_by_None_r_rev/=.
    - rewrite min_by_assoc.
      rewrite min_by_assoc.
      rewrite (min_by_com _ b).
      rewrite min_by_assoc.
      rewrite -(min_by_assoc _ def def).
      rewrite min_by_refl.
      done.
    - rewrite -min_by_assoc min_by_refl//.
    - rewrite {2}min_by_com min_by_assoc min_by_refl.
      rewrite min_by_com//.
    - rewrite min_by_refl//.
  Qed.

  Lemma max_list_cmp_singleton x acc :
    max_list_cmp cmp [x] acc = max_by (option_cmp cmp) acc (Some x).
  Proof. done. Qed.
  Lemma max_list_cmp_def_singleton def x :
    max_list_cmp_def cmp def [x] = max_by cmp def x.
  Proof.
    rewrite /max_list_cmp_def. rewrite max_list_cmp_singleton.
    rewrite max_by_Some. done.
  Qed.

  Lemma min_list_cmp_singleton x acc :
    min_list_cmp cmp [x] acc = min_by (option_cmp_rev cmp) acc (Some x).
  Proof. done. Qed.
  Lemma min_list_cmp_def_singleton def x :
    min_list_cmp_def cmp def [x] = min_by cmp def x.
  Proof.
    rewrite /min_list_cmp_def. rewrite min_list_cmp_singleton.
    rewrite min_by_Some_rev. done.
  Qed.
End max_list.

(* TODO autorewrite cannot handle the TC assumption... *)
(*Global Hint Rewrite -> @max_list_cmp_app : lithium_rewrite.*)

(** TC to simplify [partial_cmp] to [cmp], if possible (i.e. for [Ord] types) *)
Class PartialCmpToCmp {A} (partial_cmp : A → A → option comparison) (cmp : A → A → comparison) := {
  partial_cmp_cmp_iff : ∀ x y, partial_cmp x y = Some (cmp x y);
}.
Global Hint Mode PartialCmpToCmp + + - : typeclass_instances.

Global Instance partial_cmp_to_cmp_direct {A} (cmp : A → A → comparison) :
  PartialCmpToCmp (λ a b, Some (cmp a b)) cmp.
Proof.
  econstructor.
  done.
Qed.

Global Instance partial_cmp_to_cmp_option {A} (partial_cmp : A → A → option comparison) cmp :
  PartialCmpToCmp partial_cmp cmp →
  PartialCmpToCmp (option_partial_cmp partial_cmp) (option_cmp cmp).
Proof.
  intros [Hcmp].
  econstructor. intros [] []; simpl; try done.
Qed.

Section partial_ord.
  Context `{!typeGS Σ}.
  Context {A : Type} {partial_cmp cmp} `{!@PartialCmpToCmp A partial_cmp cmp}.

  Local Set Default Proof Using "Type*".

  Global Instance simpl_partial_cmp_less a b :
    SimplBoth (partial_cmp a b = Some Less) (a <o{cmp} b).
  Proof.
    unfold SimplBoth.
    rewrite partial_cmp_cmp_iff.
    solve_goal.
  Qed.
  Global Instance simpl_partial_cmp_greater a b :
    SimplBoth (partial_cmp a b = Some Greater) (a >o{cmp} b).
  Proof.
    unfold SimplBoth.
    rewrite partial_cmp_cmp_iff.
    solve_goal.
  Qed.
  Global Instance simpl_partial_cmp_eq a b :
    SimplBoth (partial_cmp a b = Some Equal) (a =o{cmp} b).
  Proof.
    unfold SimplBoth.
    rewrite partial_cmp_cmp_iff.
    solve_goal.
  Qed.
End partial_ord.

