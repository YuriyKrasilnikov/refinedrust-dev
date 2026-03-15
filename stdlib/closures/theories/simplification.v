From refinedrust Require Import typing.

(** Simplification machinery for closure predicates *)
(** Inspired by Quiver's simplification machinery:
   https://gitlab.mpi-sws.org/simonspies/quiver/-/blob/4c63760910c39373032b5dab1d78a181bdc8ad53/theories/argon/simplification/elim_existentials.v *)

Local Set Typeclasses Unique Instances.

(** A typeclass to check whether a relation is the identity relation *)
Class RelationIsIdentity {A} (R : A → A → Prop) := {
  relation_is_identity_proof : ∀ a b, R a b → a = b;
}.
Global Hint Extern 100 (RelationIsIdentity _) =>
    simpl; econstructor; solve_goal : typeclass_instances.
Global Hint Mode RelationIsIdentity + + : typeclass_instances.

Class RelationIsFunctional {A B} (R : A → B → Prop) (f : A → B) := {
  relation_is_functional : ∀ a b, R a b → b = f a;
}.
(* TODO: better solver for synthesizing the function *)
Global Hint Extern 100 (RelationIsFunctional _ _) =>
    simpl; econstructor; intros *;
    repeat (liForall || liImpl); done : typeclass_instances.
Global Hint Mode RelationIsIdentity + - : typeclass_instances.

Definition cnf Cs := fold_right and True Cs.

Lemma cnf_app Cs1 Cs2 :
  cnf (Cs1 ++ Cs2) ↔ cnf Cs1 ∧ cnf Cs2.
Proof.
  rewrite /cnf. induction Cs1 as [ | C1 Cs1 IH]; simpl; naive_solver.
Qed.

Definition simplify_prop (P R : Prop) := P ↔ R.
Section bubble_existentials.

  Implicit Types (P Q R : Prop).
  Implicit Types (A : Type).

  Definition bubble_existentials (worklist : list Prop) Cs R (prog : bool) :=
    (cnf worklist ∧ cnf Cs) ↔ R.
  Global Hint Mode bubble_existentials + + - - : typeclass_instances.

  (* this doesn't work so well in practice.
    Ideally, i should also normalize to cnf now.

    Let's do a DFS (leftmost).
    Put RHS conjuncts on a worklist.

  *)
  Lemma bubble_existentials_and P Q worklist Cs R prog :
    bubble_existentials (P :: Q :: worklist) Cs R prog →
    bubble_existentials ((P ∧ Q) :: worklist) Cs R prog.
  Proof.
    rewrite /bubble_existentials/simplify_prop/=. naive_solver.
  Qed.

  (* we made progress if there are some conjuncts on the output list already *)
  Lemma bubble_existentials_exist_no_prog A Φ Ψ worklist prog  :
    (∀ x : A, bubble_existentials (Φ x :: worklist) [] (Ψ x) prog) →
    bubble_existentials ((∃ x : A, Φ x) :: worklist) [] (∃ x : A, Ψ x) (prog).
  Proof.
    rewrite /bubble_existentials/simplify_prop. naive_solver.
  Qed.
  Lemma bubble_existentials_exist A Φ Ψ Cs worklist prog  :
    TCDone (Cs ≠ []) →
    (∀ x : A, bubble_existentials (Φ x :: worklist) Cs (Ψ x) prog) →
    bubble_existentials ((∃ x : A, Φ x) :: worklist) Cs (∃ x : A, Ψ x) true.
  Proof.
    rewrite /bubble_existentials/simplify_prop. naive_solver.
  Qed.

  Lemma bubble_existentials_nil Cs :
    bubble_existentials [] Cs (cnf Cs) false.
  Proof.
    rewrite /bubble_existentials/simplify_prop/=. naive_solver.
  Qed.

  Lemma bubble_existentials_atom worklist P Cs R prog :
    bubble_existentials worklist (P :: Cs) R prog →
    bubble_existentials (P :: worklist) Cs R prog.
  Proof.
    rewrite /bubble_existentials/simplify_prop/=. naive_solver.
  Qed.
End bubble_existentials.

Global Typeclasses Opaque bubble_existentials.
Existing Class bubble_existentials.

Global Existing Instances bubble_existentials_and | 1.
(* use [eapply] for better unification *)
Global Hint Extern 1 (bubble_existentials _ _ _ _) => eapply bubble_existentials_exist_no_prog : typeclass_instances.
Global Hint Extern 10 (bubble_existentials _ (_ :: _) _ _) => eapply bubble_existentials_exist : typeclass_instances.
Global Existing Instance bubble_existentials_nil | 1.
Global Existing Instance bubble_existentials_atom | 100.

Section normalize_conjuncts.
  Implicit Types (P Q R : Prop).
  Implicit Types (A : Type).
  Implicit Type (Cs : list Prop).


  Definition normalize_conjuncts P R (prog : bool) := simplify_prop P R.
  Definition normalize_as_conjuncts Cs Cs' (prog : bool) := simplify_prop (cnf Cs) (cnf Cs').

  Lemma normalize_conjuncts_exists A Φ Ψ prog :
    (∀ x : A, normalize_conjuncts (Φ x) (Ψ x) prog) →
    normalize_conjuncts (∃ x : A, Φ x) (∃ x : A, Ψ x) prog.
  Proof.
    rewrite /normalize_conjuncts /simplify_prop.
    naive_solver.
  Qed.

  Lemma normalize_conjuncts_exists_unused A `{!Inhabited A} P R prog :
    normalize_conjuncts P R prog →
    normalize_conjuncts (∃ x : A, P) (R) true.
  Proof.
    rewrite /normalize_conjuncts /simplify_prop.
    intros <-.
    split; first naive_solver.
    intros. exists inhabitant. done.
  Qed.
  Lemma normalize_conjuncts_exists_unit Φ R prog :
    normalize_conjuncts (Φ tt) R prog →
    normalize_conjuncts (∃ x : unit, Φ x) (R) true.
  Proof.
    rewrite /normalize_conjuncts /simplify_prop.
    intros <-.
    split; last naive_solver.
    intros [[] ?]. done.
  Qed.
  Lemma normalize_conjuncts_exists_nil_unit Φ R prog :
    normalize_conjuncts (Φ *[]) R prog →
    normalize_conjuncts (∃ x : nil_unit, Φ x) (R) true.
  Proof.
    rewrite /normalize_conjuncts /simplify_prop.
    intros <-.
    split; last naive_solver.
    intros [[] ?]. done.
  Qed.
  Lemma normalize_conjuncts_exists_plist_cons {A} (F : A → Type) (X : A) Xs Φ R prog :
    normalize_conjuncts (∃ x1 : F X, ∃ x2 : plist F Xs, Φ ( x1 -:: x2)) R prog →
    normalize_conjuncts (∃ x : plist F (X :: Xs), Φ x) (R) true.
  Proof.
    rewrite /normalize_conjuncts /simplify_prop.
    intros <-.
    split; last naive_solver.
    intros [[] ?]. eauto.
  Qed.
  Lemma normalize_conjuncts_exists_plist_nil {A} (F : A → Type) Φ R prog :
    normalize_conjuncts (Φ -[]) R prog →
    normalize_conjuncts (∃ x : plist F [], Φ x) (R) true.
  Proof.
    rewrite /normalize_conjuncts /simplify_prop.
    intros <-.
    split; last naive_solver.
    intros [[] ?]. done.
  Qed.

  Lemma normalize_conjuncts_as_conjuncts Cs Cs' prog :
    normalize_as_conjuncts Cs Cs' prog →
    normalize_conjuncts (cnf Cs) (cnf Cs') prog.
  Proof.
    rewrite /normalize_conjuncts /normalize_as_conjuncts /simplify_prop.
    naive_solver.
  Qed.

  Lemma normalize_as_conjuncts_nil :
    normalize_as_conjuncts [] [] false.
  Proof.
    rewrite /normalize_as_conjuncts/simplify_prop.
    done.
  Qed.

  Lemma normalize_as_conjuncts_trivial P Cs Cs' prog :
    TCFastDone P →
    normalize_as_conjuncts Cs Cs' prog →
    normalize_as_conjuncts (P :: Cs) Cs' true.
  Proof.
    rewrite /normalize_as_conjuncts/simplify_prop.
    unfold TCFastDone.
    simpl. naive_solver.
  Qed.

  Lemma normalize_as_conjuncts_unit_eq x Cs Cs' prog :
    normalize_as_conjuncts Cs Cs' prog →
    normalize_as_conjuncts ((x = tt) :: Cs) Cs' true.
  Proof.
    rewrite /normalize_as_conjuncts/simplify_prop.
    destruct x.
    naive_solver.
  Qed.

  Lemma normalize_as_conjuncts_pair_eq {A B} (a1 a2 : A) (b1 b2 : B) Cs Cs' prog :
    normalize_as_conjuncts ((a1 = a2) :: (b1 = b2) :: Cs) Cs' prog →
    normalize_as_conjuncts (((a1, b1) = (a2, b2)) :: Cs) Cs' true.
  Proof.
    rewrite /normalize_as_conjuncts/simplify_prop.
    naive_solver.
  Qed.

  #[universes(polymorphic)]
  Lemma normalize_as_conjuncts_pcons_eq {A C} (a1 a2 : A) (b1 b2 : C) Cs Cs' prog :
    normalize_as_conjuncts ((a1 = a2) :: (b1 = b2) :: Cs) Cs' prog →
    normalize_as_conjuncts ((a1 *:: b1 = a2 *:: b2) :: Cs) Cs' true.
  Proof.
    rewrite /normalize_as_conjuncts/simplify_prop.
    naive_solver.
  Qed.

  Lemma normalize_as_conjuncts_keep P Cs Cs' prog :
    normalize_as_conjuncts Cs Cs' prog →
    normalize_as_conjuncts (P :: Cs) (P :: Cs') prog.
  Proof.
    rewrite /normalize_as_conjuncts/simplify_prop.
    simpl. naive_solver.
  Qed.
End normalize_conjuncts.

Existing Class normalize_conjuncts.
Existing Class normalize_as_conjuncts.

Existing Instance normalize_conjuncts_exists_unused | 10.
Existing Instance normalize_conjuncts_exists_unit | 11.
Existing Instance normalize_conjuncts_exists_nil_unit | 11.
Existing Instances normalize_conjuncts_exists_plist_cons normalize_conjuncts_exists_plist_nil | 11.
Existing Instance normalize_conjuncts_exists | 99.
Existing Instance normalize_conjuncts_as_conjuncts | 100.

Existing Instance normalize_as_conjuncts_nil.
Existing Instance normalize_as_conjuncts_trivial | 10.
Existing Instance normalize_as_conjuncts_unit_eq | 11.
Existing Instance normalize_as_conjuncts_pair_eq | 20.
Existing Instance normalize_as_conjuncts_pcons_eq | 20.
Existing Instance normalize_as_conjuncts_keep | 100.

Section resolve_existentials.

  Definition elim_existentials (P R : Prop) (prog : bool) :=
    simplify_prop P R.

  Definition elim_this_existential (P R : Prop) :=
    simplify_prop P R.

  Definition resolve_this_existential {A : Type} (Φ : A → Prop) (R : Prop) (a : A) :=
    simplify_prop (∃ x : A, Φ x) R
    ∧ (∀ x, Φ x → x = a)
  .

  Definition resolve_this_existential_prop {A : Type} (φ : A → Prop) a :=
    ∀ x, φ x ↔ x = a.

  (* Resolving an existential using an atom *)
  Lemma resolve_this_existential_prop_eq_l {A: Type} (b: A):
    resolve_this_existential_prop (λ x, x = b) b.
  Proof. by rewrite /resolve_this_existential_prop. Qed.

  Lemma resolve_this_existential_prop_eq_r {A: Type} (b: A):
    resolve_this_existential_prop (λ x, b = x) b.
  Proof. by rewrite /resolve_this_existential_prop. Qed.

  (* Find an atom with which to resolve it.
     If we can't find one, this branch fails. *)
  Lemma resolve_this_existential_prove_pure {A: Type} (a: A) Φ Cs :
    resolve_this_existential_prop (λ x, Φ x) a →
    resolve_this_existential (λ x, cnf (Φ x :: Cs x)) (cnf (Cs a)) a.
  Proof.
    rewrite /resolve_this_existential /resolve_this_existential_prop /simplify_prop.
    simpl.
    intros Heq. split.
    - split.
      + intros (x & Hx%Heq & ?). subst. done.
      + naive_solver.
    - intros ? [Hx ?]. apply Heq in Hx. subst. done.
  Qed.

  Lemma resolve_this_existential_skip_pure {A: Type} (a: A) Φ Cs Cs' :
    resolve_this_existential (λ x, cnf (Cs x)) (cnf Cs') a →
    resolve_this_existential (λ x, cnf (Φ x :: Cs x)) (cnf (Φ a :: Cs')) a.
  Proof.
    rewrite /resolve_this_existential /resolve_this_existential_prop /simplify_prop/=.
    naive_solver.
  Qed.

  (** Pick an existential to eliminate *)
  Lemma elim_existentials_finish P:
    elim_existentials P P false.
  Proof. rewrite /elim_existentials/simplify_prop. done. Qed.

  Lemma elim_existentials_exists_elim X F R R' prog :
    elim_this_existential (∃ x: X, F x) R →
    elim_existentials R R' prog →
    elim_existentials (∃ x: X, F x) R' true.
  Proof.
    rewrite /elim_this_existential /elim_existentials /simplify_prop //.
    naive_solver.
  Qed.

  Lemma elim_existentials_exists_skip X (F G: X → Prop) prog :
    (∀ x, elim_existentials (F x) (G x) prog) →
    elim_existentials (∃ x: X, F x) (∃ x: X, G x) prog.
  Proof. rewrite /elim_existentials/simplify_prop. naive_solver. Qed.

  (** Eliminate an existential *)
  Lemma elim_this_existental_commute {X Y: Type} (G: X → Y → Prop) F:
    (∀ y, elim_this_existential (∃ x: X, G x y) (F y)) →
    elim_this_existential (∃ x: X, ∃ y: Y, G x y) (∃ y: Y, F y).
  Proof.
    rewrite /elim_this_existential /simplify_prop/=.
    naive_solver.
  Qed.

  (* [x] becomes an evar that will be unified if the TC search succeeds *)
  Lemma elim_this_existental_inst {X: Type} Cs R b :
    resolve_this_existential (λ x, cnf (Cs x)) R b →
    elim_this_existential (∃ x: X, cnf (Cs x)) R.
  Proof.
    rewrite /resolve_this_existential /elim_this_existential/simplify_prop.
    intros [<- Hb].
    naive_solver.
  Qed.
End resolve_existentials.

Existing Class elim_existentials.
Existing Class elim_this_existential.
Existing Class resolve_this_existential.
Existing Class resolve_this_existential_prop.

Existing Instances resolve_this_existential_prop_eq_l resolve_this_existential_prop_eq_r | 0.

Existing Instances resolve_this_existential_prove_pure resolve_this_existential_skip_pure | 0.

Existing Instance elim_existentials_finish | 1000.
Existing Instance elim_existentials_exists_skip | 500.
Existing Instances elim_existentials_exists_elim | 1.

Existing Instances elim_this_existental_commute elim_this_existental_inst.

Section unfold_cnf.

  Definition unfold_cnf P R :=
    simplify_prop P R.

  Lemma unfold_cnf_exists_skip X (F G: X → Prop):
    (∀ x, unfold_cnf (F x) (G x)) →
    unfold_cnf (∃ x: X, F x) (∃ x: X, G x).
  Proof. rewrite /unfold_cnf/simplify_prop. naive_solver. Qed.

  Lemma unfold_cnf_cons P Cs R :
    unfold_cnf (cnf Cs) R →
    unfold_cnf (cnf (P :: Cs)) (P ∧ R).
  Proof. rewrite /unfold_cnf/simplify_prop. naive_solver. Qed.
  Lemma unfold_cnf_singleton P :
    unfold_cnf (cnf [P]) P.
  Proof. rewrite /unfold_cnf/simplify_prop. naive_solver. Qed.
  Lemma unfold_cnf_nil :
    unfold_cnf (cnf []) True.
  Proof. rewrite /unfold_cnf/simplify_prop. naive_solver. Qed.
End unfold_cnf.

Existing Class unfold_cnf.
Global Existing Instance unfold_cnf_exists_skip.
Global Existing Instance unfold_cnf_singleton | 10.
Global Existing Instance unfold_cnf_cons | 12.
Global Existing Instance unfold_cnf_nil | 10.

Arguments cnf : simpl never.

Definition simplify_closure_prop P Q (prog : bool) := simplify_prop P Q.

Lemma simplify_closure_prop_simpl P1 P2 P3 P4 P5 prog1 prog2 prog3 :
  bubble_existentials [P1] [] P2 prog1 →
  normalize_conjuncts P2 P3 prog2 →
  elim_existentials P3 P4 prog3 →
  unfold_cnf P4 P5 →
  simplify_closure_prop P1 P5 (prog1 || prog2 || prog3).
Proof.
  rewrite /bubble_existentials /normalize_conjuncts /elim_existentials /unfold_cnf /simplify_closure_prop /simplify_prop /=.
  simpl. rewrite /cnf/=.
  naive_solver.
Qed.

Lemma simplify_closure_prop_replace Φ Φ' Ψ prog :
  Φ = Φ' →
  simplify_closure_prop Φ' Ψ prog →
  simplify_closure_prop Φ Ψ prog.
Proof.
  intros ->. done.
Qed.

Existing Class simplify_closure_prop.
Global Hint Extern 10 (simplify_closure_prop _ _ _) =>
  notypeclasses refine (simplify_closure_prop_simpl _ _ _ _ _ _ _ _ _ _ _ _);
  [simpl; typeclasses eauto | simpl; typeclasses eauto | simpl; typeclasses eauto | simpl; typeclasses eauto] : typeclass_instances.

Hint Extern 1 (simplify_closure_prop _ _ _) =>
  match goal with
  | |- (simplify_closure_prop (let (a, b) := ?p in ?Φ) ?P) =>
      notypeclasses refine (simplify_closure_prop_replace _ (let a := fst p in let b := snd p in Φ) _ _ _ _);
      [destruct p; done |  ]
  end : typeclass_instances.

Section test.
  Lemma test_1 (a b : Z) :
    ∃ P1 P2 P3 P4 prog1,
      bubble_existentials [(∃ pclos : plist id [], True ∧ (∃ (a0 : Z) (_ : gname), pclos = *[] ∧ *[a] = *[a0] ∧ () = () ∧ True) ∧ ∃ (a0 : Z) (_ : gname), pclos = *[] ∧ tt = tt ∧ () = () ∧ *[a] = *[a0] ∧ (b = a0 ∧ () = ()) ∧ True)] [] P1 prog1
      ∧ normalize_conjuncts P1 P2 true
      ∧ elim_existentials P2 P3 true
      ∧ unfold_cnf P3 P4
      ∧ P4 = (b = a) ∧ prog1 = true.
  Proof.
    eexists _, _, _, _, _.
    split. { apply _. }
    simpl.
    split. { apply _. }
    split. { apply _. }
    split; first apply _.
    done.
  Abort.

  Lemma test2 (a b : Z) :
    ∃ P prog,
      simplify_closure_prop (∃ pclos : plist id [], True ∧ (∃ (a0 : Z) (_ : gname), pclos = *[] ∧ *[a] = *[a0] ∧ () = () ∧ True) ∧ ∃ (a0 : Z) (_ : gname), pclos = *[] ∧ () = () ∧ *[a] = *[a0] ∧ (b = a0 ∧ () = ()) ∧ True) P prog ∧ P = (b = a) ∧ prog = true.
  Proof.
    eexists _, _.
    split; first apply _.
    done.
  Abort.

  Lemma test3 p (b : Z) (clos_states : list (plist (RT_xt ∘ place_rfnRT) [(place_rfn Z * gname)%type : RT])) :
    ∃ P, simplify_closure_prop (let '(idx, a) := p in ∃ (x : gname) (x0 : Z) (x1 : gname) (x2 : Z), b = a ∧ (x0, x) = (x2, x1) ∧ MinInt i32 ≤ 1 + x0 ∧ 1 + x0 ≤ MaxInt i32 ∧ clos_states !! S idx = Some -[(1 + x2, x1)] ∧ clos_states !! idx = Some -[(x0, x)]) P true ∧ P = P.
  Proof.
    eexists. split; first apply _.
    simpl.
  Abort.

  Lemma test4 (a b : Z) :
    ∃ P prog, simplify_closure_prop (a = b) P prog ∧ prog = false ∧ P = P.
  Proof.
    eexists _, _. split; first apply _.
    simpl.
    done.
  Abort.
End test.


(*
   Can we simplify [Forall2]?
   Basically, I want to derive relations on the RHS list.

   - basically, given Φ : A → B → Prop, synthesize a function f : A → B.
   - ideally, this should also work for subtypes of B (via tuple/ plist).
   - I guess I can focus the type on the RHS

 *)

Definition simplify_relation A B (Φ : A → B → Prop) C (Ψ : A → C → Prop) (map_C : A → C → B) (progress : bool) :=
  (∀ a b, Φ a b → ∃ c, Ψ a c ∧ b = map_C a c) ∧
  (∀ a c, Ψ a c → Φ a (map_C a c)).

Definition simplify_relation_functional A B (Φ : A → B → Prop) (map_B : A → B) :=
  (∀ a b, Φ a b → b = map_B a).

Section simplify_relation.

  (* How do I bottom out and completely eliminate something? I guess I'll need to make a second pass to eliminate unit. *)

  Lemma simplify_relation_prod A B1 B2 Φ C1 C2 Ψ1 Ψ2 map_C1 map_C2 prog1 prog2 :
    (∀ b2 : B2, simplify_relation A B1 (λ a b1, Φ a (b1, b2)) C1 (Ψ1 b2) (map_C1 b2) prog1) →
    (∀ c1 : C1, simplify_relation A B2 (λ a b2, Ψ1 b2 a c1) C2 (Ψ2 c1) (map_C2 c1) prog2) →
    simplify_relation A (B1 * B2)%type Φ (C1 * C2) (λ a c, Ψ2 c.1 a c.2) (λ a c, (map_C1 (map_C2 c.1 a c.2) a c.1, (map_C2 c.1 a c.2))) (prog1 || prog2).
  Proof.
    intros Hsimpl1 Hsimpl2. split.
    - intros a [b1 b2] Hphi.
      specialize (Hsimpl1 b2).
      destruct Hsimpl1 as [Hsimpl11 Hsimpl12].
      apply Hsimpl11 in Hphi as (c1 & Hphi1 & ->).
      specialize (Hsimpl2 c1).
      destruct Hsimpl2 as [Hsimpl21 Hsimpl22].
      apply Hsimpl21 in Hphi1 as (c2 & Hphi2 & ->).
      exists (c1, c2). eauto.
    - intros a [c1 c2] Hphi2.
      eapply Hsimpl1. eapply Hsimpl2. done.
  Qed.

  Lemma simplify_relation_prod_unit_l A B2 Φ C2 Ψ2 map_C2 prog :
    simplify_relation A B2 (λ a b2, Φ a (tt, b2)) C2 Ψ2 map_C2 prog →
    simplify_relation A (unit * B2)%type Φ C2 Ψ2 (λ a c2, (tt, map_C2 a c2)) prog.
  Proof.
    intros [Hsimpl1 Hsimpl2]. split.
    - intros a [[] b2] Hphi.
      apply Hsimpl1 in Hphi as (c & ? & ->).
      eauto.
    - apply Hsimpl2.
  Qed.
  Lemma simplify_relation_prod_unit_r A B1 Φ C1 Ψ1 map_C1 prog :
    simplify_relation A B1 (λ a b1, Φ a (b1, tt)) C1 Ψ1 map_C1 prog →
    simplify_relation A (B1 * unit)%type Φ C1 Ψ1 (λ a c1, (map_C1 a c1, tt)) prog.
  Proof.
    intros [Hsimpl1 Hsimpl2]. split.
    - intros a [b1 []] Hphi.
      apply Hsimpl1 in Hphi as (c & ? & ->).
      eauto.
    - apply Hsimpl2.
  Qed.

  Lemma simplify_relation_atom A B Φ map_B :
    simplify_relation_functional A B Φ map_B →
    simplify_relation A B Φ unit (λ a _, Φ a (map_B a)) (λ a _, map_B a) true.
  Proof.
    intros Hsimpl1.
    split.
    - intros a b Ha. exists tt.
      ospecialize * Hsimpl1; first apply Ha.
      subst. done.
    - intros a _ Ha. done.
  Qed.
  Lemma simplify_relation_atom_keep A B Φ :
    simplify_relation A B Φ B Φ (λ a b, b) false.
  Proof.
    rewrite /simplify_relation. naive_solver.
  Qed.

  Lemma simplify_relation_functional_eq A Φ :
    RelationIsIdentity Φ →
    simplify_relation_functional A A Φ id.
  Proof.
    intros [Hid].
    intros ?? ?%Hid. done.
  Qed.

  Lemma simplify_relation_functional_function A B f Φ :
    RelationIsFunctional Φ f →
    simplify_relation_functional A B Φ f.
  Proof.
    intros [Hid].
    intros ?? ?%Hid. done.
  Qed.
End simplify_relation.

Existing Class simplify_relation.
Existing Class simplify_relation_functional.

Existing Instance simplify_relation_prod | 10.
Existing Instance simplify_relation_atom | 100.
Existing Instance simplify_relation_atom_keep | 1000.
Existing Instance simplify_relation_functional_eq | 10.
Existing Instance simplify_relation_functional_function | 11.
Existing Instances simplify_relation_prod_unit_l simplify_relation_prod_unit_r | 20.

Definition simplify_relation_passes := simplify_relation.

Lemma simplify_relation_make_pass A B C1 C2 Φ Φ' Ψ1 Ψ2 map_C1 map_C2 Ψ3 prog0 prog1 prog2 prog3 :
  (∀ a b, simplify_closure_prop (Φ a b) (Φ' a b) prog0) →
  simplify_relation A B Φ' C1 Ψ1 map_C1 prog1 →
  simplify_relation A C1 Ψ1 C2 Ψ2 map_C2 prog2 →
  (∀ a c2, simplify_closure_prop (Ψ2 a c2) (Ψ3 a c2) prog3) →
  simplify_relation_passes A B Φ C2 Ψ3 (λ a c2, map_C1 a (map_C2 a c2)) (prog0 || prog1 || prog2 || prog3).
Proof.
  unfold simplify_relation_passes, simplify_relation.
  naive_solver.
Qed.

Existing Class simplify_relation_passes.

Existing Instance simplify_relation_make_pass.

Section test.

  Lemma test :
    ∃ C Ψ map_C prog, simplify_relation_passes Z (Z * Z) (λ a '(b1, b2), a = b1 ∧ a = b2) C Ψ map_C prog ∧ map_C = map_C ∧ Ψ = Ψ ∧ prog = true.
  Proof.
    eexists _, _, _, _.
    split.
    { apply _. }
    simpl.
  Abort.

  Lemma test1 :
    ∃ C Ψ map_C prog, simplify_relation_passes (Z * Z) (Z * Z) (λ a b, a.1 = b.1 ∧ a.2 = b.2) C Ψ map_C prog ∧ map_C = map_C ∧ Ψ = Ψ ∧ prog = true.
  Proof.
    eexists _, _, _, _.
    split.
    { apply _. }
    simpl.
  Abort.

  Lemma test2 :
    ∃ C Ψ map_C prog, simplify_relation_passes (Z * Z) (Z * Z) (λ a '(b1, b2), a.1 = b1 ∧ a.2 = b2) C Ψ map_C prog ∧ map_C = map_C ∧ Ψ = Ψ ∧ prog = true.
  Proof.
    eexists _, _, _, _.
    split.
    { apply _. }
    simpl.
  Abort.

  Lemma test3 (clos_states : list (plist (RT_xt ∘ place_rfnRT) [(place_rfn Z * gname)%type : RT])) :
    ∃ C Ψ map_C prog,
      simplify_relation_passes _ _ (λ (p : nat * Z) (b : Z), ∃ (x1 : gname) (x2 : Z) (x3 : gname) (x4 : Z), b = p.2 ∧ (x2, x1) = (x4, x3) ∧ MinInt i32 ≤ 1 + x2 ∧ 1 + x2 ≤ MaxInt i32 ∧ clos_states !! S p.1 = Some -[(1 + x4, x3)] ∧ clos_states !! p.1 = Some -[(x2, x1)]) C Ψ map_C prog ∧
      Ψ = Ψ.
  Proof.
    eexists _, _, _, _.
    split.
    { apply _.  }
    simpl.
  Abort.

  Lemma test4 :
    ∃ C Ψ map_C prog, simplify_relation_passes _ _ (λ (a : Z * gname) (b : Z), ∃ pclos : plist id [], True ∧ (∃ (a0 : Z * gname) (_ : gname), pclos = *[] ∧ *[a] = *[a0] ∧ () = () ∧ a0.1 = 5 ∧ True) ∧ ∃ (a0 : Z * gname) (_ : gname), pclos = *[] ∧ () = () ∧ *[a] = *[a0] ∧ (∃ a1 : Z, b = a1 ∧ a1 = a0.1 ∧  True ∧ () = ()) ∧ True)
      C Ψ map_C prog ∧ Ψ = Ψ.
  Proof.
    eexists _, _, _ ,_.
    split. { apply _. }
    simpl.
  Abort.

End test.

Lemma Forall2_simplify_relation {A B} (Φ : A → B → Prop) l1 l2 C Ψ map_C prog :
  simplify_relation A B Φ C Ψ map_C prog →
  Forall2 Φ l1 l2 ↔ (∃ l3, l2 = fmap (λ p, map_C p.1 p.2) (zip l1 l3) ∧ Forall2 Ψ l1 l3).
Proof.
  intros [Hsimpl1 Hsimpl2].
  induction l1 as [ | a l1 IH] in l2 |-*; destruct l2 as [ | b l2]; simpl.
  { naive_solver. }
  { split. { intros []%Forall2_nil_cons_inv. }
    naive_solver. }
  { split. { intros []%Forall2_cons_nil_inv. }
    intros (l3 & Heq & Hf).
    eapply Forall2_cons_inv_l in Hf as (? & ? & ? & ? & ->).
    done. }
  rewrite Forall2_cons. rewrite IH.
  split.
  - intros (Hhead & (l3 & -> & Hf)). simpl.
    apply Hsimpl1 in Hhead as (c & Hhead & ->).
    exists (c :: l3). eauto.
  - intros (l3 & Heq & Hf).
    apply Forall2_cons_inv_l in Hf as (c & l3' & Hhead & Hf & ->).
    injection Heq. intros -> ->.
    eauto.
Qed.

(* TODO: maybe we can simplify a bit more here. *)
Lemma simpl_impl_Forall2_simplify A B C Φ Ψ map_C l1 l2 prog :
  simplify_relation_passes A B Φ C Ψ map_C prog →
  prog = true →
  SimplImpl prog (Forall2 Φ l1 l2) (λ T, (∃ l3, l2 = fmap (λ p, map_C p.1 p.2) (zip l1 l3) ∧ Forall2 Ψ l1 l3) → T).
Proof.
  intros Hsimpl _ T.
  unfold simplify_relation_passes in Hsimpl.
  rewrite Forall2_simplify_relation. done.
Qed.
Global Hint Extern 10 (SimplImpl _ (Forall2 _ _ _) _) =>
  notypeclasses refine (simpl_impl_Forall2_simplify _ _ _ _ _ _ _ _ _ _ _);
  [typeclasses eauto | done ] : typeclass_instances.

Global Instance simpl_impl_Forall2_unit_r {A} (Φ : A → Prop) l1 (l2 : list unit) :
  SimplImpl true (Forall2 (λ a _, Φ a) l1 l2) (λ T, l2 = replicate (length l1) tt → Forall Φ l1 → T).
Proof.
  intros T. split.
  - intros Hcont Hf.
    opose proof* Forall2_length as Hlen; first apply Hf.
    eapply Hcont.
    { move: Hlen. generalize (length l1).
      induction n as [ | n IH] in l2 |-*; simpl.
      - destruct l2; naive_solver.
      - destruct l2 as [ | [] ?]; first naive_solver.
        simpl. intros. f_equiv. apply IH. lia. }
    eapply Forall2_Forall_l; first apply Hf.
    simpl. apply Forall_true. done.
  - intros Hcont -> Hf. apply Hcont.
    apply Forall_Forall2_l.
    + rewrite length_replicate//.
    + eapply Forall_impl; first apply Hf. done.
Qed.

(* Some more ideas:
   - maybe split up clos_states when introducing and turn it into zipped lists.
     this should make it somewhat easier to derive that some components stay equal.
   -
  *)
