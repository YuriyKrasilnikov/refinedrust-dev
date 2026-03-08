From iris.proofmode Require Import string_ident.
From lithium Require Export base.
From lithium Require Import hooks simpl_classes pure_definitions normalize.

(** This file provides various pure solvers. *)

(** * [refined_solver]
    Version of naive_solver which fails faster. *)
Ltac refined_solver_init :=
  unfold iff, not in *;
  repeat match goal with
  | H : context [∀ _, _ ∧ _ ] |- _ =>
    repeat setoid_rewrite forall_and_distr in H; revert H
  | H : context [Is_true _ ] |- _ =>
    repeat setoid_rewrite Is_true_eq in H
  | |- Is_true _ => repeat setoid_rewrite Is_true_eq
  end.
Ltac refined_solver tac := fail.
Ltac refined_solver_norec tac := fail.
Ltac refined_solver_step_1 tac :=
  match goal with
  (**i solve the goal *)
  | |- _ => fast_done
  (**i intros *)
  | |- ∀ _, _ => intro
  (**i simplification of assumptions *)
  | H : False |- _ => destruct H
  | H : _ ∧ _ |- _ =>
     (* Work around bug https://github.com/rocq-prover/rocq/issues/2901 *)
     let H1 := fresh in let H2 := fresh in
     destruct H as [H1 H2]; try clear H
  | H : ∃ _, _  |- _ =>
     let x := fresh in let Hx := fresh in
     destruct H as [x Hx]; try clear H
  | H : ?P → ?Q, H2 : ?P |- _ => specialize (H H2)
  (**i simplify and solve equalities *)
  (* | |- _ => progress simplify_eq/= *)
  | |- _ => progress subst; csimpl in *
  (**i operations that generate more subgoals *)
  | |- _ ∧ _ => split
  (* | |- Is_true (bool_decide _) => apply (bool_decide_pack _) *)
  (* | |- Is_true (_ && _) => apply andb_True; split *)
  | H : _ ∨ _ |- _ =>
     let H1 := fresh in destruct H as [H1|H1]; try clear H
  (* | H : Is_true (_ || _) |- _ => *)
     (* apply orb_True in H; let H1 := fresh in destruct H as [H1|H1]; try clear H *)
  (**i solve the goal using the user supplied tactic *)
  | |- _ => solve [tac]
  end.
Ltac refined_solver_step_2 tac :=
  (**i use recursion to enable backtracking on the following clauses. *)
  match goal with
  (**i instantiation of the conclusion *)
  | |- ∃ x, _ => no_new_unsolved_evars ltac:(eexists; refined_solver tac)
  | |- _ ∨ _ => first [left; refined_solver tac | right; refined_solver tac]
  (* | |- Is_true (_ || _) => apply orb_True; first [left; go | right; go] *)
  | _ =>
    (**i instantiations of assumptions. *)
    match goal with
    | H : ?P → ?Q |- _ =>
      let H' := fresh "H" in
      (* When instantiating an assumption, we can prune early and do not descend further recursively.
         Otherwise, we should just have instantiated something else first to afterwards make progress when instantiating this assumption. *)
      assert P as H'; [clear H; refined_solver_norec tac | specialize (H H'); clear H']
    end
  end.
Ltac refined_solver_step_2_norec tac :=
  (**i use recursion to enable backtracking on the following clauses. *)
  match goal with
  (**i instantiation of the conclusion *)
  | |- ∃ x, _ => no_new_unsolved_evars ltac:(eexists; refined_solver tac)
  | |- _ ∨ _ => first [left; refined_solver tac | right; refined_solver tac]
  end.

Ltac refined_solver_step tac :=
  repeat (refined_solver_step_1 tac); (refined_solver_step_2 tac).
Ltac refined_solver tac ::=
  solve [refined_solver_init; repeat (refined_solver_step tac)].

Ltac refined_solver_step_norec tac :=
  repeat (refined_solver_step_1 tac); (refined_solver_step_2_norec tac).
Ltac refined_solver_norec tac ::=
  solve [refined_solver_init; repeat (refined_solver_step_norec tac)].

Tactic Notation "refined_solver" tactic(t) := refined_solver t.
Tactic Notation "refined_solver" := refined_solver eauto.

(** * [normalize_and_simpl_goal] *)
Ltac normalize_and_simpl_impl handle_exist :=
  let discr :=
    lazymatch goal with
    | |- discriminate_hint ?P → ?Q =>
        constr:(true)
    | |- _ => constr:(false)
    end in
  let hint :=
    lazymatch goal with
    | |- name_hint ?h ?P -> ?Q =>
        constr:(Some h)
    | |- _ => constr:(@None String.string)
    end in
  try lazymatch goal with
  | |- discriminate_hint ?P → ?Q =>
      change_no_check (P → Q)
  | |- name_hint _ ?P → ?Q =>
      change_no_check (P → Q)
  | |- shelve_hint ?P → ?Q =>
      change_no_check (P → Q)
  | |- destruct_hint ?x ?P → ?Q =>
      change_no_check (P x → Q)
  end;
  let add_hint :=
    idtac;
    match goal with
    | |- ?P → ?Q =>
      match discr with
      | true =>
        change_no_check (discriminate_hint P → Q)
      | false =>
        match hint with
        | Some ?h =>
          change_no_check (name_hint h P → Q)
        | None =>
          idtac
        end
      end
    | |- _ =>
        (* the goal shape might have changed due to simplification, in this case drop the hint *)
        idtac
    end
  in
  let do_intro :=
    idtac;
    match goal with
    | |- (∃ _, _) → _ =>
        lazymatch handle_exist with
        | true => case
        | false => fail 1 "exist not handled"
        end
    | |- (_ = _) → _ =>
        hooks.check_injection_hook;
        let Hi := fresh "Hi" in move => Hi; injection Hi; clear Hi
    | |- (?x = _) → _ =>
        is_var x;
        let He := fresh "Heq" in move => He;
        repeat match goal with
               | H : context[x] |- _ =>
                   assert_fails (unify H He);
                   before_revert_hook H;
                   revert H
                   (*generalize dependent H*)
        end;
        subst
    | |- (_ = ?x) → _ =>
        is_var x;
        let He := fresh "Heq" in move => He;
        repeat match goal with
               | H : context[x] |- _ =>
                   assert_fails (unify H He);
                   before_revert_hook H;
                   revert H
                   (*generalize dependent H*)
        end;
        subst
    | |- False → _ => intros []
    | |- ?P → _ =>
        match discr with
        | true =>
          let Hd := fresh "Hd" in move => Hd; try discriminate Hd
        | false =>
          match hint with
          | Some ?h =>
            string_ident.string_to_ident_cps h ltac:(fun H => first [intros H | intros ?])
          | None =>
              assert_is_not_trivial P;
              let H := fresh in
              intros H; hooks.after_intro_hook H
          end
        end
    | |- _ => move => _
    end
  in
  lazymatch goal with
  (* relying on the fact that unification variables cannot contain
  dependent variables to distinguish between dependent and non
  dependent forall *)
  | |- ?P -> ?Q =>
    lazymatch type of P with
    | Prop => first [
        (* first check if the hyp is trivial *)
        assert_is_trivial P; intros _
      | (progress normalize_goal_impl); add_hint
      | let changed := open_constr:(_) in
        notypeclasses refine (@simpl_impl_unsafe changed P _ _ Q _); [solve [refine _] |];
        (* We need to simpl here to make sure that we only introduce
        fully simpl'd terms into the context (and do beta reduction
        for the lemma application above). *)
        simpl;
        let changed := eval simpl in changed in
        lazymatch changed with
        | true => add_hint
        | false => do_intro
        end
      | do_intro
      ]
    (* just some unused variable, forget it *)
    | _ => move => _
    end
  end.

Lemma intro_and_True P :
  (P ∧ True) → P.
Proof. naive_solver. Qed.

Ltac normalize_and_simpl_goal_step :=
  first [
      lazymatch goal with
      | |- _ ∧ _ => split; [splitting_fast_done|]
      | _ => splitting_fast_done
      end
    |
      progress normalize_goal; simpl
    |
      lazymatch goal with
      | |- ∃ _, _ => fail 1 "normalize_and_simpl_goal stop in exist"
      end
    |
      lazymatch goal with
      | |- _ ∧ _ => idtac
      | _ => refine (intro_and_True _ _)
      end;
      lazymatch goal with
      | |- ?P ∧ ?Q =>
        notypeclasses refine (@simpl_and_unsafe P _ _ Q _); [solve [refine _] |];
        simpl;
        split_and?
      end
    | lazymatch goal with
    (* relying on the fact that unification variables cannot contain
       dependent variables to distinguish between dependent and non dependent forall *)
      | |- ?P -> ?Q =>
        normalize_and_simpl_impl true
      | |- forall _ : ?P, _ =>
        lazymatch P with
        | (prod _ _) => case
        | unit => case
        | _ => intro
        end
    end ].

Ltac normalize_and_simpl_goal := repeat normalize_and_simpl_goal_step.

(** * [compute_map_lookup] *)
Ltac compute_map_lookup :=
  lazymatch goal with
  | |- ?Q !! _ = Some _ => try (is_var Q; unfold Q)
  | _ => fail "unknown goal for compute_map_lookup"
  end;
  solve [repeat lazymatch goal with
  | |- <[?x:=?s]> ?Q !! ?y = Some ?res =>
    lazymatch x with
    | y => change_no_check (Some s = Some res); reflexivity
    | _ => change_no_check (Q !! y = Some res)
    end
  end ].

(** * Enriching the context for lia  *)
Definition enrich_marker {A} (f : A) : A := f.
Ltac enrich_context_base :=
    repeat match goal with
         | |- context C [ Z.quot ?a ?b ] =>
           let G := context C[enrich_marker Z.quot a b] in
           change_no_check G;
           try have ?:=Z.quot_lt a b ltac:(lia) ltac:(lia);
           try have ?:=Z.quot_pos a b ltac:(lia) ltac:(lia)
         | |- context C [ Z.rem ?a ?b ] =>
           let G := context C[enrich_marker Z.rem a b] in
           change_no_check G;
           try have ?:=Z.rem_bound_pos a b ltac:(lia) ltac:(lia)
         | |- context C [ Z.modulo ?a ?b ] =>
           let G := context C[enrich_marker Z.modulo a b] in
           change_no_check G;
           try have ?:=Z.mod_bound_pos a b ltac:(lia) ltac:(lia)
         | |- context C [ length (filter ?P ?l) ] =>
           let G := context C[enrich_marker length (filter P l)] in
           change_no_check G;
           pose proof (length_filter P l)
           end.

Ltac enrich_context :=
  enrich_context_base;
  enrich_context_hook;
  unfold enrich_marker.

Section enrich_test.
  Local Open Scope Z_scope.
  Goal ∀ n m, 0 < n → 1 < m → n `quot` m = n `rem` m.
    move => n m ??. enrich_context.
  Abort.
End enrich_test.

(** * [solve_goal]  *)
Ltac reduce_closed_Z :=
  idtac;
  reduce_closed_Z_hook;
  repeat match goal with
  | |- context [(?a ≪ ?b)%Z] => progress reduce_closed (a ≪ b)%Z
  | H : context [(?a ≪ ?b)%Z] |- _ => progress reduce_closed (a ≪ b)%Z
  | |- context [(?a ≫ ?b)%Z] => progress reduce_closed (a ≫ b)%Z
  | H : context [(?a ≫ ?b)%Z] |- _ => progress reduce_closed (a ≫ b)%Z
  end.

Tactic Notation "solve_goal" "with" tactic(tac) :=
  simpl;
  try fast_done;
  solve_goal_prepare_hook;
  normalize_and_simpl_goal;
  solve_goal_normalized_prepare_hook; reduce_closed_Z; enrich_context;
  repeat case_bool_decide => //; repeat case_decide => //; repeat case_match => //;
  tac.
Tactic Notation "solve_goal" :=
  solve_goal with solve_goal_final_hook.


(** rep

 The [rep] tactic is an alternative to the [repeat] and [do] tactics
 that supports left-biased depth-first branching with optional
 backtracking on failure. *)

(* A backtrack point marker *)
Definition BACKTRACK_POINT {A} (P : A) : A := P.
Arguments BACKTRACK_POINT : simpl never.
Global Typeclasses Opaque BACKTRACK_POINT.

(* For instance, we could redefine the hook as follows: *)
(*
Ltac rep_check_backtrack_point_hook ::=
  match goal with
    | |- BACKTRACK_POINT ?P =>
      idtac
  end.
 *)

Module Rep.
  Import Ltac2.
  Import Ltac2.Printf.

  (* Check whether the current goal is a backtracking point *)
  Ltac2 rep_check_backtrack_point (_ : unit) : bool :=
    let tac_res := Control.focus 1 1 (fun _ => Control.case (fun _ => ltac1:(rep_check_backtrack_point_hook))) in
    match tac_res with
    | Err _ => false
    | Val _ => true
    end.

  (* Backtracking mode:
     - NoBacktrack: don't backtrack
     - BacktrackSteps n: backtrack to n steps before failure
     - BacktrackPoint n: go back to the n-th last goal for which [rep_check_backtrack_point] succeeded *)
  Ltac2 Type backtrack_mode := [ NoBacktrack | BacktrackSteps (int) | BacktrackPoint (int) ].

  (* Exception to signal how many more steps should be backtracked*)
  Ltac2 Type exn ::= [ RepBacktrack (backtrack_mode) ].

  (* calls [tac] [n] times (n = None means infinite) on the first goal
  under focus, stops on failure of [tac] and then backtracks according to [nback]. *)
  Ltac2 rec rep (n : int option) (nback : backtrack_mode) (tac : (unit -> unit)) : int :=
    (* if there are no goals left, we are done *)
    match Control.case (fun _ => Control.focus 1 1 (fun _ => ())) with
    | Err _ => 0
    | Val _ =>
      (* check if we should do another repetition *)
      let do_rep := match n with | None => true | Some n => Int.gt n 0 end in
      match do_rep with
      | false => 0
      | true =>
        (* maybe we should match on the goal here *)
        let is_backtrack_point := Control.focus 1 1 (fun _ => rep_check_backtrack_point ()) in
        (* backtracking point *)
        let res := Control.case (fun _ =>
          (* run tac on the first goal *)
          let tac_res := Control.focus 1 1 (fun _ => Control.case tac) in
          match tac_res  with
          | Err _ =>
              (* if tac failed, start the backtracking *)
              Control.zero (RepBacktrack nback)
          | Val _ =>
              (* compute new n and recurse *)
              let new_n :=
                match n with | None => None | Some n => Some (Int.sub n 1) end in
              let n_steps := rep new_n nback tac in
              Int.add n_steps 1
          end) in
        match res with
        | Err e =>
            match e with
            (* check if we have to backtrack *)
            | RepBacktrack m =>
                match m with
                | BacktrackSteps n =>
                  (* either rethrow it with one less or return 0 *)
                  match Int.gt n 0 with
                  | true => Control.zero (RepBacktrack (BacktrackSteps (Int.sub n 1)))
                  | false => 0
                  end
                | BacktrackPoint n =>
                    match Int.gt n 0 with
                    | true =>
                      (* check if we are at the last backtracking point or rethrow it *)
                      match is_backtrack_point with
                      | true =>
                        match Int.gt n 1 with
                        | true =>
                          Control.zero (RepBacktrack (BacktrackPoint (Int.sub n 1)))
                        | false => 0
                        end
                      | false => Control.zero (RepBacktrack (BacktrackPoint n))
                      end
                    | false => 0
                    end
                | NoBacktrack => 0
                end
            | _ => Control.zero e
            end
        | Val (r, _) => r
        end
      end
    end.

  Ltac2 print_steps (n : int) :=
    printf "Did %i steps." n.

  Ltac2 rec pos_to_ltac2_int (n : constr) : int :=
    lazy_match! n with
    | xH => 1
    | xO ?n => Int.mul (pos_to_ltac2_int n) 2
    | xI ?n => Int.add (Int.mul (pos_to_ltac2_int n) 2) 1
    end.

  Ltac2 rec z_to_ltac2_int (n : constr) : int :=
    lazy_match! n with
    | Z0 => 0
    | Z.pos ?n => pos_to_ltac2_int n
    | Z.neg ?n => Int.neg (pos_to_ltac2_int n)
    end.

  (* TODO: use a mutable record field, see Janno's message *)

  (* Calls tac on a new subgoal of type Z and converts the resulting Z
  to an int. *)
  Ltac2 int_from_z_subgoal (tac : unit -> unit) : int :=
    let x := Control.focus 1 1 (fun _ =>
      let x := open_constr:(_ : Z) in
      match Constr.Unsafe.kind x with
      | Constr.Unsafe.Cast x _ _ =>
          match Constr.Unsafe.kind x with
          | Constr.Unsafe.Evar e _ =>
              Control.new_goal e;
              x
          | _ => Control.throw Assertion_failure
          end
      | _ => Control.throw Assertion_failure
      end) in
    (* new goal has index 2 because it was added after goal number 1 *)
    Control.focus 2 2 (fun _ =>
      tac ();
      (* check that the goal is closed *)
      Control.enter (fun _ => Control.throw Assertion_failure));
    Control.focus 1 1 (fun _ =>
      let x := Std.eval_vm None x in
      z_to_ltac2_int x).

  (* Necessary because Some and None cannot be used in ltac2: quotations. *)
  Ltac2 some (n : int) : int option := Some n.
  Ltac2 none : int option := None.
End Rep.

(** rep repeatedly applies tac to the goal in a depth-first manner. In
particular, if tac generates multiple subgoals, the process continues
with the first subgoal and only looks at the second subgoal if the
first subgoal (and all goals spawed from it) are solved. If [tac]
fails, the complete process stops (unlike [repeat] which continues
with other subgoals).

[rep n tac] iterates this process at most n times.
[rep <- n tac] backtracks n steps on failure.
[rep <-! tac] backtracks to the last backtracking point on failure.
 (See the comment on [rep_check_backtrack_point] above to see what a backtracking point is)
[rep <-? n tac] backtracks to the n-th last backtracking point on failure.
*)
Tactic Notation "rep" tactic3(tac) :=
  let r := ltac2:(tac |-
    Rep.print_steps (Rep.rep Rep.none Rep.NoBacktrack (fun _ => Ltac1.run tac))) in
  r tac.

(* rep is carefully written such that all goals are passed to Ltac2
and rep can apply tac in a depth-first manner to only the first goal.
In particular, the behavior of [all: rep 10 tac.] is equivalent to
[all: rep 5 tac. all: rep 5 tac.], even if the first call spawns new
subgoals. (See also the tests.) *)
Tactic Notation "rep" int(n) tactic3(tac) :=
  let ntac := do n (refine (1 + _)%Z); refine 0%Z in
  let r := ltac2:(ntac tac |-
    let n := Rep.int_from_z_subgoal (fun _ => Ltac1.run ntac) in
    Rep.print_steps (Rep.rep (Rep.some n) Rep.NoBacktrack (fun _ => Ltac1.run tac))) in
  r ntac tac.

Tactic Notation "rep" "<-" int(n) tactic3(tac) :=
  let ntac := do n (refine (1 + _)%Z); refine 0%Z in
  let r := ltac2:(ntac tac |-
     let n := Rep.int_from_z_subgoal (fun _ => Ltac1.run ntac) in
     Rep.print_steps (Rep.rep (Rep.none) (Rep.BacktrackSteps n) (fun _ => Ltac1.run tac))) in
  r ntac tac.

Tactic Notation "rep" "<-!" tactic3(tac) :=
  let r := ltac2:(tac |-
    Rep.print_steps (Rep.rep Rep.none (Rep.BacktrackPoint 1) (fun _ => Ltac1.run tac))) in
  r tac.

Tactic Notation "rep" "<-?" int(n) tactic3(tac) :=
  let ntac := do n (refine (1 + _)%Z); refine 0%Z in
  let r := ltac2:(ntac tac |-
     let n := Rep.int_from_z_subgoal (fun _ => Ltac1.run ntac) in
     Rep.print_steps (Rep.rep (Rep.none) (Rep.BacktrackPoint n) (fun _ => Ltac1.run tac))) in
  r ntac tac.

Module RepTest.
  Definition DELAY (P : Prop) : Prop := P.

  Ltac DELAY_test_tac :=
    first [
        lazymatch goal with | |- DELAY ?P => change P end |
        exact eq_refl |
        split |
        lazymatch goal with | |- BACKTRACK_POINT ?P => change P end
      ].
  Local Ltac rep_check_backtrack_point_hook ::=
    match goal with
    | |- BACKTRACK_POINT ?P =>
      idtac
    end.

  Goal ∃ x, Nat.iter 10 DELAY (x = 1) ∧ Nat.iter 6 DELAY (x = 2). simpl. eexists.
    all: rep DELAY_test_tac.
    1: lazymatch goal with | |- 1 = 2 => idtac | |- _ => fail "unexpected goal" end.
  Abort.

  Goal ∃ x, Nat.iter 10 DELAY (x = 1) ∧ Nat.iter 6 DELAY (x = 2). simpl. eexists.
    all: rep 5 DELAY_test_tac.
    1: lazymatch goal with | |- DELAY (DELAY (DELAY (DELAY (DELAY (DELAY (_ = 1)))))) => idtac | |- _ => fail "unexpected goal" end.
    2: lazymatch goal with | |- DELAY (DELAY (DELAY (DELAY (DELAY (DELAY (_ = 2)))))) => idtac | |- _ => fail "unexpected goal" end.
    (* This should only apply tac to the first subgoal. *)
    all: rep 5 DELAY_test_tac.
    1: lazymatch goal with | |- DELAY (_ = 1) => idtac | |- _ => fail "unexpected goal" end.
    2: lazymatch goal with | |- DELAY (DELAY (DELAY (DELAY (DELAY (DELAY (_ = 2)))))) => idtac | |- _ => fail "unexpected goal" end.
    (* This finishes the first subgoal and use the remaining steps on
    the second subgoal. *)
    all: rep 5 DELAY_test_tac.
    1: lazymatch goal with | |- DELAY (DELAY (DELAY (1 = 2))) => idtac | |- _ => fail "unexpected goal" end.
  Abort.

  Goal ∃ x, Nat.iter 10 DELAY (x = 1) ∧ Nat.iter 6 DELAY (x = 2). simpl. eexists.
    repeat DELAY_test_tac.
    (* Same as rep above. *)
  Abort.

  Goal ∃ x, Nat.iter 10 DELAY (x = 1) ∧ Nat.iter 6 DELAY (x = 2). simpl. eexists.
    do 5? (DELAY_test_tac).
    (* Notice the difference to [rep] above: [do] also applies the
    steps to the second subgoal. *)
  Abort.

  Goal ∃ x, Nat.iter 10 DELAY (x ≤ 1) ∧ Nat.iter 6 DELAY (x = 2). simpl. eexists.
    rep <-3 DELAY_test_tac.
    1: lazymatch goal with | |- DELAY (DELAY (DELAY (_ ≤ 1))) => idtac | |- _ => fail "unexpected goal" end.
    2: lazymatch goal with | |- DELAY (DELAY (DELAY (DELAY (DELAY (DELAY (_ = 2)))))) => idtac | |- _ => fail "unexpected goal" end.
  Abort.

  Goal ∃ x, Nat.iter 10 DELAY (x ≤ 1) ∧ Nat.iter 6 DELAY (x = 2). simpl. eexists.
    repeat DELAY_test_tac.
    (* Notice the difference to [rep] above: [repeat] continues with
    the second subgoal on failure. *)
  Abort.

  Goal BACKTRACK_POINT (Nat.iter 10 DELAY (BACKTRACK_POINT (BACKTRACK_POINT (Nat.iter 10 DELAY (1 = 2))))). simpl.
    all: rep <-! DELAY_test_tac.
    all: do 11 DELAY_test_tac.
    1: lazymatch goal with | |- 1 = 2 => idtac | |- _ => fail "unexpected goal" end.
  Abort.

  Goal BACKTRACK_POINT (Nat.iter 10 DELAY (BACKTRACK_POINT (BACKTRACK_POINT (Nat.iter 10 DELAY (1 = 2))))). simpl.
    all: rep <-? 3 DELAY_test_tac.
    all: do 23 DELAY_test_tac.
    1: lazymatch goal with | |- 1 = 2 => idtac | |- _ => fail "unexpected goal" end.
  Abort.

End RepTest.

