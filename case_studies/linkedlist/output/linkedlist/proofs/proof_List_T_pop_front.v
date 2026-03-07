From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_List_T_pop_front.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma List_T_pop_front_proof (π : thread_id) :
  List_T_pop_front_lemma π.
Proof.
  List_T_pop_front_prelude.

  rep <-! liRStep; liShow.
  move: Hlocs.
  rep <-! liRStep; liShow.
  iRename select ([∗ list] _ ↦ _ ∈ _, _)%I into "Hels".
  destruct self as [ | head_el self]; first done.
  rename select (head locs = Some _) into Hhead.
  apply head_Some in Hhead as (locs' & ->).
  (* also move out ownership from the pointer before doing the read *)
  iRevert "Hels". simpl.
  liRStepUntil typed_call.
  apply_update updateable_strip_guards.

  rep <-! liRStep. liShow.
  rep liRStep; liShow.
  liInst Hevar_rf (<$#> self).
  liInst Hevar_locs locs'.
  rep liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  all: try rename select (if bool_decide _ then _ else _) into Hcase.
  - move: Hlocs. solve_goal.
  - move: Hlocs. solve_goal.
  - move: Hcase.
    case_bool_decide.
    + (* contradiction, but only if I have ownership *)
      intros Hlook.
      opose proof (Forall_lookup_1 _ _ _ _ _ Hlook) as Hnull; first done.
      done.
    + solve_goal.
  - move: Hcase.
    case_bool_decide.
    + intros Hlook.
      opose proof (Forall_lookup_1 _ _ _ _ _ Hlook) as Hnull; first done.
      done.
    + intros [= <-].
      destruct self; first done.
      destruct locs' as [ | l' locs']; simpl in *; lia.
  - rewrite -Hlen_eq.
    move: Hcase. case_bool_decide; solve_goal.
  - move: Hcase. case_bool_decide; last solve_goal.
    rewrite head_lookup. done.
  - rename select (last _ = Some _) into Hlast.
    move: Hlast. rewrite !last_lookup.
    simpl. destruct locs'; simpl in *; first lia.
    done.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
