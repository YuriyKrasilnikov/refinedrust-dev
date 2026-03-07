From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_List_T_push_back.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma head_app_l {A} (l1 l2 : list A) :
  length l1 > 0 →
  head (l1 ++ l2) = head l1.
Proof.
  rewrite head_app.
  destruct l1 as [ | x l1]; simpl; first lia.
  done.
Qed.
Hint Rewrite -> @head_app_l using lia : lithium_rewrite.
Hint Rewrite -> @last_lookup : lithium_rewrite.
Hint Rewrite Nat.sub_1_r : lithium_rewrite.

Lemma simplify_goal_big_sepL_app {A} (xs1 xs2 : list A) (Φ : nat → A → iProp Σ) T:
  ([∗ list] i↦x ∈ xs1, Φ i x) ∗ ([∗ list] i↦x ∈ xs2, Φ (length xs1 + i)%nat x) ∗ T
  ⊢ simplify_goal ([∗ list] i ↦ x ∈ xs1 ++ xs2, Φ i x) T.
Proof.
  rewrite /simplify_goal.
  rewrite big_sepL_app.
  iIntros "($ & $ & $)".
Qed.
Definition simplify_goal_big_sepL_app_inst := [instance @simplify_goal_big_sepL_app with 10%N].
Global Existing Instance simplify_goal_big_sepL_app_inst.

Lemma List_T_push_back_proof (π : thread_id) :
  List_T_push_back_lemma π.
Proof.
  List_T_push_back_prelude.

  rep <-! liRStep; liShow.
  { rep liRStep. liShow.
    (* manual step because of the projection.. Can I figure out a way to improve this? *)
    move: Hlocs.
    rep liRStep.
    liInst Hevar_rf ([$# value]).
    liInst Hevar_locs ([x']).
    liShow. rep liRStep. }
  rep <-! liRStep. liShow.
  revert Hlocs.
  rep <-! liRStep.

  (* acquire ownership of the last link *)
  iRename select ([∗ list] i ↦ _ ∈ _, _)%I into "Hold".
  odestruct (lookup_lt_is_Some_2 self (length self - 1) _) as (last_elem & Hlook).
  { lia. }
  iPoseProof (big_sepL_delete _ _ (length self - 1) with "Hold") as "(Hlast & Hcl)".
  { rewrite list_lookup_fmap. rewrite Hlook//. }
  rename select (_ !! _ = Some tl_ptr) into Hlook_last.
  rewrite Hlen_eq in Hlook_last.
  iRevert "Hlast".

  rep <-! liRStep. liShow.
  apply_update (updateable_strip_guards).
  rep <-! liRStep; liShow.

  iAcquireCredits as "Hcred1".
  iAcquireCredits as "Hcred2".
  rep liRStep; liShow.

  liInst Hevar_rf (($# self) ++ [$# value]).
  liInst Hevar_locs (locs ++ [x']).

  rep liRStep; liShow.

  (* show ownership for the new linked list *)
  iApply (prove_with_subtype_stratify l0).
  rep liRStep. liShow.
  iApply prove_with_subtype_default.
  iRename select ((x' ◁ₗ[_, _] _ @ _))%I into "Hnew".
  iRename select (freeable_nz l0 _ _ _) into "Hfree_old".
  iRename select (freeable_nz x' _ _ _) into "Hfree".
  (*iRename select ((l0 ◁ₗ[_, _] _ @ _))%I into "Hold".*)
  iSplitL "Hcl Hfree_old Hcred1".
  { iIntros "Hold". rep liRStep. liShow.
    iApply (big_sepL_delete  _ _ (length self - 1)).
    { rewrite list_lookup_fmap. rewrite Hlook//. }
    liShow. rep liRStep; liShow.
    iApply (big_sepL_impl with "Hcl").
    iModIntro. iIntros (k ??).
    destruct (decide (k = (length self - 1)%nat)); first done.
    rep liRStep. done. }
  rep liRStep.
  rewrite Hlen_eq. rewrite Nat.sub_diag/=.
  rep liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - apply Forall_app; solve_goal.
  - rewrite Hlen_eq Nat.sub_diag//.
  - replace (S (length self) - length self)%nat with 1%nat by lia.
    done.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
