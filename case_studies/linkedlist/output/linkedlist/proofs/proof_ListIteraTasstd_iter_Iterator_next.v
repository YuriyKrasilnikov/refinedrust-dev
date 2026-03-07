From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_ListIteraTasstd_iter_Iterator_next.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma ListIteraTasstd_iter_Iterator_next_proof (π : thread_id) :
  ListIteraTasstd_iter_Iterator_next_lemma π.
Proof.
  pose_unconstrained_lft_hint "vuclft5" ["ulft_a"].
  ListIteraTasstd_iter_Iterator_next_prelude.

  rep <-! liRStep; liShow.
  rep <-! liRStep; liShow.
  move: Hlocs.
  rep <-! liRStep.
  rename select (head locs = _) into Hhead.
  rewrite head_lookup in Hhead.
  
  match type of Hlen_eq with length _ = length ?x => rename x into xs end.
  destruct xs as [ | x_head xs]; first by simpl in *.
  destruct locs as [ | hl locs]; first done.
  iRename select ([∗ list] _ ↦ _ ∈ _, _)%I into "Hxs".
  simpl. iDestruct "Hxs" as "(Hx & Hxs)".
  iRevert "Hx".
  move: Hhead. 
  rep <-! liRStep. liShow.
  apply_update updateable_strip_guards.
  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  liInst Hevar_rf (<$#> xs).
  liInst Hevar_locs locs.
  rep <-! liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - move: Hlocs. solve_goal.
  - rename select (Forall _ locs) into Hlocs.
    destruct (decide (loc_a lnext = 0)). 
    + case_bool_decide.
      * exfalso. destruct locs as [ | lh locs]; first done.
        simpl in *. simplify_eq. 
        apply Forall_cons in Hlocs as [? ?]. done.
      * simplify_eq. split; last done.
        destruct locs; simpl in *; last lia.
        destruct xs; last done. done.
    + case_bool_decide; last by simplify_eq.
      destruct locs as [ | lh locs]; first done.
      simpl in *. simplify_eq. 
      destruct xs; first done. done.

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
