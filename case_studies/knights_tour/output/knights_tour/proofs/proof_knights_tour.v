From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.knights_tour.generated Require Import generated_code_knights_tour generated_specs_knights_tour generated_template_knights_tour.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Check SimplImpl.

Global Instance simpl_impl_elem_of_nil {A} (x : A) :
  SimplImpl true (x ∈ []) (λ T, False → T).
Proof.
  unfold SimplImpl. intros. rewrite elem_of_nil. done.
Qed. 

Lemma knights_tour_proof (π : thread_id) :
  knights_tour_lemma π.
Proof.
  knights_tour_prelude.

  rep  500 liRStep.
  rep  500 liRStep.
  rep  500 liRStep.
  rep  500 liRStep.
  rep  500 liRStep.
  rep  500 liRStep.
  rep  500 liRStep.
  rep  500 liRStep.
  rep  500 liRStep.
  rep  500 liRStep.
  rep  500 liRStep.
  rep  500 liRStep.
  rep  500 liRStep.
  rep  500 liRStep.
  rep  500 liRStep.
  { rep liRStep. }
  rep liRStep.
  (*rep <-! liRStep; liShow.*)


  (*{ rep <- 20 liRStep. liShow.*)
  (*  rewrite! wrap_to_it_id; [ | solve_goal..].*)
  (*  (*liInst Hevar_x1 0.*)*)
  (*  admit.*)
  (*}*)

  all: print_remaining_goal.
  
  Unshelve.
(*18: { }*)
  all: sidecond_solver.
  all: try rewrite! wrap_to_it_id; [ | solve_goal..].
  all: try solve [exfalso; rename select (_ ∈ []) into Hempt;inversion Hempt].
  all: cbn.
  - sidecond_hammer.
  - sidecond_hammer.
  - sidecond_hammer.
  - sidecond_hammer.
  - rename select (∀ a b : Z, _ -> a ≤ 2 ∧ _) into Hbound.
    have Hmem : *[x'5; s] ∈ _iter_hist_35 ++ -[x'5; s] :: x'3.
    { rewrite elem_of_app. right. rewrite elem_of_cons. left. done. }
    apply Hbound in Hmem.
    solve_goal.
  - rename select (∀ a b : Z, _ -> a ≤ 2 ∧ _) into Hbound.
    have Hmem : *[x'5; s] ∈ _iter_hist_35 ++ -[x'5; s] :: x'3.
    { rewrite elem_of_app. right. rewrite elem_of_cons. left. done. }
    apply Hbound in Hmem.
    solve_goal.
  - rename select (True -> in_bounds _ _) into Hinbounds.
    cbn in Hinbounds. unfold in_bounds in Hinbounds. cbn in Hinbounds. by apply Hinbounds.
  - rename select (True -> in_bounds _ _) into Hinbounds.
    cbn in Hinbounds. unfold in_bounds in Hinbounds. 
    cbn in Hinbounds. unfold name_hint in Hinbounds.
    solve_goal.
  - rename select (True -> in_bounds _ _) into Hinbounds.
    cbn in Hinbounds. unfold in_bounds in Hinbounds. cbn in Hinbounds. unfold name_hint in Hinbounds.
    solve_goal.
  - rename select (in_bounds (Z.to_nat size) _) into Hinbounds.
    cbn in Hinbounds. unfold in_bounds in Hinbounds. cbn in Hinbounds. unfold name_hint in Hinbounds.
    rewrite Z2Nat.id in Hinbounds; last done.
    solve_goal.
  - rename select (in_bounds (Z.to_nat size) _) into Hinbounds.
    cbn in Hinbounds. unfold in_bounds in Hinbounds. cbn in Hinbounds. unfold name_hint in Hinbounds.
    rewrite Z2Nat.id in Hinbounds; last done.
    solve_goal.
  - sidecond_hammer.
  - assert (length candidates + length candidates ≤ 16). 
    { lia. }
    assert (Hsoab_mono : ∀ (a b : nat) τ, a ≤ b -> size_of_array_in_bytes τ a ≤ size_of_array_in_bytes τ b).
    { intros a' b' st Haleb. unfold size_of_array_in_bytes. by nia. }
    etrans.
    { apply (Hsoab_mono (length candidates + length candidates)%nat 16%nat). solve_goal. }
    done.
  - unfold name_hint.
    rename select (_ ∈ _) into Hincands.
    rename select (∀ z, z ∈ candidates -> _) into Hcandsinbnds.
    cbn in Hincands. apply elem_of_app in Hincands.
    destruct Hincands as [Hcand | Hsing].
    + apply Hcandsinbnds in Hcand. cbn in Hcand.
      unfold in_bounds in Hcand. cbn in Hcand.
      by apply Hcand.
    + rewrite list_elem_of_singleton in Hsing.
      inversion Hsing; subst.
      rename select (in_bounds (Z.to_nat size) _) into Hib.
      cbn in Hib. unfold in_bounds in Hib.
      by apply Hib.
  - rewrite! Nat2Z.inj_succ.
    rewrite -Z.succ_le_mono.
    done.
  - rewrite! Nat2Z.inj_succ.
    apply Z.le_le_succ_r.
    done.
  - unfold name_hint.
    rename select (_ ∈ _) into Hincands.
    rename select (∀ z, z ∈ candidates -> _) into Hcandsinbnds.
    cbn in Hincands. 
    apply Hcandsinbnds in Hincands. cbn in Hincands.
    unfold in_bounds in Hincands. cbn in Hincands.
    unfold name_hint in Hincands.
    unfold in_bounds. unfold name_hint. solve_goal.
  - solve_goal.
Qed.
End proof.
