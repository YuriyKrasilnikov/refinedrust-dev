From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.knights_tour.generated Require Import generated_code_knights_tour generated_specs_knights_tour generated_template_knights_tour.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(* TODO upstream *)
Global Instance simpl_impl_elem_of_nil {A} (x : A) :
  SimplImpl true (x ∈ []) (λ T, False → T).
Proof.
  unfold SimplImpl. intros. rewrite elem_of_nil. done.
Qed.

(* TODO upstream *)
Hint Rewrite -> wrap_to_it_id using can_solve : lithium_rewrite.

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
  { rep  500 liRStep.
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
    { rep  500 liRStep.
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
    { rep  500 liRStep.
    rep  500 liRStep.
    rep  500 liRStep.
    rep  500 liRStep.
    rep  500 liRStep.
    rep  500 liRStep.
    rep  500 liRStep.
    rep  500 liRStep.
    rep  500 liRStep.
    rep  500 liRStep.
    rep  500 liRStep. }

    rep  500 liRStep.
    rep  500 liRStep.
    rep  500 liRStep. }
    rep  500 liRStep.
    rep  500 liRStep.
    { rep  liRStep. }
    rep liRStep. }
  rep liRStep.

  all: print_remaining_goal.

  Unshelve.
  all: sidecond_solver.
  all: try (revert select (_ ∈ []); solve_goal).
  all: try rename select (∀ a b : Z, _ -> a ≤ 2 ∧ _) into Hbound.
  all: cbn in *.
  all: unfold name_hint in *.
  all: try rename select (in_bounds (Z.to_nat size) _) into Hinbounds.
  all: try solve_goal.
  - opose proof (Hbound _ _ _); [ apply elem_of_app; right; apply elem_of_cons; eauto | ].
    solve_goal.
  - opose proof (Hbound _ _ _); [ apply elem_of_app; right; apply elem_of_cons; eauto | ].
    solve_goal.
  - etrans; first eapply size_of_array_in_bytes_mono; last done. lia.
  - rename select (_ ∈ _) into Hincands.
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
  - rename select (_ ∈ _) into Hincands.
    rename select (∀ z, z ∈ candidates -> _) into Hcandsinbnds.
    cbn in Hincands.
    apply Hcandsinbnds in Hincands. cbn in Hincands.
    unfold in_bounds in Hincands. cbn in Hincands.
    unfold name_hint in Hincands.
    unfold in_bounds. unfold name_hint. solve_goal.
Qed.
End proof.
