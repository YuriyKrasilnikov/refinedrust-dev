From refinedrust Require Import typing.

#[universes(polymorphic)]
Definition extract_val {rt : RT} (r : place_rfn rt) := if r is #r then Some r else None.

Section project_vec_els.
  Context {rt : RT}.
  Set Universe Polymorphism.

  Definition project_vec_els (len : nat) (els : list (place_rfn (option (place_rfn rt))))
    : list (place_rfn rt) :=
    (λ x, default (@PlaceGhost rt inhabitant) (extract_val x ≫= id)) <$> (take len els).

  Lemma project_vec_els_lookup_Some len i els x :
    project_vec_els len els !! i = Some x →
    ∃ x', els !! i = Some x' ∧ x = default (👻 inhabitant) (extract_val x' ≫= id) ∧ (i < len)%nat. 
  Proof.
    rewrite /project_vec_els.
    rewrite list_lookup_fmap_Some.
    intros (x' & Heq & Hlook).
    apply lookup_take_Some in Hlook as (Hlook & ?).
    eauto.
  Qed.

  Lemma project_vec_els_length len els :
    length (project_vec_els len els) = (len `min` length els)%nat.
  Proof. by rewrite /project_vec_els length_fmap length_take. Qed.


End project_vec_els.
