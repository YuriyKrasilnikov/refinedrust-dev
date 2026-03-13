From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.knights_tour.generated Require Import generated_code_knights_tour generated_specs_knights_tour generated_template_Board_new.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Board_new_proof (π : thread_id) :
  Board_new_lemma π.
Proof.
  Board_new_prelude.

  rep liRStep. liShow.
  {
    liInst Hevar_Inv (λ _ (p : Z * Z) (x : (plist (RT_xt ∘ place_rfnRT) [(place_rfn Z)%type : RT])), (⌜int_elem_of_it (16 * (x.:0))%Z isize⌝ ∗ ⌜p.2 = size⌝)%I).
    rep liRStep. liShow.
    split.
    { liInst Hevar_x2 (fmap (λ (y : list Z), fmap Z.to_nat y) x').
      rewrite -list_fmap_compose.
      apply list_fmap_ext => x2. cbn.
      intros inner_list Hisinner.
      rewrite -list_fmap_compose. f_equal.
      apply list_fmap_ext => z.
      cbn. intros x4 Hx4ininner. f_equal. 

      pose proof
      (@Forall2_lookup_r _ _ _ (seqZ 0 r') x' x2 inner_list H16 Hisinner) as Hres.
      cbn in Hres.

      destruct Hres as [a [Halookup Hrel]].
      destruct Hrel as [pclos [Hleft Hright]].
      destruct Hright as [a' [γ [a0 [Hpclos [Hr' [Hx [Hinner _]]]]]]].
      destruct Hinner as [a1 [-> [Hall0 [Hlen Hr'']]]].

      pose proof (lookup_lt_Some a1 z x4 Hx4ininner) as Hzlt_len.
      rewrite Hlen in Hzlt_len.

      have Hz0 : a1 !! z = Some 0.
      { apply Hall0. lia. }

      rewrite Hz0 in Hx4ininner.
      inversion Hx4ininner; subst.
      lia.
    }
    rep liRStep.
  }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve.

  - rename select (Forall2 _ _ _) into Hseqr'.
    apply Forall2_length in Hseqr'. rewrite <- Hseqr'. solve_goal.
  - rewrite list_lookup_total_fmap; last solve_goal.
    rewrite length_fmap.
    have Hlen : length (seqZ 0 r') = length x' by apply Forall2_length in H16.
    have Hlt_seq : (i < length (seqZ 0 r'))%nat by rewrite Hlen; lia.
    destruct (lookup_lt_is_Some_2 (seqZ 0 r') i Hlt_seq) as [a Ha].

    pose proof
    (@Forall2_lookup_l Z (list Z) _ (seqZ 0 r') x' i a H16 Ha) as [b [Hb_lookup Hbrel]].

    destruct Hbrel as [pclos [Hleft Hright]].
    destruct Hright as [a0 [γ [a1 [Hpclos [Hr [Ha0 [Hinner _]]]]]]].
    destruct Hinner as [a2 [Hb [Hzero [Hlen2 Hr2]]]].
    subst b.

    replace (x' !!! i) with a2.
    2:{
      symmetry. apply list_lookup_total_correct.
      exact Hb_lookup.
    }

    inversion Hr2; subst.
    exact Hlen2.
  - apply inhabitant.
Qed.
End proof.
