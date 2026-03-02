Section extra.
 Context `{RRGS : !refinedrustGS Σ}.
 Lemma iterator_next_fused_trans_map_inv {MB_rt MI_rt MF_rt Item_rt}
  (It_attrs : traits_iterator_Iterator_spec_attrs MI_rt Item_rt)
  (FnOnce_attrs : FnOnce_spec_attrs MF_rt (tuple1_rt Item_rt) MB_rt)
  (FnMut_attrs : FnMut_spec_attrs MF_rt (tuple1_rt Item_rt) MB_rt) π s1 hist s2 :
    IteratorNextFusedTrans (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs MB_rt MI_rt MF_rt Item_rt It_attrs FnOnce_attrs FnMut_attrs) π s1 hist s2 -∗
    ∃ hist' states,
      ⌜states !! 0%nat = Some s1.(map_clos)⌝ ∗
      ⌜states !! (length hist) = Some s2.(map_clos)⌝ ∗
      ⌜length states = S (length hist)⌝ ∗
      IteratorNextFusedTrans It_attrs π s1.(map_it) hist' s2.(map_it) ∗
      [∗ list] i ↦ a; b ∈ hist'; hist,
        ∃ s1 s2, ⌜states !! i = Some s1⌝ ∗ ⌜states !! S i = Some s2⌝ ∗ ☒ FnOnce_attrs.(FnOnce_Pre) π s1 *[a] ∗ FnOnce_attrs.(FnOnce_PostMut) π s1 *[a] s2 b
  .
  Proof.
    iInduction hist as [ | a hist] "IH" forall (s1 s2); simpl.
    { iIntros "<-". iExists [], [s1.(map_clos)]. simpl. done. }
    iIntros "(%s1' & (_ & %b & Ha & Hpre & Hpost) & Hc)".
    iPoseProof ("IH" with "Hc") as "(%hist' & %states & % & % & %Hlen & Hit & Hclos)".
    iExists (b :: hist'), (s1.(map_clos) :: states).
    iR.
    iSplitR. { iPureIntro. simpl. done. }
    iSplitR. { iPureIntro. simpl. rewrite Hlen. done. }
    simpl. iFrame "Hclos".
    iFrame. done.
  Qed.


  (** Declared as an extern instance below, to enforce order on the argument resolution *)
  Program Definition iterator_learn_map_stateless {MB_rt MI_rt MF_rt Item_rt}
  (It_attrs : traits_iterator_Iterator_spec_attrs MI_rt Item_rt)
  (FnOnce_attrs : FnOnce_spec_attrs MF_rt (tuple1_rt Item_rt) MB_rt)
  (FnMut_attrs : FnMut_spec_attrs MF_rt (tuple1_rt Item_rt) MB_rt)
  (It_learn : IteratorLearnInductive It_attrs)

  (FnOnce_pre_learn : ∀ π self args, SimplifyBoringlyImpl (FnOnce_attrs.(FnOnce_Pre) π self args))
  (FnMut_postmut_learn : ∀ π self args self' out, SimplifyBoringlyImpl (FnOnce_attrs.(FnOnce_PostMut) π self args self' out))
  (FnMut_postmut_stateless : ∀ π args out, RelationIsIdentity (λ self self', (FnMut_postmut_learn π self args self' out).(simplify_boringly_impl_q _)))
  :
    IteratorLearnInductive (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs MB_rt MI_rt MF_rt Item_rt It_attrs FnOnce_attrs FnMut_attrs) := {|
      iterator_learn_inductive_Q s1 hist s2 :=
        ∃ π hist',
          It_learn.(iterator_learn_inductive_Q) s1.(map_it) hist' s2.(map_it) ∧
          s1.(map_clos) = s2.(map_clos) ∧
          Forall2 (λ a b, (FnOnce_pre_learn π s1.(map_clos) *[a]).(simplify_boringly_impl_q _) ∧ (FnMut_postmut_learn π s1.(map_clos) *[a] s1.(map_clos) b).(simplify_boringly_impl_q _)) hist' hist
        ;
    |}.
  Next Obligation.
    intros ???? It_attrs FnOnce_attrs FnMut_attrs It_learn FnOnce_pure FnMut_pure FnMut_stateless.
    simpl. iIntros (? s1 hist s2) "Hnext".
    iPoseProof (boringly_mono with "Hnext") as "Ha".
    { iApply iterator_next_fused_trans_map_inv. }
    repeat setoid_rewrite boringly_exists.
    iDestruct "Ha" as "(%hist' & %states' & Ha)".
    rewrite !boringly_sep !boringly_persistent_elim.
    iDestruct "Ha" as "(%Hlook1 & %Hlook2 & %Hlen & Hnext & Hclos)".
    iPoseProof (It_learn.(iterator_learn_inductive_proof) with "Hnext") as "%Hlearn".

    iAssert (([∗ list] i↦a;b ∈ hist';hist, ∃ s0 s3 : RT_xt MF_rt, ⌜states' !! i = Some s0⌝ ∗ ⌜states' !! S i = Some s3⌝ ∗ ☒ FnOnce_Pre FnOnce_attrs π s0 *[a] ∗ ☒ FnOnce_PostMut FnOnce_attrs π s0 *[a] s3 b))%I with "[Hclos]" as "Hclos".
    { iApply boringly_persistent_elim.
      iApply boringly_mono; last iApply "Hclos".
      iIntros "Ha". iApply (big_sepL2_impl with "Ha").
      iModIntro. iIntros (?????) "(% & % & % & % & Hpre & Hpost)".
      iFrame "∗%". by iApply boringly_intro. }

    iAssert (⌜∀ i x y, states' !! i = Some x → states' !! (S i) = Some y → x = y⌝)%I as "%Hstates".
    { iIntros (i ? ? Hlook3 Hlook4). iClear "Hnext".
      assert (i < length hist). { apply lookup_lt_Some in Hlook4. lia. }

      iPoseProof (big_sepL2_length with "Hclos") as "%Hlen'".
      odestruct (lookup_lt_is_Some_2 hist i _) as (sb & ?); first lia.
      odestruct (lookup_lt_is_Some_2 hist' i _) as (sa & ?). { rewrite Hlen'. lia. }

      iPoseProof (big_sepL2_lookup _ _ _ i sa sb with "Hclos") as "Ha"; [done.. | ].
      iDestruct "Ha" as "(% & % & % & % & Hpre & Hpost)".

      rewrite ((FnMut_pure π _ _ _ _).(simplify_boringly_impl_proof)).
      iDestruct "Hpost" as "%Hpost".
      apply FnMut_stateless in Hpost.
      simplify_eq. done. }
    (* prove that the state remains constant *)
    assert (∀ j i s, (i < j)%nat → states' !! i = Some s → s = s1.(map_clos)) as Hstates'.
    { clear -Hstates Hlook1.
      induction j as [ | j IH]; simpl in *. { intros. lia. }
      intros i s Hlt Hlook.
      apply lookup_lt_Some in Hlook as ?.
      destruct (decide (i = j)) as [-> | ?].
      - destruct j as [ | j]; first by simplify_eq.
        odestruct (lookup_lt_is_Some_2 states' j _) as (? & Hlook2); first lia.
        ospecialize (IH j _ _ _); [lia | done | ].
        subst. symmetry. by eapply (Hstates j).
      - eapply IH; last done. lia. }

    iExists π, hist'.
    iSplitR; first done.
    iSplitR. { iPureIntro. symmetry. eapply (Hstates' (S (length hist))); last done. lia. }
    iApply big_sepL2_Forall2.
    iApply (big_sepL2_impl with "Hclos").
    iModIntro. iIntros (? ?? Hlook3 Hlook4) "(%sa & %sb & %Hlook5 & %Hlook6 & Hpre & Hpost)".
    rewrite ((FnMut_pure _ _ _ _ _).(simplify_boringly_impl_proof)).
    rewrite ((FnOnce_pure _ _ _).(simplify_boringly_impl_proof)).
    iDestruct "Hpre" as "%".
    iDestruct "Hpost" as "%".
    opose proof (Hstates' (S k) k _ _ Hlook5); first lia.
    opose proof (Hstates' (S (S k)) (S k) _ _ Hlook6); first lia.
    subst. done.
  Qed.

  Program Definition iterator_learn_range_it
    (Clone_attrs : Clone_spec_attrs Z)
    (PartialEq_attrs : PartialEq_spec_attrs Z Z)
    (PartialOrd_attrs : PartialOrd_spec_attrs Z Z PartialEq_attrs)
    (Step_attrs : step_Step_spec_attrs Z Clone_attrs PartialEq_attrs PartialOrd_attrs)
    :
    (∀ a b z, Step_attrs.(step_Step_Forward) a b = Some z → z = a + b) →
    (∀ a b, PartialOrd_attrs.(PartialOrd_POrd) a b = Some (Z.compare a b)) →
    IteratorLearnInductive (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs (Z)
      Clone_attrs PartialEq_attrs PartialOrd_attrs Step_attrs) :=
    λ _ _, {| iterator_learn_inductive_Q s1 hist s2 :=
        s1.2 = s2.2 ∧ s1.1 ≤ s2.1 ∧ hist = seqZ s1.1 (s2.1 - s1.1) |}.
  Next Obligation.
    iIntros (???? Hstep Hcmp_eq ????) "Hx".
    iPoseProof (boringly_persistent_elim with "Hx") as "Hx".
    iInduction hist as [ | x hist] "IH" forall (s1 s2); simpl.
    { iDestruct "Hx" as "%". subst. iPureIntro.
      rewrite Z.sub_diag. done. }
    iDestruct "Hx" as "(%s1' & %Ha & Hx)".
    iPoseProof ("IH" with "Hx") as "%Hb".
    iPureIntro.
    destruct Ha as (? & _ & <- & Hstep_some & Hcmp). destruct Hb as (? & ? & ->).
    destruct s1, s2, s1'; simpl in *.
    subst.
    symmetry in Hstep_some. apply Hstep in Hstep_some.
    subst z.
    rewrite Hcmp_eq in Hcmp.
    injection Hcmp.
    rewrite Z.compare_lt_iff. intros.
    split_and!; try solve_goal.
    rewrite (seqZ_cons r (r1 - r)); last lia.
    f_equiv. f_equiv; lia.
  Qed.


  Program Definition iterator_learn_range_it_i8 :=
    iterator_learn_range_it (i8asClone_spec_attrs) (i8asPartialEq_spec_attrs) (i8asPartialOrd_spec_attrs) (i8asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_i8.

  Program Definition iterator_learn_range_it_i16 :=
    iterator_learn_range_it (i16asClone_spec_attrs) (i16asPartialEq_spec_attrs) (i16asPartialOrd_spec_attrs) (i16asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_i16.

  Program Definition iterator_learn_range_it_i32 :=
    iterator_learn_range_it (i32asClone_spec_attrs) (i32asPartialEq_spec_attrs) (i32asPartialOrd_spec_attrs) (i32asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_i32.

  Program Definition iterator_learn_range_it_i64 :=
    iterator_learn_range_it (i64asClone_spec_attrs) (i64asPartialEq_spec_attrs) (i64asPartialOrd_spec_attrs) (i64asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_i64.

  Program Definition iterator_learn_range_it_i128 :=
    iterator_learn_range_it (i128asClone_spec_attrs) (i128asPartialEq_spec_attrs) (i128asPartialOrd_spec_attrs) (i128asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_i128.

  Program Definition iterator_learn_range_it_isize :=
    iterator_learn_range_it (isizeasClone_spec_attrs) (isizeasPartialEq_spec_attrs) (isizeasPartialOrd_spec_attrs) (isizeasstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_isize.

  Program Definition iterator_learn_range_it_u8 :=
    iterator_learn_range_it (u8asClone_spec_attrs) (u8asPartialEq_spec_attrs) (u8asPartialOrd_spec_attrs) (u8asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_u8.

  Program Definition iterator_learn_range_it_u16 :=
    iterator_learn_range_it (u16asClone_spec_attrs) (u16asPartialEq_spec_attrs) (u16asPartialOrd_spec_attrs) (u16asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_u16.

  Program Definition iterator_learn_range_it_u32 :=
    iterator_learn_range_it (u32asClone_spec_attrs) (u32asPartialEq_spec_attrs) (u32asPartialOrd_spec_attrs) (u32asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_u32.

  Program Definition iterator_learn_range_it_u64 :=
    iterator_learn_range_it (u64asClone_spec_attrs) (u64asPartialEq_spec_attrs) (u64asPartialOrd_spec_attrs) (u64asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_u64.

  Program Definition iterator_learn_range_it_u128 :=
    iterator_learn_range_it (u128asClone_spec_attrs) (u128asPartialEq_spec_attrs) (u128asPartialOrd_spec_attrs) (u128asstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_u128.

  Program Definition iterator_learn_range_it_usize :=
    iterator_learn_range_it (usizeasClone_spec_attrs) (usizeasPartialEq_spec_attrs) (usizeasPartialOrd_spec_attrs) (usizeasstep_Step_spec_attrs) _ _.
  Next Obligation. simpl; intros; case_bool_decide; simplify_eq; done. Qed.
  Next Obligation. done. Qed.
  Global Existing Instance iterator_learn_range_it_usize.

  Lemma simplify_goal_range_iter_inv Clone_attrs PEq_attrs POrd_attrs Step_attrs π b T :
    T
    ⊢ simplify_goal (traits_iterator_Iterator_Inv (step_impltraits_iterator_Iteratorforstd_ops_RangeA_spec_attrs Z Clone_attrs PEq_attrs POrd_attrs Step_attrs) π b) T.
  Proof.
    unfold traits_iterator_Iterator_Inv; simpl.
    iIntros "$".
  Qed.
  Definition simplify_goal_range_iter_inv_inst := [instance @simplify_goal_range_iter_inv with 0%N].
  Global Existing Instance simplify_goal_range_iter_inv_inst.


End extra.
Global Hint Extern 100 (IteratorLearnInductive (adapters_map_MapMIMFastraits_iterator_Iterator_spec_attrs _ _ _ _ _ _ _)) =>
  unshelve notypeclasses refine (iterator_learn_map_stateless _ _ _ _ _ _ _); [tc_solve | tc_solve | tc_solve | tc_solve] : typeclass_instances.

Global Arguments traits_iterator_Iterator_Inv : simpl never.
Global Typeclasses Opaque traits_iterator_Iterator_Inv.
