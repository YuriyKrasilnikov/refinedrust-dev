From refinedrust Require Export type int.
From refinedrust Require Import programs.
From refinedrust Require Import options.

(** * Rules for integer types *)

Open Scope Z_scope.

Section typing.
  Context `{typeGS Σ}.

  Global Program Instance learn_from_hyp_val_int_unsigned it z `{Hu : TCDone (it_signed it = false)} :
    LearnFromHypVal (int it) z :=
    {| learn_from_hyp_val_Q := ⌜0 ≤ z ≤ MaxInt it⌝ |}.
  Next Obligation.
    iIntros (? z Hu ?????) "Hv".
    rewrite /ty_own_val/=.
    iDestruct "Hv" as "(-> & %Hit)".
    specialize (val_to_Z_in_range _ _ _ Hit) as [Hran ?].
    iModIntro. iPureIntro. split_and!; [done.. | | ].
    { opose proof (MinInt_unsigned_0 it _); first done. lia. }
    { done. }
  Qed.
  Global Program Instance learn_from_hyp_val_int_signed it z `{Hs : TCDone (it_signed it = true)} :
    LearnFromHypVal (int it) z :=
    {| learn_from_hyp_val_Q := ⌜MinInt it ≤ z ≤ MaxInt it⌝ |}.
  Next Obligation.
    iIntros (? z Hs ?????) "Hv".
    rewrite /ty_own_val/=.
    iDestruct "Hv" as "(-> & %Hit)".
    specialize (val_to_Z_in_range _ _ _ Hit) as [Hran ?].
    iPureIntro. split_and!; done.
  Qed.

  Lemma type_int_val z (it : int_type) π :
    z ∈ it → ⊢ i2v z it ◁ᵥ{π, MetaNone} z @ int it.
  Proof.
    intros Hn.
    move: Hn => /(val_of_Z_is_Some) [v Hv].
    move: (Hv) => /val_to_of_Z Hn.
    rewrite /ty_own_val/=. iPureIntro.
    rewrite /i2v Hv/=//.
  Qed.

  Lemma type_val_int π z (it : int_type) (T : typed_value_cont_t):
    ⌜z ∈ it⌝ ∗ T MetaNone _ (int it) z ⊢ typed_value π (i2v z it) T.
  Proof.
    iIntros "[%Hn HT] #CTX".
    iExists Z, (int it), z. iFrame.
    iApply type_int_val; last done.
  Qed.
  Definition type_val_int_inst := [instance @type_val_int].
  Global Existing Instance type_val_int_inst.
End typing.

Section relop.
  Context `{!typeGS Σ}.

  Lemma type_relop_int_int E L it v1 (n1 : Z) v2 (n2 : Z) (T : typed_val_expr_cont_t) b op f :
    match op with
    | EqOp rit => Some (bool_decide (n1 = n2)%Z, rit)
    | NeOp rit => Some (bool_decide (n1 ≠ n2)%Z, rit)
    | LtOp rit => Some (bool_decide (n1 < n2)%Z, rit)
    | GtOp rit => Some (bool_decide (n1 > n2)%Z, rit)
    | LeOp rit => Some (bool_decide (n1 <= n2)%Z, rit)
    | GeOp rit => Some (bool_decide (n1 >= n2)%Z, rit)
    | _ => None
    end = Some (b, U8) →
    ((⌜n1 ∈ it⌝ -∗ ⌜n2 ∈ it⌝ -∗ T L (val_of_bool b) MetaNone bool bool_t b)) ⊢
      typed_bin_op E L f v1 (v1 ◁ᵥ{f.1, MetaNone} n1 @ int it) v2 (v2 ◁ᵥ{f.1, MetaNone} n2 @ int it) op (IntOp it) (IntOp it) T.
  Proof.
    rewrite /ty_own_val/=.
    iIntros "%Hop HT (_ & %Hv1) (_ & %Hv2)" (Φ) "#CTX #HE HL Hf HΦ".
    iDestruct ("HT" with "[] []" ) as "HT".
    1-2: iPureIntro; by apply: val_to_Z_in_range.
    iApply (wp_binop_det_pure (val_of_bool b)).
    { split.
      - destruct op => //; inversion 1; simplify_eq; symmetry;
        by apply val_of_bool_iff_val_of_Z.
      - move => ->. econstructor; [done.. | ].
        by apply val_of_bool_iff_val_of_Z. }
    iApply physical_step_intro. iNext.
    iApply ("HΦ" with "HL Hf") => //.
    rewrite /ty_own_val/=. by destruct b.
  Qed.

  Global Program Instance type_eq_int_int_inst E L it v1 n1 v2 n2 f :
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 (EqOp U8) (IntOp it) (IntOp it) := λ T, i2p (type_relop_int_int E L it v1 n1 v2 n2 T (bool_decide (n1 = n2)) _ f _).
  Solve Obligations with done.
  Global Program Instance type_ne_int_int_inst E L it v1 n1 v2 n2 f :
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 (NeOp U8) (IntOp it) (IntOp it) := λ T, i2p (type_relop_int_int E L it v1 n1 v2 n2 T (bool_decide (n1 ≠ n2)) _ f _).
  Solve Obligations with done.
  Global Program Instance type_lt_int_int_inst E L it v1 n1 v2 n2 f :
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 (LtOp U8) (IntOp it) (IntOp it) := λ T, i2p (type_relop_int_int E L it v1 n1 v2 n2 T (bool_decide (n1 < n2)%Z) _ f _).
  Solve Obligations with done.
  Global Program Instance type_gt_int_int_inst E L it v1 n1 v2 n2 f :
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 (GtOp U8) (IntOp it) (IntOp it) := λ T, i2p (type_relop_int_int E L it v1 n1 v2 n2 T (bool_decide (n1 > n2)%Z) _ f _).
  Solve Obligations with done.
  Global Program Instance type_le_int_int_inst E L it v1 n1 v2 n2 f :
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 (LeOp U8) (IntOp it) (IntOp it) := λ T, i2p (type_relop_int_int E L it v1 n1 v2 n2 T (bool_decide (n1 <= n2)%Z) _ f _).
  Solve Obligations with done.
  Global Program Instance type_ge_int_int_inst E L it v1 n1 v2 n2 f :
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 (GeOp U8) (IntOp it) (IntOp it) := λ T, i2p (type_relop_int_int E L it v1 n1 v2 n2 T (bool_decide (n1 >= n2)%Z) _ f _).
  Solve Obligations with done.
End relop.

Section arithop.
  Context `{!typeGS Σ}.

  (** We first define a version that wraps the result and has few sideconditions *)
  Lemma type_arithop_int_int E L f it v1 n1 v2 n2 (T : typed_val_expr_cont_t) n op m1 m2 :
    int_arithop_result it n1 n2 op = Some n →
    ((⌜n1 ∈ it⌝ -∗ ⌜n2 ∈ it⌝ -∗ ⌜int_arithop_sidecond it n1 n2 n op⌝ ∗ T L (i2v (wrap_to_it n it) it) MetaNone Z (int it) (wrap_to_it n it))) ⊢
      typed_bin_op E L f v1 (v1 ◁ᵥ{f.1, m1} n1 @ int it) v2 (v2 ◁ᵥ{f.1, m2} n2 @ int it) op (IntOp it) (IntOp it) T.
  Proof.
    rewrite /ty_own_val/=.
    iIntros "%Hop HT (-> & %Hv1) (-> & %Hv2) %Φ #CTX #HE HL Hf HΦ".
    iDestruct ("HT" with "[] []" ) as (Hsc) "HT".
    1-2: iPureIntro; by apply: val_to_Z_in_range.
    iApply wp_int_arithop; [done..| ].

    iIntros (v Hv).
    iApply physical_step_intro. iNext.
    rewrite /i2v Hv/=. iApply ("HΦ" with "HL Hf [] HT").
    rewrite /ty_own_val/=.
    iR.
    iPureIntro. by apply: val_to_of_Z.
  Qed.

  (** Now we derive a version that gets rid of the wrapping at the cost of additional sideconditions *)
  Definition int_arithop_in_range (it : int_type) (n : Z) op : Prop :=
    match op with
    (* these sideconditions are stronger than necessary and do not support the wrapping for unsigned unchecked ops that is allowed by the opsem *)
    | AddOp => n ∈ it
    | SubOp => n ∈ it
    | MulOp => n ∈ it
    | UncheckedAddOp => n ∈ it
    | UncheckedSubOp => n ∈ it
    | UncheckedMulOp => n ∈ it
    | AndOp => True
    | OrOp  => True
    | XorOp => True
    (* TODO: check accuracy of shifting semantics *)
    | ShlOp =>
        n ∈ it
    | ShrOp => True
    | DivOp => n ∈ it
    | ModOp => n ∈ it
    | _     => True (* Relational operators. *)
    end.

  Lemma bitwise_op_result_in_range op bop (it : int_type) n1 n2 :
    (0 ≤ n1 → 0 ≤ n2 → 0 ≤ op n1 n2) →
    bool_decide (op n1 n2 < 0) = bop (bool_decide (n1 < 0)) (bool_decide (n2 < 0)) →
    (∀ k, Z.testbit (op n1 n2) k = bop (Z.testbit n1 k) (Z.testbit n2 k)) →
    n1 ∈ it → n2 ∈ it → op n1 n2 ∈ it.
  Proof.
    move => Hnonneg Hsign Htestbit.
    rewrite !int_elem_of_it_iff.
    rewrite /elem_of /int_elem_of_it /min_int /max_int.
    have ? := bits_per_int_gt_0 it.
    destruct (it_signed it).
    - rewrite /int_half_modulus.
      move ? : (bits_per_int it - 1) => k.
      have Hb : ∀ n, -2^k ≤ n ≤ 2^k - 1 ↔ ∀ l, k ≤ l → Z.testbit n l = bool_decide (n < 0).
      { move => ?. rewrite -Z.bounded_iff_bits; lia. }
      move => /Hb Hn1 /Hb Hn2.
      apply Hb => l Hl.
      by rewrite Htestbit Hsign Hn1 ?Hn2.
    - rewrite /int_modulus.
      move ? : (bits_per_int it) => k.
      have Hb : ∀ n, 0 ≤ n → n ≤ 2^k - 1 ↔ ∀ l, k ≤ l → Z.testbit n l = bool_decide (n < 0).
      { move => ??. rewrite bool_decide_false -?Z.bounded_iff_bits_nonneg; lia. }
      move => [Hn1 /Hb HN1] [Hn2 /Hb HN2].
      have Hn := Hnonneg Hn1 Hn2.
      split; first done.
      apply (Hb _ Hn) => l Hl.
      by rewrite Htestbit HN1 ?HN2.
  Qed.

  Lemma int_arithop_result_in_range (it : int_type) (n1 n2 n : Z) op :
    n1 ∈ it → n2 ∈ it →
    int_arithop_result it n1 n2 op = Some n →
    int_arithop_sidecond it n1 n2 n op →
    int_arithop_in_range it n op →
    n ∈ it.
  Proof.
    move => Hn1 Hn2 Hn Hsc Hran.
    destruct op => //=; simpl in Hsc, Hran, Hn; destruct_and? => //.
    all: inversion Hn; simplify_eq.
    - apply (bitwise_op_result_in_range Z.land andb) => //.
      + rewrite Z.land_nonneg; naive_solver.
      + repeat case_bool_decide; try rewrite -> Z.land_neg in *; naive_solver.
      + by apply Z.land_spec.
    - apply (bitwise_op_result_in_range Z.lor orb) => //.
      + by rewrite Z.lor_nonneg.
      + repeat case_bool_decide; try rewrite -> Z.lor_neg in *; naive_solver.
      + by apply Z.lor_spec.
    - apply (bitwise_op_result_in_range Z.lxor xorb) => //.
      + by rewrite Z.lxor_nonneg.
      + have Hn : ∀ n, bool_decide (n < 0) = negb (bool_decide (0 ≤ n)).
        { intros. repeat case_bool_decide => //; lia. }
        rewrite !Hn.
        repeat case_bool_decide; try rewrite -> Z.lxor_nonneg in *; naive_solver.
      + by apply Z.lxor_spec.
    (*- rewrite !int_elem_of_it_iff.*)
      (*split.*)
      (*+ trans 0; [ apply min_int_le_0 | by apply Z.shiftl_nonneg ].*)
      (*+ rewrite -MaxInt_eq.  done.*)
    - split.
      + trans 0; [ apply MinInt_le_0 | by apply Z.shiftr_nonneg ].
      + destruct Hn1.
        trans n1; last done. rewrite Z.shiftr_div_pow2; last by lia.
        apply Z.div_le_upper_bound. { apply Z.pow_pos_nonneg => //. }
        rewrite -{1}(Z.mul_1_l n1). apply Z.mul_le_mono_nonneg_r => //.
        rewrite -(Z.pow_0_r 2). apply Z.pow_le_mono_r; lia.
  Qed.

  Lemma type_arithop_int_int_nowrap E L f it v1 n1 v2 n2 (T : typed_val_expr_cont_t) n op m1 m2 :
    int_arithop_result it n1 n2 op = Some n →
    ((⌜n1 ∈ it⌝ -∗ ⌜n2 ∈ it⌝ -∗ ⌜int_arithop_sidecond it n1 n2 n op⌝ ∗ ⌜int_arithop_in_range it n op⌝ ∗ T L (i2v n it) MetaNone Z (int it) n)) ⊢
      typed_bin_op E L f v1 (v1 ◁ᵥ{f.1, m1} n1 @ int it) v2 (v2 ◁ᵥ{f.1, m2} n2 @ int it) op (IntOp it) (IntOp it) T.
  Proof.
    rewrite /ty_own_val/=.
    iIntros "%Hop HT (-> & %Hv1) (-> & %Hv2) %Φ #CTX #HE HL Hf HΦ".
    iDestruct ("HT" with "[] []" ) as (Hsc Hran) "HT".
    1-2: iPureIntro; by apply: val_to_Z_in_range.
    iApply wp_int_arithop; [done..| ].

    iIntros (v Hv).
    iApply physical_step_intro. iNext.
    assert (wrap_to_it n it = n) as Heq.
    { rewrite wrap_to_it_id; [done | ].
      eapply int_arithop_result_in_range.
      - eapply val_to_Z_in_range; apply Hv1.
      - eapply val_to_Z_in_range; apply Hv2.
      - done.
      - done.
      - done. }

    rewrite Heq in Hv. rewrite /i2v Hv/=.
    iApply ("HΦ" with "HL Hf [] HT").
    rewrite /ty_own_val/=.
    iR.
    iPureIntro. by apply: val_to_of_Z.
  Qed.
  Global Program Instance type_add_int_int_inst E L f it v1 n1 v2 n2:
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 AddOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int_nowrap E L f it v1 n1 v2 n2 T (n1 + n2) _ MetaNone MetaNone _).
  Next Obligation. done. Qed.
  Global Program Instance type_sub_int_int_inst E L f it v1 n1 v2 n2:
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 SubOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int_nowrap E L f it v1 n1 v2 n2 T (n1 - n2) _ MetaNone MetaNone _).
  Next Obligation. done. Qed.
  Global Program Instance type_mul_int_int_inst E L f it v1 n1 v2 n2:
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 MulOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int_nowrap E L f it v1 n1 v2 n2 T (n1 * n2) _ MetaNone MetaNone _).
  Next Obligation. done. Qed.
  Global Program Instance type_div_int_int_inst E L f it v1 n1 v2 n2:
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 DivOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int_nowrap E L f it v1 n1 v2 n2 T (n1 `quot` n2) _ MetaNone MetaNone _).
  Next Obligation. done. Qed.
  Global Program Instance type_mod_int_int_inst E L f it v1 n1 v2 n2:
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 ModOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int_nowrap E L f it v1 n1 v2 n2 T (n1 `rem` n2) _ MetaNone MetaNone _).
  Next Obligation. done. Qed.
  Global Program Instance type_and_int_int_inst E L f it v1 n1 v2 n2:
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 AndOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int_nowrap E L f it v1 n1 v2 n2 T (Z.land n1 n2) _ MetaNone MetaNone _).
  Next Obligation. done. Qed.
  Global Program Instance type_or_int_int_inst E L f it v1 n1 v2 n2:
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 OrOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int_nowrap E L f it v1 n1 v2 n2 T (Z.lor n1 n2) _ MetaNone MetaNone _).
  Next Obligation. done. Qed.
  Global Program Instance type_xor_int_int_inst E L f it v1 n1 v2 n2:
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 XorOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int_nowrap E L f it v1 n1 v2 n2 T (Z.lxor n1 n2) _ MetaNone MetaNone _).
  Next Obligation. done. Qed.
  Global Program Instance type_shl_int_int_inst E L f it v1 n1 v2 n2:
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 ShlOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int_nowrap E L f it v1 n1 v2 n2 T (n1 ≪ n2) _ MetaNone MetaNone _).
  Next Obligation. done. Qed.
  Global Program Instance type_shr_int_int_inst E L f it v1 n1 v2 n2:
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 ShrOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int_nowrap E L f it v1 n1 v2 n2 T (n1 ≫ n2) _ MetaNone MetaNone _).
  Next Obligation. done. Qed.

  Global Program Instance type_unchecked_add_int_int_inst E L f it v1 n1 v2 n2:
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 UncheckedAddOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int_nowrap E L f it v1 n1 v2 n2 T (n1 + n2) _ MetaNone MetaNone _).
  Next Obligation. done. Qed.
  Global Program Instance type_unchecked_sub_int_int_inst E L f it v1 n1 v2 n2:
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 UncheckedSubOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int_nowrap E L f it v1 n1 v2 n2 T (n1 - n2) _ MetaNone MetaNone _).
  Next Obligation. done. Qed.
  Global Program Instance type_unchecked_mul_int_int_inst E L f it v1 n1 v2 n2:
    TypedBinOpVal E L f v1 (int it) n1 v2 (int it) n2 UncheckedMulOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_int_nowrap E L f it v1 n1 v2 n2 T (n1 * n2) _ MetaNone MetaNone _).
  Next Obligation. done. Qed.
End arithop.

Section check_arithop.
  Context `{!typeGS Σ}.

  Global Instance int_arithop_in_range_dec it n op :
    Decision (int_arithop_in_range it n op).
  Proof.
    destruct op; solve_decision.
  Defined.

  Lemma int_arithop_result_sidecond_correct it n1 n2 n op :
    int_arithop_sidecond it n1 n2 n op →
    int_arithop_result it n1 n2 op = Some n →
    compute_arith_bin_op n1 n2 it op = Some n.
  Proof.
    rewrite /int_arithop_sidecond /compute_arith_bin_op /int_arithop_result.
    destruct op; simpl.
    all: repeat case_bool_decide; try naive_solver.
  Qed.
  Lemma check_arith_bin_op_evaluates it n1 n2 n op :
    int_arithop_sidecond it n1 n2 n op →
    int_arithop_result it n1 n2 op = Some n →
    check_arith_bin_op op it n1 n2 = Some (bool_decide (n ∉ it)).
  Proof.
    intros Hsc Hres.
    eapply int_arithop_result_sidecond_correct in Hsc; last done.
    rewrite /check_arith_bin_op.
    rewrite Hsc/=//.
  Qed.


  Lemma type_check_arithop_int_int E L π f it v1 n1 v2 n2 (T : typed_val_expr_cont_t) n op m1 m2 :
    int_arithop_result it n1 n2 op = Some n →
    ⌜π = f.1⌝ ∗ ⌜int_arithop_sidecond it n1 n2 n op⌝ ∗ T L (val_of_bool (negb $ bool_decide (int_arithop_in_range it n op))) MetaNone bool (bool_t) (negb $ bool_decide (int_arithop_in_range it n op)) ⊢
    typed_check_bin_op E L f v1 (v1 ◁ᵥ{π, m1} n1 @ int it) v2 (v2 ◁ᵥ{π, m2} n2 @ int it) op (IntOp it) (IntOp it) T.
  Proof.
    rewrite /ty_own_val/=.
    iIntros "%Hop (-> & %Hsc & HT) (-> & %Hv1) (-> & %Hv2) %Φ #CTX #HE HL Hf HΦ".
    set (b := (negb $ bool_decide (int_arithop_in_range it n op))).

    iApply wp_check_binop.
    assert (check_arith_bin_op op it n1 n2 = Some b).
    { subst.
      erewrite check_arith_bin_op_evaluates; [ | done..].
      f_equiv. subst b.
      rewrite bool_decide_not. f_equiv.
      apply bool_decide_ext.
      split; first by destruct op.
      intros Hran.
      eapply int_arithop_result_in_range;
        [ | | done | | done ];
        [eapply val_to_Z_in_range; done.. | done ].
    }
    iSplitR.
    { iPureIntro. exists b. econstructor; done. }

    iApply physical_step_intro. iNext.
    iIntros (v Hv).
    inversion Hv; subst. simplify_eq/=.
    iApply ("HΦ" with "HL Hf [] HT").
    rewrite /ty_own_val.
    simpl. subst b. case_bool_decide; done.
  Qed.
  Global Program Instance type_check_add_int_int_inst E L π f it v1 n1 v2 n2 m1 m2 :
    TypedCheckBinOp E L f v1 (v1 ◁ᵥ{π, m1} n1 @ int it) v2 (v2 ◁ᵥ{π, m2} n2 @ int it) AddOp (IntOp it) (IntOp it) := λ T, i2p (type_check_arithop_int_int E L π f it v1 n1 v2 n2 T (n1 + n2) AddOp m1 m2 _).
  Next Obligation. done. Qed.
  Global Program Instance type_check_sub_int_int_inst E L π f it v1 n1 v2 n2 m1 m2 :
    TypedCheckBinOp E L f v1 (v1 ◁ᵥ{π, m1} n1 @ int it) v2 (v2 ◁ᵥ{π, m2} n2 @ int it) SubOp (IntOp it) (IntOp it) := λ T, i2p (type_check_arithop_int_int E L π f it v1 n1 v2 n2 T (n1 - n2) SubOp m1 m2 _).
  Next Obligation. done. Qed.
  Global Program Instance type_check_mul_int_int_inst E L π f it v1 n1 v2 n2 m1 m2 :
    TypedCheckBinOp E L f v1 (v1 ◁ᵥ{π, m1} n1 @ int it) v2 (v2 ◁ᵥ{π, m2} n2 @ int it) MulOp (IntOp it) (IntOp it) := λ T, i2p (type_check_arithop_int_int E L π f it v1 n1 v2 n2 T (n1 * n2) MulOp m1 m2 _).
  Next Obligation. done. Qed.
  Global Program Instance type_check_div_int_int_inst E L π f it v1 n1 v2 n2 m1 m2 :
    TypedCheckBinOp E L f v1 (v1 ◁ᵥ{π, m1} n1 @ int it) v2 (v2 ◁ᵥ{π, m2} n2 @ int it) DivOp (IntOp it) (IntOp it) := λ T, i2p (type_check_arithop_int_int E L π f it v1 n1 v2 n2 T (n1 `quot` n2) DivOp m1 m2 _).
  Next Obligation. done. Qed.
  Global Program Instance type_check_mod_int_int_inst E L π f it v1 n1 v2 n2 m1 m2 :
    TypedCheckBinOp E L f v1 (v1 ◁ᵥ{π, m1} n1 @ int it) v2 (v2 ◁ᵥ{π, m2} n2 @ int it) ModOp (IntOp it) (IntOp it) := λ T, i2p (type_check_arithop_int_int E L π f it v1 n1 v2 n2 T (n1 `rem` n2) ModOp m1 m2 _).
  Next Obligation. done. Qed.
  Global Program Instance type_check_and_int_int_inst E L π f it v1 n1 v2 n2 m1 m2 :
    TypedCheckBinOp E L f v1 (v1 ◁ᵥ{π, m1} n1 @ int it) v2 (v2 ◁ᵥ{π, m2} n2 @ int it) AndOp (IntOp it) (IntOp it) := λ T, i2p (type_check_arithop_int_int E L π f it v1 n1 v2 n2 T (Z.land n1 n2) AndOp m1 m2 _).
  Next Obligation. done. Qed.
  Global Program Instance type_check_or_int_int_inst E L π f it v1 n1 v2 n2 m1 m2 :
    TypedCheckBinOp E L f v1 (v1 ◁ᵥ{π, m1} n1 @ int it) v2 (v2 ◁ᵥ{π, m2} n2 @ int it) OrOp (IntOp it) (IntOp it) := λ T, i2p (type_check_arithop_int_int E L π f it v1 n1 v2 n2 T (Z.lor n1 n2) OrOp m1 m2 _).
  Next Obligation. done. Qed.
  Global Program Instance type_check_xor_int_int_inst E L π f it v1 n1 v2 n2 m1 m2 :
    TypedCheckBinOp E L f v1 (v1 ◁ᵥ{π, m1} n1 @ int it) v2 (v2 ◁ᵥ{π, m2} n2 @ int it) XorOp (IntOp it) (IntOp it) := λ T, i2p (type_check_arithop_int_int E L π f it v1 n1 v2 n2 T (Z.lxor n1 n2) XorOp m1 m2 _).
  Next Obligation. done. Qed.
  Global Program Instance type_check_shl_int_int_inst E L π f it v1 n1 v2 n2 m1 m2 :
    TypedCheckBinOp E L f v1 (v1 ◁ᵥ{π, m1} n1 @ int it) v2 (v2 ◁ᵥ{π, m2} n2 @ int it) ShlOp (IntOp it) (IntOp it) := λ T, i2p (type_check_arithop_int_int E L π f it v1 n1 v2 n2 T (n1 ≪  n2) ShlOp m1 m2 _).
  Next Obligation. done. Qed.
  Global Program Instance type_check_shr_int_int_inst E L π f it v1 n1 v2 n2 m1 m2 :
    TypedCheckBinOp E L f v1 (v1 ◁ᵥ{π, m1} n1 @ int it) v2 (v2 ◁ᵥ{π, m2} n2 @ int it) ShrOp (IntOp it) (IntOp it) := λ T, i2p (type_check_arithop_int_int E L π f it v1 n1 v2 n2 T (n1 ≫  n2) ShrOp m1 m2 _).
  Next Obligation. done. Qed.
End check_arithop.

Section switch.
  Context `{!typeGS Σ}.

  Inductive destruct_hint_switch_int :=
  | DestructHintSwitchIntCase (n : Z)
  | DestructHintSwitchIntDefault.

  Lemma type_switch_int E L f n it v m ss def fn R ϝ:
    ([∧ map] i↦mi ∈ m,
      li_trace (DestructHintSwitchIntCase i) (
             ⌜discriminate_hint (n = i)⌝ -∗ ∃ s, ⌜ss !! mi = Some s⌝ ∗ typed_stmt E L f s fn R ϝ)) ∧
    (li_trace (DestructHintSwitchIntDefault) (
                     ⌜discriminate_hint (n ∉ (map_to_list m).*1)⌝ -∗ typed_stmt E L f def fn R ϝ))
    ⊢ typed_switch E L f v _ (int it) n it m ss def fn R ϝ.
  Proof.
    unfold li_trace, discriminate_hint.
    iIntros "HT Hit". rewrite /ty_own_val/=. iDestruct "Hit" as "(_ & %Hv)".
    iExists n. iSplit; first done.
    iInduction m as [] "IH" using map_ind; simplify_map_eq => //.
    { iDestruct "HT" as "[_ HT]". iApply "HT". iPureIntro.
      rewrite map_to_list_empty. set_solver. }
    rewrite big_andM_insert //. destruct (decide (n = i)); subst.
    - rewrite lookup_insert_eq. iDestruct "HT" as "[[HT _] _]". by iApply "HT".
    - rewrite lookup_insert_ne//. iApply "IH". iSplit; first by iDestruct "HT" as "[[_ HT] _]".
      iIntros (Hn). iDestruct "HT" as "[_ HT]". iApply "HT". iPureIntro.
      rewrite map_to_list_insert //. set_solver.
  Qed.
  Global Instance type_switch_int_inst E L f n v it : TypedSwitch E L f v _ (int it) n it :=
    λ m ss def fn R ϝ, i2p (type_switch_int E L f n it v m ss def fn R ϝ).
End switch.


Section unop.
  Context `{!typeGS Σ}.

  Lemma type_neg_int π E L f n it v m (T : typed_val_expr_cont_t) :
    (⌜π = f.1⌝ ∗ (⌜n ∈ it⌝ -∗ ⌜it_signed it = true⌝ ∗ ⌜n ≠ MinInt it⌝ ∗ T L (i2v (-n) it) MetaNone _ (int it) (-n)))
    ⊢ typed_un_op E L f v (v ◁ᵥ{π, m} n @ int it)%I (NegOp) (IntOp it) T.
  Proof.
    rewrite /ty_own_val/=.
    iIntros "(-> & HT) (-> & %Hv) %Φ #CTX #HE HL Hf HΦ". move: (Hv) => /val_to_Z_in_range Hel.
    iDestruct ("HT" with "[//]") as (Hs Hn) "HT".
    have [|v' Hv']:= val_of_Z_is_Some it (- n). {
      rewrite int_elem_of_it_iff. rewrite int_elem_of_it_iff in Hel.
      rewrite MinInt_eq in Hn.
      unfold elem_of, int_elem_of_it, max_int, min_int in *.
      rewrite Hs. rewrite Hs in Hel, Hn. lia.
    }
    assert (-n ∈ it) as Helem.
    { by eapply val_of_Z_in_range. }
    rewrite /i2v Hv'/=.
    iApply wp_neg_int => //.
    { rewrite wrap_to_it_id//. }
    iApply physical_step_intro. iNext.
    iApply ("HΦ" with "HL Hf [] HT").
    rewrite /ty_own_val/=.
    iR.
    iPureIntro. by apply: val_to_of_Z.
  Qed.
  Definition type_neg_int_inst := [instance @type_neg_int].
  Global Existing Instance type_neg_int_inst.

  Lemma type_not_int E L π f n it v m (T : typed_val_expr_cont_t) :
    (⌜π = f.1⌝ ∗ (⌜n ∈ it⌝ -∗ T L (i2v ((if it_signed it then Z.lnot n else Z_lunot (bits_per_int it) n)) it) MetaNone _ (int it) ((if it_signed it then Z.lnot n else Z_lunot (bits_per_int it) n))))
    ⊢ typed_un_op E L f v (v ◁ᵥ{π, m} n @ int it)%I (NotIntOp) (IntOp it) T.
  Proof.
    rewrite /ty_own_val/=.
    iIntros "(-> & HT) (-> & %Hv) %Φ #CTX #HE HL Hf HΦ". move: (Hv) => /val_to_Z_in_range Hel.
    iDestruct ("HT" with "[//]") as "HT".
    set (nz := (if it_signed it then Z.lnot n else Z_lunot (bits_per_int it) n)).
    have [|v' Hv']:= val_of_Z_is_Some it nz. {
      rewrite int_elem_of_it_iff. rewrite int_elem_of_it_iff in Hel.
      unfold elem_of, int_elem_of_it, max_int, min_int, Z_lunot, Z.lnot, Z.pred in *.
      destruct (it_signed it); simpl in *; first lia.
      split.
      - apply Z.mod_pos. rewrite /bits_per_int/bytes_per_int/bits_per_byte. lia.
      - rewrite /int_modulus. subst nz.
        match goal with
        | |- ?a `mod` ?b ≤ _ => specialize (Z_mod_lt a b); lia
        end.
    }
    rewrite /i2v /=.
    iApply (wp_unop_det_pure v').
    { intros. subst nz. split; [inversion 1; simplify_eq/= | move => ->]; simplify_eq/=; first done.
      econstructor; done. }
    rewrite Hv' /=.
    iApply physical_step_intro. iNext.
    iApply ("HΦ" with "HL Hf"); last done.
    rewrite /ty_own_val/=. iR. iPureIntro.
    by apply: val_to_of_Z.
  Qed.
  Definition type_not_int_inst := [instance @type_not_int].
  Global Existing Instance type_not_int_inst.

  Lemma type_cast_int π E L f n (it1 it2 : int_type) v m (T : typed_val_expr_cont_t) :
    (⌜π = f.1⌝ ∗ (⌜n ∈ it1⌝ -∗ ∀ v, T L v MetaNone _ (int it2) (wrap_to_it n it2)))
    ⊢ typed_un_op E L f v (v ◁ᵥ{π, m} n @ int it1)%I (CastOp (IntOp it2)) (IntOp it1) T.
  Proof.
    rewrite /ty_own_val/=.
    iIntros "(-> & HT) (-> & %Hv) %Φ #CTX #HE HL Hf HΦ".
    iSpecialize ("HT" with "[]").
    { iPureIntro. by apply: val_to_Z_in_range. }
    destruct (val_of_Z_is_Some it2 (wrap_to_it n it2)) as (n' & Hit').
    { apply wrap_to_it_in_range. }
    iApply wp_cast_int => //.
    iApply physical_step_intro. iNext.
    iApply ("HΦ" with "HL Hf [] HT") => //.
    rewrite /ty_own_val/=. iR.
    iPureIntro. by apply: val_to_of_Z.
  Qed.
  Definition type_cast_int_inst := [instance @type_cast_int].
  Global Existing Instance type_cast_int_inst.
End unop.

Section bool.
  Context `{!typeGS Σ}.

  (** Bool *)
  Lemma type_val_bool' b π :
    ⊢ (val_of_bool b) ◁ᵥ{π, MetaNone} b @ bool_t.
  Proof. rewrite /ty_own_val/=. iIntros. by destruct b. Qed.
  Lemma type_val_bool b π (T : typed_value_cont_t) :
    (T MetaNone bool bool_t b) ⊢ typed_value π (val_of_bool b) T.
  Proof. iIntros "HT #LFT". iExists bool, bool_t, b. iFrame. iApply type_val_bool'. Qed.
  Definition type_val_bool_inst := [instance @type_val_bool].
  Global Existing Instance type_val_bool_inst.

  Lemma val_to_bool_val_to_Z v b :
    val_to_bool v = Some b →
    val_to_Z v U8 = Some (bool_to_Z b).
  Proof.
    intros Heq; unfold val_to_bool in Heq.
    destruct v as [ | m]; first done.
    destruct m as [ m | |]; [|done..].
    destruct m as [m  ].
    destruct (decide (m = 0)) as [ -> | ].
    { destruct v.
      - injection Heq as <-. done.
      - congruence. }
    destruct (decide (m = 1)) as [-> | ].
    { destruct v.
      - injection Heq as <-. done.
      - congruence. }
    destruct m as [ | [] | []]; congruence.
  Qed.

  Lemma type_relop_bool_bool E L f v1 b1 v2 b2 (T : typed_val_expr_cont_t) b op m1 m2 :
    match op with
    | EqOp rit => Some (eqb b1 b2, rit)
    | NeOp rit => Some (negb (eqb b1 b2), rit)
    | _ => None
    end = Some (b, U8) →
    (T L (val_of_bool b) MetaNone bool bool_t b)
    ⊢ typed_bin_op E L f v1 (v1 ◁ᵥ{f.1, m1} b1 @ bool_t) v2 (v2 ◁ᵥ{f.1, m2} b2 @ bool_t) op (BoolOp) (BoolOp) T.
  Proof.
    rewrite /ty_own_val/=.
    iIntros "%Hop HT (-> & %Hv1) (-> & %Hv2)" (Φ) "#CTX #HE HL Hf HΦ".
    iApply (wp_binop_det_pure (val_of_bool b)).
    { destruct op, b1, b2; simplify_eq.
      all: split; [ inversion 1; simplify_eq/= | move => -> ]; simplify_eq/=.
      all: try by (symmetry; eapply val_of_bool_iff_val_of_Z).
      all: econstructor => //; case_bool_decide; try done.
      all: by apply val_of_bool_iff_val_of_Z. }
    iApply physical_step_intro. iNext.
    iApply ("HΦ" with "HL Hf"); last done.
    rewrite /ty_own_val/=.
    iPureIntro. by destruct b.
  Qed.

  Global Program Instance type_eq_bool_bool_inst E L f v1 b1 v2 b2 :
    TypedBinOpVal E L f v1 (bool_t) b1 v2 (bool_t) b2 (EqOp U8) (BoolOp) (BoolOp) := λ T, i2p (type_relop_bool_bool E L f v1 b1 v2 b2 T (eqb b1 b2) _ MetaNone MetaNone _).
  Solve Obligations with done.
  Global Program Instance type_ne_bool_bool_inst E L f v1 b1 v2 b2 :
    TypedBinOpVal E L f v1 (bool_t) b1 v2 (bool_t) b2 (NeOp U8) (BoolOp) (BoolOp) := λ T, i2p (type_relop_bool_bool E L f v1 b1 v2 b2 T (negb (eqb b1 b2)) _ MetaNone MetaNone _).
  Solve Obligations with done.

  Lemma type_notop_bool π E L f v b m (T : typed_val_expr_cont_t) :
    ⌜π = f.1⌝ ∗ T L (val_of_bool (negb b)) MetaNone bool bool_t (negb b)
    ⊢ typed_un_op E L f v (v ◁ᵥ{π, m} b @ bool_t) NotBoolOp BoolOp T.
  Proof.
    rewrite /ty_own_val/=.
    iIntros "(-> & HT) (-> & %Hv)" (Φ) "#CTX #HE HL Hf HΦ".
    iApply (wp_unop_det_pure (val_of_bool (negb b))).
    { intros. split; [inversion 1; simplify_eq/= | move => ->]; simplify_eq/=; first done.
      econstructor; done. }
    iApply physical_step_intro. iNext.
    iApply ("HΦ" with "HL Hf"); last done.
    rewrite /ty_own_val/=. iPureIntro. by destruct b.
  Qed.
  Definition type_notop_bool_inst := [instance @type_notop_bool].
  Global Existing Instance type_notop_bool_inst.

  (** Bitwise operators *)
  Definition bool_arith_op_result b1 b2 op : option bool :=
    match op with
    | AndOp => Some (andb b1 b2)
    | OrOp  => Some (orb b1 b2)
    | XorOp => Some (xorb b1 b2)
    | _     => None (* Other operators are not supported. *)
    end.

  Lemma type_arithop_bool_bool E L f v1 b1 v2 b2 (T : typed_val_expr_cont_t) b op m1 m2 :
    bool_arith_op_result b1 b2 op = Some b →
    T L (val_of_bool b) MetaNone bool (bool_t) b ⊢
    typed_bin_op E L f v1 (v1 ◁ᵥ{f.1, m1} b1 @ bool_t) v2 (v2 ◁ᵥ{f.1, m2} b2 @ bool_t) op (BoolOp) (BoolOp) T.
  Proof.
    rewrite /ty_own_val/=.
    iIntros "%Hop HT (-> & %Hv1) (-> & %Hv2) %Φ #CTX #HE HL Hf HΦ".
    iApply (wp_binop_det_pure (val_of_bool b)).
    { destruct op, b1, b2; simplify_eq.
      all: split; [ inversion 1; simplify_eq/= | move => -> ]; simplify_eq/=; try done.
      all: eapply ArithOpBB; done. }
    iApply physical_step_intro. iNext.
    iApply ("HΦ" with "HL Hf [] HT").
    rewrite /ty_own_val/=. destruct b; done.
  Qed.

  Global Program Instance type_and_bool_bool_inst E L f v1 b1 v2 b2:
    TypedBinOpVal E L f v1 (bool_t) b1 v2 (bool_t) b2 AndOp (BoolOp) (BoolOp) := λ T, i2p (type_arithop_bool_bool E L f v1 b1 v2 b2 T (andb b1 b2) _ MetaNone MetaNone _).
  Next Obligation. done. Qed.
  Global Program Instance type_or_bool_bool_inst E L f v1 b1 v2 b2:
    TypedBinOpVal E L f v1 (bool_t) b1 v2 (bool_t) b2 OrOp (BoolOp) (BoolOp) := λ T, i2p (type_arithop_bool_bool E L f v1 b1 v2 b2 T (orb b1 b2) _ MetaNone MetaNone _).
  Next Obligation. done. Qed.
  Global Program Instance type_xor_bool_bool_inst E L f v1 b1 v2 b2:
    TypedBinOpVal E L f v1 (bool_t) b1 v2 (bool_t) b2 XorOp (BoolOp) (BoolOp) := λ T, i2p (type_arithop_bool_bool E L f v1 b1 v2 b2 T (xorb b1 b2) _ MetaNone MetaNone _).
  Next Obligation. done. Qed.

  Inductive trace_if_bool :=
  | TraceIfBool (b : bool).

  Lemma type_if_bool E L π b v m T1 T2:
    (case_destruct b (λ b' _,
      li_trace (TraceIfBool b, b') (
      normalize_spatial_context E L True (if b' then T1 else T2))))
    ⊢ typed_if E L v (v ◁ᵥ{π, m} b @ bool_t) T1 T2.
  Proof.
    unfold li_trace, case_destruct.
    rewrite /ty_own_val/=.
    iIntros "(% & Hs)".
    iIntros (??) "CTX HE HL (-> & %Hv)".
    iMod ("Hs" with "[] CTX HE HL [//]") as "(%L2 & HL & HT)"; first done.
    iFrame.
    iExists b. iR. destruct b; done.
  Qed.
  Definition type_if_bool_inst := [instance @type_if_bool].
  Global Existing Instance type_if_bool_inst.

  Lemma type_assert_bool E L f b s fn R v ϝ :
    (⌜b = true⌝ ∗ typed_stmt E L f s fn R ϝ)
    ⊢ typed_assert E L f v (bool_t) b s fn R ϝ.
  Proof.
    iIntros "[-> Hs] #CTX #HE HL Hf (_ & Hb)". by iFrame.
  Qed.
  Global Instance type_assert_bool_inst E L f b v : TypedAssert E L f v (bool_t) b :=
    λ s fn R ϝ, i2p (type_assert_bool E L f b s fn R v ϝ).
End bool.

Section char.
  Context `{!typeGS Σ}.

  (** Char *)
  Lemma type_char_val z π :
    is_valid_char z → ⊢ i2v z CharIt ◁ᵥ{π, MetaNone} z @ char_t.
  Proof.
    intros Hvalid.
    specialize (is_valid_char_in_char_it _ Hvalid) as Hn.
    move: Hn => /(val_of_Z_is_Some) [v Hv].
    move: (Hv) => /val_to_of_Z Hn.
    rewrite /ty_own_val/=. iPureIntro.
    rewrite /val_to_char.
    split; first done.
    apply bind_Some. exists z.
    split.
    - rewrite /i2v Hv/=//.
    - rewrite decide_True; done.
  Qed.

  Lemma type_val_char z π (T : typed_value_cont_t):
    ⌜is_valid_char z⌝ ∗ T MetaNone _ (char_t) z ⊢ typed_value π (i2v z CharIt) T.
  Proof.
    iIntros "[%Hn HT] #CTX".
    iExists Z, (char_t), z. iFrame.
    by iApply type_char_val.
  Qed.
  Definition type_val_char_inst := [instance @type_val_char].
  Global Existing Instance type_val_char_inst.
End char.
