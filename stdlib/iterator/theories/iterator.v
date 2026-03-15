From refinedrust Require Import typing.

(** Declaration of the spec attributes of the `Iterator` trait (external, in order to use it in the below theories) *)
Definition traits_iterator_Iterator_Params_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Item_rt: RT) :=
  Type.
Definition traits_iterator_Iterator_Inv_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Item_rt: RT) (traits_iterator_Iterator_Params : traits_iterator_Iterator_Params_sig Self_rt Item_rt) :=
  (thread_id → traits_iterator_Iterator_Params → (RT_xt (Self_rt)) → iProp Σ).
Definition traits_iterator_Iterator_Next_sig `{RRGS : !(refinedrustGS Σ)} (Self_rt: RT) (Item_rt: RT) (traits_iterator_Iterator_Params : traits_iterator_Iterator_Params_sig Self_rt Item_rt) (traits_iterator_Iterator_Inv: (traits_iterator_Iterator_Inv_sig (Self_rt) (Item_rt) traits_iterator_Iterator_Params)) :=
  (thread_id → traits_iterator_Iterator_Params → (RT_xt (Self_rt)) → option (RT_xt (Item_rt)) → (RT_xt (Self_rt)) → iProp Σ).
Record traits_iterator_Iterator_spec_attrs `{RRGS : !(refinedrustGS Σ)} `{Self_rt : !RT} `{Item_rt : !RT} : Type := mk_traits_iterator_Iterator_spec_attrs {
  traits_iterator_Iterator_Params : (traits_iterator_Iterator_Params_sig (Self_rt) (Item_rt));
  traits_iterator_Iterator_Inv  : (traits_iterator_Iterator_Inv_sig (Self_rt) (Item_rt) traits_iterator_Iterator_Params);
  traits_iterator_Iterator_Next  : (traits_iterator_Iterator_Next_sig (Self_rt) (Item_rt) traits_iterator_Iterator_Params (traits_iterator_Iterator_Inv));
}.
#[global] Arguments traits_iterator_Iterator_spec_attrs : clear implicits.
#[global] Arguments traits_iterator_Iterator_spec_attrs {_ _}.
#[global] Arguments mk_traits_iterator_Iterator_spec_attrs  {_} {_} {_} {_}.

Section trans.
  Context `{RRGS : !refinedrustGS Σ}.
  (* Note: Depends on the whole attrs instead of the Next projection so that the projection doesn't simplify away, which is a problem for [LearnFromHyp] rules. *)
  Fixpoint IteratorNextFusedTrans {Self_rt Item_rt : RT}
    (attrs : traits_iterator_Iterator_spec_attrs Self_rt Item_rt)
    (π : thread_id)
    p
    (s1 : RT_xt Self_rt) (els : list (RT_xt Item_rt)) (s2 : RT_xt Self_rt) : iProp Σ
    :=
    match els with
    | [] => ⌜s1 = s2⌝
    | (e1 :: els) =>
      ∃ s1',
        attrs.(traits_iterator_Iterator_Next) π p s1 (Some e1) s1' ∗
        IteratorNextFusedTrans attrs π p s1' els s2
    end.

  Lemma iterator_next_fused_trans_app {Self_rt Item_rt : RT} (A : traits_iterator_Iterator_spec_attrs Self_rt Item_rt) π p s1 hist s2 x :
    IteratorNextFusedTrans A π p s1 (hist ++ [x]) s2 ⊣⊢ (∃ s2', IteratorNextFusedTrans A π p s1 hist s2' ∗ A.(traits_iterator_Iterator_Next) π p s2' (Some x) s2).
  Proof.
    iInduction hist as [ | y hist] "IH" forall (s1 s2); simpl.
    - iSplit.
      + iIntros "(%s1' & ? & <-)". by iFrame.
      + iIntros "(%s2' & -> & ?)". by iFrame.
    - iSplit.
      + iIntros "(%s1' & Ha & Hb)".
        iPoseProof ("IH" with "Hb") as "(%s2' & Hb & Hc)".
        iFrame.
      + iIntros "(%s2' & (%s1' & ? & ?) & ?)".
        iFrame. iApply "IH". iFrame.
  Qed.

  Lemma simplify_goal_iterator_next_fused_trans_app {Self_rt Item_rt : RT} (A : traits_iterator_Iterator_spec_attrs Self_rt Item_rt) π p s1 hist s2 s1' hist'
    T :
    (∃ x,
      ⌜hist = hist' ++ [x]⌝ ∗
      IteratorNextFusedTrans A π p s1 hist' s1' ∗
      A.(traits_iterator_Iterator_Next) π p s1' (Some x) s2) ∗ T ⊢ simplify_goal (IteratorNextFusedTrans A π p s1 hist s2) T.
  Proof.
    rewrite /simplify_goal.
    iIntros "((%x & -> & Ha & Hb) & $)".
    rewrite iterator_next_fused_trans_app.
    iFrame.
  Qed.
  (* Apply transitivity in case the next relation is in context already *)
  Definition simplify_goal_iterator_next_fused_trans_app_find_next {Self_rt Item_rt : RT} (A : traits_iterator_Iterator_spec_attrs Self_rt Item_rt) π p s1 hist s2 s1' hist'
    `{!CheckOwnInContext (IteratorNextFusedTrans A π p s1 hist' s1')}
    e s1''
    `{!CheckOwnInContext (A.(traits_iterator_Iterator_Next) π p s1' (Some e) s1'')} T
    :=
    simplify_goal_iterator_next_fused_trans_app A π p s1 hist s2 s1' hist' T.
  Definition simplify_goal_iterator_next_fused_trans_app_find_next_inst := [instance @simplify_goal_iterator_next_fused_trans_app_find_next with 50%N].
  Global Existing Instance simplify_goal_iterator_next_fused_trans_app_find_next_inst.

  (* Apply transitivity if the attrs are concrete *)
  Definition simplify_goal_iterator_next_fused_trans_app_not_var {Self_rt Item_rt : RT} (A : traits_iterator_Iterator_spec_attrs Self_rt Item_rt) π p s1 hist s2 s1' hist'
    `{!CheckOwnInContext (IteratorNextFusedTrans A π p s1 hist' s1')}
    `{!IsNotVar A} T
    :=
    simplify_goal_iterator_next_fused_trans_app A π p s1 hist s2 s1' hist' T.
  Definition simplify_goal_iterator_next_fused_trans_app_not_var_inst := [instance @simplify_goal_iterator_next_fused_trans_app_not_var with 50%N].
  Global Existing Instance simplify_goal_iterator_next_fused_trans_app_not_var_inst.

  Lemma simplify_goal_iterator_next_fused_trans_nil {Self_rt Item_rt : RT} (A : traits_iterator_Iterator_spec_attrs Self_rt Item_rt) π p s1 hist T :
    (⌜hist = []⌝) ∗ T ⊢ simplify_goal (IteratorNextFusedTrans A π p s1 hist s1) T.
  Proof.
    rewrite /simplify_goal.
    iIntros "(-> & $)".
    eauto.
  Qed.
  Definition simplify_goal_iterator_next_fused_trans_nil_inst := [instance @simplify_goal_iterator_next_fused_trans_nil with 10%N].
  Global Existing Instance simplify_goal_iterator_next_fused_trans_nil_inst.

  Global Instance IteratorNextFusedTrans_pers {Self_rt Item_rt : RT} (A : traits_iterator_Iterator_spec_attrs Self_rt Item_rt) π p :
    (∀ s1 e s2, Persistent (A.(traits_iterator_Iterator_Next) π p s1 e s2)) →
    ∀ s1 hist s2, Persistent (IteratorNextFusedTrans A π p s1 hist s2).
  Proof.
    intros Hpers. intros s1 hist s2.
    induction hist as [ | x hist IH] in s1, s2, hist |-*; simpl; first apply _.
    apply _.
  Qed.

  (** Automation support for learning inductive properties about iterator executions *)
  Class IteratorLearnInductive {Self_rt Item_rt : RT} (A : traits_iterator_Iterator_spec_attrs Self_rt Item_rt) p := mk_iterator_learn {
    iterator_learn_inductive_Q : RT_xt Self_rt → list (RT_xt Item_rt) → RT_xt Self_rt → Prop;
    iterator_learn_inductive_proof π s1 hist s2 :
      ☒ IteratorNextFusedTrans A π p s1 hist s2 -∗ ⌜iterator_learn_inductive_Q s1 hist s2⌝;
  }.

  Global Program Instance learn_from_hyp_iterator {Self_rt Item_rt : RT} (A : traits_iterator_Iterator_spec_attrs Self_rt Item_rt) π p s1 xs s2 :
    IteratorLearnInductive A p →
    LearnFromHyp (IteratorNextFusedTrans A π p s1 xs s2) :=
    λ L, {| learn_from_hyp_Q := ⌜L.(iterator_learn_inductive_Q) s1 xs s2⌝ |}.
  Next Obligation.
    iIntros (?? A ? p s1 xs s2 L F ?) "Ha".
    iPoseProof (boringly_intro with "Ha") as "#Hx".
    iPoseProof (iterator_learn_inductive_proof with "Hx") as "$".
    done.
  Qed.
End trans.

(* We seal these for Lithium *)
Global Arguments traits_iterator_Iterator_Inv : simpl never.
Global Typeclasses Opaque traits_iterator_Iterator_Inv.

Section automation.
  Context `{!refinedrustGS Σ}.

  Definition FindIteratorInv {Self_rt Item_rt : RT} (A : traits_iterator_Iterator_spec_attrs Self_rt Item_rt) π self :=
    {| fic_A := traits_iterator_Iterator_Params A; fic_Prop x := traits_iterator_Iterator_Inv A π x self |}.
  Global Typeclasses Opaque FindIteratorInv.


  Global Instance related_to_iterator_inv {Self_rt Item_rt : RT} (A : traits_iterator_Iterator_spec_attrs Self_rt Item_rt) π x self :
    RelatedTo (traits_iterator_Iterator_Inv A π x self) | 100 :=
      {| rt_fic := FindIteratorInv A π self |}.

  Lemma find_in_context_iterator_inv {Self_rt Item_rt : RT} (A : traits_iterator_Iterator_spec_attrs Self_rt Item_rt) π self T :
    (∃ x, traits_iterator_Iterator_Inv A π x self ∗ T x)
    ⊢ find_in_context (FindIteratorInv A π self) T.
  Proof.
    rewrite /FindIteratorInv/find_in_context.
    iIntros "(%x & Hinv & HT)".
    iFrame.
  Qed.
  Definition find_in_context_iterator_inv_inst := [instance @find_in_context_iterator_inv with FICSyntactic].
  Global Existing Instance find_in_context_iterator_inv_inst.

  Lemma subsume_iterator_inv {Self_rt Item_rt : RT} (A : traits_iterator_Iterator_spec_attrs Self_rt Item_rt) π x1 x2 self1 self2 T :
    ⌜x1 = x2⌝ ∗ ⌜self1 = self2⌝ ∗ T
    ⊢ subsume (traits_iterator_Iterator_Inv A π x1 self1) (traits_iterator_Iterator_Inv A π x2 self2) T.
  Proof.
    iIntros "(<- & <- & $)".
    eauto.
  Qed.
  Definition subsume_iterator_inv_inst := [instance @subsume_iterator_inv].
  Global Existing Instance subsume_iterator_inv_inst.
End  automation.
