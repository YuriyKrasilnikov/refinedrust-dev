From refinedrust Require Import typing shims.
From rrstd.iterator.theories Require Import iterator.
From rrstd.closures.theories Require Import closures.

Record MapX (I : RT) (F : RT) : Type := mk_map_x {
  map_it : RT_xt I;
  map_clos : RT_xt F;
}.
Global Arguments map_it {_ _}.
Global Arguments map_clos {_ _}.
Global Arguments mk_map_x {_ _}.
Canonical Structure MapXRT (I F : RT) := directRT (MapX I F).

Global Instance MapX_inh I F :
  Inhabited (RT_xt I) → Inhabited (RT_xt F) → Inhabited (MapX I F).
Proof.
  intros Ha Hb. exact (populate (mk_map_x inhabitant inhabitant)).
Qed.

Global Instance MapX_simpl_exist I F H :
  SimplExist (MapX I F) H (∃ (i : RT_xt I) (f : RT_xt F), H (mk_map_x i f)).
Proof.
  intros (i & f & Ha).
  eexists _. done.
Qed.
Global Instance MapX_simpl_forall I F H :
  SimplForall (MapX I F) 2 H (∀ (i : RT_xt I) (f : RT_xt F), H (mk_map_x i f)).
Proof.
  intros Ha (i & f). apply Ha.
Qed.

Global Instance simpl_both_mapX {I F} (m1 m2 : MapX I F) :
  SimplBothRel (=) m1 m2 (m1.(map_it) = m2.(map_it) ∧ (m1.(map_clos) = m2.(map_clos))).
Proof.
  unfold SimplBothRel.
  destruct m1, m2; naive_solver.
Qed.

(** Instantiation hints for iterator adapters which are mapping a closure over an iterator (map, all, position, exists, ...) *)
Section map_inv_variants.
  Context `{!refinedrustGS Σ}.

  Definition map_inv_ty (Self_rt Item_rt Clos_rt Clos_out_rt : RT)
    (fnonce_attrs : FnOnce_spec_attrs Clos_rt (tuple1_rt Item_rt) Clos_out_rt) :=
    thread_id → RT_xt Self_rt → RT_xt Clos_rt → iProp Σ.
  Global Arguments map_inv_ty : simpl never.

  Context (Self_rt Item_rt Clos_rt Clos_out_rt : RT)
    (fnonce_attrs : FnOnce_spec_attrs Clos_rt (tuple1_rt Item_rt) Clos_out_rt).

  (* Default instantiation *)
  Lemma simpl_exist_map_inv_trivial Q :
    SimplExist (map_inv_ty _ _ _ _ fnonce_attrs) Q
      (∃ (Inv : thread_id → RT_xt Self_rt → RT_xt Clos_rt → iProp Σ), Q Inv).
  Proof. unfold SimplExist. done. Qed.
  Lemma simpl_forall_map_inv Q :
    SimplForall (map_inv_ty _ _ _ _ fnonce_attrs) 1 Q (∀ (Inv : thread_id → RT_xt Self_rt → RT_xt Clos_rt → iProp Σ), Q Inv).
  Proof. unfold SimplForall. done. Qed.

  (* For a trivial pre, instantiate with a trivial invariant *)
  Lemma simpl_exist_map_inv_pure_pre Q :
    ClosureHasTrivialPre _ _ _ fnonce_attrs →
    SimplExist (map_inv_ty Self_rt Item_rt Clos_rt Clos_out_rt fnonce_attrs) Q
      (Q (λ _ _ _, True)%I).
  Proof.
    intros Hpre.
    unfold SimplExist.
    eauto with iFrame.
  Qed.
End map_inv_variants.
Global Hint Extern 1000 (SimplExist (map_inv_ty _ _ _ _ ?fnonce) _ _) =>
  notypeclasses refine (simpl_exist_map_inv_trivial _ _ _ _ fnonce _) : typeclass_instances.
Global Hint Extern 10 (SimplForall (map_inv_ty _ _ _ _ ?fnonce) _ _ _) =>
  notypeclasses refine (simpl_forall_map_inv _ _ _ _ fnonce _) : typeclass_instances.

Global Hint Extern 100 (SimplExist (map_inv_ty _ _ _ _ ?fnonce) _ _) =>
  notypeclasses refine (simpl_exist_map_inv_pure_pre _ _ _ _ fnonce _ _);
  typeclasses eauto : typeclass_instances.

(** Instantiation hints for iterator adapters which receive a closure param instantiation predicate *)
Section clos_param_variants.
  Context `{!refinedrustGS Σ}.

  Definition clos_param_pred_ty (Args_rt Clos_rt Clos_out_rt : RT)
    (fnonce_attrs : FnOnce_spec_attrs Clos_rt Args_rt Clos_out_rt) :=
    fnonce_attrs.(FnOnce_Params) → Prop.
  Global Arguments clos_param_pred_ty : simpl never.

  Context (Args_rt Clos_rt Clos_out_rt : RT)
    (fnonce_attrs : FnOnce_spec_attrs Clos_rt Args_rt Clos_out_rt).

  (* Default instantiation *)
  Lemma simpl_exist_clos_param_pred_trivial Q :
    SimplExist (clos_param_pred_ty _ _ _ fnonce_attrs) Q
      (∃ (ParamPred : fnonce_attrs.(FnOnce_Params) → Prop), Q ParamPred).
  Proof. unfold SimplExist. done. Qed.
  Lemma simpl_forall_clos_param_pred Q :
    SimplForall (clos_param_pred_ty _ _ _ fnonce_attrs) 1 Q (∀ (ParamPred : fnonce_attrs.(FnOnce_Params) → Prop), Q ParamPred).
  Proof. unfold SimplForall. done. Qed.

  (* For trivial Params, instantiate with a trivial invariant *)
  Lemma simpl_exist_clos_param_pred_empty Q :
    TCDone (fnonce_attrs.(FnOnce_Params) = plist id []) →
    SimplExist (clos_param_pred_ty Args_rt Clos_rt Clos_out_rt fnonce_attrs) Q
      (Q (λ _, True)).
  Proof.
    intros Hpre.
    unfold SimplExist.
    eauto with iFrame.
  Qed.
End clos_param_variants.
Global Hint Extern 1000 (SimplExist (clos_param_pred_ty _ _ _ ?fnonce) _ _) =>
  notypeclasses refine (simpl_exist_clos_param_pred_trivial _ _ _ fnonce _) : typeclass_instances.
Global Hint Extern 10 (SimplForall (clos_param_pred_ty _ _ _ ?fnonce) _ _ _) =>
  notypeclasses refine (simpl_forall_clos_param_pred _ _ _ fnonce _) : typeclass_instances.

Global Hint Extern 100 (SimplExist (clos_param_pred_ty _ _ _ ?fnonce) _ _) =>
  notypeclasses refine (simpl_exist_clos_param_pred_empty _ _ _ fnonce _ _);
  typeclasses eauto : typeclass_instances.


Section map.
  Context `{RRGS : !refinedrustGS Σ}.
  Definition MapInv {Self_rt Item_rt Clos_rt Clos_out_rt : RT} {ClosParams : Type}
    (iter_attrs : traits_iterator_Iterator_spec_attrs Self_rt Item_rt)
    (Pre : thread_id → ClosParams → RT_xt Clos_rt → RT_xt (tuple1_rt Item_rt) → iProp Σ)
    (PostMut : thread_id → ClosParams → RT_xt Clos_rt → RT_xt (tuple1_rt Item_rt) → RT_xt Clos_rt → RT_xt Clos_out_rt → iProp Σ)
    : _ → _ → _ → iProp Σ :=
    λ (π : thread_id) (p : _ * (ClosParams → Prop)) (s : MapX Self_rt Clos_rt),
    let '(inner_p, ParamPred) := p in
    (∃ (Inv : thread_id → RT_xt Self_rt → RT_xt Clos_rt → iProp Σ),
      (* user-picked invariant *)
      Inv π s.(map_it) s.(map_clos) ∗
      (* nested iterator invariant *)
      iter_attrs.(traits_iterator_Iterator_Inv) π inner_p s.(map_it) ∗
      (* progress *)
      li_sealed (□ (∀ it_state it_state' clos_state e,
        (☒ iter_attrs.(traits_iterator_Iterator_Next) π inner_p it_state (Some e) it_state') -∗
        Inv π it_state clos_state -∗
        ∃ p_clos, ⌜ParamPred p_clos⌝ ∗ Pre π p_clos clos_state *[e] ∗
        (∀ e' clos_state', ☒ PostMut π p_clos clos_state *[e] clos_state' e' -∗ Inv π it_state' clos_state'))) ∗
      (* progress (no element) *)
      li_sealed (□ (∀ it_state it_state' clos_state,
        (☒ iter_attrs.(traits_iterator_Iterator_Next) π inner_p it_state None it_state') -∗
        Inv π it_state clos_state -∗
        Inv π it_state' clos_state)))%I.

  Global Arguments MapInv : simpl never.
  Global Typeclasses Opaque MapInv.
End map.
