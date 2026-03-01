From refinedrust Require Import typing shims.
From rrstd.iterator.theories Require Import iterator.
From rrstd.closures.closures.generated Require Import generated_specs_closures.

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


(* TODO move *)
Definition li_sealed `{!refinedrustGS Σ} (P : iProp Σ) : iProp Σ :=
  P.
Global Typeclasses Opaque li_sealed.

Lemma li_sealed_use_pers `{!refinedrustGS Σ} (P : iProp Σ) `{!Persistent P} :
  li_sealed P -∗ □ P.
Proof.
  unfold li_sealed. iIntros "#Ha". iModIntro. done.
Qed.

Section closure_props.
  Context `{!refinedrustGS Σ}.

  Context (Clos_rt Args_rt Clos_out_rt : RT).

  Class ClosureHasTrivialPre (fnonce_attrs : FnOnce_spec_attrs Clos_rt Args_rt Clos_out_rt) := closure_has_trivial_pre_proof : ∀ π self args, ⊢ FnOnce_Pre fnonce_attrs π self args.

End closure_props.

Ltac solve_closure_has_trivial_pre :=
  match goal with
  | |- ClosureHasTrivialPre _ _ _ _ =>
    unfold ClosureHasTrivialPre;
    intros ???; prepare_initial_coq_context;
    iStartProof;
    unshelve (repeat liRStep; solve[fail]);
    unshelve (sidecond_solver);
    sidecond_hammer; 
    apply inhabitant
  end.

(* TODO: don't have this as hint, but generate instances in the frontend *)
Global Hint Extern 100 (ClosureHasTrivialPre _ _ _ _) =>
  solve_closure_has_trivial_pre : typeclass_instances.

Section map_inv_variants.
  Context `{!refinedrustGS Σ}.

  Definition map_inv_ty (Self_rt Item_rt Clos_rt Clos_out_rt : RT)
    (fnonce_attrs : FnOnce_spec_attrs Clos_rt (tuple1_rt Item_rt) Clos_out_rt)
    (fnmut_attrs : FnMut_spec_attrs Clos_rt (tuple1_rt Item_rt) Clos_out_rt) :=
    thread_id → RT_xt Self_rt → RT_xt Clos_rt → iProp Σ.
  Global Arguments map_inv_ty : simpl never.

  Context
    (Self_rt Item_rt Clos_rt Clos_out_rt : RT)
    (fnonce_attrs : FnOnce_spec_attrs Clos_rt (tuple1_rt Item_rt) Clos_out_rt)
    (fnmut_attrs : FnMut_spec_attrs Clos_rt (tuple1_rt Item_rt) Clos_out_rt)
  .

  Lemma simpl_exist_map_inv_trivial Q :
    SimplExist (map_inv_ty _ _ _ _ fnonce_attrs fnmut_attrs) Q
      (∃ (Inv : thread_id → RT_xt Self_rt → RT_xt Clos_rt → iProp Σ), Q Inv).
  Proof.
    unfold SimplExist.
    done.
  Qed.

  (* For a trivial pre, instantiate with a trivial invariant *)
  Lemma simpl_exist_map_inv_pure_pre Q :
    ClosureHasTrivialPre _ _ _ fnonce_attrs →
    SimplExist (map_inv_ty Self_rt Item_rt Clos_rt Clos_out_rt fnonce_attrs fnmut_attrs) Q
      (Q (λ _ _ _, True)%I).
  Proof.
    intros Hpre.
    unfold SimplExist.
    eauto with iFrame.
  Qed.

  Lemma simpl_forall_map_inv Q :
    SimplForall (map_inv_ty _ _ _ _ fnonce_attrs fnmut_attrs) 1 Q (∀ (Inv : thread_id → RT_xt Self_rt → RT_xt Clos_rt → iProp Σ), Q Inv).
  Proof.
    unfold SimplForall.
    done.
  Qed.
End map_inv_variants.
Global Hint Extern 1000 (SimplExist (map_inv_ty _ _ _ _ ?fnonce ?fnmut) _ _) =>
  notypeclasses refine (simpl_exist_map_inv_trivial _ _ _ _ fnonce fnmut _) : typeclass_instances.
Global Hint Extern 10 (SimplForall (map_inv_ty _ _ _ _ ?fnonce ?fnmut) _ _ _) =>
  notypeclasses refine (simpl_forall_map_inv _ _ _ _ fnonce fnmut _) : typeclass_instances.

Global Hint Extern 100 (SimplExist (map_inv_ty _ _ _ _ ?fnonce ?fnmut) _ _) =>
  notypeclasses refine (simpl_exist_map_inv_pure_pre _ _ _ _ fnonce fnmut _ _);
  typeclasses eauto : typeclass_instances.

Section map.
  Context `{RRGS : !refinedrustGS Σ}.
  Definition MapInv {Self_rt Item_rt Clos_rt Clos_out_rt : RT}
    (iter_attrs : traits_iterator_Iterator_spec_attrs Self_rt Item_rt)
    (Pre : thread_id → RT_xt Clos_rt → RT_xt (tuple1_rt Item_rt) → iProp Σ)
    (PostMut : thread_id → RT_xt Clos_rt → RT_xt (tuple1_rt Item_rt) → RT_xt Clos_rt → RT_xt Clos_out_rt → iProp Σ)
    (*(fnonce_attrs : FnOnce_spec_attrs Clos_rt (tuple1_rt Item_rt) Clos_out_rt)*)
    (*(fnmut_attrs : FnMut_spec_attrs Clos_rt (tuple1_rt Item_rt) Clos_out_rt) *)
    : _ → _ → iProp Σ :=
    λ (π : thread_id) (s : MapX Self_rt Clos_rt),
    (∃ (Inv : thread_id → RT_xt Self_rt → RT_xt Clos_rt → iProp Σ),
      (* user-picked invariant *)
      Inv π s.(map_it) s.(map_clos) ∗
      (* nested iterator invariant *)
      iter_attrs.(traits_iterator_Iterator_Inv) π s.(map_it) ∗
      (* progress *)
      li_sealed (□ (∀ it_state it_state' clos_state e,
        (☒ iter_attrs.(traits_iterator_Iterator_Next) π it_state (Some e) it_state') -∗
        Inv π it_state clos_state -∗
        Pre π clos_state *[e] ∗
        (∀ e' clos_state', ☒ PostMut π clos_state *[e] clos_state' e' -∗ Inv π it_state' clos_state'))) ∗
      (* progress (no element) *)
      li_sealed (□ (∀ it_state it_state' clos_state,
        (☒ iter_attrs.(traits_iterator_Iterator_Next) π it_state None it_state') -∗
        Inv π it_state clos_state -∗
        Inv π it_state' clos_state)))%I.

  Global Arguments MapInv : simpl never.
  Global Typeclasses Opaque MapInv.
End map.
