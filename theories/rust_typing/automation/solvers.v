Require Import Stdlib.Strings.String.
From iris.proofmode Require Import coq_tactics reduction string_ident.
From refinedrust Require Export type ltypes hlist.
From lithium Require Export all.
From lithium Require Import hooks.
From refinedrust.automation Require Import lookup_definition proof_state.
From refinedrust.automation Require Export layout_ltac.
From refinedrust Require Import int programs program_rules functions uninit mut_ref.mut_ref shr_ref.shr_ref struct.struct unit value array.array alias_ptr.

Set Default Proof Using "Type".


(** * Automation for solving sideconditions spawned by the type system *)

(** The main hook for solving sideconditions, will be re-defined later. *)
Ltac sidecond_hook := idtac.
Ltac unsolved_sidecond_hook := idtac.

Tactic Notation "unfold_opaque" constr(c) := with_strategy 0 [c] (unfold c).
Tactic Notation "unfold_opaque" constr(c) "in" constr(d) := with_strategy 0 [c] (rewrite [d] /c).

(** ** interpret_rust_type solver *)

(** Since [lookup_definition] will give us a term that requires us to
   explicitly give all implicit arguments, we need some hackery to
   apply the arguments of literal type terms that would usually be implicit.
   Basically, we handle the case that the literal term expects a [typeGS] assumption
   and then a number of [RT]s that are later determined by the parameters we instantiate. *)
Ltac instantiate_benign_universals term :=
  lazymatch type of term with
  | ∀ (_ : gFunctors) (_ : typeGS _), _ =>
      instantiate_benign_universals uconstr:(term _ _)
  | ∀ _ : typeGS _, _ =>
      instantiate_benign_universals uconstr:(term ltac:(refine _))
  | _ =>
      constr:(term)
  end.

(** Instantiate a number of [RT] universals *)
Ltac count_in_term' term acc :=
  match type of term with
  | RT → _ =>
      (* [ZRT] is a dummy to instantiate the generic *)
      count_in_term' ltac:(constr:((term ZRT))) ltac:(constr:((S acc)))
  | spec_with _ _ _ =>
      acc
  (* hack, because for arguments afterwards we cannot instantiate with default inhabitants *)
  | _ → spec_with _ _ _ =>
      constr:(S acc)
  | _ → _ → spec_with _ _ _ =>
      constr:((2 + acc)%nat)
  | _ → _ → _ → spec_with _ _ _ =>
      constr:((3 + acc)%nat)
  | _ → _ → _ → _ → spec_with _ _ _ =>
      constr:((4 + acc)%nat)
  | ?x =>
      fail 1000 "extend count_in_term' for " x
  end.



Ltac count_in_term term :=
  count_in_term' term constr:(0).
Ltac instantiate_universal_evars term count :=
  match count with
  | 0 => uconstr:(term)
  | S ?n =>
      instantiate_universal_evars uconstr:(term _) constr:(n)
  end.
Ltac instantiate_universals term sub_count cont :=
  let term := instantiate_benign_universals term in
  let count := count_in_term term in
  let count := constr:((count - sub_count)%nat) in
  let count := eval simpl in count in
  let term := instantiate_universal_evars term count in
  cont term
.


(** Apply [term] to the sequence of arguments [apps]. [apps] is expected to be of type [hlist id ?tys] *)
Ltac apply_term_het term apps :=
  match apps with
  | +[] => constr:(term)
  | ?app +:: ?apps =>
      apply_term_het uconstr:(term app) apps
  end.
Ltac apply_term_het' term apps :=
  match apps with
  | +[] => uconstr:(term)
  | ?app +:: ?apps =>
      apply_term_het' uconstr:(term app) apps
  end.

(** Instantiate a type-like definition receiving a list of semantic lifetime parameters [lfts] and a list of semantic type parameters [tys]. *)
Definition hlist_indexl {A} {F : A → Type} {Xs} (hl : hlist F Xs) := Xs.
Ltac apply_type_term_het_evar term lfts tys attrs cont :=
  let attr_len := constr:(length (hlist_indexl attrs)) in
  let attr_len := eval simpl in attr_len in
  instantiate_universals term attr_len ltac:(fun term =>
    let term := apply_term_het' term attrs in
    let term := uconstr:(term (list_to_plist (F:=id) lft lfts) (hlist_to_plist tys)) in
    let term := constr:(term) in
    let term := eval simpl in term in
    cont constr:(term)
  )
.

(** This interprets syntactic Rust types used in some annotations into semantic RefinedRust types *)
(* NOTE: Be REALLY careful with this. The Ltac2 for looking up definitions will easily go haywire, and we cannot properly handle the exceptions here or show them.
   In particular, if this fails for some unknown reason, make sure that there are NO other definitions with the same name in scope, even below other modules! *)
Ltac interpret_rust_type_core lfts env ty := idtac.
Ltac interpret_lit_term lfts env term := idtac.

Ltac interpret_lit_term_list lfts env terms :=
  match terms with
  | [] => exact (+[] : hlist (@id Type) [])
  | ?term :: ?terms =>
      refine (_ +:: _);
      [interpret_lit_term lfts env term
      | interpret_lit_term_list lfts env terms ]
  end.

Ltac interpret_lit_term lfts env term ::=
  let term := eval hnf in term in
  match term with
  | TypeRt ?ty =>
      let Ha := fresh in
      refine (let Ha := ltac:(interpret_rust_type_core lfts env ty) in _);
      let Hx := eval unfold Ha in Ha in
      (*idtac "bla";*)
      (*idtac "ty = " Hx;*)
      let Hr := eval simpl in (rt_of Hx) in
      exact Hr

  | AppDef ?defname ?terms =>
      lookup_definition
        ltac:(fun term =>
          (let Ha := fresh in
          refine (let Ha : hlist (@id Type) _ := ltac:(interpret_lit_term_list lfts env terms) in _);
          let Hx := eval unfold Ha in Ha in
          (*let Hx := eval simpl in Hx in*)

          let term := instantiate_benign_universals term in
          let applied_term := apply_term_het term Hx in
          let t := eval simpl in applied_term in
          exact t)
          || fail 1000 "processing for " defname " failed"

        )
        defname || fail 1000 "definition lookup for " defname " failed"
  end
.


Ltac interpret_rust_type_list lfts env tys :=
  match tys with
  | [] => exact +[]
  | ?ty :: ?tys =>
      refine (_ +:: _);
      [ interpret_rust_type_core lfts env ty
      | interpret_rust_type_list lfts env tys ]
  end.
Ltac interpret_rust_lft lfts env lft :=
  (* TODO not great *)
  let κ := eval vm_compute in (lfts !! lft) in
  match κ with
  | Some ?κ =>
    refine κ
  | None =>
      fail 3 "did not find lifetime"
  end.
Ltac interpret_rust_lfts lfts env ls :=
  match ls with
  | [] => exact []
  | ?κ :: ?κs =>
      refine (_ :: _);
      [ interpret_rust_lft lfts env κ
      | interpret_rust_lfts lfts env κs ]
  end.

Ltac apply_rust_scope_inst lfts env inst term :=
  (* interpret the arguments *)
  match inst with
  | RSTScopeInst ?ls ?tys ?attrs =>
    let Ha := fresh in
    let Hb := fresh in
    let Hc := fresh in

    refine (let Ha : hlist type _ := ltac:(interpret_rust_type_list lfts env tys) in _);
    let Ha := eval unfold Ha in Ha in

    refine (let Hb : list lft := ltac:(interpret_rust_lfts lfts env ls) in _);
    let Hb := eval unfold Hb in Hb in

    refine (let Hc : hlist (@id Type) _ := ltac:(interpret_lit_term_list lfts env attrs) in _);
    let Hc := eval unfold Hc in Hc in

    apply_type_term_het_evar term Hb Ha Hc ltac:(fun applied_term =>
      exact applied_term
    )
  end.


Ltac interpret_rust_type_core lfts env ty ::=
  lazymatch ty with
  | RSTTyVar ?name =>
      let sty := eval vm_compute in (env !! name) in
      match sty with
      | Some (existT _ ?sty) =>
          exact sty
      | None =>
          fail 3 "Failed to find type variable " name " in the context"
      end
  | RSTLitType ?name ?inst =>
      (* CAVEAT: This only works if a unique identifier can be found! *)
      lookup_definition
        ltac:(fun term =>
          apply_rust_scope_inst lfts env inst term
          || fail 1000 "processing for " name " failed"
        )
        name || fail 1000 "definition lookup for " name " failed"
  | RSTInt ?it =>
      exact (int it)
  | RSTBool =>
      exact bool_t
  | RSTAliasPtr =>
      exact alias_ptr_t
  | RSTUnit =>
      exact unit_t
  | RSTStruct ?sls ?tys =>
      refine (struct_t sls ltac:(interpret_rust_type_list lfts env tys))
  | RSTArray ?len ?ty =>
      refine (array_t len _); interpret_rust_type_core lfts env ty
  | RSTRef ?mut ?κ ?ty =>
      match mut with
      | Mut =>
          refine (mut_ref _ _)
      | Shr =>
          refine (shr_ref _ _)
      end;
      [ interpret_rust_lft lfts env κ | interpret_rust_type_core lfts env ty ]
  end.
Tactic Notation "interpret_rust_type" constr(lfts) constr(env) constr(ty) :=
  interpret_rust_type_core lfts env ty .

Ltac solve_interpret_rust_type ::=
  match goal with
  | |- interpret_rust_type_pure_goal ?lfts ?st ?ty =>
      match goal with
      | H : TYVAR_MAP ?M |- _ =>
          let Hc := fresh in
          refine (let Hc := ltac:(interpret_rust_type lfts M st) in _);
          assert (ty = Hc) by reflexivity;
          exact I
      end
  end.

Ltac interpret_rust_enum_def_core lfts env ty :=
  lazymatch ty with
  | RSTEnumDef ?name ?inst =>
      (* CAVEAT: This only works if a unique identifier can be found! *)
      lookup_definition
        ltac:(fun term =>
          apply_rust_scope_inst lfts env inst term
        )
        name || fail 1000 "definition lookup for " name " failed"
  end.

Tactic Notation "interpret_rust_enum_def" constr(lfts) constr(env) constr(ty) :=
  interpret_rust_enum_def_core lfts env ty .
Ltac solve_interpret_rust_enum_def ::=
  match goal with
  | |- interpret_rust_enum_def_pure_goal ?lfts ?st ?en =>
      match goal with
      | H : TYVAR_MAP ?M |- _ =>
          let Hc := fresh in
          refine (let Hc := ltac:(interpret_rust_enum_def lfts M st) in _);
          assert (en = Hc) by reflexivity;
          exact I
      end
  end.



(** Evar instantiation *)
Ltac solve_ensure_evar_instantiated ::=
  lazymatch goal with
  | |- ensure_evar_instantiated_pure_goal (protected ?a) ?b =>
      liInst a b; exact I
  | |- ensure_evar_instantiated_pure_goal ?a ?b =>
      (* this is not an evar, we are done *)
      exact I
  end.

Section solve_evars.
  Context `{!typeGS Σ}.

  Lemma ensure_evars_instantiated_pure_goal_skip {A} {F : A → Type} (xs ys : list (sigT F)) a b :
    ensure_evars_instantiated_pure_goal xs ys →
    ensure_evars_instantiated_pure_goal (a :: xs) (b :: ys).
  Proof. done. Qed.
End solve_evars.

Ltac solve_ensure_evars_instantiated_step :=
  lazymatch goal with
  | |- ensure_evars_instantiated_pure_goal (existT _ (protected ?a) :: ?xs) (existT _ ?b :: ?ys) =>
      simpl; liInst a b;
      refine (ensure_evars_instantiated_pure_goal_skip xs ys _ _ _)
  | |- ensure_evars_instantiated_pure_goal (existT _ _ :: ?xs) (existT _ ?b :: ?ys) =>
      refine (ensure_evars_instantiated_pure_goal_skip xs ys _ _ _)
  | |- ensure_evars_instantiated_pure_goal [] [] =>
      exact I
  end.
Ltac solve_ensure_evars_instantiated ::=
  simpl;
  repeat solve_ensure_evars_instantiated_step.

(** Find inheritances *)
Ltac get_Σ :=
  let tgs := constr:(_ : typeGS _) in
  match type of tgs with
  | typeGS ?Σ => Σ
  end.
Ltac gather_inheritances env :=
  let Σ := get_Σ in
  match env with
  | Enil => constr:([] : list (list lft * iProp Σ))
  | Esnoc ?env' _ ?p =>
      let rs := gather_inheritances env' in
      lazymatch p with
      | (Inherit ?κs ?P)%I =>
          constr:((κs, P) :: rs)
      | _ => constr:(rs)
      end
  end.
Ltac solve_find_inheritances ::=
  match goal with
  | H := Envs ?Δi ?Δs _ |- find_inheritances_pure_goal ?ks =>
      let inheritances := gather_inheritances Δs in
      let inheritances := constr:(inheritances) in
      unify ks inheritances;
      unfold find_inheritances_pure_goal;
      done
  end.

(** Find spatial locs *)
Ltac gather_location_list env :=
  match env with
  | Enil => uconstr:([])
  | Esnoc ?env' _ ?p =>
      let rs := gather_location_list env' in
      lazymatch p with
      | (?l ◁ₗ[?π, Owned] ?r @ ?lty)%I =>
          uconstr:(l :: rs)
      | _ => uconstr:(rs)
      end
  end.
Ltac solve_find_spatial_locs ::=
  match goal with
  | H := Envs ?Δi ?Δs _ |- find_spatial_locs_pure_goal ?ks =>
      let locs := gather_location_list Δs in
      let locs := constr:(locs) in
      unify ks locs;
      unfold find_spatial_locs_pure_goal;
      done
  end.

(** Discover which local lifetimes are dying implied by another local lifetime dying (due to inclusion / aliases) *)
Ltac check_list_elem_of_lctx κ κs cont :=
  lazymatch κs with
  | [] =>
      cont constr:(false)
  | ?κ1 :: ?κs =>
      first [unify κ κ1; cont constr:(true) | check_list_elem_of_lctx κ κs cont ]
  end.
Ltac find_dying_lifetimes L κ cont :=
  match L with
  | [] => cont constr:([] : list lft)
  | (?κ1 ≡ₗ ?κs2) :: ?L =>
      find_dying_lifetimes L κ ltac:(fun dying =>
      once check_list_elem_of_lctx κ κs2 ltac:(fun el =>
        match el with
        | true =>
            cont constr:(κ1 :: dying)
        | false =>
            cont constr:(dying)
        end
      ))
  | (?κ1 ⊑ₗ{_} ?κs2) :: ?L =>
      find_dying_lifetimes L κ ltac:(fun dying =>
      once check_list_elem_of_lctx κ κs2 ltac:(fun el =>
        match el with
        | true =>
            cont constr:(κ1 :: dying)
        | false =>
            cont constr:(dying)
        end
      ))
  end.

Ltac solve_find_implied_dying_lifetimes ::=
  match goal with
  | |- find_implied_dying_lifetimes_pure_goal ?L ?κ ?ks =>
      find_dying_lifetimes L κ ltac:(fun res =>
      let res := constr:(res) in
      let res := eval simpl in res in
      unify ks res;
      unfold find_implied_dying_lifetimes_pure_goal; done)
  end.

(** [check_lft_is_local_pure_goal] *)
Ltac check_lft_is_local L κ cont :=
  match L with
  (* bottom out if we reach the function lifetime *)
  | [?ϝ ⊑ₗ{_} []] =>
    cont constr:(false)
  | (?κ' ⊑ₗ{_} ?κs') :: ?L' =>
    first [
      unify κ κ'; cont constr:(true)
    | check_lft_is_local L' κ cont]
  | (?κ' ≡ₗ ?κs') :: ?L' =>
      check_lft_is_local L' κ cont
  end.

Ltac solve_check_lft_is_local_goal ::=
  match goal with
  | |- check_lft_is_local_pure_goal _ ?L ?κ ?b =>
      check_lft_is_local L κ ltac:(fun res => unify b res; unfold check_lft_is_local_pure_goal; done)
  end.


(** Check if an element is contained in a list *)
Ltac solve_check_list_elem_of ::=
  match goal with
  | |- check_list_elem_of_pure_goal ?x ?xs ?b =>
      unfold check_list_elem_of_pure_goal;
      first [unify b true; simpl; solve [simple_list_elem_solver] | unify b false; simpl; exact I]
  end.

(** ** lifetime inclusion solver *)
(* Due to the structure of local inclusions (unique LHS), local inclusions are fairly easy to handle in the solver. *)
(* External inclusions are harder, as they are less structured.
   The goals are disjunctions in order to support backtracking on usage of external inclusions. *)
(* TODO: the solver relies equivalences between external lifetimes having been normalized.
  Actually implement this normalization. *)
Section incl_tac.
  Context `{typeGS Σ}.
  Definition lctx_lft_incl_list (E : elctx) (L : llctx) (κs1 κs2 : list lft) :=
    lctx_lft_incl E L (lft_intersect_list κs1) (lft_intersect_list κs2).

  Lemma tac_lctx_lft_incl_init_list E L κ1 κ2 :
    lctx_lft_incl_list E L [κ1] [κ2] ∨ False → lctx_lft_incl E L κ1 κ2.
  Proof.
    rewrite /lctx_lft_incl_list /=.
    rewrite !lft_intersect_right_id.
    intros [? | []]. done.
  Qed.

  Lemma tac_lctx_lft_incl_list_nil_r E L κs1 P :
    lctx_lft_incl_list E L κs1 [] ∨ P.
  Proof.
    rewrite /lctx_lft_incl_list /=.
    left.
    iIntros (?) "HL !> HE".
    iApply lft_incl_static.
  Qed.

  (* should be applied by automation only if κ2 cannot be decomposed further *)
  Lemma tac_lctx_lft_incl_list_intersect_l E L κ1 κ2 κs1 κs2 P :
    lctx_lft_incl_list E L (κ1 :: κ2 :: κs1) κs2 ∨ P →
    lctx_lft_incl_list E L (κ1 ⊓ κ2 :: κs1) κs2 ∨ P.
  Proof.
    rewrite /lctx_lft_incl_list /=.
    by rewrite lft_intersect_assoc.
  Qed.
  Lemma tac_lctx_lft_incl_list_intersect_r E L κ1 κ2 κs1 κs2 P :
    lctx_lft_incl_list E L κs1 (κ1 :: κ2 :: κs2) ∨ P →
    lctx_lft_incl_list E L κs1 (κ1 ⊓ κ2 :: κs2) ∨ P.
  Proof.
    rewrite /lctx_lft_incl_list /=.
    by rewrite lft_intersect_assoc.
  Qed.

  (* used for normalizing the head *)
  Lemma tac_lctx_lft_incl_list_head_assoc_l E L κ1 κ2 κ3 κs1 κs2 P :
    lctx_lft_incl_list E L ((κ1 ⊓ κ2) ⊓ κ3 :: κs1) κs2 ∨ P →
    lctx_lft_incl_list E L (κ1 ⊓ (κ2 ⊓ κ3) :: κs1) κs2 ∨ P.
  Proof. by rewrite lft_intersect_assoc. Qed.
  Lemma tac_lctx_lft_incl_list_head_assoc_r E L κ1 κ2 κ3 κs1 κs2 P :
    lctx_lft_incl_list E L κs1 ((κ1 ⊓ κ2) ⊓ κ3 :: κs2) ∨ P →
    lctx_lft_incl_list E L κs1 (κ1 ⊓ (κ2 ⊓ κ3) :: κs2) ∨ P.
  Proof. by rewrite lft_intersect_assoc. Qed.
  Lemma tac_lctx_lft_incl_list_head_static_l E L κ1 κs1 κs2 P :
    lctx_lft_incl_list E L (κ1 :: κs1) κs2 ∨ P →
    lctx_lft_incl_list E L (κ1 ⊓ static :: κs1) κs2 ∨ P.
  Proof. rewrite lft_intersect_right_id //. Qed.
  Lemma tac_lctx_lft_incl_list_head_static_r E L κ1 κs1 κs2 P :
    lctx_lft_incl_list E L κs1 (κ1 :: κs2) ∨ P →
    lctx_lft_incl_list E L κs1 (κ1 ⊓ static :: κs2) ∨ P.
  Proof. rewrite lft_intersect_right_id //. Qed.
  Lemma tac_lctx_lft_incl_list_static_l E L κs1 κs2 P :
    lctx_lft_incl_list E L κs1 κs2 ∨ P →
    lctx_lft_incl_list E L (static :: κs1) κs2 ∨ P.
  Proof. rewrite /lctx_lft_incl_list /= lft_intersect_left_id //. Qed.
  Lemma tac_lctx_lft_incl_list_static_r E L κs1 κs2 P :
    lctx_lft_incl_list E L κs1 κs2 ∨ P →
    lctx_lft_incl_list E L κs1 (static :: κs2) ∨ P.
  Proof. rewrite /lctx_lft_incl_list /= lft_intersect_left_id //. Qed.

  (* applied when a matching lifetime is found on left and right *)
  Lemma tac_lctx_lft_incl_list_dispatch_r E L i j κ κs1 κs2 P :
    κs1 !! i = Some κ →
    κs2 !! j = Some κ →
    lctx_lft_incl_list E L (κs1) (delete j κs2) ∨ P →
    lctx_lft_incl_list E L κs1 κs2 ∨ P.
  Proof.
    rewrite /lctx_lft_incl_list /=.
    rewrite !delete_take_drop.
    intros H1 H2.
    rewrite -{1 2}(take_drop_middle κs1 _ _ H1).
    rewrite -{3}(take_drop_middle κs2 _ _ H2).
    rewrite !lft_intersect_list_app. simpl.
    rewrite !lft_intersect_assoc.
    rewrite ![lft_intersect_list _ ⊓ κ]lft_intersect_comm.
    rewrite -!lft_intersect_assoc.
    intros Ha.
    destruct Ha as [ Ha | ?]; last by right. left.
    apply lctx_lft_incl_idemp_l.
    rewrite -lft_intersect_assoc.
    apply lctx_lft_incl_intersect; done.
  Qed.

  (* augment lhs with a local inclusion *)
  Lemma tac_lctx_lft_incl_list_augment_local_owned E L κs1 κs2 κ κs i j c P :
    L !! j = Some (κ ⊑ₗ{c} κs) →
    κs1 !! i = Some κ →
    lctx_lft_incl_list E L (κs ++ delete i κs1) κs2 ∨ P →
    lctx_lft_incl_list E L κs1 κs2 ∨ P.
  Proof.
    rewrite /lctx_lft_incl_list /=.
    rewrite !delete_take_drop.
    intros HL%list_elem_of_lookup_2 H1. rewrite -{3}(take_drop_middle κs1 _ _ H1).
    rewrite !lft_intersect_list_app. simpl. intros Ha.
    rewrite lft_intersect_assoc. rewrite [lft_intersect_list _ ⊓ κ]lft_intersect_comm.
    rewrite -lft_intersect_assoc.
    destruct Ha as [ Ha | ?]; last by right. left.
    eapply lctx_lft_incl_local_owned_full; done.
  Qed.

  Lemma tac_lctx_lft_incl_list_augment_local_alias E L κs1 κs2 κ κs i j P :
    L !! j = Some (κ ≡ₗ κs) →
    κs1 !! i = Some κ →
    lctx_lft_incl_list E L (κs ++ delete i κs1) κs2 ∨ P →
    lctx_lft_incl_list E L κs1 κs2 ∨ P.
  Proof.
    rewrite /lctx_lft_incl_list /=.
    rewrite !delete_take_drop.
    intros HL%list_elem_of_lookup_2 H1. rewrite -{3}(take_drop_middle κs1 _ _ H1).
    rewrite !lft_intersect_list_app. simpl. intros Ha.
    rewrite lft_intersect_assoc. rewrite [lft_intersect_list _ ⊓ κ]lft_intersect_comm.
    rewrite -lft_intersect_assoc.
    destruct Ha as [ Ha | ?]; last by right. left.
    eapply lctx_lft_incl_local_alias_full; done.
  Qed.

  (* For direct equivalences in the local context, just also rewrite on the RHS. *)
  Lemma tac_lctx_lft_incl_list_augment_local_alias_rhs E L κs1 κs2 κ κ' i j P :
    L !! j = Some (κ ≡ₗ [κ']) →
    κs2 !! i = Some κ →
    lctx_lft_incl_list E L (κs1) (κ' :: delete i κs2) ∨ P →
    lctx_lft_incl_list E L κs1 κs2 ∨ P.
  Proof.
    rewrite /lctx_lft_incl_list /=.
    rewrite !delete_take_drop.
    intros HL%list_elem_of_lookup_2 H1. rewrite -{3}(take_drop_middle κs2 _ _ H1).
    rewrite !lft_intersect_list_app. simpl. intros Ha.
    rewrite lft_intersect_assoc. rewrite [lft_intersect_list _ ⊓ κ]lft_intersect_comm.
    rewrite -lft_intersect_assoc.
    destruct Ha as [ Ha | ?]; last by right. left.
    etrans; first apply Ha.
    eapply lctx_lft_incl_intersect; last done.
    eapply lctx_lft_incl_local_alias_reverse; [done.. | ].
    simpl. rewrite right_id. done.
  Qed.

  (* WIP: better approach to handling symbolic lfts *)
  Lemma lctx_lft_incl_list_intersect_r E L κs1 κs2 κs P :
    lctx_lft_incl_list E L κs1 (κs2 ++ κs) ∨ P →
    lctx_lft_incl_list E L κs1 (lft_intersect_list κs :: κs2) ∨ P.
  Proof.
    rewrite /lctx_lft_incl_list/=.
    rewrite lft_intersect_list_app.
    rewrite lft_intersect_comm. done.
  Qed.
  Lemma lctx_lft_incl_list_intersect_l E L κs1 κs2 κs i P :
    κs1 !! i = Some (lft_intersect_list κs) →
    lctx_lft_incl_list E L (delete i κs1 ++ κs) κs2 ∨ P →
    lctx_lft_incl_list E L κs1 κs2 ∨ P.
  Proof.
    rewrite /lctx_lft_incl_list/=.
    rewrite !delete_take_drop.
    intros Hlook [Ha | ?]; last by right. left.
    rewrite -(take_drop_middle κs1 _ _ Hlook).
    move: Ha.
    rewrite !lft_intersect_list_app. simpl.
    rewrite [lft_intersect_list κs ⊓ lft_intersect_list (drop _ _)]lft_intersect_comm.
    rewrite lft_intersect_assoc.
    done.
  Qed.

  (* TODO this doesnt' work. we also have to remove it on the LHS. *)
  (* TODO: no, not true. see [lctx_lft_incl_idemp_l] *)
  Lemma lctx_lft_incl_list_ty_lfts_r E L κs1 κs2 {rt} (ty : type rt) P :
    ty_lfts ty ⊆ κs1 →
    lctx_lft_incl_list E L κs1 κs2 ∨ P →
    lctx_lft_incl_list E L κs1 (ty_lfts ty ++ κs2) ∨ P.
  Proof.
    rewrite /lctx_lft_incl_list/=.
    intros Hincl [Ha | ]; last by right. left.
    rewrite lft_intersect_list_app.

    (*Search lft_intersect.*)
    (*Search lctx_lft_incl.*)
    (*apply lctx_lft_incl_intersect_r.*)
  Abort.


  (*
  (* augment lhs with an external inclusion *)
  Lemma tac_lctx_lft_incl_list_augment_external E L κ1 κ2 κs1 κs2 i P :
    (κ1 ⊑ₑ κ2) ∈ E →
    κs1 !! i = Some κ1 →
    lctx_lft_incl_list E L (κ2 :: delete i κs1) κs2 ∨ P →
    lctx_lft_incl_list E L κs1 κs2 ∨ P.
  Proof.
    rewrite /lctx_lft_incl_list /=.
    rewrite !delete_take_drop.
    intros HE H1. rewrite -{3}(take_drop_middle κs1 _ _ H1).
    rewrite !lft_intersect_list_app. simpl. intros Ha.
    rewrite lft_intersect_assoc. rewrite [lft_intersect_list _ ⊓ κ1]lft_intersect_comm.
    rewrite -lft_intersect_assoc.
    destruct Ha as [ Ha | ?]; last by right. left.
    eapply lctx_lft_incl_external_full; done.
  Qed.
   *)
End incl_tac.

Section incl_external_tac.
  Context `{!typeGS Σ}.

  Definition lctx_lft_incl_list_expand_ext
    (candidates : list (lft * lft))
    (E : elctx) (L : llctx) (κs1 κs2 : list lft) : Prop :=
    lctx_lft_incl_list E L κs1 κs2.
  Arguments lctx_lft_incl_list_expand_ext : simpl never.

  (* Switch to reasoning about external inclusions *)
  Lemma tac_lctx_lft_incl_list_expand_ext_init E L candidates κs1 κs2 P :
    lctx_lft_incl_list_expand_ext candidates E L κs1 κs2 ∨ P →
    lctx_lft_incl_list E L κs1 κs2 ∨ P.
  Proof. done. Qed.

  (* Pick an expansion *)
  (* We also expand from the LHS, as we expand local lifetimes from the LHS.
     Expanding external lifetimes from the RHS would make some goals unprovable, e.g.
      [lctx_lft_incl [κ ⊑ₑ κ'] [κ' ⊑ₗ{ c1} [κ'']] κ κ'']
  *)
  Lemma tac_lctx_lft_incl_list_expand_ext_choose E L (e1 c1 : lft) candidates κs1 κs2 i P :
    (e1 ⊑ₑ c1) ∈ E →
    κs1 !! i = Some e1 →
    (lctx_lft_incl_list E L (c1 :: delete i κs1) κs2
      ∨ (lctx_lft_incl_list_expand_ext (candidates) E L κs1 κs2 ∨ P)) →
    lctx_lft_incl_list_expand_ext ((e1, c1) :: candidates) E L κs1 κs2 ∨ P.
  Proof.
    intros Hel Hlook [Ha | [Ha | Ha]]; [ | by eauto..].
    rewrite /lctx_lft_incl_list_expand_ext. left.
    revert Hlook Ha.
    rewrite /lctx_lft_incl_list /=.
    rewrite !delete_take_drop.
    intros Hlook.
    rewrite -{3}(take_drop_middle κs1 _ _ Hlook).
    rewrite !lft_intersect_list_app. simpl. intros Ha.
    rewrite lft_intersect_assoc.
    rewrite [lft_intersect_list _ ⊓ e1]lft_intersect_comm.
    rewrite -lft_intersect_assoc.
    eapply lctx_lft_incl_external_full; done.
  Qed.
  Lemma tac_lctx_lft_incl_list_expand_ext_skip E L (e1 c1 : lft) candidates κs1 κs2 P :
    lctx_lft_incl_list_expand_ext candidates E L κs1 κs2 ∨ P →
    lctx_lft_incl_list_expand_ext ((e1, c1) :: candidates) E L κs1 κs2 ∨ P.
  Proof. done. Qed.

  Lemma tac_lctx_lft_incl_list_expand_ext_done E L κs1 κs2 (P : Prop) :
    P →
    lctx_lft_incl_list_expand_ext [] E L κs1 κs2 ∨ P.
  Proof. by right. Qed.

  (* If we can't make progress on the left goal... *)
  Lemma tac_lctx_lft_incl_list_give_up E L κs1 κs2 (P : Prop) :
    P →
    lctx_lft_incl_list E L κs1 κs2 ∨ P.
  Proof.
    by right.
  Qed.
End incl_external_tac.

(* Find inclusions to use for expanding external lifetimes *)
Ltac elctx_find_expansions E :=
  match constr:(E) with
  | [] => constr:([] : list (lft * lft))
  | (?e ⊑ₑ ?c) :: ?E =>
      let candidates := (elctx_find_expansions E) in
      constr:((e, c) :: candidates)
  | ty_outlives_E _ _ ++ ?E =>
      elctx_find_expansions E
  | ty_wf_E _ ++ ?E =>
      elctx_find_expansions E
  | lfts_outlives_E _ _ ++ ?E =>
      elctx_find_expansions E
  | _ =>
      constr:([] : list (lft * lft))
  end.

(* Execute an ltac tactical [cont] for each element of a list [l].
  [cont] gets an element of the list as argument.
  Breaks if [cont] succeeds.
 *)
Ltac list_find_tac' cont l i :=
  match l with
  | [] => fail
  | ?h :: ?l => first [cont i h | list_find_tac' cont l constr:(S i)]
  end.
Ltac list_find_tac cont l := list_find_tac' cont l constr:(0).

Ltac list_find_tac_noindex cont l :=
  match l with
  | [] => fail
  | ?h :: ?l => first [cont h | list_find_tac_noindex cont l]
  | _ ++ ?l => list_find_tac_noindex cont l
  end.

(* Similar to [list_find_tac_noindex], but searches for a symbolic sublist used as an application. *)
Ltac list_find_tac_app cont l :=
  match l with
  | [] => fail
  | _ :: ?l => list_find_tac_app cont l
  | ?a ++ ?b =>
      first [cont a | list_find_tac_app cont a | list_find_tac_app cont b]
  | ?a => cont a
  end.


(* TODO: what about symbolic lifetimes like ty_lfts? *)

(** Basic algorithm: Want to eliminate the RHS to [], so that the inclusion to [static] holds trivially.
  For that, expand inclusions on the LHS, until we can eliminate one lifetime on the RHS *)
Ltac solve_lft_incl_list_step cont :=
  match goal with
  (* normalize the head if it is an intersection *)
  | |- lctx_lft_incl_list ?E ?L ((?κ1 ⊓ (?κ2 ⊓ ?κ3)) :: ?κs1) ?κs2 ∨ _ =>
      notypeclasses refine (tac_lctx_lft_incl_list_head_assoc_l E L _ _ _ κs1 κs2 _ _); cont
  | |- lctx_lft_incl_list ?E ?L ?κs1 ((?κ1 ⊓ (?κ2 ⊓ ?κ3)) :: ?κs2) ∨ _ =>
      notypeclasses refine (tac_lctx_lft_incl_list_head_assoc_r E L _ _ _ κs1 κs2 _ _); cont
  (* remove the atomic rhs static of an intersection *)
  | |- lctx_lft_incl_list ?E ?L (?κ1 ⊓ static :: ?κs1) ?κs2 ∨ _ =>
      notypeclasses refine (tac_lctx_lft_incl_list_head_static_l E L _ κs1 κs2 _ _); cont
  | |- lctx_lft_incl_list ?E ?L ?κs1 (?κ1 ⊓ static :: ?κs2) ∨ _ =>
      notypeclasses refine (tac_lctx_lft_incl_list_head_static_r E L _ κs1 κs2 _ _); cont
  (* shift the atomic rhs conjunct of an intersection *)
  | |- lctx_lft_incl_list ?E ?L (?κ1 ⊓ ?κ2 :: ?κs1) ?κs2 ∨ _ =>
      is_var κ2;
      notypeclasses refine (tac_lctx_lft_incl_list_intersect_l E L _ _ κs1 κs2 _ _); cont
  | |- lctx_lft_incl_list ?E ?L ?κs1 (?κ1 ⊓ ?κ2 :: ?κs2) ∨ _ =>
      is_var κ2;
      notypeclasses refine (tac_lctx_lft_incl_list_intersect_r E L _ _ κs1 κs2 _ _); cont
  (* eliminate static at the head *)
  | |- lctx_lft_incl_list ?E ?L (static :: ?κs1) ?κs2 ∨ _ =>
      notypeclasses refine (tac_lctx_lft_incl_list_static_l E L κs1 κs2 _ _); cont
  | |- lctx_lft_incl_list ?E ?L ?κs1 (static :: ?κs2) ∨ _ =>
      notypeclasses refine (tac_lctx_lft_incl_list_static_r E L κs1 κs2 _ _); cont
  (* goal is solved if RHS is empty *)
  | |- lctx_lft_incl_list ?E ?L ?κs1 [] ∨ _ =>
      notypeclasses refine (tac_lctx_lft_incl_list_nil_r E L κs1 _)

  (*| |- lctx_lft_incl_list ?E ?L ?κs1 (lft_intersect_list ?κs :: ?κs2) ∨ _ =>*)
      (*notypeclasses refine *)

  (* Normalize a direct local equivalence [κ ≡ₗ [κ']] on the RHS *)
  (* TODO this is a hack and doesn't work in all cases, because we don't use any other (external) inclusions on the RHS.
      Really, the proper way to do this would be to eliminate all such equivalences before starting the solver on a normalized goal + lifetime context. *)
  | |- lctx_lft_incl_list ?E ?L ?κs1 ?κs2 ∨ _ =>
      let find_in_llctx := fun j κ =>
        list_find_tac ltac:(fun i el =>
          match el with
          | κ ≡ₗ [?κ'] =>
              notypeclasses refine (tac_lctx_lft_incl_list_augment_local_alias_rhs E L κs1 κs2 κ κ' j i _ _ _ _);
              [ reflexivity | reflexivity | simpl; cont ]
          | _ => fail
          end
        ) L
      in
      list_find_tac find_in_llctx κs2

  (* eliminate a lifetime on the RHS that also occurs on the LHS *)
  | |- lctx_lft_incl_list ?E ?L ?κs1 ?κs2 ∨ _ =>
      let check_equality j κ2 := ltac:(fun i κ1 =>
        first [unify κ1 κ2;
          notypeclasses refine (tac_lctx_lft_incl_list_dispatch_r E L i j κ1 κs1 κs2 _ _ _ _);
            [reflexivity | reflexivity | simpl ]
        | fail ]
      ) in
      let check_rhs := ltac:(fun j κ2 => list_find_tac ltac:(check_equality j κ2) κs1) in
      list_find_tac check_rhs κs2

  (* Expand a local lifetime on the LHS *)
  | |- lctx_lft_incl_list ?E ?L ?κs1 ?κs2 ∨ _ =>
      let find_in_llctx := fun j κ =>
        list_find_tac ltac:(fun i el =>
          match el with
          | κ ⊑ₗ{_} ?κs =>
              (* only do this if the RHS is non-empty---otherwise, this cannot serve to make progress *)
              assert_fails (unify κs (@nil lft));
              notypeclasses refine (tac_lctx_lft_incl_list_augment_local_owned E L κs1 κs2 κ κs j i _ _ _ _ _);
              [ reflexivity | reflexivity | simpl; cont ]
          | κ ≡ₗ ?κs =>
              (* only do this if the RHS is non-empty---otherwise, this cannot serve to make progress *)
              assert_fails (unify κs (@nil lft));
              notypeclasses refine (tac_lctx_lft_incl_list_augment_local_alias E L κs1 κs2 κ κs j i _ _ _ _);
              [ reflexivity | reflexivity | simpl; cont ]
          | _ => fail
          end
        ) L
      in
      list_find_tac find_in_llctx κs1


  (* Expand an external lifetime on the LHS.
     We first find candidate inclusions to use. *)
  | |- lctx_lft_incl_list ?E ?L ?κs1 ?κs2 ∨ _ =>
      (* first make sure that there exists an inclusion we use, to make sure we can make progress *)
      let find_in_elctx := fun j κ =>
        list_find_tac_noindex ltac:(fun el =>
          match el with
          | κ ⊑ₑ ?κ' => idtac
          | _ => fail
          end
        ) E
      in
      list_find_tac find_in_elctx κs1;

      let expansions := elctx_find_expansions E in
      notypeclasses refine (tac_lctx_lft_incl_list_expand_ext_init E L expansions κs1 κs2 _ _);
      cont

  (* Otherwise, give up on this branch *)
  | |- lctx_lft_incl_list ?E ?L ?κs1 ?κs2 ∨ _ =>
      notypeclasses refine (tac_lctx_lft_incl_list_give_up _ _ _ _ _ _);
      cont

  (* Try a candidate for external lifetime expansion *)
  | |- lctx_lft_incl_list_expand_ext ((?e1, ?c1) :: ?cs) ?E ?L ?κs1 ?κs2 ∨ _ =>
       let find_e1 := fun j el =>
         match el with
         | e1 =>
            notypeclasses refine (tac_lctx_lft_incl_list_expand_ext_choose E L e1 c1 cs κs1 κs2 j _ _ _ _);
            [simple_list_elem_solver | reflexivity | simpl; cont]
         | _ => fail
         end
       in
       first [
        list_find_tac find_e1 κs1
      | notypeclasses refine (tac_lctx_lft_incl_list_expand_ext_skip E L e1 c1 cs κs1 κs2 _ _); cont
      ]

  (* The expansion candidates are exhausted *)
  | |- lctx_lft_incl_list_expand_ext [] ?E ?L ?κs1 ?κs2 ∨ _ =>
      notypeclasses refine (tac_lctx_lft_incl_list_expand_ext_done _ _ _ _ _ _);
      cont

  (* old rule *)
  (* expand an external lifetime on the LHS *)
  (* we cannot always make this expansion safely and may need backtracking (there might be multiple possible expansions);
      alternatively, think about representing the elctx similar to llctx (with unique LHS).
      [works, but would cause problems in the procedure for lctx_lft_alive below...]
    also, this might loop, since there can be cycles in the elctx. we need to keep track of that.
  *)
      (*
  | |- lctx_lft_incl_list ?E ?L ?κs1 ?κs2 ∨ _ =>
      let find_in_elctx := fun j κ =>
        list_find_tac_noindex ltac:(fun el =>
          match el with
          | κ ⊑ₑ ?κ' =>
              notypeclasses refine (tac_lctx_lft_incl_list_augment_external E L κ κ' κs1 κs2 j _ _ _ _);
              [ elctx_list_elem_solver | reflexivity | simpl; cont ]
          | _ => fail
          end
        ) E
      in
      list_find_tac find_in_elctx κs1
       *)
  end.

Ltac solve_lft_incl_list := repeat solve_lft_incl_list_step idtac.
Ltac solve_lft_incl_init :=
  match goal with
  | |- lctx_lft_incl ?E ?L ?κ1 ?κ2 =>
      unfold lft_intersect_list; simpl
  end;
  match goal with
  | |- lctx_lft_incl ?E ?L ?κ1 ?κ2 =>
      first [unify κ1 κ2; refine (lctx_lft_incl_refl E L κ1) |
            refine (tac_lctx_lft_incl_init_list E L κ1 κ2 _)
            ]
  end.
Ltac solve_lft_incl :=
  solve_lft_incl_init;
  solve_lft_incl_list.


Ltac solve_check_lctx_lft_incl_goal ::=
  match goal with
  | |- check_lctx_lft_incl_pure_goal ?E ?L ?κ1 ?κ2 ?b =>
      unfold check_lctx_lft_incl_pure_goal;
      first [
        unify b true; simpl;
        solve [solve_lft_incl]
      | unify b false;
        exact I]
  end.

(** lifetime alive solver *)
(*
  desired invariant:
  - every lifetime on the lhs of ⊑ₗ should be alive (because we should end lifetimes in a well-nested way, ending (and removing) shorter lifetimes first.
    -> if we can find a lifetime on the lhs in the local context, it should always be safe to apply [lctx_lft_alive_local] and reduce to smaller subgoals.
  - if a lifetime is external, it should be alive, because it outlives the local function lifetime, which should always be in the local context.
    -> if we can find a lifetime on the RHS of a ⊑ₑ, it should always be safe to apply [lctx_lft_alive_external]
  - for intersections, we should split to both sides. This should always be safe as the lifetime contexts should only contain atoms on the LHS.
 *)

Section alive_tac.
  Context `{typeGS Σ}.

  Definition lctx_lft_alive_list (E : elctx) (L : llctx) (κs : list lft) : Prop :=
    lctx_lft_alive E L (lft_intersect_list κs).
  Arguments lctx_lft_alive_list : simpl never.

  Lemma tac_lctx_lft_alive_init E L κ :
    lctx_lft_alive_list E L [κ] ∨ False →
    lctx_lft_alive E L κ.
  Proof.
    rewrite /lctx_lft_alive_list. simpl.
    by rewrite !right_id.
  Qed.
  Lemma tac_lctx_lft_alive_init_forall E L κs :
    lctx_lft_alive_list E L (κs ++ []) ∨ False →
    Forall (lctx_lft_alive E L) κs.
  Proof.
    rewrite /lctx_lft_alive_list. simpl.
    rewrite !right_id.
    apply lctx_lft_alive_intersect_list.
  Qed.

  Lemma tac_lctx_lft_alive_list_assoc E L κs1 κs2 κs3 P :
    lctx_lft_alive_list E L (κs1 ++ κs2 ++ κs3) ∨ P →
    lctx_lft_alive_list E L ((κs1 ++ κs2) ++ κs3) ∨ P.
  Proof.
    by rewrite app_assoc.
  Qed.
  Lemma tac_lctx_lft_alive_list_intersect_list E L κs κs' P :
    lctx_lft_alive_list E L (κs ++ κs') ∨ P →
    lctx_lft_alive_list E L (lft_intersect_list κs :: κs') ∨ P.
  Proof.
    rewrite /lctx_lft_alive_list/=.
    by rewrite -lft_intersect_list_app.
  Qed.

  Lemma tac_lctx_lft_alive_list_static E L κs P :
    lctx_lft_alive_list E L κs ∨ P →
    lctx_lft_alive_list E L (static :: κs) ∨ P.
  Proof.
    rewrite /lctx_lft_alive_list/=.
    rewrite left_id//.
  Qed.
  Lemma tac_lctx_lft_alive_list_nil E L P :
    lctx_lft_alive_list E L [] ∨ P.
  Proof.
    left.
    rewrite /lctx_lft_alive_list/=.
    apply lctx_lft_alive_static.
  Qed.

  Lemma tac_lctx_lft_alive_list_intersect E L κs κ κ' P :
    lctx_lft_alive_list E L (κ :: κ' :: κs) ∨ P →
    lctx_lft_alive_list E L ((κ ⊓ κ') :: κs) ∨ P.
  Proof.
    rewrite /lctx_lft_alive_list/=.
    intros [Ha | ?]; last by eauto. left.
    by rewrite -lft_intersect_assoc.
  Qed.

  Lemma tac_lctx_lft_alive_local_owned E L κ κs κs' i c P :
    L !! i = Some (κ ⊑ₗ{c} κs') →
    lctx_lft_alive_list E L (κs' ++ κs) ∨ P →
    lctx_lft_alive_list E L (κ :: κs) ∨ P.
  Proof.
    intros ?%list_elem_of_lookup_2.
    rewrite /lctx_lft_alive_list/=.
    rewrite lft_intersect_list_app.
    intros [Ha | ?]; last by eauto. left.
    apply lctx_lft_alive_intersect_2 in Ha as [Ha Hb].
    apply lctx_lft_alive_intersect; last done.
    eapply lctx_lft_alive_local_owned; first done.
    by apply lctx_lft_alive_intersect_list.
  Qed.

  Lemma tac_lctx_lft_alive_local_alias E L κ κs κs' i P :
    L !! i = Some (κ ≡ₗ κs') →
    lctx_lft_alive_list E L (κs' ++ κs) ∨ P →
    lctx_lft_alive_list E L (κ :: κs) ∨ P.
  Proof.
    intros ?%list_elem_of_lookup_2.
    rewrite /lctx_lft_alive_list/=.
    rewrite lft_intersect_list_app.
    intros [Ha | ?]; last by eauto. left.
    apply lctx_lft_alive_intersect_2 in Ha as [Ha Hb].
    apply lctx_lft_alive_intersect; last done.
    eapply lctx_lft_alive_local_alias; first done.
    by apply lctx_lft_alive_intersect_list.
  Qed.

  Lemma tac_lctx_lft_alive_list_ty_lfts {rt} (ty : type rt) E L i κ1 n1 κs P :
    ty_outlives_E ty κ1 ⊆ E →
    L !! i = Some (κ1 ⊑ₗ{n1} []) →
    lctx_lft_alive_list E L κs ∨ P →
    lctx_lft_alive_list E L (ty_lfts ty ++ κs) ∨ P.
  Proof.
    unfold ty_outlives_E.
    rewrite lfts_outlives_E_fmap /lfts_outlives_E.
    unfold subseteq, list_subseteq.
    rewrite /lctx_lft_alive_list/=.
    rewrite lft_intersect_list_app.
    generalize (ty_lfts ty); intros κs'.
    intros Hel Hlook.
    intros [Ha | ?]; last by eauto. left.

    apply lctx_lft_alive_intersect; last done.
    apply lctx_lft_alive_intersect_list.

    apply Forall_forall.
    intros κ Hκ.
    eapply (lctx_lft_alive_external _ _ κ1).
    { eapply Hel. apply list_elem_of_fmap. eauto. }
    eapply lctx_lft_alive_local_owned.
    { by eapply list_elem_of_lookup_2. }
    by apply Forall_nil.
  Qed.

  (*
  (* This weakens the elctx by removing the inclusion we used.
    This should ensure termination of the solver without making goals unprovable.
    (once we need to prove liveness of an external lifetime, the only local lifetime we should
      need is ϝ)
  *)
  Lemma tac_lctx_lft_alive_external E L κ κ' i :
    E !! i = Some (κ' ⊑ₑ κ) →
    lctx_lft_alive (delete i E) L κ' →
    lctx_lft_alive E L κ.
  Proof.
    intros ?%list_elem_of_lookup_2 H'.
    eapply lctx_lft_alive_external; first done.
    iIntros (F ??) "#HE HL".
    iApply H'; [ done | | done].
    iApply (big_sepL_submseteq with "HE").
    apply submseteq_delete.
  Qed.
  *)
  (* for this, I should again have a candidate list of expansions. But this time, I expand in the other direction. *)

End alive_tac.
Section alive_external_tac.
  Context `{!typeGS Σ}.

  Lemma tac_lctx_lft_alive_list_simpl_head_app E L κs1 κs1' κs2 P :
    (∀ (κs1'':=κs1'), κs1 = κs1'') →
    (lctx_lft_alive_list E L (κs1' ++ κs2) ∨ P) →
    lctx_lft_alive_list E L (κs1 ++ κs2) ∨ P.
  Proof.
    intros ->. done.
  Qed.

  Definition lctx_lft_alive_list_expand_ext
    (candidates : list lft)
    (E : elctx) (L : llctx) (κs : list lft) : Prop :=
    lctx_lft_alive_list E L κs.
  Arguments lctx_lft_alive_list_expand_ext : simpl never.

  (* Switch to reasoning about external inclusions *)
  Lemma tac_lctx_lft_alive_list_expand_ext_init E L candidates κs P :
    lctx_lft_alive_list_expand_ext candidates E L κs ∨ P →
    lctx_lft_alive_list E L κs ∨ P.
  Proof. done. Qed.

  (* Pick an expansion *)
  (* TODO maybe we can use the heuristic that, if there is a local lifetime to expand to, we only use that.
     That should suffice, since we anyways always have to go to a local lifetime to prove liveness. *)
  Lemma tac_lctx_lft_alive_list_expand_ext_choose E L (c1 : lft) candidates κ κs P :
    (c1 ⊑ₑ κ) ∈ E →
    (lctx_lft_alive_list E L (c1 :: κs)
      ∨ (lctx_lft_alive_list_expand_ext candidates E L (κ :: κs) ∨ P)) →
    lctx_lft_alive_list_expand_ext (c1 :: candidates) E L (κ :: κs) ∨ P.
  Proof.
    rewrite /lctx_lft_alive_list_expand_ext.
    rewrite /lctx_lft_alive_list /=.
    intros Hel [Ha | [Ha | Ha]]; [ | by eauto..].
    left.
    apply lctx_lft_alive_intersect_2 in Ha as [? ?].
    apply lctx_lft_alive_intersect; last done.
    by eapply lctx_lft_alive_external.
  Qed.

  Lemma tac_lctx_lft_alive_list_expand_ext_done E L κs (P : Prop) :
    P →
    lctx_lft_alive_list_expand_ext [] E L κs ∨ P.
  Proof. by right. Qed.

  (* If we can't make progress on the left goal... *)
  Lemma tac_lctx_lft_alive_list_give_up E L κs (P : Prop) :
    P →
    lctx_lft_alive_list E L κs ∨ P.
  Proof.
    by right.
  Qed.
End alive_external_tac.

Ltac solve_lft_alive_init :=
  simpl;
  match goal with
  | |- lctx_lft_alive ?E ?L ?κ =>
      notypeclasses refine (tac_lctx_lft_alive_init E L κ _)
  | |- Forall (lctx_lft_alive ?E ?L) ?κs =>
      notypeclasses refine (tac_lctx_lft_alive_init_forall E L κs _)
  end.

(* Find inclusions to use for expanding external lifetimes *)
Ltac elctx_find_expansions_for_rhs E κ :=
  match constr:(E) with
  | [] => constr:([] : list lft)
  | (?e ⊑ₑ κ) :: ?E =>
      let candidates := (elctx_find_expansions_for_rhs E κ) in
      constr:(e :: candidates)
  | (?e ⊑ₑ _) :: ?E =>
      elctx_find_expansions_for_rhs E κ
  | ty_outlives_E _ _ ++ ?E =>
      elctx_find_expansions_for_rhs E κ
  | ty_wf_E _ ++ ?E =>
      elctx_find_expansions_for_rhs E κ
  | lfts_outlives_E _ _ ++ ?E =>
      elctx_find_expansions_for_rhs E κ
  | _ =>
      constr:([] : list lft)
  end.

(** Specialized solver for proving list inclusions on normalized elctx.
  Treats lists as atomic parts. *)
Ltac elctx_fast_inclusion_solver_step :=
  match goal with
  | |- ?a ⊆ _ :: _ =>
      notypeclasses refine (list_subseteq_cons _ _ _ _)
  | |- ?a ⊆ ?a ++ _ =>
      notypeclasses refine (list_subseteq_app_l _ _ _ _);
      reflexivity
  | |- ?a ⊆ _ ++ _ =>
      notypeclasses refine (list_subseteq_app_r _ _ _ _)
  | |- ?a ⊆ ?a =>
      reflexivity
  end.
Ltac elctx_fast_inclusion_solver :=
  repeat elctx_fast_inclusion_solver_step.

Ltac solve_lft_alive := idtac.
Ltac solve_lft_alive_step :=
  simpl;
  match goal with
  (* done *)
  | |- lctx_lft_alive_list ?E ?L [] ∨ _ =>
      notypeclasses refine (tac_lctx_lft_alive_list_nil E L _)

  (* associativity *)
  | |- lctx_lft_alive_list ?E ?L ((_ ++ _) ++ _) ∨ _ =>
      notypeclasses refine (tac_lctx_lft_alive_list_assoc E L _ _ _ _ _)

  (* intersection *)
  | |- lctx_lft_alive_list ?E ?L ((lft_intersect_list ?κs) :: _) ∨ _ =>
      notypeclasses refine (tac_lctx_lft_alive_list_intersect_list E L κs _ _ _)
  (* split intersections *)
  | |- lctx_lft_alive_list ?E ?L ((?κ ⊓ ?κ') :: _) ∨ _ =>
      notypeclasses refine (tac_lctx_lft_alive_list_intersect E L _ κ κ' _ _)
  (* eliminate static *)
  | |- lctx_lft_alive_list ?E ?L (static :: _) ∨ _ =>
      notypeclasses refine (tac_lctx_lft_alive_list_static E L _ _ _)

  (* If we prove liveness of lifetimes of a type parameter,
     we search for a constraint that this lifetime outlives something *)
  | |- lctx_lft_alive_list ?E ?L (ty_lfts ?ty ++ _) ∨ _ =>
      is_var ty;
      let find_outlives al :=
        match al with
        | ty_outlives_E ty ?κ1 =>
            list_find_tac ltac:(fun i el =>
              match el with
              | κ1 ⊑ₗ{_} [] =>
                notypeclasses refine (tac_lctx_lft_alive_list_ty_lfts ty E L i κ1 _ _ _ _ _ _);
                [ elctx_fast_inclusion_solver | reflexivity | ]
              end) L
        | _ => fail
        end
      in
      list_find_tac_app find_outlives E
  (* If it is not a var, unfold *)
  | |- lctx_lft_alive_list ?E ?L (ty_lfts ?ty ++ _) ∨ _ =>
      notypeclasses refine (tac_lctx_lft_alive_list_simpl_head_app _ _ _ _ _ _ _ _);
      [let x := fresh in intros x; rewrite [(@ty_lfts _ _)]ty_lfts_unfold; simpl; subst x; reflexivity | ]
      (*unfold_opaque (@ty_lfts) in (ty_lfts ty); simpl*)

  (* liveness of local lifetimes *)
  | |- lctx_lft_alive_list ?E ?L (?κ :: ?κs) ∨ _ =>
      list_find_tac ltac:(fun i el =>
        match el with
        | κ ⊑ₗ{_} ?κs' =>
            notypeclasses refine (tac_lctx_lft_alive_local_owned E L κ κs _ i _ _ _ _);
              [ reflexivity | ]
        | κ ≡ₗ ?κs' =>
            notypeclasses refine (tac_lctx_lft_alive_local_alias E L κ κs _ i _ _ _);
              [ reflexivity | ]
        | _ => fail
        end) L

  (* Expand an external lifetime.
     We first find candidate inclusions to use. *)
  | |- lctx_lft_alive_list ?E ?L (?κ :: ?κs) ∨ _ =>
      (* first make sure that there exists an inclusion we use, to make sure we can make progress *)
      list_find_tac_noindex ltac:(fun el =>
        match el with
        | ?κ' ⊑ₑ ?κ => idtac
        | _ => fail
        end
      ) E;

      let expansions := elctx_find_expansions_for_rhs E κ in
      notypeclasses refine (tac_lctx_lft_alive_list_expand_ext_init E L expansions _ _ _)

  (* Otherwise, give up on this branch *)
  | |- lctx_lft_alive_list ?E ?L ?κs1 ∨ _ =>
      notypeclasses refine (tac_lctx_lft_alive_list_give_up E L _ _ _)

  (* Try a candidate for external lifetime expansion *)
  | |- lctx_lft_alive_list_expand_ext (?c1 :: ?cs) ?E ?L (?κ :: ?κs) ∨ _ =>
      notypeclasses refine (tac_lctx_lft_alive_list_expand_ext_choose E L c1 cs κ κs _ _ _);
      [simple_list_elem_solver | ]

  (* The expansion candidates are exhausted *)
  | |- lctx_lft_alive_list_expand_ext [] ?E ?L ?κs1 ∨ _ =>
      notypeclasses refine (tac_lctx_lft_alive_list_expand_ext_done E L _ _ _)

  (* old rule *)
  (*
  (* use external inclusions by rewriting right-to-left *)
  (* TODO this relies on internal backtracking, as we may have multiple choices, hence the recursive call *)
  | |- lctx_lft_alive ?E ?L ?κ =>
      list_find_tac ltac:(fun i el =>
        match el with
        | ?κ' ⊑ₑ κ =>
            notypeclasses refine (tac_lctx_lft_alive_external E L κ κ' i _ _);
            [reflexivity | simpl; solve_lft_alive ]
        | _ => fail
        end) E
        *)
  end.

Ltac solve_lft_alive ::=
  solve_lft_alive_init;
  repeat solve_lft_alive_step;
  fast_done.

(** simplify_elctx *)

Global Arguments ty_lfts : simpl never.
Global Arguments ty_wf_E : simpl never.
Global Arguments ty_outlives_E : simpl never.

(* Otherwise [simpl] will unfold too much despite [simpl never], breaking the solver *)
Global Opaque ty_outlives_E.
Global Opaque lfts_outlives_E.

Section tac.
  Context `{!typeGS Σ}.
  Lemma simplify_app_head_tac (E1 E1' E2 E : elctx) :
    E1 = E1' →
    E1' ++ E2 = E →
    E1 ++ E2 = E.
  Proof.
    intros <- <-. done.
  Qed.

  Lemma simplify_app_head_init_tac (E E' : elctx) :
    E ++ [] = E' →
    E = E'.
  Proof.
    rewrite app_nil_r. done.
  Qed.

  Lemma tac_lfts_outlives_E_cons κ1 κs2 κ E :
    lfts_outlives_E [κ1] κ ++ lfts_outlives_E κs2 κ = E →
    lfts_outlives_E (κ1 :: κs2) κ = E.
  Proof.
    rewrite !lfts_outlives_E_fmap fmap_cons//.
  Qed.
  Lemma tac_lfts_outlives_E_app κs1 κs2 κ E :
    lfts_outlives_E κs1 κ ++ lfts_outlives_E κs2 κ = E →
    lfts_outlives_E (κs1 ++ κs2) κ = E.
  Proof.
    rewrite !lfts_outlives_E_fmap fmap_app//.
  Qed.
  Lemma tac_lfts_outlives_E_nil κ :
    lfts_outlives_E [] κ = [].
  Proof. done. Qed.
  Lemma tac_lfts_outlives_E_singleton κ2 κ :
    lfts_outlives_E [κ2] κ = [κ ⊑ₑ κ2].
  Proof. done. Qed.
  (*Lemma ty_outlives_E_eq {rt} (ty : type rt) κ :*)
    (*ty_outlives_E ty κ = lfts_outlives_E (ty_lfts ty) κ.*)
  (*Proof.*)
    (*unfold_opaque @ty_outlives_E. done.*)
  (*Qed.*)

  Lemma tac_unfold_ty_wf_E {rt} (ty : type rt) E :
    _ty_wf_E _ ty = E →
    ty_wf_E ty = E.
  Proof. rewrite ty_wf_E_unfold. done. Qed.
  Lemma tac_unfold_ty_outlives_E {rt} (ty : type rt) κ E :
    lfts_outlives_E (ty_lfts ty) κ = E →
    ty_outlives_E ty κ = E.
  Proof. done. Qed.
  Lemma tac_lfts_outlives_E_unfold_ty {rt} (ty : type rt) κ E :
    lfts_outlives_E (_ty_lfts _ ty) κ = E →
    lfts_outlives_E (ty_lfts ty) κ = E.
  Proof. rewrite ty_lfts_unfold. done. Qed.

  Lemma tac_lfts_outlives_E_tyvar_fold {rt} (ty : type rt) κ E1 E2 :
    ty_outlives_E ty κ ++ E1 = E2 →
    lfts_outlives_E (ty_lfts ty) κ ++ E1 = E2.
  Proof. done. Qed.
  Lemma tac_lfts_outlives_E_app_nil κ E1 E2 :
    E1 = E2 →
    lfts_outlives_E [] κ ++ E1 = E2.
  Proof. done. Qed.

  Lemma tac_simplify_elctx_assoc (L1 L2 L3 E : elctx) :
    L1 ++ L2 ++ L3 = E →
    (L1 ++ L2) ++ L3 = E.
  Proof. rewrite app_assoc. done. Qed.
End tac.

Ltac ty_is_var ty :=
  lazymatch ty with
  | xtype_ty ?ty => is_var ty
  | _ => is_var ty
  end.
Ltac ty_is_not_var ty :=
  lazymatch ty with
  | xtype_ty ?ty => assert_fails (is_var ty)
  | _ => assert_fails (is_var ty)
  end.

(* TODO: eliminate rewrites and use tacs instead *)
Ltac simplify_elctx_subterm :=
  try match goal with
  | |- ty_outlives_E ?ty _ = _ =>
      ty_is_not_var ty;
      notypeclasses refine (tac_unfold_ty_outlives_E ty _ _ _)
  end;
  match goal with
  | |- ty_wf_E ?ty = _ =>
      ty_is_not_var ty;
      notypeclasses refine (tac_unfold_ty_wf_E ty _ _);
      rewrite [(_ty_wf_E _ ty)]/_ty_wf_E /=;
      simpl;
      reflexivity
  | |- lfts_outlives_E (ty_lfts ?ty) _ = _ =>
      first [ty_is_var ty |
          notypeclasses refine (tac_lfts_outlives_E_unfold_ty ty _ _ _);
          first [
            notypeclasses refine (tac_lfts_outlives_E_app _ _ _ _ _) |
            autounfold with tyunfold; rewrite /_ty_lfts ]
            ];
      simpl; reflexivity
  | |- lfts_outlives_E [?κ2] _ = _ =>
      notypeclasses refine (tac_lfts_outlives_E_singleton _ _)
  | |- lfts_outlives_E (?κs1 ++ ?κs2) _ = _ =>
      notypeclasses refine (tac_lfts_outlives_E_app _ _ _ _ _);
      simpl;
      reflexivity
  | |- lfts_outlives_E (?κ1 :: ?κs2) _ = _ =>
      notypeclasses refine (tac_lfts_outlives_E_cons _ _ _ _ _);
      simpl;
      reflexivity
  end.

Ltac simplify_elctx_step :=
simpl;
match goal with
| |- (_ ++ _) ++ _ = _ =>
    notypeclasses refine (tac_simplify_elctx_assoc _ _ _ _ _)
| |- ty_wf_E ?ty ++ _ = _ =>
    ty_is_not_var ty;
    notypeclasses refine (simplify_app_head_tac _ _ _ _ _ _);
    [ simplify_elctx_subterm | ]
| |- ty_wf_E ?ty ++ _ = _ =>
    ty_is_var ty; f_equiv
| |- ty_outlives_E ?ty _ ++ _ = _ =>
    ty_is_not_var ty;
    notypeclasses refine (simplify_app_head_tac _ _ _ _ _ _);
    [ simplify_elctx_subterm | ]
| |- ty_outlives_E ?ty _ ++ _ = _ =>
    ty_is_var ty; f_equiv
| |- lfts_outlives_E (ty_lfts ?T) ?κ ++ _ = _ =>
    ty_is_var T;
    (*fold (ty_outlives_E T κ);*)
    notypeclasses refine (tac_lfts_outlives_E_tyvar_fold T κ _ _ _);
    f_equiv
| |- lfts_outlives_E [] _ ++ _ = _ =>
    notypeclasses refine (tac_lfts_outlives_E_app_nil _ _ _ _)
| |- lfts_outlives_E ?κs _ ++ _ = _ =>
    assert_fails (is_var κs);
    refine (simplify_app_head_tac _ _ _ _ _ _);
    [ simplify_elctx_subterm | ]
| |- bor_kind_outlives_elctx _ _ ++ _ = _ =>
    (* TODO: more elaborate simplification? *)
    f_equiv
    (*refine (simplify_app_head_tac _ _ _ _ _ _);*)
    (*[ reflexivity | ]*)
| |- _ :: _ = _ =>
    f_equiv
| |- [] = _ =>
    reflexivity
end.

Ltac simplify_elctx :=
  match goal with
  | |- ?E = ?E' =>
    is_evar E';
    simpl;
    unfold typarams_elctx, typaram_elctx;
    simpl;
    refine (simplify_app_head_init_tac _ _ _);
    repeat simplify_elctx_step
  end.

(** Reordering an [elctx] so that all the opaque inclusions from generics are at the tail,
   while directly known inclusions appear at the head. This makes life easier for the lifetime solvers. *)
Section reorder_elctx.
  Context `{!typeGS Σ}.

  Lemma reorder_elctx_init_tac (E E0 E' E'' : elctx) :
    E ≡ₚ E' ++ E'' →
    E0 = E' ++ E'' →
    E ≡ₚ E0.
  Proof.
    intros -> ->. done.
  Qed.

  Lemma reorder_elctx_shuffle_left_tac E E' E1' E'' κ1 κ2 :
    E' = (κ1 ⊑ₑ κ2) :: E1' →
    E ≡ₚ E1' ++ E'' →
    (κ1 ⊑ₑ κ2) :: E ≡ₚ E' ++ E''.
  Proof.
    intros -> Hp. simpl. f_equiv. done.
  Qed.
  Lemma reorder_elctx_shuffle_left_app_tac (E E' E1' E'' E1 : elctx) :
    E' = E1 ++ E1' →
    E ≡ₚ E1' ++ E'' →
    E1 ++ E ≡ₚ E' ++ E''.
  Proof.
    intros -> Hp. simpl.
    rewrite -app_assoc.
    f_equiv. done.
  Qed.

  Lemma reorder_elctx_shuffle_right_tac (E E' E1'' E'' E0 : elctx) :
    E'' = E0 ++ E1'' →
    E ≡ₚ E' ++ E1'' →
    E0 ++ E ≡ₚ E' ++ E''.
  Proof.
    intros -> ->.
    rewrite [E0 ++ _]assoc [E0 ++ _]comm - [(E' ++ E0) ++ E1'']assoc.
    done.
  Qed.
End reorder_elctx.

(** The invariant is that we shuffle all the opaque parts into [E''],
  while the concrete parts get shuffled into [E']. *)
Ltac reorder_elctx_step :=
  match goal with
  | |- ?E ≡ₚ ?E' ++ ?E'' =>
      match E with
      | _ :: ?E =>
          notypeclasses refine (reorder_elctx_shuffle_left_tac E E' _ E'' _ _ _ _);
          [reflexivity | ]
      (* this should simplify later, so also put it left *)
      | bor_kind_outlives_elctx _ _ ++ _ =>
          notypeclasses refine (reorder_elctx_shuffle_left_app_tac E E' _ E'' (bor_kind_outlives_elctx _ _) _ _);
          [reflexivity | ]

      | ?E0 ++ ?E =>
          notypeclasses refine (reorder_elctx_shuffle_right_tac E E' _ E'' E0 _ _);
          [reflexivity | ]
      | [] => unify E' ([] : elctx); unify E'' ([] : elctx); reflexivity
      | ?E =>
          unify E' ([] : elctx); unify E'' (E); reflexivity
      end
  end.

Ltac reorder_elctx :=
  match goal with
  | |- ?E ≡ₚ ?E' =>
      is_evar E';
      refine (reorder_elctx_init_tac E E' _ _ _ _);
      [ solve [repeat reorder_elctx_step]
      | rewrite ?app_nil_r; reflexivity ]
  end.

(* TODO eliminate cyclic external inclusions *)

(** Optimize an elctx by removing unnecessary inclusions *)
Section optimize_elctx.
  Context `{!typeGS Σ}.

  Lemma tac_optimize_elctx_remove (E E' : elctx) κ κ' :
    E' ⊆+ E →
    E' ⊆+ (κ ⊑ₑ κ') :: E.
  Proof.
    intros ->. by apply submseteq_cons.
  Qed.
  Lemma tac_optimize_elctx_keep (E E' E'' : elctx) κ κ' :
    E' = (κ ⊑ₑ κ') :: E'' →
    E'' ⊆+ E →
    E' ⊆+ (κ ⊑ₑ κ') :: E.
  Proof.
    intros ->. by apply submseteq_skip.
  Qed.
  Lemma tac_optimize_elctx_finish (E E' : elctx) :
    E' = E →
    E' ⊆+ E.
  Proof. by intros ->. Qed.
End optimize_elctx.

Ltac optimize_elctx_step :=
  lazymatch goal with
  | |- ?E' ⊆+ (?κ ⊑ₑ ?κ) :: ?E =>
      notypeclasses refine (tac_optimize_elctx_remove _ _ _ _ _)
  | |- ?E' ⊆+ (?κ ⊑ₑ ?κ') :: ?E =>
      notypeclasses refine (tac_optimize_elctx_keep _ _ _ _ _ _ _);
      [ reflexivity | ]
  | |- ?E' ⊆+ _ =>
      notypeclasses refine (tac_optimize_elctx_finish _ _ _);
      reflexivity
  end.
Ltac optimize_elctx :=
  repeat optimize_elctx_step.

(** Combined elctx preprocessing *)
Lemma tac_preprocess_elctx (E1 E2 E E' : elctx) :
  E = E1 →
  E1 ≡ₚ E2 →
  E' ⊆+ E2 →
  E' ⊆+ E.
Proof.
  intros -> ->. done.
Qed.

Ltac preprocess_elctx :=
  match goal with
  | |- ?E' ⊆+ ?E =>
      notypeclasses refine (tac_preprocess_elctx _ _ _ _ _ _ _);
      [simplify_elctx | reorder_elctx | optimize_elctx]
  end.


(** elctx_sat solver *)
Section elctx_sat.
  Context `{typeGS Σ}.

  Lemma tac_elctx_sat_cons_r E E' L κ κ' i :
    E !! i = Some (κ ⊑ₑ κ') →
    elctx_sat E L (E') →
    elctx_sat E L ((κ ⊑ₑ κ') :: E').
  Proof.
    intros ?%list_elem_of_lookup_2 Hr.
    eapply (elctx_sat_app _ _ [_]); last done.
    eapply elctx_sat_submseteq.
    by apply singleton_submseteq_l.
  Qed.

  Lemma tac_elctx_sat_simpl E1 E2 L E1' E2' :
    (E1 = E1') →
    (E2 = E2') →
    elctx_sat E1' L E2' →
    elctx_sat E1 L E2.
  Proof.
    intros -> ->. done.
  Qed.

  Lemma tac_elctx_app_ty_wf_E E1 L {rt} (ty : type rt) :
    ty_wf_E ty ⊆+ E1 ∧ True →
    elctx_sat E1 L (ty_wf_E ty).
  Proof.
    intros [Hsub _] Hsat.
    apply elctx_sat_submseteq; done.
  Qed.

  Lemma tac_elctx_app_bor_kind_outlives_elctx E1 L k κ κ' :
    (* κ' is an evar that is shared between the two subgoals *)
    bor_kind_outlives_elctx k κ' ⊆+ E1 ∧ lctx_lft_incl E1 L κ κ' →
    elctx_sat E1 L (bor_kind_outlives_elctx k κ).
  Proof.
    intros [Houtl Hincl].
    eapply (elctx_sat_submseteq _ _ L) in Houtl.
    iIntros (qL) "HL".
    iPoseProof (Hincl with "HL") as "#Hincl".
    iPoseProof (Houtl with "HL") as "#Houtl".
    iModIntro. iIntros "#HE".
    iPoseProof ("Hincl" with "HE") as "Hincl'".
    iPoseProof ("Houtl" with "HE") as "Houtl'".
    iClear "Hincl Houtl HE".
    unfold_opaque @ty_outlives_E.
    unfold_opaque @lfts_outlives_E.
    rewrite /bor_kind_outlives_elctx.
    rewrite /elctx_interp/elctx_elt_interp.
    destruct k; simpl; first done; (iSplitL; last done);
      iDestruct "Houtl'" as "(Houtl' & _)".
    all: iApply lft_incl_trans; done.
  Qed.

  Lemma tac_elctx_app_ty_outlives_E E1 L κ κ' {rt} (ty : type rt) :
    (* κ' is an evar that is shared between the two subgoals *)
    ty_outlives_E ty κ' ⊆+ E1 ∧ lctx_lft_incl E1 L κ κ' →
    elctx_sat E1 L (ty_outlives_E ty κ).
  Proof.
    intros [Houtl Hincl].
    eapply (elctx_sat_submseteq _ _ L) in Houtl.
    iIntros (qL) "HL".
    iPoseProof (Hincl with "HL") as "#Hincl".
    iPoseProof (Houtl with "HL") as "#Houtl".
    iModIntro. iIntros "#HE".
    iPoseProof ("Hincl" with "HE") as "Hincl'".
    iPoseProof ("Houtl" with "HE") as "Houtl'".
    iClear "Hincl Houtl HE".
    unfold_opaque @ty_outlives_E.
    unfold_opaque @lfts_outlives_E.
    rewrite /ty_outlives_E /lfts_outlives_E.
    generalize (ty_lfts ty) => κs. clear.
    iInduction κs as [ | κ0 κs] "IH"; simpl; first done.
    rewrite /elctx_interp. simpl.
    iDestruct "Houtl'" as "(Ha & Houtl)".
    iPoseProof ("IH" with "Houtl") as "$".
    rewrite /elctx_elt_interp/=.
    iApply lft_incl_trans; done.
  Qed.

  Lemma tac_submseteq_skip_app_r {A} (K E0 E1 : list A) P :
    K ⊆+ E1 ∧ P →
    K ⊆+ (E0 ++ E1) ∧ P.
  Proof.
    intros [? ?]. split; last done.
    apply submseteq_app_r.
    exists [], K. split_and!; [done | | done].
    apply submseteq_nil_l.
  Qed.

  Lemma tac_submseteq_find_app_r {A} (K E0 E1 : list A) P :
    K = E0 ∧ P →
    K ⊆+ (E0 ++ E1) ∧ P.
  Proof.
    intros [-> ?]. split; last done.
    apply submseteq_app_r.
    eexists E0, []. rewrite app_nil_r.
    split_and!; [done.. | ]. apply submseteq_nil_l.
  Qed.

  Lemma tac_submseteq_cons {A} (K E : list A) x P :
    K ⊆+ E ∧ P →
    K ⊆+ (x :: E) ∧ P.
  Proof.
    intros [? ?]. split; last done.
    by apply submseteq_cons.
  Qed.

  Lemma tac_submseteq_assoc {A} (K E1 E2 E3 : list A) P :
    K ⊆+ E1 ++ E2 ++ E3 ∧ P →
    K ⊆+ (E1 ++ E2) ++ E3 ∧ P.
  Proof.
    by rewrite -app_assoc.
  Qed.

  Lemma tac_submseteq_init {A} (K E : list A) P :
    K ⊆+ E ++ [] ∧ P →
    K ⊆+ E ∧ P.
  Proof.
    rewrite app_nil_r//.
  Qed.
End elctx_sat.

(** Solve goals of the form [(_ ⊆+ _) ∧ _].
    Leaves the RHS unsolved.
  This tactic only operates on the left part of the goal, but if solving the inclusion on the left-hand side instantiates an evar,
   we can backtrack to the left side if the right side fails for this instantiation. *)
Ltac solve_elctx_submseteq_step :=
  simpl;
  multimatch goal with
  | |- (_ ⊆+ _ :: _) ∧ _ =>
      notypeclasses refine (tac_submseteq_cons _ _ _ _ _)
  | |- (_ ⊆+ (_ ++ _) ++ _) ∧ _ =>
      notypeclasses refine (tac_submseteq_assoc _ _ _ _ _ _)
  | |- (ty_outlives_E ?ty ?κ ⊆+ (ty_outlives_E ?ty' ?κ') ++ ?E) ∧ _ =>
      first [
        unify ty ty';
        notypeclasses refine (tac_submseteq_find_app_r _ _ _ _ _);
        split; [reflexivity | ]
      | notypeclasses refine (tac_submseteq_skip_app_r  _ _ _ _ _)
      ]
  | |- (ty_wf_E ?ty ⊆+ (ty_wf_E ?ty') ++ ?E) ∧ _ =>
      first [
        unify ty ty';
        notypeclasses refine (tac_submseteq_find_app_r _ _ _ _ _);
        split; [reflexivity | ]
      | notypeclasses refine (tac_submseteq_skip_app_r _ _ _ _ _)
      ]
  | |- (bor_kind_outlives_elctx ?k1 ?κ ⊆+ (bor_kind_outlives_elctx ?k2 ?κ') ++ ?E) ∧ _ =>
      first [
        unify k1 k2;
        notypeclasses refine (tac_submseteq_find_app_r _ _ _ _ _);
        split; [reflexivity | ]
      | notypeclasses refine (tac_submseteq_skip_app_r _ _ _ _ _)
      ]
  | |- (_ ⊆+ _ ++ _) ∧ _ =>
        notypeclasses refine (tac_submseteq_skip_app_r _ _ _ _ _)
  end.
Ltac solve_elctx_submseteq :=
  notypeclasses refine (tac_submseteq_init _ _ _ _);
  repeat solve_elctx_submseteq_step.

(** Solve goals of the shape [elctx_sat _ _ _] *)
Ltac solve_elctx_sat_step :=
  multimatch goal with
  | |- elctx_sat ?E ?L [] =>
      notypeclasses refine (elctx_sat_nil _ _)
  | |- elctx_sat ?E ?L ?E =>
      notypeclasses refine (elctx_sat_refl _ _)
  | |- elctx_sat ?E ?L (?E1 ++ ?E2) =>
      notypeclasses refine (elctx_sat_app E L E1 E2 _ _)
  (* dispatch as many elements as possible via direct inclusion *)
  | |- elctx_sat ?E ?L ((?κ ⊑ₑ ?κ') :: ?E') =>
      list_find_tac ltac:(fun i el =>
        match el with
        | (κ ⊑ₑ κ') =>
            notypeclasses refine (tac_elctx_sat_cons_r E L κ κ' i _ _);
            [reflexivity | ]
        | _ => fail
        end) E
  (* dispatch remaining elements via lifetime inclusion solving *)
  | |- elctx_sat ?E ?L ((?κ ⊑ₑ ?κ') :: ?E') =>
        notypeclasses refine (elctx_sat_lft_incl E L E' κ κ' _ _);
        [solve_lft_incl | ]
  (* dispatch assumptions for generic type parameters *)
  | |- elctx_sat ?E ?L (ty_wf_E ?ty) =>
      notypeclasses refine (tac_elctx_app_ty_wf_E E L ty _);
      solve_elctx_submseteq;
      done
  | |- elctx_sat ?E ?L (ty_outlives_E ?ty ?κ) =>
      notypeclasses refine (tac_elctx_app_ty_outlives_E E L κ _ ty _);
      solve_elctx_submseteq;
      solve[solve_lft_incl]
  (* assumption about parametric bor_kinds*)
  | |- elctx_sat ?E ?L (bor_kind_outlives_elctx ?k ?κ) =>
      notypeclasses refine (tac_elctx_app_bor_kind_outlives_elctx E L k κ _ _);
      solve_elctx_submseteq;
      solve[solve_lft_incl]
  end.

Ltac solve_elctx_sat_init :=
  (* first unfold stuff is commonly included in these conditions *)
  (*let esimpl := (unfold ty_outlives_E, tyl_outlives_E; simpl; notypeclasses refine eq_refl) in*)
  lazymatch goal with
  | |- elctx_sat ?E ?L ?E' =>
      notypeclasses refine (tac_elctx_sat_simpl _ _ _ _ _ _ _ _);
      [ simplify_elctx | simplify_elctx | ]
  end.
Ltac solve_elctx_sat :=
  solve_elctx_sat_init;
  repeat solve_elctx_sat_step
  .

(** lctx_bor_kind_alive solver *)
Section bor_kind_alive_tac.
  Context `{typeGS Σ}.

  Lemma tac_lctx_bor_kind_alive_simpl E L b b' :
    (∀ (b'':=b'), b = b'') →
    lctx_bor_kind_alive E L b' →
    lctx_bor_kind_alive E L b.
  Proof.
    intros ->. done.
  Qed.

  Lemma tac_lctx_bor_kind_alive_shared E L κ:
    lctx_lft_alive E L κ →
    lctx_bor_kind_alive E L (Shared κ).
  Proof. done. Qed.

  Lemma tac_lctx_bor_kind_alive_uniq E L κ γ :
    lctx_lft_alive E L κ →
    lctx_bor_kind_alive E L (Uniq κ γ).
  Proof. done. Qed.

  Lemma tac_lctx_bor_kind_alive_owned E L :
    lctx_bor_kind_alive E L (Owned).
  Proof. done. Qed.
End bor_kind_alive_tac.

Global Arguments lctx_bor_kind_alive : simpl never.
Ltac solve_bor_kind_alive :=
  (* first compute [bor_kind_min] *)
  let simp_min := let x := fresh in intros x; simpl; unfold x; notypeclasses refine eq_refl in
  match goal with
  | |- lctx_bor_kind_alive ?E ?L ?b =>
      refine (tac_lctx_bor_kind_alive_simpl _ _ _ _ _ _);
      [ simp_min
      | ]
  | |- _ =>
      fail 1000 "solve_bor_kind_alive: not an lctx_bor_kind_alive"
  end;
  match goal with
  | |- lctx_bor_kind_alive ?E ?L (Uniq _ _) =>
      refine (tac_lctx_bor_kind_alive_uniq _ _ _ _ _); [solve_lft_alive]
  | |- lctx_bor_kind_alive ?E ?L (Shared _) =>
      refine (tac_lctx_bor_kind_alive_shared _ _ _ _); [solve_lft_alive]
  | |- lctx_bor_kind_alive ?E ?L (Owned) =>
      refine (tac_lctx_bor_kind_alive_owned _ _); solve[fail]
  | |- lctx_bor_kind_alive _ _ _ =>
      fail 1000 "solve_bor_kind_alive: cannot determine bor_kind shape"
  end.
(** lctx_bor_kind_direct_incl solver *)
Section bor_kind_direct_incl_tac.
  Context `{typeGS Σ}.

  Lemma tac_lctx_bor_kind_direct_incl_simpl E L b1 b2 b1' b2' :
    (∀ (b1'':=b1'), b1 = b1'') →
    (∀ (b2'':=b2'), b2 = b2'') →
    lctx_bor_kind_direct_incl E L b1' b2' →
    lctx_bor_kind_direct_incl E L b1 b2.
  Proof.
    intros -> ->. done.
  Qed.

  Lemma tac_lctx_bor_kind_direct_incl_owned_owned E L :
    lctx_bor_kind_direct_incl E L (Owned) (Owned).
  Proof.
    iIntros (?) "HL !> HE". done.
  Qed.

  Lemma tac_lctx_bor_kind_direct_incl_uniq_uniq E L κ γ κ' :
    lctx_lft_incl E L κ κ' →
    lctx_bor_kind_direct_incl E L (Uniq κ γ) (Uniq κ' γ).
  Proof.
    iIntros (Hincl ?) "HL". iPoseProof (Hincl with "HL") as "#Hincl".
    iIntros "!> HE". iDestruct ("Hincl" with "HE") as "#Hincl'".
    iSplitR; done.
  Qed.

  Lemma tac_lctx_bor_kind_direct_incl_shared_shared E L κ κ' :
    lctx_lft_incl E L κ κ' →
    lctx_bor_kind_direct_incl E L (Shared κ) (Shared κ').
  Proof.
    iIntros (Hincl ?) "HL". iPoseProof (Hincl with "HL") as "#Hincl".
    iIntros "!> HE". iDestruct ("Hincl" with "HE") as "#Hincl'".
    done.
  Qed.
End bor_kind_direct_incl_tac.
Ltac solve_bor_kind_direct_incl :=
  try match goal with
  | |- lctx_bor_kind_direct_incl ?E ?L ?b1 ?b2 =>
      try (is_var b1; destruct b1);
      try (is_var b2; destruct b2)
  end;
  (* first compute [bor_kind_min] *)
  let simp_min := let x := fresh in intros x; simpl; unfold x; notypeclasses refine eq_refl in
  match goal with
  | |- lctx_bor_kind_direct_incl ?E ?L ?b1 ?b2 =>
      refine (tac_lctx_bor_kind_direct_incl_simpl _ _ _ _ _ _ _ _ _);
      [ simp_min
      | simp_min
      | ]
  | |- _ =>
      fail 1000 "solve_bor_kind_direct_incl: not an lctx_bor_kind_direct_incl"
  end;
  match goal with
  | |- lctx_bor_kind_direct_incl ?E ?L (Owned) (Owned) =>
      refine (tac_lctx_bor_kind_direct_incl_owned_owned _ _); solve[fail]
  | |- lctx_bor_kind_direct_incl ?E ?L (Uniq _ _) (Uniq _ _) =>
      refine (tac_lctx_bor_kind_direct_incl_uniq_uniq _ _ _ _ _ _); [solve_lft_incl]
  | |- lctx_bor_kind_direct_incl ?E ?L (Shared _) (Shared _) =>
      refine (tac_lctx_bor_kind_direct_incl_shared_shared _ _ _ _ _); [solve_lft_incl]
  | |- lctx_bor_kind_direct_incl ?E ?L ?b1 ?b2 =>
      fail 1000 "solve_bor_kind_direct_incl: unable to solve inclusion"
  end.

(** [lctx_lft_list_incl] solver *)
Section lft_list_incl.
  Context `{!typeGS Σ}.

  (* now process left to right *)
  Lemma tac_lctx_lft_list_incl_cons E L κ κs1 κs2 i κ' :
    κs2 !! i = Some κ' →
    lctx_lft_incl E L κ κ' →
    lctx_lft_list_incl E L κs1 κs2 →
    lctx_lft_list_incl E L (κ :: κs1) κs2.
  Proof.
    intros Hlook Hincl1 Hincl2.
    apply (lctx_lft_list_incl_app _ _ [_]); last done.
    eapply lctx_lft_list_incl_singleton_l; last done.
    by eapply list_elem_of_lookup_2.
  Qed.
  (* For this, we need to show inclusion of lists, where we interpret both sides as a join (i.e. max)
     In other words, for each lifetime on the left we have to find one on the right which lives longer.
  *)
End lft_list_incl.

Ltac solve_lft_list_incl_step cont :=
  lazymatch goal with
  | |- lctx_lft_list_incl ?E ?L [] _ =>
      notypeclasses refine (lctx_lft_list_incl_nil_l E L _)
  | |- lctx_lft_list_incl ?E ?L (?κ :: ?κs1) ?κs2 =>
        list_find_tac ltac:(fun i el =>
          notypeclasses refine (tac_lctx_lft_list_incl_cons E L κ κs1 κs2 i el _ _ _);
          [ reflexivity | solve_lft_incl | cont ]
        ) κs2
  end.
Ltac solve_lft_list_incl := repeat solve_lft_list_incl_step idtac.

(** ** [place_update_kind] solvers *)
Section place_update_kind_outlives.
  Context `{!typeGS Σ}.

  Lemma tac_lctx_place_update_kind_outlives_simpl E L b b' κs :
    (∀ (b'':=b'), b = b'') →
    lctx_place_update_kind_outlives E L b' κs →
    lctx_place_update_kind_outlives E L b κs.
  Proof.
    intros <-. done.
  Qed.

  Lemma tac_lctx_place_update_kind_outlives_strong E L κs :
    lctx_place_update_kind_outlives E L UpdStrong κs.
  Proof.
    iIntros (?) "HL HE". done.
  Qed.

  Lemma tac_lctx_place_update_kind_outlives_weak E L κs :
    lctx_place_update_kind_outlives E L UpdWeak κs.
  Proof.
    iIntros (?) "HL HE". done.
  Qed.

  Lemma tac_lctx_place_update_kind_outlives_uniq E L κs κs' :
    lctx_lft_list_incl E L κs' κs →
    lctx_place_update_kind_outlives E L (UpdUniq κs) κs'.
  Proof.
    iIntros (Hincl ?) "HL HE".
    iPoseProof (Hincl with "HL") as "#Ha".
    by iApply "Ha".
  Qed.
End place_update_kind_outlives.

Ltac solve_place_update_kind_outlives :=
  (* simplify first *)
  let simp_min := let x := fresh in intros x; unfold place_update_kind_restrict, place_update_kind_max, UpdBot; simpl; unfold x; notypeclasses refine eq_refl in
  match goal with
  | |- lctx_place_update_kind_outlives ?E ?L ?b ?κs =>
      refine (tac_lctx_place_update_kind_outlives_simpl _ _ _ _ _ _ _);
      [ simp_min
      | ]
  | |- _ =>
      fail 1000 "solve_place_update_kind_outlives: not an lctx_place_update_kind_outlives goal"
  end;
  lazymatch goal with
  | |- lctx_place_update_kind_outlives ?E ?L UpdStrong _ =>
      refine (tac_lctx_place_update_kind_outlives_strong E L _)
  | |- lctx_place_update_kind_outlives ?E ?L UpdWeak _ =>
      refine (tac_lctx_place_update_kind_outlives_weak E L _)
  | |- lctx_place_update_kind_outlives ?E ?L (UpdUniq ?κs) _ =>
      refine (tac_lctx_place_update_kind_outlives_uniq _ _ _ _ _);
      solve_lft_list_incl
  end.

(** [lctx_place_update_kind_incl] solver *)
(* this essentially reduces to solve_lft_incl *)
Section place_update_kind_incl_tac.
  Context `{typeGS Σ}.

  Lemma tac_lctx_place_update_kind_incl_simpl E L b1 b1' b2 b2' :
    (∀ (b1'':=b1'), b1 = b1'') →
    (∀ (b2'':=b2'), b2 = b2'') →
    lctx_place_update_kind_incl E L b1' b2' →
    lctx_place_update_kind_incl E L b1 b2.
  Proof.
    intros -> ->. done.
  Qed.

  Lemma tac_lctx_place_update_kind_incl_any_strong E L b :
    lctx_place_update_kind_incl E L b UpdStrong.
  Proof.
    iIntros (?) "HL !> HE". destruct b; done.
  Qed.

  Lemma tac_lctx_place_update_kind_incl_uniq_uniq E L κs κs' :
    lctx_lft_list_incl E L κs κs' →
    lctx_place_update_kind_incl E L (UpdUniq κs) (UpdUniq κs').
  Proof.
    iIntros (Hincl ?) "HL". iPoseProof (Hincl with "HL") as "#Hincl".
    iIntros "!> HE". iDestruct ("Hincl" with "HE") as "#Hincl'".
    done.
  Qed.

  Lemma tac_lctx_place_update_kind_incl_uniq_weak E L κs :
    lctx_place_update_kind_incl E L (UpdUniq κs) UpdWeak.
  Proof.
    iIntros (?) "HL". iIntros "!> HE". done.
  Qed.

  Lemma tac_lctx_place_update_kind_incl_weak_weak E L :
    lctx_place_update_kind_incl E L UpdWeak UpdWeak.
  Proof.
    iIntros (?) "HL". iIntros "!> HE". done.
  Qed.
End place_update_kind_incl_tac.

Ltac solve_place_update_kind_incl :=
  try match goal with
  | |- lctx_place_update_kind_incl ?E ?L ?b1 ?b2 =>
      try (is_var b1; destruct b1);
      try (is_var b2; destruct b2)
  end;
  (* first compute [place_update_kind_max] *)
  let simp_min := let x := fresh in intros x; unfold place_update_kind_restrict, place_update_kind_max, UpdBot; simpl; unfold x; notypeclasses refine eq_refl in
  match goal with
  | |- lctx_place_update_kind_incl ?E ?L ?b1 ?b2 =>
      refine (tac_lctx_place_update_kind_incl_simpl _ _ _ _ _ _ _ _ _);
      [ simp_min
      | simp_min
      | ]
  | |- _ =>
      fail 1000 "solve_place_update_kind_incl: not an lctx_place_update_kind_incl"
  end;
  match goal with
  | |- lctx_place_update_kind_incl ?E ?L _ UpdStrong =>
      refine (tac_lctx_place_update_kind_incl_any_strong _ _ _); solve[fail]
  | |- lctx_place_update_kind_incl ?E ?L (UpdUniq _) (UpdUniq _) =>
      refine (tac_lctx_place_update_kind_incl_uniq_uniq _ _ _ _ _); [solve_lft_list_incl]
  | |- lctx_place_update_kind_incl ?E ?L (UpdUniq _) UpdWeak =>
      refine (tac_lctx_place_update_kind_incl_uniq_weak _ _ _); solve[fail]
  | |- lctx_place_update_kind_incl ?E ?L UpdWeak UpdWeak =>
      refine (tac_lctx_place_update_kind_incl_weak_weak _ _); solve[fail]
  | |- lctx_place_update_kind_incl ?E ?L ?b1 ?b2 =>
      fail 1000 "solve_place_update_kind_incl: unable to solve inclusion"
  end.

(** [check_llctx_place_update_kind_incl] *)

Ltac solve_check_llctx_place_update_kind_incl_pure_goal ::=
  lazymatch goal with
  | |- check_llctx_place_update_kind_incl_pure_goal ?E ?L ?b1 ?b2 ?res =>
      first [
        assert (res = true) by reflexivity;
        simpl;
        solve_place_update_kind_incl
      | assert (res = false) by reflexivity;
        simpl;
        exact I ]
  end.

(* [check_llctx_place_update_kind_incl_uniq] *)

Ltac solve_check_llctx_place_update_kind_incl_uniq_pure_goal ::=
  lazymatch goal with
  | |- check_llctx_place_update_kind_incl_uniq_pure_goal ?E ?L ?b1 ?κs ?res =>
      first [
        assert (res = Some eq_refl) by reflexivity;
        simpl;
        solve_place_update_kind_incl
      | assert (res = None) by reflexivity;
        simpl;
        exact I ]
  end.

(** lctx_lft_alive_count *)
Section alive_tac.
  Context `{typeGS Σ}.

  Lemma tac_lctx_lft_alive_count_local_owned i c κs E L κ κs' κs'' L' L'' :
    lctx_lft_alive_count_iter E L κs κs' L' →
    L' !! i = Some (κ ⊑ₗ{c} κs) →
    κs'' = κ :: κs' →
    L'' = (<[i:=κ ⊑ₗ{ S c} κs]> L') →
    lctx_lft_alive_count E L κ κs'' L''.
  Proof.
    intros ? ? -> ->. by eapply lctx_lft_alive_count_local_owned.
  Qed.

  Lemma tac_lctx_lft_alive_count_local_alias i κs E L κ κs' L' :
    lctx_lft_alive_count_iter E L κs κs' L' →
    L !! i = Some (κ ≡ₗ κs) →
    lctx_lft_alive_count E L κ κs' L'.
  Proof.
    intros ? ?. eapply lctx_lft_alive_count_local_alias; last done.
    by eapply list_elem_of_lookup_2.
  Qed.

  Lemma tac_lctx_lft_alive_count_iter_cons E L κ κs κs1 κs2 κs3 L1 L2 :
    lctx_lft_alive_count E L κ κs1 L1 →
    lctx_lft_alive_count_iter E L1 κs κs2 L2 →
    κs3 = κs1 ++ κs2 →
    lctx_lft_alive_count_iter E L (κ :: κs) κs3 L2.
  Proof.
    intros ? ? ->. simpl. eexists _, _, _. done.
  Qed.
  Lemma tac_lctx_lft_alive_count_iter_nil E L :
    lctx_lft_alive_count_iter E L [] [] L.
  Proof. done. Qed.

  Lemma tac_lctx_lft_alive_count_intersect E L κ κ' κs1 κs2 κs3 L1 L2 :
    lctx_lft_alive_count E L κ κs1 L1 →
    lctx_lft_alive_count E L1 κ' κs2 L2 →
    κs3 = κs1 ++ κs2 →
    lctx_lft_alive_count E L (κ ⊓ κ') κs3 L2.
  Proof. intros ?? ->. by eapply lctx_lft_alive_count_intersect. Qed.

  (* This weakens the elctx by removing the inclusion we used.
    This should ensure termination of the solver without making goals unprovable.
    (once we need to prove liveness of an external lifetime, the only local lifetime we should
      need is ϝ)
  *)
  Lemma tac_lctx_lft_alive_count_external i E L κ κ' κs L' :
    E !! i = Some (κ' ⊑ₑ κ) →
    lctx_lft_alive_count (delete i E) L κ' κs L' →
    lctx_lft_alive_count E L κ κs L'.
  Proof.
    intros ?%list_elem_of_lookup_2 H'.
    eapply lctx_lft_alive_count_external; first done.
    iIntros (F ?) "#HE HL".
    iApply H'; [ done | | done].
    iApply (big_sepL_submseteq with "HE").
    apply submseteq_delete.
  Qed.

End alive_tac.

(* redefined below *)
Ltac solve_lft_alive_count_iter :=
  idtac.

Ltac solve_lft_alive_count ::=
  repeat match goal with
  | |- lctx_lft_alive_count ?E ?L static _ _ =>
      notypeclasses refine (lctx_lft_alive_count_static E L)
  | |- lctx_lft_alive_count ?E ?L (?κ ⊓ ?κ') _ _ =>
      notypeclasses refine (tac_lctx_lft_alive_count_intersect E L κ κ' _ _ _ _ _ _ _ _);
        [solve_lft_alive_count | solve_lft_alive_count | simpl; reflexivity ]
  (* local inclusion *)
  | |- lctx_lft_alive_count ?E ?L ?κ _ _ =>
      (** Here, the solver relies on the fact that the indices of lifetimes should not change when increasing the counts. *)
      list_find_tac ltac:(fun i el =>
        match el with
        | κ ⊑ₗ{?c} ?κs =>
            notypeclasses refine (tac_lctx_lft_alive_count_local_owned i c κs E L κ _ _ _ _ _ _ _ _);
              [ solve_lft_alive_count_iter
              | simpl; reflexivity
              | simpl; reflexivity
              | simpl; reflexivity ]
        | κ ≡ₗ?κs =>
            notypeclasses refine (tac_lctx_lft_alive_count_local_alias i κs E L κ _ _ _ _);
              [ solve_lft_alive_count_iter
              | simpl; reflexivity ]
        | _ => fail
        end) L
  (* external inclusion *)
  | |- lctx_lft_alive_count ?E ?L ?κ _ _ =>
      list_find_tac ltac:(fun i el =>
        match el with
        | ?κ' ⊑ₑ κ =>
            notypeclasses refine (tac_lctx_lft_alive_count_external i E L κ κ' _ _ _ _);
            [reflexivity | simpl; solve[solve_lft_alive_count]]
        | _ => fail
        end) E
  end; fast_done.

Ltac solve_lft_alive_count_iter ::=
  match goal with
  | |- lctx_lft_alive_count_iter ?E ?L [] _ _ =>
    notypeclasses refine (tac_lctx_lft_alive_count_iter_nil E L)
  | |- lctx_lft_alive_count_iter ?E ?L (?κ :: ?κs) _ _ =>
      notypeclasses refine (tac_lctx_lft_alive_count_iter_cons E L κ κs _ _ _ _ _ _ _ _);
      [ solve_lft_alive_count
      | solve_lft_alive_count_iter
      | simpl; reflexivity ]
  end.

Section return_tac.
  Context `{!invGS Σ, !lctxGS Σ, !lftGS Σ lft_userE}.

  Lemma tac_llctx_release_toks_nil L :
    llctx_release_toks L [] L.
  Proof. done. Qed.

  Lemma tac_llctx_release_toks_cons i c κs' L κ κs L1 L2 :
    L !! i = Some (κ ⊑ₗ{c} κs') →
    L1 = <[i := κ ⊑ₗ{pred c} κs']> L →
    llctx_release_toks L1 κs L2 →
    llctx_release_toks L (κ :: κs) L2.
  Proof.
    intros ? -> ?. simpl. left. eexists _, _, _. done.
  Qed.

  Lemma tac_llctx_release_toks_cons_skips κ κs L1 L2 :
    llctx_release_toks L1 κs L2 →
    llctx_release_toks L1 (κ :: κs) L2.
  Proof.
    intros ?. simpl. right. done.
  Qed.
End return_tac.

Ltac solve_llctx_release_toks ::=
  match goal with
  | |- llctx_release_toks ?L [] _ =>
      notypeclasses refine (tac_llctx_release_toks_nil L)
  | |- llctx_release_toks ?L (?κ :: ?κs) _ =>
      first [list_find_tac ltac:(fun i el =>
        match el with
        | κ ⊑ₗ{?c} ?κs' =>
            notypeclasses refine (tac_llctx_release_toks_cons i c κs' L κ κs _ _ _ _ _);
              [ simpl; reflexivity
              | simpl; reflexivity
              | solve_llctx_release_toks ]
        | _ => fail
        end) L
      | notypeclasses refine (tac_llctx_release_toks_cons_skips κ κs _ _ _);
        solve_llctx_release_toks ]
  end.


(** llctx_find_llft *)
Section llctx_lft_split.
  Lemma tac_llctx_find_llft_solve_step_skip L L' κ κ' κs κs' oc key :
    llctx_find_llft L κ' key κs' L' →
    llctx_find_llft ((oc, κ, κs) :: L) κ' key κs' ((oc, κ, κs) :: L').
  Proof.
    intros (A & B & ? & -> & -> & ?).
    eexists ((oc, κ, κs) :: A), B, _. done.
  Qed.

  Lemma tac_llctx_find_llft_solve_step_find L κ κs κs' key oc :
    llctx_find_lft_key_interp key κ oc →
    κs' = κs →
    llctx_find_llft ((oc, κ, κs) :: L) κ key κs' L.
  Proof.
    intros ? ->.
    eexists [], L, _. split; first done. done.
  Qed.
End llctx_lft_split.

Ltac solve_llctx_find_llft ::=
  repeat match goal with
  | |- llctx_find_llft ((?oc, ?κ, ?κs) :: ?L) ?κ ?key ?κs' ?L' =>
      (notypeclasses refine (tac_llctx_find_llft_solve_step_find L κ κs κs' key oc _ _);
      [first [done | eexists _; done] | done]) || fail 1000 "llctx_find_llft_solver: cannot find lifetime " κ " because there are still " oc " open tokens"
  | |- llctx_find_llft ((?oc, ?κ, ?κs) :: ?L) ?κ' ?key ?κs' ?L' =>
      refine (tac_llctx_find_llft_solve_step_skip L _ κ κ' κs κs' oc key _)
  end.

(** llctx_remove_dead_aliases *)
Ltac solve_llctx_remove_dead_aliases_step κ :=
  lazymatch goal with
  | |- sublist _ ((?κ' ≡ₗ ?κs) :: ?L) =>
      first [
        (* discard *)
        list_find_tac_noindex ltac:(fun κ2 => unify κ κ2) κs;
        notypeclasses refine (sublist_cons _ _ _ _)
      | notypeclasses refine (sublist_skip _ _ _ _) ]
  | |- sublist _ (_ :: ?L) =>
      notypeclasses refine (sublist_skip _ _ _ _)
  | |- sublist _ [] =>
      notypeclasses refine (sublist_nil)
  end.
Ltac solve_llctx_remove_dead_aliases ::=
  lazymatch goal with
  | |- llctx_remove_dead_aliases ?L1 ?L2 ?κ =>
    unfold llctx_remove_dead_aliases;
    repeat solve_llctx_remove_dead_aliases_step κ
  end.

(** solve_map_lookup *)
(* this extends the Lithium solver with support for goals where the lookup is None *)
Ltac compute_map_lookup_unchecked :=
  unfold_opaque @named_lft_delete;
  unfold_opaque @named_lft_update;
  lazymatch goal with
  | |- ?Q !! _ = Some _ => try (is_var Q; unfold Q)
  | |- ?Q !! _ = ?e => idtac
  | _ => fail "unknown goal for compute_map_lookup"
  end; (solve
   [ repeat
      lazymatch goal with
      | |- <[?x:=?s]> ?Q !! ?y = ?res =>
            lazymatch x with
            | y => change_no_check (Some s = res); reflexivity
            | _ => change_no_check (Q !! y = res)
            end
      | |- ∅ !! _ = ?res =>
         change_no_check (None = res); reflexivity
      end ]).
Ltac compute_map_lookup_checked :=
  unfold_opaque @named_lft_delete;
  unfold_opaque @named_lft_update;
  lazymatch goal with
  | |- ?Q !! _ = Some _ => try (is_var Q; unfold Q)
  | |- ?Q !! _ = ?e => idtac
  | _ => fail "unknown goal for compute_map_lookup"
  end; (solve
   [ repeat
      lazymatch goal with
      | |- <[?x:=?s]> ?Q !! ?y = ?res =>
            lazymatch x with
            | y => change (Some s = res); reflexivity
            | _ => change (Q !! y = res)
            end
      | |- ∅ !! _ = ?res =>
         change (None = res); reflexivity
      end ]).
Ltac solve_compute_map_lookup unchecked ::=
  match unchecked with
  | true => compute_map_lookup_unchecked
  | false => compute_map_lookup_checked
  end.
Ltac solve_compute_map_lookup_nofail ::=
  compute_map_lookup_unchecked.

Lemma compute_map_lookups_cons_tac (M : gmap string lft) (ns : list string) (n : string) (κs κs' : list lft) κ :
  M !! n = Some κ →
  Forall2 (λ x y, M !! x = Some y) ns κs' →
  κs = κ :: κs' →
  Forall2 (λ x y, M !! x = Some y) (n :: ns) κs.
Proof.
  intros Hlook Hall ->.
  econstructor; done.
Qed.

Ltac compute_map_lookups :=
  lazymatch goal with
  | |- Forall2 _ [] ?out =>
        unify out (@nil lft); by apply (Forall2_nil)
  | |- Forall2 _ (?x :: ?xs) ?out =>
      refine (compute_map_lookups_cons_tac _ xs x _ _ _ _ _ _);
      [ compute_map_lookup_unchecked | compute_map_lookups | reflexivity]
  end.
Ltac solve_compute_map_lookups_nofail ::=
  compute_map_lookups.

(** local_fresh *)
Section tac.
  Lemma tac_local_fresh_nil x :
    local_fresh x [].
  Proof.
    unfold local_fresh. set_solver.
  Qed.
  Lemma tac_local_fresh_cons x y ys :
    x ≠ y →
    local_fresh x ys →
    local_fresh x (y :: ys).
  Proof.
    unfold local_fresh. set_solver.
  Qed.

End tac.
Ltac solve_local_fresh :=
  repeat match goal with
  | |- local_fresh ?x [] =>
      notypeclasses refine (tac_local_fresh_nil _)
  | |- local_fresh ?x (?y :: ?ys) =>
      notypeclasses refine (tac_local_fresh_cons _ _ _ _ _);
      [done | ]
  end.

(** solve_simplify_map *)

Section simplify_gmap.
  Context `{!typeGS Σ}.

  Lemma simplify_gmap_tac `{Countable K} {V} (M M' E : gmap K V) :
    map_to_list M' = map_to_list M →
    M' = E →
    M = E.
  Proof.
    intros Heq <-.
    eapply map_to_list_inj. rewrite Heq. done.
  Qed.

  Lemma simplify_lft_map_tac `{Countable K} {V} (M M' E : gmap K V) :
    E = M' →
    opaque_eq M E.
  Proof.
    Local Transparent opaque_eq.
    rewrite /opaque_eq. done.
  Qed.
End simplify_gmap.

(* keeps the invariant that the term contains no deletes *)
Ltac simplify_gmap M :=
  lazymatch M with
  (* push down deletes *)
  | delete ?x (<[?y := ?s]> ?Q) =>
      lazymatch x with
      | y =>
          simplify_gmap constr:(Q)
      | _ =>
          let M' := simplify_gmap constr:(delete x Q) in
          uconstr:(<[y := s]> M')
      end
  (* skip over inserts without deletes *)
  | <[?y := ?s]> ?Q =>
      let M' := simplify_gmap constr:(Q) in
      uconstr:(<[y := s]> M')
  (* remove a delete from an empty map *)
  | delete _ ∅ =>
      uconstr:(∅)
  | _ =>
      constr:(M)
  end.
Ltac solve_simplify_gmap ::=
  match goal with
  | |- ?Q = ?e => try (is_var Q; unfold Q); is_evar e
  | |- ?e = ?Q => try (is_var Q; unfold Q); is_evar e; symmetry
  | _ => fail "unknown goal for simplify_gmap"
  end;
  lazymatch goal with
  | |- ?Q = ?e =>
      let Q' := simplify_gmap constr:(Q) in
      (* NOTE: this relies on the simplification being order-preserving *)
      refine (simplify_gmap_tac Q Q' e _ _);
      [abstract (vm_compute; reflexivity) | reflexivity ]
  end.

Ltac simplify_lft_map M :=
  lazymatch M with
  (* push down deletes *)
  | named_lft_delete ?x (named_lft_update ?y ?s ?Q) =>
      lazymatch x with
      | y =>
          simplify_lft_map constr:(Q)
      | _ =>
          let M' := simplify_lft_map constr:(named_lft_delete x Q) in
          uconstr:(named_lft_update y s M')
      end
  (* skip over inserts without deletes *)
  | named_lft_update ?y ?s ?Q =>
      let M' := simplify_lft_map constr:(Q) in
      uconstr:(named_lft_update y s M')
  (* remove a delete from an empty map *)
  | named_lft_delete _ ∅ =>
      uconstr:(∅)
  | _ =>
      constr:(M)
  end.
Ltac solve_simplify_lft_map ::=
  match goal with
  | |- opaque_eq ?Q ?e => try (is_var Q; unfold Q); is_evar e
  | |- opaque_eq ?e ?Q => try (is_var Q; unfold Q); is_evar e; change_no_check (opaque_eq Q e)
      (*symmetry*)
  | _ => fail "unknown goal for simplify_lft_map"
  end;
  lazymatch goal with
  | |- opaque_eq ?Q ?e =>
      let Q' := simplify_lft_map constr:(Q) in
      refine (simplify_lft_map_tac Q Q' e _);
      [reflexivity ]
  end.

(** Simplifying local lists *)
Section tac.
  Lemma tac_simplify_remove_local_cons_ne M x y xs :
    x ≠ y →
    remove_local xs y = M →
    remove_local (x :: xs) y = (x :: M).
  Proof.
    unfold remove_local.
    intros Hneq. simpl.
    rewrite decide_False; first naive_solver.
    set_solver.
  Qed.
  Lemma tac_simplify_remove_local_cons_eq M x xs :
    remove_local xs x = M →
    remove_local (x :: xs) x = M.
  Proof.
    unfold remove_local.
    intros Hneq. simpl.
    rewrite decide_True; first naive_solver.
    set_solver.
  Qed.
  Lemma tac_simplify_remove_local_nil x :
    remove_local [] x = [].
  Proof.
    unfold remove_local. done.
  Qed.
End tac.

Ltac simplify_local_list_step :=
  lazymatch goal with
  | |- remove_local (?x :: ?xs) ?x = ?m =>
    notypeclasses refine (tac_simplify_remove_local_cons_eq _ _ _ _)
  | |- remove_local (?x :: ?xs) ?y = ?m =>
    notypeclasses refine (tac_simplify_remove_local_cons_ne _ _ _ _ _ _);
    [done | ]
  | |- remove_local [] ?y = ?m =>
    notypeclasses refine (tac_simplify_remove_local_nil _)
  end.
Ltac solve_simplify_local_list ::=
  match goal with
  | |- ?Q = ?e => is_evar e
  | _ => fail "unknown goal for simplify_local_list"
  end;
  lazymatch goal with
  | |- ?Q = ?e =>
      repeat simplify_local_list_step
  end.

(** ** Solver for goals of the form [ty_has_op_type] *)
Section tac.
  Context `{!typeGS Σ}.

  Lemma ty_has_op_type_simplify_tac {rt} (ty : type rt) ot ot2 mt :
    ot = ot2 →
    ty_has_op_type ty ot2 mt →
    ty_has_op_type ty ot mt.
  Proof. intros ->; done. Qed.
End tac.

Ltac simplify_ot :=
  simpl;
  unfold ty_sized_syn_type;
  match goal with
  | |- (use_op_alg' ?st) = ?ot =>
      solve_op_alg
  | |- ?ot = use_op_alg' ?st =>
      symmetry; solve_op_alg
  | |- _ => reflexivity
  end.
Arguments is_value_ot : simpl never.
Arguments is_array_ot : simpl never.
Arguments is_struct_ot : simpl never.
Ltac solve_ty_has_op_type_core_step :=
  first
  [ match goal with
    | |- ∃ _, _ => eexists
    end
  | split_and !; simpl
  | done ];
  first [
  solve[fail]
  | sidecond_hook
  | shelve ].
Ltac solve_ty_has_op_type_core :=
  repeat solve_ty_has_op_type_core_step.

Ltac solve_ty_has_op_type_prepare :=
  (* simplify op_type *)
  lazymatch goal with
  | |- ty_has_op_type ?ty ?ot ?mc =>
        refine (ty_has_op_type_simplify_tac ty ot _ mc _ _);
         [ simplify_ot |  ]
  end;
  (* unfold *)
  repeat lazymatch goal with
  | |- ty_has_op_type ?ty ?ot ?mc =>
      first [ assert_fails (is_var ty); rewrite ty_has_op_type_unfold/_ty_has_op_type/= | idtac]
  end;
  (* specific handling for a few cases *)
  lazymatch goal with
  | |- is_value_ot ?st (use_op_alg' ?st) ?mc =>
        refine (is_value_ot_use_op_alg _ _ _ _ _);
        [ done | solve_layout_alg ]
  | |- is_value_ot _ _ _ => rewrite /is_value_ot; eexists _
  | |- _ =>
      (*otherwise unfold *)
      hnf
  end.
Ltac solve_ty_has_op_type :=
  solve_ty_has_op_type_prepare;
  solve_ty_has_op_type_core.

(** Solver for goals of the form [ty_allows_reads ?ty] and [ty_allows_writes ?ty] *)
Ltac solve_ty_allows :=
  lazymatch goal with
  | |- ty_allows_reads ?ty =>
      unfold ty_allows_reads
  | |- ty_allows_writes ?ty =>
      unfold ty_allows_writes
  end;
  solve_ty_has_op_type.


(** ** Augment the context with commonly needed facts. *)
Section augment.
  Lemma bytes_per_addr_eq :
    bytes_per_addr = 8%nat.
  Proof. done. Qed.
End augment.

Lemma MaxInt_2_ISize_USize :
  (2 * MaxInt ISize < MaxInt USize)%Z.
Proof.
  unsafe_unfold_common_caesium_defs. simpl.
  nia.
Qed.

Ltac init_cache :=
  ensure_jcache;
  (*specialize (bytes_per_addr_eq) as ?;*)
  specialize_cache (MaxInt_2_ISize_USize);
  specialize_cache (MaxInt_ge_127 I8);
  specialize_cache (MaxInt_ge_127 U8);
  specialize_cache (MaxInt_ge_127 I16);
  specialize_cache (MaxInt_ge_127 U16);
  specialize_cache (MaxInt_ge_127 I32);
  specialize_cache (MaxInt_ge_127 U32);
  specialize_cache (MaxInt_ge_127 I64);
  specialize_cache (MaxInt_ge_127 U64);
  specialize_cache (MaxInt_ge_127 I128);
  specialize_cache (MaxInt_ge_127 U128);
  specialize_cache (MaxInt_ge_127 ISize);
  specialize_cache (MaxInt_ge_127 USize);
  specialize_cache (MinInt_le_n128_signed I8 eq_refl);
  specialize_cache (MinInt_le_n128_signed I16 eq_refl);
  specialize_cache (MinInt_le_n128_signed I32 eq_refl);
  specialize_cache (MinInt_le_n128_signed I64 eq_refl);
  specialize_cache (MinInt_le_n128_signed I128 eq_refl);
  specialize_cache (MinInt_le_n128_signed ISize eq_refl);
  specialize_cache (MinInt_unsigned_0 U8 eq_refl);
  specialize_cache (MinInt_unsigned_0 U16 eq_refl);
  specialize_cache (MinInt_unsigned_0 U32 eq_refl);
  specialize_cache (MinInt_unsigned_0 U64 eq_refl);
  specialize_cache (MinInt_unsigned_0 U128 eq_refl);
  specialize_cache (MinInt_unsigned_0 USize eq_refl)
  (*specialize (layout_wf_unit) as ?;*)
  (*specialize (layout_wf_ptr) as ?*)
.


(** Solve [Inhabited] instances for inductives, used for enum declarations.
   We assume that arguments of inductive constructors have already been proved inhabited. *)
Ltac solve_inhabited :=
  simpl; intros; try unfold TCNoResolve;
  repeat match goal with
  | |- Inhabited ?X =>
      first [apply _ | refine (populate _); econstructor; eapply inhabitant]
  end.

(** ** Trait inclusion *)
Ltac solve_function_subtype_hook :=
  idtac.
Ltac solve_function_subtype :=
  lazymatch goal with
  | |- function_subtype ?a ?a =>
      apply function_subtype_refl
  | |- function_subtype ?a ?b =>
      solve_function_subtype_hook
  end.


(* Recursively destruct a product in hypothesis H, using the given name as template. *)
Ltac destruct_product_hypothesis name H :=
  match type of H with
  | (_ * _)%type =>   let tmp1 := fresh "tmp" in
                      let tmp2 := fresh "tmp" in
                      destruct H as [tmp1 tmp2];
                      destruct_product_hypothesis name tmp1;
                      destruct_product_hypothesis name tmp2
  | nil_unit => destruct H
  | cons_prod _ _ =>
      let tmp1 := fresh "tmp" in
      let tmp2 := fresh "tmp" in
      destruct H as [tmp1 tmp2];
      destruct_product_hypothesis name tmp1;
      destruct_product_hypothesis name tmp2
  | prod_vec _ ?n =>
      let m := eval simpl in n in
      match m with
      | S _ =>
                      let tmp1 := fresh "tmp" in
                      let tmp2 := fresh "tmp" in
                      destruct H as [tmp1 tmp2];
                      destruct_product_hypothesis name tmp1;
                      destruct_product_hypothesis name tmp2
      | 0%nat => destruct H
      end
  | plist _ ?xs =>
      let ys := eval simpl in xs in
      match ys with
      | _ :: _ =>
                      let tmp1 := fresh "tmp" in
                      let tmp2 := fresh "tmp" in
                      destruct H as [tmp1 tmp2];
                      destruct_product_hypothesis name tmp1;
                      destruct_product_hypothesis name tmp2
      | [] => destruct H
      end
  |    _ =>
      simpl in H;
      let id := fresh name in
      rename H into id
  end.

(** Automation for finding [FunctionSubtype] for assumed trait specifications. *)
Ltac is_applied_spec t :=
  match t with
  | ?spec ?a ?b =>
      match type of a with
      | plist _ _ => idtac
      end;
      match type of b with
      | plist _ _ => idtac
      end;
      match type of spec with
      | spec_with _ _ _ => idtac
      | prod_vec _ _ → plist _ _ → _ => idtac
      end
  end.
Local Ltac strip_applied_params a acc cont :=
  match a with
  | ?a1 ?a2 =>
      let a2 := eval unfold reverse_coercion in a2 in
      lazymatch type of a2 with
      | syn_type =>
          strip_applied_params a1 uconstr:(a2 +:: acc) cont
      | RT =>
          strip_applied_params a1 uconstr:(a2 +:: acc) cont
      | Type =>
          strip_applied_params a1 uconstr:(a2 +:: acc) cont
      | Set =>
          strip_applied_params a1 uconstr:(a2 +:: acc) cont
      | _ =>
          first [
            (* this is the spec term, finish *)
            is_applied_spec a2;
            cont a acc
          |
            (* this is an attrs record *)
            strip_applied_params a1 uconstr:(a2 +:: acc) cont
          ]
      end
  end.

(** Check if [a] is a projection of a record. *)
Ltac is_projection a :=
  let a := eval hnf in a in
  match a with
  | match _ with _ => _ end =>
    idtac
  end.

Local Ltac decompose_instantiated_spec_rec a ty_acc lft_acc cont :=
  lazymatch a with
  | spec_instantiate_lft_fst _ ?κ ?a =>
      decompose_instantiated_spec_rec a ty_acc (κ :: lft_acc) cont
  | spec_instantiate_typaram_fst _ _ ?ty ?a =>
      decompose_instantiated_spec_rec a (ty +:: ty_acc) (lft_acc) cont
  | _ => cont a ty_acc lft_acc
  end.
Local Ltac decompose_instantiated_tys tys :=
  lazymatch tys with
  | -[] => constr:(hnil id)
  | ?ty -:: ?tys =>
      let a := decompose_instantiated_tys tys in
      constr:(ty +:: a)
  end.
Local Ltac decompose_instantiated_lfts lfts :=
  lazymatch lfts with
  | -[] => constr:(@nil lft)
  | ?lft -:: ?lfts =>
      let a := decompose_instantiated_lfts lfts in
      constr:(lft :: a)
  end.

(** Decompose a term [a] of the shape [b <TY> ... <LFT> ... <INST!>]
   into the list of type instantiations [ty_inst] and lifetime instantiations
   [lft_inst], calling [cont b ty_inst lft_inst] afterwards. *)
Ltac decompose_instantiated_spec a cont :=
  lazymatch a with
  | spec_instantiated (?a) =>
      decompose_instantiated_spec_rec a (hnil id) (@nil lft) cont
  (* also handle the case that the instantiation has been reduced *)
  | ?a ?lfts ?tys =>
      let lfts := decompose_instantiated_lfts lfts in
      let tys := decompose_instantiated_tys tys in
      cont a tys lfts
  end.

(** Instantiate a spec term [spec] with types [tys] and lfts [lfts].
  [tys] has to be a [plist id Type].
  In contrast to directly applying [spec tys lfts], this works if it is not statically known that [spec] and [tys] have compatible types. *)
Ltac instantiate_spec_rec spec tys lfts :=
  lazymatch tys with
  | +[] =>
      lazymatch lfts with
      | [] => constr:(spec)
      | (?κ :: ?lfts) =>
          instantiate_spec_rec constr:(spec <LFT> κ) tys lfts
      end
  | (?ty +:: ?tys) =>
      instantiate_spec_rec constr:(spec <TY> ty) tys lfts
  end.


(** Given a quantified [trait_spec], find the spec inclusion assumption for this [trait_spec] and generate an instance of it for the instantiation [trait_ty_inst] and [trait_lft_inst].
  Calls [cont t1 t2 H] afterwards, where [t1] and [t2] are the applied trait specs and [H] is the generated proof hypothesis. *)
Ltac prove_trait_incl_for trait_spec trait_ty_inst trait_lft_inst cont :=
  lazymatch goal with
  | H : trait_incl_marker (lift_trait_incl ?incl trait_spec ?spec2) |- _ =>
      let H2 := fresh in

      let t1 := instantiate_spec_rec trait_spec trait_ty_inst trait_lft_inst in
      let t1 := constr:(t1 <INST!>) in

      let t2 := instantiate_spec_rec spec2 trait_ty_inst trait_lft_inst in
      let t2 := constr:(t2 <INST!>) in

      assert (incl t1 t2) as H2;
      [ rewrite trait_incl_marker_unfold in H;
        notypeclasses refine (H _ _)
      | cont t1 t2 H2 ]
  end.
(** Given a quantified [trait_spec], find the spec inclusion assumption for this [trait_spec] and generate an instance of it for the instantiation [trait_ty_inst] and [trait_lft_inst].
  Then, get its projection [trait_proj] and apply it to [appspec].
  Calls [cont t1 t2 H] afterwards, where [t1] and [t2] are the projected specs and [H] is the generated proof hypothesis. *)
Ltac prove_trait_proj_incl_for trait_proj appspec trait_spec trait_ty_inst trait_lft_inst cont :=
  prove_trait_incl_for trait_spec trait_ty_inst trait_lft_inst ltac:(fun t1 t2 H =>
    let t1 := constr:(trait_proj t1) in
    let t1 := apply_term_het constr:(t1) constr:(appspec) in

    let t2 := constr:(trait_proj t2) in
    let t2 := apply_term_het constr:(t2) constr:(appspec) in

    let H2 := fresh in
    assert (function_subtype t1 t2) as H2;
    [ apply H
    | clear H; cont H2 ]
  ).


(**
  Given a [function_subtype] proof goal, check whether the left function spec is a projection of an assumed trait spec.
  If that is the case, call [cont trait_proj trait_spec ty_inst lft_inst app],
   where [trait_proj] is the projection of the trait spec record,
   [trait_spec] is the quantified trait spec,
   [ty_inst] is the instantiation of its type parameters,
   [lft_inst] is the instantiation of its lifetime parameters,
   and [app] is the list of terms the resuling spec was applied to. *)
Ltac function_subtype_find_trait_spec cont :=
  match goal with
  | |- function_subtype ?a _ =>
      (* Find a subtype with function type... *)
      match a with
      | context [?a] =>
          let d := type of a in
          let e := eval simpl in d in
          match e with
          | prod_vec _ _ → plist _ _ → fn_spec =>
              (* Which is a projection of the universal spec record *)
              strip_applied_params a (hnil id) ltac:(fun a acc =>
              is_projection a;
              match a with
              | ?c1 ?d =>
                  (* now decompose d into the instantiation *)
                  decompose_instantiated_spec d ltac:(fun d ty lft =>
                    is_var d;
                    cont c1 d ty lft acc
                  )
              end
              )
          end
      end
  end.

Ltac function_subtype_solve_trait :=
  lazymatch goal with
  | |- FunctionSubtype ?a ?b =>
      is_evar b;
      unfold a;
      rewrite /FunctionSubtype;

      (* we lift out all the generics *)
      let κs := fresh "κs" in let tys := fresh "tys" in

      (* we have to be a bit careful here with the RHS term, to make sure that the instantiation below doesn't fail due to evar scopes. *)
      let evar_ident := fresh "_fn_term" in
      eapply (function_subtype_lift_generics_1 _ (λ κs tys,
        ltac:(evar (evar_ident : fn_spec); exact evar_ident)));

      (* we destruct the tuples *)
      intros κs tys;
      destruct_product_hypothesis κs κs;
      destruct_product_hypothesis tys tys;

      (* and do the same in the context of the evar *)
      let evar_ident := fresh "_fn_term2" in
      only [_fn_term]: (destruct_product_hypothesis κs κs; evar (evar_ident : fn_spec); exact evar_ident);
      only [_fn_term2]: destruct_product_hypothesis tys tys;

      (* lift the trait incl precondition *)
      lazymatch goal with
      | |- function_subtype ?a _ =>
        lazymatch a with
        | context [fn_spec_add_late_pre _ _] =>

        notypeclasses refine (function_subtype_lift_late_pre_2 _ _  _ _); [apply _ | ];

        (* unfold <MERGE!>, so that the application can properly reduce *)
        unfold spec_collapse_params;

        simpl;
        function_subtype_find_trait_spec ltac:(fun trait_proj trait_spec trait_ty_inst trait_lft_inst appspec =>
          (* Prove the inclusion for this projection *)
          prove_trait_proj_incl_for trait_proj appspec trait_spec trait_ty_inst trait_lft_inst
          ltac:(fun H =>
            (* apply the generated inclusion proof *)
            eapply function_subtype_lift_generics_2 in H; simpl in H;
            eapply function_subtype_trans; [apply H | ];
            eapply function_subtype_refl
          )
        )
        end
      end
  end.


Global Hint Extern 3 (FunctionSubtype _ _) => function_subtype_solve_trait : typeclass_instances.

Ltac strip_all_applied_params a acc cont :=
  match a with
  | ?a1 ?a2 =>
      strip_all_applied_params a1 uconstr:(a2 +:: acc) cont
  | _ => cont a acc
  end.
Ltac solve_trait_incl_prepare :=
  lazymatch goal with
  | |- trait_incl_marker ?P =>
      rewrite trait_incl_marker_unfold;
      let κs := fresh in let tys := fresh in
      intros κs tys;
      destruct_product_hypothesis κs κs;
      destruct_product_hypothesis tys tys
  end.
Ltac solve_trait_incl_core :=
  lazymatch goal with
  | |- ?incl ?spec1 ?spec2 =>
      try (decompose_instantiated_spec constr:(spec1) ltac:(fun spec1 spec1_tys spec1_lfts =>
        (* look for an assumption we can specialize *)
        is_var spec1;
        prove_trait_incl_for spec1 spec1_tys spec1_lfts ltac:(fun t1 t2 H2 =>
          etrans; first apply H2; clear H2
        )));
      first [reflexivity |
      (* directly solve the inclusion *)
      (* first unfold the inclusion *)
      strip_all_applied_params incl (hnil id) ltac:(fun a _ =>
        unfold a;
        intros;
        split_and?;
        intros
        (* leave the individual function inclusions *)
      )]
  end
.
Ltac solve_trait_incl_fn :=
  first [solve_function_subtype | done ].

Ltac solve_trait_incl :=
  solve_trait_incl_prepare;
  solve_trait_incl_core;
  try solve_trait_incl_fn.

