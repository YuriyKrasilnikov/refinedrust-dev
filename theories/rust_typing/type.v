From iris.bi Require Export fractional.
From iris.base_logic.lib Require Export invariants.
From iris.base_logic Require Import ghost_map na_invariants.
From caesium Require Export proofmode notation syntypes.
From lrust.lifetime Require Export frac_borrow.
From refinedrust Require Export base util hlist pinned_borrows lft_contexts gvar_refinement memcasts.
From caesium Require Import loc.
From iris.algebra Require Import stepindex_finite.
From refinedrust Require Import options.

(** * RefinedRust's notion of value types *)


(** Iris resource algebras that need to be available *)
Class typeGS Σ := TypeG {
  type_heapG :: refinedcG Σ;
  type_lftGS :: lftGS Σ lft_userE;
  type_na_mapG :: ghost_mapG Σ thread_id na_inv_pool_name;
  type_na_map_name : gname;
  type_na_invG :: na_invG Σ;
  type_frac_borrowG :: frac_borG Σ;
  type_lctxGS :: lctxGS Σ;
  type_ghost_var :: ghost_varG Σ RT;
  type_pinnedBorG :: pinnedBorG Σ;
}.
#[export] Hint Mode typeGS - : typeclass_instances.

Definition rrust_ctx `{typeGS Σ} : iProp Σ := lft_ctx ∗ llctx_ctx.

(** A thin wrapper around non-atomic invariants, using RefinedRust's thread ids as identifiers. *)
Section non_atomic.
  Context `{!typeGS Σ}.

  (* NOTE: auth element is allocated in adequacy and inaccessible afterwards. *)
  Definition na_own_def (π : thread_id) (E : coPset) :=
    (∃ γ, ghost_map_elem type_na_map_name π DfracDiscarded γ ∗ na_own γ E)%I.
  Definition na_own_aux π E : seal (na_own_def π E). Proof. by eexists. Qed.
  Definition na_own π E := (na_own_aux π E).(unseal).
  Definition na_own_unfold π E : na_own π E = na_own_def π E := (na_own_aux π E).(seal_eq).

  Definition na_inv_def (π : thread_id) (N : namespace) (P : iProp Σ) : iProp Σ :=
    (∃ γ, ghost_map_elem type_na_map_name π DfracDiscarded γ ∗ na_inv γ N P)%I.
  Definition na_inv_aux π N : seal (na_inv_def π N). Proof. by eexists. Qed.
  Definition na_inv π N := (na_inv_aux π N).(unseal).
  Definition na_inv_unfold π N : na_inv π N = na_inv_def π N := (na_inv_aux π N).(seal_eq).

  Global Instance na_own_timeless π E : Timeless (na_own π E).
  Proof. rewrite na_own_unfold. apply _. Qed.
  Global Instance na_own_empty_persistent π : Persistent (na_own π ∅).
  Proof. rewrite na_own_unfold. apply _. Qed.

  Global Instance na_inv_contractive p N : Contractive (na_inv p N).
  Proof. rewrite na_inv_unfold. solve_contractive. Qed.
  Global Instance na_inv_ne p N : NonExpansive (na_inv p N).
  Proof. rewrite na_inv_unfold. solve_proper. Qed.
  Global Instance na_inv_proper p N : Proper ((≡) ==> (≡)) (na_inv p N).
  Proof. apply (ne_proper _). Qed.

  Global Instance na_inv_persistent p N P : Persistent (na_inv p N P).
  Proof. rewrite na_inv_unfold; apply _. Qed.

  Lemma na_inv_iff p N P Q : na_inv p N P -∗ ▷ □ (P ↔ Q) -∗ na_inv p N Q.
  Proof.
    rewrite !na_inv_unfold.
    iIntros "(%γ & Hg & Hna) HPQ".
    iExists γ. iFrame. iApply (na_inv_iff with "Hna HPQ").
  Qed.

  (*Lemma na_alloc : ⊢ |==> ∃ p, na_own p ⊤.*)
  (*Proof. by apply own_alloc. Qed.*)

  Lemma na_own_disjoint π E1 E2 :
    na_own π E1 -∗ na_own π E2 -∗ ⌜E1 ## E2⌝.
  Proof.
    rewrite !na_own_unfold.
    iIntros "(%γ1 & Hg & Hna) (%γ2 & Hg2 & Hna2)".
    iPoseProof (ghost_map_elem_agree with "Hg Hg2") as "<-".
    iApply (na_own_disjoint with "Hna Hna2").
  Qed.

  Lemma na_own_union π E1 E2 :
    E1 ## E2 → na_own π (E1 ∪ E2) ⊣⊢ na_own π E1 ∗ na_own π E2.
  Proof.
    intros. rewrite !na_own_unfold. iSplit.
    - iIntros "(%γ & #Hg & Hna)". iFrame "#". by iApply na_own_union.
    - iIntros "[(%γ1 & Hg & Hna) (%γ2 & Hg2 & Hna2)]".
      iPoseProof (ghost_map_elem_agree with "Hg Hg2") as "<-".
      iExists γ1. iFrame. iApply na_own_union; first done.
      iFrame.
  Qed.

  Lemma na_own_acc E2 E1 π :
    E2 ⊆ E1 → na_own π E1 -∗ na_own π E2 ∗ (na_own π E2 -∗ na_own π E1).
  Proof.
    rewrite !na_own_unfold.
    iIntros (Hf) "(%γ & #Hg & Hna)".
    iPoseProof (na_own_acc with "Hna") as "(Hna & Hcl)"; first apply Hf.
    iFrame "#∗".
    iIntros "(%γ' & Hg' & Hna)".
    iPoseProof (ghost_map_elem_agree with "Hg Hg'") as "<-".
    iFrame. by iApply "Hcl".
  Qed.

  (* TODO Note: for compatibility with na_borrow, let's add na_own π ∅ to [ty_share].
     In existentials_na interpretation put the same mapping here (let's not go through the trouble of creating an abstraction for na_bor as well).
     Alternative: Redo the na_borrow definition on top of this interface here.

   *)
  Lemma na_inv_alloc π E N P :
    na_own π ∅ -∗
    ▷ P ={E}=∗
    na_inv π N P.
  Proof.
    iIntros "Hown HP".
    rewrite na_inv_unfold na_own_unfold.
    iDestruct "Hown" as "(%γ & Hg & Hown)".
    iMod (na_inv_alloc with "HP") as "Ha".
    by iFrame.
  Qed.

  Lemma na_inv_acc p E F N P :
    ↑N ⊆ E → ↑N ⊆ F →
    na_inv p N P -∗ na_own p F ={E}=∗ ▷ P ∗ na_own p (F∖↑N) ∗
                       (▷ P ∗ na_own p (F∖↑N) ={E}=∗ na_own p F).
  Proof.
    rewrite na_inv_unfold !na_own_unfold.
    iIntros (??) "(%γ1 & #Hg1 & Hna) (%γ2 & Hg2 & Hown)".
    iPoseProof (ghost_map_elem_agree with "Hg1 Hg2") as "<-".
    iMod (na_inv_acc with "Hna Hown") as "($ & Hna & Hcl)"; [done.. | ].
    iModIntro.
    iFrame. iIntros "(Hp & (%γ3 & Hg3 & Hown))".
    iPoseProof (ghost_map_elem_agree with "Hg1 Hg3") as "<-".
    iMod ("Hcl" with "[$]") as "Hna".
    by iFrame.
  Qed.

  (* Note: we don't get this *)
  Lemma na_own_empty π :
    ⊢ |==> na_own π ∅.
  Proof.
  Abort.
  (* But we can get this (note that [na_own π ∅] is persistent) *)
  Lemma na_own_empty π E :
    ⊢ na_own π E -∗ na_own π ∅.
  Proof.
    iIntros "Ha".
    iPoseProof (na_own_acc ∅ with "Ha") as "(#Hna' & Hcl)"; first set_solver.
    done.
  Qed.

  Lemma na_own_split π E E' :
    E' ⊆ E →
    na_own π E -∗ na_own π E' ∗ na_own π (E ∖ E').
  Proof.
    iIntros (?) "Hna".
    rewrite comm.

    iApply na_own_union.
    { set_solver. }

    replace E with ((E ∖ E') ∪ E') at 1; first done.

    set_unfold.
    split; first intuition.
    destruct (decide (x ∈ E')); intuition.
  Qed.

  Global Instance into_inv_na p N P : IntoInv (na_inv p N P) N := {}.

  Global Instance into_acc_na p F E N P :
    IntoAcc (X:=unit) (na_inv p N P)
            (↑N ⊆ E ∧ ↑N ⊆ F) (na_own p F) (fupd E E) (fupd E E)
            (λ _, ▷ P ∗ na_own p (F∖↑N))%I (λ _, ▷ P ∗ na_own p (F∖↑N))%I
              (λ _, Some (na_own p F))%I.
  Proof.
    rewrite /IntoAcc /accessor. iIntros ((?&?)) "#Hinv Hown".
    iExists tt.
    rewrite -assoc /=.
    iApply (na_inv_acc with "Hinv"); done.
  Qed.
End non_atomic.


(* The number of credits we deposit in the interpretation of Box/&mut for accessing them at a logical_step. *)
Definition num_cred := 5%nat.
Lemma num_cred_le `{!typeGS Σ} n :
  (1 ≤ n)%nat →
  num_cred ≤ num_laters_per_step n.
Proof.
  rewrite /num_cred/num_laters_per_step /=. lia.
Qed.

Definition have_creds `{!typeGS Σ} : iProp Σ := £ num_cred ∗ tr 1.
Definition maybe_creds `{!typeGS Σ} (wl : bool) := (if wl then have_creds else True)%I.

#[universes(polymorphic)]
Record RT : Type := mk_RT {
  RT_rt :> Type;
  RT_xt : Type;
  RT_xrt : RT_xt → RT_rt;
}.

(** metadata for unsized types *)
Inductive metadata_kind : Set :=
(* No metadata, i.e. [()] *)
| MetadataNone
(* Metadata describing a size, i.e. [usize] *)
| MetadataSize
(* Metadata describing a ptr *)
| MetadataPtr
.
Global Instance metadata_kind_inh : Inhabited metadata_kind.
Proof. exact (populate MetadataNone). Qed.
Global Instance metadata_kind_eq_dec : EqDecision metadata_kind.
Proof. solve_decision. Defined.

(* What is the semantic content of a type's metadata? *)
Definition metadata_kind_interp (k : metadata_kind) : Type :=
  match k with
  | MetadataNone => unit : Type
  | MetadataSize => Z
  | MetadataPtr => loc
  end.

Inductive metadata : Set :=
| MetaNone
| MetaSize (z : nat)
(* TODO: probably instead of the location this would rather be some other structure describing the layout or so *)
| MetaPtr (l : loc)
.

Import EqNotations.

(** Types are defined semantically by what it means for a value to have a particular type.
    Types are indexed by their refinement type [rt].
*)
Record type `{!typeGS Σ} (rt : RT) := {
  (* The xt type should be inhabited *)
  ty_xt_inhabited : Inhabited (RT_xt rt);

  (* What metadata does this type need? *)
  ty_metadata_kind : metadata_kind;

  (** Ownership of values, depending also on the metadata *)
  ty_own_val :
    thread_id → RT_rt rt → metadata → val → iProp Σ;

  (** This type's syntactic type *)
  ty_syn_type : metadata → syn_type;

  (** Determines how values are altered when they are read and written *)
  (** This is formulated as a property of the semantic type, because the memcast compatibility is a semantic property *)
  _ty_has_op_type : op_type → memcast_compat_type → Prop;

  (** The sharing predicate: what does it mean to have a shared reference to this type at a particular lifetime? *)
  ty_shr : lft → thread_id → RT_rt rt → metadata → loc → iProp Σ;

  (** We have a separate well-formedness predicate to capture persistent + timeless information about
    the type's structure. Needed to evade troubles with the ltype unfolding equations. *)
  ty_sidecond : iProp Σ;

  (* [ty_lfts] is the set of lifetimes that needs to be active for this type to make sense.*)
  _ty_lfts : list lft;

  (* [ty_wf_E] is a set of inclusion constraints on lifetimes that need to hold for the type to make sense. *)
  _ty_wf_E : elctx;

  (** Given the concrete layout algorithm at runtime, we can get a layout *)
  ty_has_layout π r m v :
    ty_own_val π r m v -∗
    ∃ ly : layout, ⌜syn_type_has_layout (ty_syn_type m) ly⌝ ∗ ⌜v `has_layout_val` ly⌝;

  ty_ghost_drop : thread_id → rt → iProp Σ;

  (** If we specify a particular op_type, its layout needs to be compatible with the underlying syntactic type.
    In particular, this needs to be independent of the metadata -- forcing [ty_has_op_type] for unsized types to be [False].
  *)
  _ty_op_type_stable ot mt :
    _ty_has_op_type ot mt → syn_type_has_layout (ty_syn_type MetaNone) (ot_layout ot);

  (** We can get access to the sidecondition *)
  ty_own_val_sidecond π r m v : ty_own_val π r m v -∗ ty_sidecond;
  ty_shr_sidecond κ π r m l : ty_shr κ π r m l -∗ ty_sidecond;

  (** The sharing predicate is persistent *)
  (* Disabling TC resolution in order to make the proof opaque for type declarations *)
  _ty_shr_persistent κ π l r m : TCNoResolve (Persistent (ty_shr κ π r m l));
  (** The address at which a shared type is stored must be correctly aligned *)
  ty_shr_aligned κ π l r m :
    ty_shr κ π r m l -∗
    ∃ (ly : layout),
      ⌜l `has_layout_loc` ly⌝ ∗ ⌜syn_type_has_layout (ty_syn_type m) ly⌝;

  (** We need to be able to initiate sharing *)
  ty_share E κ l ly π r m q:
    lftE ⊆ E →
    rrust_ctx -∗
    na_own π ∅ -∗
    (* We get a token not only for κ, but for all that we might need to recursively use to initiate sharing *)
    let κ' := lft_intersect_list (_ty_lfts) in
    q.[κ ⊓ κ'] -∗
    (* [l] needs to be well-layouted *)
    ⌜syn_type_has_layout (ty_syn_type m) ly⌝ -∗
    ⌜l `has_layout_loc` ly⌝ -∗
    loc_in_bounds l 0 (ly_size ly) -∗
    &{κ} (∃ v, l ↦ v ∗ ty_own_val π r m v) -∗
    (* after a logical step, we can initiate sharing *)
    logical_step E (ty_shr κ π r m l ∗ q.[κ ⊓ κ']);

  (** The sharing predicate is monotonic *)
  ty_shr_mono κ κ' tid r m l :
    κ' ⊑ κ -∗ ty_shr κ tid r m l -∗ ty_shr κ' tid r m l;

  ty_own_ghost_drop π r m v F :
    lftE ⊆ F → ty_own_val π r m v -∗ logical_step F (ty_ghost_drop π r);

  (** We can transport value ownership over memcasts according to the specification by [ty_has_op_type] *)
  _ty_memcast_compat ot mt st π r m v :
    _ty_has_op_type ot mt →
    ty_own_val π r m v -∗
    match mt with
    | MCNone => True
    | MCCopy => ty_own_val π r m (mem_cast v ot st)
    | MCId => ⌜mem_cast_id v ot⌝
    end;

  (* TODO this would be a good property to have, but currently uninit doesn't satisfy it. *)
  (* we require that ops at least as given by the "canonical" optype obtained by [use_op_alg] are allowed *)
  (*ty_has_op_type_compat ot mt : *)
    (*use_op_alg ty_syn_type = Some ot →*)
    (*mt ≠ MCId →*)
    (*ty_has_op_type ot mt;*)

  (** Untyped operations are always allowed  *)
  _ty_has_op_type_untyped ly mt :
    ty_metadata_kind = MetadataNone →
    syn_type_has_layout (ty_syn_type MetaNone) ly →
    _ty_has_op_type (UntypedOp ly) mt;

  ty_sidecond_timeless : Timeless ty_sidecond;
  ty_sidecond_persistent : Persistent ty_sidecond;
}.
Arguments ty_own_val : simpl never.
Arguments ty_shr : simpl never.
(*Arguments ty_ghost_drop : simpl never.*)
#[export] Existing Instance ty_sidecond_timeless.
#[export] Existing Instance ty_sidecond_persistent.
#[export] Existing Instance ty_xt_inhabited.
Global Instance ty_rt_inhabited `{!typeGS Σ} {rt} (ty : type rt) : Inhabited rt :=
  populate (RT_xrt rt (@inhabitant _ (ty_xt_inhabited _ ty))).

Arguments ty_xt_inhabited {_ _ _}.
Arguments ty_own_val {_ _ _}.
Arguments ty_sidecond {_ _ _}.
Arguments ty_syn_type {_ _ _}.
Arguments ty_shr {_ _ _}.
Arguments ty_share {_ _ _}.
Arguments ty_metadata_kind {_ _ _}.
Arguments ty_ghost_drop {_ _ _}.

#[export] Instance ty_shr_persistent `{!typeGS Σ} {rt : RT} (ty : type rt) κ π l r m :
  Persistent (ty_shr ty κ π r m l).
Proof. apply _ty_shr_persistent. Qed.

Class TySized `{!typeGS Σ} {rt} (ty : type rt) := {
  ty_sized_metadata_none : ty.(ty_metadata_kind) = MetadataNone;
  ty_sized_syn_type_eq : ∀ m1 m2, ty.(ty_syn_type) m1 = ty.(ty_syn_type) m2;
}.

Definition ty_sized_syn_type `{!typeGS Σ} {rt} (ty : type rt) `{!TySized ty} : syn_type :=
  ty.(ty_syn_type) MetaNone.
  (*ty.(ty_syn_type) (rew <- sized_metadata_none in (tt : metadata_kind_interp MetadataNone)).*)

(** We seal [ty_has_op_type] in order to avoid performance issues with automation accidentally unfolding it. *)
Definition ty_has_op_type_aux `{!typeGS Σ} : seal (@_ty_has_op_type _ _). Proof. by eexists. Qed.
Definition ty_has_op_type `{!typeGS Σ} := ty_has_op_type_aux.(unseal).
Definition ty_has_op_type_unfold `{!typeGS Σ} : ty_has_op_type = _ty_has_op_type := ty_has_op_type_aux.(seal_eq).
Arguments ty_has_op_type {_ _ _}.

Lemma ty_op_type_stable `{!typeGS Σ} {rt} (ty : type rt) ot mt :
  ty_has_op_type ty ot mt →
  syn_type_has_layout (ty.(ty_syn_type) MetaNone) (ot_layout ot).
Proof. rewrite ty_has_op_type_unfold. apply _ty_op_type_stable. Qed.
Global Arguments ty_op_type_stable {_ _ _} [_ _ _].

Lemma ty_sized_has_op_type_untyped `{!typeGS Σ} {rt} (ty : type rt) `{!TySized ty} ly mt :
  syn_type_has_layout (ty_sized_syn_type ty) ly →
  ty_has_op_type ty (UntypedOp ly) mt.
Proof.
  rewrite ty_has_op_type_unfold. apply _ty_has_op_type_untyped.
  apply ty_sized_metadata_none.
Qed.
Global Arguments ty_sized_has_op_type_untyped {_ _ _} [_ _ _ _].

Lemma ty_memcast_compat `{!typeGS Σ} rt (ty : type rt) ot mt st π r m v :
  ty_has_op_type ty ot mt →
  ty.(ty_own_val) π r m v -∗
  match mt with
  | MCNone => True
  | MCCopy => ty.(ty_own_val) π r m (mem_cast v ot st)
  | MCId => ⌜mem_cast_id v ot⌝
  end.
Proof. rewrite ty_has_op_type_unfold. apply _ty_memcast_compat. Qed.

(** We seal [ty_wf_E] in order to avoid performance issues with Qed time. *)
Definition ty_wf_E_aux `{!typeGS Σ} : seal (@_ty_wf_E _ _). Proof. by eexists. Qed.
Definition ty_wf_E `{!typeGS Σ} := ty_wf_E_aux.(unseal).
Definition ty_wf_E_unfold `{!typeGS Σ} : ty_wf_E = _ty_wf_E := ty_wf_E_aux.(seal_eq).
Global Arguments ty_wf_E {_ _ _} _.

(** We seal [ty_lfts] in order to avoid performance issues with Qed time. *)
Definition ty_lfts_aux `{!typeGS Σ} : seal (@_ty_lfts _ _). Proof. by eexists. Qed.
Definition ty_lfts `{!typeGS Σ} := ty_lfts_aux.(unseal).
Definition ty_lfts_unfold `{!typeGS Σ} : ty_lfts = _ty_lfts := ty_lfts_aux.(seal_eq).
Global Arguments ty_lfts {_ _ _} _.

Global Hint Extern 3 (type ?rt) => lazymatch goal with H : type rt |- _ => apply H end : typeclass_instances.

Definition RT_of `{!typeGS Σ} {rt} (ty : type rt) : RT := rt.
Definition rt_of `{!typeGS Σ} {rt} (ty : type rt) : Type := rt.
Notation st_of ty := (ty_syn_type ty).
Global Arguments RT_of _ _ _ _ /.
Global Arguments rt_of _ _ _ _ /.

Definition ty_is_xrfn `{!typeGS Σ} {rt} (ty : type rt) (r : rt) :=
  ∃ xr, r = RT_xrt _ xr.
Arguments ty_is_xrfn : simpl never.
Global Typeclasses Opaque ty_is_xrfn.

Lemma ty_own_val_has_layout `{!typeGS Σ} {rt} (ty : type rt) ly π r m v :
  syn_type_has_layout (ty.(ty_syn_type) m) ly →
  ty.(ty_own_val) π r m v -∗
  ⌜v `has_layout_val` ly⌝.
Proof.
  iIntros (Hly) "Hval". iPoseProof (ty_has_layout with "Hval") as (ly') "(%Hst & %Hly')".
  have ?: ly' = ly by eapply syn_type_has_layout_inj. subst ly'. done.
Qed.

Definition ty_allows_writes `{!typeGS Σ} {rt} (ty : type rt) `{!TySized ty} :=
  ty_has_op_type ty (use_op_alg' (ty_sized_syn_type ty)) MCNone.
Definition ty_allows_reads `{!typeGS Σ} {rt} (ty : type rt) `{!TySized ty} :=
  ty_has_op_type ty (use_op_alg' (ty_sized_syn_type ty)) MCCopy.

#[universes(polymorphic)]
Record rtype `{!typeGS Σ} `{!LayoutAlg} := mk_rtype {
  rt_rty : RT;
  rt_ty : type rt_rty;
}.
Global Arguments mk_rtype {_ _ _ _}.

(** Well-formedness of a type with respect to lifetimes.  *)
(* Generate a constraint that a type outlives κ. *)
Fixpoint lfts_outlives_E `{!typeGS Σ} (κs : list lft) (κ : lft) : elctx :=
  match κs with
  | [] => []
  | α :: κs => (κ, α) :: lfts_outlives_E κs κ
  end.
Lemma lfts_outlives_E_fmap `{!typeGS Σ} κs κ :
  lfts_outlives_E κs κ = (λ α, (κ, α)) <$> κs.
Proof.
  induction κs; simpl; first done.
  f_equiv. done.
Qed.
Arguments lfts_outlives_E : simpl never.
Definition ty_outlives_E `{!typeGS Σ} {rt} (ty : type rt) (κ : lft) : elctx :=
  lfts_outlives_E (ty_lfts ty) κ.

(* TODO this can probably not uphold the invariant that our elctx should be keyed by the LHS of ⊑ₑ *)
Fixpoint tyl_lfts `{!typeGS Σ} (tyl : list rtype) : list lft :=
  match tyl with
  | [] => []
  | [ty] => ty_lfts ty.(rt_ty)
  | ty :: tyl => (ty_lfts ty.(rt_ty)) ++ tyl.(tyl_lfts)
  end.

Fixpoint tyl_wf_E `{!typeGS Σ} (tyl : list rtype) : elctx :=
  match tyl with
  | [] => []
  | [ty] => ty_wf_E ty.(rt_ty)
  | ty :: tyl => ty_wf_E ty.(rt_ty) ++ tyl.(tyl_wf_E)
  end.

Fixpoint tyl_outlives_E `{!typeGS Σ} (tyl : list rtype) (κ : lft) : elctx :=
  match tyl with
  | [] => []
  | [ty] => ty_outlives_E ty.(rt_ty) κ
  | ty :: tyl => ty_outlives_E ty.(rt_ty) κ ++ tyl.(tyl_outlives_E) κ
  end.

Section memcast.
  Context `{!typeGS Σ}.
  Lemma ty_memcast_compat_copy {rt} π r v ot (ty : type rt) m st :
    ty_has_op_type ty ot MCCopy →
    ty.(ty_own_val) π r m v -∗ ty.(ty_own_val) π r m (mem_cast v ot st).
  Proof. move => ?. by apply: (ty_memcast_compat _ _ _ MCCopy). Qed.

  Lemma ty_memcast_compat_id {rt} π r v ot (ty : type rt) m :
    ty_has_op_type ty ot MCId →
    ty.(ty_own_val) π r m v -∗ ⌜mem_cast_id v ot⌝.
  Proof. move => ?. by apply: (ty_memcast_compat _ _ _ MCId inhabitant). Qed.
End memcast.

(** simple types *)
(* Simple types are copy, have a simple sharing predicate, and do not nest. *)
Record simple_type `{!typeGS Σ} (rt : RT) :=
  { st_xt_inhabited : Inhabited (RT_xt rt);
    st_own : thread_id → rt → val → iProp Σ;
    st_syn_type : syn_type;
    st_has_op_type : op_type → memcast_compat_type → Prop;
    st_has_layout π r v :
      st_own π r v -∗ ∃ ly, ⌜syn_type_has_layout st_syn_type ly⌝ ∗ ⌜v `has_layout_val` ly⌝;
    st_op_type_stable ot mt : st_has_op_type ot mt → syn_type_has_layout st_syn_type (ot_layout ot);
    (* TCNoResolve so we can make the proof opaque *)
    _st_own_persistent π r v : TCNoResolve (Persistent (st_own π r v));

    st_memcast_compat ot mt st π r v :
      st_has_op_type ot mt →
      st_own π r v -∗
      match mt with
      | MCNone => True
      | MCCopy => st_own π r (mem_cast v ot st)
      | MCId => ⌜mem_cast_id v ot⌝
      end;

    st_has_op_type_untyped mt ly :
      syn_type_has_layout st_syn_type ly →
      st_has_op_type (UntypedOp ly) mt;

    (*st_has_op_type_compat ot mt :*)
      (*use_op_alg st_syn_type = Some ot →*)
      (*mt ≠ MCId →*)
      (*st_has_op_type ot mt;*)
  }.
#[export] Existing Instance st_xt_inhabited.
#[export] Instance: Params (@st_own) 4 := {}.
Arguments st_own {_ _ _}.
Arguments st_has_op_type {_ _ _}.
Arguments st_syn_type {_ _ _}.

#[export] Instance st_own_persistent `{!typeGS Σ} {rt} (ty : simple_type rt) π r v :
  (Persistent (st_own ty π r v)).
Proof. apply _st_own_persistent. Qed.

Lemma st_own_has_layout `{!typeGS Σ} {rt} (ty : simple_type rt) ly π r v :
  syn_type_has_layout ty.(st_syn_type) ly →
  ty.(st_own) π r v -∗
  ⌜v `has_layout_val` ly⌝.
Proof.
  iIntros (Hly) "Hval". iPoseProof (st_has_layout with "Hval") as (ly') "(%Hst & %Hly')".
  have ?: ly' = ly by eapply syn_type_has_layout_inj. subst ly'. done.
Qed.


Program Definition ty_of_st `{!typeGS Σ} rt (st : simple_type rt) : type rt :=
  {| ty_xt_inhabited := st.(st_xt_inhabited _);
    ty_metadata_kind := MetadataNone;
    ty_own_val tid r m v := (⌜m = MetaNone⌝ ∗ st.(st_own) tid r v)%I;
    _ty_has_op_type := st.(st_has_op_type);
    ty_syn_type _ := st.(st_syn_type);
    ty_sidecond := True;
    ty_shr κ tid r m l :=
      (∃ vl ly, ⌜m = MetaNone⌝ ∗ &frac{κ} (λ q, l ↦{q} vl) ∗
        (* later for contractiveness *)
        ▷ st.(st_own) tid r vl ∗
        ⌜syn_type_has_layout st.(st_syn_type) ly⌝ ∗
        ⌜l `has_layout_loc` ly⌝)%I;
    ty_ghost_drop π r := True%I;
     _ty_lfts := [];
     _ty_wf_E := [];
  |}.
Next Obligation.
  iIntros (????????) "(-> & Hown)".
  iApply (st_has_layout with "Hown").
Qed.
Next Obligation.
  iIntros (??? st ot mt Hot). by eapply st_op_type_stable.
Qed.
Next Obligation.
  iIntros (????????) "Hown". done.
Qed.
Next Obligation.
  iIntros (?????????) "Hown". done.
Qed.
Next Obligation.
  unfold TCNoResolve. apply _.
Qed.
Next Obligation.
  iIntros (??? st κ π l r m). simpl.
  iIntros "(%vl & %ly & -> & _ & _ & %Hst & %Hly)".
  iExists _.
  eauto.
Qed.
Next Obligation.
  iIntros (??? st E κ l ly π r m ? ?) "#(LFT & TIME) Hna Hκ Hst Hly Hlb Hmt".
  simpl. rewrite right_id.
  iApply fupd_logical_step.
  iMod (bor_exists with "LFT Hmt") as (vl) "Hmt"; first solve_ndisj.
  iMod (bor_sep with "LFT Hmt") as "[Hmt Hown]"; first solve_ndisj.
  iMod (bor_persistent with "LFT Hown Hκ") as "[Hown Hκ]"; first solve_ndisj.
  iDestruct "Hown" as "(>-> & Hown)".
  iMod (bor_fracture (λ q, l ↦{q} vl)%I with "LFT Hmt") as "Hfrac"; [eauto with iFrame.. |].
  iApply logical_step_intro. eauto 8 with iFrame.
Qed.
Next Obligation.
  iIntros (??? st κ κ' π r m l) "#Hord H".
  iDestruct "H" as (vl ly) "(-> & #Hf & #Hown)".
  iExists vl, ly. iFrame "Hown". iR. by iApply (frac_bor_shorten with "Hord").
Qed.
Next Obligation.
  intros. iIntros "_". by iApply logical_step_intro.
Qed.
Next Obligation.
  intros. iIntros "(-> & Hown)".
  destruct mt.
  - done.
  - iR. by iApply (st_memcast_compat _ _ _ MCCopy).
  - by iApply (st_memcast_compat _ _ _ MCId).
Qed.
Next Obligation.
  intros. by apply st_has_op_type_untyped.
Qed.
(*Next Obligation.*)
  (*intros. apply st_has_op_type_compat; done.*)
(*Qed.*)

Coercion ty_of_st : simple_type >-> type.

Global Instance simple_type_sized `{!typeGS Σ} {rt} (ty : simple_type rt) :
  TySized ty.
Proof.
  done.
Qed.

Lemma simple_type_shr_equiv `{!typeGS Σ} {rt} (ty : simple_type rt) l π κ r m :
  (ty_shr ty κ π r m l) ≡
  (∃ (v : val) (ly : layout),
    ⌜m = MetaNone⌝ ∗
    ⌜syn_type_has_layout (ty_sized_syn_type ty) ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
    &frac{κ} (λ q : Qp, l ↦{q} v) ∗
    ▷ ty.(ty_own_val) π r MetaNone v)%I.
Proof.
  iSplit.
  - iIntros "(%v & %ly & -> & ? & ? & ? & ?)"; simpl.
    by iFrame.
  - iIntros "(%v & %ly & -> & ? & ? & ? & (_ & ?))"; iExists _, _.
    by iFrame.
Qed.

Bind Scope bi_scope with type.

Notation "l ◁ₗ{ π , m , κ } r @ ty" := (ty_shr ty κ π r m l) (at level 15, format "l  ◁ₗ{ π , m , κ }  r @ ty") : bi_scope.
Notation "v ◁ᵥ{ π , m }  r @ ty" := (ty_own_val ty π r m v) (at level 15) : bi_scope.
Notation "l ◁ₗ{ π , m , κ } .@ ty" := (ty_shr ty κ π () m l) (at level 15, format "l  ◁ₗ{ π , m , κ }  .@ ty") : bi_scope.
Notation "v ◁ᵥ{ π , m }  .@ ty" := (ty_own_val ty π () m v) (at level 15) : bi_scope.

Notation "'$#' x" := (RT_xrt _ x) (at level 9).
Notation "'$#@{' A '}' x" := (RT_xrt A x) (at level 9).
Notation "'<$#>' x" := (fmap (M := list) (RT_xrt _) x) (at level 30).
Notation "'<$#@{' A '}>' x" := (fmap (M := list) (RT_xrt A) x) (at level 30).
Notation "'<$#@{' A '}>@{' B '}' x" := (fmap (M := B) (RT_xrt A) x) (at level 30).
Notation "'<$#>@{' B '}' x" := (fmap (M := B) (RT_xrt _) x) (at level 30).


Record xtype `{!typeGS Σ} := mk_xtype {
  xtype_rt : RT;
  xtype_ty : type xtype_rt;
  xtype_rfn : RT_xt xtype_rt;
  xtype_sized : TySized xtype_ty;
}.
Global Arguments mk_xtype {_ _ _}.
Global Existing Instance xtype_sized.

(*** Cofe and Ofe *)
Section ofe.
  Context `{!typeGS Σ}.
  Context {rt : RT}.

  Canonical Structure metadataO := leibnizO metadata.
  Canonical Structure metadata_kindO := leibnizO metadata_kind.

  Inductive type_equiv' (ty1 ty2 : type rt) : Prop :=
    Type_equiv :
      (ty1.(ty_metadata_kind) = ty2.(ty_metadata_kind)) →
      (∀ ot mt, ty_has_op_type ty1 ot mt ↔ ty_has_op_type ty2 ot mt) →
      (∀ π r m v, ty1.(ty_own_val) π r m v ≡ ty2.(ty_own_val) π r m v) →
      (∀ κ π r m l, ty1.(ty_shr) κ π r m l ≡ ty2.(ty_shr) κ π r m l) →
      (∀ π r, ty1.(ty_ghost_drop) π r ≡ ty2.(ty_ghost_drop) π r) →
      (∀ m, ty1.(ty_syn_type) m = ty2.(ty_syn_type) m) →
      (ty1.(ty_sidecond) ≡ ty2.(ty_sidecond)) →
      (ty_lfts ty1) = (ty_lfts ty2) →
      (ty_wf_E ty1 = ty_wf_E ty2) →
      type_equiv' ty1 ty2.
  Instance type_equiv : Equiv (type rt) := type_equiv'.
  Inductive type_dist' (n : nat) (ty1 ty2 : type rt) : Prop :=
    Type_dist :
      (ty1.(ty_metadata_kind) = ty2.(ty_metadata_kind)) →
      (∀ ot mt, ty_has_op_type ty1 ot mt ↔ ty_has_op_type ty2 ot mt) →
      (∀ π r m v, ty1.(ty_own_val) π r m v ≡{n}≡ ty2.(ty_own_val) π r m v) →
      (∀ κ π r m v, ty1.(ty_shr) κ π r m v ≡{n}≡ ty2.(ty_shr) κ π r m v) →
      (∀ π r, ty1.(ty_ghost_drop) π r ≡{n}≡ ty2.(ty_ghost_drop) π r) →
      (∀ m, ty1.(ty_syn_type) m = ty2.(ty_syn_type) m) →
      (ty1.(ty_sidecond) ≡{n}≡ ty2.(ty_sidecond)) →
      (ty_lfts ty1) = (ty_lfts ty2) →
      (ty_wf_E ty1 = ty_wf_E ty2) →
      type_dist' n ty1 ty2.
  Instance type_dist : Dist (type rt) := type_dist'.

  (* type rt is isomorphic to { x : T | P x } *)
  Let T :=
    prodO (prodO (prodO (prodO (prodO (prodO (prodO (prodO
      (thread_id -d> rt -d> metadataO -d> val -d> iPropO Σ)
      (lft -d> thread_id -d> rt -d> metadataO -d> loc -d> iPropO Σ))
      (thread_id -d> rt -d> iPropO Σ))
      metadata_kindO)
      (metadataO -d> syn_typeO))
      (op_type -d> leibnizO memcast_compat_type -d> PropO))
      (iPropO Σ))
      (leibnizO (list lft)))
      (leibnizO elctx).
  Let P (x : T) : Prop :=
    (*let '(T_own_val, T_shr, T_syn_type, T_depth, T_ot, T_sidecond, T_drop, T_lfts, T_wf_E) := x in*)
    (* ty_has_layout *)
    (∀ π r m v, x.1.1.1.1.1.1.1.1 π r m v -∗ ∃ ly : layout, ⌜syn_type_has_layout (x.1.1.1.1.2 m) ly⌝ ∗ ⌜v `has_layout_val` ly⌝) ∧
    (* ty_op_type_stable *)
    (∀ ot mt m, x.1.1.1.2 ot mt → syn_type_has_layout (x.1.1.1.1.2 m) (ot_layout ot)) ∧
    (* ty_own_val_sidecond *)
    (∀ π r m v, x.1.1.1.1.1.1.1.1 π r m v -∗ x.1.1.2) ∧
    (* ty_shr_sidecond *)
    (∀ κ π r m l, x.1.1.1.1.1.1.1.2 κ π r m l -∗ x.1.1.2) ∧
    (* ty_shr_persistent *)
    (∀ κ π r m l, Persistent (x.1.1.1.1.1.1.1.2 κ π r m l)) ∧
    (* ty_shr_aligned *)
    (∀ κ π l r m, x.1.1.1.1.1.1.1.2 κ π r m l -∗ ∃ (ly : layout), ⌜l `has_layout_loc` ly⌝ ∗ ⌜syn_type_has_layout (x.1.1.1.1.2 m) ly⌝) ∧
    (* ty_share *)
    (∀ E κ l ly π r m q, lftE ⊆ E → rrust_ctx -∗
      let κ' := lft_intersect_list x.1.2 in
      q.[κ ⊓ κ'] -∗
      ⌜syn_type_has_layout (x.1.1.1.1.2 m) ly⌝ -∗
      ⌜l `has_layout_loc` ly⌝ -∗
      loc_in_bounds l 0 (ly_size ly) -∗
      &{κ} (∃ v, l ↦ v ∗ x.1.1.1.1.1.1.1.1 π r m v) -∗ logical_step E (x.1.1.1.1.1.1.1.2 κ π r m l ∗ q.[κ ⊓ κ'])) ∧
    (* ty_shr_mono *)
    (∀ κ κ' π r m (l : loc), κ' ⊑ κ -∗ x.1.1.1.1.1.1.1.2 κ π r m l -∗ x.1.1.1.1.1.1.1.2 κ' π r m l) ∧
    (* ty_own_ghost_drop *)
    (∀ π r m v F, lftE ⊆ F → x.1.1.1.1.1.1.1.1 π r m v -∗ logical_step F (x.1.1.1.1.1.1.2 π r)) ∧
    (* ty_memcast_compat *)
    (∀ ot mt st π r m v, x.1.1.1.2 ot mt → x.1.1.1.1.1.1.1.1 π r m v -∗
      match mt with | MCNone => True | MCCopy => x.1.1.1.1.1.1.1.1 π r m (mem_cast v ot st) | MCId => ⌜mem_cast_id v ot⌝ end) ∧
    (* ty_has_op_type_untyped *)
    (∀ (ly : layout) (mt : memcast_compat_type) m,
      x.1.1.1.1.1.2 = MetadataNone →
      syn_type_has_layout (x.1.1.1.1.2 m) ly →
      x.1.1.1.2 (UntypedOp ly) mt) ∧
    (* ty_has_op_type_compat *)
    (*(∀ ot mt, use_op_alg x.1.1.1.1.1.2 = Some ot → mt ≠ MCId → x.1.1.1.1.2 ot mt) ∧*)
    (* ty_sidecond_timeless *)
    (Timeless (x.1.1.2)) ∧
    (* ty_sidecond_persistent *)
    (Persistent (x.1.1.2)).

  (* to handle the let destruct in an acceptable way *)
  Local Set Program Cases.

  Definition type_unpack (ty : type rt) : T :=
    (ty.(ty_own_val),
     ty.(ty_shr),
     ty.(ty_ghost_drop),
     ty.(ty_metadata_kind),
     ty.(ty_syn_type),
     ty_has_op_type ty,
     ty.(ty_sidecond),
     ty_lfts ty,
     ty_wf_E ty).
  (*
  Program Definition type_pack (x : T) (H : P x) : type rt :=
    let '(existT xt (xrt, xinh), T_own_val, T_shr, T_syn_type, T_ot, T_sidecond, T_lfts, T_wf_E) := x in
    {|
      ty_xt_inhabited := populate xinh;
      ty_xt := xt;
      ty_xrt := xrt;
      ty_own_val := T_own_val;
      _ty_has_op_type := T_ot;
      ty_syn_type := T_syn_type;
      ty_shr := T_shr;
      ty_sidecond := T_sidecond;
      ty_lfts := T_lfts;
      _ty_wf_E := T_wf_E;
    |}.
  Solve Obligations with
    intros [[[[[[[[] T_own_val] T_shr] T_syn_type] T_ot] T_sidecond] T_lfts] T_wf_E];
    intros (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ?);
    intros ?????????? Heq; injection Heq; intros -> -> -> -> -> -> ->;
    done.
   *)

  Definition type_ofe_mixin : OfeMixin (type rt).
  Proof.
    apply (iso_ofe_mixin type_unpack).
    - intros t1 t2. split.
      + destruct 1 as [? ? ? ? ? ? ? ? ?].
        repeat split_and!; simpl; try done.
      + intros [[[[[[[[]]]]]]]]; simpl in *.
        constructor; try done.
    - intros ? t1 t2. split.
      + destruct 1 as [? ? ? ? ? ? ? ? ?].
        repeat split_and!; simpl; try done.
      + intros [[[[[[[[]]]]]]]]; simpl in *.
        constructor; try done.
  Qed.
  Canonical Structure typeO : ofe := Ofe (type rt) type_ofe_mixin.

  Global Instance ty_own_val_ne n:
    Proper (dist n ==> eq ==> eq ==> eq ==> eq ==> dist n) ty_own_val.
  Proof. intros ?? EQ ??-> ??-> ??-> ??->. apply EQ. Qed.
  Global Instance ty_own_val_proper : Proper ((≡) ==> eq ==> eq ==> eq ==> eq ==> (≡)) ty_own_val.
  Proof. intros ?? EQ ??-> ??-> ??-> ??->. apply EQ. Qed.
  Lemma ty_own_val_entails ty1 ty2 π r m v:
    ty1 ≡@{type rt} ty2 →
    ty_own_val ty1 π r m v -∗
    ty_own_val ty2 π r m v.
  Proof. intros [_ _ -> _]; eauto. Qed.

  Global Instance ty_shr_ne n:
    Proper (dist n ==> eq ==> eq ==> eq ==> eq ==> eq ==> dist n) ty_shr.
  Proof. intros ?? EQ ??-> ?? -> ??-> ??-> ??->. apply EQ. Qed.
  Global Instance ty_shr_proper : Proper ((≡) ==> eq ==> eq ==> eq ==> eq ==> eq ==> (≡)) ty_shr.
  Proof. intros ?? EQ ??-> ?? -> ??-> ??-> ??->. apply EQ. Qed.
  Lemma ty_shr_entails ty1 ty2 κ π r m l:
    ty1 ≡@{type rt} ty2 →
    ty_shr ty1 κ π r m l -∗
    ty_shr ty2 κ π r m l.
  Proof. intros [_ _ _ -> _]; eauto. Qed.

  Global Instance ty_ghost_drop_ne n:
    Proper (dist n ==> eq ==> eq ==>  dist n) ty_ghost_drop.
  Proof. intros ?? EQ ??-> ?? ->. apply EQ. Qed.
  Global Instance ty_ghost_drop_proper : Proper ((≡) ==> eq ==> eq ==> (≡)) ty_ghost_drop.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.
  Lemma ty_ghost_drop_entails ty1 ty2 π r :
    ty1 ≡@{type rt} ty2 →
    ty_ghost_drop ty1 π r -∗
    ty_ghost_drop ty2 π r.
  Proof. intros [_ _ _ _ -> _]; eauto. Qed.

  Instance ty_sidecond_ne n:
    Proper (dist n ==> dist n) ty_sidecond.
  Proof. intros ?? EQ. apply EQ. Qed.
  Instance ty_sidecond_proper : Proper ((≡) ==> (≡)) ty_sidecond.
  Proof. intros ?? EQ. apply EQ. Qed.
  Lemma ty_sidecond_entails ty1 ty2:
    ty1 ≡@{type rt} ty2 →
    ty_sidecond ty1 -∗
    ty_sidecond ty2.
  Proof. intros [? ? ? ? ? ? -> ]; eauto. Qed.

  Instance ty_syn_type_ne n : Proper (dist n ==> eq ==> eq) ty_syn_type.
  Proof. intros ?? EQ ??->. apply EQ. Qed.
  Instance ty_syn_type_proper : Proper ((≡) ==> eq ==> eq) ty_syn_type.
  Proof. intros ?? EQ ??->  . apply EQ. Qed.

  Instance ty_wf_E_ne n : Proper (dist n ==> eq) ty_wf_E.
  Proof. intros ?? EQ. apply EQ. Qed.
  Instance ty_wf_E_proper : Proper ((≡) ==> eq) ty_wf_E.
  Proof. intros ?? EQ. apply EQ. Qed.

  Instance ty_lfts_ne n : Proper (dist n ==> eq) ty_lfts.
  Proof. intros ?? EQ. apply EQ. Qed.
  Instance ty_lfts_proper : Proper ((≡) ==> eq) ty_lfts.
  Proof. intros ?? EQ. apply EQ. Qed.


  (*
  Local Ltac intro_T :=
        intros [[[[[[[[T_inh T_own_val] T_shr ] T_syn_type] T_ot] T_sidecond] T_drop] T_lfts] T_wf_E].
  Global Instance type_cofe : Cofe typeO.
  Proof.
    apply (iso_cofe_subtype' P type_pack type_unpack).
    - intros []; simpl; rewrite /type_unpack/=. rewrite ty_has_op_type_unfold. done.
    - intros ? t1 t2. split.
      + destruct 1 as [[Heq1 [Heq2 Heq3]] ? ? ? ? ? ? ? ?].
        repeat split_and!; simpl; try done.
        clear -Heq1 Heq2 Heq3.
        unfold dist, ofe_dist, discrete_dist.
        unfold equiv, ofe_equiv, equivL.
        destruct t1 as [ ? ? [inh1]], t2 as [ ? ? [inh2]]; simpl in *; clear -Heq1 Heq2 Heq3.
        subst. done.
      + intros [[[[[[[[Heq1]]]]]]]]; simpl in *.
        constructor; try done.
        specialize (eq_sigT_fst Heq1) as Heq2.
        exists Heq2.
        destruct t1 as [ ? ? [inh1]], t2 as [ ? ? [inh2]]; simpl in *; clear -Heq1 Heq2.
        subst.
        apply existT_inj in Heq1. simplify_eq. done.
    - intros [[[[[[[[[? [xt xrt]]]]]]]]]] Hx; rewrite /type_unpack/=.
      rewrite ty_has_op_type_unfold; done.
    - repeat apply limit_preserving_and; repeat (apply limit_preserving_forall; intros ?).
      + apply bi.limit_preserving_emp_valid => n ty1 ty2. intro_T; f_equiv;
        [ apply T_own_val | f_equiv; rewrite T_syn_type; done].
      + apply limit_preserving_impl.
        { intros ty1 ty2; intro_T. intros ?. by apply T_ot. }
        { apply limit_preserving_discrete. intros ty1 ty2; intro_T. by rewrite T_syn_type. }
      + apply bi.limit_preserving_emp_valid => n ty1 ty2; intro_T; f_equiv; last done. apply T_own_val.
      + apply bi.limit_preserving_emp_valid => n ty1 ty2; intro_T; f_equiv; last done. apply T_shr.
      + apply bi.limit_preserving_Persistent => n ty1 ty2; intro_T. apply T_shr.
      + apply bi.limit_preserving_emp_valid => n ty1 ty2; intro_T; f_equiv.
        { apply T_shr. }
        { f_equiv. by rewrite T_syn_type. }
      + apply bi.limit_preserving_emp_valid => n ty1 ty2.
        intro_T. f_equiv. simpl. f_equiv. { rewrite T_lfts. done. }
        f_equiv. { by rewrite T_syn_type. }
        f_equiv. f_equiv. f_equiv. { repeat f_equiv; apply T_own_val. }

        apply logical_step_ne.
        f_equiv; first apply T_shr.
        rewrite T_lfts. done.
      + apply bi.limit_preserving_emp_valid => n ty1 ty2; simpl.
        intro_T. f_equiv. f_equiv; apply T_shr.
      + apply bi.limit_preserving_emp_valid => n ty1 ty2; intro_T; f_equiv.
        { apply T_own_val. }
        apply logical_step_ne. apply T_drop.
      + apply limit_preserving_impl.
        { intros ty1 ty2. intro_T. intros ?. by apply T_ot. }
        destruct y0.
        * apply bi.limit_preserving_emp_valid => n ty1 ty2. intro_T. f_equiv.
          apply T_own_val.
        * apply bi.limit_preserving_emp_valid => n ty1 ty2; intro_T; f_equiv;
          apply T_own_val.
        * apply bi.limit_preserving_emp_valid => n ty1 ty2; intro_T; f_equiv;
          apply T_own_val.
    (*
      + apply limit_preserving_impl.
        { intros ty1 ty2; intro_T. intros ?. by rewrite -T_syn_type. }
        apply limit_preserving_impl.
        { intros ? ?; intro_T. done. }
        apply limit_preserving_discrete. intros ty1 ty2; intro_T.
        intros ?. by apply T_ot.
        *)
      + apply bi.limit_preserving_entails => n ty1 ty2; intro_T; f_equiv; done.
      + apply bi.limit_preserving_Persistent => n ty1 ty2; intro_T. apply T_sidecond.
  Qed.
   *)
End ofe.
Section st_ofe.
  Context `{!typeGS Σ}.
  Context {rt : RT}.

  Inductive st_equiv' (ty1 ty2 : simple_type rt) : Prop :=
    St_equiv :
      (∀ ot mt, ty_has_op_type ty1 ot mt ↔ ty_has_op_type ty2 ot mt) →
      (∀ π r vs, ty1.(st_own) π r vs ≡ ty2.(st_own) π r vs) →
      (ty1.(st_syn_type) = ty2.(st_syn_type)) →
      st_equiv' ty1 ty2.
  Local Instance st_equiv : Equiv (simple_type rt) := st_equiv'.

  Inductive st_dist' (n : nat) (ty1 ty2 : simple_type rt) : Prop :=
    St_dist :
      (∀ ot mt, ty_has_op_type ty1 ot mt ↔ ty_has_op_type ty2 ot mt) →
      (∀ π r vs, ty1.(st_own) π r vs ≡{n}≡ (ty2.(st_own) π r vs)) →
      (ty1.(st_syn_type) = ty2.(st_syn_type)) →
      st_dist' n ty1 ty2.
  Local Instance st_dist : Dist (simple_type rt) := st_dist'.

  (* type rt is isomorphic to { x : T | P x } *)
  Let T :=
    prodO (prodO
      (thread_id -d> rt -d> val -d> iPropO Σ)
      (syn_typeO))
      (op_type -d> leibnizO memcast_compat_type -d> PropO).
  Let P (x : T) : Prop :=
    (* st_has_layout *)
    (∀ π r v, x.1.1 π r v -∗ ∃ ly : layout, ⌜syn_type_has_layout x.1.2 ly⌝ ∗ ⌜v `has_layout_val` ly⌝) ∧
    (* ty_op_type_stable *)
    (∀ ot mt, x.2 ot mt → syn_type_has_layout x.1.2 (ot_layout ot)) ∧
    (* ty_shr_persistent *)
    (∀ π r v, Persistent (x.1.1 π r v)) ∧
    (* ty_memcast_compat *)
    (∀ ot mt st π r v, x.2 ot mt → x.1.1 π r v -∗
      match mt with | MCNone => True | MCCopy => x.1.1 π r (mem_cast v ot st) | MCId => ⌜mem_cast_id v ot⌝ end).

  (* to handle the let destruct in an acceptable way *)
  Local Set Program Cases.

  Definition simple_type_unpack (ty : simple_type rt) : T :=
    ( ty.(st_own),
     ty.(st_syn_type),
     ty_has_op_type ty).
  (*Program Definition simple_type_pack (x : T) (H : P x) : simple_type rt :=*)
    (*let '(T_inh, T_own_val, T_syn_type, T_ot) := x in*)
    (*{|*)
      (*st_rt_inhabited := populate T_inh;*)
      (*st_own := T_own_val;*)
      (*st_has_op_type := T_ot;*)
      (*st_syn_type := T_syn_type;*)
    (*|}.*)
  (*Solve Obligations with*)
    (*intros [[[T_inh T_own_val] T_syn_type] T_ot];*)
    (*intros (? & ? & ? & ?);*)
    (*intros ???? Heq; injection Heq; intros -> -> -> ->;*)
    (*done.*)

  Definition simple_type_ofe_mixin : OfeMixin (simple_type rt).
  Proof.
    apply (iso_ofe_mixin simple_type_unpack).
    - intros t1 t2. split.
      + destruct 1. done.
      + intros [[]]; simpl in *.
        by constructor.
    - intros t1 t2. split.
      + destruct 1. done.
      + intros [[]]; simpl in *.
        by constructor.
  Qed.
  Canonical Structure stO : ofe := Ofe (simple_type rt) simple_type_ofe_mixin.

  Global Instance st_own_ne n :
    Proper (dist n ==> eq ==> eq ==> eq ==> dist n) st_own.
  Proof. intros ?? EQ ??-> ??-> ??->. apply EQ. Qed.
  Global Instance st_own_proper : Proper ((≡) ==> eq ==> eq ==> eq ==> (≡)) st_own.
  Proof. intros ?? EQ ??-> ??-> ??->. apply EQ. Qed.

  Global Instance st_syn_type_ne n : Proper (dist n ==> eq) st_syn_type.
  Proof. intros ?? EQ. apply EQ. Qed.
  Global Instance st_syn_type_proper : Proper ((≡) ==> eq) st_syn_type.
  Proof. intros ?? EQ. apply EQ. Qed.

  Global Instance ty_of_st_ne : NonExpansive (ty_of_st rt).
  Proof.
    intros n ?? EQ. constructor; try apply EQ; try done.
    - simpl. intros. unfold ty_own_val; simpl.
      do 2 f_equiv. done.
    - simpl. intros. unfold ty_shr; simpl.
      do 7 f_equiv.
      { f_equiv. apply EQ. }
      do 3 f_equiv. apply EQ.
    - intros. unfold ty_syn_type; simpl. apply EQ.
    - rewrite ty_lfts_unfold. done.
    - rewrite ty_wf_E_unfold. done.
  Qed.
  Global Instance ty_of_st_proper : Proper ((≡) ==> (≡)) (ty_of_st rt).
  Proof. apply (ne_proper _). Qed.

End st_ofe.

(**
  In order for us to be able to take a fixpoint of a type functor, the functor's lifetime requirements need to become constant after a few iterations of the functor.
   We cannot express this simply by requiring idempotence, as we also need to allow to compose functors of different types.
   Hence, we express this as the following syntactic requirements.

   This approach is inspired by RustHornBelt [https://gitlab.mpi-sws.org/iris/lambda-rust/-/blob/9e137e44215b2601c2cdf5433a8aa4646b11a0ce/theories/typing/type.v].
 *)
Section lft_morph.
  Context `{!typeGS Σ}.

  (* The functor has constant lifetime requirements *)
  Record TyLftMorphismConst {rt1 rt2} (F : type rt1 → type rt2) : Type := mk_lft_morph_const {
    ty_lft_morph_const_α : lft;
    ty_lft_morph_const_E : elctx;
    ty_lft_morph_const_lfts :
      ⊢ ∀ ty, lft_equiv (lft_intersect_list (ty_lfts (F ty))) ty_lft_morph_const_α;
    ty_lft_morph_const_wf_E :
      ∀ ty, elctx_interp (ty_wf_E (F ty)) ≡ elctx_interp ty_lft_morph_const_E;
  }.
  Existing Class TyLftMorphismConst.
  Global Arguments mk_lft_morph_const {_ _ _}.
  Global Arguments ty_lft_morph_const_lfts {_ _ _ _}.
  Global Arguments ty_lft_morph_const_wf_E {_ _ _ _}.

  (* An application of the functor adds some lifetime requirements which are essentially constant *)
  Record TyLftMorphismAdd {rt1 rt2} (F : type rt1 → type rt2) : Type := mk_lft_morph_add {
    ty_lft_morph_add_α : lft;
    ty_lft_morph_add_E : elctx;
    ty_lft_morph_add_βs : list lft;
    ty_lft_morph_add_lfts :
      ⊢ ∀ ty, lft_equiv (lft_intersect_list (ty_lfts (F ty))) (ty_lft_morph_add_α ⊓ lft_intersect_list (ty_lfts ty));
    ty_lft_morph_add_wf_E :
      ∀ ty, elctx_interp (ty_wf_E (F ty)) ≡
          (elctx_interp ty_lft_morph_add_E ∗ elctx_interp (ty_wf_E ty) ∗
            (* some requirements of lifetimes that the type has to outlive *)
            [∗ list] β ∈ ty_lft_morph_add_βs, β ⊑ lft_intersect_list (ty_lfts ty))%I;
  }.
  Existing Class TyLftMorphismAdd.
  Global Arguments mk_lft_morph_add {_ _ _}.
  (*Global Arguments ty_lft_morph_add_lfts {_ _ _ _}.*)
  (*Global Arguments ty_lft_morph_add_wf_E {_ _ _ _}.*)

  Inductive TyLftMorphism {rt1 rt2} (F : type rt1 → type rt2) : Type :=
  | ty_lft_morph_const (_ : TyLftMorphismConst F)
  | ty_lft_morph_add (_ : TyLftMorphismAdd F)
  .
  Existing Class TyLftMorphism.

  Global Instance TyLftMorphism_compose {rt1 rt2 rt3} (F1 : type rt1 → type rt2) (F2 : type rt2 → type rt3) :
    TyLftMorphism F1 →
    TyLftMorphism F2 →
    TyLftMorphism (F2 ∘ F1).
  Proof.
    intros X1 [C2 | A2].
    { apply ty_lft_morph_const.
      refine (mk_lft_morph_const (C2.(ty_lft_morph_const_α _)) C2.(ty_lft_morph_const_E _) _ _).
      - simpl. iIntros (?). iApply ty_lft_morph_const_lfts.
      - simpl. iIntros (?). iApply ty_lft_morph_const_wf_E. }
    destruct X1 as [C1 | A1].
    - apply ty_lft_morph_const.
      refine (mk_lft_morph_const (A2.(ty_lft_morph_add_α _) ⊓ C1.(ty_lft_morph_const_α _))
      (A2.(ty_lft_morph_add_E _) ++ C1.(ty_lft_morph_const_E _) ++ ((λ β, β ⊑ₑ C1.(ty_lft_morph_const_α _)) <$> A2.(ty_lft_morph_add_βs _))) _ _).
      + simpl. iIntros (?).
        iApply lft_equiv_trans. { iApply ty_lft_morph_add_lfts. }
        iApply lft_equiv_intersect; first iApply lft_equiv_refl.
        iApply lft_equiv_trans.
        { iApply ty_lft_morph_const_lfts. }
        iApply lft_equiv_refl.
      + simpl. iIntros (?).
        etrans. { iApply ty_lft_morph_add_wf_E. }
        rewrite !elctx_interp_app.
        f_equiv; first done.
        f_equiv. { apply ty_lft_morph_const_wf_E. }
        unfold elctx_interp.
        rewrite big_sepL_fmap.
        apply big_sepL_proper.
        unfold elctx_elt_interp; simpl.
        intros ???.
        apply lft_incl_proper; first apply lft_equiv_refl.
        iApply ty_lft_morph_const_lfts.
    - apply ty_lft_morph_add.
      refine (mk_lft_morph_add (A2.(ty_lft_morph_add_α _) ⊓ A1.(ty_lft_morph_add_α _))
      (A2.(ty_lft_morph_add_E _) ++ A1.(ty_lft_morph_add_E _) ++ ((λ β, β ⊑ₑ A1.(ty_lft_morph_add_α _)) <$> (ty_lft_morph_add_βs F2 A2)))
        (A2.(ty_lft_morph_add_βs _) ++ A1.(ty_lft_morph_add_βs _))
        _ _).
      + simpl. iIntros (?).
        iApply lft_equiv_trans. { iApply ty_lft_morph_add_lfts. }
        rewrite -lft_intersect_assoc.
        iApply lft_equiv_intersect; first iApply lft_equiv_refl.
        iApply ty_lft_morph_add_lfts.
      + simpl. iIntros (?).
        rewrite !elctx_interp_app.
        rewrite -assoc.
        etrans. { iApply ty_lft_morph_add_wf_E. }
        f_equiv; first done.
        etrans. { apply bi.sep_proper; last done. apply ty_lft_morph_add_wf_E. }
        rewrite -!assoc.
        f_equiv.
        iSplit.
        * iIntros "(? & ? & Ha)". iFrame.
          unfold elctx_interp. rewrite big_sepL_fmap.
          iApply big_sepL_sep.
          iApply (big_sepL_impl with "Ha"). iModIntro. iIntros (???).
          rewrite /elctx_elt_interp/=.
          iIntros "#Ha". iSplit; iApply (lft_incl_trans with "Ha").
          all: iApply lft_incl_trans; first (iApply lft_equiv_incl_l; iApply ty_lft_morph_add_lfts).
          { iApply lft_intersect_incl_l. }
          { iApply lft_intersect_incl_r. }
        * rewrite big_sepL_app.
          iIntros "(Hb & ? & Ha & ?)". iFrame.
          unfold elctx_interp. rewrite big_sepL_fmap.
          iCombine "Ha Hb" as "Ha".
          rewrite -big_sepL_sep.
          iApply (big_sepL_impl with "Ha"). iModIntro. iIntros (???).
          rewrite /elctx_elt_interp/=.
          iIntros "#[Ha Hb]".
          (*iSplit; iApply (lft_incl_trans with "Ha").*)
          iApply lft_incl_trans; last (iApply lft_equiv_incl_r; iApply ty_lft_morph_add_lfts).
          iApply lft_incl_glb; done.
          Unshelve. apply _.
  Qed.

  Lemma TyLftMorphism_ty_lfts_proper {rt1 rt2} (F : type rt1 → type rt2) `{HF : !TyLftMorphism F} ty ty' :
    (⊢ lft_equiv (lft_intersect_list (ty_lfts ty)) (lft_intersect_list (ty_lfts ty'))) →
    ⊢ lft_equiv (lft_intersect_list (ty_lfts (F ty))) (lft_intersect_list (ty_lfts (F ty'))).
  Proof.
    intros Ha.
    destruct HF as [HF | HF].
    - iApply lft_equiv_trans. { iApply ty_lft_morph_const_lfts. }
      iApply lft_equiv_sym. iApply lft_equiv_trans. { iApply ty_lft_morph_const_lfts. }
      iApply lft_equiv_refl.
    - iApply lft_equiv_trans. { iApply ty_lft_morph_add_lfts. }
      iApply lft_equiv_sym. iApply lft_equiv_trans. { iApply ty_lft_morph_add_lfts. }
      iApply lft_equiv_intersect; first iApply lft_equiv_refl.
      iApply lft_equiv_sym. done.
      Unshelve. apply _.
  Qed.
  Lemma TyLftMorphism_ty_wf_E_proper {rt1 rt2} (F : type rt1 → type rt2) `{HF : !TyLftMorphism F} ty ty' :
    elctx_interp (ty_wf_E ty) ≡ elctx_interp (ty_wf_E ty') →
    (⊢ lft_equiv (lft_intersect_list (ty_lfts ty)) (lft_intersect_list (ty_lfts ty'))) →
    elctx_interp (ty_wf_E (F ty)) ≡ elctx_interp (ty_wf_E (F ty')).
  Proof.
    intros Heq Heq2. destruct HF as [HF | HF].
    - etrans. { iApply ty_lft_morph_const_wf_E. }
      symmetry. apply ty_lft_morph_const_wf_E.
    - etrans. { iApply ty_lft_morph_add_wf_E. }
      symmetry. etrans. { iApply ty_lft_morph_add_wf_E. }
      rewrite Heq.
      f_equiv; first done.
      f_equiv.
      f_equiv. intros ??. apply lft_incl_proper; first apply lft_equiv_refl.
      iApply lft_equiv_sym. iApply Heq2.
      Unshelve. apply _.
  Qed.

  (* Key property needed for recursive types -- the lifetimes become constant after one iteration. *)
  Lemma TyLftMorphism_ty_lfts_idempotent {rt} (F : type rt → type rt) `{HF : !TyLftMorphism F} ty :
    ⊢ lft_equiv (lft_intersect_list (ty_lfts (F (F ty)))) (lft_intersect_list (ty_lfts (F ty))).
  Proof.
    destruct HF as [ HF | HF].
    - iApply lft_equiv_trans. { iApply ty_lft_morph_const_lfts. }
      iApply lft_equiv_sym. iApply ty_lft_morph_const_lfts.
    - iApply lft_equiv_trans. { iApply ty_lft_morph_add_lfts. }
      iApply lft_equiv_trans. {
        iApply lft_equiv_intersect; first iApply lft_equiv_refl.
        iApply ty_lft_morph_add_lfts. }
      rewrite assoc.
      iApply lft_equiv_sym. iApply lft_equiv_trans. { iApply ty_lft_morph_add_lfts. }
      iApply lft_equiv_intersect; last iApply lft_equiv_refl.
      iApply lft_intersect_idempotent.
      Unshelve. apply _.
  Qed.
  (* Same for [ty_wf_E].
     Here, we need two iterations for a fixpoint, as the outlives requirements are only stable after two iterations. *)
  Lemma TyLftMorphism_ty_wf_E_idempotent {rt} (F : type rt → type rt) `{HF : !TyLftMorphism F} ty :
    elctx_interp (ty_wf_E (F (F (F ty)))) ≡ elctx_interp (ty_wf_E (F (F ty))).
  Proof.
    destruct HF as [ HF | HF].
    - etrans. { apply ty_lft_morph_const_wf_E. }
      symmetry. apply ty_lft_morph_const_wf_E.
    - rewrite !ty_lft_morph_add_wf_E.
      rewrite -!assoc.
      iSplit.
      { iIntros "(? & _ & ? & ? & ? & ? & ?)". iFrame. }
      { iIntros "(#? & _ & ? & #Hb & #Hc)".
        iFrame "# ∗".
        iApply (big_sepL_impl with "Hc").
        iModIntro. iIntros (???) "Hincl".
        iApply (lft_incl_trans with "Hincl").
        rewrite lft_incl_proper; [ | iApply ty_lft_morph_add_lfts | ].
        2: { iApply lft_equiv_trans; first iApply ty_lft_morph_add_lfts.
          iApply lft_equiv_intersect; first iApply lft_equiv_refl.
          iApply ty_lft_morph_add_lfts. }
        rewrite assoc.
        iApply lft_intersect_mono; last iApply lft_incl_refl.
        iApply lft_incl_glb; iApply lft_incl_refl.
        Unshelve. apply _.
      }
  Qed.

  Lemma elctx_interp_nil :
    elctx_interp [] ≡ True%I.
  Proof. done. Qed.

  (* Constructors *)
  Lemma ty_lft_morph_make_id {rt1 rt2} (F : type rt1 → type rt2) :
    (∀ ty, ty_lfts (F ty) = ty_lfts ty) →
    (∀ ty, (ty_wf_E (F ty)) = (ty_wf_E ty)) →
    TyLftMorphism F.
  Proof.
    intros Hlfts HwfE. eapply ty_lft_morph_add.
    apply (mk_lft_morph_add static [] []).
    - iIntros (ty). rewrite left_id. rewrite Hlfts. iApply lft_equiv_refl.
    - intros ty. rewrite HwfE. simpl. rewrite right_id.
      rewrite elctx_interp_nil left_id//.
  Qed.

  Lemma ty_lft_morph_make_ref {rt1 rt2} (F : type rt1 → type rt2) α :
    (∀ ty, ty_lfts (F ty) = α :: (ty_lfts ty)) →
    (∀ ty, (ty_wf_E (F ty)) = (ty_wf_E ty) ++ ty_outlives_E ty α) →
    TyLftMorphism F.
  Proof.
    intros Hlfts HwfE. eapply ty_lft_morph_add.
    apply (mk_lft_morph_add α [] [α]).
    - iIntros (ty). rewrite Hlfts. iApply lft_equiv_refl.
    - intros ty. rewrite HwfE. simpl. rewrite right_id.
      rewrite elctx_interp_app elctx_interp_nil left_id//.
      f_equiv.
      rewrite /ty_outlives_E lfts_outlives_E_fmap /elctx_interp/elctx_elt_interp big_sepL_fmap/=.
      generalize (ty_lfts ty) as l.
      induction l as [ | ? l IH]; simpl.
      { iSplit; last eauto. iIntros "_". iApply lft_incl_static. }
      rewrite IH. iSplit.
      + iIntros "#[? ?]". iApply lft_incl_glb; done.
      + iIntros "#Ha".
        iSplit; iApply (lft_incl_trans with "Ha"); [iApply lft_intersect_incl_l | iApply lft_intersect_incl_r].
  Qed.

  Lemma ty_lft_morph_make_const {rt1 rt2} (F : type rt1 → type rt2) α E :
    (∀ ty, ty_lfts (F ty) = α) →
    (∀ ty, (ty_wf_E (F ty)) = E) →
    TyLftMorphism F.
  Proof.
    intros Hlfts HwfE. eapply ty_lft_morph_const.
    apply (mk_lft_morph_const (lft_intersect_list α) E).
    - iIntros (ty). rewrite Hlfts. iApply lft_equiv_refl.
    - intros ty. rewrite HwfE. done.
  Qed.
End lft_morph.

Definition dist_later_2 {A : Type} `{!Dist A} (n : nat) (a b : A) : Prop :=
  ∀ m, (S m < n)%nat → a ≡{m}≡ b.
Global Typeclasses Opaque dist_later_2.
Lemma dist_later_2_lt {A : Type} `{!Dist A} (n : nat) (a b : A) :
  dist_later_2 n a b →
  ∀ m, (S m < n)%nat → a ≡{m}≡ b.
Proof.
  done.
Qed.
Lemma dist_later_2_intro {A : Type} `{!Dist A} (n : nat) (a b : A) :
  (∀ m, (S m < n)%nat → a ≡{m}≡ b) →
  dist_later_2 n a b.
Proof. done. Qed.
Ltac dist_later_2_intro :=
  refine (dist_later_2_intro _ _ _ _);
  intros ??.

Ltac unfold_sidx :=
  repeat match goal with
  | H : (_ < _)%sidx |- _ =>
      unfold sidx_lt, natSI in H
  end;
  try match goal with
  | |- (_ < _)%sidx =>
      unfold sidx_lt, natSI
  end
.


Lemma dist_later_fin_lt {A : Type} `{!Dist A} (n : nat) (x y : A) :
  dist_later n x y → ∀ m : nat, (m < n)%nat → x ≡{m}≡ y.
Proof.
  intros ? m Hlt.
  eapply dist_later_lt; first done.
  unfold_sidx. lia.
Qed.
Lemma dist_later_mono {A : Type} `{!Dist A} (m n : nat) (x y : A) :
  dist_later n x y →
  m ≤ n →
  dist_later m x y.
Proof.
  intros Hd Hle.
  econstructor.
  intros ??. eapply Hd.
  simpl in *. lia.
Qed.

Class TypeDist `{!typeGS Σ} {rt} (n : nat) (ty1 ty2 : type rt) : Prop := {
  type_dist_st m :
    ty1.(ty_syn_type) m = ty2.(ty_syn_type) m;
  type_dist_sc :
    ty1.(ty_sidecond) ≡ ty2.(ty_sidecond);
  (*type_dist_ot : *)
    (*(∀ ot mt, ty_has_op_type ty1 ot mt ↔ ty_has_op_type ty2 ot mt);*)
  type_dist_own_val :
    (∀ π r m v, (v ◁ᵥ{π, m} r @ ty1 ≡{n}≡ v ◁ᵥ{π, m} r @ ty2)%I);
  type_dist_shr :
    (∀ κ π r m l, (l ◁ₗ{π, m, κ} r @ ty1 ≡{n}≡ l ◁ₗ{π, m, κ} r @ ty2)%I);
  type_dist_ghost_drop :
    (∀ π r, (ty_ghost_drop ty1 π r ≡{n}≡ ty_ghost_drop ty2 π r)%I);
}.
Class TypeDist2 `{!typeGS Σ} {rt} (n : nat) (ty1 ty2 : type rt) : Prop := {
  type_dist2_st m :
    ty1.(ty_syn_type) m = ty2.(ty_syn_type) m;
  type_dist2_sc :
    ty1.(ty_sidecond) ≡ ty2.(ty_sidecond);
  (*type_dist_ot : *)
    (*(∀ ot mt, ty_has_op_type ty1 ot mt ↔ ty_has_op_type ty2 ot mt);*)
  type_dist2_own_val :
    (∀ π r m v, dist_later n (v ◁ᵥ{π, m} r @ ty1)%I (v ◁ᵥ{π, m} r @ ty2)%I);
  type_dist2_shr :
    (∀ κ π r m l, (l ◁ₗ{π, m, κ} r @ ty1 ≡{n}≡ l ◁ₗ{π, m, κ} r @ ty2)%I);
  type_dist2_ghost_drop :
    (∀ π r, dist_later n (ty_ghost_drop ty1 π r) (ty_ghost_drop ty2 π r)%I);
}.
Class TypeDistLater `{!typeGS Σ} {rt} (n : nat) (ty1 ty2 : type rt) : Prop := {
  type_dist_later_st m :
    ty1.(ty_syn_type) m = ty2.(ty_syn_type) m;
  type_dist_later_sc :
    ty1.(ty_sidecond) ≡ ty2.(ty_sidecond);
  (*type_dist_ot : *)
    (*(∀ ot mt, ty_has_op_type ty1 ot mt ↔ ty_has_op_type ty2 ot mt);*)
  type_dist_later_own_val :
    (∀ π r m v, dist_later n (v ◁ᵥ{π, m} r @ ty1)%I (v ◁ᵥ{π, m} r @ ty2)%I);
  type_dist_later_shr :
    (∀ κ π r m l, dist_later n (l ◁ₗ{π, m, κ} r @ ty1)%I (l ◁ₗ{π, m, κ} r @ ty2)%I);
  type_dist_later_ghost_drop :
    (∀ π r, dist_later n (ty_ghost_drop ty1 π r) (ty_ghost_drop ty2 π r)%I);
}.
Class TypeDistLater2 `{!typeGS Σ} {rt} (n : nat) (ty1 ty2 : type rt) : Prop := {
  type_dist_later2_st m :
    ty1.(ty_syn_type) m = ty2.(ty_syn_type) m;
  type_dist_later2_sc :
    ty1.(ty_sidecond) ≡ ty2.(ty_sidecond);
  (*type_dist_ot : *)
    (*(∀ ot mt, ty_has_op_type ty1 ot mt ↔ ty_has_op_type ty2 ot mt);*)
  type_dist_later2_own_val :
    (∀ π r m v, dist_later_2 n (v ◁ᵥ{π, m} r @ ty1)%I (v ◁ᵥ{π, m} r @ ty2)%I);
  type_dist_later2_shr :
    (∀ κ π r m l, dist_later n (l ◁ₗ{π, m, κ} r @ ty1)%I (l ◁ₗ{π, m, κ} r @ ty2)%I);
  type_dist_later2_ghost_drop :
    (∀ π r, dist_later_2 n (ty_ghost_drop ty1 π r) (ty_ghost_drop ty2 π r)%I);
}.
Global Instance type_dist_later `{!typeGS Σ} {rt} (n : nat) (ty1 ty2 : type rt) :
  TypeDist (Nat.pred n) ty1 ty2 → TypeDistLater n ty1 ty2.
Proof.
  intros [? ? ? ?].
  constructor; [done.. | | | ].
  - intros. dist_later_fin_intro. eapply dist_le; first done. lia.
  - intros. dist_later_fin_intro. eapply dist_le; first done. lia.
  - intros. dist_later_fin_intro. eapply dist_le; first done. lia.
Qed.
Global Instance type_dist2_dist_later `{!typeGS Σ} {rt} (n m : nat) (ty1 ty2 : type rt) :
  TCFastDone (TypeDist2 m ty1 ty2) → CanSolve (n ≤ m) → TypeDistLater n ty1 ty2.
Proof.
  rewrite /TCFastDone/CanSolve.
  intros [? ? ? ?] Hle. constructor; [done.. | | | ].
  - intros. dist_later_fin_intro. eapply dist_later_lt; first done.
    unfold_sidx. lia.
  - intros. dist_later_fin_intro. eapply dist_le; first done. lia.
  - intros. eapply dist_later_mono; first done. done.
Qed.
Global Instance type_dist_le `{!typeGS Σ} {rt} (n m : nat) (ty1 ty2 : type rt) :
  TCFastDone (TypeDist n ty1 ty2) → CanSolve (m ≤ n) → TypeDist m ty1 ty2 | 100.
Proof.
  rewrite /CanSolve. intros [? ? ? ?] Hle. constructor; [done.. | | | ].
  - intros. eapply dist_le; first done. lia.
  - intros. eapply dist_le; first done. lia.
  - intros. eapply dist_le; first done. lia.
Qed.
Global Instance type_dist_dist2 `{!typeGS Σ} {rt} (n : nat) (ty1 ty2 : type rt) :
  TypeDist n ty1 ty2 → TypeDist2 n ty1 ty2 | 50.
Proof.
  intros [? ? ? ?].
  constructor; [done.. | | | ].
  - intros. dist_later_fin_intro. eapply dist_le; first done. lia.
  - intros. done.
  - intros. dist_later_fin_intro. eapply dist_le; first done. lia.
Qed.
Lemma type_dist2_dist `{!typeGS Σ} {rt} (n m : nat) (ty1 ty2 : type rt) :
  TypeDist2 n ty1 ty2 →
  CanSolve (m < n) →
  TypeDist m ty1 ty2.
Proof.
  rewrite /CanSolve. intros [? ? ? ?] Hle. constructor; [done.. | | | ].
  - intros. eapply dist_later_fin_lt; first done. lia.
  - intros. eapply dist_le; first done. lia.
  - intros. eapply dist_later_fin_lt; first done. lia.
Qed.
Global Instance type_dist2_le `{!typeGS Σ} {rt} (n m : nat) (ty1 ty2 : type rt) :
  TCFastDone (TypeDist2 n ty1 ty2) →
  CanSolve (m ≤ n) →
  TypeDist2 m ty1 ty2 | 100.
Proof.
  rewrite /CanSolve. intros [? ? ? ?] Hle. constructor; [done.. | | | ].
  - intros. dist_later_fin_intro.
    eapply dist_later_fin_lt; first done. lia.
  - intros. eapply dist_le; first done. lia.
  - intros. dist_later_fin_intro.
    eapply dist_later_fin_lt; first done. lia.
Qed.
Global Instance type_dist2_later `{!typeGS Σ} {rt} (n : nat) (ty1 ty2 : type rt) :
  TypeDist2 (Nat.pred n) ty1 ty2 → TypeDistLater2 n ty1 ty2.
Proof.
  intros [? ? ? ?].
  constructor; [done.. | | | ].
  - intros. dist_later_2_intro.
    eapply dist_later_fin_lt; first done. lia.
  - intros. dist_later_fin_intro.
    eapply dist_le; first done. lia.
  - intros. dist_later_2_intro.
    eapply dist_later_fin_lt; first done. lia.
Qed.
Global Instance type_dist_later2_dist2 `{!typeGS Σ} {rt} (n m : nat) (ty1 ty2 : type rt) :
  TCFastDone (TypeDistLater2 n ty1 ty2) →
  CanSolve (m < n) →
  TypeDist2 m ty1 ty2.
Proof.
  unfold CanSolve. intros [? ? ? ?] Hle.
  constructor; [done.. | | | ].
  - intros. dist_later_fin_intro.
    eapply dist_later_2_lt; first done. lia.
  - intros. eapply dist_later_fin_lt; first done. lia.
  - intros. dist_later_fin_intro.
    eapply dist_later_2_lt; first done. lia.
Qed.
Lemma type_dist_later_dist `{!typeGS Σ} {rt} (n m : nat) (ty1 ty2 : type rt) :
  TypeDistLater n ty1 ty2 →
  CanSolve (m < n) →
  TypeDist m ty1 ty2.
Proof.
  rewrite /CanSolve.
  intros [? ? ? ?] ?. constructor; [done.. | | | ].
  - intros. eapply dist_later_fin_lt; first done. lia.
  - intros. eapply dist_later_fin_lt; first done. lia.
  - intros. eapply dist_later_fin_lt; first done. lia.
Qed.

Class TypeNonExpansive `{!typeGS Σ} {rt1 rt2} (F : type rt1 → type rt2) : Type := {
  type_ne_metadata :
    ∀ ty ty',
      ty.(ty_metadata_kind) = ty'.(ty_metadata_kind) →
      (F ty).(ty_metadata_kind) = (F ty').(ty_metadata_kind);

  type_ne_syn_type :
    ∀ ty ty',
      (∀ m, ty.(ty_syn_type) m = ty'.(ty_syn_type) m) →
      ∀ m, (F ty).(ty_syn_type) m = (F ty').(ty_syn_type) m;

  type_ne_lft_mor :: TyLftMorphism F;

  (*type_ne_lfts :*)
    (*∀ ty ty', *)
      (*(⊢ lft_equiv (lft_intersect_list ty.(ty_lfts)) (lft_intersect_list ty'.(ty_lfts))) →*)
      (*(⊢ lft_equiv (lft_intersect_list (F ty).(ty_lfts)) (lft_intersect_list (F ty').(ty_lfts)));*)
  (* doesn't work, because the functor goes between different types *)
  (*type_ne_lfts_idemp :*)
    (*∀ ty,*)
      (*lft_equiv (lft_intersect_list (F (F ty)).(ty_lfts)) (lft_intersect_list (F ty).(ty_lfts));*)

  type_ne_has_op_type :
    ∀ ty ty',
      (∀ m, ty_syn_type ty m = ty_syn_type ty' m) →
      (∀ ot mt, ty_has_op_type ty ot mt ↔ ty_has_op_type ty' ot mt) →
      (∀ ot mt, ty_has_op_type (F ty) ot mt ↔ ty_has_op_type (F ty') ot mt);

  type_ne_sidecond :
    ∀ ty ty',
      (∀ m, ty.(ty_syn_type) m = ty'.(ty_syn_type) m) →
      ty_sidecond ty ≡ ty_sidecond ty' →
      ty_sidecond (F ty) ≡ ty_sidecond (F ty');

  type_ne_own_val :
    ∀ n ty ty',
      TypeDist n ty ty' →
      (∀ π r m v, (v ◁ᵥ{π, m} r @ F ty ≡{n}≡ v ◁ᵥ{π, m} r @ F ty')%I);

  type_ne_shr :
    ∀ n ty ty',
      TypeDist2 n ty ty' →
      (∀ κ π r m l, (l ◁ₗ{π, m, κ} r @ F ty ≡{n}≡ l ◁ₗ{π, m, κ} r @ F ty')%I);

  type_ne_ghost_drop :
    ∀ n ty ty',
      TypeDist n ty ty' →
      (∀ π r , (ty_ghost_drop (F ty) π r ≡{n}≡ ty_ghost_drop (F ty') π r)%I);
}.

Class TypeContractive `{!typeGS Σ} {rt1 rt2} (F : type rt1 → type rt2) : Type := {
  type_ctr_metadata :
    ∀ ty ty',
      (* contractive functors should introduce pointer indirections over recursive occurences,
         hence their metadata cannot depend on their own recursive metadata *)
      (F ty).(ty_metadata_kind) = (F ty').(ty_metadata_kind);

  type_ctr_syn_type :
    ∀ ty ty',
      (* Contractive functors need to introduce a pointer indirection over recursive occurrences,
         hence their syn_type should be trivially equal *)
      (*ty.(ty_syn_type) = ty'.(ty_syn_type) →*)
      ∀ m, (F ty).(ty_syn_type) m = (F ty').(ty_syn_type) m;

  type_ctr_lft_mor :: TyLftMorphism F;

  type_ctr_has_op_type :
    ∀ ty ty',
      (* Contractive functors need to introduce a pointer indirection over recursive occurrences,
         hence their op_type should be trivially equal *)
      (*(∀ ot mt, ty_has_op_type ty ot mt ↔ ty_has_op_type ty' ot mt) →*)
      (∀ ot mt, ty_has_op_type (F ty) ot mt ↔ ty_has_op_type (F ty') ot mt);

  type_ctr_sidecond :
    ∀ ty ty',
      (∀ m, ty.(ty_syn_type) m = ty'.(ty_syn_type) m) →
      ty_sidecond (F ty) ≡ ty_sidecond (F ty');

  type_ctr_own_val :
    ∀ n ty ty',
      TypeDist2 n ty ty' →
      (∀ π r m v, (v ◁ᵥ{π, m} r @ F ty ≡{n}≡ v ◁ᵥ{π, m} r @ F ty')%I);

  type_ctr_shr :
    ∀ n ty ty',
      (* This needs two laters for the fixpoint to go through *)
      TypeDistLater2 n ty ty' →
      (∀ κ π r m l, (l ◁ₗ{π, m, κ} r @ F ty ≡{n}≡ l ◁ₗ{π, m, κ} r @ F ty')%I);

  type_ctr_ghost_drop :
    ∀ n ty ty',
      TypeDist2 n ty ty' →
      (∀ π r , (ty_ghost_drop (F ty) π r ≡{n}≡ ty_ghost_drop (F ty') π r)%I)
}.

(** Properties about [TypeNonExpansive] and [TypeContractive] *)
Section properties.
  Context `{!typeGS Σ}.

  Global Instance type_dist_use_ne {rt1 rt2} (n : nat) (ty1 ty2 : type rt1) (F : type rt1 → type rt2) :
    TypeNonExpansive F → TypeDist n ty1 ty2 → TypeDist n (F ty1) (F ty2).
  Proof.
    intros Hne [????].
    constructor.
    - apply Hne. done.
    - apply Hne; done.
    - intros. apply Hne; done.
    - intros. apply Hne. constructor; [done | done | | done | ].
      + intros. dist_later_fin_intro. eapply dist_le; first done. lia.
      + intros. dist_later_fin_intro. eapply dist_le; first done. lia.
    - apply Hne. done.
  Qed.
  Global Instance type_dist2_use_ne {rt1 rt2} (n : nat) (ty1 ty2 : type rt1) (F : type rt1 → type rt2) :
    TypeNonExpansive F → TypeDist2 n ty1 ty2 → TypeDist2 n (F ty1) (F ty2).
  Proof.
    intros Hne [????].
    constructor.
    - apply Hne. done.
    - apply Hne; done.
    - intros. dist_later_fin_intro.
      apply Hne. constructor; [done.. | | | ].
      + intros. eapply dist_later_fin_lt; first done. lia.
      + intros. eapply dist_le; first done. lia.
      + intros. eapply dist_later_fin_lt; first done. lia.
    - intros. apply Hne; done.
    - intros. dist_later_fin_intro.
      apply Hne. constructor; [done.. | | | ].
      + intros. eapply dist_later_fin_lt; first done. lia.
      + intros. eapply dist_le; first done. lia.
      + intros. eapply dist_later_fin_lt; first done. lia.
  Qed.
  Global Instance type_dist_later_use_ne {rt1 rt2} (n : nat) (ty1 ty2 : type rt1) (F : type rt1 → type rt2) :
    TypeNonExpansive F → TypeDistLater n ty1 ty2 → TypeDistLater n (F ty1) (F ty2).
  Proof.
    intros Hne Hd.
    pose proof Hd as [????].
    constructor.
    - apply Hne. done.
    - apply Hne; done.
    - intros. dist_later_fin_intro.
      apply Hne.
      eapply type_dist_later_dist; first done.
      unfold CanSolve; lia.
    - intros. dist_later_fin_intro.
      apply Hne.
      apply type_dist_dist2.
      eapply type_dist_later_dist; first done.
      unfold CanSolve; lia.
    - intros. dist_later_fin_intro.
      apply Hne.
      eapply type_dist_later_dist; first done.
      unfold CanSolve; lia.
  Qed.

  Global Instance type_contractive_type_ne {rt1 rt2} (F : type rt1 → type rt2) :
    TypeContractive F → TypeNonExpansive F.
  Proof.
    intros [Hm Hst Hlft Hot Hsc Hv Hshr Hghost]. constructor.
    - done.
    - done.
    - done.
    - done.
    - intros ?? Hst' Hsc'. apply Hsc. done.
    - intros n ty ty' Hd.
      eapply Hv. by apply type_dist_dist2.
    - intros n ty ty' Hd.
      eapply Hshr.
      (* TODO instance too weak *)
      eapply type_dist2_later.
      eapply type_dist2_le. { apply _. }
      unfold CanSolve. lia.
  - intros n ty ty' Hd.
    eapply Hghost. by apply type_dist_dist2.
  Qed.

  Global Instance type_ne_ne_compose {rt1 rt2 rt3} (F1 : type rt1 → type rt2) (F2 : type rt2 → type rt3) :
    TypeNonExpansive F1 → TypeNonExpansive F2 → TypeNonExpansive (F2 ∘ F1).
  Proof.
    intros Hne1 Hne2.
    pose proof Hne1 as [Hm1 Hst1 Hlft1 Hot1 Hsc1 Hv1 Hshr1 Hghost1].
    pose proof Hne2 as [Hm2 Hst2 Hlft2 Hot2 Hsc2 Hv2 Hshr2 Hghost2].
    constructor; simpl in *.
    - intros ?? Heq. apply Hm2. apply Hm1. done.
    - naive_solver.
    - apply _.
    - intros ?? ? Ha. eapply Hot2.
      { by eapply Hst1. }
      by eapply Hot1.
    - naive_solver.
    - intros n ?? Hd.
      eapply Hv2. apply _.
    - intros n ?? Hst' Hsc' Hv' Hshr'.
      eapply Hshr2. apply _.
    - intros n ?? Hd.
      eapply Hghost2. apply _.
  Qed.
  Global Instance type_ne_ne_compose' {rt1 rt2 rt3} (F1 : type rt1 → type rt2) (F2 : type rt2 → type rt3) :
    TypeNonExpansive F1 → TypeNonExpansive F2 → TypeNonExpansive (λ ty, F2 (F1 ty)).
  Proof.
    intros. by eapply type_ne_ne_compose.
  Qed.

  Global Instance type_contractive_compose_right {rt1 rt2 rt3} (F1 : type rt1 → type rt2) (F2 : type rt2 → type rt3) :
    TypeContractive F1 → TypeNonExpansive F2 → TypeContractive (F2 ∘ F1).
  Proof.
    intros Hc1 Hne2.
    pose proof Hc1 as [Hm1 Hst1 Hlft1 Hot1 Hsc1 Hv1 Hshr1 Hghost1].
    pose proof Hne2 as [Hm2 Hst2 Hlft2 Hot2 Hsc2 Hv2 Hshr2 Hghost2].
    constructor; simpl in *.
    - intros ??. apply Hm2. apply Hm1.
    - naive_solver.
    - apply _.
    - intros ?? Ha. by eapply Hot2, Hot1.
    - naive_solver.
    - intros n ?? Hd.
      eapply Hv2. constructor.
      + naive_solver.
      + apply Hsc1. apply Hd.
      + eapply Hv1; naive_solver.
      + intros. eapply Hshr1.
        apply type_dist2_later.
        eapply type_dist2_le; first done. unfold CanSolve; lia.
      + eapply Hghost1; naive_solver.
    - intros n ?? Hd.
      eapply Hshr2. constructor.
      + naive_solver.
      + apply Hsc1. apply Hd.
      + intros. dist_later_fin_intro.
        eapply Hv1.
        eapply type_dist_later2_dist2; first done.
        unfold CanSolve; lia.
      + eapply Hshr1; done.
      + intros. dist_later_fin_intro.
        eapply Hghost1.
        eapply type_dist_later2_dist2; first done.
        unfold CanSolve; lia.
    - intros n ?? Hd.
      eapply Hghost2. constructor.
      + naive_solver.
      + apply Hsc1. apply Hd.
      + eapply Hv1; naive_solver.
      + intros. eapply Hshr1.
        apply type_dist2_later.
        eapply type_dist2_le; first done. unfold CanSolve; lia.
      + eapply Hghost1; naive_solver.
  Qed.

  Global Instance type_contractive_compose_left {rt1 rt2 rt3} (F1 : type rt1 → type rt2) (F2 : type rt2 → type rt3) :
    TypeNonExpansive F1 → TypeContractive F2 → TypeContractive (F2 ∘ F1).
  Proof.
    intros Hne1 Hc2.
    pose proof Hne1 as [Hm1 Hst1 Hlft1 Hot1 Hsc1 Hv1 Hshr1 Hghost1].
    pose proof Hc2 as [Hm2 Hst2 Hlft2 Hot2 Hsc2 Hv2 Hshr2 Hghost2].
    constructor; simpl in *.
    - naive_solver.
    - naive_solver.
    - apply _.
    - intros ?? Ha. eapply Hot2.
    - naive_solver.
    - intros n ?? Hd. eapply Hv2. apply _.
    - intros n ?? Hd.
      eapply Hshr2.
      constructor.
      + apply Hst1. apply Hd.
      + apply Hsc1; apply Hd.
      + intros. intros m1 Hm1'.
        eapply Hv1.
        eapply type_dist2_dist; first eapply (type_dist_later2_dist2 _ (S m1)); first done.
        all: unfold CanSolve; lia.
      + intros. dist_later_fin_intro.
        eapply Hshr1.
        eapply type_dist_later2_dist2; first done. unfold CanSolve; lia.
      + intros. intros m1 Hm1'.
        eapply Hghost1.
        eapply type_dist2_dist; first eapply (type_dist_later2_dist2 _ (S m1)); first done.
        all: unfold CanSolve; lia.
    - intros n ?? Hd. eapply Hghost2. apply _.
  Qed.

  Global Instance TypeNe_const {rt1 rt2} (ty : type rt2) :
    TypeNonExpansive (λ _ : type rt1, ty).
  Proof.
    constructor.
    - done.
    - done.
    - eapply ty_lft_morph_make_const; done.
    - done.
    - done.
    - eauto.
    - eauto.
    - eauto.
  Qed.

  Global Instance TypeNe_id {rt1} :
    TypeNonExpansive (rt1:=rt1) id.
  Proof.
    constructor.
    - done.
    - done.
    - eapply ty_lft_morph_make_id; done.
    - done.
    - done.
    - intros ??? Ha. apply Ha.
    - intros ??? Ha. apply Ha.
    - intros ??? Ha. apply Ha.
  Qed.

  Global Instance TypeContr_const {rt1 rt2} (ty : type rt2) :
    TypeContractive (λ _ : type rt1, ty).
  Proof.
    constructor.
    - done.
    - done.
    - eapply ty_lft_morph_make_const; done.
    - done.
    - done.
    - eauto.
    - eauto.
    - eauto.
  Qed.

  Global Instance type_contractive_dist (rt1 rt2 : RT) (F : type rt1 → type rt2) :
    TypeContractive F →
    ∀ n ty ty', TypeDist2 n ty ty' →
    TypeDist n (F ty) (F ty').
  Proof.
    intros Hcontr n ty ty' Hd.
    constructor.
    - apply Hcontr.
    - apply Hcontr.
      apply Hd.
    - apply Hcontr. done.
    - apply Hcontr.
      apply type_dist2_later.
      eapply type_dist2_le; first done.
      unfold CanSolve. lia.
    - apply Hcontr. done.
  Qed.

  Global Instance type_contractive_dist2 (rt1 rt2 : RT) (F : type rt1 → type rt2) :
    TypeContractive F →
    ∀ n ty ty', TypeDistLater2 n ty ty' →
    TypeDist2 n (F ty) (F ty').
  Proof.
    intros Hcontr n ty ty' Hd.
    constructor.
    - apply Hcontr.
    - apply Hcontr.
      apply Hd.
    - intros.
      constructor. simpl.
      intros ? Hlt.
      apply Hcontr.
      eapply type_dist_later2_dist2; first done.
      unfold CanSolve. lia.
    - intros. apply Hcontr. done.
    - intros.
      constructor. simpl.
      intros ? Hlt.
      apply Hcontr.
      eapply type_dist_later2_dist2; first done.
      unfold CanSolve. lia.
  Qed.
End properties.

(** Tactics  to solve non-expansiveness *)
Ltac solve_type_proper_hook := fail.
Ltac solve_type_proper_step :=
  first [
    match goal with
    | H : TypeNonExpansive _ |- _ => apply H
    | H : TypeContractive _ |- _ => apply H
    | H : TypeDist _ _ _ |- _ => apply H
    | H : TypeDist2 _ _ _ |- _ => apply H
    | H : TypeDistLater _ _ _ |- _ => apply H
    | H : TypeDistLater2 _ _ _ |- _ => apply H
    end
  | match goal with
    | |- ty_sidecond _ ≡{_}≡ ty_sidecond _ => apply equiv_dist
    end

  | solve_type_proper_hook
  | apply type_dist_use_ne; first by apply _
  | eapply type_dist2_dist; apply _

  (*| done*)
  (*| eapply dist_later_lt; [done | lia]*)
  (*| eapply dist_later_2_lt; [done | lia]*)
  | f_contractive | my_f_equiv
      ].
Ltac solve_proper_step := first [eassumption | solve_type_proper_step].
Ltac solve_type_proper :=
  solve_proper_core ltac:(fun _ => solve_type_proper_step).


(** Point-wise non-expansive type lists *)
Class HTypeNonExpansive `{!typeGS Σ} {rt} {rts : list RT}
  (Ts : type rt → hlist type rts) : Type := mk_htype_ne {
    HTypeNe_Ts' : hlist (λ rt', type rt → type rt') rts;
    HTypeNe_Ne : HTForall (λ _, TypeNonExpansive) HTypeNe_Ts';
    HtypeNe_Eq : Ts = happly HTypeNe_Ts';
}.
Arguments mk_htype_ne {_ _ _ _}.
Class HTypeContractive `{!typeGS Σ} {rt} {rts : list RT}
  (Ts : type rt → hlist type rts) : Type := mk_htype_contr {
    HTypeContr_Ts' : hlist (λ rt', type rt → type rt') rts;
    HTypeContr_Ne : HTForall (λ _, TypeContractive) HTypeContr_Ts';
    HtypeContr_Eq : Ts = happly HTypeContr_Ts';
}.
Arguments mk_htype_contr {_ _ _ _}.
Section ne.
  Context `{!typeGS Σ}.

  Global Instance HTypeNonExpansive_nil {rt} :
    HTypeNonExpansive (λ _ : type rt, +[]).
  Proof.
    refine (mk_htype_ne _ +[] _ _).
    - constructor.
    - done.
  Qed.
  Global Instance HTypeNonExpansive_cons {rt rt1 rts} (F : type rt → type rt1) (Fs : type rt → hlist type rts) :
    HTypeNonExpansive Fs →
    TypeNonExpansive F →
    HTypeNonExpansive (λ ty : type rt, (F ty) +:: (Fs ty)).
  Proof.
    intros Hne1 Hne.
    destruct Hne1 as [Fs' ? ?].
    refine (mk_htype_ne _ (F +:: Fs') _ _).
    - constructor; done.
    - simpl. naive_solver.
  Qed.

  Global Instance HTypeContractive_nil {rt} :
    HTypeContractive (λ _ : type rt, +[]).
  Proof.
    refine (mk_htype_contr _ +[] _ _).
    - constructor.
    - done.
  Qed.
  Global Instance HTypeContractive_cons {rt rt1 rts} (F : type rt → type rt1) (Fs : type rt → hlist type rts) :
    HTypeContractive Fs →
    TypeContractive F →
    HTypeContractive (λ ty : type rt, (F ty) +:: (Fs ty)).
  Proof.
    intros Hne1 Hne.
    destruct Hne1 as [Fs' ? ?].
    refine (mk_htype_contr _ (F +:: Fs') _ _).
    - constructor; done.
    - simpl. naive_solver.
  Qed.
End ne.


(** ** Subtyping etc. *)
Definition type_incl `{!typeGS Σ} {rt1 rt2 : RT}  (r1 : rt1) (r2 : rt2) (ty1 : type rt1) (ty2 : type rt2) : iProp Σ :=
  (* Require equality of the syntypes.
     This also ensures that the alignment requirements are the same, so that we can use [type_incl] below pointers. *)
  (* TODO: can we just require the layout to be the same? *)
  (⌜∀ m, ty1.(ty_syn_type) m = ty2.(ty_syn_type) m⌝ ∗
  (□ (ty1.(ty_sidecond) -∗ ty2.(ty_sidecond))) ∗
  (□ ∀ π m v, ty1.(ty_own_val) π r1 m v -∗ ty2.(ty_own_val) π r2 m v) ∗
  (□ ∀ κ π m l, ty1.(ty_shr) κ π r1 m l -∗ ty2.(ty_shr) κ π r2 m l))%I.
#[export] Instance: Params (@type_incl) 4 := {}.

(** Owned value subtyping (is NOT compatible with shared references). *)
(* NOTE: For supporting subtyping of unsized types, parameterize by metadata *)
Definition owned_type_incl `{!typeGS Σ}  π {rt1 rt2 : RT} (r1 : rt1) (r2 : rt2) (ty1 : type rt1) (ty2 : type rt2) : iProp Σ :=
  ⌜syn_type_size_eq (ty_syn_type ty1 MetaNone) (ty_syn_type ty2 MetaNone)⌝ ∗
  (ty_sidecond ty1 -∗ ty_sidecond ty2) ∗
  (∀ (v : val), v ◁ᵥ{π, MetaNone} r1 @ ty1 -∗ v ◁ᵥ{ π, MetaNone} r2 @ ty2).

(* Heterogeneous subtyping *)
Definition subtype `{!typeGS Σ} (E : elctx) (L : llctx) {rt1 rt2 : RT} (r1 : rt1) (r2 : rt2) (ty1 : type rt1) (ty2 : type rt2) : Prop :=
  ∀ qL, llctx_interp_noend L qL  -∗ (elctx_interp E -∗ type_incl r1 r2 ty1 ty2).
#[export] Instance: Params (@subtype) 6 := {}.

(* Homogeneous subtyping independently of the refinement *)
Definition full_subtype `{!typeGS Σ} (E : elctx) (L : llctx) {rt : RT} (ty1 ty2 : type rt) : Prop :=
  ∀ r, subtype E L r r ty1 ty2.
#[export] Instance: Params (@full_subtype) 5 := {}.

(* Heterogeneous type equality *)
Definition eqtype `{!typeGS Σ} (E : elctx) (L : llctx) {rt1 rt2 : RT} (r1 : rt1) (r2 : rt2) (ty1 : type rt1) (ty2 : type rt2) : Prop :=
  subtype E L r1 r2 ty1 ty2 ∧ subtype E L r2 r1 ty2 ty1.
#[export] Instance: Params (@eqtype) 6 := {}.

Definition full_eqtype `{!typeGS Σ} (E : elctx) (L : llctx) {rt : RT} (ty1 ty2 : type rt) : Prop :=
  ∀ r, eqtype E L r r ty1 ty2.
#[export] Instance: Params (@full_eqtype) 5 := {}.

Section subtyping.
  Context `{!typeGS Σ}.

  Implicit Type rt : RT.

  (** *** [type_incl] *)
  Global Instance type_incl_ne {rt1 rt2} r1 r2 : NonExpansive2 (type_incl (rt1 := rt1) (rt2 := rt2) r1 r2).
  Proof.
    iIntros (n ty1 ty1' Heq ty2 ty2' Heq2).
    unfold type_incl. f_equiv.
    { f_equiv. destruct Heq as [? ? ? ? ? Heq1 ?], Heq2 as [? ? ? ? ? Heq2 ?].
      setoid_rewrite Heq1. setoid_rewrite Heq2. done. }
    f_equiv.
    { f_equiv. f_equiv; by destruct Heq, Heq2. }
    do 2 f_equiv.
    { do 7 f_equiv; by destruct Heq, Heq2. }
    do 9 f_equiv; by destruct Heq, Heq2.
  Qed.
  Global Instance type_incl_proper {rt1 rt2} r1 r2 : Proper ((≡) ==> (≡) ==> (≡)) (type_incl (rt1 := rt1) (rt2 := rt2) r1 r2).
  Proof.
    iIntros (ty1 ty1' Heq ty2 ty2' Heq2).
    apply equiv_dist => n. apply type_incl_ne; by apply equiv_dist.
  Qed.

  Global Instance type_incl_persistent {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) : Persistent (type_incl r1 r2 ty1 ty2) := _.

  Lemma type_incl_refl {rt} (r : rt) (ty : type rt) : ⊢ type_incl r r ty ty.
  Proof.
    iSplit; first done.
    iSplitR. { iModIntro; iIntros "$". }
    iSplit; iModIntro; iIntros; done.
  Qed.

  Lemma type_incl_trans {rt1 rt2 rt3} r1 r2 r3 (ty1 : type rt1) (ty2 : type rt2) (ty3 : type rt3) :
    type_incl r1 r2 ty1 ty2 -∗ type_incl r2 r3 ty2 ty3 -∗ type_incl r1 r3 ty1 ty3.
  Proof.
    iIntros "(% & #Hsc12 & #Ho12 & #Hs12) (% & #Hsc23 & #Ho23 & #Hs23)".
    iSplit. { iPureIntro. iIntros (m). etrans; eauto. }
    iSplitR. { iModIntro. iIntros "H1". iApply "Hsc23". by iApply "Hsc12". }
    iSplit; iModIntro; iIntros.
    - iApply "Ho23". iApply "Ho12". done.
    - iApply "Hs23". iApply "Hs12". done.
  Qed.

  (** *** [owned_type_incl] *)
  Lemma owned_type_incl_refl π {rt} (ty : type rt) (r : rt) :
    ⊢ owned_type_incl π r r ty ty.
  Proof.
    iSplitR. { iPureIntro. intros ?. by eapply syn_type_size_eq_refl. }
    iSplitR. { eauto. }
    iIntros (v). eauto.
  Qed.
  Lemma type_incl_owned_type_incl π {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) :
    type_incl r1 r2 ty1 ty2 -∗ □ owned_type_incl π r1 r2 ty1 ty2.
  Proof.
    iIntros "(%Hst & #$ & #Hv & _)".
    iDestruct ("Hv" $! π _) as "$".
    iPureIntro. setoid_rewrite Hst.
    apply syn_type_size_eq_refl.
  Qed.
  Lemma owned_type_incl_incl_l π {rt1 rt2 rt3} (ty1 : type rt1) (ty2 : type rt2) (ty3 : type rt3) r1 r2 r3 :
    type_incl r1 r2 ty1 ty2 -∗
    owned_type_incl π r2 r3 ty2 ty3 -∗
    owned_type_incl π r1 r3 ty1 ty3.
  Proof.
    iIntros "(%Hst1 & Hsc1 & Hv1 & _) (%Hst2 & Hsc2 & Hv2)".
    iSplit; last iSplitR "Hv1 Hv2".
    - iPureIntro.
      intros ? Ha1.
      rewrite Hst1 in Ha1.
      apply Hst2 in Ha1.
      done.
    - iIntros "Hsc". iApply "Hsc2". by iApply "Hsc1".
    - iIntros (v) "Hv". iApply "Hv2". by iApply "Hv1".
  Qed.
  Lemma owned_type_incl_incl_r π {rt1 rt2 rt3} (ty1 : type rt1) (ty2 : type rt2) (ty3 : type rt3) r1 r2 r3 :
    owned_type_incl π r1 r2 ty1 ty2 -∗
    type_incl r2 r3 ty2 ty3 -∗
    owned_type_incl π r1 r3 ty1 ty3.
  Proof.
    iIntros "(%Hst1 & Hsc1 & Hv1) (%Hst2 & Hsc2 & Hv2 & _)".
    iSplit; last iSplitR "Hv1 Hv2".
    - iPureIntro.
      intros ? Ha1.
      apply Hst1 in Ha1.
      rewrite Hst2 in Ha1. done.
    - iIntros "Hsc". iApply "Hsc2". by iApply "Hsc1".
    - iIntros (v) "Hv". iApply "Hv2". by iApply "Hv1".
  Qed.

  (** *** [subtype] *)
  Lemma subtype_refl E L {rt} r (ty : type rt) : subtype E L r r ty ty.
  Proof. iIntros (?) "_ _". iApply type_incl_refl. Qed.
  Lemma subtype_trans E L {rt1 rt2 rt3} r1 r2 r3 (ty1 : type rt1) (ty2 : type rt2) (ty3 : type rt3) :
    subtype E L r1 r2 ty1 ty2 → subtype E L r2 r3 ty2 ty3 → subtype E L r1 r3 ty1 ty3.
  Proof.
    intros H12 H23. iIntros (?) "HL #HE".
    iDestruct (H12 with "HL HE") as "#H12".
    iDestruct (H23 with "HL HE") as "#H23".
    iApply (type_incl_trans with "[#]"); [by iApply "H12" | by iApply "H23"].
  Qed.

  (* For the homogenous case, we get an instance *)
  #[export] Instance full_subtype_preorder E L {rt} :
    PreOrder (full_subtype E L (rt:=rt)).
  Proof.
    split; first (intros ??; apply subtype_refl).
    intros ??????. by eapply subtype_trans.
  Qed.

  Lemma subtype_acc E L {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) :
    subtype E L r1 r2 ty1 ty2 →
    elctx_interp E -∗
    llctx_interp L -∗
    type_incl r1 r2 ty1 ty2.
  Proof.
    iIntros (Hsub) "HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & Hcl_L)".
    iPoseProof (Hsub with "HL HE") as "#Hincl". done.
  Qed.
  Lemma full_subtype_acc E L {rt} (ty1 : type rt) (ty2 : type rt) :
    full_subtype E L ty1 ty2 →
    elctx_interp E -∗
    llctx_interp L -∗
    ∀ r, type_incl r r ty1 ty2.
  Proof.
    iIntros (Hsub) "HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & Hcl_L)".
    iIntros (?). iPoseProof (Hsub with "HL HE") as "#Hincl". done.
  Qed.
  Lemma full_subtype_acc_noend E L {rt} (ty1 : type rt) (ty2 : type rt) qL :
    full_subtype E L ty1 ty2 →
    elctx_interp E -∗
    llctx_interp_noend L qL -∗
    ∀ r, type_incl r r ty1 ty2.
  Proof.
    iIntros (Hsub) "HE HL".
    iIntros (?). iPoseProof (Hsub with "HL HE") as "#Hincl". done.
  Qed.

  Lemma equiv_full_subtype E L {rt} (ty1 ty2 : type rt) : ty1 ≡ ty2 → full_subtype E L ty1 ty2.
  Proof. unfold subtype=>EQ ? ?. setoid_rewrite EQ. apply subtype_refl. Qed.

  Lemma eqtype_unfold E L {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) :
    eqtype E L r1 r2 ty1 ty2 ↔
    (∀ qL, llctx_interp_noend L qL -∗ (elctx_interp E -∗
      (⌜∀ m, ty1.(ty_syn_type) m = ty2.(ty_syn_type) m⌝ ∗
      (□ (ty1.(ty_sidecond) ↔ ty2.(ty_sidecond))) ∗
      (□ ∀ π m v, ty1.(ty_own_val) π r1 m v ↔ ty2.(ty_own_val) π r2 m v) ∗
      (□ ∀ κ π m l, ty1.(ty_shr) κ π r1 m l ↔ ty2.(ty_shr) κ π r2 m l)))%I).
  Proof.
    split.
    - iIntros ([EQ1 EQ2] qL) "HL HE".
      iDestruct (EQ1 with "HL HE") as "#EQ1".
      iDestruct (EQ2 with "HL HE") as "#EQ2".
      iDestruct ("EQ1") as "(% & #Hsc1 & #H1own & #H1shr)".
      iDestruct ("EQ2") as "(_ & #Hsc2 & #H2own & #H2shr)".
      iSplitR; first done. iSplit; last iSplit.
      + iModIntro. iSplit; iIntros "?"; [iApply "Hsc1" | iApply "Hsc2"]; done.
      + by iIntros "!#*"; iSplit; iIntros "H"; [iApply "H1own"|iApply "H2own"].
      + by iIntros "!#*"; iSplit; iIntros "H"; [iApply "H1shr"|iApply "H2shr"].
    - intros EQ. split; (iIntros (qL) "HL HE";
      iDestruct (EQ with "HL HE") as "#EQ";
      iDestruct ("EQ") as "(% & #Hsc & #Hown & #Hshr)"; iSplitR; [done | ]; iSplit; [ | iSplit ]).
      + iIntros "!> H". by iApply "Hsc".
      + iIntros "!> * H". by iApply "Hown".
      + iIntros "!> * H". by iApply "Hshr".
      + iIntros "!> H". by iApply "Hsc".
      + iIntros "!> * H". by iApply "Hown".
      + iIntros "!> * H". by iApply "Hshr".
  Qed.

  Lemma eqtype_refl E L {rt} r (ty : type rt) : eqtype E L r r ty ty.
  Proof. split; apply subtype_refl. Qed.

  Lemma equiv_full_eqtype E L {rt} (ty1 ty2 : type rt) : ty1 ≡ ty2 → full_eqtype E L ty1 ty2.
  Proof. by intros ??; split; apply equiv_full_subtype. Qed.

  Global Instance subtype_proper E L {rt1 rt2} r1 r2 :
    Proper (eqtype E L (rt1:=rt1) (rt2:=rt1) r1 r1 ==> eqtype E L (rt1:=rt2)(rt2:=rt2) r2 r2 ==> iff) (subtype E L (rt1 := rt1) (rt2 := rt2) r1 r2).
  Proof.
    intros ??[H1 H2] ??[H3 H4]. split; intros H.
    - eapply subtype_trans; last eapply subtype_trans; [ apply H2 | apply H | apply H3].
    - eapply subtype_trans; last eapply subtype_trans; [ apply H1 | apply H |  apply H4].
  Qed.

  #[export] Instance full_eqtype_equivalence E L {rt} : Equivalence (full_eqtype E L (rt:=rt)).
  Proof.
    split.
    - split; apply subtype_refl.
    - intros ?? Heq; split; apply Heq.
    - intros ??? H1 H2. split; eapply subtype_trans; (apply H1 || apply H2).
  Qed.

  Lemma type_incl_simple_type {rt1} {rt2} r1 r2 (st1 : simple_type rt1) (st2 : simple_type rt2) :
    □ (∀ tid v, st1.(st_own) tid r1 v -∗ st2.(st_own) tid r2 v) -∗
    ⌜st1.(st_syn_type) = st2.(st_syn_type)⌝ -∗
    type_incl r1 r2 st1 st2.
  Proof.
    iIntros "#Hst %Hly". iSplit; first done. iSplitR; first done. iSplit; iModIntro.
    - simpl. iIntros (???) "(-> & Ha)". iR. by iApply "Hst".
    - iIntros (???).
      iDestruct 1 as (vl ly) "(-> & Hf & Hown & %Hst & %Hly')". iExists vl, ly. iFrame "Hf". iR.
      iSplitL. { by iApply "Hst". } rewrite -Hly. done.
  Qed.

  Lemma subtype_simple_type E L {rt1 rt2} r1 r2 (st1 : simple_type rt1) (st2 : simple_type rt2):
    (∀ qL, llctx_interp_noend L qL -∗ (elctx_interp E -∗
       (□ ∀ tid v, st1.(st_own) tid r1 v -∗ st2.(st_own) tid r2 v) ∗
       ⌜st1.(st_syn_type) = st2.(st_syn_type)⌝)) →
    subtype E L r1 r2 st1 st2.
  Proof.
    intros Hst. iIntros (qL) "HL HE". iDestruct (Hst with "HL HE") as "#Hst".
    iClear "∗". iDestruct ("Hst") as "[Hst' %Hly]".
    iApply type_incl_simple_type.
    - iIntros "!#" (??) "?". by iApply "Hst'".
    - done.
  Qed.

  Lemma subtype_weaken E1 E2 L1 L2 {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) :
    E1 ⊆+ E2 → L1 ⊆+ L2 →
    subtype E1 L1 r1 r2 ty1 ty2 → subtype E2 L2 r1 r2 ty1 ty2.
  Proof.
    iIntros (HE12 ? Hsub qL) "HL HE". iDestruct (Hsub with "[HL] [HE]") as "#Hsub".
    { rewrite /llctx_interp. by iApply big_sepL_submseteq. }
    { rewrite /elctx_interp. by iApply big_sepL_submseteq. }
    iApply "Hsub".
  Qed.

  Lemma subtype_eqtype E L {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) :
    subtype E L r1 r2 ty1 ty2 →
    subtype E L r2 r1 ty2 ty1 →
    eqtype E L r1 r2 ty1 ty2.
  Proof. intros; split; done. Qed.

  Lemma all_subtype_alt E L {rt} (ty1 ty2 : type rt) :
    (∀ r, subtype E L r r ty1 ty2) ↔
    (∀ qL, llctx_interp_noend L qL -∗ (elctx_interp E -∗ ∀ r, type_incl r r ty1 ty2)).
  Proof.
    split.
    - intros Ha qL. iIntros "HL HE" (r).
      by iPoseProof (Ha r with "HL HE") as "Ha".
    - intros Ha r. iIntros (qL) "HL HE".
      iApply (Ha with "HL HE").
  Qed.
  Lemma all_eqtype_alt E L {rt} (ty1 ty2 : type rt) :
    (∀ r, eqtype E L r r ty1 ty2) ↔
    ((∀ qL, llctx_interp_noend L qL -∗ elctx_interp E -∗ ∀ r, type_incl r r ty1 ty2) ∧
    (∀ qL, llctx_interp_noend L qL -∗ elctx_interp E -∗ ∀ r, type_incl r r ty2 ty1)).
  Proof.
    rewrite forall_and_distr !all_subtype_alt //.
  Qed.

  Lemma full_subtype_eqtype E L {rt} (ty1 ty2 : type rt) :
    full_subtype E L ty1 ty2 →
    full_subtype E L ty2 ty1 →
    full_eqtype E L ty1 ty2.
  Proof.
    intros Hsub1 Hsub2 r. split; done.
  Qed.

  Lemma full_eqtype_subtype_l E L {rt} (ty1 ty2 : type rt) :
    full_eqtype E L ty1 ty2 → full_subtype E L ty1 ty2.
  Proof.
    iIntros (Heq r). destruct (Heq r) as [Ha Hb]. done.
  Qed.
  Lemma full_eqtype_subtype_r E L {rt} (ty1 ty2 : type rt) :
    full_eqtype E L ty1 ty2 → full_subtype E L ty2 ty1.
  Proof.
    iIntros (Heq r). destruct (Heq r) as [Ha Hb]. done.
  Qed.

  Lemma eqtype_acc E L {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) :
    eqtype E L r1 r2 ty1 ty2 →
    elctx_interp E -∗
    llctx_interp L -∗
    type_incl r1 r2 ty1 ty2 ∗ type_incl r2 r1 ty2 ty1.
  Proof.
    iIntros ([Hsub1 Hsub2]) "HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & Hcl_L)".
    iPoseProof (Hsub1 with "HL HE") as "#Hincl1".
    iPoseProof (Hsub2 with "HL HE") as "#Hincl2".
    iFrame "#".
  Qed.
  Lemma eqtype_acc_noend E L {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) qL :
    eqtype E L r1 r2 ty1 ty2 →
    elctx_interp E -∗
    llctx_interp_noend L qL -∗
    type_incl r1 r2 ty1 ty2 ∗ type_incl r2 r1 ty2 ty1.
  Proof.
    iIntros ([Hsub1 Hsub2]) "HE HL".
    iPoseProof (Hsub1 with "HL HE") as "#Hincl1".
    iPoseProof (Hsub2 with "HL HE") as "#Hincl2".
    iFrame "#".
  Qed.
  Lemma full_eqtype_acc E L {rt} (ty1 : type rt) (ty2 : type rt) :
    full_eqtype E L ty1 ty2 →
    elctx_interp E -∗
    llctx_interp L -∗
    ∀ r, type_incl r r ty1 ty2 ∗ type_incl r r ty2 ty1.
  Proof.
    iIntros (Heq) "HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & Hcl_L)".
    iIntros (r). destruct (Heq r) as [Hsub1 Hsub2].
    iPoseProof (Hsub1 with "HL HE") as "#$".
    iPoseProof (Hsub2 with "HL HE") as "#$".
  Qed.
  Lemma full_eqtype_acc_noend E L {rt} (ty1 : type rt) (ty2 : type rt) qL :
    full_eqtype E L ty1 ty2 →
    elctx_interp E -∗
    llctx_interp_noend L qL -∗
    ∀ r, type_incl r r ty1 ty2 ∗ type_incl r r ty2 ty1.
  Proof.
    iIntros (Heq) "HE HL".
    iIntros (r). destruct (Heq r) as [Hsub1 Hsub2].
    iPoseProof (Hsub1 with "HL HE") as "#$".
    iPoseProof (Hsub2 with "HL HE") as "#$".
  Qed.
End subtyping.

(** Copy types *)
Fixpoint shr_locsE (l : loc) (n : nat) : coPset :=
  match n with
  | 0%nat => ∅
  | S n => ↑shrN.@l ∪ shr_locsE (l +ₗ 1%nat) n
  end.

(* TODO: add na_own here. *)
Class Copyable `{!typeGS Σ} {rt} (ty : type rt) := {
  copy_own_persistent π r m v : Persistent (ty.(ty_own_val) π r m v);
  (* sharing predicates of copyable types should actually allow us to get a Copy out from below the reference *)
  copy_shr_acc κ π E l r m q :
    lftE ∪ ↑shrN ⊆ E →
    (* syn_type_has_layout (ty.(ty_syn_type) m) ly →*)
    rrust_ctx -∗
    ty.(ty_shr) κ π r m l -∗
    q.[κ] ={E}=∗ ∃ ly,
    ▷ ⌜syn_type_has_layout (ty.(ty_syn_type) m) ly⌝ ∗
    ▷ ⌜l `has_layout_loc` ly⌝ ∗
    ∃ q' v, ▷ (l ↦{q'} v ∗ ty.(ty_own_val) π r m v) ∗
     (▷l ↦{q'} v ={E}=∗ q.[κ])
}.
#[export] Hint Mode Copyable - - + + : typeclass_instances.
#[export] Existing Instance copy_own_persistent.

Section copy.
  Lemma shr_locsE_incl' l n :
    shr_locsE l n ⊆ ↑shrN ∧ (∀ m, n ≤ m → ↑shrN.@(l +ₗ m) ## (shr_locsE l n)).
  Proof.
    induction n as [ | n IH] in l |-*; simpl.
    - set_solver.
    - specialize (IH (l +ₗ 1%nat)) as (? & Ha).
      split.
      + solve_ndisj.
      + intros m Hm. specialize (Ha (m - 1)).
        assert (n ≤ m -1) as Hb by lia.
        specialize (Ha Hb) as Hc.
        rewrite shift_loc_assoc in Hc.
        replace (1%nat + (m - 1)) with m in Hc by lia.
        assert (l +ₗ m ≠ l). { rewrite -{2}(shift_loc_0 l). intros Heq%shift_loc_inj2. lia. }
        solve_ndisj.
  Qed.
  Lemma shr_locsE_incl l n :
    shr_locsE l n ⊆ ↑shrN.
  Proof. apply shr_locsE_incl'. Qed.

  Lemma loc_in_shr_locsE l (off sz : nat) :
    off < sz →
    ↑shrN.@(l +ₗ off) ⊆ shr_locsE l sz.
  Proof.
    intros Hlt. induction sz as [ | sz IH] in l, off, Hlt |-*; simpl.
    { lia. }
    destruct off as [ | off].
    { rewrite shift_loc_0_nat. set_solver. }
    apply union_subseteq_r'.
    rewrite -(shift_loc_assoc_nat _ 1).
    apply IH. lia.
  Qed.

  Lemma shr_locsE_disjoint l (n m : nat) :
    (n ≤ m)%Z → ↑shrN.@(l +ₗ m) ## shr_locsE l n.
  Proof. apply shr_locsE_incl'. Qed.

  Lemma shr_locsE_offset l (off sz1 sz2 sz : nat) F :
    sz1 ≤ off →
    off + sz2 ≤ sz →
    shr_locsE l sz ⊆ F →
    shr_locsE (l +ₗ off) sz2 ⊆ F ∖ shr_locsE l sz1.
  Proof.
    intros Hl1 Hl2 Hl3.
    induction sz2 as [ | sz2 IH] in sz1, off, sz, Hl1, Hl2, Hl3 |-*.
    { simpl. set_solver. }
    simpl. apply union_least.
    - apply namespaces.coPset_subseteq_difference_r.
      2: { etrans; last apply Hl3. apply loc_in_shr_locsE. lia. }
      apply shr_locsE_disjoint. lia.
    - rewrite shift_loc_assoc.
      rewrite -Nat2Z.inj_add. eapply IH; last done; lia.
  Qed.

  Lemma shr_locsE_add l (sz1 sz2 : nat) :
    shr_locsE l (sz1 + sz2) = shr_locsE l sz1 ∪ shr_locsE (l +ₗ sz1) sz2.
  Proof.
    induction sz1 as [ | sz1 IH] in l |-*; simpl.
    { rewrite shift_loc_0_nat. set_solver. }
    rewrite IH shift_loc_assoc -Nat2Z.inj_add.
    set_solver.
  Qed.

  Lemma shr_locsE_shift l n m :
    shr_locsE l (n + m) = shr_locsE l n ∪ shr_locsE (l +ₗ n) m.
  Proof.
    revert l; induction n as [|n IHn]; intros l.
    - rewrite shift_loc_0. set_solver+.
    - rewrite -Nat.add_1_l Nat2Z.inj_add /= IHn shift_loc_assoc.
      set_solver+.
  Qed.

  Lemma shr_locsE_subseteq l n m :
    (n ≤ m)%nat → shr_locsE l n ⊆ shr_locsE l m.
  Proof.
    induction 1; first done. etrans; first done.
    rewrite -Nat.add_1_l [(_ + _)%nat]comm_L shr_locsE_shift. set_solver+.
  Qed.

  Lemma shr_locsE_disj l n m :
    shr_locsE l n ## shr_locsE (l +ₗ n) m.
  Proof.
    revert l; induction n as [|n IHn]; intros l.
    - simpl. set_solver+.
    - rewrite -Nat.add_1_l Nat2Z.inj_add /=.
      apply disjoint_union_l. split; last (rewrite -shift_loc_assoc; exact: IHn).
      clear IHn. revert n; induction m as [|m IHm]; intros n; simpl; first set_solver+.
      rewrite shift_loc_assoc. apply disjoint_union_r. split.
      + apply ndot_ne_disjoint. destruct l. intros [=]. lia.
      + rewrite -Z.add_assoc. move:(IHm (n + 1)%nat). rewrite Nat2Z.inj_add //.
  Qed.
  Lemma shr_locsE_split_tok `{!typeGS Σ} l n m tid :
    na_own tid (shr_locsE l (n + m)) ⊣⊢
      na_own tid (shr_locsE l n) ∗ na_own tid (shr_locsE (l +ₗ n) m).
  Proof.
    rewrite shr_locsE_shift na_own_union //. apply shr_locsE_disj.
  Qed.

  #[export] Program Instance simple_type_copyable `{typeGS Σ} {rt} (st : simple_type rt) : Copyable st.
  Next Obligation.
    iIntros (??? st κ π E l r m ? ?) "#(LFT & LLCTX) (%v & %ly & -> & Hf & #Hown & %Hst' & Hly) Hlft".
    iMod (frac_bor_acc with "LFT Hf Hlft") as (q') "[Hmt Hclose]"; first solve_ndisj.
    iExists ly.
    iModIntro. iFrame "Hly". iR. iExists _. iDestruct "Hmt" as "[Hmt1 Hmt2]".
    iExists v.
    iSplitL "Hmt1". { iFrame. rewrite /ty_own_val/=. iL. done. }
    iIntros "Hmt1".
    iApply "Hclose". iModIntro. rewrite -{3}(Qp.div_2 q').
    iPoseProof (heap_pointsto_agree with "Hmt1 Hmt2") as "%Heq"; first done.
    rewrite heap_pointsto_fractional. iFrame.
  Qed.

  Global Instance copy_equiv `{!typeGS Σ} {rt} : Proper (equiv ==> impl) (@Copyable _ _ rt).
  Proof.
    intros ty1 ty2 [? EQ_op EQown EQshr ? EQst] Hty1. split.
    - intros. rewrite -EQown. apply _.
    - intros *. rewrite -EQshr. setoid_rewrite <-EQown.
      setoid_rewrite <-EQst.
      apply copy_shr_acc.
  Qed.
End copy.


(** Lifetime morphisms which are not composable, but work for any projections into a lifetime list + elctx *)
(* This is very convenient to use in order to show that something is a [TyLftMorphism]. *)
Section lft_mor.
Context `{!typeGS Σ}.

(* TODO deduplicate def *)
(* The functor has constant lifetime requirements *)
Record DirectLftMorphismConst {rt1} (Flfts : type rt1 → list lft) (FE : type rt1 → elctx) : Type := mk_direct_lft_morph_const {
  direct_lft_morph_const_α : lft;
  direct_lft_morph_const_E : elctx;
  direct_lft_morph_const_lfts :
    ⊢ ∀ ty, lft_equiv (lft_intersect_list (Flfts ty)) direct_lft_morph_const_α;
  direct_lft_morph_const_wf_E :
    ∀ ty, elctx_interp (FE ty) ≡ elctx_interp direct_lft_morph_const_E;
}.
Global Arguments mk_direct_lft_morph_const {_ _ _}.
Global Arguments direct_lft_morph_const_lfts {_ _ _ _}.
Global Arguments direct_lft_morph_const_wf_E {_ _ _ _}.

(* An application of the functor adds some lifetime requirements which are essentially constant *)
Record DirectLftMorphismAdd {rt1} (Flfts : type rt1 → list lft) (FE : type rt1 → elctx) : Type := mk_direct_lft_morph_add {
  direct_lft_morph_add_α : lft;
  direct_lft_morph_add_E : elctx;
  direct_lft_morph_add_βs : list lft;
  direct_lft_morph_add_lfts :
    ⊢ ∀ ty, lft_equiv (lft_intersect_list (Flfts ty)) (direct_lft_morph_add_α ⊓ lft_intersect_list (ty_lfts ty));
  direct_lft_morph_add_wf_E :
    ∀ ty, elctx_interp (FE ty) ≡
        (elctx_interp direct_lft_morph_add_E ∗ elctx_interp (ty_wf_E ty) ∗
          (* some requirements of lifetimes that the type has to outlive *)
          [∗ list] β ∈ direct_lft_morph_add_βs, β ⊑ lft_intersect_list (ty_lfts ty))%I;
}.
Global Arguments mk_direct_lft_morph_add {_ _ _}.

Inductive DirectLftMorphism {rt1} (Flfts : type rt1 → list lft) (FE : type rt1 → elctx) : Type :=
| direct_lft_morph_const (_ : DirectLftMorphismConst Flfts FE)
| direct_lft_morph_add (_ : DirectLftMorphismAdd Flfts FE)
.
Existing Class DirectLftMorphism.

Global Instance ty_lft_morphism_of_direct {rt1 rt2} (F : type rt1 → type rt2) :
  DirectLftMorphism (λ ty, ty_lfts (F ty)) (λ ty, (ty_wf_E (F ty))) →
  TyLftMorphism F.
Proof.
  intros [Hm | Hm].
  - apply ty_lft_morph_const.
    destruct Hm as [α E Hα HE].
    refine (mk_lft_morph_const α E _ _); done.
  - destruct Hm as [α E βs Hα HE].
    apply ty_lft_morph_add.
    refine (mk_lft_morph_add α E βs _ _); done.
Qed.
Global Instance ty_lft_morphism_to_direct {rt1 rt2} (F : type rt1 → type rt2) :
  TyLftMorphism F →
  DirectLftMorphism (λ ty, ty_lfts (F ty)) (λ ty, (ty_wf_E (F ty))).
Proof.
  intros [Hm | Hm].
  - apply direct_lft_morph_const.
    destruct Hm as [α E Hα HE].
    refine (mk_direct_lft_morph_const α E _ _); done.
  - destruct Hm as [α E βs Hα HE].
    apply direct_lft_morph_add.
    refine (mk_direct_lft_morph_add α E βs _ _); done.
Qed.

Global Instance direct_lft_morphism_app {rt1} (Flft1 Flft2 : type rt1 → list lft) (FE1 FE2 : type rt1 → elctx) :
  DirectLftMorphism Flft1 FE1 →
  DirectLftMorphism Flft2 FE2 →
  DirectLftMorphism (λ ty, Flft1 ty ++ Flft2 ty) (λ ty, FE1 ty ++ FE2 ty).
Proof.
  intros [Hl1 | Hl1] [Hl2 | Hl2].
  - destruct Hl1 as [α1 E1 Hα1 HE1].
    destruct Hl2 as [α2 E2 Hα2 HE2].
    apply direct_lft_morph_const.
    refine (mk_direct_lft_morph_const (α1 ⊓ α2) (E1 ++ E2) _ _).
    + iIntros (ty). rewrite lft_intersect_list_app.
      iApply lft_equiv_intersect; done.
    + intros ty. rewrite !elctx_interp_app.
      rewrite HE1 HE2. done.
  - destruct Hl1 as [α1 E1 Hα1 HE1].
    destruct Hl2 as [α2 E2 βs2 Hα2 HE2].
    apply direct_lft_morph_add.
    refine (mk_direct_lft_morph_add (α1 ⊓ α2) (E1 ++ E2) βs2 _ _).
    + iIntros (ty). rewrite lft_intersect_list_app.
      iApply lft_equiv_trans.
      { iApply lft_equiv_intersect; [iApply Hα1 |  iApply Hα2]. }
      rewrite assoc. iApply lft_equiv_refl.
    + intros ty. rewrite elctx_interp_app.
      rewrite HE1 HE2. rewrite elctx_interp_app assoc. done.
  - destruct Hl1 as [α1 E1 βs1 Hα1 HE1].
    destruct Hl2 as [α2 E2 Hα2 HE2].
    apply direct_lft_morph_add.
    refine (mk_direct_lft_morph_add (α1 ⊓ α2) (E1 ++ E2) βs1 _ _).
    + iIntros (ty). rewrite lft_intersect_list_app.
      iApply lft_equiv_trans.
      { iApply lft_equiv_intersect; [iApply Hα1 |  iApply Hα2]. }
      rewrite -assoc. rewrite [lft_intersect_list _ ⊓ _]comm assoc.
      iApply lft_equiv_refl.
    + intros ty. rewrite elctx_interp_app.
      rewrite HE1 HE2. rewrite elctx_interp_app.
      rewrite -!assoc.
      iSplit; iIntros "(? & ? & ? & ?)"; iFrame.
  - destruct Hl1 as [α1 E1 βs1 Hα1 HE1].
    destruct Hl2 as [α2 E2 βs2 Hα2 HE2].
    apply direct_lft_morph_add.
    refine (mk_direct_lft_morph_add (α1 ⊓ α2) (E1 ++ E2) (βs1 ++ βs2) _ _).
    + iIntros (ty). rewrite lft_intersect_list_app.
      iApply lft_equiv_trans.
      { iApply lft_equiv_intersect; [iApply Hα1 |  iApply Hα2]. }
      rewrite -assoc. rewrite [lft_intersect_list _ ⊓ _]comm.
      rewrite -assoc.
      rewrite assoc.
      iApply lft_equiv_intersect; first iApply lft_equiv_refl.
      iApply lft_equiv_sym. iApply lft_intersect_idempotent.
    + intros ty. rewrite elctx_interp_app.
      rewrite HE1 HE2. rewrite elctx_interp_app.
      rewrite -!assoc.
      iSplit.
      * iIntros "(? & ? & ? & ? & ? & ?)". iFrame.
      * iIntros "(? & ? & #? & ? & ?)". iFrame. iFrame "#".
Qed.

Global Instance direct_lft_morph_make_const {rt} κs E :
  DirectLftMorphism (λ _ : type rt, κs) (λ _, E).
Proof.
  constructor.
  apply (mk_direct_lft_morph_const (lft_intersect_list κs) E).
  - iIntros (_). iApply lft_equiv_refl.
  - done.
Qed.
End lft_mor.

Section place_rfn.
  Context `{!typeGS Σ}.

  (**
    [PlaceIn]: the current inner refinement is accurate (no blocking of the inner refinement).
    [PlaceGhost]: the current inner refinement is determined by a ghost variable, either because it is currently blocked or was implicitly unblocked.
  *)
  Inductive place_rfn_mode := PlaceModeIn | PlaceModeGhost.
  (* concrete refinements *)
  Inductive place_rfn (rt : Type) :=
    | PlaceIn (r : rt)
    | PlaceGhost (γ : gname).
  Global Arguments PlaceIn {_}.
  Global Arguments PlaceGhost {_}.

  Global Instance place_rfn_inh rt : Inhabited (place_rfn rt).
  Proof. refine (populate (PlaceGhost inhabitant )). Qed.
  Global Instance place_rfn_mode_inh : Inhabited (place_rfn_mode).
  Proof. refine (populate (PlaceModeGhost)). Qed.

  (* interpretation of place_rfn under owned *)
  Definition place_rfn_interp_owned {rt} (r : place_rfn rt) (r' : rt) : iProp Σ :=
    match r with
    | PlaceIn r'' => ⌜r'' = r'⌝
    | PlaceGhost γ' => gvar_pobs γ' r'
    end.

  (* interpretation of place_rfn under mut *)
  Definition place_rfn_interp_mut {rt} (r : place_rfn rt) γ : iProp Σ :=
    match r with
    | PlaceIn r' => gvar_obs γ r'
    | PlaceGhost γ' => RelEq (T:=rt) γ' γ
    end.

  (* interpretation of place_rfn under shared *)
  (* we don't get any knowledge for PlaceGhost: we should really unblock before initiating sharing *)
  Definition place_rfn_interp_shared {rt} (r : place_rfn rt) (r' : rt) : iProp Σ :=
    match r with
    | PlaceIn r'' => ⌜r'' = r'⌝
    | PlaceGhost γ => gvar_pobs γ r'
    end.
  Global Instance place_rfn_interp_shared_pers {rt} (r : place_rfn rt) r' : Persistent (place_rfn_interp_shared r r').
  Proof. destruct r; apply _. Qed.
  (* NOTE: It's a bit unlucky that we have to rely on timelessness of this in some cases, in particular for some of the unfolding lemmas. *)
  (* Global Instance place_rfn_interp_shared_timeless {rt} (r : place_rfn rt) r' : Timeless (place_rfn_interp_shared r r'). *)
  (* Proof. destruct r; apply _. Qed. *)
  Global Instance place_rfn_interp_owned_timeless {rt} (r : place_rfn rt) r' : Timeless (place_rfn_interp_owned r r').
  Proof. destruct r; apply _. Qed.
  Global Instance place_rfn_interp_mut_timeless {rt} (r : place_rfn rt) γ : Timeless (place_rfn_interp_mut r γ).
  Proof. destruct r; apply _. Qed.

  Lemma place_rfn_interp_mut_iff {rt} (r : place_rfn rt) γ :
    place_rfn_interp_mut r γ ⊣⊢ ∃ r' : rt, gvar_obs γ r' ∗ match r with | PlaceGhost γ' => gvar_pobs γ' r' | PlaceIn r => ⌜r = r'⌝ end.
  Proof.
    destruct r as [ r | γ']; simpl.
    - iSplit.
      + iIntros "?"; eauto with iFrame.
      + iIntros "(%r' & ? & ->)"; iFrame.
    - rewrite /RelEq. iSplit.
      + iIntros "(%r1 & %r2 & ? & ? & ->)". iExists _. iFrame.
      + iIntros "(%r' & ? & ?)". iExists _, _. iFrame. done.
  Qed.

  Lemma place_rfn_interp_mut_owned {rt} (r : place_rfn rt) (r' : rt) γ :
    place_rfn_interp_mut r γ -∗
    gvar_auth γ r' ==∗
    place_rfn_interp_owned r r' ∗
    gvar_obs γ r' ∗ gvar_auth γ r'.
  Proof.
    iIntros "Hrfn Hauth".
    destruct r as [r'' | γ']; simpl.
    - iPoseProof (gvar_agree with "Hauth Hrfn") as "#->".
      iSplitR; first done. by iFrame.
    - rewrite /RelEq. iDestruct "Hrfn" as "(%r1 & %r2 & Hauth' & Hobs & ->)".
      iPoseProof (gvar_agree with "Hauth Hobs") as "#->". iFrame. done.
  Qed.
  Lemma place_rfn_interp_owned_mut {rt} (r : place_rfn rt) r' γ :
    place_rfn_interp_owned r r' -∗
    gvar_obs γ r' -∗
    place_rfn_interp_mut r γ.
  Proof.
    iIntros "Hrfn Hobs".
    destruct r as [r'' | γ'].
    - iDestruct "Hrfn" as "<-". iFrame.
    - iDestruct "Hrfn" as "Hauth'". simpl.
      rewrite /RelEq. iExists _, _. by iFrame.
  Qed.

  (** lemmas for sharing *)
  Lemma place_rfn_interp_owned_share' {rt} (r : place_rfn rt) (r' : rt) :
    place_rfn_interp_owned r r' -∗
    place_rfn_interp_shared r r'.
  Proof.
    iIntros "Hrfn".
    destruct r.
    - iDestruct "Hrfn" as "->". eauto.
    - iDestruct "Hrfn" as "#Hrfn". eauto.
  Qed.
  Lemma place_rfn_interp_owned_share F {rt} (r : place_rfn rt) (r' : rt) q κ :
    lftE ⊆ F →
    lft_ctx -∗
    &{κ} (place_rfn_interp_owned r r') -∗
    q.[κ] ={F}=∗
    place_rfn_interp_shared r r' ∗ q.[κ].
  Proof.
    iIntros (?) "#LFT Hb Htok".
    iMod (bor_acc with "LFT Hb Htok") as "(>Hrfn & Hcl)"; first solve_ndisj.
    iPoseProof (place_rfn_interp_owned_share' with "Hrfn") as "#Hrfn'".
    iMod ("Hcl" with "[//]") as "(? & $)". eauto.
  Qed.
  Lemma place_rfn_interp_mut_share' (F : coPset) {rt : RT} `{!Inhabited rt} (r : place_rfn rt) (r' : rt) γ (q : Qp) κ :
    lftE ⊆ F →
    lft_ctx -∗
    place_rfn_interp_mut r γ -∗
    &{κ} (gvar_auth γ r') -∗
    q.[κ] ={F}=∗
    place_rfn_interp_shared r r' ∗ (▷ place_rfn_interp_mut r γ) ∗ &{κ} (gvar_auth γ r') ∗ q.[κ].
  Proof.
    iIntros (?) "#CTX Hobs Hauth Htok".
    iMod (bor_acc with "CTX Hauth Htok") as "(>Hauth & Hcl_auth)"; first solve_ndisj.
    iAssert (|={F}=> place_rfn_interp_shared r r' ∗ gvar_auth γ r' ∗ ▷ place_rfn_interp_mut r γ)%I with "[Hauth Hobs]" as ">(Hrfn & Hauth & Hobs)".
    { destruct r.
      - iDestruct "Hobs" as "Hobs". iPoseProof (gvar_agree with "Hauth Hobs") as "#->". eauto with iFrame.
      - simpl. rewrite /RelEq. iDestruct "Hobs" as "(%v1 & %v2 & #Hpobs & Hobs & %Heq')". rewrite Heq'.
        iPoseProof (gvar_agree with "Hauth Hobs") as "%Heq". rewrite Heq.
        iFrame. iR. iModIntro. iModIntro. iExists _. iR. done.
    }
    iMod ("Hcl_auth" with "[$Hauth]") as "($ & Htoka2)".
    by iFrame.
  Qed.
  Lemma place_rfn_interp_mut_share (F : coPset) {rt : RT} `{!Inhabited rt} (r : place_rfn rt) (r' : rt) γ (q : Qp) κ :
    lftE ⊆ F →
    lft_ctx -∗
    &{κ} (place_rfn_interp_mut r γ) -∗
    &{κ} (gvar_auth γ r') -∗
    q.[κ] ={F}=∗
    place_rfn_interp_shared r r' ∗ &{κ} (place_rfn_interp_mut r γ) ∗ &{κ} (gvar_auth γ r') ∗ q.[κ].
  Proof.
    iIntros (?) "#CTX Hobs Hauth (Htok1 & Htok2)".
    iMod (bor_acc with "CTX Hobs Htok1") as "(>Hobs & Hcl_obs)"; first solve_ndisj.
    iMod (place_rfn_interp_mut_share' with "CTX Hobs Hauth Htok2") as "($ & Hmut & $ & $)"; first done.
    iMod ("Hcl_obs" with "[$Hmut]") as "($ & Htok_κ')".
    by iFrame.
  Qed.

  Lemma place_rfn_interp_shared_mut {rt} (r : place_rfn rt) r' γ :
    place_rfn_interp_shared r r' -∗
    gvar_obs γ r' -∗
    place_rfn_interp_mut r γ.
  Proof.
    iIntros "Hrfn Hobs".
    destruct r as [ r | γ']; simpl.
    - iDestruct "Hrfn" as "<-"; eauto with iFrame.
    - iExists _, _. eauto with iFrame.
  Qed.
  Lemma place_rfn_interp_shared_owned {rt} (r : place_rfn rt) r' :
    place_rfn_interp_shared r r' -∗
    place_rfn_interp_owned r r'.
  Proof. destruct r; eauto with iFrame. Qed.


  (** For adding information to the context *)
  Definition place_rfn_interp_mut_extracted {rt} (r : place_rfn rt) (γ : gname) : iProp Σ :=
    match r with
    | PlaceIn r' => gvar_pobs γ r'
    | PlaceGhost γ' => RelEq (T:=rt) γ' γ
    end.
  Definition place_rfn_interp_owned_extracted {rt} (r : place_rfn rt) (r' : rt) : iProp Σ :=
    match r with
    | PlaceIn r'' => ⌜r'' = r'⌝
    | PlaceGhost γ' => gvar_pobs γ' r'
    end.

  Lemma place_rfn_interp_mut_extract {rt} (r : place_rfn rt) (γ : gname) :
    place_rfn_interp_mut r γ ==∗ place_rfn_interp_mut_extracted r γ.
  Proof.
    destruct r; simpl.
    - iIntros "Hobs". iApply (gvar_obs_persist with "Hobs").
    - eauto.
  Qed.
  Lemma place_rfn_interp_owned_extract {rt} (r : place_rfn rt) (r' : rt) :
    place_rfn_interp_owned r r' ==∗ place_rfn_interp_owned_extracted r r'.
  Proof.
    destruct r; simpl.
    - eauto.
    - eauto.
  Qed.
End place_rfn.

Notation "# x" := (PlaceIn x) (at level 9) : stdpp_scope.
Notation "'<#>' x" := (fmap (M := list) PlaceIn x) (at level 30).
Notation "'<#>@{' A '}' x" := (fmap (M := A) PlaceIn x) (at level 30).
Notation "👻 γ" := (PlaceGhost γ) (at level 9) : stdpp_scope.

(** ** Basic enum infrastructure *)
Section enum.
  Context `{!typeGS Σ}.

  Record enum_tag_sem {rt : Type} := mk_enum_tag_sem {
    enum_tag_sem_rt : RT;
    enum_tag_sem_ty : type enum_tag_sem_rt;
    enum_tag_rt_inj : enum_tag_sem_rt → rt;
  }.
  Global Arguments enum_tag_sem : clear implicits.
  Global Arguments mk_enum_tag_sem {_}.

  Record enum (rt : RT) : Type := _mk_enum {
    enum_xt_inhabited : Inhabited (RT_xt rt);
    (* the layout spec *)
    enum_els : enum_layout_spec;
    (* out of the current refinement, extract the tag *)
    enum_tag : rt → option var_name;
    (* out of the current refinement, extract the component type and refinement *)
    enum_rt : rt → RT;
    enum_ty : ∀ r, type (enum_rt r);
    enum_r : ∀ r, enum_rt r;
    (* convenience function: given the variant name, also project out the type *)
    enum_tag_ty_inj :
      var_name →
      option (enum_tag_sem rt);
    (* explicitly track the lifetimes each of the variants needs -- needed for sharing *)
    enum_lfts : list lft;
    enum_wf_E : elctx;
    enum_lfts_complete : ∀ (r : rt), ty_lfts (enum_ty r) ⊆ enum_lfts;
    enum_wf_E_complete : ∀ (r : rt), ty_wf_E (enum_ty r) ⊆ enum_wf_E;
    enum_tag_compat : ∀ (r : rt) (variant : var_name),
      enum_tag r = Some variant →
      (*enum_tag_ty_inj variant = Some (mk_enum_tag_sem (enum_rt r) (enum_ty r));*)
      sigT (λ vinj, enum_tag_ty_inj variant = Some (mk_enum_tag_sem (enum_rt r) (enum_ty r) vinj));
  }.
  Global Arguments _mk_enum {_}.
  Global Arguments enum_xt_inhabited {_}.
  Global Arguments enum_els {_}.
  Global Arguments enum_tag {_}.
  Global Arguments enum_rt {_}.
  Global Arguments enum_r {_}.
  Global Arguments enum_ty {_}.
  Global Arguments enum_tag_ty_inj {_}.
  Global Arguments enum_lfts {_}.
  Global Arguments enum_wf_E {_}.
  Global Instance enum_rt_inhabited {rt} (e : enum rt) : Inhabited rt :=
    populate (RT_xrt rt e.(enum_xt_inhabited).(inhabitant)).

  (* Block TC resolution from solving the [Inhabited] requirement automatically to make automation more deterministic *)
  Definition mk_enum {rt : RT} (inh : TCNoResolve (Inhabited (RT_xt rt))) := _mk_enum inh.


  Definition enum_tag' {rt} (en : enum rt) (r : rt) : string :=
    default "" (enum_tag en r).

  Definition enum_lookup_tag {rt} (e : enum rt) (r : rt) : option Z :=
    fmap (els_lookup_tag e.(enum_els)) (e.(enum_tag) r).

  Definition size_of_enum_data (els : enum_layout_spec) :=
    ly_size (use_union_layout_alg' (uls_of_els els)).

  Definition els_data_ly (els : enum_layout_spec) :=
    use_union_layout_alg' (uls_of_els els).

  Import EqNotations.
  Lemma enum_tag_rt_eq {rt} (en : enum rt) r tag sem :
    enum_tag en r = Some tag →
    enum_tag_ty_inj en tag = Some sem →
    sem.(enum_tag_sem_rt) = enum_rt en r.
  Proof.
    intros Htag Hsem.
    odestruct (enum_tag_compat _ en) as (vinj & Htg); first done.
    simplify_eq. done.
  Defined.

  Lemma enum_tag_type_eq {rt} (en : enum rt) r tag sem
    (Heq : enum_tag en r = Some tag)
    (Hsem : enum_tag_ty_inj en tag = Some sem) :
    sem.(enum_tag_sem_ty) =
    rew <-[type] (enum_tag_rt_eq en r _ _ Heq Hsem) in enum_ty en r.
  Proof.
    odestruct (enum_tag_compat _ en) as (vinj & Htg); first done.
    simplify_eq.
    generalize (enum_tag_rt_eq en r tag _ Heq Hsem) as Heq2.
    simpl. intros Heq2. rewrite (UIP_refl _ _ Heq2); done.
  Qed.
  Lemma enum_tag_type_eq' {rt} (en : enum rt) r tag sem
    (Heq : enum_tag en r = Some tag)
    (Hsem : enum_tag_ty_inj en tag = Some sem) :
    rew ->[type] (enum_tag_rt_eq en r _ _ Heq Hsem) in sem.(enum_tag_sem_ty) =
    enum_ty en r.
  Proof.
    odestruct (enum_tag_compat _ en) as (vinj & Htg); first done.
    simplify_eq.
    generalize (enum_tag_rt_eq en r tag _ Heq Hsem) as Heq2.
    simpl. intros Heq2. rewrite (UIP_refl _ _ Heq2); done.
  Qed.
End enum.

(** ** Basic plain ADT infrastructure *)
(** Existential types with "simple" invariants that are tacked on via a separating conjunction *)
(* Note: this does not allow for, e.g., Cell or Mutex -- we will need a different version using non-atomic/atomic invariants for those *)
(*
  [X] is the inner refinement type,
  [Y] is the type it is being abstracted to.
*)
Record ex_inv_def `{!typeGS Σ} (X : RT) (Y : RT) : Type := mk_ex_inv_def' {
  inv_xr_inh : Inhabited (RT_xt Y);

  inv_P : thread_id → X → Y → iProp Σ;
  inv_P_shr : thread_id → lft → X → Y → iProp Σ;

  (* extra requirements on E and lfts, e.g. in case that P asserts extra location ownership *)
  inv_P_lfts : list lft;
  inv_P_wf_E : elctx;

  inv_P_shr_pers : ∀ π κ x y, Persistent (inv_P_shr π κ x y);
  inv_P_shr_mono : ∀ π κ κ' x y, κ' ⊑ κ -∗ inv_P_shr π κ x y -∗ inv_P_shr π κ' x y;
  inv_P_share :
    ∀ F π κ x y q,
    lftE ⊆ F →
    rrust_ctx -∗
    na_own π ∅ -∗
    let κ' := lft_intersect_list inv_P_lfts in
    q.[κ ⊓ κ'] -∗
    &{κ} (inv_P π x y) -∗
   logical_step F (inv_P_shr π κ x y ∗ q.[κ ⊓ κ']);
}.
(* Stop Typeclass resolution for the [inv_P_shr_pers] argument, to make it more deterministic. *)
Definition mk_ex_inv_def `{!typeGS Σ} {X Y : RT} `{!Inhabited (RT_xt Y)}
  (inv_P : thread_id → X → Y → iProp Σ)
  (inv_P_shr : thread_id → lft → X → Y → iProp Σ)
  inv_P_lfts
  (inv_P_wf_E : elctx)
  (inv_P_shr_pers : TCNoResolve (∀ (π : thread_id) (κ : lft) (x : X) (y : Y), Persistent (inv_P_shr π κ x y)))
  inv_P_shr_mono
  inv_P_share := mk_ex_inv_def' _ _ _ _ _ inv_P inv_P_shr inv_P_lfts inv_P_wf_E inv_P_shr_pers inv_P_shr_mono inv_P_share.
Global Arguments inv_P {_ _ _ _ _}.
Global Arguments inv_P_shr {_ _ _ _ _}.
Global Arguments inv_P_lfts {_ _ _ _ _}.
Global Arguments inv_P_wf_E {_ _ _ _ _}.
Global Arguments inv_P_share {_ _ _ _ _}.
Global Arguments inv_P_shr_mono {_ _ _ _ _}.
Global Arguments inv_P_shr_pers {_ _ _ _ _}.
Global Existing Instance inv_P_shr_pers.

(** Smart constructor for persistent and timeless [P] *)
Program Definition mk_pers_ex_inv_def `{!typeGS Σ} {X : RT} {Y : RT} `{!Inhabited (RT_xt Y)} (P : X → Y → iProp Σ)
  (_: TCNoResolve (∀ x y, Persistent (P x y))) (_: TCNoResolve (∀ x y, Timeless (P x y))) : ex_inv_def X Y :=
  mk_ex_inv_def (λ _, P) (λ _ _, P) [] [] _ _ _.
Next Obligation.
  rewrite /TCNoResolve.
  eauto with iFrame.
Qed.
Next Obligation.
  rewrite /TCNoResolve. eauto with iFrame.
Qed.
Next Obligation.
  rewrite /TCNoResolve.
  iIntros (????? P ?? F ? κ x y q ?) "#CTX Hna Htok Hb".
  iDestruct "CTX" as "(LFT & LLCTX)".
  iApply fupd_logical_step.
  rewrite right_id. iMod (bor_persistent with "LFT Hb Htok") as "(>HP & Htok)"; first done.
  iApply logical_step_intro. by iFrame.
Qed.
Global Arguments mk_pers_ex_inv_def : simpl never.

(** Typeclass to customize how a prop is shared *)
Class Shareable `{!typeGS Σ} (π : thread_id) (κ : lft) (κs : list lft) (P : iProp Σ) := {
  shareable_prop : iProp Σ;
  shareable_proof :
    ∀ F G q,
    lftE ⊆ F →
    rrust_ctx -∗
    na_own π ∅ -∗
    q.[κ] -∗
    q.[lft_intersect_list κs] -∗
    &{κ} P -∗
    (logical_step F
      (shareable_prop ∗ (q).[κ] ∗ (q).[lft_intersect_list κs] -∗
       G)) -∗
   logical_step F G;
}.
Global Hint Mode Shareable + + + + + + : typeclass_instances.

(** Smart constructor to auto derive the sharing predicate *)
Program Definition mk_auto_ex_inv_def `{!typeGS Σ} {X : RT} {Y : RT} `{!Inhabited (RT_xt Y)} (P : thread_id → X → Y → iProp Σ)
  (inv_P_lfts : list lft)
  (inv_P_wf_E : elctx)
  (Hshr : ∀ π κ x y, TCNoResolve (Shareable π κ inv_P_lfts (P π x y)))
  inv_P_shr_pers
  inv_P_shr_mono
  : ex_inv_def X Y :=
  mk_ex_inv_def P (λ π κ x y, (Hshr π κ x y).(shareable_prop)) inv_P_lfts inv_P_wf_E inv_P_shr_pers inv_P_shr_mono _.
Next Obligation.
  simpl.
  iIntros (???????? Hshr ? ? ? π κ x y ??).
  iIntros "CTX Hna Htok Hb".
  rewrite -lft_tok_sep.
  iDestruct "Htok" as "(Htok & Htok1)".
  iApply ((Hshr π κ x y).(shareable_proof) with "CTX Hna Htok Htok1 Hb"); first done.
  iApply logical_step_intro.
  eauto.
Qed.


Class ExInvDefNonExpansive `{!typeGS Σ} {rt X Y : RT} (F : type rt → ex_inv_def X Y) : Type := {
  ex_inv_def_ne_lft_mor : DirectLftMorphism (λ ty, (F ty).(inv_P_lfts)) (λ ty, (F ty).(inv_P_wf_E));

  ex_inv_def_ne_val_own :
    ∀ (n : nat) (ty ty' : type rt),
      TypeDist n ty ty' →
      ∀ π x y,
        (F ty).(inv_P) π x y ≡{n}≡ (F ty').(inv_P) π x y;

  ex_inv_def_ne_shr :
    ∀ (n : nat) (ty ty' : type rt),
      TypeDist2 n ty ty' →
      ∀ π κ x y,
        (F ty).(inv_P_shr) π κ x y ≡{n}≡ (F ty').(inv_P_shr) π κ x y;
}.

Class ExInvDefContractive `{!typeGS Σ} {rt X Y : RT} (F : type rt → ex_inv_def X Y) : Type := {
  ex_inv_def_contr_lft_mor : DirectLftMorphism (λ ty, (F ty).(inv_P_lfts)) (λ ty, (F ty).(inv_P_wf_E));

  ex_inv_def_contr_val_own :
    ∀ (n : nat) (ty ty' : type rt),
      TypeDist2 n ty ty' →
      ∀ π x y,
        (F ty).(inv_P) π x y ≡{n}≡ (F ty').(inv_P) π x y;

  ex_inv_def_contr_shr :
    ∀ (n : nat) (ty ty' : type rt),
      TypeDistLater2 n ty ty' →
      ∀ π κ x y,
        (F ty).(inv_P_shr) π κ x y ≡{n}≡ (F ty').(inv_P_shr) π κ x y;
}.

Section insts.
  Context `{!typeGS Σ}.

  Global Instance ex_inv_def_contractive_const {rt X Y} (v : ex_inv_def X Y) :
    ExInvDefContractive (λ _ : type rt, v).
  Proof.
    constructor.
    - apply (direct_lft_morph_make_const _ _).
    - eauto.
    - eauto.
  Qed.

  Global Instance ex_inv_def_ne_const {rt X Y} (v : ex_inv_def X Y) :
    ExInvDefNonExpansive (λ _ : type rt, v).
  Proof.
    constructor.
    - apply (direct_lft_morph_make_const _ _).
    - eauto.
    - eauto.
  Qed.

  (* TODO: instance for showing non-expansiveness from contractiveness? *)

End insts.

Section incl.
  Context `{!typeGS Σ}.

  Definition ex_inv_def_incl {X Y} (P1 P2 : ex_inv_def X Y) : iProp Σ :=
    (□ ∀ π x r, @inv_P _ _ _ _ P1 π x r -∗ @inv_P _ _ _ _ P2 π x r) ∗
    (□ ∀ π κ x r, @inv_P_shr _ _ _ _ P1 π κ x r -∗ @inv_P_shr _ _ _ _ P2 π κ x r).

  Definition ex_inv_def_sub (E : elctx) (L : llctx) {X Y} (P1 P2 : ex_inv_def X Y) : Prop :=
    ⊢ ∀ qL, llctx_interp_noend L qL -∗ elctx_interp E -∗ ex_inv_def_incl P1 P2.

  Lemma ex_inv_def_incl_refl {X Y} (P : ex_inv_def X Y) :
    ⊢ ex_inv_def_incl P P.
  Proof.
    iSplit; iModIntro; eauto.
  Qed.
  Lemma ex_inv_def_sub_refl E L {X Y} (P : ex_inv_def X Y) :
    ex_inv_def_sub E L P P.
  Proof.
    iIntros (?) "_ _". iApply ex_inv_def_incl_refl.
  Qed.
End incl.


(** Common RTs *)
Definition directRT (ty : Type) : RT :=
  mk_RT ty ty (@id ty).
Canonical Structure unitRT := directRT (unit : Type).
Canonical Structure ZRT := directRT (Z : Type).
Canonical Structure natRT := directRT (nat : Type).
Canonical Structure boolRT := directRT (bool : Type).

Canonical Structure gnameRT := directRT (gname : Type).
Canonical Structure locRT := directRT (loc : Type).
Canonical Structure valRT := directRT (val : Type).

Definition prodRT (rt1 rt2 : RT) : RT :=
  mk_RT (RT_rt rt1 * RT_rt rt2)%type (RT_xt rt1 * RT_xt rt2)%type (λ p, (RT_xrt rt1 p.1, RT_xrt rt2 p.2)).
Canonical Structure prodRT.

Definition listRT (A : RT) : RT :=
  mk_RT (list (RT_rt A)) (list (RT_xt A)) (fmap (RT_xrt A)).
Canonical Structure listRT.

Definition propRT : RT :=
  mk_RT Prop Prop id.
Canonical Structure propRT.

Canonical Structure funRT (A B : Type) : RT := directRT (A → B).

Definition resultRT (A1 A2 : RT) : RT :=
  mk_RT (result (RT_rt A1) (RT_rt A2)) (result (RT_xt A1) (RT_xt A2))
  (λ x,
    match x with
    | inl x => inl (RT_xrt A1 x)
    | inr x => inr (RT_xrt A2 x)
    end).
#[warning="-projection-no-head-constant"]
Canonical Structure resultRT.

Definition optionRT (A : RT) : RT :=
  mk_RT (option (RT_rt A)) (option (RT_xt A)) (fmap (RT_xrt A)).
Canonical Structure optionRT.

Definition place_rfnRT (rt : RT) : RT :=
  mk_RT (place_rfn (RT_rt rt))%type (RT_xt rt) (PlaceIn ∘ RT_xrt rt).
Canonical Structure place_rfnRT.

Definition plistRT (l : list RT) : RT :=
  mk_RT (plist (RT_rt ∘ place_rfnRT) l) (plist (RT_xt ∘ place_rfnRT) l)
    (pmap (F:=(RT_xt ∘ place_rfnRT))(G:= (RT_rt ∘ place_rfnRT))
      (λ (X : RT) (a : RT_xt (place_rfnRT X)), RT_xrt (place_rfnRT X) a))
.
Canonical Structure plistRT.
