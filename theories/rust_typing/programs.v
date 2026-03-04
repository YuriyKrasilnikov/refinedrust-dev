From caesium Require Import lang proofmode derived lifting.
From refinedrust Require Export base type ltypes lft_contexts annotations ltype_rules.
From refinedrust Require Import options.


Section named_lfts.
  Context `{typeGS Σ}.
  (** [named_lfts] is a construct used by the automation to map annotated lifetime names to concrete Coq names.
    This does not have a semantic meaning: we can in principle change this map arbitrarily, the worst thing that
    can happen is that the automation will make the goal unprovable.
    Invariant: there is a global singleton around.
   *)
  (* TODO: find a better way to seal this off and hide it from basic automation. *)
  Definition named_lfts (M : gmap string lft) : iProp Σ := True -∗ True.
  Lemma named_lfts_update M M' : named_lfts M -∗ named_lfts M'.
  Proof. auto. Qed.
  Definition lookup_named_lfts (M : gmap string lft) (lfts : list string) :=
    foldr (λ s oacc, acc ← oacc; κ ← M !! s; Some (κ :: acc)) (Some []) lfts.

  Lemma named_lfts_init (M : gmap string lft) : ⊢ named_lfts M.
  Proof. unfold named_lfts. iIntros "_". done. Qed.

  (* Making it opaque so that simplification doesn't get stuck with it *)
  Definition named_lft_update (name : string) (κ : lft) (M : gmap string lft) :=
    <[name := κ]> (M).

  Definition named_lft_delete (name : string) (M : gmap string lft) :=
    delete name M.
End named_lfts.
(* make opaque so that automation does not do weird things (this should not be persistent, etc.) *)
Global Typeclasses Opaque named_lfts.
Global Opaque named_lfts.
Global Arguments named_lfts : simpl never.
Global Opaque named_lft_update.
Global Opaque named_lft_delete.

Section named_tyvars.
  Context `{!typeGS Σ}.

  Definition TYVAR_MAP (m : gmap string (sigT type)) : Set := unit.
  Arguments TYVAR_MAP : simpl never.
End named_tyvars.

(** Hint for equality sideconditions to use a different strategy *)
Definition fast_eq_hint (P : Prop) : Prop :=
  P.
Global Typeclasses Opaque fast_eq_hint.
Arguments fast_eq_hint : simpl never.

(** Hint for solving credit store sideconditions *)
Definition fast_lia_hint (P : Prop) : Prop :=
  P.
Global Typeclasses Opaque fast_lia_hint.
Arguments fast_lia_hint : simpl never.

(** Hint for solving inclusion sideconditions *)
Definition fast_set_hint (P : Prop) : Prop :=
  P.
Global Typeclasses Opaque fast_set_hint.
Arguments fast_set_hint : simpl never.

(** Automation for finding the location for a local variable *)
Class FindLocalLoc (f : frame_path) (v : var_name) (l : loc) := {}.
Global Hint Mode FindLocalLoc + + - : typeclass_instances.
Global Instance find_local_loc `{!typeGS Σ} f v l st :
  CheckOwnInContext (v is_live{f, st} l) →
  FindLocalLoc f v l.
Proof. Qed.

Class FindLocalLocs (f : frame_path) (vars : list var_name) (locs : list loc) := {}.
Global Hint Mode FindLocalLocs + + - : typeclass_instances.

Global Instance find_local_locs_cons f x xs l ls :
  FindLocalLoc f x l →
  FindLocalLocs f xs ls →
  FindLocalLocs f (x :: xs) (l :: ls).
Proof. Qed.
Global Instance find_local_locs_nil f :
  FindLocalLocs f [] [].
Proof. Qed.

(** Instances for Lithium to put things into the persistent context *)
Section intro_persistent.
  Context `{!typeGS Σ}.

  Global Instance lft_dead_intro_pers κ : IntroPersistent ([† κ]) ([† κ]).
  Proof. constructor. iIntros "#$". Qed.
  Global Instance gvar_pobs_intro_pers {T} γ (x : T) : IntroPersistent (gvar_pobs γ x) (gvar_pobs γ x).
  Proof. constructor. iIntros "#$". Qed.
  Global Instance ty_sidecond_intro_pers {rt} (ty : type rt) : IntroPersistent (ty_sidecond ty) (ty_sidecond ty).
  Proof. constructor. iIntros "#$". Qed.

  Global Instance intro_persistent_loc_in_bounds l a b :
  IntroPersistent (loc_in_bounds l a b) (loc_in_bounds l a b).
  Proof.
    constructor. iIntros "#Ha". iFrame "#".
  Qed.
End intro_persistent.

Section credits.
  Context `{typeGS Σ}.

  (* We require at least one credit here so that the majority of clients does not need any sideconditions.
    We require at least one tr here, as place accesses will use the receipt every step gains for boosting, so we need to have at least one here to regenerate a potential credit we use.
   *)
  Definition credit_store_def (n m : nat) : iProp Σ :=
    £(S n) ∗ tr (S m).
  Definition credit_store_aux : seal (@credit_store_def). Proof. by eexists. Qed.
  Definition credit_store := unseal credit_store_aux.
  Definition credit_store_eq : @credit_store = @credit_store_def := seal_eq credit_store_aux.

  Lemma credit_store_acc (n m : nat) :
    credit_store n m -∗
    £ (S n) ∗ tr (S m) ∗ (∀ n' m', £ (S n') -∗ tr (S m') -∗ credit_store n' m').
  Proof.
    rewrite credit_store_eq /credit_store_def.
    iIntros "($ & $)". eauto with iFrame.
  Qed.

  (* allows direct access to one credit, and after regenerating some (usually m' = 0 or m' = 1), we get back *)
  Lemma credit_store_get_reg (n m : nat) :
    credit_store n m -∗
    £ 1 ∗ tr (S m) ∗ (∀ m', £ (1 + m' + m) -∗ tr (1 + m' + m) -∗ credit_store (m' + m + n) (m' + m)).
  Proof.
    iIntros "Hst". iPoseProof (credit_store_acc with "Hst") as "(Hcred & $ & Hcl)".
    rewrite lc_succ. iDestruct "Hcred" as "($ & Hcred)".
    iIntros (m') "Hcred' Hc".
    iPoseProof (lc_split with "[$Hcred' $Hcred]") as "Hcred".
    iApply ("Hcl" with "Hcred Hc").
  Qed.

  (* the two common instantiations of this *)
  Lemma credit_store_get_reg0 (n m : nat) :
    credit_store n m -∗
    £ 1 ∗ tr (S m) ∗ (£ (1 + m) -∗ tr (S m) -∗ credit_store (m + n) (m)).
  Proof.
    iIntros "Hst".
    iPoseProof (credit_store_get_reg with "Hst") as "($ & $ & Hcl)".
    iApply "Hcl".
  Qed.
  Lemma credit_store_get_reg1 (n m : nat) :
    credit_store n m -∗
    £ 1 ∗ tr (S m) ∗ (£ (S (S m)) -∗ tr (S (S m)) -∗ credit_store (1 + m + n) (1 + m)).
  Proof.
    iIntros "Hst".
    iPoseProof (credit_store_get_reg with "Hst") as "($ & $ & Hcl)".
    iApply ("Hcl" $! 1%nat).
  Qed.

  Lemma credit_store_borrow_receipt (n m : nat) :
    credit_store n m -∗
    tr 1 ∗ (tr 1 -∗ credit_store n m).
  Proof.
    iIntros "Hst".
    iPoseProof (credit_store_acc with "Hst") as "(Hcred & Hat & Hcl)".
    rewrite tr_succ. iDestruct "Hat" as "(Hat1 & Hat)".
    iFrame. iIntros "Hat1".
    iApply ("Hcl" with "Hcred [Hat1 Hat]").
    iApply tr_succ. iFrame.
  Qed.

  Lemma credit_store_borrow (n m : nat) :
    credit_store n m -∗
    £ 1 ∗ tr 1 ∗ (£ 1 -∗ tr 1 -∗ credit_store n m).
  Proof.
    iIntros "Hst".
    iPoseProof (credit_store_acc with "Hst") as "(Hcred & Hat & Hcl)".
    rewrite tr_succ. iDestruct "Hat" as "(Hat1 & Hat)".
    rewrite lc_succ. iDestruct "Hcred" as "(Hc1 & Hc)".
    iFrame. iIntros "Hc1 Hat1".
    iApply ("Hcl" with "[Hc Hc1] [Hat1 Hat]").
    { iApply lc_succ. iFrame. }
    iApply tr_succ. iFrame.
  Qed.

  (* allows direct access to credits, but without regenerating and instead requires to prove a sidecondition *)
  Lemma credit_store_scrounge {n m : nat} (k : nat) :
    n ≥ k →
    credit_store n m -∗
    £ k ∗ credit_store (n - k) m.
  Proof.
    iIntros (?) "Hst". iPoseProof (credit_store_acc with "Hst") as "(Hcred & Hc & Hcl)".
    replace (S n)%nat with (S (n - k) + k)%nat by lia.
    rewrite lc_split. iDestruct "Hcred" as "(Hcred & $)".
    iApply ("Hcl" with "Hcred Hc").
  Qed.
  Lemma credit_store_scrounge_tr {n m : nat} (k : nat) :
    m ≥ k →
    credit_store n m -∗
    tr k ∗ credit_store n (m - k).
  Proof.
    iIntros (?) "Hst". iPoseProof (credit_store_acc with "Hst") as "(Hcred & Hc & Hcl)".
    replace (S m)%nat with (S (m - k) + k)%nat by lia.
    rewrite tr_split. iDestruct "Hc" as "(Hc & $)".
    iApply ("Hcl" with "Hcred Hc").
  Qed.
  Lemma credit_store_donate n m k :
    credit_store n m -∗ £ k -∗ credit_store (k + n) m.
  Proof.
    iIntros "Hst Hcred0".
    iPoseProof (credit_store_acc with "Hst") as "(Hcred & Hat & Hcl)".
    iApply ("Hcl" with "[Hcred0 Hcred] Hat").
    iApply lc_succ. iDestruct "Hcred" as "($ & ?)".
    rewrite lc_split. iFrame.
  Qed.
  Lemma credit_store_donate_tr n m k :
    credit_store n m -∗ tr k -∗ credit_store n (k + m).
  Proof.
    iIntros "Hst Hat0".
    iPoseProof (credit_store_acc with "Hst") as "(Hcred & Hat & Hcl)".
    iApply ("Hcl" with "Hcred [Hat Hat0]").
    rewrite -Nat.add_succ_r. rewrite tr_split. iFrame.
  Qed.

  Lemma credit_store_mono (n m n' m' : nat) :
    n' ≤ n → m' ≤ m → credit_store n m -∗ credit_store n' m'.
  Proof.
    rewrite credit_store_eq/credit_store_def.
    iIntros (??) "(Ha & Hb)".
    iSplitL "Ha". { iApply lc_weaken; last done. lia. }
    iApply tr_weaken; last done. lia.
  Qed.
End credits.

Section simp_ltype.
  Context `{!typeGS Σ}.

  Class SimpLtype {rt} (lt1 lt2 : ltype rt) := mkSL {
    sl_proof : lt1 = lt2;
  }.
  Class SimpLtypes {rts} (lts1 lts2 : hlist ltype rts) := mkSLs {
    sls_proof : lts1 = lts2;
  }.
  Class SimpLtypeIds {rt} (lts1 lts2 : list (nat * ltype rt)) := mkSLIs {
    slis_proof : lts1 = lts2;
  }.

  Global Instance simp_ltypes_nil :
    SimpLtypes +[] +[].
  Proof. by econstructor. Qed.
  Global Instance simp_ltypes_cons {rt rts} (lt1 lt2 : ltype rt) (lts1 lts2 : hlist ltype rts)  :
    SimpLtype lt1 lt2 →
    SimpLtypes lts1 lts2 →
    SimpLtypes (lt1 +:: lts1) (lt2 +:: lts2).
  Proof.
    intros [<-] [<-].
    done.
  Qed.

  Global Instance simp_ltype_ids_nil rt :
    SimpLtypeIds (rt:=rt) [] [].
  Proof. by econstructor. Qed.
  Global Instance simp_ltype_ids_cons {rt} (lt1 lt2 : ltype rt) i lts1 lts2  :
    SimpLtype lt1 lt2 →
    SimpLtypeIds lts1 lts2 →
    SimpLtypeIds ((i, lt1) :: lts1) ((i, lt2) :: lts2).
  Proof.
    intros [<-] [<-].
    done.
  Qed.

  Global Instance simp_ltype_ofty {rt} (ty : type rt) :
    SimpLtype (ltype_core (◁ ty))%I (◁ ty)%I.
  Proof.
    econstructor. by rewrite ltype_core_ofty.
  Qed.
  Global Instance simp_ltype_core {rt} (lt : ltype rt) lt' :
    SimpLtype (ltype_core lt) lt' →
    SimpLtype (ltype_core (ltype_core lt)) lt'.
  Proof.
    intros [<-]. econstructor. by rewrite ltype_core_idemp.
  Qed.
  Global Instance simp_ltype_alias {rt} st p :
    SimpLtype (ltype_core (AliasLtype rt st p)) (AliasLtype rt st p).
  Proof.
    econstructor. by rewrite ltype_core_alias.
  Qed.
  Global Instance simp_ltype_blocked {rt} (ty : type rt) κ :
    SimpLtype (ltype_core (BlockedLtype ty κ)) (◁ ty)%I.
  Proof.
    econstructor. by rewrite ltype_core_blocked.
  Qed.
  Global Instance simp_ltype_shrblocked {rt} (ty : type rt) κ :
    SimpLtype (ltype_core (ShrBlockedLtype ty κ)) (◁ ty)%I.
  Proof.
    econstructor. by rewrite ltype_core_shrblocked.
  Qed.
  Global Instance simp_ltype_mut {rt} (lt lt' : ltype rt) κ :
    SimpLtype (ltype_core lt) lt' →
    SimpLtype (ltype_core (MutLtype lt κ)) (MutLtype lt' κ).
  Proof.
    intros [<-]. econstructor. by rewrite ltype_core_mut_ref.
  Qed.
  Global Instance simp_ltype_shr {rt} (lt lt' : ltype rt) κ :
    SimpLtype (ltype_core lt) lt' →
    SimpLtype (ltype_core (ShrLtype lt κ)) (ShrLtype lt' κ).
  Proof.
    intros [<-]. econstructor. by rewrite ltype_core_shr_ref.
  Qed.
  Global Instance simp_ltype_struct {rts} (lts lts' : hlist ltype rts) sls :
    SimpLtypes (@ltype_core _ _ +<$> lts) lts' →
    SimpLtype (ltype_core (StructLtype lts sls)) (StructLtype lts' sls).
  Proof.
    intros [<-]. econstructor. by rewrite ltype_core_struct.
  Qed.
  Global Instance simp_ltype_array {rt} (ty : type rt) n es es' :
    SimpLtypeIds ((λ '(i, lt), (i, ltype_core lt)) <$> es) es' →
    SimpLtype (ltype_core (ArrayLtype ty n es)) (ArrayLtype ty n es').
  Proof.
    intros [<-]. econstructor. by rewrite ltype_core_array.
  Qed.
  Global Instance simp_ltype_enum {rt rte} (en : enum rt) tag (lte lte' : ltype rte) re :
    SimpLtype (ltype_core lte) lte' →
    SimpLtype (ltype_core (EnumLtype en tag lte re)) (EnumLtype en tag lte' re).
  Proof.
    intros [<-]. econstructor. by rewrite ltype_core_enum.
  Qed.
  Global Instance simp_ltype_opened {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost :
    SimpLtype (ltype_core (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost)) (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost).
  Proof.
    by rewrite ltype_core_opened.
  Qed.
  Global Instance simp_ltype_coreable {rt_full} (lt_full lt_full' : ltype rt_full) κs :
    SimpLtype (ltype_core lt_full) lt_full' →
    SimpLtype (ltype_core (CoreableLtype κs lt_full)) lt_full'.
  Proof.
    intros [<-]. econstructor. by rewrite ltype_core_coreable.
  Qed.
  Global Instance ltype_core_shadowed {rt_cur rt_full} (lt_cur : ltype rt_cur) (lt_full lt_full' : ltype rt_full) r_cur :
    SimpLtype (ltype_core lt_full) lt_full' →
    SimpLtype (ltype_core (ShadowedLtype lt_cur r_cur lt_full)) lt_full'.
  Proof.
    intros [<-]. econstructor. by rewrite ltype_core_shadowed.
  Qed.
  Global Instance simp_ltype_openedna {rt_cur rt_inner} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) Cpre Cpost :
    SimpLtype (ltype_core (OpenedNaLtype lt_cur lt_inner Cpre Cpost)) (OpenedNaLtype lt_cur lt_inner Cpre Cpost).
  Proof.
    by rewrite ltype_core_opened_na.
  Qed.
End simp_ltype.
Global Hint Mode SimpLtypes + + + + - : typeclass_instances.
Global Hint Mode SimpLtypeIds + + + + - : typeclass_instances.
Global Hint Mode SimpLtype + + + + - : typeclass_instances.

(** Agreement-style propositions *)
Class LiAgree {Σ} {A} (P : iProp Σ) (P' : A → iProp Σ) := {
  li_agree_elem : A;
  li_agree_to_pred : P ⊣⊢ P' li_agree_elem;
  li_agree_pers : ∀ a, Persistent (P' a);
  li_agree_agree : ⊢ ∀ a b, P' a -∗ P' b -∗ ⌜a = b⌝;
}.


(** find type of val in context *)
Definition FindVal `{!typeGS Σ} (v : val) :=
  {| fic_A := @sigT RT (λ rt, type rt * rt * thread_id * metadata)%type; fic_Prop '(existT rt (ty, r, π, m)) := (v ◁ᵥ{π, m} r @ ty)%I; |}.
Global Typeclasses Opaque FindVal.

(** find type of val in context -- also allows to find location assignments by accepting an arbitrary prop [P].
  Thus, this is used mostly for RelatedTo/Subsume *)
Definition FindValP `{!typeGS Σ} (v : val) :=
  {| fic_A := iProp Σ; fic_Prop P := P |}.
Global Typeclasses Opaque FindValP.

(** find type of val with known rt in context *)
Definition FindValWithRt `{!typeGS Σ} (rt : RT) (v : val) (π : thread_id) :=
  {| fic_A := (type rt * rt * metadata)%type; fic_Prop '(ty, r, m) := (v ◁ᵥ{π, m} r @ ty)%I; |}.
Global Typeclasses Opaque FindValWithRt.

(** find type of location in context *)
Definition FindLoc `{!typeGS Σ} (l : loc) :=
  {| fic_A := @sigT RT (λ rt, ltype rt * (place_rfn rt) * bor_kind * thread_id)%type; fic_Prop '(existT rt (lt, r, b, π)) := (l ◁ₗ[π, b] r @ lt)%I; |}.
Global Typeclasses Opaque FindLoc.

Definition FindOptLoc `{!typeGS Σ} (l : loc) :=
  {| fic_A := option (@sigT RT (λ rt, ltype rt * (place_rfn rt) * bor_kind * thread_id)%type); fic_Prop a :=
      match a with Some (existT rt (lt, r, b, π)) => (l ◁ₗ[π, b] r @ lt)%I | _ => True%I end; |}.
Global Typeclasses Opaque FindOptLoc.

(** Find freeable_nz for a location *)
Definition FindFreeable `{!typeGS Σ} (l : loc) :=
  {| fic_A := (nat * Qp * alloc_kind); fic_Prop '(size, q, kind) := freeable_nz l size q kind |}.
Global Typeclasses Opaque FindFreeable.

(** find type of location in context -- more flexible by accepting an arbitrary prop [P].
  Thus, this is used mostly for RelatedTo/Subsume *)
Definition FindLocP `{!typeGS Σ} (l : loc) :=
  {| fic_A := iProp Σ; fic_Prop P := P |}.
Global Typeclasses Opaque FindLocP.

(** find type of location with known rt in context *)
Definition FindLocWithRt `{!typeGS Σ} (rt : RT) (l : loc) (π : thread_id) :=
  {| fic_A := (ltype rt * (place_rfn rt) * bor_kind)%type; fic_Prop '(lt, r, b) := (l ◁ₗ[π, b] r @ lt)%I; |}.
Global Typeclasses Opaque FindLocWithRt.

(* Find a local variable mapping *)
Definition FindLocal `{!typeGS Σ} (f : frame_path) (x : var_name) :=
  {| fic_A := (syn_type * loc)%type;
     fic_Prop '(st, l) := (x is_live{f, st} l)%I; |}.
Global Typeclasses Opaque FindLocal.

(* Find the set of local variables in a frame *)
Definition FindFrameLocals `{!typeGS Σ} (f : frame_path) :=
  {| fic_A := list var_name;
     fic_Prop locals := (allocated_locals f locals); |}.
Global Typeclasses Opaque FindFrameLocals.


(** find a loc_in_bounds fact for l.
   We also allow other propositions [P], in particular location ownership,
   and will handle them using subsume instances. *)
Definition FindLocInBounds `{!typeGS Σ} (l : loc) :=
  {| fic_A := iProp Σ; fic_Prop P := P |}.
Global Typeclasses Opaque FindLocInBounds.

(** find the named lifetime judgment *)
Definition FindNamedLfts `{!typeGS Σ} :=
  {| fic_A := gmap string lft; fic_Prop M := (named_lfts (Σ := Σ) M)%I; |}.
Global Typeclasses Opaque FindNamedLfts.

(** find the credit store *)
Definition FindCreditStore `{!typeGS Σ} :=
  {| fic_A := nat * nat; fic_Prop '(n, m) := credit_store n m; |}.
Global Typeclasses Opaque FindCreditStore.

(** find the mask token *)
Definition FindNaOwn `{!typeGS Σ} (π : thread_id) :=
  {| fic_A := coPset; fic_Prop '(E) := na_own π E; |}.
Global Typeclasses Opaque FindNaOwn.

Definition FindOptNaOwn `{!typeGS Σ} (π : thread_id) :=
  {| fic_A := option coPset;
     fic_Prop a :=
        match a with
        | Some (E) => na_own π E
        | _ => True%I
        end
  |}.
Global Typeclasses Opaque FindOptNaOwn.

(** find a lft dead token *)
Definition FindOptLftDead `{!typeGS Σ} (κ : lft) :=
  {| fic_A := bool; fic_Prop b := (if b then [† κ] else True)%I; |}.
Global Typeclasses Opaque FindOptLftDead.

Definition FindLftDead `{!typeGS Σ} (κ : lft) :=
  {| fic_A := (); fic_Prop _ := [† κ]%I; |}.
Global Typeclasses Opaque FindLftDead.

(** attempt to find an observation, or give up if there is none *)
Definition FindOptGvarPobs `{!typeGS Σ} (γ : gname) :=
  {| fic_A := (@sigT RT (λ rt, rt) + unit)%type;
    fic_Prop a :=
      match a with
      | inl (existT rt r) => (gvar_pobs γ r)%I
      | inr _ => True%I
      end
  |}.
Global Typeclasses Opaque FindOptGvarPobs.

(** attempt to find an inheritance for an observation, or give up *)
Definition FindOptInheritGvarPobs `{!typeGS Σ} (γ : gname) :=
  {| fic_A := ((list lft * @sigT RT (λ rt, rt))%type + unit)%type;
    fic_Prop a :=
      match a with
      | inl (κs, existT rt r) => Inherit κs (gvar_pobs γ r)%I
      | inr _ => True%I
      end
  |}.
Global Typeclasses Opaque FindOptInheritGvarPobs.

(** attempt to find an inheritance for an observation, or give up *)
Definition FindOptInheritGvarRelEq `{!typeGS Σ} (γ : gname) :=
  {| fic_A := ((list lft * RT * gname) + unit)%type;
    fic_Prop a :=
      match a with
      | inl (κs, rt, γ') => Inherit κs (RelEq (T:=rt) γ' γ)%I
      | inr _ => True%I
      end
  |}.
Global Typeclasses Opaque FindOptInheritGvarRelEq.

(** find an observation on a ghost variable *)
(** NOTE: Ideally, we would also fix the type beforehand.
  However, that leads to universe trouble when using the definition that I have not yet figured out.
*)
Definition FindGvarPobs `{!typeGS Σ} (γ : gname) :=
  {| fic_A := (@sigT RT (λ rt, rt))%type;
    fic_Prop '(existT rt r) := (gvar_pobs γ r)%I
  |}.
Global Typeclasses Opaque FindGvarPobs.
Definition FindGvarPobsP `{!typeGS Σ} (γ : gname) :=
  {| fic_A := iProp Σ;
    fic_Prop P := P
  |}.
Global Typeclasses Opaque FindGvarPobsP.

(** Find a relation with the given gvar on the right hand side. *)
Definition FindOptGvarRelEq `{!typeGS Σ} (γ : gname) :=
  {| fic_A := ((RT * gname) + unit)%type;
    fic_Prop a :=
      match a with
      | inl (rt, γ') => (RelEq (T:=rt) γ' γ)%I
      | inr _ => True%I
      end
  |}.
Global Typeclasses Opaque FindOptGvarRelEq.

Definition FindInherit `{!typeGS Σ} (κs : list lft) (P : iProp Σ) :=
  {| fic_A := ();
     fic_Prop _ := Inherit κs P;
  |}.
Global Typeclasses Opaque FindInherit.

(** Find a type assignment for a location [l] that may be part of a larger type assignment -- e.g. if [l] offsets into an array, this will find a type assignment for an array whose memory range includes [l].

   Note that the obligation stated here does not require that [l] and the actually found here are in any way related -- rather, this will be enforced by the corresponding [FindHypEqual] with a custom [FICRelated] key, defined in [automation/loc_related.v].
   The client needing this information will have to spawn a sidecondition (re-)proving it.
*)
Definition FindRelatedLoc `{!typeGS Σ} (π : thread_id) :=
  {| fic_A := @sigT RT (λ rt, loc * ltype rt * (place_rfn rt) * bor_kind)%type;
     fic_Prop '(existT rt (l', lt, r, b)) := (l' ◁ₗ[π, b] r @ lt)%I;
  |}.
Global Typeclasses Opaque FindRelatedLoc.

(** Degenerate instance for optionally finding any guarded proposition in the context. *)
Definition FindOptGuarded `{!typeGS Σ} :=
  {| fic_A := option (bool * iProp Σ)%type;
     fic_Prop x := if_iSome x (λ '(prepaid, P), guarded prepaid P);
  |}.
Global Typeclasses Opaque FindOptGuarded.

(** A judgment to trigger TC search on [H] for some output [a : A]. *)
Definition trigger_tc `{!typeGS Σ} {A} (H : A → Type) (T : A → iProp Σ) : iProp Σ :=
  ∃ (a : A) (x : H a), T a.
Definition find_tc_inst `{!typeGS Σ} (H : Type) (T : H → iProp Σ) : iProp Σ :=
  ∃ (x : H), T x.

Section judgments.
  Context `{typeGS Σ}.
  Implicit Types (rt : RT).

  Class SimplifyHypPlace (l : loc) (π : thread_id) {rt} (ty : type rt) (r : place_rfn rt) (n : option N) : Type :=
    simplify_hyp_place :: SimplifyHyp (l ◁ₗ[π, Owned] r @ (◁ ty)%I) n.
  Global Hint Mode SimplifyHypPlace + + + + + - : typeclass_instances.
  Class SimplifyHypVal (v : val) (π : thread_id) {rt} (ty : type rt) (r : rt) (m : metadata) (n : option N) : Type :=
    simplify_hyp_val :: SimplifyHyp (v ◁ᵥ{π, m} r @ ty) n.
  Global Hint Mode SimplifyHypVal + + + + + + - : typeclass_instances.

  Class SimplifyGoalPlace (l : loc) π (b : bor_kind) {rt} (lty : ltype rt) (r : place_rfn rt) (n : option N) : Type :=
    simplify_goal_place :: SimplifyGoal (l ◁ₗ[π, b] r @ lty) n.
  Global Hint Mode SimplifyGoalPlace + + + - - - - : typeclass_instances.
  Class SimplifyGoalVal (v : val) π {rt} (ty : type rt) (r : rt) (m : metadata) (n : option N) : Type :=
    simplify_goal_val :: SimplifyGoal (v ◁ᵥ{π, m} r @ ty) n.
  Global Hint Mode SimplifyGoalVal + + - - - - - : typeclass_instances.

  (** Notion of [subsume] with support for lifetime contexts + executing updates *)
  Definition subsume_full (E : elctx) (L : llctx) (step : bool) (P : iProp Σ) (Q : iProp Σ) (T : llctx → iProp Σ → iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ ⌜lft_userE ⊆ F⌝ -∗ ⌜shrE ⊆ F⌝ -∗
      rrust_ctx -∗
      elctx_interp E -∗
      llctx_interp L -∗
      P -∗ |={F}=>
      ∃ L' R, maybe_logical_step step F (Q ∗ R) ∗ llctx_interp L' ∗ T L' R.
  Class SubsumeFull (E : elctx) (L : llctx) (step : bool) (P Q : iProp Σ) : Type :=
    subsume_full_proof T : iProp_to_Prop (subsume_full E L step P Q T).

  Lemma subsume_full_id E L step P T :
    T L True ⊢ subsume_full E L step P P T.
  Proof.
    iIntros "HT" (????) "CTX HE HL ?".
    iExists L, True%I. iFrame.
    iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Global Instance subsume_full_id_inst E L step (P : iProp Σ) : SubsumeFull E L step P P := λ T, i2p (subsume_full_id E L step P T).

  Lemma subsume_full_subsume E L step P Q T :
    subsume P Q (T L True) ⊢
    subsume_full E L step P Q T.
  Proof.
    iIntros "Hsub" (????) "#CTX #HE HL HP". iPoseProof ("Hsub" with "HP") as "(HQ & HT)".
    iExists L, True%I; iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  (* low priority, should not trigger when there are other more specific instances *)
  Global Instance subsume_full_subsume_inst E L step P Q : SubsumeFull E L step P Q | 2000 :=
    λ T, i2p (subsume_full_subsume E L step P Q T).

  Class SubsumeFullPlace (E : elctx) (L : llctx) (step : bool) (l : loc) (π : thread_id) (b : bor_kind) {rt1} (ty1 : ltype rt1) (r1 : place_rfn rt1) {rt2} (ty2 : ltype rt2) (r2 : place_rfn rt2) : Type :=
    subsume_full_place :: SubsumeFull E L step (l ◁ₗ[π, b] r1 @ ty1) (l ◁ₗ[π, b] r2 @ ty2).
  Global Hint Mode SubsumeFullPlace + + + + + + ! ! ! - - - : typeclass_instances.
  Class SubsumeFullVal (π : thread_id) (E : elctx) (L : llctx) (step : bool) (v : val) {rt1} (ty1 : type rt1) (r1 : rt1) (m1 : metadata) {rt2} (ty2 : type rt2) (r2 : rt2) (m2 : metadata) : Type :=
    subsume_full_val :: SubsumeFull E L step (v ◁ᵥ{π, m1} r1 @ ty1) (v ◁ᵥ{π, m2} r2 @ ty2).
  Global Hint Mode SubsumeFullVal + + + + + ! ! ! ! - - - - : typeclass_instances.

  (** *** Expressions *)

  (** Typing of values *)
  Definition typed_value_cont_t := metadata → ∀ rt, type rt → rt → iProp Σ.
  Definition typed_value (π : thread_id) (v : val) (T : typed_value_cont_t) : iProp Σ :=
    (rrust_ctx -∗ ∃ rt (ty : type rt) r m, v ◁ᵥ{π, m} r @ ty ∗ T m rt ty r).
  Class TypedValue π (v : val) : Type :=
    typed_value_proof T : iProp_to_Prop (typed_value π v T).

  (** Typing of value expressions (unfolding [typed_value] for easier usage) *)
  Definition typed_val_expr_cont_t := llctx → val → metadata → ∀ (rt : RT), type rt → rt → iProp Σ.
  Definition typed_val_expr (E : elctx) (L : llctx) (f : frame_path) (e : expr) (T : typed_val_expr_cont_t) : iProp Σ :=
    (∀ Φ, rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      current_frame f.1 f.2 -∗
      (∀ L' v rt (ty : type rt) r m,
        llctx_interp L' -∗ current_frame f.1 f.2 -∗ v ◁ᵥ{f.1, m} r @ ty -∗ T L' v m rt ty r -∗ Φ v) -∗
    WPe{f.1} e {{ Φ }}).

  (** Typing of binary op expressions *)
  Definition typed_bin_op (E : elctx) (L : llctx) (f : frame_path) (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ)
    (o : bin_op) (ot1 ot2 : op_type) (T : typed_val_expr_cont_t) : iProp Σ :=
    (P1 -∗ P2 -∗ typed_val_expr E L f (BinOp o ot1 ot2 v1 v2) T).
  Class TypedBinOp (E : elctx) (L : llctx) (f : frame_path) (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ) (o : bin_op) (ot1 ot2 : op_type) : Type :=
    typed_bin_op_proof T : iProp_to_Prop (typed_bin_op E L f v1 P1 v2 P2 o ot1 ot2 T).

  (* class for instances specialized to value ownership *)
  Class TypedBinOpVal (E : elctx) (L : llctx) (f : frame_path) (v1 : val) {rt1} (ty1 : type rt1) (r1 : rt1) (v2 : val) {rt2} (ty2 : type rt2) (r2 : rt2) (o : bin_op) (ot1 ot2 : op_type) : Type :=
    typed_bin_op_val :: TypedBinOp E L f v1 (v1 ◁ᵥ{f.1, MetaNone} r1 @ ty1) v2 (v2 ◁ᵥ{f.1, MetaNone} r2 @ ty2) o ot1 ot2.
  Global Hint Mode TypedBinOpVal + + + + + + + + + + + + + + : typeclass_instances.

  (** Checking for overflows *)
  Definition typed_check_bin_op (E : elctx) (L : llctx) (f : frame_path) (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ)
    (o : bin_op) (ot1 ot2 : op_type) (T : typed_val_expr_cont_t) : iProp Σ :=
    (P1 -∗ P2 -∗ typed_val_expr E L f (CheckBinOp o ot1 ot2 v1 v2) T).
  Class TypedCheckBinOp (E : elctx) (L : llctx) (f : frame_path) (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ) (o : bin_op) (ot1 ot2 : op_type) : Type :=
    typed_check_bin_op_proof T : iProp_to_Prop (typed_check_bin_op E L f v1 P1 v2 P2 o ot1 ot2 T).

  (** Typing of unary op expressions *)
  Definition typed_un_op (E : elctx) (L : llctx) (f : frame_path) (v : val) (P : iProp Σ) (o : un_op) (ot : op_type)
    (T : typed_val_expr_cont_t) : iProp Σ :=
    (P -∗ typed_val_expr E L f (UnOp o ot v) T).
  Class TypedUnOp (E : elctx) (L : llctx) (f : frame_path) (v : val) (P : iProp Σ) (o : un_op) (ot : op_type) : Type :=
    typed_un_op_proof T : iProp_to_Prop (typed_un_op E L f v P o ot T).

  (* class for instances specialized to value ownership *)
  Class TypedUnOpVal (E : elctx) (L : llctx) (f : frame_path) (v : val) {rt} (ty : type rt) (r : rt) (o : un_op) (ot : op_type) : Type :=
    typed_un_op_val :: TypedUnOp E L f v (v ◁ᵥ{f.1, MetaNone} r @ ty) o ot.
  Global Hint Mode TypedUnOpVal + + + + + + + + + : typeclass_instances.

  (** Checking for overflows *)
  Definition typed_check_un_op (E : elctx) (L : llctx) (f : frame_path) (v : val) (P : iProp Σ) (o : un_op) (ot : op_type)
    (T : typed_val_expr_cont_t) : iProp Σ :=
    (P -∗ typed_val_expr E L f (CheckUnOp o ot v) T).
  Class TypedCheckUnOp (E : elctx) (L : llctx) (f : frame_path) (v : val) (P : iProp Σ) (o : un_op) (ot : op_type) : Type :=
    typed_check_un_op_proof T : iProp_to_Prop (typed_check_un_op E L f v P o ot T).

  (** Typing of CAS expressions *)
  Definition typed_cas (E : elctx) (L : llctx) (f : frame_path)
    (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ) (v3 : val) (P3 : iProp Σ)
    (ot : op_type) (T : typed_val_expr_cont_t) : iProp Σ :=
    (P1 -∗ P2 -∗ P3 -∗ typed_val_expr E L f (CAS ot v1 v2 v3) T).
  Class TypedCas (E : elctx) (L : llctx) (f : frame_path)
    (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ) (v3 : val) (P3 : iProp Σ)
    (ot : op_type) : Type :=
    typed_cas_proof T : iProp_to_Prop (typed_cas E L f v1 P1 v2 P2 v3 P3 ot T).

  (* class for instances specialized to value ownership *)
  Class TypedCasVal (E : elctx) (L : llctx) (f : frame_path)
    (v1 : val) {rt1} (ty1 : type rt1) (r1 : rt1)
    (v2 : val) {rt2} (ty2 : type rt2) (r2 : rt2)
    (v3 : val) {rt3} (ty3 : type rt3) (r3 : rt3)
    (ot : op_type) : Type :=
    typed_cas_val :: TypedCas E L f
      v1 (v1 ◁ᵥ{f.1, MetaNone} r1 @ ty1)
      v2 (v2 ◁ᵥ{f.1, MetaNone} r2 @ ty2)
      v3 (v3 ◁ᵥ{f.1, MetaNone} r3 @ ty3) ot.
  Global Hint Mode TypedCasVal + + + + + + + + + + + + + + + + : typeclass_instances.

  (** Typing of atomic read-modify-write expressions *)
  Definition typed_atomic_rmw (E : elctx) (L : llctx) (f : frame_path)
    (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ)
    (op : atomic_rmw_op) (ot : op_type) (T : typed_val_expr_cont_t) : iProp Σ :=
    (P1 -∗ P2 -∗ typed_val_expr E L f (AtomicRMW op ot v1 v2) T).
  Class TypedAtomicRmw (E : elctx) (L : llctx) (f : frame_path)
    (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ)
    (op : atomic_rmw_op) (ot : op_type) : Type :=
    typed_atomic_rmw_proof T : iProp_to_Prop (typed_atomic_rmw E L f v1 P1 v2 P2 op ot T).

  (* class for instances specialized to value ownership *)
  Class TypedAtomicRmwVal (E : elctx) (L : llctx) (f : frame_path)
    (v1 : val) {rt1} (ty1 : type rt1) (r1 : rt1)
    (v2 : val) {rt2} (ty2 : type rt2) (r2 : rt2)
    (op : atomic_rmw_op) (ot : op_type) : Type :=
    typed_atomic_rmw_val :: TypedAtomicRmw E L f
      v1 (v1 ◁ᵥ{f.1, MetaNone} r1 @ ty1)
      v2 (v2 ◁ᵥ{f.1, MetaNone} r2 @ ty2) op ot.
  Global Hint Mode TypedAtomicRmwVal + + + + + + + + + + + + + : typeclass_instances.

  (** Typing of atomic load expressions (ScOrd deref).

      The instance opens the atomic invariant, executes [wp_deref ScOrd]
      at the reduced mask, closes the invariant, and returns the loaded
      value to the continuation [T].

      Structurally identical to CAS: evaluate pointer arg to value,
      then dispatch to instance via [find_in_context (FindLoc l)]. *)
  Definition typed_atomic_load (E : elctx) (L : llctx) (f : frame_path)
    (v : val) (P : iProp Σ) (ot : op_type) (T : typed_val_expr_cont_t) : iProp Σ :=
    (P -∗ typed_val_expr E L f (Deref ScOrd ot true v) T).
  Class TypedAtomicLoad (E : elctx) (L : llctx) (f : frame_path)
    (v : val) (P : iProp Σ) (ot : op_type) : Type :=
    typed_atomic_load_proof T : iProp_to_Prop (typed_atomic_load E L f v P ot T).

  (* class for instances specialized to value ownership *)
  Class TypedAtomicLoadVal (E : elctx) (L : llctx) (f : frame_path)
    (v : val) {rt} (ty : type rt) (r : rt)
    (ot : op_type) : Type :=
    typed_atomic_load_val :: TypedAtomicLoad E L f
      v (v ◁ᵥ{f.1, MetaNone} r @ ty) ot.
  Global Hint Mode TypedAtomicLoadVal + + + + + + + + : typeclass_instances.

  (** Typed call expressions, assuming a list of argument values with given types and refinements.
    [P] may state additional preconditions on the function. *)
  Definition typed_call_cont_t := llctx → val → ∀ rt : RT, type rt → rt → iProp Σ.
  Definition typed_call E L (f : frame_path) (eκs : list lft) (etys : list (sigT type)) (v : val) (P : iProp Σ) (vl : list val) (tys : list (sigT (λ rt : RT, type rt * rt)%type)) (T : typed_call_cont_t) : iProp Σ :=
    (P -∗
     ([∗ list] v;ty∈vl;tys, let '(existT rt (ty, r)) := ty in v ◁ᵥ{f.1, MetaNone} r @ ty) -∗
     ∀ Φ,
      rrust_ctx -∗
      elctx_interp E -∗
      llctx_interp L -∗
      current_frame f.1 f.2 -∗
      (∀ (L' : llctx) (v : val) (rt : RT) (ty : type rt) r,
        llctx_interp L' -∗ current_frame f.1 f.2 -∗ T L' v rt ty r -∗ Φ v) -∗
      WPe{f.1} (Call v (Val <$> vl)) {{ λ v, Φ v }})%I.
  Class TypedCall (E : elctx) (L : llctx) (f : frame_path) (eκs : list lft) (etys : list (sigT type)) (v : val) (P : iProp Σ) (vl : list val) (tys : list (sigT (λ rt, type rt * rt)%type)) : Type :=
    typed_call_proof T : iProp_to_Prop (typed_call E L f eκs etys v P vl tys T).

  Definition typed_if (E : elctx) (L : llctx) (v : val) (P T1 T2 : iProp Σ) : iProp Σ :=
    (P -∗ ∃ b, ⌜val_to_bool v = Some b⌝ ∗ (if b then T1 else T2)).
  Class TypedIf E L (v : val) (P : iProp Σ) : Type :=
    typed_if_proof T1 T2 : iProp_to_Prop (typed_if E L v P T1 T2).

  (** Typing of annotated expressions -- annotation determined by the [A]*)
  (* A is the annotation from the code *)
  Definition typed_annot_expr (E : elctx) (L : llctx) π (n : nat) {A} (a : A) (v : val) (P : iProp Σ) (T : typed_val_expr_cont_t) : iProp Σ :=
    (rrust_ctx -∗
      elctx_interp E -∗
      llctx_interp L -∗
      P ={⊤}[∅]▷=∗^n |={⊤}=>
      ∃ L2 m rt (ty : type rt) r, llctx_interp L2 ∗ v ◁ᵥ{π, m} r @ ty ∗ T L2 v m rt ty r).
  Class TypedAnnotExpr (E : elctx) (L : llctx) (π : thread_id) (n : nat) {A} (a : A) (v : val) (P : iProp Σ) : Type :=
    typed_annot_expr_proof T : iProp_to_Prop (typed_annot_expr E L π n a v P T).

  Definition enter_cache_hint (P : Prop) := P.
  Global Arguments enter_cache_hint : simpl never.
  Global Typeclasses Opaque enter_cache_hint.

  (** Learn from a hypothesis on introduction with [introduce_with_hooks], defined below *)
  Class LearnFromHyp (P : iProp Σ) := {
    learn_from_hyp_Q : iProp Σ;
    learn_from_hyp_pers :: Persistent (learn_from_hyp_Q);
    learn_from_hyp_proof :
      ∀ F, ⌜lftE ⊆ F⌝ -∗ P ={F}=∗ P ∗ learn_from_hyp_Q;
  }.

  Class LearnFromHypVal {rt} (ty : type rt) (r : rt) := {
    learn_from_hyp_val_Q : iProp Σ;
    learn_from_hyp_val_pers :: Persistent (learn_from_hyp_val_Q);
    learn_from_hyp_val_proof :
      ∀ F π v m, ⌜lftE ⊆ F⌝ -∗ v ◁ᵥ{π, m} r @ ty ={F}=∗ v ◁ᵥ{π, m} r @ ty ∗ learn_from_hyp_val_Q;
  }.
  (* For specific forms of values, we can override this with stronger rules. *)
  Global Program Instance learn_hyp_val π v m {rt} (ty : type rt) r :
    LearnFromHypVal ty r → LearnFromHyp (v ◁ᵥ{π, m} r @ ty) | 100 :=
    λ H, {| learn_from_hyp_Q := learn_from_hyp_val_Q |}.
  Next Obligation. intros π v m rt ty r [Q HQ]. done. Qed.

  Global Program Instance learn_hyp_place_owned π l {rt} (ty : type rt) r :
    LearnFromHypVal ty r → LearnFromHyp (l ◁ₗ[π, Owned] #r @ (◁ ty))%I | 10 :=
        λ H, {| learn_from_hyp_Q := learn_from_hyp_val_Q ∗ ∃ ly, ⌜use_layout_alg (ty_syn_type ty MetaNone) = Some ly⌝ ∗ ⌜enter_cache_hint (l `has_layout_loc` ly)⌝(*  ∗ loc_in_bounds l 0 (ly_size ly) *) |}.
  Next Obligation.
    intros π l rt ty r [Q ? HQ] F.
    iIntros (?) "Hl". simpl.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & % & ? & #Hlb & %r' & -> & HT)".
    iMod (fupd_mask_mono with "HT") as "(%v & Hl & Hv)"; first done.
    iMod (HQ with "[//] Hv") as "(Hv & #HQ')".
    iSplitL. { iModIntro. iExists _. iFrame. do 4 iR. done. }
    iModIntro. iFrame "HQ'". iExists _.
    (*iFrame "Hlb".*)
    rewrite /enter_cache_hint. done.
  Qed.

  (* Lower-priority instance for other ownership modes and place types *)
  Global Program Instance learn_hyp_place_layout π l k {rt} (lt : ltype rt) r :
    LearnFromHyp (l ◁ₗ[π, k] r @ lt)%I | 20 :=
        {| learn_from_hyp_Q := ∃ ly, ⌜use_layout_alg (ltype_st lt) = Some ly⌝ ∗ ⌜enter_cache_hint (l `has_layout_loc` ly)⌝ (* ∗ loc_in_bounds l 0 (ly_size ly) *) |}.
  Next Obligation.
    intros π l k rt lt r F.
    iIntros (?) "Hl".
    iPoseProof (ltype_own_has_layout with "Hl") as "(%ly & %Hst & %Hl)".
    iPoseProof (ltype_own_loc_in_bounds with "Hl") as "#Hlb"; first done.
    iModIntro. iFrame. iExists _. (* iFrame "Hlb". *)
    rewrite /enter_cache_hint. iPureIntro. eauto.
  Qed.

  Global Program Instance learn_hyp_loc_in_bounds l off1 off2 :
    LearnFromHyp (loc_in_bounds l off1 off2)%I | 10 :=
    {| learn_from_hyp_Q := ⌜enter_cache_hint (0 ≤ l.(loc_a) - off1)%Z⌝ ∗ ⌜enter_cache_hint (l.(loc_a) + off2 ≤ MaxInt USize)%Z⌝ |}.
  Next Obligation.
    iIntros (l off1 off2 ? ?) "Hlb".
    iPoseProof (loc_in_bounds_ptr_in_range with "Hlb") as "%Hinrange".
    iFrame. iModIntro. iPureIntro.
    move: Hinrange. rewrite /min_alloc_start /enter_cache_hint.
    split; first lia.
    rewrite MaxInt_eq.
    specialize (max_alloc_end_le_usize). lia.
  Qed.

  (** * Introduce a proposition containing tokens that we want to directly return *)
  (* TODO also thread na tokens through here *)
  Definition introduce_with_hooks (E : elctx) (L : llctx) (P : iProp Σ) (T : llctx → iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ elctx_interp E -∗ llctx_interp L -∗ P ={F}=∗ ∃ L', llctx_interp L' ∗ T L'.
  Class IntroduceWithHooks (E : elctx) (L : llctx) (P : iProp Σ) : Type :=
    introduce_with_hooks_proof T : iProp_to_Prop (introduce_with_hooks E L P T).

  (** Do a custom iteration in the type system, determined by rules for specific M *)
  Definition iterate_with_hooks (E : elctx) (L : llctx) {M} (m : M) (T : llctx → M → iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ elctx_interp E -∗ llctx_interp L ={F}=∗ ∃ L' m', llctx_interp L' ∗ T L' m'.
  Class IterateWithHooks (E : elctx) (L : llctx) {M} (m : M) : Type :=
    iterate_with_hooks_proof T : iProp_to_Prop (iterate_with_hooks E L m T).

  (** *** Statements *)
  Definition typed_stmt_R_t := val → llctx → iProp Σ.

  Definition typed_stmt_post_cond (f : frame_path) (rf : function) (R : typed_stmt_R_t) (Φ : val → iProp Σ) : iProp Σ :=
    (∀ L' (v : val) locals,
      llctx_interp L' -∗
      current_frame f.1 f.2 -∗
      (* get ownership of the frame assertion. *)
      allocated_locals f locals -∗
      ([∗ list] x ∈ locals, ∃ ly l st, ⌜syn_type_has_layout st ly⌝ ∗ x is_live{f, st} l ∗ l ↦|ly|) -∗
      R v L' -∗
      Φ v).

  (* [Q]: the current function body,
     [ϝ]: the function lifetime
     [R] is a relation on the result value of this statement and its type: we require that the result value is a well-typed [R]-value at this type.
  *)
  Definition typed_stmt (E : elctx) (L : llctx) (f : frame_path) (s : stmt) (rf : function) (R : typed_stmt_R_t) (ϝ : lft) : iProp Σ :=
    (∀ (Φ : val → iProp Σ),
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      current_frame f.1 f.2 -∗
      typed_stmt_post_cond f rf R Φ -∗
      WPs{f.1} s {{rf.(f_code), Φ}})%I.
  Global Arguments typed_stmt _ _ _ _%_E _ _%_I _.

  (** Typing of atomic store statements (ScOrd assign).

      Structurally parallel to CAS/AtomicRMW but at the statement level.
      The instance opens the atomic invariant, executes the store at the
      reduced mask, and closes the invariant. The continuation [T L']
      is threaded via [typed_stmt] for the succeeding statement. *)
  Definition typed_atomic_store (E : elctx) (L : llctx) (f : frame_path)
    (v_ptr : val) (P_ptr : iProp Σ) (v_val : val) (P_val : iProp Σ)
    (ot : op_type) (T : llctx → iProp Σ) : iProp Σ :=
    (P_ptr -∗ P_val -∗
      ∀ (s : stmt) (fn : function) (R : typed_stmt_R_t) (ϝ : lft),
      (∀ L', T L' -∗ typed_stmt E L' f s fn R ϝ) -∗
      typed_stmt E L f (Assign ScOrd ot v_ptr v_val s) fn R ϝ)%I.
  Class TypedAtomicStore (E : elctx) (L : llctx) (f : frame_path)
    (v_ptr : val) (P_ptr : iProp Σ) (v_val : val) (P_val : iProp Σ)
    (ot : op_type) : Type :=
    typed_atomic_store_proof T : iProp_to_Prop (typed_atomic_store E L f v_ptr P_ptr v_val P_val ot T).

  (* class for instances specialized to value ownership *)
  Class TypedAtomicStoreVal (E : elctx) (L : llctx) (f : frame_path)
    (v_ptr : val) {rt1} (ty1 : type rt1) (r1 : rt1)
    (v_val : val) {rt2} (ty2 : type rt2) (r2 : rt2)
    (ot : op_type) : Type :=
    typed_atomic_store_val :: TypedAtomicStore E L f
      v_ptr (v_ptr ◁ᵥ{f.1, MetaNone} r1 @ ty1)
      v_val (v_val ◁ᵥ{f.1, MetaNone} r2 @ ty2) ot.
  Global Hint Mode TypedAtomicStoreVal + + + + + + + + + + + + : typeclass_instances.

  (* [P] is an invariant on the context. *)
  Definition typed_block (P : elctx → llctx → iProp Σ) (f : frame_path) (b : label) (fn : function) (R : typed_stmt_R_t) (ϝ : lft) : iProp Σ :=
    (∀ Φ E L,
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      current_frame f.1 f.2 -∗
      logical_step ⊤ (P E L) -∗
      typed_stmt_post_cond f fn R Φ -∗
      WPs{f.1} (Goto b) {{ fn.(f_code), Φ}}).

  (** for all succeeding statements [s], assuming that [v] has type [ty], it can be converted to a non-zero integer *)
  Definition typed_assert (E : elctx) (L : llctx) (f : frame_path) (v : val) {rt} (ty : type rt) (r : rt) (s : stmt) (fn : function) (R : typed_stmt_R_t) (ϝ : lft) : iProp Σ :=
    (rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      current_frame f.1 f.2 -∗
      v ◁ᵥ{f.1, MetaNone} r @ ty -∗
      ⌜val_to_bool v = Some true⌝ ∗ llctx_interp L ∗ current_frame f.1 f.2 ∗ typed_stmt E L f s fn R ϝ)%I.
  Class TypedAssert (E : elctx) (L : llctx) (f : frame_path) (v : val) {rt} (ty : type rt) (r : rt) : Type :=
    typed_assert_proof s fn R ϝ : iProp_to_Prop (typed_assert E L f v ty r s fn R ϝ).


  (** annotated statements are allowed to execute an update and take a step *)
  (* TODO: make this more useful and actually use it *)
  Definition typed_annot_stmt {A} (a : A) (T : iProp Σ) : iProp Σ :=
    (rrust_ctx ={⊤}[∅]▷=∗ T).
  Class TypedAnnotStmt {A} (a : A) : Type :=
    typed_annot_stmt_proof T : iProp_to_Prop (typed_annot_stmt a T).

  Definition typed_switch (E : elctx) (L : llctx) (f : frame_path) (v : val) rt (ty : type rt) (r : rt) (it : int_type) (m : gmap Z nat) (ss : list stmt) (def : stmt) (fn : function) (R : typed_stmt_R_t) (ϝ : lft) : iProp Σ :=
    (v ◁ᵥ{f.1, MetaNone} r @ ty -∗ ∃ z, ⌜val_to_Z v it = Some z⌝ ∗
      match m !! z with
      | Some i => ∃ s, ⌜ss !! i = Some s⌝ ∗ typed_stmt E L f s fn R ϝ
      | None   => typed_stmt E L f def fn R ϝ
      end).
  Class TypedSwitch (E : elctx) (L : llctx) (f : frame_path) (v : val) rt (ty : type rt) (r : rt) (it : int_type) : Type :=
    typed_switch_proof m ss def fn R ϝ : iProp_to_Prop (typed_switch E L f v rt ty r it m ss def fn R ϝ).



  (** *** Places *)

  (* This defines what place expressions can contain. We cannot reuse
  W.ectx_item because of BinOpPCtx since there the root of the place
  expression is not in evaluation position. *)
  Inductive place_ectx_item :=
  | DerefPCtx (o : lang.order) (ot : op_type) (mc : bool)
  | GetMemberPCtx (sls : struct_layout_spec) (m : var_name)
  | GetMemberUnionPCtx (uls : union_layout_spec) (m : var_name)
  | AnnotExprPCtx (n : nat) {A} (x : A)
    (* for PtrOffsetOp, second ot must be PtrOp *)
  | BinOpPCtx (op : bin_op) (ot : op_type) (v : val) (m : metadata) rt (ty : type rt) (r : rt)
    (* for ptr-to-ptr casts, ot must be PtrOp *)
  | UnOpPCtx (op : un_op)
  | EnumDataPCtx (els : enum_layout_spec) (variant : var_name)
  .

  (* Computes the WP one has to prove for the place ectx_item Ki
  applied to the location l. *)
  Definition place_item_to_wp (f : frame_path) (Ki : place_ectx_item) (Φ : loc → iProp Σ) (l : loc) : iProp Σ :=
    match Ki with
    | DerefPCtx o ot mc => WPe{f.1} !{ot, o, mc} l {{ λ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | GetMemberPCtx sls m => WPe{f.1} l at{sls} m {{ λ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | GetMemberUnionPCtx uls m => WPe{f.1} l at_union{uls} m {{ λ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | AnnotExprPCtx n x => WPe{f.1} AnnotExpr n x l {{ λ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    (* we have proved typed_val_expr e1 before so we can use v ◁ᵥ ty here;
      note that the offset is on the left and evaluated first *)
    | BinOpPCtx op ot v m rt ty r => v ◁ᵥ{f.1, m} r @ ty -∗ WPe{f.1} BinOp op ot PtrOp v l {{ λ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | UnOpPCtx op => WPe{f.1} UnOp op PtrOp l {{ λ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | EnumDataPCtx els variant => WPe{f.1} EnumData els variant l {{ λ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    end%I.
  Definition place_to_wp (f : frame_path) (K : list place_ectx_item) (Φ : loc → iProp Σ) : (loc → iProp Σ) := foldr (place_item_to_wp f) (λ v, |={⊤}=> Φ v)%I K.

  Lemma fupd_place_item_to_wp f Ki Φ l :
    (|={⊤}=> place_item_to_wp f Ki Φ l) -∗ place_item_to_wp f Ki Φ l.
  Proof.
    destruct Ki; simpl; iIntros "Ha"; iIntros; iApply fupd_wpe; iMod "Ha"; by iApply "Ha".
  Qed.
  Lemma fupd_place_to_wp f K Φ l:
    (|={⊤}=> place_to_wp f K Φ l) -∗ place_to_wp f K Φ l.
  Proof.
    destruct K as [ | Ki K]; simpl.
    - by iIntros ">>$".
    - iApply fupd_place_item_to_wp.
  Qed.

  Global Instance place_item_to_wp_proper f K :
    Proper (pointwise_relation _ equiv ==> eq ==> equiv) (place_item_to_wp f K).
  Proof.
    intros Φ1 Φ2 Hequiv l l' <-.
    destruct K; simpl.
    5: f_equiv.
    all: apply wpe_proper.
    1-7: solve_proper.
    all: solve_proper.
  Qed.
  Lemma place_to_wp_app f (K1 K2 : list place_ectx_item) Φ l :
    place_to_wp f (K1 ++ K2) Φ l ≡ place_to_wp f K1 (place_to_wp f K2 Φ) l.
  Proof.
    induction K1 as [ | Ki K IH] in l |-*.
    - simpl. iSplit; [ by eauto | ].
      iApply fupd_place_to_wp.
    - simpl. apply place_item_to_wp_proper; last done.
      intros l'. by rewrite IH.
  Qed.

  Lemma place_item_to_wp_mono f K Φ1 Φ2 l:
    place_item_to_wp f K Φ1 l -∗ (∀ l, Φ1 l -∗ Φ2 l) -∗ place_item_to_wp f K Φ2 l.
  Proof.
    iIntros "HP HΦ". move: K => [o ly mc|sls m|uls m |n A x|op ot v m rt ty r|op | els variant]//=.
    5: iIntros "Hv".
    1-4,6-7: iApply (@wpe_wand with "HP").
    7: iApply (@wpe_wand with "[Hv HP]"); first by iApply "HP".
    all: iIntros (?); iDestruct 1 as (l' ->) "HΦ1".
    all: iExists _; iSplit => //; by iApply "HΦ".
  Qed.

  Lemma place_to_wp_mono f K Φ1 Φ2 l:
    place_to_wp f K Φ1 l -∗ (∀ l, Φ1 l -∗ Φ2 l) -∗ place_to_wp f K Φ2 l.
  Proof.
    iIntros "HP HΦ".
    iInduction (K) as [] "IH" forall (l) => /=. { by iApply "HΦ". }
    iApply (place_item_to_wp_mono with "HP").
    iIntros (l') "HP". by iApply ("IH" with "HP HΦ").
  Qed.

  Lemma place_to_wp_fupd f K Φ l:
    (place_to_wp f K (λ l, |={⊤}=> Φ l) l) -∗ place_to_wp f K Φ l.
  Proof.
    induction K as [ | Ki K IH] in l |-*; simpl.
    - by iIntros ">>$".
    - iIntros "Ha". iApply (place_item_to_wp_mono with "Ha").
      iIntros (l'). iApply IH.
  Qed.

  (* We need to take some extra care because the lifetime context may change during this operation. *)
  Fixpoint find_place_ctx (E : elctx) (f : frame_path) (e : W.expr) : option (llctx → (llctx → list place_ectx_item → loc → iProp Σ) → iProp Σ) :=
    match e with
    | W.Loc l => Some (λ L T, T L [] l)
    | W.Deref o ot mc e =>
      T' ← find_place_ctx E f e; Some (λ L T, T' L (λ L' K l, T L' (K ++ [DerefPCtx o ot mc]) l))
    | W.GetMember e sls m => T' ← find_place_ctx E f e; Some (λ L T, T' L (λ L' K l, T L' (K ++ [GetMemberPCtx sls m]) l))
    | W.GetMemberUnion e uls m => T' ← find_place_ctx E f e; Some (λ L T, T' L (λ L' K l, T L' (K ++ [GetMemberUnionPCtx uls m]) l))
    | W.EnumData els variant e => T' ← find_place_ctx E f e; Some (λ L T, T' L (λ L' K l, T L' (K ++ [EnumDataPCtx els variant]) l))
    | W.AnnotExpr n x e => T' ← find_place_ctx E f e; Some (λ L T, T' L (λ L' K l, T L' (K ++ [AnnotExprPCtx n x]) l))
    | W.LocInfoE a e => find_place_ctx E f e

    (* Here we use the power of having a continuation available to add
    a typed_val_expr. It is important that this happens before we get
    to place_to_wp_mono since we will need to give up ownership of the
    root of the place expression once we hit it. This allows us to
    support e.g. a[a[0]]. *)
    | W.BinOp op ot PtrOp e1 e2 =>
      T' ← find_place_ctx E f e2;
      Some (λ L T, typed_val_expr E L f (W.to_expr e1) (λ L' v m rt ty r, T' L' (λ L'' K l, T L'' (K ++ [BinOpPCtx op ot v m rt ty r]) l)))
    | W.UnOp op PtrOp e => T' ← find_place_ctx E f e; Some (λ L T, T' L (λ L' K l, T L' (K ++ [UnOpPCtx op]) l))
    (* TODO: Is the existential quantifier here a good idea or should this be a fullblown judgment? *)
    | W.UnOp op (IntOp it) e =>
      Some (λ L T, typed_val_expr E L f (UnOp op (IntOp it) (W.to_expr e)) (λ L' v m rt ty r,
        v ◁ᵥ{f.1, m} r @ ty -∗ ∃ l, ⌜v = val_of_loc l⌝ ∗ T L' [] l)%I)
    | W.LValue e =>
      Some (λ L T, typed_val_expr E L f (W.to_expr e) (λ L' v m rt ty r,
        v ◁ᵥ{f.1, m} r @ ty -∗ ∃ l, ⌜v = val_of_loc l⌝ ∗ T L' [] l)%I)
    | W.Var x =>
      Some (λ L T, find_in_context (FindLocal f x) (λ '(st, l), x is_live{f, st} l -∗ T L [] l))%I
    | _ => None
    end.

  Class IntoPlaceCtx E f (e : expr) (T : llctx → (llctx → list place_ectx_item → loc → iProp Σ) → iProp Σ) :=
    into_place_ctx Φ Φ':
    (⊢ ∀ L, rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ current_frame f.1 f.2 -∗ T L Φ' -∗
      (∀ L' K l, llctx_interp L' -∗ current_frame f.1 f.2 -∗ Φ' L' K l -∗ place_to_wp f K (Φ ∘ val_of_loc) l) -∗
        WPe{f.1} e {{ Φ }}).

  Section find_place_ctx_correct.
  Arguments W.to_expr : simpl nomatch.
  Lemma find_place_ctx_correct E f e T:
    find_place_ctx E f e = Some T →
    IntoPlaceCtx E f (W.to_expr e) T.
  Proof.
    elim: e T => //= *.
    all: iIntros (Φ Φ' L) "#LFT #HE HL Hframe HT HΦ'".
    all: iApply wpe_fupd.
    3,4: case_match.
    all: try match goal with
    |  H : ?x ≫= _ = Some _ |- _ => destruct x as [?|] eqn:Hsome
    end; simplify_eq/=.
    all: try match goal with
    |  H : context [IntoPlaceCtx _ _ _ _ ] |- _ => rename H into IH
    end.
    1: { iDestruct "HT" as ([st l])  "(Hx & HT)". destruct f as [π i].
      simpl. iApply (wp_var with "Hframe Hx").
      iApply physical_step_intro. iNext.
      iIntros "Hframe Hx". iSpecialize ("HT" with "Hx").
      iApply ("HΦ'" with "HL Hframe HT"). }
    1: iApply @wpe_value; by iApply ("HΦ'" with "HL Hframe HT").
    1: {
      iApply ("HT" with "LFT HE HL Hframe"). iIntros (L' rt ty v m r) "HL Hframe Hv HT".
      iDestruct ("HT" with "Hv") as (l ?) "HT". subst.
        by iApply ("HΦ'" $! _ [] with "HL Hframe HT").
    }
    4: {
      rewrite /LValue. iApply ("HT" with "LFT HE HL Hframe"). iIntros (L' rt ty v m r) "HL Hframe Hv HT".
      iDestruct ("HT" with "Hv") as (l ?) "HT". subst.
      by iApply ("HΦ'" $! _ [] with "HL Hframe").
    }
    2: wpe_bind. 2: rewrite -!/(W.to_expr _).
    2: iApply ("HT" with "LFT HE HL Hframe"); iIntros (L' v m rt ty r) "HL Hframe Hv HT".
    2: iDestruct (IH with "LFT HE HL Hframe HT") as "HT" => //.
    2: fold W.to_expr.
    1, 3-7: iDestruct (IH with "LFT HE HL Hframe HT") as " HT" => //.
    all: wpe_bind; iApply "HT".
    all: iIntros (L'' K l) "HL Hframe HT" => /=.
    all: iDestruct ("HΦ'" with "HL Hframe HT") as "HΦ"; rewrite place_to_wp_app /=.
    all: iApply (place_to_wp_mono with "HΦ"); iIntros (l') "HWP" => /=.
    7: iApply (@wpe_wand with "[Hv HWP]"); first by iApply "HWP".
    1-6: iApply (@wpe_wand with "HWP").
    all: iIntros (?); by iDestruct 1 as (? ->) "$".
  Qed.
  End find_place_ctx_correct.


  Lemma imp_unblockable_lft_incl κs1 κs2 {rt} (lt : ltype rt) :
    lft_list_incl κs1 κs2 -∗
    imp_unblockable κs1 lt -∗
    imp_unblockable κs2 lt.
  Proof.
    unfold lft_list_incl.
    iIntros "(_ & Hincl)".
    by iApply imp_unblockable_shorten.
  Qed.

  (** ** Condition on places: when is a client allowed to replace [lt] with [lt2]
    under a context where the intersected [bor_kind] is [b]?
    *)
  Inductive place_update_kind : Type :=
  (* strong updates *)
  | UpdStrong
  (* weak updates that don't change the refinement type *)
  | UpdWeak
  (* uniq updates: once all the lifetimes are dead, the place becomes unblockable *)
  (* This becomes degenerate if [κs = nil] -- then this means that updates are allowed as long as the core is equal *)
  | UpdUniq (κs : list lft)
  .


  Definition place_update_kind_incl (a b : place_update_kind) : iProp Σ :=
    match a, b with
    | _, UpdStrong => True
    | UpdWeak, UpdWeak => True
    | UpdUniq _, UpdWeak => True
    | UpdUniq κs1, UpdUniq κs2 =>
        lft_list_incl κs1 κs2
    | _, _ => False
    end.
  Definition place_update_kind_max (a b : place_update_kind) : place_update_kind :=
    match a, b with
    | UpdStrong, _ => UpdStrong
    | _, UpdStrong => UpdStrong
    | UpdWeak, _ => UpdWeak
    | _, UpdWeak => UpdWeak
    | UpdUniq κs1, UpdUniq κs2 =>
        UpdUniq (κs1 ++ κs2)
    end.

  (* We cannot easily define a notion of intersection for the [UpdUniq] case, but we can define intersection with a [place_restriction] *)
  Inductive place_restriction : Type :=
  | RestrictNone
  | RestrictWeak
  | RestrictUniq (κ : lft)
  .
  Definition place_update_kind_restrict (a : place_update_kind) (b : place_restriction) : place_update_kind :=
    match a, b with
    | UpdUniq κs1, RestrictUniq κ => UpdUniq ((λ κ1, κ1 ⊓ κ) <$> κs1)
    | UpdUniq κ1, _ => UpdUniq κ1
    | _, RestrictUniq κ1 => UpdUniq [κ1]
    | UpdWeak, _ => UpdWeak
    | _, RestrictWeak => UpdWeak
    | _, _ => UpdStrong
    end.
  Definition bor_kind_to_place_restriction (b : bor_kind) : place_restriction :=
    match b with
    | Uniq κ _ => RestrictUniq κ
    | _ => RestrictNone
    end.
  Global Coercion bor_kind_to_place_restriction : bor_kind >-> place_restriction.

  (* Bottom in the hierarchy *)
  Definition UpdBot := (UpdUniq []).

  Infix "⪯ₚ" := (place_update_kind_incl) (at level 51).
  Infix "⊔ₚₖ" := (place_update_kind_max) (at level 50).
  Infix "⊓ₚ" := (place_update_kind_restrict) (at level 50).

  Global Instance place_update_kind_incl_pers b1 b2 : Persistent (b1 ⪯ₚ b2).
  Proof. destruct b1, b2; try apply _. Qed.

  Lemma place_update_kind_incl_refl b:
    ⊢ (b ⪯ₚ b)%I.
  Proof.
    destruct b; try done.
    iApply lft_list_incl_refl.
  Qed.
  Lemma place_update_kind_incl_trans b1 b2 b3 :
    ⊢ (b1 ⪯ₚ b2 -∗ b2 ⪯ₚ b3 -∗ b1 ⪯ₚ b3)%I.
  Proof.
    destruct b1, b2, b3; simpl; iIntros "#Hx#Hy //".
    iApply lft_list_incl_trans; done.
  Qed.
  Lemma upd_bot_min b :
    ⊢ UpdBot ⪯ₚ b.
  Proof.
    destruct b; try done.
    simpl.
    iApply lft_list_incl_nil_l.
  Qed.

  (** Properties about meet *)
  (*Lemma place_update_kind_min_incl_l b1 b2 :*)
    (*⊢ (b1 ⊓ₚ b2 ⪯ₚ b1)%I.*)
  (*Proof. destruct b1, b2; simpl; eauto using lft_incl_refl, lft_intersect_incl_l. Qed.*)
  (*Lemma place_update_kind_min_incl_r b1 b2 :*)
    (*⊢ (b1 ⊓ₚ b2 ⪯ₚ b2)%I.*)
  (*Proof. destruct b1, b2; simpl; eauto using lft_incl_refl, lft_intersect_incl_r. Qed.*)
  (*
  Lemma place_update_kind_incl_glb b1 b2 b3 :
    b1 ⪯ₚ b2 -∗
    b1 ⪯ₚ b3 -∗
    b1 ⪯ₚ b2 ⊓ₚ b3.
  Proof.
    iIntros "Hincl1 Hincl2".
    destruct b1, b2, b3; unfold place_update_kind_min, place_update_kind_incl; simpl; try done; try iApply lft_incl_refl.
    all: iApply (lft_incl_glb with "Hincl1 Hincl2").
  Qed.
   *)

  Lemma place_update_kind_restrict_incl b r :
    ⊢ b ⊓ₚ r ⪯ₚ b.
  Proof.
    destruct b, r; simpl; try done.
    - iApply lft_list_incl_refl.
    - iApply lft_list_incl_refl.
    - iApply lft_list_incl_pointwise.
      iApply big_sepL2_intro.
      { rewrite length_fmap//. }
      iModIntro. iIntros (??? Hlook1 Hlook2).
      rewrite list_lookup_fmap Hlook2/= in Hlook1.
      injection Hlook1 as <-.
      iApply lft_intersect_incl_l.
  Qed.

  (** Properties about join *)
  Lemma place_update_kind_max_incl_l b1 b2 :
    ⊢ (b1 ⪯ₚ b1 ⊔ₚₖ b2)%I.
  Proof.
    destruct b1, b2; simpl; try done.
    iApply lft_list_incl_app_l.
  Qed.
  Lemma place_update_kind_max_incl_r b1 b2 :
    ⊢ (b2 ⪯ₚ b1 ⊔ₚₖ b2)%I.
  Proof.
    destruct b1, b2; simpl; try done.
    iApply lft_list_incl_app_r.
  Qed.
  Lemma place_update_kind_incl_lub b1 b2 b3 :
    b1 ⪯ₚ b3 -∗
    b2 ⪯ₚ b3 -∗
    b1 ⊔ₚₖ b2 ⪯ₚ b3.
  Proof.
    iIntros "#Hincl1 #Hincl2".
    destruct b1, b2, b3; unfold place_update_kind_max, place_update_kind_incl; simpl; try done.
    by iApply lft_list_incl_lub.
  Qed.


  Global Arguments place_update_kind_incl : simpl nomatch.

  Definition lctx_place_update_kind_incl (E : elctx) (L : llctx) b b' : Prop :=
    ∀ qL, llctx_interp_noend L qL -∗ □ (elctx_interp E -∗ b ⪯ₚ b').

  Lemma lctx_place_update_kind_incl_acc E L k1 k2 :
    lctx_place_update_kind_incl E L k1 k2 →
    elctx_interp E -∗ llctx_interp L -∗ k1 ⪯ₚ k2.
  Proof.
    intros Hincl. iIntros "HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & Hcl_L)".
    iApply (Hincl with "HL HE").
  Qed.

  Lemma lctx_place_update_kind_incl_use E L b1 b2 :
    lctx_place_update_kind_incl E L b1 b2 →
    elctx_interp E -∗
    llctx_interp L -∗
    b1 ⪯ₚ b2.
  Proof.
    iIntros (Hincl) "HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    by iPoseProof (Hincl with "HL HE") as "Ha".
  Qed.

  (** Outliving:
    Usually, we want to know that we can perform updates to a place at least until all the blocked lifetimes in the place are over.
    Otherwise, already something went wrong before.

    TODO: it would be nice if we could get this as an implicit property of our model.
  *)
  Definition place_update_kind_outlives (b : place_update_kind) (κs : list lft) : iProp Σ :=
    match b with
    | UpdUniq κs' =>
        lft_list_incl κs κs'
    | _ => True
    end.
  Global Instance place_update_kind_outlives_persistent b κ : Persistent (place_update_kind_outlives b κ).
  Proof. destruct b; apply _. Qed.
  Lemma place_update_kind_outlives_incl b b' κ :
    b ⪯ₚ b' -∗ place_update_kind_outlives b κ -∗ place_update_kind_outlives b' κ.
  Proof.
    iIntros "#Hincl1 #Hincl2".
    destruct b, b'; unfold place_update_kind_incl; simpl; try done.
    by iApply lft_list_incl_trans.
  Qed.

  Lemma place_update_kind_outlives_uniq_incl b κs :
    place_update_kind_outlives b κs -∗
    UpdUniq κs ⪯ₚ b.
  Proof.
    destruct b; simpl; by eauto.
  Qed.

  Definition lctx_place_update_kind_outlives (E : elctx) (L : llctx) (b : place_update_kind) (κs : list lft) :=
    ∀ qL, llctx_interp_noend L qL -∗ elctx_interp E -∗ place_update_kind_outlives b κs.
  Arguments lctx_place_update_kind_outlives : simpl nomatch.

  Lemma lctx_place_update_kind_outlives_use (E : elctx) (L : llctx) k κs :
    lctx_place_update_kind_outlives E L k κs →
    elctx_interp E -∗
    llctx_interp L -∗
    place_update_kind_outlives k κs.
  Proof.
    iIntros (Hf) "#HE HL".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iPoseProof (Hf with "HL HE") as "#Hout".
    done.
  Qed.
  Lemma lctx_place_update_kind_outlives_all_use (E : elctx) (L : llctx) k κs :
    Forall (lctx_place_update_kind_outlives E L k) κs →
    elctx_interp E -∗
    llctx_interp L -∗
    [∗ list] κ ∈ κs, place_update_kind_outlives k κ.
  Proof.
    iIntros (Hf) "#HE HL".
    iPoseProof (Forall_big_sepL _ (place_update_kind_outlives k) with "HL []") as "(Houtl & HL)"; first apply Hf.
    { iModIntro. iIntros (?) "HL _ %Hout". iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
      iPoseProof (Hout with "HL HE") as "#Hout". iPoseProof ("HL_cl"  with "HL") as "?". by iFrame. }
    done.
  Qed.


  (* How do I handle Opened now?
      I allow strong updates below.
      if the thing above doesn't allow strong updates, I'm stuck.
      I can rule that out already in the precondition of the place rule, so that's okay.
  *)

  Definition place_update_kind_rt_same (pupd : place_update_kind) : bool :=
    match pupd with
    | UpdStrong => false
    | _ => true
    end.
  Definition opt_place_update_eq (upd : place_update_kind) (rt1 rt2 : RT) : Prop :=
    if place_update_kind_rt_same upd then rt1 = rt2 else True.
  Definition opt_place_update_eq_refl `{upd : !place_update_kind} `{rt : !RT} : opt_place_update_eq upd rt rt.
  Proof.
    unfold opt_place_update_eq.
    destruct upd; simpl; [apply I | apply eq_refl..].
  Defined.
  Import EqNotations.
  Lemma opt_place_update_eq_lift (f : RT → RT) {b rt1 rt2} :
    opt_place_update_eq b rt1 rt2 →
    opt_place_update_eq b (f rt1) (f rt2).
  Proof.
    unfold opt_place_update_eq.
    destruct b; simpl.
    - intros. exact I.
    - intros Heq. exact (rew [λ rt, f rt1 = f rt] Heq in @eq_refl _ (f rt1)).
    - intros Heq. exact (rew [λ rt, f rt1 = f rt] Heq in @eq_refl _ (f rt1)).
  Defined.

  Lemma opt_place_update_eq_lift_join {rt1 rt2} b1 b2 :
    opt_place_update_eq b1 rt1 rt2 →
    opt_place_update_eq (b1 ⊔ₚₖ b2) rt1 rt2.
  Proof.
    unfold opt_place_update_eq.
    destruct b1, b2; simpl; done.
  Defined.

  Lemma opt_place_update_eq_use allowed old_rt pupd_rt :
    place_update_kind_rt_same allowed = true →
    opt_place_update_eq allowed old_rt pupd_rt →
    old_rt = pupd_rt.
  Proof.
    unfold opt_place_update_eq. intros ->.
    done.
  Defined.


  (* Note: I can't make the bound condition part of this because it is an iProp *)
  Record place_update (old_rt : RT) (allowed : place_update_kind) : Type := mkPUpd {
    pupd_rt : RT;
    pupd_lt : ltype pupd_rt;
    pupd_rfn : place_rfn pupd_rt;
    pupd_R : iProp Σ;
    pupd_performed : place_update_kind;
    (*pupd_bound *)
    pupd_eq_1 :
      opt_place_update_eq pupd_performed old_rt pupd_rt;
    pupd_eq_2 :
      opt_place_update_eq allowed old_rt pupd_rt;
  }.
  Add Printing Constructor place_update.
  Global Arguments pupd_rt {_ _}.
  Global Arguments pupd_lt {_ _}.
  Global Arguments pupd_rfn {_ _}.
  Global Arguments pupd_R {_ _}.
  Global Arguments pupd_performed {_ _}.
  Global Arguments pupd_eq_1 {_ _ _}.
  Global Arguments pupd_eq_2 {_ _ _}.

  Lemma pupd_performed_incl_uniq_rt old_rt allowed (upd : place_update old_rt allowed) κs  :
    upd.(pupd_performed) ⪯ₚ UpdUniq κs -∗
    ⌜old_rt = upd.(pupd_rt)⌝.
  Proof.
    destruct upd as [? ? ? ? [] ? ?]; simpl; eauto.
  Qed.

  Definition place_update_ctx (rti rto: RT) (allowed_inner allowed_outer : place_update_kind) : Type :=
      llctx →
      place_update rti allowed_inner →
      (place_update rto allowed_outer → iProp Σ) →
      iProp Σ.


  Import EqNotations.

  (** Condition on type changes from [lt] to [lt2] *)
  (* NOTE Now that ltype_eq involves the refinement, maybe we should merge this with the condition on the refinement?
      -> no. since the eq proof is used in the lifetime logic's inheritance vs in the Uniq case, we cannot fix to the current refinement, but rather need to have a proof for all refinements.
  *)
  Definition typed_place_cond {rt rt2} (b : place_update_kind) (lt : ltype rt) (lt2 : ltype rt2) : iProp Σ :=
    match b with
    | UpdStrong =>
        True
    | UpdWeak =>
        ⌜rt = rt2⌝
    | UpdUniq κs =>
        ∃ (Heq : rt = rt2),
        (* We could allow a disjunction here:
           - if we actually change the place type, then we change the contents of the borrow, and we must prove that we can actually unblock the new type [lt2] in time.
           - if we don't actually change the place type, we've proved this before, and it is fine.
            (this isn't completely true for products: we will need sideconditions for products to handle components that don't change, because we can't just extract this from the VS again when we change one component).
            TODO: pinned borrows actually allow to get the VS out now with the strong accessor, so there should be nothing stopping us from allowing this.
        *)
        (∀ b r, ltype_eq b r r (ltype_core lt) (ltype_core (rew <- [ltype] Heq in lt2))) ∗
        imp_unblockable κs lt2
        (* ∨ ⌜lt = rew <- [lty] Heq in lt2⌝ *)
    end%I.


  (* TODO: If we would allow viewshifts in the Uniq case of [ltype_incl], we could use [ltype_incl] for the RHS instead *)
  Lemma imp_unblockable_nil {rt} (lt : ltype rt) :
    imp_unblockable [] lt ⊣⊢
    (□ ∀ π b r l, l ◁ₗ[ π, b] r @ lt ={lftE}=∗ l ◁ₗ[ π, b] r @ ltype_core lt).
  Proof.
    iSplit.
    - iIntros "(#Hub1 & #Hub2)".
      iModIntro. iIntros (π b r l) "Hl".
      destruct b.
      + rewrite -ltype_own_core_equiv.
        iApply "Hub2"; last done.
        iApply lft_dead_list_nil_1.
      + iModIntro. by iApply ltype_own_shared_to_core.
      + rewrite -ltype_own_core_equiv.
        iApply "Hub1"; last done.
        iApply lft_dead_list_nil_1.
    - iIntros "#Hub".
      iSplitL; iModIntro.
      + iIntros (?????) "_".
        rewrite ltype_own_core_equiv.
        iApply "Hub".
      + iIntros (???) "_".
        rewrite ltype_own_core_equiv.
        iApply "Hub".
  Qed.

  (*  TODO: can I change UpdUniq such that UpdBot becomes satisfying?
  Lemma typed_place_cond_upd_eq {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) :
    typed_place_cond UpdEq lt1 lt2 ⊣⊢
    ((∃ Heq, (∀ b r, ltype_eq b r r lt1 ((rew <- [ltype] Heq in lt2))))).
  Proof.
    simpl. iSplit.
    - iIntros "(%Heq & Ha & Hub)".
      iExists Heq. subst.
      rewrite imp_unblockable_nil.
      done.
    - iIntros "(%Heq & Ha)".
      iExists Heq. iFrame.
      Search imp_unblockable.
      iApply imp_unblockable.
   *)

  Global Instance typed_place_cond_pers {rt rt2} b (lt : ltype rt) (lt2 : ltype rt2) :
    Persistent (typed_place_cond b lt lt2).
  Proof. destruct b; apply _. Qed.

  Lemma typed_place_cond_incl k1 k2 {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) :
    k1 ⪯ₚ k2 -∗
    typed_place_cond k1 lt1 lt2 -∗
    typed_place_cond k2 lt1 lt2.
  Proof.
    iIntros "#Hincl Hcond".
    destruct k2, k1; simpl in *; try done.
    - iDestruct "Hcond" as "(%Heq & ?)". done.
    - iDestruct "Hcond" as "(%Heq & ? & Hub)".
      iExists Heq. iFrame.
      iApply imp_unblockable_lft_incl; done.
  Qed.
  Lemma typed_place_cond_trans {rt1 rt2 rt3} (lt1 : ltype rt1) (lt2 : ltype rt2) (lt3 : ltype rt3) b :
    typed_place_cond b lt1 lt2 -∗
    typed_place_cond b lt2 lt3 -∗
    typed_place_cond b lt1 lt3 .
  Proof.
    destruct b; simpl.
    - iIntros "% % !%". congruence.
    - iIntros "-> ->". done.
    - iIntros "(%Heq & Heq & Hub) (%Heq' & Heq' & Hub')".
      subst.
      iExists eq_refl. iFrame. cbn.
      iIntros (b r). iApply (ltype_eq_trans with "Heq Heq'").
  Qed.

  Lemma imp_unblockable_incl_blocked_lfts {rt} κs (lt : ltype rt) :
    □ (lft_dead_list κs ={lftE}=∗ lft_dead_list (ltype_blocked_lfts lt)) -∗
    imp_unblockable κs lt.
  Proof.
    iIntros "#Houtl".
    iApply (imp_unblockable_shorten with "[Houtl]"); last iApply imp_unblockable_blocked_dead.
    done.
  Qed.

  Definition place_kind_outlives_unblock_lt {rt} (k : place_update_kind) (lt : ltype rt) : iProp Σ :=
    place_update_kind_outlives k (ltype_blocked_lfts lt).
  Lemma place_kind_outlives_unblock_lt_use F κs {rt} (lt : ltype rt) :
    lftE ⊆ F →
    place_kind_outlives_unblock_lt (UpdUniq κs) lt -∗
    lft_dead_list κs ={F}=∗
    lft_dead_list (ltype_blocked_lfts lt).
  Proof.
    iIntros (?) "Houtl".
    unfold place_kind_outlives_unblock_lt, place_update_kind_outlives.
    iApply lft_list_incl_acc_dead; done.
  Qed.

  (** Requires a sidecondition to make sure we can actually do the unblocking. *)
  (* NOTE: if we were to revise the use of unblocking and have a disjunct to just show ltype_eq instead of unblockable, we could get rid of the sidecondition *)
  Lemma typed_place_cond_refl {rt} b (lt : ltype rt) :
    place_kind_outlives_unblock_lt b lt -∗
    typed_place_cond b lt lt.
  Proof.
    iIntros "#Houtl".
    destruct b => /=.
    - by iPureIntro.
    - done.
    - iExists eq_refl. cbn. iSplitR.
      { iIntros (??). iApply ltype_eq_refl. }
      iApply imp_unblockable_incl_blocked_lfts.
      iModIntro. iApply lft_list_incl_acc_dead; done.
  Qed.

  Lemma typed_place_cond_refl_ofty {rt} b (ty : type rt) :
    ⊢ typed_place_cond b (◁ ty)%I (◁ ty)%I.
  Proof.
    destruct b.
    - done.
    - iPureIntro. done.
    - iApply (typed_place_cond_refl (UpdUniq _)).
      unfold place_kind_outlives_unblock_lt.
      simpl. iApply lft_list_incl_nil_l.
  Qed.

  Lemma typed_place_cond_uniq_core_eq {rt} (lt1 lt2 : ltype rt) κ :
    typed_place_cond (UpdUniq κ) lt1 lt2 -∗
    ∀ b r, ltype_eq b r r (ltype_core lt1) (ltype_core lt2).
  Proof.
    iIntros "(%Heq & Ha & _)". rewrite (UIP_refl _ _ Heq). done.
  Qed.
  Lemma typed_place_cond_uniq_unblockable {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κs :
    typed_place_cond (UpdUniq κs) lt1 lt2 -∗
    imp_unblockable κs lt2.
  Proof.
    iIntros "(%Heq & _ & Ha)". done.
  Qed.
  Lemma typed_place_cond_shadowed_update_cur {rt_cur rt_cur' rt_full} (lt_cur : ltype rt_cur) (lt_cur' : ltype rt_cur') r_cur r_cur' (lt_full : ltype rt_full) k :
    place_kind_outlives_unblock_lt k lt_full -∗
    typed_place_cond k (ShadowedLtype lt_cur r_cur lt_full) (ShadowedLtype lt_cur' r_cur' lt_full).
  Proof.
    iIntros "#Hcond".
    destruct k; simpl; simp_ltypes.
    - done.
    - done.
    - iExists eq_refl. cbn. simp_ltypes.
      iSplitR. { iIntros (??). iApply ltype_eq_refl. }
      iApply shadowed_ltype_imp_unblockable.
      iApply imp_unblockable_incl_blocked_lfts.
      iModIntro. iIntros "Hdead".
      by iApply place_kind_outlives_unblock_lt_use.
  Qed.
  Lemma typed_place_cond_blocked_r_Uniq {rt} (lt : ltype rt) (ty : type rt) κs κ' :
    lft_list_incl [κ'] κs -∗
    typed_place_cond (UpdUniq κs) lt (◁ ty) -∗
    typed_place_cond (UpdUniq κs) lt (BlockedLtype ty κ').
  Proof.
    iIntros "#Hincl Hcond".
    iDestruct "Hcond" as "(%Heq & Heq & Hub)".
    rewrite (UIP_refl _ _ Heq).
    iExists eq_refl. cbn. simp_ltypes.
    iSplitL "Heq"; first done.
    iApply imp_unblockable_lft_incl; last iApply blocked_imp_unblockable.
    done.
  Qed.
  Lemma typed_place_cond_blocked_l {rt1 rt2} (lt : ltype rt1) (ty : type rt2) b κ' :
    typed_place_cond b (◁ ty) lt -∗
    typed_place_cond b (BlockedLtype ty κ') lt.
  Proof.
    iIntros "Hcond". destruct b; try done.
    iDestruct "Hcond" as "(%Heq & #Heq & #Hub)".
    subst rt2.
    iExists eq_refl. cbn. simp_ltypes.
    iSplitL; done.
  Qed.
  Lemma typed_place_cond_shrblocked_r_Uniq {rt} (lt : ltype rt) (ty : type rt) κs κ' :
    lft_list_incl [κ'] κs -∗
    typed_place_cond (UpdUniq κs) lt (◁ ty) -∗
    typed_place_cond (UpdUniq κs) lt (ShrBlockedLtype ty κ').
  Proof.
    iIntros "#Hincl Hcond".
    iDestruct "Hcond" as "(%Heq & Heq & Hub)".
    rewrite (UIP_refl _ _ Heq).
    iExists eq_refl. cbn. simp_ltypes.
    iSplitL "Heq"; first done.
    iApply imp_unblockable_lft_incl; last iApply shr_blocked_imp_unblockable.
    done.
  Qed.
  Lemma typed_place_cond_shrblocked_l {rt1 rt2} (lt : ltype rt1) (ty : type rt2) b κ' :
    typed_place_cond b (◁ ty) lt -∗
    typed_place_cond b (ShrBlockedLtype ty κ') lt.
  Proof.
    iIntros "Hcond". destruct b; try done.
    iDestruct "Hcond" as "(%Heq & #Heq & #Hub)".
    subst rt2.
    iExists eq_refl. cbn. simp_ltypes.
    iSplitL; done.
  Qed.
  Lemma typed_place_cond_coreable_r_Uniq {rt} (lt1 lt2 : ltype rt) κ κs :
    lft_list_incl κs κ -∗
    typed_place_cond (UpdUniq κ) lt1 lt2 -∗
    typed_place_cond (UpdUniq κ) lt1 (CoreableLtype κs lt2).
  Proof.
    iIntros "#Hincl (%Heq & Heq & Hub)".
    rewrite (UIP_refl _ _ Heq).
    iExists eq_refl. cbn.
    simp_ltypes. iSplitL "Heq"; first done.
    iApply imp_unblockable_lft_incl; last iApply coreable_ltype_imp_unblockable.
    done.
  Qed.
  Lemma typed_place_cond_coreable_l {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) b κs :
    typed_place_cond b lt1 lt2 -∗
    typed_place_cond b (CoreableLtype κs lt1) lt2.
  Proof.
    iIntros "Hcond". destruct b; try done.
    iDestruct "Hcond" as "(%Heq & Heq & Hub)".
    subst rt2.
    iExists eq_refl. cbn. simp_ltypes. by iFrame.
  Qed.

  Lemma typed_place_cond_shadowed_l {rt_cur rt_full rt2} (lt_cur : ltype rt_cur) (lt_full : ltype rt_full) (lt2 : ltype rt2) b r_cur :
    typed_place_cond b lt_full lt2 -∗
    typed_place_cond b (ShadowedLtype lt_cur r_cur lt_full) lt2.
  Proof.
    unfold typed_place_cond. destruct b; try by eauto.
    iIntros "(%Heq & Ha & Hb)".
    subst rt2. iExists eq_refl. iFrame.
    simp_ltypes. done.
  Qed.
  Lemma typed_place_cond_shadowed_r {rt_cur rt_full rt2} (lt_cur : ltype rt_cur) (lt_full : ltype rt_full) (lt2 : ltype rt2) b r_cur :
    typed_place_cond b lt2 lt_full -∗
    typed_place_cond b lt2 (ShadowedLtype lt_cur r_cur lt_full).
  Proof.
    unfold typed_place_cond. destruct b; try by eauto.
    iIntros "(%Heq & Ha & Hb)".
    subst rt2. iExists eq_refl.
    simp_ltypes. iFrame.
    iApply shadowed_ltype_imp_unblockable.
    done.
  Qed.

  Lemma typed_place_cond_core {rt} (lt : ltype rt) b :
    ⊢ typed_place_cond b lt (ltype_core lt).
  Proof.
    iStartProof.
    destruct b; simpl; try done.
    iExists eq_refl. cbn.
    iSplitL.
    - rewrite ltype_core_idemp.
      iIntros (??). iApply ltype_eq_refl.
    - iApply core_imp_unblockable.
  Qed.

  Global Arguments typed_place_cond : simpl never.

  (* controls conditions on refinement type changes *)
  Definition place_access_rt_rel (bmin : place_update_kind) (rt1 rt2 : RT) :=
    match bmin with
    | UpdStrong => True
    | _ => rt1 = rt2
    end.
  Lemma place_access_rt_rel_refl bmin rt : place_access_rt_rel bmin rt rt.
  Proof. by destruct bmin. Qed.

  Lemma typed_place_cond_Uniq_rt_eq {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) k κ :
    k ⪯ₚ UpdUniq κ -∗
    typed_place_cond k lt1 lt2 -∗
    ⌜rt1 = rt2⌝.
  Proof.
    iIntros "Hincl Hcond".
    destruct k; simpl; try done.
    all: iDestruct "Hcond" as "(%Heq & Ha)"; iClear "Ha"; by done.
  Qed.

  (* NOTE: if put the ltype_eq disjunct for the Uniq case into typed_place_cond,
      then we would get a direct subsumption lemma. *)
  Lemma ltype_eq_place_cond_ty_trans {rt rt2} (lt1 lt2 : ltype rt) (lt3 : ltype rt2) b :
    (∀ b' r, ltype_eq b' r r lt1 lt2) -∗
    typed_place_cond b lt2 lt3 -∗
    typed_place_cond b lt1 lt3.
  Proof.
    iIntros "Heq Hc".
    destruct b; simpl.
    - done.
    - done.
    - iDestruct "Hc" as "(%Heq & Heq' & $)". subst. iExists eq_refl.
      iIntros (??).
      iPoseProof (ltype_eq_core with "Heq") as "Heq".
      iApply (ltype_eq_trans with "Heq Heq'").
  Qed.
  Lemma place_cond_ltype_eq_trans b {rt1 rt2} (lt1 : ltype rt1) (lt2 lt3 : ltype  rt2) :
    typed_place_cond b lt1 lt2 -∗
    (∀ b' r, ltype_eq b' r r lt2 lt3) -∗
    typed_place_cond b lt1 lt3.
  Proof.
    iIntros "Hcond #Heq".
    destruct b; simpl.
    - done.
    - done.
    - iDestruct "Hcond" as "(%Heq & #Heq2 & Hub)". subst rt2.
      iExists eq_refl.
      iSplitR. { iIntros (??). iPoseProof (ltype_eq_core with "Heq") as "Heq'". iApply ltype_eq_trans; done. }
      iApply ltype_eq_imp_unblockable; done.
  Qed.
  Lemma ltype_eq_place_cond_trans {rt rt2} (lt1 lt2 : ltype rt) (lt3 : ltype rt2) b :
    (∀ b' r, ltype_eq b' r r lt1 lt2) -∗
    typed_place_cond b lt2 lt3 -∗
    typed_place_cond b lt1 lt3.
  Proof.
    iIntros "Heq Hc".
    iApply (ltype_eq_place_cond_ty_trans with "Heq Hc").
  Qed.

  Lemma typed_place_cond_ltype_eq_ofty {rt rt2} (lt1 : ltype rt) (lt2 : ltype rt2) (ty3 : type rt2) b :
    typed_place_cond b lt1 lt2  -∗
    (∀ b' r, ltype_eq b' r r lt2 (◁ ty3)%I) -∗
    typed_place_cond b lt1 (◁ ty3)%I.
  Proof.
    iIntros "Hc Heq".
    destruct b; simpl.
    - done.
    - done.
    - iDestruct "Hc" as "(%Heq & Heq' & Hub)". destruct Heq. iExists eq_refl. cbn.
      iSplitL. {
        iIntros (??).
        iApply (ltype_eq_trans with "Heq'").
        iApply (ltype_eq_core _ _ _ _ (◁ _)%I). done.
      }
      iApply ofty_imp_unblockable.
  Qed.

  (** We can mutably borrow from the place, assuming that the ownership [b] of the place is at least Uniq κ. *)
  Lemma ofty_blocked_place_cond b κ {rt} (ty : type rt) :
    UpdUniq [κ] ⪯ₚ b -∗
    typed_place_cond b (◁ ty)%I (BlockedLtype ty κ).
  Proof.
    destruct b; simpl.
    - iIntros "_". done.
    - iIntros "Ha". done.
    - iIntros "#Hincl".
      iExists eq_refl. cbn. iSplitR.
      + simp_ltypes. iIntros (??). iApply ltype_eq_refl.
      + iApply (imp_unblockable_lft_incl); last iApply blocked_imp_unblockable.
        done.
  Qed.

  (* Note: [ShrBlockedLtype] is not used for reborrowing shared borrows, so the sidecondition is okay *)
  Lemma ofty_shr_blocked_place_cond b κ {rt} (ty : type rt) :
    UpdUniq [κ] ⪯ₚ b -∗
    typed_place_cond b (◁ ty)%I (ShrBlockedLtype ty κ).
  Proof.
    destruct b; simpl.
    - iIntros "_". done.
    - iIntros "Ha". done.
    - iIntros "#Hincl".
      iExists eq_refl. cbn. iSplitR.
      + simp_ltypes. iIntros (??). iApply ltype_eq_refl.
      + iApply (imp_unblockable_lft_incl); last iApply shr_blocked_imp_unblockable.
        done.
  Qed.

  Definition bor_kind_writeable (b : bor_kind) :=
    match b with
    | Owned => True
    | Uniq _ _ => True
    | Shared _ => False
    end.
  Definition bor_kind_mut_borrowable (b : bor_kind) :=
    match b with
    | Shared _ => False
    | _ => True
    end.

  (*
    Parameters:
    - [π]: thread id
    - [E]: external lifetime context
    - [L]: local lifetime context
    - [l1]: location that we access
    - [ltyo]: ltype of [l1]
    - [r1]: refinement of [ltyo] at [l1]
    - [bmin0]: the intersection of all [bor_kind]s of places above this one on the way of the access
    - [b1]: the immediate [bor_kind] at which [ltyo] is owned
    - [P]: place ctx, the accesses that we go through
    - [T]: client continuation, with the following arguments:
      + [L' : llctx]: the new local lifetime context
      + [κs] : lifetimes for which we have obtained tokens to access the place
      + [l2 : loc] : inner location that is acessed by the place access (the "result")
      + [b2 : bor_kind] : inner [bor_kind] at which the accessed place is immediately owned
      + [bmin : bor_kind] : the intersection of all [bor_kind]s on the way to [l2]
      + [br] : true if the place requires the refinement type to be unchanged
      + [rti : Type] : refinement type of [l2]
      + [tyli : lty rti] : the ltype at [l2]
      + [rti : place_rfn rti] : the refinement of [tyli]
      + [strong : option (strong_ctx rti)] : describes how an update to the accessed place at [l2] is reflected in an update to [l1] in case we need to do a strong refinement update
      + [weak : option (weak_ctx rto rti)] : describes how an update to the accessed place at [l2] is reflected in an update to [l1] in case do a weak update.


      Note that the [strong] and [weak] options are incomparable. [weak] does not only give stronger assumptions, but also requires giving stronger guarantees, which not all place types can do.
      In particular, [OpenedLtype] can not guarantee that an update will uphold the contract of the place it is nested under, so it cannot support [weak] updates.
   *)
  Definition place_cont_t rto allowed_outer : Type := llctx → list lft → loc → bor_kind → ∀ (allowed_inner : place_update_kind) rti, ltype rti → place_rfn rti → place_update_ctx rti rto allowed_inner allowed_outer → iProp Σ.

  Definition typed_place (E : elctx) (L : llctx) (f : frame_path) (l1 : loc) {rto : RT} (ltyo : ltype rto) (r1 : place_rfn rto) (allowed0 : place_update_kind) (b1 : bor_kind) (P : list place_ectx_item) (T : place_cont_t rto allowed0) : iProp Σ :=
    (∀ Φ F, ⌜lftE ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      current_frame f.1 f.2 -∗
      (* [allowed0] is the intersection of all bor_kinds to this place, including [b1] *)
      (*allowed0 ⪯ₚ b1 -∗*)
      (* assume ownership of l1 *)
      l1 ◁ₗ[f.1, b1] r1 @ ltyo -∗
      (* precondition provided by the client that we necessarily need to go through to get Φ *)
      (∀ (L' : llctx) (κs : list lft) (l2 : loc) (allowed1 : place_update_kind) (b2 : bor_kind) (rti : RT) (ltyi : ltype rti) (ri : place_rfn rti)
        (updcx : place_update_ctx rti rto allowed1 allowed0),
        (* sanity check *)
        (*bmin ⊑ₖ bmin0 -∗*)
        (*allowed1 ⪯ₚ b2 -∗*)
        (* l2 is the inner location we eventually access, provide that to the client *)
        l2 ◁ₗ[f.1, b2] ri @ ltyi -∗

        (* for any update to l2 by the client, we need to update our "outer" place accordingly: *)
        (∀ (upd : place_update rti allowed1),
          upd.(pupd_performed) ⪯ₚ allowed1 -∗
          (* assume an update by the client *)
          l2 ◁ₗ[f.1, b2] upd.(pupd_rfn) @ upd.(pupd_lt) -∗
          (* needs to have the same st *)
          ⌜ltype_st ltyi = ltype_st upd.(pupd_lt)⌝ -∗
          (* remaining ownership *)
          upd.(pupd_R) -∗
          typed_place_cond upd.(pupd_performed) ltyi upd.(pupd_lt) ={F}=∗
          ∀ (L2 : llctx) (cont : place_update rto allowed0 → iProp Σ),
          llctx_interp L2 -∗
          current_frame f.1 f.2 -∗
          updcx L2 upd cont ={F}=∗
          ∃ upd' : place_update rto allowed0,
            (* provide the updated ownership of l1 *)
            l1 ◁ₗ[f.1, b1] upd'.(pupd_rfn) @ upd'.(pupd_lt) ∗
            (* and a proof that the "outer" update is legal *)
            ⌜ltype_st ltyo = ltype_st upd'.(pupd_lt)⌝ ∗
            (* and a proof that the "outer" update is legal *)
            typed_place_cond upd'.(pupd_performed) ltyo upd'.(pupd_lt) ∗
            (* the update obeys the restrictions *)
            upd'.(pupd_performed) ⪯ₚ allowed0 ∗
            (* the tokens for the lifetime *)
            llft_elt_toks κs ∗
            (* as well as a "remaining" ownership that we get out from the update *)
            upd'.(pupd_R) ∗
            llctx_interp L2 ∗
            current_frame f.1 f.2 ∗
            cont upd') -∗

        (* provide the continuation condition *)
        T L' κs l2 b2 allowed1  rti ltyi ri updcx -∗
        (* and the context: we hand the client the new context [L'] *)
        llctx_interp L' -∗
        current_frame f.1 f.2 -∗
        (* then we can assume the postcondition *)
        Φ l2) -∗
      place_to_wp f P Φ l1).

  (** Instances need to have priority >= 10, the ones below are reserved for ghost resolution, id, etc. *)
  Class TypedPlace E L f l1 {rto} (ltyo : ltype rto) (r1 : place_rfn rto) (bmin0 : place_update_kind) (b1 : bor_kind) (P : list place_ectx_item) : Type :=
    typed_place_proof T : iProp_to_Prop (typed_place E L f l1 ltyo r1 bmin0 b1 P T).

  Import EqNotations.
  (*place_update*)
  Lemma typed_place_id {rt} E L f (lt : ltype rt) bmin0 (b : bor_kind) r l (T : place_cont_t rt bmin0) :
    (*⌜lctx_place_update_kind_incl E L bmin0 b⌝ ∗*)
    T L [] l b bmin0 rt lt r (λ L2 upd cont, cont upd)
    ⊢ typed_place E L f l lt r bmin0 b [] T.
  Proof.
    iIntros "Hs" (Φ F ??). iIntros "#LFT #HE HL Hf HP HΦ /=".
    (*iPoseProof (lctx_place_update_kind_incl_use with "HE HL") as "#Hincl"; first apply Hincl.*)
    iSpecialize ("HΦ" $! _ _ _ _ _ _ _ _ _ with "HP").
    (*{ iApply "Hincl". }*)
    iApply ("HΦ" with "[] Hs HL Hf").
    iIntros (upd) "Hincl' Hl %Hst ? Hcond" => /=.
    iModIntro.
    iIntros (L2 cont) "HL Hf Hcont".
    iExists upd.
    iFrame. iR.
    iApply llft_elt_toks_nil.
  Qed.
  Global Instance typed_place_id_inst {rt} E L f (lt : ltype rt) bmin0 b r l :
    TypedPlace E L f l lt r bmin0 b [] | 9 := λ T, i2p (typed_place_id E L f lt bmin0 b r l T).

  Lemma typed_place_eqltype {rto} E L f (lt1 lt2 : ltype rto) bmin0 b r l P T :
    full_eqltype E L lt1 lt2 →
    typed_place E L f l lt2 r bmin0 b P T -∗
    typed_place E L f l lt1 r bmin0 b P T.
  Proof.
    iIntros (Heq) "Hp". iIntros (????) "#CTX #HE HL Hf Hl HΦ".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Heq"; [apply Heq | ].
    iDestruct ("Heq" $! b r) as "[Hi1 Hi2]".
    iApply fupd_place_to_wp.
    iMod (ltype_incl_use with "Hi1 Hl") as "Hl"; first done. iModIntro.
    iDestruct "CTX" as "(LFT & LLCTX)".

    iApply ("Hp" with "[//] [//] [$LFT $LLCTX] HE HL Hf Hl").
    iIntros (L' κs l2 b2 bmin rti tyli ri updcx) "Hl2 Hs HT HL".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _  with "Hl2 [Hs] HT HL").
    iIntros (upd) "Hincl' Hl2 %Hst HR Hcond".
    iMod ("Hs" with "Hincl' Hl2 [//] HR Hcond") as "Hs".
    (*"(Hl & %Hst2 & Hcond & Htoks & HR)".*)
    iModIntro. iIntros (L2 cont) "HL Hf Hcont".
    iMod ("Hs" with "HL Hf Hcont") as (upd') "(Hl & %Hst2 & ? & ? & ? & ?)".
    iExists upd'.
    iPoseProof (ltype_incl_syn_type with "Hi1") as "%Hst'".
    rewrite Hst' Hst2. iFrame. iR.
    iApply ltype_eq_place_cond_trans; last done.
    iApply "Heq".
  Qed.
  (* intentionally not an instance -- since [eqltype] is transitive, that would not be a good idea. *)

  (* generic instance constructors for descending below ofty *)
  Lemma typed_place_ofty_access_val_owned E L (f : frame_path) {rt} l (ty : type rt) (r : rt) bmin0 P T :
    ty_has_op_type ty PtrOp MCCopy →
    (∀ F v, ⌜lftE ⊆ F⌝ -∗
      v ◁ᵥ{f.1, MetaNone} r @ ty ={F}=∗
      ∃ (l2 : loc) (rt2 : RT) (lt2 : ltype rt2) r2 b2, ⌜v = l2⌝ ∗
        v ◁ᵥ{f.1, MetaNone} r @ ty ∗ l2 ◁ₗ[f.1, b2] r2 @ lt2 ∗
        typed_place E L f l2 lt2 r2 UpdStrong b2 P (λ L' κs li b3 bmin rti ltyi ri updcx,
          (* point: the outer place is not updated, it stays at ◁ ty.
             but I emit new updated ownership *)
          T L' κs li b3 bmin rti ltyi ri
          (λ L2 upd cont, updcx L2 upd (λ upd',
            cont (mkPUpd _ _ _ (◁ ty) (# r)
              (l2 ◁ₗ[f.1, b2] (upd').(pupd_rfn) @ (upd').(pupd_lt) ∗ (upd').(pupd_R))
              UpdBot opt_place_update_eq_refl opt_place_update_eq_refl)))
        ))
      ⊢
    typed_place E L f l (◁ ty) (#r) bmin0 (Owned) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    iIntros (Hot) "HT".
    iIntros (????) "#CTX #HE HL Hf Hl Hcont". iApply fupd_place_to_wp.
    iPoseProof (ofty_ltype_acc_owned ⊤ with "Hl") as "(%ly & %Halg & %Hly & Hsc & Hlb & >(%v & Hl & Hv & Hcl))"; first done.
    simpl. iModIntro.
    iDestruct "CTX" as "(LFT & LLCTX)".
    iApply wpe_fupd.
    iApply (wpe_logical_step with "Hcl"); [done.. | ].
    specialize (ty_op_type_stable Hot) as Halg'.
    assert (ly = ot_layout PtrOp) as -> by by eapply syn_type_has_layout_inj.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    iApply (wp_deref with "Hl"); [by right | | done | done | ].
    { by rewrite val_to_of_loc. }
    iApply physical_step_intro. iNext.
    iIntros (st) "Hl Ha".
    iMod ("HT" with "[] Hv") as "(%l2 & %rt2 & %lt2 & %r2 & %b2 & -> & Hv & Hl2 & HT)"; first done.
    iMod ("Ha" with "Hl [//] Hsc Hv") as "Hl".
    iModIntro.
    iExists l2. rewrite mem_cast_id_loc. iSplitR; first done.
    iApply ("HT" with "[//] [//] [$LFT $LLCTX] HE HL Hf Hl2").
    iIntros (L2 κs l3 b3 bmin rti ltyi ri updcx) "Hl3 Hcl HT HL Hf".
    iApply ("Hcont" with "Hl3 [Hcl Hl] HT HL Hf"). simpl.
    iIntros (upd) "#Hincl2 Hl2 %Hst HR Hcond".
    iMod ("Hcl" with "Hincl2 Hl2 [//] HR Hcond") as "Hcl".
    iModIntro. iIntros (L3 cont) "HL Hf Hcont".
    iMod ("Hcl" with "HL Hf Hcont") as (upd') "(Hl' & % & ? & ? & ? & Hstrong & ?)".
    simpl. iFrame. iR. simpl.
    iSplitL; last iApply upd_bot_min.
    iApply typed_place_cond_refl_ofty.
  Qed.

  (* TODO generalize this similarly as the one above? *)
  Lemma typed_place_ofty_access_val_uniq E L f {rt} l (ty : type rt) (r : rt) bmin0 κ γ P T :
    ty_has_op_type ty PtrOp MCCopy →
    ⌜lctx_lft_alive E L κ⌝ ∗
    (∀ F v, ⌜lftE ⊆ F⌝ -∗
      v ◁ᵥ{f.1, MetaNone} r @ ty ={F}=∗
      ∃ (l2 : loc) (rt2 : RT) (lt2 : ltype rt2) r2 b2, ⌜v = l2⌝ ∗
        v ◁ᵥ{f.1, MetaNone} r @ ty ∗ l2 ◁ₗ[f.1, b2] r2 @ lt2 ∗
        typed_place E L f l2 lt2 r2 UpdStrong b2 P (λ L' κs li b3 bmin rti ltyi ri updcx,
          T L' κs li b3 bmin rti ltyi ri
          (λ L2 upd cont, updcx L2 upd (λ upd',
            cont (mkPUpd _ _ _ (◁ ty) (# r)
              (l2 ◁ₗ[f.1, b2] upd'.(pupd_rfn) @ upd'.(pupd_lt) ∗ upd'.(pupd_R))
              UpdBot opt_place_update_eq_refl opt_place_update_eq_refl)))
        ))
    ⊢ typed_place E L f l (◁ ty) (#r) bmin0 (Uniq κ γ) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    iIntros (Hot) "(%Hal & HT)".
    iIntros (????) "#CTX #HE HL Hf Hl Hcont". iApply fupd_place_to_wp.
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iMod (fupd_mask_subseteq lftE) as "HF_cl"; first done.
    iMod (Hal with "HE HL") as "(%q' & Htok & HL_cl2)"; first done.
    iPoseProof (ofty_ltype_acc_uniq lftE with "CTX Htok HL_cl2 Hl") as "(%ly & %Halg & %Hly & Hlb & >(%v & Hl & Hv & Hcl))"; first done.
    iMod "HF_cl" as "_".
    simpl. iModIntro.
    iDestruct "CTX" as "(LFT & LLCTX)".
    iApply wpe_fupd.
    iApply (wpe_logical_step with "Hcl"); [done.. | ].
    specialize (ty_op_type_stable Hot) as Halg'.
    assert (ly = ot_layout PtrOp) as -> by by eapply syn_type_has_layout_inj.
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    iApply (wp_deref with "Hl"); [by right | | done | done | ].
    { by rewrite val_to_of_loc. }
    iApply physical_step_intro. iNext.
    iIntros (st) "Hl [Ha _]".
    iMod ("HT" with "[] Hv") as "(%l2 & %rt2 & %lt2 & %r2 & %b2 & -> & Hv & Hl2 & HT)"; first done.
    iMod (fupd_mask_mono with "(Ha Hl Hv)") as "(Hl & HL)"; first done.
    iPoseProof ("HL_cl" with "HL") as "HL".
    iModIntro.
    iExists l2. rewrite mem_cast_id_loc. iSplitR; first done.
    iApply ("HT" with "[//] [//] [$LFT $LLCTX] HE HL Hf Hl2").
    iIntros (L2 κs l3 b3 bmin rti ltyi ri updcx) "Hl3 Hcl HT HL Hf".
    iApply ("Hcont" with "Hl3 [Hcl Hl] HT HL Hf"). simpl.
    iIntros (upd) "Hincl2 Hl2 %Hst HR Hcond".
    iMod ("Hcl" with "Hincl2 Hl2 [//] HR Hcond") as "Hcl".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hcl" with "HL Hf Hcont") as (upd') "(Hl' & % & ? & ? & ? & ? & ?)".
    simpl. iFrame. simpl. iR.
    iSplitL; last iApply upd_bot_min.
    iApply typed_place_cond_refl_ofty.
  Qed.

  (* NOTE: we need to require it to be a simple type to get this generic lemma *)
  Lemma typed_place_ofty_access_val_shared E L f {rt} l (ty : simple_type rt) (r : rt) bmin0 κ P T :
    ty_has_op_type ty PtrOp MCCopy →
    ⌜lctx_lft_alive E L κ⌝ ∗
    (∀ F v, ⌜lftE ⊆ F⌝ -∗
      v ◁ᵥ{f.1, MetaNone} r @ ty ={F}=∗
      ∃ (l2 : loc) (rt2 : RT) (lt2 : ltype rt2) r2 b2, ⌜v = l2⌝ ∗
        v ◁ᵥ{f.1, MetaNone} r @ ty ∗ l2 ◁ₗ[f.1, b2] r2 @ lt2 ∗
        typed_place E L f l2 lt2 r2 UpdStrong b2 P (λ L' κs li b3 bmin rti ltyi ri updcx,
          T L' κs li b3 bmin rti ltyi ri
          (λ L2 upd cont, updcx L2 upd  (λ upd',
            cont (mkPUpd _ _ _ (◁ ty) (# r)
              (l2 ◁ₗ[f.1, b2] (upd').(pupd_rfn) @ (upd').(pupd_lt) ∗ (upd').(pupd_R))
              UpdBot opt_place_update_eq_refl opt_place_update_eq_refl)))))
    ⊢ typed_place E L f l (◁ ty) (# r) bmin0 (Shared κ) (DerefPCtx Na1Ord PtrOp true :: P) T.
  Proof.
    iIntros (Hot) "(%Hal & HT)".
    iIntros (????) "#CTX #HE HL Hf #Hl Hcont". iApply fupd_place_to_wp.
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iMod (Hal with "HE HL") as "(%q' & Htok & HL_cl2)"; first done.
    iPoseProof (ofty_ltype_acc_shared ⊤ with "Hl") as "(%ly & %Halg & %Hly & Hlb & >Hb)"; first done.
    rewrite simple_type_shr_equiv. iDestruct "Hb" as "(%v & %ly' & _ & % & %Hly' & Hloc & Hv)".
    assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.

    iDestruct "CTX" as "(LFT & LLCTX)".
    iMod (frac_bor_acc with "LFT Hloc Htok") as "(%q0 & >Hloc & Hl_cl)"; first done.
    simpl. iModIntro.
    specialize (ty_op_type_stable Hot) as Halg'.
    assert (ly = ot_layout PtrOp) as -> by by eapply syn_type_has_layout_inj.
    iPoseProof (ty_own_val_has_layout with "Hv") as "#>%Hlyv"; first done.
    iApply wpe_fupd.
    iApply (wp_deref with "Hloc"); [by right | | done | done | ].
    { by rewrite val_to_of_loc. }
    iApply physical_step_intro. iNext.
    iIntros (st) "Hloc".
    iMod ("HT" with "[] Hv") as "(%l2 & %rt2 & %lt2 & %r2 & %b2 & -> & Hv & Hl2 & HT)"; first done.
    iMod ("Hl_cl" with "Hloc") as "Htok".
    iMod ("HL_cl2" with "Htok") as "HL". iPoseProof ("HL_cl" with "HL") as "HL".
    iModIntro.
    iExists l2. rewrite mem_cast_id_loc. iSplitR; first done.
    iApply ("HT" with "[//] [//] [$LFT $LLCTX] HE HL Hf Hl2").
    iIntros (L2 κs l3 b3 bmin rti ltyi ri updcx) "Hl3 Hcl HT HL Hf".
    iApply ("Hcont" with "Hl3 [Hcl Hv] HT HL Hf"). simpl.
    iIntros (upd) "Hincl2 Hl2 %Hst HR Hcond".
    iMod ("Hcl" with "Hincl2 Hl2 [//] HR Hcond") as "Hcl".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hcl" with "HL Hf Hcont") as (upd') "(Hl' & % & ? & ? & ? & ? &?)".
    simpl. iFrame. iFrame "#". simpl. iR.
    iSplitL; last iApply upd_bot_min.
    iApply typed_place_cond_refl_ofty.
  Qed.

  (** ** Prove a typed_place_cond (used together with [stratify_ltype]) *)
  Record place_update_kind_res (allowed : place_update_kind) (rt1 rt2 : RT) : Type := mkPUKRes{
    puk_res_k :> place_update_kind;
    puk_res_eq_1 : opt_place_update_eq puk_res_k rt1 rt2;
    puk_res_eq_2 : opt_place_update_eq allowed rt1 rt2;
  }.
  Global Arguments puk_res_eq_1 {_ _ _}.
  Global Arguments puk_res_eq_2 {_ _ _}.
  Global Arguments puk_res_k {_ _ _}.
  Global Arguments mkPUKRes {_ _ _}.

  (* Compose two updates *)
  Program Definition place_update_kind_res_trans {allowed} {rt1 rt2 rt3}
    (upd1 : place_update_kind_res allowed rt1 rt2)
    (upd2 : place_update_kind_res allowed rt2 rt3) :
    place_update_kind_res allowed rt1 rt3 :=
    mkPUKRes (upd1.(puk_res_k) ⊔ₚₖ upd2.(puk_res_k))  _ _.
  Next Obligation.
    intros ???? [pk1 Heq1 Heq2] [pk2 Heq3 Heq4].
    simpl.
    unfold opt_place_update_eq in *.
    destruct pk1, pk2; simpl in *; try done.
    all: subst; done.
  Defined.
  Next Obligation.
    intros ???? [pk1 Heq1 Heq2] [pk2 Heq3 Heq4].
    simpl.
    unfold opt_place_update_eq in *.
    destruct allowed; simpl in *; try done.
    all: subst; done.
  Defined.

  Definition prove_place_cond (E : elctx) (L : llctx) {rt1 rt2} (bmin : place_update_kind) (lt1 : ltype rt1) (lt2 : ltype rt2) (T : place_update_kind_res bmin rt1 rt2 → iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ rrust_ctx -∗ elctx_interp E -∗ llctx_interp L ={F}=∗
      llctx_interp L ∗
      ∃ upd : place_update_kind_res _ _ _,
        upd ⪯ₚ bmin ∗
        typed_place_cond upd lt1 lt2 ∗ ⌜ltype_st lt1 = ltype_st lt2⌝ ∗
        T upd.
  Class ProvePlaceCond (E : elctx) (L : llctx) {rt1 rt2} (bmin : place_update_kind) (lt1 : ltype rt1) (lt2 : ltype rt2) : Type :=
    prove_place_cond_proof T : iProp_to_Prop (prove_place_cond E L bmin lt1 lt2 T).

  Lemma prove_place_cond_eqltype_l E L bmin {rt1 rt2} (lt1 lt1' : ltype rt1) (lt2 : ltype rt2) T :
    full_eqltype E L lt1 lt1' →
    prove_place_cond E L bmin lt1' lt2 T -∗
    prove_place_cond E L bmin lt1 lt2 T.
  Proof.
    iIntros (Heq) "Hcond". iIntros (F ?) "#CTX #HE HL".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Heq"; [done.. | ].
    iMod ("Hcond" with "[//] CTX HE HL") as "($ & Hcond)".
    iDestruct "Hcond" as "(%upd & Hcond & Hcond' & <- & HT)".
    iExists upd. iFrame.
    iPoseProof (ltype_eq_syn_type inhabitant inhabitant with "Heq") as "->".
    iL. iApply ltype_eq_place_cond_ty_trans; done.
  Qed.
  Lemma prove_place_cond_eqltype_r E L bmin {rt1 rt2} (lt1 : ltype rt1) (lt2 lt2' : ltype rt2) T :
    full_eqltype E L lt2 lt2' →
    prove_place_cond E L bmin lt1 lt2' T -∗
    prove_place_cond E L bmin lt1 lt2 T.
  Proof.
    iIntros (Heq) "Hcond". iIntros (F ?) "#CTX #HE HL".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Heq"; [done.. | ].
    iMod ("Hcond" with "[//] CTX HE HL") as "($ & Hcond)".
    iDestruct "Hcond" as "(%upd & Hcond & #Hcond' & -> & HT)".
    iExists upd. iFrame.
    iPoseProof (ltype_eq_syn_type inhabitant inhabitant with "Heq") as "->". iL.
    iApply (place_cond_ltype_eq_trans with "Hcond'").
    iModIntro. iIntros (??). iApply ltype_eq_sym. done.
  Qed.

  (** ** Some utilities for finishing a place access by either using the strong or the weak VS *)
  Definition typed_place_finish_upd
    {rti rti2 : RT}
    {allowed_inner : place_update_kind}
    (performed_access : place_update_kind_res allowed_inner rti rti2)
    (lt2 : ltype rti2) (r2 : place_rfn rti2)
    : place_update rti allowed_inner :=
      (mkPUpd _ _ rti2 lt2 r2 True performed_access performed_access.(puk_res_eq_1) performed_access.(puk_res_eq_2))
  .

  Definition typed_place_finish π (E : elctx) (L : llctx) {rto rti rti2 : RT}
    {allowed_inner allowed_outer : place_update_kind}
    (upd_cx : place_update_ctx rti rto allowed_inner allowed_outer)
    (* this might be the result from [prove_place_cond], updating from [rti] to [rti2] *)
    (performed_access : place_update_kind_res allowed_inner rti rti2)
    (* leftover ownership *)
    (R : iProp Σ)
    (* the updated type assignment of the inner place *)
    (l : loc) (b : bor_kind) (lt2 : ltype rti2) (r2 : place_rfn rti2)
    (T : llctx → iProp Σ) : iProp Σ :=
    upd_cx L (typed_place_finish_upd performed_access lt2 r2) (λ upd2,
    l ◁ₗ[π, b] upd2.(pupd_rfn) @ upd2.(pupd_lt) -∗
    introduce_with_hooks E L (upd2.(pupd_R) ∗ R) T)%I.

  (** Fold an [lty] to a [type].
    This is usually used after accessing a place, to push the ◁ to the outside again.
  *)
  (* TODO: consider replacing this with a tactic hint *)
  Definition cast_ltype_to_type E L {rt} (lt : ltype rt) (T : type rt → iProp Σ) : iProp Σ :=
    ∃ ty, ⌜full_eqltype E L lt (◁ ty)⌝ ∗ T ty.
  Class CastLtypeToType {rt} (E : elctx) (L : llctx) (lt : ltype rt) : Type :=
    cast_ltype_to_type_proof T : iProp_to_Prop (cast_ltype_to_type E L lt T).


  (** Update the refinement of an [ltype]. If [lb = true], this can take a logical step and thus descend below other types.
      On the other hand, if [lb = false], this should only do an update at the top-level.

      [R] is additional ownership that will be available after the (optional) logical step. We usually use this to return lifetime tokens that we first take, e.g. when resolving below a borrow.
      (We need this because we need to return the lifetime context immediately (not below the logical step) in order to support parallel operation when stratifying products.) *)
  (** [ResolveAll] will fail if we cannot resolve some variable. [ResolveTry] will just leave a [PlaceGhost] if we cannot resolve it. *)
  Inductive ResolutionMode := ResolveAll | ResolveTry.
  Definition resolve_ghost_cont_t (rt : RT) := llctx → place_rfn rt → iProp Σ → bool → iProp Σ.
  Definition resolve_ghost {rt} π E L (rm : ResolutionMode) (lb : bool) l (lt : ltype rt) b (r : place_rfn rt) (T : resolve_ghost_cont_t rt) : iProp Σ :=
    ∀ F,
      ⌜lftE ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      l ◁ₗ[π, b] r @ lt ={F}=∗
      ∃ L' r' R progress,
      maybe_logical_step lb F (l ◁ₗ[π, b] r' @ lt ∗ R) ∗
      llctx_interp L' ∗ T L' r' R progress.
  Class ResolveGhost {rt} π E L rm lb l (lt : ltype rt) b r : Type :=
    resolve_ghost_proof T : iProp_to_Prop (resolve_ghost π E L rm lb l lt b r T).

  (** User-defined ADTs should provide an instance of this if they provide means of borrowing below their abstraction-level. *)
  Definition resolve_ghost_adt_cont_t (rt : RT) := llctx → rt → iProp Σ → bool → iProp Σ.
  Definition resolve_ghost_adt (π : thread_id) (E : elctx) (L : llctx) (rm : ResolutionMode) {rt : RT} (r : rt) (ty : type rt) (T : resolve_ghost_adt_cont_t rt) : iProp Σ :=
    ∀ F v,
      ⌜lftE ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      v ◁ᵥ{π, MetaNone} r @ ty ={F}=∗
      ∃ L' r' R progress,
      logical_step F (v ◁ᵥ{π, MetaNone} r' @ ty ∗ R) ∗
      llctx_interp L' ∗ T L' r' R progress.
  Class ResolveGhostADT {rt} π E L rm (r : rt) (ty : type rt) : Type :=
    resolve_ghost_adt_proof T : iProp_to_Prop (resolve_ghost_adt π E L rm r ty T).

  (* TODO phrase this with fold_list instead. Problem: llctxupdate, existential quantifier, updating ownershp *)
  (* Iteration is controlled by refinement [rs] *)
  Definition resolve_ghost_iter_cont_t rt : Type := llctx → list (place_rfn rt) → iProp Σ → bool → iProp Σ.
  Definition resolve_ghost_iter {rt} (π : thread_id) (E : elctx) (L : llctx) (rm : ResolutionMode) (lb : bool) (l : loc) (st : syn_type) (lts : list (ltype rt)) (b : bor_kind) (rs : list (place_rfn rt)) (ig : list nat) (i0 : nat) (T : resolve_ghost_iter_cont_t rt) : iProp Σ :=
    (∀ F : coPset,
      ⌜lftE ⊆ F⌝ -∗
      ⌜lft_userE ⊆ F⌝ -∗
      rrust_ctx -∗
      elctx_interp E -∗
      llctx_interp L -∗
      ⌜length lts = (length rs)%nat⌝ -∗
      ([∗ list] i ↦ r; lt ∈ rs; lts, if decide ((i + i0) ∈ ig) then True else (l offsetst{st}ₗ (i + i0)) ◁ₗ[ π, b] r @ lt) ={F}=∗
      ∃ (L' : llctx) (rs' : list $ place_rfn rt) (R : iPropI Σ) (progress : bool),
      maybe_logical_step lb F (([∗ list] i ↦ r; lt ∈ rs'; lts, if decide ((i + i0) ∈ ig) then True else (l offsetst{st}ₗ (i + i0)) ◁ₗ[ π, b] r @ lt) ∗ R) ∗
      llctx_interp L' ∗ T L' rs' R progress).
  Class ResolveGhostIter {rt} (π : thread_id) (E : elctx) (L : llctx) (rm : ResolutionMode) (lb : bool) (l : loc) (st : syn_type) (lts : list (ltype rt)) (b : bor_kind) (rs : list (place_rfn rt)) (ig : list nat) (i0 : nat) : Type :=
    resolve_ghost_iter_proof T : iProp_to_Prop (resolve_ghost_iter π E L rm lb l st lts b rs ig i0 T).
  Global Hint Mode ResolveGhostIter + + + + + + + + + + + + + : typeclass_instances.

  (** Finding observations *)
  Inductive FindObsMode : Set :=
    | FindObsModeDirect
    | FindObsModeRel.
  Definition find_observation_result {rt : RT} γ (r : place_rfn rt) : iProp Σ :=
    match r with
    | PlaceIn r => gvar_pobs γ r
    | PlaceGhost γ' => RelEq (T:=rt) γ' γ
    end.
  Lemma place_rfn_interp_owned_find_observation {rt : RT} (r' : rt) (r : place_rfn rt) γ :
    place_rfn_interp_owned (👻 γ) r' -∗
    find_observation_result γ r -∗
    place_rfn_interp_owned r r'.
  Proof.
    unfold place_rfn_interp_owned, find_observation_result.
    destruct r.
    - iIntros "Hobs1 Hobs2". iPoseProof (gvar_pobs_agree_2 with "Hobs1 Hobs2") as "%Heq".
      done.
    - iIntros "Hobs Hrel".
      rewrite /RelEq.
      iDestruct "Hrel" as "(% & % & ? & Hobs' & <-)".
      iPoseProof (gvar_pobs_agree with "Hobs' Hobs") as "<-".
      done.
  Qed.
  Lemma place_rfn_interp_mut_find_observation {rt : RT} (r : place_rfn rt) γ γ' :
    place_rfn_interp_mut (rt:=rt) (👻 γ) γ' -∗
    find_observation_result γ r -∗
    place_rfn_interp_mut r γ'.
  Proof.
    unfold place_rfn_interp_mut, find_observation_result.
    destruct r.
    - iIntros "Hrel Hobs".
      iPoseProof (RelEq_use_pobs with "Hobs Hrel") as "Hobs".
      done.
    - iIntros "Hrel1 Hrel2".
      iApply (RelEq_trans with "Hrel2 Hrel1").
  Qed.
  Lemma place_rfn_interp_shared_find_observation {rt : RT} (r : place_rfn rt) γ γ' :
    place_rfn_interp_shared (rt:=rt) (👻 γ) γ' -∗
    find_observation_result γ r -∗
    place_rfn_interp_shared r γ'.
  Proof.
    unfold place_rfn_interp_shared, find_observation_result.
    destruct r.
    - iIntros "Hobs1 Hobs2". iPoseProof (gvar_pobs_agree_2 with "Hobs1 Hobs2") as "%Heq".
      done.
    - iIntros "Hobs Hrel".
      rewrite /RelEq.
      iDestruct "Hrel" as "(% & % & ? & Hobs' & <-)".
      iPoseProof (gvar_pobs_agree with "Hobs' Hobs") as "<-".
      done.
  Qed.

  Definition find_observation_cont_t (rt : RT) : Type := option (place_rfn rt) → iProp Σ.
  Definition find_observation (rt : RT) (γ : gname) (m : FindObsMode) (T : find_observation_cont_t rt) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ |={F}=> (∃ r : place_rfn rt, find_observation_result γ r ∗ T (Some r)) ∨ T None.
  Class FindObservation (rt : RT) (γ : gname) (m : FindObsMode) : Type :=
    find_observation_proof T : iProp_to_Prop (find_observation rt γ m T).

  Definition find_delayed_observation_cont_t (rt : RT) : Type := option (place_rfn rt) → iProp Σ.
  Definition find_delayed_observation (E : elctx) (L : llctx) (rt : RT) (γ : gname) (m : FindObsMode) (κ : lft) (T : find_delayed_observation_cont_t rt) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ elctx_interp E -∗ llctx_interp L -∗ |={F}=> ((∃ r : place_rfn rt, Inherit [κ] (find_observation_result γ r) ∗ T (Some r)) ∨ T None) ∗ llctx_interp L .
  Class FindDelayedObservation (E : elctx) (L : llctx) (rt : RT) (γ : gname) (m : FindObsMode) (κ : lft) : Type :=
    find_delayed_observation_proof T : iProp_to_Prop (find_delayed_observation E L rt γ m κ T).

  (** *** Stratification: unfold, unblock, and fold an ltype. *)
  (** Determines whether we descend below references.
    [StratMutStrong] will only descend below places with strong ownership mode (no references).
    [StratMutWeak] will also descend below mutable references.
    [StratMutNone] will in addition descend below shared references. *)
  Inductive StratifyMutabilityMode :=
    | StratMutStrong
    | StratMutWeak
    | StratMutNone
  .
  Global Instance StratifyMutabilityMode_eqdec : EqDecision StratifyMutabilityMode.
  Proof. solve_decision. Defined.

  (** Unfold ltypes upon descending or treat ◁ as a leaf? *)
  Inductive StratifyDescendUnfoldMode :=
    | StratDoUnfold
    | StratNoUnfold
  .
  Global Instance StratifyDescendUnfoldMode_eqdec : EqDecision StratifyDescendUnfoldMode.
  Proof. solve_decision. Defined.

  (** Fold ltypes when ascending? *)
  Inductive StratifyAscendMode :=
    | StratRefoldFull     (* failure if it cannot be folded to a [◁ ty] *)
    | StratRefoldOpened   (* need to fold at least all [OpenedLtype]s, but keeping blocked places is okay. *)
    | StratNoRefold       (* don't even try to fold *)
  .
  Global Instance StratifyAscendMode_eqdec : EqDecision StratifyAscendMode.
  Proof. solve_decision. Defined.

  (** Stratification is parameterized by four flags (that don't have any semantic meaning, but guide the automation):
    - [mu] determines whether it should descend below references.
    - [mdu] determines whether it should unfold ltypes upon descending or treat ◁ as a leaf.
    - [ma] determines whether ltypes are folded on ascending.
    - [ml] determines the operation at leaf nodes. This is generic, as it is determined by the concrete operation we take.

     Note that stratification is not parameterized by a [bmin] giving the allowed updates at the current place.
     This is motivated by the fact that our operations should anyways not be influenced by how the place is owned - we have one canonical shape the type should get into.
     Instead, we prove the corresponding [typed_place_cond] condition after the fact, where needed.
   *)
  Definition stratify_ltype_cont_t := llctx → iProp Σ → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ.
  Definition stratify_ltype {rt} (π : thread_id) (E : elctx) (L : llctx) (mu : StratifyMutabilityMode) (mdu : StratifyDescendUnfoldMode)
      (ma : StratifyAscendMode) {M} (ml : M) (l : loc) (lt : ltype rt) (r : place_rfn rt) (b : bor_kind)
      (T : stratify_ltype_cont_t) : iProp Σ :=
    ∀ F,
      ⌜lftE ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ → ⌜shrE ⊆ F⌝ →
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      l ◁ₗ[π, b] r @ lt ={F}=∗
      ∃ L' R (rt' : RT) (lt' : ltype rt') (r' : place_rfn rt'),
      llctx_interp L' ∗
      ⌜ltype_st lt = ltype_st lt'⌝ ∗
      logical_step F (l ◁ₗ[π, b] r' @ lt' ∗ R) ∗
      T L' R rt' lt' r'.

  Class StratifyLtype {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) (r : place_rfn rt) b : Type :=
    stratify_ltype_proof T : iProp_to_Prop (stratify_ltype π E L mu mdu ma ml l lt r b T).

  (** Iterative variant for arrays *)
  Definition stratify_ltype_array_iter_cont_t (rt : RT) := llctx → iProp Σ → list (nat * ltype rt) → list (place_rfn rt) → iProp Σ.
  Definition stratify_ltype_array_iter (π : thread_id) (E : elctx) (L : llctx) (mu : StratifyMutabilityMode) (md : StratifyDescendUnfoldMode) (ma : StratifyAscendMode) {M} (m : M) (l : loc) (ig : list nat) {rt} (def : type rt) (len : nat) (iml : list (nat * ltype rt)) (rs : list (place_rfn rt)) (k : bor_kind) (T : stratify_ltype_array_iter_cont_t rt) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗
    ⌜lft_userE ⊆ F⌝ -∗
    ⌜shrE ⊆ F⌝ -∗
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    ([∗ list] i ↦ lt; r ∈ interpret_iml (◁ def)%I len iml; rs,
      if decide (i ∉ ig) then (⌜ltype_st lt = ty_syn_type def MetaNone⌝ ∗ (l offsetst{ty_syn_type def MetaNone}ₗ i) ◁ₗ[π, k] r @ lt) else True) ={F}=∗
    ∃ (L' : llctx) (R' : iProp Σ) (iml' : list (nat * ltype rt)) (rs' : list (place_rfn rt)),
      ⌜length rs' = length rs⌝ ∗
      logical_step F (([∗ list] i ↦ lt; r ∈ interpret_iml (◁ def)%I len iml'; rs', if decide (i ∉ ig) then (⌜ltype_st lt = ty_syn_type def MetaNone⌝ ∗ (l offsetst{ty_syn_type def MetaNone}ₗ i) ◁ₗ[π, k] r @ lt) else True) ∗ R') ∗
      llctx_interp L' ∗
      T L' R' iml' rs'.
  Class StratifyLtypeArrayIter (π : thread_id) (E : elctx) (L : llctx) (mu : StratifyMutabilityMode) (md : StratifyDescendUnfoldMode) (ma : StratifyAscendMode) {M} (m : M) (l : loc) (ig : list nat) {rt} (def : type rt) (len : nat) (iml : list (nat * ltype rt)) (rs : list (place_rfn rt)) (k : bor_kind) : Type :=
    stratify_ltype_array_iter_proof T : iProp_to_Prop (stratify_ltype_array_iter π E L mu md ma m l ig def len iml rs k T).

  (** Post-hook that is run after stratification visits a node.
     This is intended to be overridden by different stratification clients, depending on [ml]. *)
  Definition stratify_ltype_post_hook_cont_t := llctx → iProp Σ → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ.
  Definition stratify_ltype_post_hook {rt} (π : thread_id) (E : elctx) (L : llctx) {M} (ml : M) (l : loc) (lt : ltype rt) (r : place_rfn rt) (b : bor_kind) (T : stratify_ltype_post_hook_cont_t) : iProp Σ :=
    ∀ F,
      ⌜lftE ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ → ⌜shrE ⊆ F⌝ →
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      l ◁ₗ[π, b] r @ lt ={F}=∗
      ∃ L' R (rt' : RT) (lt' : ltype rt') (r' : place_rfn rt'),
      llctx_interp L' ∗
      ⌜ltype_st lt = ltype_st lt'⌝ ∗
      l ◁ₗ[π, b] r' @ lt' ∗ R ∗
      T L' R rt' lt' r'.
  Class StratifyLtypePostHook {rt} π E L {M} (ml : M) l (lt : ltype rt) (r : place_rfn rt) b : Type :=
    stratify_ltype_post_hook_proof T : iProp_to_Prop (stratify_ltype_post_hook π E L ml l lt r b T).

  (** Low-priority instance in case no overrides are provided for this [ml]. *)
  Lemma stratify_ltype_post_hook_id {rt} (π : thread_id) (E : elctx) (L : llctx) {M} (ml : M) (l : loc) (lt : ltype rt) (r : place_rfn rt) (b : bor_kind) (T : stratify_ltype_post_hook_cont_t) :
    T L True%I _ lt r ⊢ stratify_ltype_post_hook π E L ml l lt r b T.
  Proof.
    iIntros "HT" (????) "CTX HE HL Hb".
    iExists _, _, _, _, _. iFrame. done.
  Qed.
  Global Instance stratify_ltype_post_hook_id_inst {rt} π E L {M} (ml : M) l (lt : ltype rt) r b :
    StratifyLtypePostHook π E L ml l lt r b | 1000 := λ T, i2p (stratify_ltype_post_hook_id π E L ml l lt r b T).

  Lemma stratify_ltype_id {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) (r : place_rfn rt) b T :
    stratify_ltype_post_hook π E L ml l lt r b T
    ⊢ stratify_ltype π E L mu mdu ma ml l lt r b T.
  Proof.
    iIntros "HT" (????) "CTX HE HL Hb".
    iMod ("HT" with "[//] [//] [//] CTX HE HL Hb") as "(%L2 & %R2 & %rt2 & %lt2 & %r2 & HL & Hst & Hb & HR & HT)".
    iExists _, _, _, _, _. iFrame. iApply logical_step_intro. by iFrame.
  Qed.
  (* TODO: remove this instance *)
  Global Instance stratify_ltype_id_inst {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) (r : place_rfn rt) b :
    StratifyLtype π E L mu mdu ma ml l lt r b | 1000 := λ T, i2p (stratify_ltype_id π E L mu mdu ma ml l lt r b T).

  Lemma stratify_ltype_eqltype {rt} π E L mu mdu ma {M} (ml : M) l (lt1 lt2 : ltype rt) (r1 r2 : place_rfn rt) b T :
    ⌜eqltype E L b r1 r2 lt1 lt2⌝ ∗ stratify_ltype π E L mu mdu ma ml l lt2 r2 b T -∗
    stratify_ltype π E L mu mdu ma ml l lt1 r1 b T.
  Proof.
    iIntros "(%Heq & Hs)".
    iIntros (????) "#CTX #HE HL Hb".
    iPoseProof (eqltype_use F with "CTX HE HL") as "(Hvs & HL)"; [done.. | ].
    iMod ("Hvs" with "Hb") as "Hb".
    iPoseProof (eqltype_acc with "CTX HE HL") as "#Heq"; first done.
    iPoseProof (ltype_eq_syn_type with "Heq") as "->".
    iPoseProof ("Hs" with "[//] [//] [//] CTX HE HL Hb") as ">Hb". iModIntro.
    iDestruct "Hb" as "(%L' & %R & %rt' & %lt' & %r' & HL & Hstep & HT)".
    iExists L', R, rt', lt', r'. iFrame.
  Qed.

  (* Typeclass to decide whether we should try to close [OpenedLtype]/[OpenedNaLtype]/[ShadowedLtype] *)
  Class StratifyLtypeShouldCloseInv {M} (m : M) (bk : bor_kind) := {}.
  Global Hint Mode StratifyLtypeShouldCloseInv + + + : typeclass_instances.

  (* Typeclass to decide whether we should try to unblocked [BlockedLtype]/[CoreableLtype]/[ShrBlockedLtype] *)
  Class StratifyLtypeShouldUnblock {M} (m : M) := {}.
  Global Hint Mode StratifyLtypeShouldUnblock + + : typeclass_instances.

  (** Operation for unblocking (remove Blocked and ShrBlocked at leaves). *)
  Inductive StratifyUnblock :=
    | StratifyUnblockOp.
  (* We specialize all flags except for the ascend mode, as that needs to be different for different operations. *)
  Definition stratify_ltype_unblock {rt} (π : thread_id) (E : elctx) (L : llctx) (ma : StratifyAscendMode) (l : loc) (lt : ltype rt) (r : place_rfn rt) (b : bor_kind) (T : llctx → iProp Σ → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ) :=
    stratify_ltype π E L StratMutNone StratNoUnfold ma StratifyUnblockOp l lt r b T.

  Global Instance stratify_unblock_close_inv bk : StratifyLtypeShouldCloseInv StratifyUnblockOp bk := {}.
  Global Instance stratify_unblock_unblock : StratifyLtypeShouldUnblock StratifyUnblockOp := {}.

  (** Operation for extracting observations from dead references. *)
  Inductive StratifyExtract :=
    | StratifyExtractOp (κ : lft).
  Definition stratify_ltype_extract {rt} (π : thread_id) (E : elctx) (L : llctx) (ma : StratifyAscendMode) (l : loc) (lt : ltype rt) (r : place_rfn rt) (b : bor_kind) (κ : lft) (T : llctx → iProp Σ → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ) :=
    stratify_ltype π E L StratMutStrong StratDoUnfold ma (StratifyExtractOp κ) l lt r b T.

  Global Instance stratify_extract_close_inv κ bk : StratifyLtypeShouldCloseInv (StratifyExtractOp κ) bk := {}.
  Global Instance stratify_extract_unblock κ : StratifyLtypeShouldUnblock (StratifyExtractOp κ) := {}.

  (** Operation for resolving observations. *)
  Inductive StratifyResolve :=
    | StratifyResolveOp.
  Definition stratify_ltype_resolve {rt} (π : thread_id) (E : elctx) (L : llctx) (ma : StratifyAscendMode) (l : loc) (lt : ltype rt) (r : place_rfn rt) (b : bor_kind) (T : llctx → iProp Σ → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ) :=
    stratify_ltype π E L StratMutStrong StratDoUnfold ma (StratifyResolveOp) l lt r b T.

  Global Instance stratify_resolve_close_inv bk : StratifyLtypeShouldCloseInv (StratifyResolveOp) bk := {}.
  Global Instance stratify_resolve_unblock : StratifyLtypeShouldUnblock (StratifyResolveOp) := {}.

  (** Operation for closing invariants to end a lifetime *)
  Inductive StratifyClose :=
    | StratifyCloseOp (κs : list lft).

  Definition stratify_ltype_close_inv κs {rt} (π : thread_id) (E : elctx) (L : llctx) (l : loc) (lt : ltype rt) (r : place_rfn rt) (b : bor_kind) (T : llctx → iProp Σ → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ) :=
    stratify_ltype π E L StratMutWeak StratDoUnfold StratRefoldOpened (StratifyCloseOp κs) l lt r b T.

  Global Instance stratify_close_close_inv_uniq κs κ γ :
    TCFastListElemOf (κ ∈ κs) →
    StratifyLtypeShouldCloseInv (StratifyCloseOp κs) (Uniq κ γ) := {}.
  Global Instance stratify_close_inv_unblock κs : StratifyLtypeShouldUnblock (StratifyCloseOp κs) := {}.


  (* TODO: even shared borrows and reads should not always refold, in order to handle ShrBlocked.
      We might want to have an operation on ltypes that captures this in some way, e.g. by "slicing" out a part that can be copied or so.
      But probably this will have to be pretty specific to those. The best I can do is to unblock beforehand, at least.

     TODO: The unblocking should, in the case of shared-borrowing from shr_blocked, not apply to all shr_blocked that we can find, but only those that are dead.
  *)


  (** ** Subtyping judgment with access to lifetime contexts. *)
  (*
    Conceptually, what is subtyping in our type system? Does subtyping in our type system  allow refinement updates?
    For now: seems to be mostly relevant for uninit. But uninit is somewhat special, maybe, at least if you consider safe Rust.
    But later for unsafe code, uninit should conceivably take a stronger role.
    Also for loops now, we should have reasonable subsumption for uninit.
      e.g. what if the loop leaves one component of a struct uninitialized in the invariant, but always initializes at the start of an iteration?

   I would like to say that (i32, i32) is a subtype of (i32, uninit i32), because I can always deinitialize something. (Note: does not work for types with non-trivial drop)
    - with non-trivial drop, an explicit destructor call beforehand would deinitialize it.
    - in general, I could alternatively say that a "storagedead" should explicitly deinitialize primitive types like i32.
  Currently, we have this weird subsume instance that only works at top-level.

  TODO: think on whether the current solution is the right way.
  *)

  (** These are the core judgments used for subtyping by the type system.
     The main entry point is from [subsume_full].
     These judgments enforce stronger requirements than, e.g., [subsume_full]:
     - they require compatibility of [ty_sidecond] and [ty_syn_type]
     - they require subtyping to be persistent
     This allows to get compatibility lemmas, including for shared references.
     However, they are not compatible with mutable references, which have stronger requirements still. *)

  (** This is called "weak" because it just requires the subtyping to hold for a particular combination of refinements. *)
  Definition weak_subtype E L {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) (T : iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L ={F}=∗
    type_incl r1 r2 ty1 ty2 ∗ llctx_interp L ∗ T.
  Class Subtype (E : elctx) (L : llctx) {rt1 rt2} r1 r2 (ty1 : type rt1) (ty2 : type rt2) : Type :=
    subtype_proof T : iProp_to_Prop (weak_subtype E L r1 r2 ty1 ty2 T).

  Definition weak_subltype E L {rt1 rt2} (b : bor_kind) r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) (T : iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L ={F}=∗
    ltype_incl b r1 r2 lt1 lt2 ∗ llctx_interp L ∗ T.
  Class SubLtype (E : elctx) (L : llctx) {rt1 rt2} b r1 r2 (lt1 : ltype rt1) (lt2 : ltype rt2) : Type :=
    subltype_proof T : iProp_to_Prop (weak_subltype E L b r1 r2 lt1 lt2 T).

  Definition owned_subtype π E L (pers : bool) {rt1 rt2 : RT} (r1 : rt1) (r2 : rt2) (ty1 : type rt1) (ty2 : type rt2) (T : llctx → iProp Σ) : iProp Σ :=
    ∀ F,
    ⌜lftE ⊆ F⌝ -∗ ⌜lft_userE ⊆ F⌝ -∗ ⌜shrE ⊆ F⌝ -∗
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗ |={F}=> ∃ L',
    (□?pers owned_type_incl π r1 r2 ty1 ty2) ∗ llctx_interp L' ∗ T L'.
  Class OwnedSubtype (π : thread_id) (E : elctx) (L : llctx) (pers : bool) {rt1 rt2 : RT} (r1 : rt1) (r2 : rt2) (ty1 : type rt1) (ty2 : type rt2) : Type :=
    owned_subtype_proof T : iProp_to_Prop (owned_subtype π E L pers r1 r2 ty1 ty2 T).

  Lemma owned_subtype_weak_subtype π E L pers {rt1 rt2} (r1 : rt1) (r2 : rt2) (ty1 : type rt1) (ty2 : type rt2) T :
    weak_subtype E L r1 r2 ty1 ty2 (T L)
    ⊢ owned_subtype π E L pers r1 r2 ty1 ty2 T.
  Proof.
    iIntros "HT" (????) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(#Hincl & ? & ?)".
    iExists L. iFrame.
    iModIntro. iApply bi.intuitionistically_intuitionistically_if. iModIntro.
    iPoseProof (type_incl_owned_type_incl with "Hincl") as "Hincl'".
    done.
  Qed.
  Global Instance owned_subtype_weak_subtype_inst π E L pers {rt1 rt2} (r1 : rt1) (r2 : rt2) ty1 ty2 :
    OwnedSubtype π E L pers r1 r2 ty1 ty2 | 1000 := λ T, i2p (owned_subtype_weak_subtype π E L pers r1 r2 ty1 ty2 T).

  Lemma owned_subtype_id π E L step {rt} (r1 r2 : rt) (ty : type rt) T :
    ⌜r1 = r2⌝ ∗ T L ⊢ owned_subtype π E L step r1 r2 ty ty T.
  Proof.
    iIntros "(-> & HT)".
    iIntros (????) "#CTX #HE HL". iExists L. iFrame.
    iModIntro. destruct step; simpl; try iModIntro. all: iApply owned_type_incl_refl.
  Qed.
  (*Global Instance owned_subtype_id_inst π E L step {rt} (r1 r2 : rt) (ty : type rt) :*)
    (*OwnedSubtype π E L step r1 r2 ty ty | 5 := λ T, i2p (owned_subtype_id π E L step r1 r2 ty T).*)

  Lemma owned_subtype_subtype_l {rt1 rt2 rt1'} (ty1 : type rt1) (ty1' : type rt1') (ty2 : type rt2) r1 r1' r2 π E L b T :
    subtype E L r1 r1' ty1 ty1' →
    owned_subtype π E L b r1' r2 ty1' ty2 T -∗
    owned_subtype π E L b r1 r2 ty1 ty2 T.
  Proof.
    iIntros (Heqt) "HT".
    rewrite /owned_subtype.
    iIntros (????) "#CTX #HE HL".
    iPoseProof (subtype_acc with "HE  HL") as "#Hincl1"; first done.
    iMod ("HT" with "[] [] [] CTX HE HL") as "(%L2 & Hincl & HL & HT)"; [done.. | ].
    iModIntro. iExists L2. iFrame.
    destruct b; simpl.
    - iDestruct "Hincl" as "#Hincl". iModIntro.
      iApply owned_type_incl_incl_l; done.
    - iApply owned_type_incl_incl_l; done.
  Qed.
  Lemma owned_subtype_subtype_r {rt1 rt2 rt2'} (ty1 : type rt1) (ty2' : type rt2') (ty2 : type rt2) r1 r2' r2 π E L b T :
    subtype E L r2' r2 ty2' ty2 →
    owned_subtype π E L b r1 r2' ty1 ty2' T -∗
    owned_subtype π E L b r1 r2 ty1 ty2 T.
  Proof.
    iIntros (Heqt) "HT".
    rewrite /owned_subtype.
    iIntros (????) "#CTX #HE HL".
    iPoseProof (subtype_acc with "HE  HL") as "#Hincl1"; first done.
    iMod ("HT" with "[] [] [] CTX HE HL") as "(%L2 & Hincl & HL & HT)"; [done.. | ].
    iModIntro. iExists L2. iFrame.
    destruct b; simpl.
    - iDestruct "Hincl" as "#Hincl". iModIntro.
      iApply owned_type_incl_incl_r; done.
    - iApply (owned_type_incl_incl_r with "Hincl"); done.
  Qed.


  (** Owned location subtyping with a logical step (used for extracting ghost observations) *)
  Definition owned_subltype_step (π : thread_id) E L (l : loc) {rt1 rt2} (r1 : place_rfn rt1) (r2 : place_rfn rt2) (lt1 : ltype rt1) (lt2 : ltype rt2) (T : llctx → iProp Σ → iProp Σ) : iProp Σ :=
    ∀ F,
    ⌜lftE ⊆ F⌝ -∗
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    l ◁ₗ[π, Owned] r1 @ lt1 -∗ |={F}=>
    ∃ L' R,
    (logical_step F (l ◁ₗ[π, Owned] r2 @ lt2 ∗ R)) ∗
    (⌜syn_type_size_eq (ltype_st lt1) (ltype_st lt2)⌝) ∗
    llctx_interp L' ∗ T L' R.
  Class OwnedSubltypeStep (π : thread_id) (E : elctx) (L : llctx) (l : loc) {rt1 rt2} (r1 : place_rfn rt1) (r2 : place_rfn rt2) (lt1 : ltype rt1) (lt2 : ltype rt2) : Type :=
    owned_subltype_step_proof T : iProp_to_Prop (owned_subltype_step π E L l r1 r2 lt1 lt2 T).

  Lemma owned_subltype_step_weak_subltype π E L l {rt1 rt2} (r1 : place_rfn rt1) (r2 : place_rfn rt2) lt1 lt2 T :
    weak_subltype E L (Owned) r1 r2 lt1 lt2 (T L True)
    ⊢ owned_subltype_step π E L l r1 r2 lt1 lt2 T.
  Proof.
    iIntros "HT" (??) "CTX HE HL Hl".
    iExists L, True%I. iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    iModIntro. iDestruct "Hincl" as "(%Hst & #Hincl & _)".
    iSplitL; first last.
    { iPureIntro. rewrite Hst. eapply syn_type_size_eq_refl. }
    iApply fupd_logical_step. iMod (fupd_mask_mono with "(Hincl Hl)"); first done.
    iApply logical_step_intro. eauto.
  Qed.
  Global Instance owned_subltype_step_weak_subltype_inst π E L l {rt1 rt2} (r1 : place_rfn rt1) (r2 : place_rfn rt2) lt1 lt2 :
    OwnedSubltypeStep π E L l r1 r2 lt1 lt2 | 1000 := λ T, i2p (owned_subltype_step_weak_subltype π E L l r1 r2 lt1 lt2 T).

  (** Subtyping for compatibility with mutable references. Importantly, this is independent of the refinement. *)
  Definition mut_subtype E L {rt} (ty1 ty2 : type rt) (T : iProp Σ) : iProp Σ :=
    ⌜full_subtype E L ty1 ty2⌝ ∗ T.
  Class MutSubtype (E : elctx) (L : llctx) {rt} (ty1 ty2 : type rt) : Type :=
    mut_subtype_proof T : iProp_to_Prop (mut_subtype E L ty1 ty2 T).

  Definition mut_subltype E L {rt} (lt1 lt2 : ltype rt) (T : iProp Σ) : iProp Σ :=
    ⌜full_subltype E L lt1 lt2⌝ ∗ T.
  Class MutSubLtype (E : elctx) (L : llctx) {rt} (lt1 lt2 : ltype rt) : Type :=
    mut_subltype_proof T : iProp_to_Prop (mut_subltype E L lt1 lt2 T).

  Definition mut_eqtype E L {rt} (ty1 ty2 : type rt) (T : iProp Σ) : iProp Σ :=
    ⌜full_eqtype E L ty1 ty2⌝ ∗ T.
  Class MutEqtype (E : elctx) (L : llctx) {rt} (ty1 ty2 : type rt) : Type :=
    mut_eqtype_proof T : iProp_to_Prop (mut_eqtype E L ty1 ty2 T).

  Definition mut_eqltype E L {rt} (lt1 lt2 : ltype rt) (T : iProp Σ) : iProp Σ :=
    ⌜full_eqltype E L lt1 lt2⌝ ∗ T.
  Class MutEqLtype (E : elctx) (L : llctx) {rt} (lt1 lt2 : ltype rt) : Type :=
    mut_eqltype_proof T : iProp_to_Prop (mut_eqltype E L lt1 lt2 T).

  (** Subtyping for ADT defs *)
  Definition subtype_adt E L {X Y} (P1 P2 : ex_inv_def X Y) (T : iProp Σ) : iProp Σ :=
    ⌜ex_inv_def_sub E L P1 P2⌝ ∗ T.
  Class SubtypeADT (E : elctx) (L : llctx) {X Y} (P1 P2 : ex_inv_def X Y) : Type :=
    subtype_adt_proof T : iProp_to_Prop (subtype_adt E L P1 P2 T).

  (** ** Prove a proposition using subtyping *)
  Inductive ProofMode :=
  | ProveDirect
  | ProveWithStratify.
  Global Instance ProofMode_eqdecision : EqDecision ProofMode.
  Proof. solve_decision. Defined.
  (* ideally, would like to both stratify and then subsume.
     But the problem is that both will take steps in the return case.
     So for return, I could either have two steps, or keep the context fold. *)
  Definition prove_with_subtype (E : elctx) (L : llctx) (step : bool) (pm : ProofMode) (P : iProp Σ) (T : llctx → list lft → iProp Σ → iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ ⌜lft_userE ⊆ F⌝ -∗ ⌜shrE ⊆ F⌝ -∗ rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ |={F}=>
      ∃ L' κs R, maybe_logical_step step F ((if pm is ProveWithStratify then (lft_dead_list κs ={lftE}=∗ P) else P) ∗ R) ∗ llctx_interp L' ∗ T L' κs R.
  Class ProveWithSubtype (E : elctx) (L : llctx) (step : bool) (pm : ProofMode) (P : iProp Σ) : Type :=
    prove_with_subtype_proof T : iProp_to_Prop (prove_with_subtype E L step pm P T).

  (** Interpreting typing hints *)
  Definition interpret_typing_hint_cont_t (bmin : place_update_kind) (rt : RT) :=
    ∀ (rt' : RT), type rt' → rt' → place_update_kind_res bmin rt rt' → iProp Σ.
  Definition interpret_typing_hint (E : elctx) (L : llctx) (orty : option rust_type) (bmin : place_update_kind) {rt} (ty : type rt) (r : rt) (T : interpret_typing_hint_cont_t bmin rt) : iProp Σ :=
    ∀ F,
      ⌜lftE ⊆ F⌝ →
      ⌜↑rrustN ⊆ F⌝ →
      ⌜lft_userE ⊆ F⌝ →
      rrust_ctx -∗
      elctx_interp E -∗
      llctx_interp L ={F}=∗
      ∃ (rt2 : RT) (ty2 : type rt2) (r2 : rt2) (upd : place_update_kind_res bmin rt rt2),
        llctx_interp L ∗
        type_incl r r2 ty ty2 ∗
        typed_place_cond upd (◁ ty) (◁ ty2) ∗
        upd ⪯ₚ bmin ∗
        T rt2 ty2 r2 upd
    .
  Class InterpretTypingHint (E : elctx) (L : llctx) (orty : option rust_type) (bmin : place_update_kind) {rt} (ty : type rt) (r : rt) : Type :=
    interpret_typing_hint_proof T : iProp_to_Prop (interpret_typing_hint E L orty bmin ty r T).
  Global Hint Mode InterpretTypingHint + + + + + + + : typeclass_instances.


  (** ** Read judgments *)
  Inductive ReadMode := ReadDoCopy | ReadDoMove.
  (* In a given lifetime context, we can read from [e], in the process determining that [e] reads from a location [l] and getting a value typed at a type [ty] with a layout compatible with [ot], and afterwards, the remaining [T L' v ty' r'] needs to be proved, where [ty'] is the new type of the read value and [v] is the read value.

    The prover will prove a [typed_read] in a number of steps:
     - first, the place that is read is checked with [typed_place].
     - then, the actual type-checking of the read is performed with [typed_read_end]
   *)
  (* Parameters:
      - [π] : the thread id
      - [E] : external lifetime context
      - [L] : local lifetime context
      - [e] : read expression
      - [ot] : [op_type] to use for the read
      - [T] : continuation for the client, receiving the following arguments:
          + [L' : llctx] : the updated lifetime context, as the read may have side-effects
          + [v : val] : the read value
          + [rt' : Type] : the refinement type of the read value
          + [ty' : type rt] : the type of the read value
          + [r' : rt] : the refinement of the read value
  *)
  Definition typed_read_cont_t : Type := llctx → val → ∀ rt : RT, type rt → rt → iProp Σ.
  Definition typed_read (E : elctx) (L : llctx) (f : frame_path) (e : expr) (ot : op_type) (m : ReadMode) (T : typed_read_cont_t) : iProp Σ :=
    (∀ Φ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ → ⌜shrE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ current_frame f.1 f.2 -∗
      (∀ (l : loc),
        (* the client gets ownership of the read value and fractional ownership of the location *)
        (* this is below a logical step in order to execute stratification here.
          TODO we may want to move this into a separate thing, together with moving the skip in Use to a separate annotation *)
        logical_step F (∃ v q rt (ty : type rt) r,
          ⌜l `has_layout_loc` ot_layout ot⌝ ∗ ⌜v `has_layout_val` ot_layout ot⌝ ∗ l ↦{q} v ∗
            ▷ v ◁ᵥ{f.1, MetaNone} r @ ty ∗
          (* additionally, the client can assume that it can transform this to the ownership required by the continuation T *)
          logical_step F (∀ st,
              l ↦{q} v -∗
              v ◁ᵥ{f.1, MetaNone} r @ ty ={F}=∗
              ∃ L' rt' (ty' : type rt') r',
                llctx_interp L' ∗
                current_frame f.1 f.2 ∗
                mem_cast v ot st ◁ᵥ{f.1, MetaNone} r' @ ty' ∗
                T L' (mem_cast v ot st) rt' ty' r')) -∗
        (* under this knowledge, the client has to prove the postcondition *)
        Φ (val_of_loc l)) -∗
      (* TODO: maybe different mask F *)
      WPe{f.1} e {{ Φ }})%I.


  (* The core of reading from a location [l] with [ot] that is typed at [lt] and immediately owned at [b2] below a path with intersected [bor_kind] [bmin].

    This is called [typed_read_end] because it ends the chain of typing rules applied to do the read, after typing all the places that are accessed to get to [l].

    The continuation [T] has access to the new place type and refinement of [l] after reading ([lt']),
    and the type ([ty3]) and refinement that is "moved out" of [l] for the client to keep (i.e., the ownership of the read value)
  *)
  Definition typed_read_end_cont_t (allowed : place_update_kind) (rt : RT) : Type :=
    llctx → val → ∀ rt3, type rt3 → rt3 → ∀ rt', ltype rt' → place_rfn rt' → place_update_kind_res allowed rt rt' → iProp Σ.
  Definition typed_read_end (π : thread_id) (E : elctx) (L : llctx) (l : loc) {rt} (lt : ltype rt) (r : place_rfn rt) (b2 : bor_kind) (bmin : place_update_kind) (ot : op_type) (m : ReadMode) (T : typed_read_end_cont_t bmin rt) : iProp Σ :=
    (∀ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ → ⌜shrE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      (*bmin ⪯ₚ b2 -∗*)
      (* given ownership of the read location *)
      l ◁ₗ[π, b2] r @ lt ={F}=∗
      ∃ q v
        (* the type of the object we read *)
        (* TODO: why do we quantify over rt2? can we also make this rt? *)
        rt2 (ty2 : type rt2) r2,
        (* we can provide fractional permission ownership of the stored value [v] to the client,
          typed at an actual type [ty2] (that we can extract from [lt]) *)
        ⌜l `has_layout_loc` ot_layout ot⌝ ∗ ⌜v `has_layout_val` ot_layout ot⌝ ∗ l ↦{q} v ∗ ▷ v ◁ᵥ{π, MetaNone} r2 @ ty2 ∗
        (* prove the continuation after the client is done *)
        logical_step F (∀ st,
          (* assuming that the client provides the ownership back... *)
          l ↦{q} v -∗
          v ◁ᵥ{π, MetaNone} r2 @ ty2 ={F}=∗
          (* ... we transform to some new ownership [ty3] that the client "can keep" (imagine we move out of [l]) *)
          ∃ (L' : llctx) (rt3 : RT) (ty3 : type rt3) r3,
            (mem_cast v ot st) ◁ᵥ{π, MetaNone} r3 @ ty3 ∗
            (* and the lifetime context *)
            llctx_interp L' ∗
            (∃ rt' (lt' : ltype rt') (r' : place_rfn rt') (res : place_update_kind_res _ _ _),
              (* and the remaining ownership for the location *)
              l ◁ₗ[π, b2] r' @ lt' ∗
              ⌜ltype_st lt' = ltype_st lt⌝ ∗
              res ⪯ₚ bmin ∗
              typed_place_cond res lt lt' ∗
              T L' (mem_cast v ot st) rt3 ty3 r3 rt' lt' r' res))).
  Class TypedReadEnd (π : thread_id) (E : elctx) (L : llctx) (l : loc) {rt} (lt : ltype rt) (r : place_rfn rt) (b2 : bor_kind) (bmin : place_update_kind) (ot : op_type) (m : ReadMode) : Type :=
    typed_read_end_proof T : iProp_to_Prop (typed_read_end π E L l lt r b2 bmin ot m T).

  (** ** Write judgments *)
  (* In a given lifetime context, we can write [v] to [e], compatible with [ot], where the written value has type [ty] at refinement [r], and afterwards, the remaining [T] needs to be proved.

    The prover will prove a [typed_write] in a number of steps:
     - first, the place that is read is checked with [typed_place].
     - then, the actual type-checking of the read is performed with [typed_read_end]
   *)
  Definition typed_write_cont_t : Type := llctx → iProp Σ.
  Definition typed_write (E : elctx) (L : llctx) (f : frame_path) (e : expr) (ot : op_type) (v : val) {rt} (ty : type rt) (r : rt) (T : typed_write_cont_t) : iProp Σ :=
    (∀ Φ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ → ⌜shrE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ current_frame f.1 f.2 -∗
      (* provided by the client: for any location l... *)
      (∀ (l : loc),
        (* we can hand out ownership to [l], and when the client has written [v] to it,
          the postcondition holds. *)
        (* if the client provides ownership of v... *)
        (v ◁ᵥ{f.1, MetaNone} r @ ty -∗ logical_step F (
          (* This is something the client learns (in order to prove its wp), rather than something that is provided.
            That the type is compatible with the ot is something that actually needs to be proven as part of [typed_write_end],
            and so we provide it here to the client. *)
          ⌜v `has_layout_val` ot_layout ot⌝ ∗
          (* then it gets access to l *)
          l ↦|ot_layout ot| ∗
          (* and after having written v to it, it gets access to T *)
          logical_step F (l ↦ v ={F}=∗ ∃ L', llctx_interp L' ∗ current_frame f.1 f.2 ∗ T L'))) -∗
        Φ (val_of_loc l)) -∗
      (* TODO: maybe different mask F *)
      WPe{f.1} e {{ Φ }})%I.


  (* The core of writing a value [v1] typed at [ty1] to a location [l2] typed at [lt2] with [ot], where [l2] immediately owned at [b2] below a path with intersected [bor_kind] [bmin].

    After the write, [l2] has a new type [ty3] that is passed on to the continuation.
  *)
  Definition typed_write_end_cont_t allowed rt2 := llctx → ∀ rt3 : RT, type rt3 → rt3 → place_update_kind_res allowed rt2 rt3 → iProp Σ.
  Definition typed_write_end (π : thread_id) (E : elctx) (L : llctx) (ot : op_type) (v1 : val) {rt1} (ty1 : type rt1) (r1 : rt1) (b2 : bor_kind) (bmin : place_update_kind) (l2 : loc) {rt2} (lt2 : ltype rt2) (r2 : place_rfn rt2) (T : typed_write_end_cont_t bmin rt2) : iProp Σ :=
    (∀ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ → ⌜shrE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      (*bmin ⪯ₚ b2 -∗*)
      (* given ownership of the written-to location *)
      l2 ◁ₗ[π, b2] r2 @ lt2 -∗
      (* assuming that the client provides ownership of [v1] *)
      v1 ◁ᵥ{π, MetaNone} r1 @ ty1 ={F}=∗
      (* we need to prove that [v1]'s layout is compatible with [ot], and provide it to the client *)
      ⌜v1 `has_layout_val` ot_layout ot⌝ ∗
      (* we provide [l2] *)
      l2 ↦|ot_layout ot| ∗

      (* and after the client has written to [l2] ... *)
      logical_step F (l2 ↦ v1 ={F}=∗
        ((∃ L' (rt3 : RT) (ty3 : type rt3) (r3 : rt3) (res : place_update_kind_res _ _ _),
        llctx_interp L' ∗
        (* [l2] is typed at a new type [ty3] satisfying the postcondition *)
        l2 ◁ₗ[π, b2] #r3 @ (◁ ty3) ∗
        ⌜ltype_st lt2 = ty_syn_type ty3 MetaNone⌝ ∗
        res ⪯ₚ bmin ∗
        typed_place_cond res lt2 (◁ ty3) ∗
        T L' rt3 ty3 r3 res)))).
  Class TypedWriteEnd (π : thread_id) (E : elctx) (L : llctx) (ot : op_type) (v1 : val) {rt1} (ty1 : type rt1) (r1 : rt1) (b2 : bor_kind) (bmin : place_update_kind) (l2 : loc) {rt2} (lt2 : ltype rt2) (r2 : place_rfn rt2) : Type :=
    typed_write_end_proof T : iProp_to_Prop (typed_write_end π E L ot v1 ty1 r1 b2 bmin l2 lt2 r2 T).

  (** ** Borrow judgments *)
  (** [typed_borrow_mut] gets triggered when we borrow mutably at lifetime [κ] from a place [e].

    Usually, this will be proved in multiple steps:
    * we decompose [e] to a place context and a location
    * we find a typing for the location in the context
    * we type the place context with [typed_place]
    * we use [typed_borrow_mut_end] to do the final checking
  *)
  Definition typed_borrow_mut_cont_t := llctx → val → gname → ∀ (rt : RT), type rt → rt → iProp Σ.
  Definition typed_borrow_mut (E : elctx) (L : llctx) (f : frame_path) (e : expr) (κ : lft) (ty_annot : option rust_type) (T : typed_borrow_mut_cont_t) : iProp Σ :=
    (∀ Φ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ → ⌜shrE ⊆ F⌝ →
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ current_frame f.1 f.2 -∗
      (* for any location provided to the client *)
      (∀ (l : loc),
        (* and a time receipt we provide for generating our credits *)
        tr 1 -∗
        (* the client can assume after an update... *)
        logical_step F (
          (* credits to prepay the borrow *)
          £ num_cred -∗
          (* and the returned receipt *)
          tr 1 ={F}=∗
          ∃ L' (rt : RT) (ty : type rt) (r : rt) (γ : gname) (ly : layout),
          (* a new observation *)
          gvar_obs γ r ∗
          (* and a borrow *)
          &{κ}(∃ (r': rt), gvar_auth γ r' ∗ |={lftE}=> l ↦: ty.(ty_own_val) f.1 r' MetaNone) ∗
          (* + some well-formedness *)
          ⌜syn_type_has_layout (ty.(ty_syn_type) MetaNone) ly⌝ ∗
          ⌜l `has_layout_loc` ly⌝ ∗
          loc_in_bounds l 0 (ly.(ly_size)) ∗ ty_sidecond ty ∗
          (* + the condition T *)
          llctx_interp L' ∗
          current_frame f.1 f.2 ∗
          T L' (val_of_loc l) γ rt ty r) -∗
          Φ (val_of_loc l)) -∗
      WPe{f.1} e {{ Φ }})%I.

  Definition typed_borrow_mut_end_cont_t bmin rt := gname → ∀ rt', ltype rt' → place_rfn rt' → type rt' → rt' → place_update_kind_res bmin rt rt' → iProp Σ.
  Definition typed_borrow_mut_end (π : thread_id) (E : elctx) (L : llctx) (κ : lft) (l : loc) (ty_hint : option rust_type) {rt} (lt : ltype rt) (r : place_rfn rt) (b2 : bor_kind) (bmin : place_update_kind) (T : typed_borrow_mut_end_cont_t bmin rt) : iProp Σ :=
    (∀ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
    (*bmin ⪯ₚ b2 -∗*)
    (* given ownership of the location we borrow from *)
    l ◁ₗ[π, b2] r @ lt -∗ £(num_cred) ={F}=∗
    ∃ (γ : gname) (ly : layout) (rt2 : RT) (ty2 : type rt2) (r2 : rt2) (res : place_update_kind_res bmin rt rt2),
    (* we provide a borrow of ty *)
    place_rfn_interp_mut (#r2) γ ∗
    &{κ}(∃ (r': rt2), gvar_auth γ r' ∗ |={lftE}=> l ↦: ty2.(ty_own_val) π r' MetaNone)  ∗
    ty_sidecond ty2 ∗
    ⌜syn_type_has_layout (ty2.(ty_syn_type) MetaNone) ly⌝ ∗
    loc_in_bounds l 0 (ly.(ly_size)) ∗
    (* and a blocked ownership of the borrowed location *)
    l ◁ₗ[π, b2] (PlaceGhost γ: place_rfn rt2) @ (BlockedLtype ty2 κ) ∗
    res ⪯ₚ bmin ∗
    (* and a proof that we can unblock again *)
    typed_place_cond res lt (BlockedLtype ty2 κ) ∗
    ⌜ltype_st lt = ty_syn_type ty2 MetaNone⌝ ∗
    (* and the context and postco *)
    llctx_interp L ∗
    T γ rt2 (BlockedLtype ty2 κ) (PlaceGhost γ) ty2 r2 res).
  Class TypedBorrowMutEnd π (E : elctx) (L : llctx) (κ : lft) (l : loc) (orty : option rust_type) {rt} (lt : ltype rt) (r : place_rfn rt) (b2 : bor_kind) (bmin : place_update_kind) : Type :=
    typed_borrow_mut_end_proof T : iProp_to_Prop (typed_borrow_mut_end π E L κ l orty lt r b2 bmin T).

  (** [typed_borrow_shr] gets triggered when we do a shared borrow at lifetime [κ] from a place [e].

    Usually, this will be proved in multiple steps:
    * we decompose [e] to a place context and a location
    * we find a typing for the location in the context
    * we type the place context with [typed_place]
    * we use [typed_borrow_shr_end] to do the final checking
  *)
  Definition typed_borrow_shr_cont_t := llctx → val → ∀ (rt : RT), type rt → place_rfn rt → iProp Σ.
  Definition typed_borrow_shr (E : elctx) (L : llctx) (f : frame_path) (e : expr) (κ : lft) (ty_annot : option rust_type) (T : typed_borrow_shr_cont_t) : iProp Σ :=
    (∀ Φ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ → ⌜shrE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ current_frame f.1 f.2 -∗
      (* for any location provided to the client... *)
      (∀ (l : loc),
      (* the client needs to prove the postcondition, assuming shared ownership after an update *)
      (* this requires two logical steps: one for stratifying, and one for initiating sharing *)
      logical_step F (logical_step F (
        (* one credit for the inheritance VS *)
        £1 ={F}=∗
        ∃ (L' : llctx) (rt : RT) (ty : type rt) (r : place_rfn rt) (r' : rt) (ly : layout),
          place_rfn_interp_shared r r' ∗ ty.(ty_shr) κ f.1 r' MetaNone l ∗
          ⌜syn_type_has_layout (ty.(ty_syn_type) MetaNone) ly⌝ ∗
          ⌜l `has_layout_loc` ly⌝ ∗
          loc_in_bounds l 0 (ly.(ly_size)) ∗ ty.(ty_sidecond) ∗
          (* as well as the condition T *)
          llctx_interp L' ∗
          current_frame f.1 f.2 ∗
          T L' (val_of_loc l) rt ty r)) -∗
        Φ (val_of_loc l)) -∗
      WPe{f.1} e {{ Φ }})%I.

  Definition typed_borrow_shr_end_cont_t bmin rt := ∀ rt', ltype rt' → place_rfn rt' → type rt' → rt' → place_update_kind_res bmin rt rt' → iProp Σ.
  Definition typed_borrow_shr_end π (E : elctx) (L : llctx) (κ : lft) (l : loc) (orty : option rust_type) {rt} (lt : ltype rt) (r : place_rfn rt) (b2 : bor_kind) (bmin : place_update_kind) (T : typed_borrow_shr_end_cont_t bmin rt) : iProp Σ :=
    (∀ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ → ⌜shrE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
    (*bmin ⪯ₚ b2 -∗*)
    (* given ownership of the location we borrow from *)
    l ◁ₗ[π, b2] r @ lt ={F}=∗
    (* we provide a borrow of ty *)
    logical_step F (
    (* one credit for the inheritance VS *)
    £1 ={F}=∗
    ∃ ly rt2 (lt2 : ltype rt2) (r2 : rt2) (ty2 : type rt2) (res : place_update_kind_res bmin rt rt2),
    (*place_rfn_interp_shared r r2 ∗*)
    ty2.(ty_shr) κ π r2 MetaNone l ∗
    ⌜syn_type_has_layout (ty2.(ty_syn_type) MetaNone) ly⌝ ∗
    loc_in_bounds l 0 (ly.(ly_size)) ∗ ty2.(ty_sidecond) ∗
    (* and a blocked ownership of the borrowed location *)
    l ◁ₗ[π, b2] #r2 @ lt2  ∗
    (* and a proof that we can unblock again *)
    typed_place_cond res lt lt2 ∗
    ⌜ltype_st lt = ltype_st lt2⌝ ∗
    ⌜ltype_st lt = ty_syn_type ty2 MetaNone⌝ ∗
    res ⪯ₚ bmin ∗
    (* and the context and postco *)
    llctx_interp L ∗
    T rt2 lt2 (#r2) ty2 r2 res)).
  Class TypedBorrowShrEnd π (E : elctx) (L : llctx) (κ : lft) (l : loc) (orty : option rust_type) {rt} (lt : ltype rt) (r : place_rfn rt) (b2 : bor_kind) (bmin : place_update_kind) : Type :=
    typed_borrow_shr_end_proof T : iProp_to_Prop (typed_borrow_shr_end π E L κ l orty lt r b2 bmin T).

  (** ** Address-of judgments *)
  (** [*mut] address of *)
  Definition typed_addr_of_mut_cont_t := llctx → val → ∀ (rt : RT), type rt → rt → iProp Σ.
  Definition typed_addr_of_mut (E : elctx) (L : llctx) (f : frame_path) (e : expr) (T : typed_addr_of_mut_cont_t) : iProp Σ :=
    (∀ Φ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ current_frame f.1 f.2 -∗
    (* for any location provided to the client *)
    (∀ (l : loc),
      logical_step F (
        ∃ L' (rt : RT) (ty : type rt) (r : rt),
        l ◁ᵥ{f.1, MetaNone} r @ ty ∗
        llctx_interp L' ∗
        current_frame f.1 f.2 ∗
        T L' (val_of_loc l) rt ty r) -∗
        Φ (val_of_loc l)) -∗
    WPe{f.1} e {{ Φ }})%I.

  (** This does not work below shared references, as we cannot get a full fraction out of the sharing predicate.
     This does not seem that terrible, because we should not take *mut references from shared borrows anyways.
     (Note: we are really using here that the difference between *mut and *const have the role of providing some intent by the programmer.) *)
  Definition typed_addr_of_mut_end_cont_t := llctx → ∀ rt0, type rt0 → rt0 → ∀ rt', ltype rt' → place_rfn rt' → iProp Σ.
  Definition typed_addr_of_mut_end (π : thread_id) (E : elctx) (L : llctx) (l : loc) {rt} (lt : ltype rt) (r : place_rfn rt) (b2 : bor_kind) (bmin : place_update_kind) (T : typed_addr_of_mut_end_cont_t) : iProp Σ :=
    (∀ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
    (*bmin ⪯ₚ b2 -∗*)
    (* given ownership of the location we borrow from *)
    l ◁ₗ[π, b2] r @ lt -∗
    (* do a logical step in order to be able to create [OpenedLtype] *)
    logical_step F (
    ∃ (L' : llctx)
      (rt0 : RT) (ty0 : type rt0) (r0 : rt0)
      (rt' : RT) (lt' : ltype rt') (r' : place_rfn rt'),
    (* provide ownership of some ty0, the result of the operation -- usually will be alias_ptr_t *)
    l ◁ᵥ{π, MetaNone} r0 @ ty0 ∗
    (* and blocked ownership of the borrowed location (where the notion of blocking is not fixed, and determined by the existentially-quantified lt');
       usually it will be AliasLtype l or OpenedLtype (AliasLtype l) .. *)
    l ◁ₗ[π, b2] r' @ lt' ∗
    (* and the ownership to move out *)
    l ◁ₗ[π, Owned] r @ lt ∗
    ⌜ltype_st lt' = ltype_st lt⌝ ∗
    (* and the context and postco *)
    llctx_interp L' ∗
    T L' rt0 ty0 r0 rt' lt' r')).
  Class TypedAddrOfMutEnd (π : thread_id) (E : elctx) (L : llctx) (l : loc) {rt} (lt : ltype rt) (r : place_rfn rt) (b2 : bor_kind) (bmin : place_update_kind) : Type :=
    typed_addr_of_mut_end_proof T : iProp_to_Prop (typed_addr_of_mut_end π E L l lt r b2 bmin T).

  (*
     expected flow:
     - we do a typed_place
     - now we need to reshape the resulting ltype to an Owned ofty
       in order to be able to take that ownership out.
     - one possibility to do this: just have different _end instances for Owned, Uniq and Shared.
       Owned is straight; for Uniq and Shared we do a strong update.
       Shared is more challenging though: we can only get one fraction out.
       Also, we can't write here.
       There we again face the problem of specifying shared pointers in a reasonable way.
      For now: just don't support it for shared pointers.
   *)

  (* TODO addr_of_const
      This should give us some kind of shared ownership.
  *)

  (* TODO maybe we also generally want this to unblock/stratify first? *)
  Definition typed_array_access_cont_t : Type := llctx → ∀ (rt' : RT), type rt' → nat → list (nat * ltype rt') → list (place_rfn rt') → bor_kind → ∀ rte, ltype rte → place_rfn rte → iProp Σ.
  Definition typed_array_access (π : thread_id) (E : elctx) (L : llctx) (base : loc) (off : Z) (st : syn_type) {rt} (lt : ltype rt) (r : place_rfn rt) (k : bor_kind) (T : typed_array_access_cont_t) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ ⌜lft_userE ⊆ F⌝ -∗ ⌜shrE ⊆ F⌝ -∗
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    base ◁ₗ[π, k] r @ lt ={F}=∗
    ∃ L' k' rt' (ty' : type rt') (len : nat) (iml : list (nat * ltype rt')) rs' (rte : RT) re (lte : ltype rte),
      (* updated array assignment *)
      base ◁ₗ[π, k'] #rs' @ ArrayLtype ty' len iml ∗
      (base offsetst{st}ₗ off) ◁ₗ[π, k'] re @ lte ∗
      llctx_interp L' ∗
      T L' _ ty' len iml rs' k' rte lte re.
  Class TypedArrayAccess (π : thread_id) (E : elctx) (L : llctx) (base : loc) (off : Z) (st : syn_type) {rt} (lt : ltype rt) (r : place_rfn rt) (k : bor_kind) : Type :=
    typed_array_access_proof T : iProp_to_Prop (typed_array_access π E L base off st lt r k T).
End judgments.

Global Infix "⪯ₚ" := (place_update_kind_incl) (at level 51).
Global Infix "⊔ₚₖ" := (place_update_kind_max) (at level 50).
Global Infix "⊓ₚ" := (place_update_kind_restrict) (at level 50).

(* HintDb for unfolding place expressions. Currently used to unfold the box magic deref *)
Create HintDb solve_into_place_unfold.

Ltac solve_into_place_ctx :=
  autounfold with solve_into_place_unfold;
  match goal with
  | |- IntoPlaceCtx ?E ?f ?e ?T =>
      let e' := W.of_expr e in
      change_no_check (IntoPlaceCtx E f (W.to_expr e') T);
      refine (find_place_ctx_correct E f _ _ _); rewrite/=/W.to_expr/=; done
  end.
Global Hint Extern 0 (IntoPlaceCtx _ _ _ _) => solve_into_place_ctx : typeclass_instances.

(* we want this to be transparent because it's just a cosmetic wrapper around [stratify_ltype], but the same typeclasses should fire *)
Global Typeclasses Transparent stratify_ltype_unblock.

(** Tactic hint to compute a map lookup, either as [None] or [Some v]. *)
Definition compute_map_lookup_goal `{!typeGS Σ} `{Countable K} {V} (M : gmap K V) (k : K) (unchecked : bool) (T : option V → iProp Σ) : iProp Σ :=
  ∃ res, ⌜M !! k = res⌝ ∗ T res.
#[global] Typeclasses Opaque compute_map_lookup_goal.
Program Definition compute_map_lookup_hint `{!typeGS Σ} `{Countable K} {V} (M : gmap K V) k (unchecked : bool) res :
  M !! k = res →
  LiTactic (compute_map_lookup_goal M k unchecked) := λ a, {|
    li_tactic_P T := T res;
  |}.
Next Obligation.
  iIntros (?? K ?? V M k ? res Hlook T) "HT". iExists res. iFrame. done.
Qed.

Global Typeclasses Opaque compute_map_lookup_goal.
Ltac solve_compute_map_lookup unchecked := fail "implement solve_compute_map_lookup".
#[global] Hint Extern 10 (LiTactic (compute_map_lookup_goal _ _ ?unchecked)) =>
    refine (compute_map_lookup_hint _ _ _ _ _); solve_compute_map_lookup unchecked : typeclass_instances.

(** Variant of [compute_map_lookup_goal] that expects a [Some v]. *)
Definition compute_map_lookup_nofail_goal `{!typeGS Σ} `{Countable K} {V} (M : gmap K V) (k : K) (T : V → iProp Σ) : iProp Σ :=
  ∃ res, ⌜M !! k = Some res⌝ ∗ T res.
#[global] Typeclasses Opaque compute_map_lookup_nofail_goal.
Program Definition compute_map_lookup_nofail_hint `{!typeGS Σ} `{Countable K} {V} (M : gmap K V) k res :
  M !! k = Some res →
  LiTactic (compute_map_lookup_nofail_goal M k) := λ a, {|
    li_tactic_P T := T res;
  |}.
Next Obligation.
  iIntros (?? K ?? V M k res Hlook T) "HT". iExists res. iFrame. done.
Qed.

Global Typeclasses Opaque compute_map_lookup_nofail_goal.
Ltac solve_compute_map_lookup_nofail := fail "implement solve_compute_map_lookup_nofail".
#[global] Hint Extern 10 (LiTactic (compute_map_lookup_nofail_goal _ _)) =>
    refine (compute_map_lookup_nofail_hint _ _ _ _); solve_compute_map_lookup_nofail : typeclass_instances.

(** Tactic hint to compute an iterated map lookup *)
Definition compute_map_lookups_nofail_goal `{!typeGS Σ} `{Countable K} {V} (M : gmap K V) (ks : list K) (T : (list V) → iProp Σ) : iProp Σ :=
  ∃ res, ⌜Forall2 (λ k v, M !! k = Some v) ks res⌝ ∗ T (res).
#[global] Typeclasses Opaque compute_map_lookups_nofail_goal.
Program Definition compute_map_lookups_nofail_hint `{!typeGS Σ} `{Countable K} {V} (M : gmap K V) ks res :
  Forall2 (λ k v, M !! k = Some v) ks res →
  LiTactic (compute_map_lookups_nofail_goal M ks) := λ a, {|
    li_tactic_P T := T res;
  |}.
Next Obligation.
  iIntros (?? K ?? V M ks res Hlook T) "HT". iExists res. iFrame. done.
Qed.

Global Typeclasses Opaque compute_map_lookups_nofail_goal.
Ltac solve_compute_map_lookups_nofail := fail "implement solve_compute_map_lookups_nofail".
#[global] Hint Extern 10 (LiTactic (compute_map_lookups_nofail_goal _ _)) =>
    refine (compute_map_lookups_nofail_hint _ _ _ _); solve_compute_map_lookups_nofail : typeclass_instances.

(** Tactic hint to simplify a map, e.g. compute deletes *)
Definition simplify_gmap_goal `{!typeGS Σ} `{Countable K} {V} (M : gmap K V) (T : gmap K V → iProp Σ) : iProp Σ :=
  ∃ M', ⌜M = M'⌝ ∗ T M'.
#[global] Typeclasses Opaque simplify_gmap_goal.
Program Definition simplify_gmap_hint `{!typeGS Σ} `{Countable K} {V} (M M' : gmap K V) :
  M = M' →
  LiTactic (simplify_gmap_goal M) := λ a, {|
    li_tactic_P T := T M';
  |}.
Next Obligation.
  iIntros (?? K ?? V M M' -> T) "HT". iExists M'. iFrame. done.
Qed.

Global Typeclasses Opaque simplify_gmap_goal.
Ltac solve_simplify_gmap := fail "implement solve_simplify_gmap".
#[global] Hint Extern 10 (LiTactic (simplify_gmap_goal _)) =>
    refine (simplify_gmap_hint _ _ _); solve_simplify_gmap : typeclass_instances.

(** Tactic hint to simplify a lft map, e.g. compute deletes *)
(* We don't actually require an equality here, since the map doesn't have any semantic meaning *)
Definition opaque_eq {A} (a b : A) := True.
Global Opaque opaque_eq.
Definition simplify_lft_map_goal `{!typeGS Σ} `{Countable K} {V} (M : gmap K V) (T : gmap K V → iProp Σ) : iProp Σ :=
  ∃ M', ⌜opaque_eq M M'⌝ ∗ T M'.
#[global] Typeclasses Opaque simplify_lft_map_goal.
Program Definition simplify_lft_map_hint `{!typeGS Σ} `{Countable K} {V} (M M' : gmap K V) :
  opaque_eq M M' →
  LiTactic (simplify_lft_map_goal M) := λ a, {|
    li_tactic_P T := T M';
  |}.
Next Obligation.
  iIntros (?? K ?? V M M' ? T) "HT". iExists M'. iFrame. done.
Qed.

Global Typeclasses Opaque simplify_lft_map_goal.
Ltac solve_simplify_lft_map := fail "implement solve_simplify_lft_map".
#[global] Hint Extern 10 (LiTactic (simplify_lft_map_goal _)) =>
    refine (simplify_lft_map_hint _ _ _); solve_simplify_lft_map : typeclass_instances.

(** Tactic hint to simplify the local list, i.e. compute [list_difference] *)
Definition simplify_local_list_goal `{!typeGS Σ} (M : list var_name) (T : list var_name → iProp Σ) : iProp Σ :=
  ∃ M', ⌜M = M'⌝ ∗ T M'.
#[global] Typeclasses Opaque simplify_local_list_goal.
Program Definition simplify_local_list_hint `{!typeGS Σ} (M M' : list var_name) :
  M = M' →
  LiTactic (simplify_local_list_goal M) := λ a, {|
    li_tactic_P T := T M';
  |}.
Next Obligation.
  iIntros (?? M M' -> T) "HT". iExists M'. iFrame. done.
Qed.

Global Typeclasses Opaque simplify_local_list_goal.
Ltac solve_simplify_local_list := fail "implement solve_simplify_local_list".
#[global] Hint Extern 10 (LiTactic (simplify_local_list_goal _)) =>
    refine (simplify_local_list_hint _ _ _); solve_simplify_local_list : typeclass_instances.

(** Tactic hint to find a local lifetime and split it off from the context *)
Definition llctx_find_llft_goal `{!typeGS Σ} (L : llctx) (κ : lft) (key : llctx_find_llft_key) (T : (list lft * llctx) → iProp Σ) : iProp Σ :=
    ∃ L' κs, ⌜llctx_find_llft L κ key κs L'⌝ ∗ T (κs, L').
#[global] Typeclasses Opaque llctx_find_llft_goal.
Program Definition llctx_find_llft_hint `{!typeGS Σ} (L : llctx) (κ : lft) (key : llctx_find_llft_key) (κs : list lft) (L' : llctx) :
  llctx_find_llft L κ key κs L' →
  LiTactic (llctx_find_llft_goal L κ key) := λ H, {|
    li_tactic_P T := T (κs, L');
|}.
Next Obligation.
  iIntros (?? L κ key κs L' Hsplit T) "HL'". iExists L', κs. eauto.
Qed.

Global Typeclasses Opaque llctx_find_llft_goal.
Ltac solve_llctx_find_llft := fail "implement llctx_find_llft_solve".
Global Hint Extern 10 (LiTactic (llctx_find_llft_goal _ _ _)) =>
    eapply llctx_find_llft_hint; solve_llctx_find_llft : typeclass_instances.

(** Tactic hint to remove dead local lifetime aliases after a local lifetime has been ended *)
Definition llctx_remove_dead_aliases_goal `{!typeGS Σ} (L : llctx) (κ : lft) (T : llctx → iProp Σ) : iProp Σ :=
    ∃ L', ⌜sublist L' L⌝ ∗ T L'.
#[global] Typeclasses Opaque llctx_remove_dead_aliases_goal.
Definition llctx_remove_dead_aliases (L1 L2 : llctx) (κ : lft) :=
  sublist L2 L1.
Program Definition llctx_remove_dead_aliases_hint `{!typeGS Σ} (L : llctx) (κ : lft) (L' : llctx) :
  llctx_remove_dead_aliases L L' κ →
  LiTactic (llctx_remove_dead_aliases_goal L κ) := λ H, {|
    li_tactic_P T := T L';
|}.
Next Obligation.
  iIntros (?? L κ L' Ha T) "HL'". iExists L'. eauto.
Qed.

Global Typeclasses Opaque llctx_remove_dead_aliases_goal.
Ltac solve_llctx_remove_dead_aliases := fail "implement llctx_remove_dead_aliases".
Global Hint Extern 10 (LiTactic (llctx_remove_dead_aliases_goal _ _)) =>
    eapply llctx_remove_dead_aliases_hint; solve_llctx_remove_dead_aliases : typeclass_instances.


(** Tactic hint to compute a layout for a syn_type *)
Definition compute_layout_goal `{!typeGS Σ} (st : syn_type) (T : layout → iProp Σ) : iProp Σ :=
  ∃ ly, ⌜syn_type_has_layout st ly⌝ ∗ T ly.
#[global] Typeclasses Opaque compute_layout_goal.
Program Definition compute_layout_hint `{!typeGS Σ} (st : syn_type) (ly : layout) :
  syn_type_has_layout st ly →
  LiTactic (compute_layout_goal st) := λ a, {|
    li_tactic_P T := T ly;
  |}.
Next Obligation.
  iIntros (?? st ly Hly T) "HT". iExists ly. iFrame. done.
Qed.

Global Typeclasses Opaque compute_layout_goal.
Ltac solve_compute_layout := fail "implement solve_compute_layout".
#[global] Hint Extern 1 (LiTactic (compute_layout_goal _)) =>
    refine (compute_layout_hint _ _ _); solve_compute_layout : typeclass_instances.

(** Tactic hint to compute a struct_layout for a struct_layout_spec *)
Definition compute_struct_layout_goal `{!typeGS Σ} (sls : struct_layout_spec) (T : struct_layout → iProp Σ) : iProp Σ :=
  ∃ sl, ⌜struct_layout_spec_has_layout sls sl⌝ ∗ T sl.
#[global] Typeclasses Opaque compute_struct_layout_goal.
Program Definition compute_struct_layout_hint `{!typeGS Σ} (sls : struct_layout_spec) (sl : struct_layout) :
  struct_layout_spec_has_layout sls sl →
  LiTactic (compute_struct_layout_goal sls) := λ a, {|
    li_tactic_P T := T sl;
  |}.
Next Obligation.
  iIntros (?? sls sl Hly T) "HT". iExists sl. iFrame. done.
Qed.

Global Typeclasses Opaque compute_struct_layout_goal.
Ltac solve_compute_struct_layout := fail "implement solve_compute_struct_layout".
#[global] Hint Extern 1 (LiTactic (compute_struct_layout_goal _)) =>
    refine (compute_struct_layout_hint _ _ _); solve_compute_struct_layout : typeclass_instances.

(** Tactic hint to compute a enum_layout for a enum_layout_spec *)
Definition compute_enum_layout_goal `{!typeGS Σ} (sls : enum_layout_spec) (T : struct_layout → iProp Σ) : iProp Σ :=
  ∃ sl, ⌜enum_layout_spec_has_layout sls sl⌝ ∗ T sl.
#[global] Typeclasses Opaque compute_enum_layout_goal.
Program Definition compute_enum_layout_hint `{!typeGS Σ} (sls : enum_layout_spec) (sl : struct_layout) :
  enum_layout_spec_has_layout sls sl →
  LiTactic (compute_enum_layout_goal sls) := λ a, {|
    li_tactic_P T := T sl;
  |}.
Next Obligation.
  iIntros (?? sls sl Hly T) "HT". iExists sl. iFrame. done.
Qed.

Global Typeclasses Opaque compute_enum_layout_goal.
Ltac solve_compute_enum_layout := fail "implement solve_compute_enum_layout".
#[global] Hint Extern 1 (LiTactic (compute_enum_layout_goal _)) =>
    refine (compute_enum_layout_hint _ _ _); solve_compute_enum_layout : typeclass_instances.

(** Tactic hint to compute a semantic Rust type for a given syntactic [rust_type] *)
Definition interpret_rust_type_goal `{!typeGS Σ} (lfts : gmap string lft) (sty : rust_type) (T : sigT type → iProp Σ) : iProp Σ :=
  ∃ (rt : RT) (ty : type rt), T (existT _ ty).
#[global] Typeclasses Opaque interpret_rust_type_goal.
Definition interpret_rust_type_pure_goal `{!typeGS Σ} (lfts : gmap string lft) (sty : rust_type) {rt} (ty : type rt) := True.
Global Typeclasses Opaque interpret_rust_type_pure_goal.
Arguments interpret_rust_type_pure_goal : simpl never.
Program Definition interpret_rust_type_hint `{!typeGS Σ} (lfts : gmap string lft) (sty : rust_type) {rt} (ty : type rt) :
  interpret_rust_type_pure_goal lfts sty ty →
  LiTactic (interpret_rust_type_goal lfts sty) := λ a, {|
    li_tactic_P T := T (existT _ ty);
  |}.
Next Obligation.
  iIntros (??? sty rt ty _ T) "Ha". simpl.
  iExists _, _. done.
Qed.

Global Typeclasses Opaque interpret_rust_type_goal.
Ltac solve_interpret_rust_type := fail "implement solve_interpret_rust_type".
#[global] Hint Extern 1 (LiTactic (interpret_rust_type_goal _ _)) =>
    refine (interpret_rust_type_hint _ _ _ _); solve_interpret_rust_type : typeclass_instances.

(** Tactic hint to compute an [enum] for a given path *)
Definition interpret_rust_enum_def_goal `{!typeGS Σ} (lfts : gmap string lft) (sty : rust_enum_def) (T : sigT enum → iProp Σ) : iProp Σ :=
  ∃ (rt : RT) (en : enum rt), T (existT _ en).
#[global] Typeclasses Opaque interpret_rust_enum_def_goal.
Definition interpret_rust_enum_def_pure_goal `{!typeGS Σ} (lfts : gmap string lft) (sty : rust_enum_def) {rt} (en : enum rt) := True.
Global Typeclasses Opaque interpret_rust_enum_def_pure_goal.
Arguments interpret_rust_enum_def_pure_goal : simpl never.
Program Definition interpret_rust_enum_def_hint `{!typeGS Σ} (lfts : gmap string lft) (sty : rust_enum_def) {rt} (en : enum rt) :
  interpret_rust_enum_def_pure_goal lfts sty en →
  LiTactic (interpret_rust_enum_def_goal lfts sty) := λ a, {|
    li_tactic_P T := T (existT _ en);
  |}.
Next Obligation.
  iIntros (??? sty rt en _ T) "Ha". simpl.
  iExists _, _. done.
Qed.

Global Typeclasses Opaque interpret_rust_enum_def_goal.
Ltac solve_interpret_rust_enum_def := fail "implement solve_interpret_rust_enum_def".
#[global] Hint Extern 1 (LiTactic (interpret_rust_enum_def_goal _ _)) =>
    refine (interpret_rust_enum_def_hint _ _ _ _); solve_interpret_rust_enum_def : typeclass_instances.


(* The same, but lifted to lists *)
(*
Definition interpret_rust_types_goal `{!typeGS Σ} (lfts : gmap string lft) (stys : list rust_type) (T : list (sigT type) → iProp Σ) : iProp Σ :=
  ∃ (rt : Type) (ty : type rt), T (existT _ ty).
#[global] Typeclasses Opaque interpret_rust_type_goal.
Definition interpret_rust_type_pure_goal `{!typeGS Σ} (lfts : gmap string lft) (sty : rust_type) {rt} (ty : type rt) := True.
Global Typeclasses Opaque interpret_rust_type_pure_goal.
Arguments interpret_rust_type_pure_goal : simpl never.
Program Definition interpret_rust_type_hint `{!typeGS Σ} (lfts : gmap string lft) (sty : rust_type) {rt} (ty : type rt) :
  interpret_rust_type_pure_goal lfts sty ty →
  LiTactic (interpret_rust_type_goal lfts sty) := λ a, {|
    li_tactic_P T := T (existT _ ty);
  |}.
Next Obligation.
  iIntros (??? sty rt ty _ T) "Ha". simpl.
  iExists _, _. done.
Qed.
 *)

(** Tactic hint to ensure that an evar is instantiated, instantiating it with the given [hint] otherwise. *)
Definition ensure_evar_instantiated_goal `{!typeGS Σ} {A} (evar : A) (hint : A) (T : A → iProp Σ) :=
  T evar.
#[global] Typeclasses Opaque ensure_evar_instantiated_goal.
Definition ensure_evar_instantiated_pure_goal `{!typeGS Σ} {A} (evar : A) (hint : A) := True.
Global Typeclasses Opaque ensure_evar_instantiated_pure_goal.
Arguments ensure_evar_instantiated_pure_goal : simpl never.
Program Definition ensure_evar_instantiated_hint `{!typeGS Σ} {A} (evar : A) (hint : A) :
  ensure_evar_instantiated_pure_goal evar hint →
  LiTactic (ensure_evar_instantiated_goal evar hint) := λ a, {|
    li_tactic_P T := T (evar);
  |}.
Next Obligation.
  iIntros (??? evar hint _ T). done.
Qed.

Global Typeclasses Opaque ensure_evar_instantiated_goal.
Ltac solve_ensure_evar_instantiated := fail "implement solve_ensure_evar_instantiated".
#[global] Hint Extern 1 (LiTactic (ensure_evar_instantiated_goal _ _)) =>
    refine (ensure_evar_instantiated_hint _ _ _); solve_ensure_evar_instantiated : typeclass_instances.

(** Same thing but for multiple evars *)
Definition ensure_evars_instantiated_goal `{!typeGS Σ} {A} {F : A → Type} (evars : list (sigT F)) (hint : list (sigT F)) (T : () → iProp Σ) :=
  T tt.
#[global] Typeclasses Opaque ensure_evars_instantiated_goal.
Definition ensure_evars_instantiated_pure_goal `{!typeGS Σ} {A} {F : A → Type} (evars : list (sigT F)) (hint : list (sigT F)) := True.
Global Typeclasses Opaque ensure_evars_instantiated_pure_goal.
Arguments ensure_evars_instantiated_pure_goal : simpl never.
Program Definition ensure_evars_instantiated_hint `{!typeGS Σ} {A} {F : A → Type} (evars : list (sigT F)) (hint : list (sigT F)) :
  ensure_evars_instantiated_pure_goal evars hint →
  LiTactic (ensure_evars_instantiated_goal evars hint) := λ a, {|
    li_tactic_P T := T tt;
  |}.
Next Obligation.
  iIntros (???? evar hint _ T). done.
Qed.

Global Typeclasses Opaque ensure_evars_instantiated_goal.
Ltac solve_ensure_evars_instantiated := fail "implement solve_ensure_evars_instantiated".
#[global] Hint Extern 1 (LiTactic (ensure_evars_instantiated_goal _ _)) =>
    refine (ensure_evars_instantiated_hint _ _ _); solve_ensure_evars_instantiated : typeclass_instances.

(** Solving [lctx_lft_alive_count] *)
(** the continuation gets the list of opened lifetimes + the new local lifetime context *)
Definition lctx_lft_alive_count_goal `{!typeGS Σ} (E : elctx) (L : llctx) (κ : lft)
    (T : (list lft) * llctx → iProp Σ) : iProp Σ :=
  ∃ κs L', ⌜lctx_lft_alive_count E L κ κs L'⌝ ∗ T (κs, L').
Program Definition lctx_lft_alive_count_hint `{!typeGS Σ} E L κ (κs : list lft) (L' : llctx) :
  lctx_lft_alive_count E L κ κs L' →
  LiTactic (lctx_lft_alive_count_goal E L κ) := λ a, {|
    li_tactic_P T := T (κs, L');
  |}.
Next Obligation.
  simpl. iIntros (?? E L κ κs L' ? T) "HT".
  iExists κs, L'. iFrame. done.
Qed.

Global Typeclasses Opaque lctx_lft_alive_count_goal.
Ltac solve_lft_alive_count := fail "implement solve_lft_alive_count".
#[global] Hint Extern 10 (LiTactic (lctx_lft_alive_count_goal _ _ _)) =>
    refine (lctx_lft_alive_count_hint _ _ _ _ _ _); solve_lft_alive_count : typeclass_instances.


(** Releasing lifetime tokens *)
Definition llctx_release_toks_goal `{!typeGS Σ} (L : llctx) (κs : list lft) (T : llctx → iProp Σ) : iProp Σ :=
  ∃ L', ⌜llctx_release_toks L κs L'⌝ ∗ T L'.
Program Definition llctx_release_toks_hint `{!typeGS Σ} L κs (L' : llctx) :
  llctx_release_toks L κs L' →
  LiTactic (llctx_release_toks_goal L κs) := λ a, {|
    li_tactic_P T := T L';
  |}.
Next Obligation.
  iIntros (?? L κs L' ? T) "HT". iExists L'. iFrame. done.
Qed.

Global Typeclasses Opaque llctx_release_toks_goal.
Ltac solve_llctx_release_toks := fail "implement solve_llctx_release_toks".
#[global] Hint Extern 10 (LiTactic (llctx_release_toks_goal _ _)) =>
    refine (llctx_release_toks_hint _ _ _ _); solve_llctx_release_toks : typeclass_instances.

(** Computing the inheritance worklist *)
Definition find_inheritances_goal `{!typeGS Σ} (T : list (list lft * iProp Σ) → iProp Σ) : iProp Σ :=
  ∃ ks, T ks.
Definition find_inheritances_pure_goal `{!typeGS Σ}  (ks : list (list lft * iProp Σ)) :=
  True.
Program Definition find_inheritances_hint `{!typeGS Σ} (ks : list (list lft * iProp Σ)) :
  find_inheritances_pure_goal ks →
  LiTactic (find_inheritances_goal) := λ a, {|
    li_tactic_P T := T ks;
  |}.
Next Obligation.
  iIntros (?? ? ? ?) "HT". iExists _. iFrame.
Qed.

Global Typeclasses Opaque find_inheritances_goal.
Global Typeclasses Opaque find_inheritances_pure_goal.
Ltac solve_find_inheritances := fail "implement solve_find_inheritances".
#[global] Hint Extern 10 (LiTactic (find_inheritances_goal)) =>
  refine (find_inheritances_hint _ _); solve_find_inheritances : typeclass_instances.

(** Computing the list of all spatial locations *)
Definition find_spatial_locs_goal `{!typeGS Σ} (T : list loc → iProp Σ) : iProp Σ :=
  ∃ ks, T ks.
Definition find_spatial_locs_pure_goal `{!typeGS Σ}  (ks : list loc) :=
  True.
Program Definition find_spatial_locs_hint `{!typeGS Σ} (ks : list loc) :
  find_spatial_locs_pure_goal ks →
  LiTactic (find_spatial_locs_goal) := λ a, {|
    li_tactic_P T := T ks;
  |}.
Next Obligation.
  iIntros (?? ? ? ?) "HT". iExists _. iFrame.
Qed.

Global Typeclasses Opaque find_spatial_locs_goal.
Global Typeclasses Opaque find_spatial_locs_pure_goal.
Ltac solve_find_spatial_locs := fail "implement solve_find_spatial_locs".
#[global] Hint Extern 10 (LiTactic (find_spatial_locs_goal)) =>
  refine (find_spatial_locs_hint _ _); solve_find_spatial_locs : typeclass_instances.

(** Computing the list of all local lifetimes whose death is implied by the death of another local lifetime (due to inclusion) *)
Definition find_implied_dying_lifetimes_goal `{!typeGS Σ} (L : llctx) (κ : lft) (T : list lft → iProp Σ) : iProp Σ :=
  ∃ ks, T ks.
Definition find_implied_dying_lifetimes_pure_goal `{!typeGS Σ} (L : llctx) (κ : lft) (ks : list lft) :=
  True.
Program Definition find_implied_dying_lifetimes_hint `{!typeGS Σ} (L : llctx) (κ : lft) (ks : list lft) :
  find_implied_dying_lifetimes_pure_goal L κ ks →
  LiTactic (find_implied_dying_lifetimes_goal L κ) := λ a, {|
    li_tactic_P T := T ks;
  |}.
Next Obligation.
  iIntros (?? ?? ? ? ?) "HT". iExists _. iFrame.
Qed.

Global Typeclasses Opaque find_implied_dying_lifetimes_goal.
Global Typeclasses Opaque find_implied_dying_lifetimes_pure_goal.
Ltac solve_find_implied_dying_lifetimes := fail "implement solve_find_implied_dying_lifetimes".
#[global] Hint Extern 10 (LiTactic (find_implied_dying_lifetimes_goal ?L ?κ)) =>
  refine (find_implied_dying_lifetimes_hint L κ _ _); solve_find_implied_dying_lifetimes : typeclass_instances.

(** Check whether an element is part of a list *)
Definition check_list_elem_of_goal `{!typeGS Σ} {A} (x : A) (xs : list A) (T : bool → iProp Σ) : iProp Σ :=
  ∃ b : bool, ⌜(if b then x ∈ xs else True)⌝ ∗ T b.
Definition check_list_elem_of_pure_goal {A} (x : A) (xs : list A) (b : bool) :=
  if b then x ∈ xs else True.
Program Definition check_list_elem_of_hint `{!typeGS Σ} {A} (x : A) (xs : list A) (b : bool) :
  check_list_elem_of_pure_goal x xs b →
  LiTactic (check_list_elem_of_goal x xs) := λ a, {|
    li_tactic_P T := T b;
  |}.
Next Obligation.
  iIntros (?? ? x xs b Ha ?) "HT". iExists _. by iFrame.
Qed.

Global Typeclasses Opaque check_list_elem_of_goal.
Global Typeclasses Opaque check_list_elem_of_pure_goal.
Ltac solve_check_list_elem_of := fail "implement solve_check_list_elem_of".
#[global] Hint Extern 10 (LiTactic (check_list_elem_of_goal ?x ?xs)) =>
  refine (check_list_elem_of_hint x xs _ _); solve_check_list_elem_of : typeclass_instances.

(** Attempt to prove a [place_update_kind] inclusion *)
Definition check_llctx_place_update_kind_incl_goal `{!typeGS Σ} (E : elctx) (L : llctx) (k1 k2 : place_update_kind) (T : bool → iProp Σ) : iProp Σ :=
  ∃ b : bool, ⌜if b then lctx_place_update_kind_incl E L k1 k2 else True⌝ ∗ T b.
Definition check_llctx_place_update_kind_incl_pure_goal `{!typeGS Σ} (E : elctx) (L : llctx) (k1 k2 : place_update_kind) (b : bool) : Prop :=
  if b then lctx_place_update_kind_incl E L k1 k2 else True.
Program Definition check_llctx_place_update_kind_incl_goal_hint `{!typeGS Σ} (E : elctx) (L : llctx) (k1 k2 : place_update_kind)  (b : bool) :
  check_llctx_place_update_kind_incl_pure_goal E L k1 k2 b →
  LiTactic (check_llctx_place_update_kind_incl_goal E L k1 k2) := λ a, {|
    li_tactic_P T := T b;
  |}.
Next Obligation.
  unfold check_llctx_place_update_kind_incl_pure_goal.
  iIntros (?????? b Ha T) "HT".
  iExists b. iR. done.
Qed.

Global Typeclasses Opaque check_llctx_place_update_kind_incl_goal.
Ltac solve_check_llctx_place_update_kind_incl_pure_goal := fail "implement solve_check_llctx_place_update_kind_incl_pure_goal".
#[global] Hint Extern 10 (LiTactic (check_llctx_place_update_kind_incl_goal _ _ _ _)) =>
    refine (check_llctx_place_update_kind_incl_goal_hint _ _ _ _ _ _); solve_check_llctx_place_update_kind_incl_pure_goal : typeclass_instances.

(** Check whether a [place_update_kind] obeys [UpdUniq] *)
Definition check_llctx_place_update_kind_incl_uniq_goal `{!typeGS Σ} (E : elctx) (L : llctx) (k1 : place_update_kind) (κs : list lft) (T : option (place_update_kind_rt_same k1 = true) → iProp Σ) : iProp Σ :=
  ∃ ob : option _, ⌜if ob then lctx_place_update_kind_incl E L k1 (UpdUniq κs) else True⌝ ∗ T ob.
Definition check_llctx_place_update_kind_incl_uniq_pure_goal `{!typeGS Σ} (E : elctx) (L : llctx) (k1 : place_update_kind) (κs : list lft) (b : option (place_update_kind_rt_same k1 = true)) : Prop :=
  if b then lctx_place_update_kind_incl E L k1 (UpdUniq κs) else True.
Program Definition check_llctx_place_update_kind_incl_uniq_goal_hint `{!typeGS Σ} (E : elctx) (L : llctx) (k1 : place_update_kind) (κs : list lft) (b : option (place_update_kind_rt_same k1 = true)) :
  check_llctx_place_update_kind_incl_uniq_pure_goal E L k1 κs b →
  LiTactic (check_llctx_place_update_kind_incl_uniq_goal E L k1 κs) := λ a, {|
    li_tactic_P T := T b;
  |}.
Next Obligation.
  unfold check_llctx_place_update_kind_incl_uniq_pure_goal.
  iIntros (?????? b Ha T) "HT".
  iExists b. iR. done.
Qed.

Global Typeclasses Opaque check_llctx_place_update_kind_incl_uniq_goal.
Ltac solve_check_llctx_place_update_kind_incl_uniq_pure_goal := fail "implement solve_check_llctx_place_update_kind_incl_uniq_pure_goal".
#[global] Hint Extern 10 (LiTactic (check_llctx_place_update_kind_incl_uniq_goal _ _ _ _)) =>
    refine (check_llctx_place_update_kind_incl_uniq_goal_hint _ _ _ _ _ _); solve_check_llctx_place_update_kind_incl_uniq_pure_goal : typeclass_instances.

(** Check whether a lifetime inclusion holds *)
Definition check_lctx_lft_incl_goal `{!typeGS Σ} (E : elctx) (L : llctx) (κ1 κ2 : lft) (T : bool → iProp Σ) : iProp Σ :=
  ∃ b : bool, ⌜if b then lctx_lft_incl E L κ1 κ2 else True⌝ ∗ T b.
Definition check_lctx_lft_incl_pure_goal `{!typeGS Σ} (E : elctx) (L : llctx) (κ1 κ2 : lft) (b : bool) : Prop :=
  if b then lctx_lft_incl E L κ1 κ2 else True.

Program Definition check_lctx_lft_incl_goal_hint `{!typeGS Σ} (E : elctx) (L : llctx) (κ1 κ2 : lft) (b : bool) :
  check_lctx_lft_incl_pure_goal E L κ1 κ2 b →
  LiTactic (check_lctx_lft_incl_goal E L κ1 κ2) := λ a, {|
    li_tactic_P T := T b;
  |}.
Next Obligation.
  unfold check_lctx_lft_incl_pure_goal.
  iIntros (?????? b Ha T) "HT".
  iExists b. iR. done.
Qed.

Global Typeclasses Opaque check_lctx_lft_incl_goal.
Global Typeclasses Opaque check_lctx_lft_incl_pure_goal.
Ltac solve_check_lctx_lft_incl_goal := fail "implement solve_check_lctx_lft_incl_goal".
#[global] Hint Extern 10 (LiTactic (check_lctx_lft_incl_goal _ _ _ _)) =>
    refine (check_lctx_lft_incl_goal_hint _ _ _ _ _ _); solve_check_lctx_lft_incl_goal : typeclass_instances.

(** ** Generic context folding mechanism *)
Section folding.
  Context `{!typeGS Σ}.
  (** We (formerly) use this primarily for unblocking the typing context when ending a lifetime *)

  (* bundled ltypes *)
  Record bltype := mk_bltype {
    bltype_rt : RT;
    bltype_rfn : place_rfn bltype_rt;
    bltype_ltype : ltype bltype_rt;
  }.
  Definition type_ctx := list (loc * bltype).
  Implicit Types (tctx : type_ctx).

  Definition type_ctx_interp π tctx : iProp Σ :=
    [∗ list] i ∈ tctx, let '(l, bt) := i in l ◁ₗ[π, Owned] bt.(bltype_rfn) @ bt.(bltype_ltype).
  Lemma type_ctx_interp_cons π l t tctx :
    type_ctx_interp π ((l, t) :: tctx) ⊣⊢ (l ◁ₗ[π, Owned] t.(bltype_rfn) @ t.(bltype_ltype)) ∗ type_ctx_interp π tctx.
  Proof. iApply big_sepL_cons. Qed.

  Section folder.
  Context {Acc : Type} (Acc_interp : Acc → iProp Σ).
  (** Initializer for doing a context fold with action [m].
      The automation will use this typing judgment as a hint to gather up the context and
        start folding over the context.

      Clients that want to initiate context folding should generate a goal with this judgment,
        with a [m] that identifies the folding action.
   *)
  Definition typed_pre_context_fold (π : thread_id) (E : elctx) (L : llctx) {M} (m : M) (T : llctx → iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ ⌜lft_userE ⊆ F⌝ -∗ ⌜shrE ⊆ F⌝ -∗
    rrust_ctx -∗
    elctx_interp E -∗
    llctx_interp L -∗
    logical_step F (∃ L', llctx_interp L' ∗ T L').
  Class TypedPreContextFold {M} (π : thread_id) (E : elctx) (L : llctx) (m : M) :=
    typed_pre_context_fold_proof T : iProp_to_Prop (typed_pre_context_fold π E L m T).

  (** The main context folding judgment. [tctx] is the list of types to fold. *)
  Definition typed_context_fold {M} (E : elctx) (L : llctx) (m : M) (tctx : list loc) (acc : Acc) (T : llctx → M → Acc → iProp Σ) : iProp Σ :=
    (∀ F, ⌜lftE ⊆ F⌝ -∗ ⌜lft_userE ⊆ F⌝ -∗ ⌜shrE ⊆ F⌝ -∗
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      logical_step F (Acc_interp acc) ={F}=∗
      ∃ L' acc' m', llctx_interp L' ∗ logical_step F (Acc_interp acc') ∗ T L' m' acc').
  Class TypedContextFold (E : elctx) (L : llctx) {M} (m : M) (tctx : list loc) (acc : Acc) :=
    typed_context_fold_proof T : iProp_to_Prop (typed_context_fold E L m tctx acc T).

  (**
    This does a context fold step, by transforming [tctx] and [acc].
    Clients of context folding should register instances of this (for the right [m]) in
      order to register the folding action.
    Every such rule should make progress, so that the whole thing is terminating.
   *)
  Definition typed_context_fold_step {M} (π : thread_id) (E : elctx) (L : llctx) (m : M) (l : loc) {rt} (lt : ltype rt) (r : place_rfn rt) (tctx : list loc) (acc : Acc) (T : llctx → M → Acc → iProp Σ) : iProp Σ :=
    (∀ F, ⌜lftE ⊆ F⌝ -∗ ⌜lft_userE ⊆ F⌝ -∗ ⌜shrE ⊆ F⌝ -∗
      rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      logical_step F (Acc_interp acc) -∗
      l ◁ₗ[ π, Owned] r @ lt -∗ |={F}=>
      (∃ L' acc' m', llctx_interp L' ∗ logical_step F (Acc_interp acc') ∗ T L' m' acc')).
  Class TypedContextFoldStep {M} (π : thread_id) (E : elctx) (L : llctx) (m : M) (l : loc) {rt} (lt : ltype rt) (r : place_rfn rt) (tctx : list loc) (acc : Acc) :=
    typed_context_fold_step_proof T : iProp_to_Prop (typed_context_fold_step π E L m l lt r tctx acc T).

  (** Terminator for the context folding typing process.
    It gathers up the folding result and takes a program step to strip the accumulated laters.
  *)
  Definition typed_context_fold_end (E : elctx) (L : llctx) (acc : Acc) (T : llctx → iProp Σ) : iProp Σ :=
    ∀ F, ⌜lftE ⊆ F⌝ -∗ ⌜lft_userE ⊆ F⌝ -∗ ⌜shrE ⊆ F⌝ -∗
      rrust_ctx -∗
      elctx_interp E -∗
      llctx_interp L -∗
      logical_step F (Acc_interp acc) -∗
      logical_step F (∃ L2, llctx_interp L2 ∗ T L2).
  (* no type class -- we should directly apply the typing rule for this. *)

  (** Finish context folding when the whole list has been processed. *)
  Lemma typed_context_fold_nil {M} E L (m : M) acc T  :
    T L m acc
    ⊢ typed_context_fold E L m [] acc T.
  Proof.
    iIntros "HT".
    iIntros (????) "#CTX #HE HL Hdel".
    iExists L, acc, m. by iFrame.
  Qed.
  Global Instance typed_context_fold_nil_inst {M} E L (m : M) acc :
    TypedContextFold E L m [] acc :=
      λ T, i2p (typed_context_fold_nil E L m acc T).

  (** Take a context folding step. *)
  (* We make this optional, because some of the items may already have been used for stratifying other types (e.g. for invariant folding) *)
  Lemma typed_context_fold_cons {M} E L (m : M) l (tctx : list loc) acc T :
    find_in_context (FindOptLoc l) (λ res,
      match res with
      | None => typed_context_fold E L m tctx acc T
      | Some (existT rt' (lt', r', bk', π)) =>
          ⌜bk' = Owned⌝ ∗ (typed_context_fold_step π E L m l lt' r' tctx acc T)
      end)
    ⊢ typed_context_fold E L m (l :: tctx) acc T.
  Proof.
    rewrite /FindOptLoc. iIntros "(%res & HT)".
    destruct res as [ [rt' [[[lt' r'] bk'] π]] | ]; simpl.
    - iDestruct "HT" as "(Hl & HT)". iPoseProof ("HT") as "(-> & HT)".
      iIntros (????) "#CTX #HE HL Hdel".
      iDestruct ("HT" with "[//] [//] [//] CTX HE HL Hdel Hl") as ">Hs".
      done.
    - iDestruct "HT" as "(_ & HT)". iApply "HT".
  Qed.
  Global Instance typed_context_fold_cons_inst {M} E L (m : M) l (tctx : list loc) acc :
    TypedContextFold E L m (l :: tctx) acc :=
      λ T, i2p (typed_context_fold_cons E L m l tctx acc T).

  (** Typing rule for ending context folding.
    Yields the accumulated result and continues with the next statement.
  *)
  Lemma type_context_fold_end E L acc T :
    (introduce_with_hooks E L (Acc_interp acc) T)
    ⊢ typed_context_fold_end E L acc T.
  Proof.
    iIntros "Hs". iIntros (????) "#(LFT & LLCTX) #HE HL Hstep".
    iApply logical_step_fupd.
    iApply (logical_step_wand with "Hstep").
    iIntros "Hacc". iMod ("Hs" with "[//] HE HL Hacc") as "(%L3 & HL & HT)".
    eauto with iFrame.
  Qed.

  (** Initialize context folding.
     This is not an instance, but can be used when constructing instances for particular instantiations of context folding. *)
  Lemma typed_context_fold_init {M} (init_acc : Acc) π E L (m : M) (tctx : list loc) Φ T :
    Acc_interp init_acc ∗
    typed_context_fold E L m tctx init_acc (λ L' m' acc, Φ m' acc ∗ typed_context_fold_end E L' acc T) -∗
    typed_pre_context_fold π E L m T.
  Proof.
    iIntros "(Hinit & Hfold)".
    iIntros (????) "#CTX #HE HL".
    iApply fupd_logical_step.
    iDestruct ("Hfold" $! F with "[//] [//] [//] CTX HE HL [Hinit]") as ">Hs".
    { iApply logical_step_intro. iFrame. }
    iDestruct "Hs" as (L' acc' m') "(HL & Hdel & ? & Hs)".
    rewrite /typed_context_fold_end.
    iApply ("Hs" with "[//] [//] [//] CTX HE HL Hdel").
  Qed.
  End folder.

  (* Unfold the type context so Lithium separates the big_sep *)
  Lemma simplify_type_context π tctx T :
    (([∗ list] i ∈ tctx, let '(l, bt) := i in l ◁ₗ[ π, Owned] bltype_rfn bt @ bltype_ltype bt) -∗ T) ⊢
    simplify_hyp (type_ctx_interp π tctx) T.
  Proof. done. Qed.
  Global Instance simplify_type_context_inst π tctx :
    SimplifyHyp (type_ctx_interp π tctx) (Some 0%N) :=
    λ T, i2p (simplify_type_context π tctx T).
End folding.

Section relate_list.
  Context `{!typeGS Σ}.
  (** A generalization of subsume_list. *)
  Record FoldableRelation {A B} : Type := FR {
    fr_rel : elctx → llctx → nat → A → B → iProp Σ → iProp Σ;
    fr_cap : nat;
    fr_inv : Prop;
    fr_core_rel : elctx → llctx → nat → A → B → iProp Σ;
    fr_elim_mode : bool;
    fr_elim E L i a b :
      ⊢ if fr_elim_mode then
        ∀ T F, ⌜lftE ⊆ F⌝ -∗ rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ fr_rel E L i a b T ={F}=∗ fr_core_rel E L i a b ∗ llctx_interp L ∗ T
      else ∀ T, fr_rel E L i a b T -∗ fr_core_rel E L i a b ∗ T;
  }.
  Arguments fr_rel {_ _}.
  Arguments fr_core_rel {_ _}.
  Arguments fr_elim_mode {_ _}.

  Definition relate_list {A B} (E : elctx) (L : llctx) (ig : list nat) (l1 : list A) (l2 : list B) (i0 : nat) (R : FoldableRelation) (T : iProp Σ) : iProp Σ :=
    if R.(fr_elim_mode) then
      (∀ F, ⌜lftE ⊆ F⌝ -∗ rrust_ctx -∗ elctx_interp E -∗ llctx_interp L ={F}=∗
      (⌜i0 + length l1 ≤ R.(fr_cap)⌝ -∗ ⌜R.(fr_inv)⌝ -∗
      [∗ list] i ↦ a; b ∈ l1; l2, if decide ((i + i0)%nat ∈ ig) then True else R.(fr_core_rel) E L (i + i0)%nat a b) ∗ llctx_interp L ∗ T)%I
    else ((⌜i0 + length l1 ≤ R.(fr_cap)⌝ -∗ ⌜R.(fr_inv)⌝ -∗
      [∗ list] i ↦ a; b ∈ l1; l2, if decide ((i + i0)%nat ∈ ig) then True else R.(fr_core_rel) E L (i + i0)%nat a b) ∗ T)%I
  .
  Class RelateList {A B} (E : elctx) (L : llctx) (ig : list nat) (l1 : list A) (l2 : list B) (i0 : nat) (R : FoldableRelation) : Type :=
    relate_list_proof T : iProp_to_Prop (relate_list E L ig l1 l2 i0 R T).

  Lemma relate_list_ig_cons_le {A B} E L ig (j i0 : nat) (l1 : list A) (l2 : list B) (R : FoldableRelation) :
    (j < i0)%nat →
    ([∗ list] i ↦ a; b ∈ l1; l2, if decide (i + i0 ∈ (j :: ig))%nat then True else fr_core_rel R E L (i + i0)%nat a b) -∗
    ([∗ list] i ↦ a; b ∈ l1; l2, if decide (i + i0 ∈ (ig))%nat then True else fr_core_rel R E L (i + i0)%nat a b).
  Proof.
    intros Hlt.
    iInduction l1 as [ | a l1] "IH" forall (j i0 l2 Hlt); simpl; first by eauto.
    destruct l2 as [ | b l2]; simpl; first by eauto.
    case_decide as Hel.
    - apply elem_of_cons in Hel as [ ? | ?]; first lia.
      rewrite decide_True; last done. rewrite !left_id.
      iIntros "Ha". iApply (big_sepL2_mono); first last.
      { iApply ("IH" $! _ (S i0)); first last.
        { iApply big_sepL2_mono; last done. iIntros. rewrite Nat.add_succ_r//. }
        iPureIntro. lia. }
      iIntros. rewrite Nat.add_succ_r//.
    - apply not_elem_of_cons in Hel as [_ Hel].
      rewrite decide_False; last done.
      iIntros "($ & Ha)". iApply (big_sepL2_mono); first last.
      { iApply ("IH" $! _ (S i0)); first last.
        { iApply big_sepL2_mono; last done. iIntros. rewrite Nat.add_succ_r//. }
        iPureIntro. lia. }
      iIntros. rewrite Nat.add_succ_r//.
  Qed.

  Lemma relate_list_replicate_elim_full {A B} E L ig n (a : A) (b : B) i0 (R : FoldableRelation) T :
    R.(fr_elim_mode) = true →
    (rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ ⌜R.(fr_inv)⌝ -∗
      □ ∀ i, ⌜(i0 ≤ i < R.(fr_cap))%nat⌝ -∗ ⌜i ∉ ig⌝ -∗ R.(fr_core_rel) E L i a b) -∗
    T -∗ relate_list E L ig (replicate n a) (replicate n b) i0 R T.
  Proof.
    intros Ha. rewrite /relate_list Ha.
    iIntros "HR HT" (F ?) "#CTX #HE HL".
    iPoseProof ("HR" with "CTX HE HL") as "#HR".
    iFrame "HT HL".
    iInduction n as [ | n] "IH" forall (i0) "HR"; simpl.
    { by iFrame. }
    iMod ("IH" $! (S i0) with "[]") as "Ha".
    { iModIntro. iIntros (Hinv i Hi Hnel). iModIntro. iApply "HR"; iPureIntro; first [done | lia]. }
    iModIntro. iIntros "%Hinv %Hi".
    case_decide.
    - iR.
      iApply (big_sepL2_wand with "(Ha [] [//])").
      { iPureIntro. lia. }
      iApply big_sepL2_intro; first (by rewrite !length_replicate).
      iModIntro. iIntros (?????). rewrite Nat.add_succ_r. eauto.
    - iSplitR. { iApply "HR"; simpl in Hinv; iPureIntro; first [lia | done]. }
      iApply (big_sepL2_mono with "(Ha [] [//])"); last by (iPureIntro; lia).
      iIntros (?????). rewrite Nat.add_succ_r. done.
  Qed.
  Lemma relate_list_replicate_elim_weak {A B} E L ig n (a : A) (b : B) i0 (R : FoldableRelation) T :
    R.(fr_elim_mode) = false →
    (⌜R.(fr_inv)⌝ -∗ □ ∀ i, ⌜(i0 ≤ i < R.(fr_cap))%nat⌝ -∗ ⌜i ∉ ig⌝ -∗ R.(fr_core_rel) E L i a b) -∗
    T -∗ relate_list E L ig (replicate n a) (replicate n b) i0 R T.
  Proof.
    intros Ha. rewrite /relate_list Ha.
    iIntros "HR $". iIntros "%Hinv %Hi". iPoseProof ("HR" with "[//]") as "#HR".
    iInduction n as [ | n] "IH" forall (i0 Hinv Hi) "HR"; simpl.
    { by iFrame. }
    iPoseProof ("IH" $! (S i0) with "[] [//] []") as "Ha".
    { iPureIntro. simpl in Hinv. lia. }
    { iModIntro. iIntros (i ? Hnel). iApply "HR"; iPureIntro; first [done | lia]. }
    case_decide.
    - iR.
      iApply (big_sepL2_wand with "Ha").
      iApply big_sepL2_intro; first (by rewrite !length_replicate).
      iModIntro. iIntros (?????). rewrite Nat.add_succ_r. eauto.
    - iSplitR. { iApply "HR"; simpl in Hinv; iPureIntro; first [lia | done]. }
      iApply (big_sepL2_mono with "Ha"). iIntros (?????). rewrite Nat.add_succ_r. done.
  Qed.

  Local Lemma relate_list_insert_in_ig' {A B} E L (ig : list nat) (l1 : list A) (l2 : list B) (i0 : nat) i x R :
    (i0 + i ∈ ig)%nat →
    (⌜i0 + length l1 ≤ fr_cap R⌝ -∗ ⌜fr_inv R⌝ -∗ [∗ list] i↦a;b ∈ l1;l2, if decide ((i + i0)%nat ∈ ig) then True else fr_core_rel R E L (i + i0) a b) -∗
    (⌜i0 + length (<[ i:= x]> l1) ≤ fr_cap R⌝ -∗ ⌜fr_inv R⌝ -∗ [∗ list] i↦a;b ∈ <[i:=x]>l1;l2, if decide ((i + i0)%nat ∈ ig) then True else fr_core_rel R E L (i + i0) a b).
  Proof.
    iIntros (Hel) "Ha %Hinv %".
    iSpecialize ("Ha" with "[] [//]").
    { rewrite length_insert in Hinv. done. }
    iInduction l1 as [ | a l1] "IH" forall (l2 i i0 Hel Hinv); simpl; first done.
    destruct l2 as [ | b l2]. { destruct i; done. }
    destruct i as [ | i].
    - simpl.
      case_decide; first done.
      rewrite Nat.add_0_r in Hel. done.
    - simpl.
      case_decide.
      + iDestruct "Ha" as "(_ & Ha)". iR.
        iPoseProof ("IH" $! _ _ (S i0) with "[] [] [Ha]") as "Hi"; first last.
        { iApply (big_sepL2_mono); last iApply "Hi". iIntros. rewrite -Nat.add_succ_r//. }
        { iApply (big_sepL2_mono with "Ha"). iIntros. rewrite -Nat.add_succ_r//. }
        { simpl in Hinv. iPureIntro. lia. }
        { iPureIntro. move: Hel. rewrite Nat.add_succ_r//. }
      + iDestruct "Ha" as "($ & Ha)".
        iPoseProof ("IH" $! _ _ (S i0) with "[] [] [Ha]") as "Hi"; first last.
        { iApply (big_sepL2_mono); last iApply "Hi". iIntros. rewrite -Nat.add_succ_r//. }
        { iApply (big_sepL2_mono with "Ha"). iIntros. rewrite -Nat.add_succ_r//. }
        { simpl in Hinv. iPureIntro. lia. }
        { iPureIntro. move: Hel. rewrite Nat.add_succ_r//. }
  Qed.
  Lemma relate_list_insert_in_ig {A B} E L ig (l1 : list A) (l2 : list B) (i0 : nat) i x R T `{CanSolve (i0 + i ∈ ig)%nat} :
    relate_list E L ig l1 l2 i0 R T
    ⊢ relate_list E L ig (<[i := x]> l1) l2 i0 R T.
  Proof.
    match goal with H : CanSolve _ |- _ => unfold CanSolve in H; rename H into Hel end.
    iIntros "Ha".
    rewrite /relate_list; destruct fr_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iMod ("Ha" with "[//] CTX HE HL") as "(Ha & $ & $)".
      iModIntro. by iApply relate_list_insert_in_ig'.
    - iDestruct "Ha" as "(Ha & $)". by iApply relate_list_insert_in_ig'.
  Qed.
  Global Instance relate_list_insert_in_ig_inst {A B} E L ig (l1 : list A) (l2 : list B) (i0 : nat) i x R `{!CanSolve (i0 + i ∈ ig)%nat} :
    RelateList E L ig (<[i := x]> l1) l2 i0 R :=
    λ T, i2p (relate_list_insert_in_ig E L ig l1 l2 i0 i x R T).

  Lemma relate_list_cons_l {A B} E L ig (l1 : list A) (l2 : list B) i0 R a T :
    ⌜i0 ∉ ig⌝ ∗ (∃ b l2', ⌜l2 = b :: l2'⌝ ∗
      R.(fr_rel) E L i0 a b (relate_list E L ig l1 l2' (S i0) R T))
    ⊢ relate_list E L ig (a :: l1) l2 i0 R T.
  Proof.
    iIntros "(%Hnel & %b & %l2' & -> & HR)".
    rewrite /relate_list. iPoseProof (fr_elim R) as "Hx". destruct fr_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iMod ("Hx" with "[//] CTX HE HL HR") as "(HR & HL & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & $)".
      iModIntro. iIntros "%Hinv %". iSpecialize ("Ha" with "[] [//]").
      { simpl in Hinv. iPureIntro. lia. }
      rewrite big_sepL2_cons. simpl.
      rewrite decide_False; last done. iFrame.
      iApply (big_sepL2_mono with "Ha").
      iIntros. rewrite Nat.add_succ_r//.
    - iPoseProof ("Hx" with "HR") as "(Ha & Hb & $)".
      iIntros "%Hinv %". iSpecialize ("Hb" with "[] [//]").
      { simpl in Hinv. iPureIntro. lia. }
      rewrite big_sepL2_cons. simpl.
      rewrite decide_False; last done. iFrame.
      iApply (big_sepL2_mono with "Hb").
      iIntros. rewrite Nat.add_succ_r//.
  Qed.
  Global Instance relate_list_cons_l_inst {A B} E L ig (l1 : list A) (l2 : list B) i0 a R :
    RelateList E L ig (a :: l1) l2 i0 R :=
    λ T, i2p (relate_list_cons_l E L ig l1 l2 i0 R a T).

  Local Lemma relate_list_insert_not_in_ig' {A B} E L ig (l1 : list A) (l2 : list B) (R : FoldableRelation) i0 i a b :
    (i0 + i ∉ ig)%nat →
    i < length l1 →
    l2 !! i = Some b →
    fr_core_rel R E L (i0 + i) a b -∗
    (⌜i0 + length l1 ≤ fr_cap R⌝ -∗ ⌜fr_inv R⌝ -∗ [∗ list] i1↦a0;b0 ∈ l1;l2, if decide ((i1 + i0)%nat ∈ (i0 + i)%nat :: ig) then True else fr_core_rel R E L (i1 + i0) a0 b0) -∗
    (⌜i0 + length (<[i:=a]> l1) ≤ fr_cap R⌝ -∗ ⌜fr_inv R⌝ -∗ [∗ list] i1↦a0;b0 ∈ <[i:=a]> l1;l2, if decide ((i1 + i0)%nat ∈ ig) then True else fr_core_rel R E L (i1 + i0) a0 b0).
  Proof.
    iIntros (Hnel Hi Hlook) "HR Ha %Hinv %". iSpecialize ("Ha" with "[] [//]").
    { iPureIntro. rewrite length_insert in Hinv. lia. }
    iInduction l1 as [ | a' l1] "IH" forall (l2 i i0 Hnel Hi Hlook Hinv).
    { simpl in *. lia. }
    destruct i as [ | i]; simpl.
    - destruct l2 as [ | b' l2]; first done.
      injection Hlook as ->.
      rewrite !big_sepL2_cons.
      simpl. iDestruct "Ha" as "(_ & Ha)".
      rewrite decide_False; first last. { move: Hnel. rewrite Nat.add_0_r//. }
      rewrite Nat.add_0_r. iFrame.
      iApply big_sepL2_mono; first last.
      { iApply (relate_list_ig_cons_le); first last.
        { iApply big_sepL2_mono; last done. iIntros. rewrite -Nat.add_succ_r//. }
        lia.
      }
      iIntros. rewrite Nat.add_succ_r//.
    - destruct l2 as [ | b' l2]; first done.
      simpl in Hlook.
      rewrite !big_sepL2_cons/=.
      destruct (decide (i0 ∈ ig)).
      + iR. iDestruct "Ha" as "(_ & Ha)".
        iApply big_sepL2_mono; first last.
        { iApply ("IH" with "[] [] [] [] [HR]"); first last.
          - iApply big_sepL2_mono; last done. iIntros. rewrite -(Nat.add_succ_r _ i0) (Nat.add_succ_r _ i) //.
          - rewrite Nat.add_succ_r. done.
          - iPureIntro. simpl in Hinv. lia.
          - done.
          - simpl in *; iPureIntro. lia.
          - iPureIntro. move: Hnel. rewrite Nat.add_succ_r. done.
        }
        iIntros. rewrite Nat.add_succ_r//.
      + rewrite decide_False; first last. { apply not_elem_of_cons. split; last done. lia. }
        iDestruct "Ha" as "($ & Ha)".
        iApply big_sepL2_mono; first last.
        { iApply ("IH" with "[] [] [] [] [HR]"); first last.
          - iApply big_sepL2_mono; last done. iIntros. rewrite -(Nat.add_succ_r _ i0) (Nat.add_succ_r _ i) //.
          - rewrite Nat.add_succ_r. done.
          - iPureIntro. simpl in Hinv. lia.
          - done.
          - simpl in *; iPureIntro. lia.
          - iPureIntro. move: Hnel. rewrite Nat.add_succ_r. done.
        }
        iIntros. rewrite Nat.add_succ_r//.
  Qed.

  Lemma relate_list_insert_not_in_ig {A B} E L ig (l1 : list A) (l2 : list B) (R : FoldableRelation) i0 i a T `{CanSolve (i0 + i ∉ ig)%nat} :
    ⌜i < length l1⌝ ∗
    (∃ b, ⌜l2 !! i = Some b⌝ ∗ R.(fr_rel) E L (i0 + i) a b (relate_list E L ((i0 + i) :: ig)%nat l1 l2 i0 R T))
    ⊢ relate_list E L ig (<[i := a]> l1) l2 i0 R T.
  Proof.
    match goal with H : CanSolve _ |- _ => rewrite /CanSolve in H; rename H into Hnel end.
    iIntros "(%Hi & %b & %Hlook & HR)".
    iPoseProof (fr_elim R) as "Hx".
    rewrite /relate_list. destruct fr_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iMod ("Hx" with "[//] CTX HE HL HR") as "(HR & HL & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & $)".
      iModIntro. iApply (relate_list_insert_not_in_ig' with "HR Ha"); done.
    - iPoseProof ("Hx" with "HR") as "(HR & Ha & $)".
      iApply (relate_list_insert_not_in_ig' with "HR Ha"); done.
  Qed.
  Global Instance relate_list_insert_not_in_ig_inst {A B} E L ig (l1 : list A) (l2 : list B) R (i0 : nat) i a `{!CanSolve (i0 + i ∉ ig)%nat} :
    RelateList E L ig (<[i := a]> l1) l2 i0 R :=
    λ T, i2p (relate_list_insert_not_in_ig E L ig l1 l2 R i0 i a T).

  Lemma relate_list_app_l {A B} E L ig (l1 l1' : list A) (l2 : list B) (R : FoldableRelation) (i0 : nat) T :
    relate_list E L ig l1 (take (length l1) l2) i0 R (relate_list E L ig l1' (drop (length l1) l2) (length l1 + i0)%nat R T)
    ⊢ relate_list E L ig (l1 ++ l1') l2 i0 R T.
  Proof.
    iIntros "Ha".
    rewrite /relate_list; destruct fr_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iMod ("Ha" with "[//] CTX HE HL") as "(Ha & HL & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Hb & $ & $)".
      iModIntro. iIntros "%Hinv %".
      rewrite length_app in Hinv.
      iSpecialize ("Ha" with "[] [//]").
      { iPureIntro. lia. }
      iSpecialize ("Hb" with "[] [//]").
      { iPureIntro. lia. }
      rewrite -{3}(take_drop (length l1) l2).
      iApply (big_sepL2_app with "Ha").
      iApply (big_sepL2_mono with "Hb").
      iIntros. rewrite Nat.add_assoc [(k + _)%nat]Nat.add_comm//.
    - iDestruct "Ha" as "(Ha & Hb & $)". iIntros "%Hinv %".
      rewrite length_app in Hinv.
      iSpecialize ("Ha" with "[] [//]").
      { iPureIntro. lia. }
      iSpecialize ("Hb" with "[] [//]").
      { iPureIntro. lia. }
      rewrite -{3}(take_drop (length l1) l2).
      iApply (big_sepL2_app with "Ha").
      iApply (big_sepL2_mono with "Hb").
      iIntros. rewrite Nat.add_assoc [(k + _)%nat]Nat.add_comm//.
  Qed.
  Global Instance relate_list_app_l_inst {A B} E L ig (l1 l1' : list A) (l2 : list B) R i0 :
    RelateList E L ig (l1 ++ l1') l2 i0 R :=
    λ T, i2p (relate_list_app_l E L ig l1 l1' l2 R i0 T).
End relate_list.

Section relate_hlist.
  Context `{!typeGS Σ}.
  (** A generalization of subsume_list. *)
  Record HetFoldableRelation {A} {G : A → Type} {H : A → Type} : Type := HFR {
    hfr_rel : elctx → llctx → nat → ∀ {x : A}, G x → H x → iProp Σ → iProp Σ;
    hfr_cap : nat;
    hfr_inv : Prop;
    hfr_core_rel : elctx → llctx → nat → ∀ {x : A}, G x → H x → iProp Σ;
    hfr_elim_mode : bool;
    hfr_elim E L i (x : A) (a : G x) (b : H x) :
      ⊢ if hfr_elim_mode then
        ∀ T F, ⌜lftE ⊆ F⌝ -∗ rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ hfr_rel E L i a b T ={F}=∗ hfr_core_rel E L i a b ∗ llctx_interp L ∗ T
      else ∀ T, hfr_rel E L i a b T -∗ hfr_core_rel E L i a b ∗ T;
  }.
  Arguments hfr_rel {_ _ _}.
  Arguments hfr_core_rel {_ _ _}.
  Arguments hfr_elim_mode {_ _ _}.

  Definition relate_hlist {A} {G H : A → Type} (E : elctx) (L : llctx) (ig : list nat) (Xs : list A) (l1 : hlist G Xs) (l2 : hlist H Xs) (i0 : nat) (R : @HetFoldableRelation A G H) (T : iProp Σ) : iProp Σ :=
    if R.(hfr_elim_mode) then
      (∀ F, ⌜lftE ⊆ F⌝ -∗ rrust_ctx -∗ elctx_interp E -∗ llctx_interp L ={F}=∗
      (⌜i0 + length Xs ≤ R.(hfr_cap)⌝ -∗ ⌜R.(hfr_inv)⌝ -∗
      [∗ list] i ↦ p ∈ hzipl2 _ l1 l2, let '(existT _ (a, b)) := (p : (sigT (λ x : A, G x * H x)%type))  in
        if decide ((i + i0)%nat ∈ ig) then True else
        R.(hfr_core_rel) E L (i + i0)%nat _ a b) ∗ llctx_interp L ∗ T)%I
    else ((⌜i0 + length Xs ≤ R.(hfr_cap)⌝ -∗ ⌜R.(hfr_inv)⌝ -∗
      [∗ list] i ↦ p ∈ hzipl2 _ l1 l2, let '(existT _ (a, b)) := p in
        if decide ((i + i0)%nat ∈ ig) then True else R.(hfr_core_rel) E L (i + i0)%nat _ a b) ∗ T)%I
  .
  Class RelateHList {A} {G H : A → Type} (E : elctx) (L : llctx) (ig : list nat) (Xs : list A) (l1 : hlist G Xs) (l2 : hlist H Xs) (i0 : nat) (R : @HetFoldableRelation A G H) : Type :=
    relate_hlist_proof T : iProp_to_Prop (relate_hlist E L ig Xs l1 l2 i0 R T).

  Lemma relate_hlist_nil {A} {G H : A → Type} E L ig (l1 : hlist G []) (l2 : hlist H []) i0 R T :
    T ⊢ relate_hlist E L ig [] l1 l2 i0 R T.
  Proof.
    iIntros "HT". rewrite /relate_hlist. destruct hfr_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iFrame. iIntros "!> _ _". inv_hlist l1; inv_hlist l2. done.
    - iFrame. iIntros (??). inv_hlist l1; inv_hlist l2; done.
  Qed.
  Global Instance relate_hlist_nil_inst {A} {G H : A → Type} E L ig (l1 : hlist G []) (l2 : hlist H []) i0 R :
    RelateHList E L ig [] (l1) l2 i0 R :=
    λ T, i2p (relate_hlist_nil E L ig l1 l2 i0 R T).

  Lemma relate_hlist_cons {A} {G H : A → Type} E L ig (X : A) (Xs : list A) (l1 : hlist G (X :: Xs)) (l2 : hlist H (X :: Xs)) i0 R T :
    ⌜i0 ∉ ig⌝ ∗ (∃ a l1' b l2', ⌜l1 = a +:: l1'⌝ ∗ ⌜l2 = b +:: l2'⌝ ∗
      R.(hfr_rel) E L i0 _ a b (relate_hlist E L ig Xs l1' l2' (S i0) R T))
    ⊢ relate_hlist E L ig (X :: Xs) l1 l2 i0 R T.
  Proof.
    iIntros "(%Hnel & %a & %l1' & %b & %l2' & -> & -> & HR)".
    rewrite /relate_hlist. iPoseProof (hfr_elim R) as "Hx". destruct hfr_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iMod ("Hx" with "[//] CTX HE HL HR") as "(HR & HL & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & $)".
      iModIntro. iIntros "%Hinv %". iSpecialize ("Ha" with "[] [//]").
      { simpl in Hinv. iPureIntro. lia. }
      simpl.
      rewrite decide_False; last done. iFrame.
      iApply (big_sepL_mono with "Ha").
      iIntros. rewrite Nat.add_succ_r//.
    - iPoseProof ("Hx" with "HR") as "(Ha & Hb & $)".
      iIntros "%Hinv %". iSpecialize ("Hb" with "[] [//]").
      { simpl in Hinv. iPureIntro. lia. }
      simpl.
      rewrite decide_False; last done. iFrame.
      iApply (big_sepL_mono with "Hb").
      iIntros. rewrite Nat.add_succ_r//.
  Qed.
  Global Instance relate_hlist_cons_l_inst {A} {G H} E L ig (X : A) (Xs : list A) (l1 : hlist G (X::Xs)) (l2 : hlist H (X :: Xs)) i0 R :
    RelateHList E L ig (X :: Xs) (l1) l2 i0 R :=
    λ T, i2p (relate_hlist_cons E L ig X Xs l1 l2 i0 R T).

  (* TODO more instances similar to the ones for relate_list *)
End relate_hlist.

(*
Section relate_hplist.
  Context `{!typeGS Σ}.

  Definition relate_hplist {A} {G : A → Type} (E : elctx) (L : llctx) (ig : list nat) (Xs : list A) (l1 : hlist G Xs) (l2 : plist G Xs) (i0 : nat) (R : @HetFoldableRelation A G) (T : iProp Σ) : iProp Σ :=
    if R.(hfr_elim_mode) then
      (∀ F, ⌜lftE ⊆ F⌝ -∗ rrust_ctx -∗ elctx_interp E -∗ llctx_interp L ={F}=∗
      (⌜i0 + length Xs ≤ R.(hfr_cap)⌝ -∗ ⌜R.(hfr_inv)⌝ -∗
      [∗ list] i ↦ p ∈ hzipl2 _ l1 l2, let '(existT _ (a, b)) := (p : (sigT (λ x : A, G x * G x)%type))  in
        if decide ((i + i0)%nat ∈ ig) then True else
        R.(hfr_core_rel) E L (i + i0)%nat _ a b) ∗ llctx_interp L ∗ T)%I
    else ((⌜i0 + length Xs ≤ R.(hfr_cap)⌝ -∗ ⌜R.(hfr_inv)⌝ -∗
      [∗ list] i ↦ p ∈ hzipl2 _ l1 l2, let '(existT _ (a, b)) := p in
        if decide ((i + i0)%nat ∈ ig) then True else R.(hfr_core_rel) E L (i + i0)%nat _ a b) ∗ T)%I
  .
  Class RelateHList {A} {G : A → Type} (E : elctx) (L : llctx) (ig : list nat) (Xs : list A) (l1 : hlist G Xs) (l2 : hlist G Xs) (i0 : nat) (R : @HetFoldableRelation A G) : Type :=
    relate_hlist_proof T : iProp_to_Prop (relate_hlist E L ig Xs l1 l2 i0 R T).

  Lemma relate_hlist_nil {A} {G : A → Type} E L ig (l1 : hlist G []) (l2 : hlist G []) i0 R T :
    T -∗
    relate_hlist E L ig [] l1 l2 i0 R T.
  Proof.
    iIntros "HT". rewrite /relate_hlist. destruct hfr_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iFrame. iIntros "!> _ _". inv_hlist l1; inv_hlist l2. done.
    - iFrame. iIntros (??). inv_hlist l1; inv_hlist l2; done.
  Qed.
  Global Instance relate_hlist_nil_inst {A} {G : A → Type} E L ig (l1 : hlist G []) (l2 : hlist G []) i0 R :
    RelateHList E L ig [] (l1) l2 i0 R :=
    λ T, i2p (relate_hlist_nil E L ig l1 l2 i0 R T).

  Lemma relate_hlist_cons {A} {G : A → Type} E L ig (X : A) (Xs : list A) (l1 : hlist G (X :: Xs)) (l2 : hlist G (X :: Xs)) i0 R T :
    ⌜i0 ∉ ig⌝ ∗ (∃ a l1' b l2', ⌜l1 = a +:: l1'⌝ ∗ ⌜l2 = b +:: l2'⌝ ∗
      R.(hfr_rel) E L i0 _ a b (relate_hlist E L ig Xs l1' l2' (S i0) R T)) -∗
    relate_hlist E L ig (X :: Xs) l1 l2 i0 R T.
  Proof.
    iIntros "(%Hnel & %a & %l1' & %b & %l2' & -> & -> & HR)".
    rewrite /relate_hlist. iPoseProof (hfr_elim R) as "Hx". destruct hfr_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iMod ("Hx" with "[//] CTX HE HL HR") as "(HR & HL & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & $)".
      iModIntro. iIntros "%Hinv %". iSpecialize ("Ha" with "[] [//]").
      { simpl in Hinv. iPureIntro. lia. }
      simpl.
      rewrite decide_False; last done. iFrame.
      iApply (big_sepL_mono with "Ha").
      iIntros. rewrite Nat.add_succ_r//.
    - iPoseProof ("Hx" with "HR") as "(Ha & Hb & $)".
      iIntros "%Hinv %". iSpecialize ("Hb" with "[] [//]").
      { simpl in Hinv. iPureIntro. lia. }
      simpl.
      rewrite decide_False; last done. iFrame.
      iApply (big_sepL_mono with "Hb").
      iIntros. rewrite Nat.add_succ_r//.
  Qed.
  Global Instance relate_hlist_cons_l_inst {A} {G} E L ig (X : A) (Xs : list A) (l1 : hlist G (X::Xs)) (l2 : hlist G (X :: Xs)) i0 R :
    RelateHList E L ig (X :: Xs) (l1) l2 i0 R :=
    λ T, i2p (relate_hlist_cons E L ig X Xs l1 l2 i0 R T).

  (* TODO more instances similar to the ones for relate_list *)
End relate_hlist.
*)

Section fold_list.
  Context `{!typeGS Σ}.
  (** A generalization of subsume_list. *)
  Record FoldablePredicate {A} : Type := FP {
    fp_pred : elctx → llctx → nat → A → iProp Σ → iProp Σ;
    fp_cap : nat;
    fp_inv : Prop;
    fp_elim_mode : bool;
    fp_core_pred : elctx → llctx → nat → A → iProp Σ;
    fp_elim E L i a :
      ⊢ if fp_elim_mode then (∀ T F, ⌜lftE ⊆ F⌝ -∗ rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ fp_pred E L i a T ={F}=∗ fp_core_pred E L i a ∗ llctx_interp L ∗ T) else ∀ T, fp_pred E L i a T -∗ fp_core_pred E L i a ∗ T;
  }.
  Arguments fp_pred {_}.
  Arguments fp_core_pred {_}.
  Arguments fp_elim_mode {_}.

  Definition fold_list {A} (E : elctx) (L : llctx) (ig : list nat) (l : list A) (i0 : nat) (R : FoldablePredicate) (T : iProp Σ) : iProp Σ :=
    if R.(fp_elim_mode) then
      (∀ F, ⌜lftE ⊆ F⌝ -∗ rrust_ctx -∗ elctx_interp E -∗ llctx_interp L ={F}=∗
        (⌜i0 + length l ≤ R.(fp_cap)⌝ -∗ ⌜R.(fp_inv)⌝ -∗ [∗ list] i ↦ a ∈ l, if decide ((i + i0)%nat ∈ ig) then True else R.(fp_core_pred) E L (i + i0)%nat a) ∗ llctx_interp L ∗ T)%I
    else ((⌜i0 + length l ≤ R.(fp_cap)⌝ -∗ ⌜R.(fp_inv)⌝ -∗ [∗ list] i ↦ a ∈ l, if decide ((i + i0)%nat ∈ ig) then True else R.(fp_core_pred) E L (i + i0)%nat a) ∗ T)%I.
  Class FoldList {A} (E : elctx) (L : llctx) (ig : list nat) (l : list A) (i0 : nat) (R : FoldablePredicate) : Type :=
    fold_list_proof T : iProp_to_Prop (fold_list E L ig l i0 R T).

  Lemma fold_list_ig_cons_le {A} E L ig (j i0 : nat) (l1 : list A) (R : FoldablePredicate) :
    (j < i0)%nat →
    ([∗ list] i ↦ a ∈ l1, if decide (i + i0 ∈ (j :: ig))%nat then True else fp_core_pred R E L (i + i0)%nat a) -∗
    ([∗ list] i ↦ a ∈ l1, if decide (i + i0 ∈ (ig))%nat then True else fp_core_pred R E L (i + i0)%nat a).
  Proof.
    intros Hlt.
    iInduction l1 as [ | a l1] "IH" forall (j i0 Hlt); simpl; first by eauto.
    case_decide as Hel.
    - apply elem_of_cons in Hel as [ ? | ?]; first lia.
      rewrite decide_True; last done. rewrite !left_id.
      iIntros "Ha". iApply (big_sepL_mono); first last.
      { iApply ("IH" $! _ (S i0)); first last.
        { iApply big_sepL_mono; last done. iIntros. rewrite Nat.add_succ_r//. }
        iPureIntro. lia. }
      iIntros. rewrite Nat.add_succ_r//.
    - apply not_elem_of_cons in Hel as [_ Hel].
      rewrite decide_False; last done.
      iIntros "($ & Ha)". iApply (big_sepL_mono); first last.
      { iApply ("IH" $! _ (S i0)); first last.
        { iApply big_sepL_mono; last done. iIntros. rewrite Nat.add_succ_r//. }
        iPureIntro. lia. }
      iIntros. rewrite Nat.add_succ_r//.
  Qed.

  Lemma fold_list_replicate_elim_full {A} E L ig n (a : A) i0 (R : FoldablePredicate) T :
    R.(fp_elim_mode) = true →
    (rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗ ⌜R.(fp_inv)⌝ -∗ □ ∀ i, ⌜(i < R.(fp_cap))%nat⌝ -∗ R.(fp_core_pred) E L i a) -∗
    T -∗ fold_list E L ig (replicate n a) i0 R T.
  Proof.
    rewrite /fold_list. iIntros (->) "HR HT". iIntros (F ?) "#CTX #HE HL".
    iPoseProof ("HR" with "CTX HE HL") as "#HR".
    iFrame "HT HL".
    iModIntro. iIntros "%Hinv %Hinv'". iSpecialize ("HR" with "[//]").
    iInduction n as [ | n] "IH" forall (i0 Hinv); simpl.
    { by iFrame. }
    iPoseProof ("IH" $! (S i0) with "[]") as "Ha".
    { simpl in Hinv. iPureIntro. lia. }
    case_decide.
    - iR.
      iApply (big_sepL_wand with "Ha").
      iApply big_sepL_intro.
      iModIntro. iIntros (???). rewrite Nat.add_succ_r. eauto.
    - iFrame. iSplitR. { iApply "HR". simpl in Hinv. iPureIntro. lia. }
      iApply (big_sepL_mono with "Ha").
      iIntros (???). rewrite Nat.add_succ_r. done.
  Qed.

  Lemma fold_list_replicate_elim_weak {A} E L ig n (a : A) i0 (R : FoldablePredicate) T :
    R.(fp_elim_mode) = false →
    (⌜R.(fp_inv)⌝ -∗ □ ∀ i, ⌜(i < R.(fp_cap))%nat⌝ -∗ R.(fp_core_pred) E L i a) -∗
    T -∗ fold_list E L ig (replicate n a) i0 R T.
  Proof.
    rewrite /fold_list. iIntros (->) "HR $".
    iIntros "%Hinv %Hinv'". iSpecialize ("HR" with "[//]").
    iDestruct "HR" as "#HR".
    iInduction n as [ | n] "IH" forall (i0 Hinv); simpl.
    { by iFrame. }
    iPoseProof ("IH" $! (S i0) with "[]") as "Ha".
    { simpl in Hinv. iPureIntro. lia. }
    case_decide.
    - iR.
      iApply (big_sepL_wand with "Ha").
      iApply big_sepL_intro.
      iModIntro. iIntros (???). rewrite Nat.add_succ_r. eauto.
    - iFrame. iSplitR. { iApply "HR". simpl in Hinv. iPureIntro. lia. }
      iApply (big_sepL_mono with "Ha").
      iIntros (???). rewrite Nat.add_succ_r. done.
  Qed.

  Local Lemma fold_list_insert_in_ig' {A} E L (ig : list nat) (l1 : list A) (i0 : nat) i x R :
    (i0 + i ∈ ig)%nat →
    (⌜i0 + length l1 ≤ fp_cap R⌝ -∗ ⌜fp_inv R⌝ -∗ [∗ list] i1↦a ∈ l1, if decide ((i1 + i0)%nat ∈ ig) then True else fp_core_pred R E L (i1 + i0) a) -∗
    (⌜i0 + length (<[i:=x]> l1) ≤ fp_cap R⌝ -∗ ⌜fp_inv R⌝ -∗ [∗ list] i1↦a ∈ <[i:=x]> l1, if decide ((i1 + i0)%nat ∈ ig) then True else fp_core_pred R E L (i1 + i0) a).
  Proof.
    iIntros (Hel) "Ha". iIntros "%Hinv %". iSpecialize ("Ha" with "[] [//]").
    { rewrite length_insert in Hinv. done. }
    iInduction l1 as [ | a l1] "IH" forall (i i0 Hel Hinv); simpl; first done.
    destruct i as [ | i].
    - simpl.
      case_decide; first done.
      rewrite Nat.add_0_r in Hel. done.
    - simpl.
      case_decide.
      + iDestruct "Ha" as "(_ & Ha)". iR.
        iPoseProof ("IH" $! _ (S i0) with "[] [] [Ha]") as "Hi"; first last.
        { iApply (big_sepL_mono); last iApply "Hi". iIntros. rewrite -Nat.add_succ_r//. }
        { iApply (big_sepL_mono with "Ha"). iIntros. rewrite -Nat.add_succ_r//. }
        { simpl in Hinv. iPureIntro. lia. }
        { iPureIntro. move: Hel. rewrite Nat.add_succ_r//. }
      + iDestruct "Ha" as "($ & Ha)".
        iPoseProof ("IH" $! _ (S i0) with "[] [] [Ha]") as "Hi"; first last.
        { iApply (big_sepL_mono); last iApply "Hi". iIntros. rewrite -Nat.add_succ_r//. }
        { iApply (big_sepL_mono with "Ha"). iIntros. rewrite -Nat.add_succ_r//. }
        { simpl in Hinv. iPureIntro. lia. }
        { iPureIntro. move: Hel. rewrite Nat.add_succ_r//. }
  Qed.

  Lemma fold_list_insert_in_ig {A} E L ig (l1 : list A) (i0 : nat) i x R T `{CanSolve (i0 + i ∈ ig)%nat} :
    fold_list E L ig l1 i0 R T
    ⊢ fold_list E L ig (<[i := x]> l1) i0 R T.
  Proof.
    match goal with H : CanSolve _ |- _ => unfold CanSolve in H; rename H into Hel end.
    rewrite /fold_list. destruct fp_elim_mode.
    - iIntros "HP" (??) "#CTX #HE HL".
      iMod ("HP" with "[//] CTX HE HL") as "(Ha & $ & $)".
      iModIntro. by iApply fold_list_insert_in_ig'.
    - iIntros "(HP & $)". by iApply fold_list_insert_in_ig'.
  Qed.
  Global Instance fold_list_insert_in_ig_inst {A} E L ig (l1 : list A) (i0 : nat) i x R `{!CanSolve (i0 + i ∈ ig)%nat} :
    FoldList E L ig (<[i := x]> l1) i0 R :=
    λ T, i2p (fold_list_insert_in_ig E L ig l1 i0 i x R T).

  Lemma fold_list_cons {A} E L ig (l1 : list A) i0 R a T :
    ⌜i0 ∉ ig⌝ ∗ (R.(fp_pred) E L i0 a (fold_list E L ig l1 (S i0) R T))
    ⊢ fold_list E L ig (a :: l1) i0 R T.
  Proof.
    iIntros "(%Hnel & HR)". rewrite /fold_list.
    iPoseProof (fp_elim R) as "Hx". destruct fp_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iMod ("Hx" with "[//] CTX HE HL HR") as "(HR & HL & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Ha & $ & $)".
      iModIntro. iIntros "%Hinv %". iSpecialize ("Ha" with "[] [//]").
      { simpl in Hinv. iPureIntro. lia. }
      rewrite big_sepL_cons. simpl.
      rewrite decide_False; last done. iFrame.
      iApply (big_sepL_mono with "Ha").
      iIntros. rewrite Nat.add_succ_r//.
    - iPoseProof ("Hx" with "HR") as "(HR & HT)".
      iPoseProof ("HT") as "(Ha & $)".
      iIntros "%Hinv %". iSpecialize ("Ha" with "[] [//]").
      { simpl in Hinv. iPureIntro. lia. }
      rewrite big_sepL_cons. simpl.
      rewrite decide_False; last done. iFrame.
      iApply (big_sepL_mono with "Ha").
      iIntros. rewrite Nat.add_succ_r//.
  Qed.
  Global Instance fold_list_cons_inst {A} E L ig (l1 : list A) i0 a R :
    FoldList E L ig (a :: l1) i0 R := λ T, i2p (fold_list_cons E L ig l1 i0 R a T).

  Lemma fold_list_nil {A} E L ig i0 R T :
    T ⊢ fold_list E L ig ([] : list A) i0 R T.
  Proof.
    iIntros "HT". rewrite /fold_list.
    destruct fp_elim_mode.
    - iIntros (??) "#CTX #HE $". iModIntro. iFrame.
      iIntros "_ _". by iApply big_sepL_nil.
    - iFrame. iIntros "_ _". by iApply big_sepL_nil.
  Qed.
  Global Instance fold_list_nil_inst {A} E L ig i0 R :
    FoldList E L ig ([] : list A) i0 R := λ T, i2p (fold_list_nil E L ig i0 R T).

  Local Lemma fold_list_insert_not_in_ig' {A} E L ig (l1 : list A) (R : FoldablePredicate) i0 i a :
    (i0 + i ∉ ig)%nat →
    i < length l1 →
    fp_core_pred R E L (i0 + i) a -∗
    (⌜i0 + length l1 ≤ fp_cap R⌝ -∗ ⌜fp_inv R⌝ -∗ [∗ list] i1↦a0 ∈ l1, if decide ((i1 + i0)%nat ∈ (i0 + i)%nat :: ig) then True else fp_core_pred R E L (i1 + i0) a0) -∗
    (⌜i0 + length (<[i:=a]> l1) ≤ fp_cap R⌝ -∗ ⌜fp_inv R⌝ -∗ [∗ list] i1↦a0 ∈ <[i:=a]> l1, if decide ((i1 + i0)%nat ∈ ig) then True else fp_core_pred R E L (i1 + i0) a0).
  Proof.
    iIntros (Hnel Hi) "HR Ha".
    iIntros "%Hinv %". iSpecialize ("Ha" with "[] [//]").
    { iPureIntro. rewrite length_insert in Hinv. lia. }
    iInduction l1 as [ | a' l1] "IH" forall (i i0 Hnel Hi Hinv).
    { simpl in *. lia. }
    destruct i as [ | i]; simpl.
    - iDestruct "Ha" as "(_ & Ha)".
      rewrite decide_False; first last. { move: Hnel. rewrite Nat.add_0_r//. }
      rewrite Nat.add_0_r. iFrame.
      iApply big_sepL_mono; first last.
      { iApply (fold_list_ig_cons_le); first last.
        { iApply big_sepL_mono; last done. iIntros. rewrite -Nat.add_succ_r//. }
        lia.
      }
      iIntros. rewrite Nat.add_succ_r//.
    - destruct (decide (i0 ∈ ig)).
      + iR. iDestruct "Ha" as "(_ & Ha)".
        iApply big_sepL_mono; first last.
        { iApply ("IH" with "[] [] [] [HR] [Ha]"); first last.
          - iApply big_sepL_mono; last done. iIntros. rewrite -(Nat.add_succ_r _ i0) (Nat.add_succ_r _ i) //.
          - rewrite Nat.add_succ_r. done.
          - iPureIntro. simpl in Hinv. lia.
          - simpl in *; iPureIntro. lia.
          - iPureIntro. move: Hnel. rewrite Nat.add_succ_r. done.
        }
        iIntros. rewrite Nat.add_succ_r//.
      + rewrite decide_False; first last. { apply not_elem_of_cons. split; last done. lia. }
        iDestruct "Ha" as "($ & Ha)".
        iApply big_sepL_mono; first last.
        { iApply ("IH" with "[] [] [] [HR]"); first last.
          - iApply big_sepL_mono; last done. iIntros. rewrite -(Nat.add_succ_r _ i0) (Nat.add_succ_r _ i) //.
          - rewrite Nat.add_succ_r. done.
          - iPureIntro. simpl in Hinv. lia.
          - simpl in *; iPureIntro. lia.
          - iPureIntro. move: Hnel. rewrite Nat.add_succ_r. done.
        }
        iIntros. rewrite Nat.add_succ_r//.
  Qed.
  Lemma fold_list_insert_not_in_ig {A} E L ig (l1 : list A) (R : FoldablePredicate) i0 i a T `{CanSolve (i0 + i ∉ ig)%nat} :
    ⌜i < length l1⌝ ∗
    (R.(fp_pred) E L (i0 + i) a (fold_list E L ((i0 + i) :: ig)%nat l1 i0 R T))
    ⊢ fold_list E L ig (<[i := a]> l1) i0 R T.
  Proof.
    match goal with H : CanSolve _ |- _ => rewrite /CanSolve in H; rename H into Hnel end.
    iIntros "(%Hi & HR)". rewrite /fold_list.
    iPoseProof (fp_elim R) as "Hx". destruct fp_elim_mode.
    - iIntros (??) "#CTX #HE HL".
      iMod ("Hx" with "[//] CTX HE HL HR") as "(HR & HL & HT)".
      iMod ("HT" with "[//] CTX HE HL ") as "(Ha & $ & $)".
      iModIntro. by iApply (fold_list_insert_not_in_ig' with "HR Ha").
    - iPoseProof ("Hx" with "HR") as "(HR & Ha & $)".
      by iApply (fold_list_insert_not_in_ig' with "HR Ha").
  Qed.
  Global Instance fold_list_insert_not_in_ig_inst {A} E L ig (l1 : list A) R (i0 : nat) i a `{!CanSolve (i0 + i ∉ ig)%nat} :
    FoldList E L ig (<[i := a]> l1) i0 R :=
    λ T, i2p (fold_list_insert_not_in_ig E L ig l1 R i0 i a T).

  Lemma fold_list_app {A} E L ig (l1 l1' : list A) (R : FoldablePredicate) (i0 : nat) T :
    fold_list E L ig l1 i0 R (fold_list E L ig l1' (length l1 + i0)%nat R T)
    ⊢ fold_list E L ig (l1 ++ l1') i0 R T.
  Proof.
    rewrite /fold_list. destruct fp_elim_mode.
    - iIntros "Ha" (??) "#CTX #HE HL".
      iMod ("Ha" with "[//] CTX HE HL") as "(Ha & HL & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Hb & $ & $)".
      iModIntro. iIntros "%Hinv %". rewrite length_app in Hinv.
      iSpecialize ("Ha" with "[] [//]"). { iPureIntro. lia. }
      iSpecialize ("Hb" with "[] [//]"). { iPureIntro. lia. }
      rewrite big_sepL_app. iFrame.
      iApply (big_sepL_mono with "Hb").
      iIntros. rewrite Nat.add_assoc [(k + _)%nat]Nat.add_comm//.
    - iIntros "(Ha & Hb & $)".
      iIntros "%Hinv %". rewrite length_app in Hinv.
      iSpecialize ("Ha" with "[] [//]"). { iPureIntro. lia. }
      iSpecialize ("Hb" with "[] [//]"). { iPureIntro. lia. }
      rewrite big_sepL_app. iFrame.
      iApply (big_sepL_mono with "Hb").
      iIntros. rewrite Nat.add_assoc [(k + _)%nat]Nat.add_comm//.
  Qed.
  Global Instance fold_list_app_inst {A} E L ig (l1 l1' : list A) R i0 :
    FoldList E L ig (l1 ++ l1') i0 R :=
    λ T, i2p (fold_list_app E L ig l1 l1' R i0 T).
End fold_list.

From lithium Require Import hooks.
Ltac generate_i2p_instance_to_tc_hook arg c ::=
  lazymatch c with
  | typed_value ?π ?x => constr:(TypedValue π x)
  | typed_bin_op ?E ?L ?f ?v1 ?P1 ?v2 ?P2 ?o ?ot1 ?ot2 => constr:(TypedBinOp E L f v1 P1 v2 P2 o ot1 ot2)
  | typed_un_op ?E ?L ?f ?v ?P ?o ?ot => constr:(TypedUnOp E L f v P o ot)
  | typed_check_bin_op ?E ?L ?f ?v1 ?P1 ?v2 ?P2 ?o ?ot1 ?ot2 => constr:(TypedCheckBinOp E L f v1 P1 v2 P2 o ot1 ot2)
  | typed_check_un_op ?E ?L ?f ?v ?P ?o ?ot => constr:(TypedCheckUnOp E L f v P o ot)
  | typed_cas ?E ?L ?f ?v1 ?P1 ?v2 ?P2 ?v3 ?P3 ?ot => constr:(TypedCas E L f v1 P1 v2 P2 v3 P3 ot)
  | typed_atomic_rmw ?E ?L ?f ?v1 ?P1 ?v2 ?P2 ?op ?ot => constr:(TypedAtomicRmw E L f v1 P1 v2 P2 op ot)
  | typed_switch ?E ?L ?f ?v ?ty ?r ?it => constr:(TypedSwitch E L f v ty r it)
  | typed_call ?E ?L ?f ?κs ?etys ?v ?P ?vs ?tys => constr:(TypedCall E L f κs etys v P vs tys)
  | typed_place ?E ?L ?f ?l ?lto ?ro ?b1 ?b2 ?K => constr:(TypedPlace E L f l lto ro b1 b2 K)
  | typed_read_end ?π ?E ?L ?l ?lt ?r ?b1 ?b2 ?ot ?m => constr:(TypedReadEnd π E L l lt r b1 b2 ot m)
  | typed_write_end ?π ?E ?L ?ot ?v ?ty1 ?r1 ?b1 ?b2 ?l ?lt2 ?r2 => constr:(TypedWriteEnd π E L ot v ty1 r1 b1 b2 l lt2 r2)
  | typed_borrow_mut_end ?π ?E ?L ?κ ?l ?orty ?lt ?r ?b1 ?b2 =>
    constr:(TypedBorrowMutEnd π E L κ l orty lt r b1 b2)
  | typed_borrow_shr_end ?π ?E ?L ?κ ?l ?orty ?lt ?r ?b1 ?b2 =>
    constr:(TypedBorrowShrEnd π E L κ l orty lt r b1 b2)
  | typed_addr_of_mut_end ?π ?E ?L ?l ?lt ?r ?b1 ?b2 => constr:(TypedAddrOfMutEnd π E L l lt r b1 b2)
  | typed_annot_expr ?E ?L ?f ?n ?a ?v ?P => constr:(TypedAnnotExpr E L f n a v P)
  | typed_if ?E ?L ?v ?P => constr:(TypedIf E L v P)
  | typed_assert ?E ?L ?f ?v ?ty ?r  => constr:(TypedAssert E L f v ty r)
  | typed_switch ?E ?L ?f ?v ?ty ?r ?it => constr:(TypedSwitch E L f v ty r it)
  | typed_annot_stmt ?a => constr:(TypedAnnotStmt a)
  | introduce_with_hooks ?E ?L ?P => constr:(IntroduceWithHooks E L P)
  | iterate_with_hooks ?E ?L ?m => constr:(IterateWithHooks E L m)
  | subsume_full ?E ?L ?wl ?P1 ?P2 => constr:(SubsumeFull E L wl P1 P2)
  | resolve_ghost ?π ?E ?L ?rm ?f ?l ?lt ?k ?r => constr:(ResolveGhost π E L rm f l lt k r)
  | resolve_ghost_adt ?π ?E ?L ?rm ?r ?ty => constr:(ResolveGhostADT π E L rm r ty)
  | resolve_ghost_iter ?π ?E ?L ?rm ?b ?l ?st ?ltys ?bk ?rs ?ig ?i => constr:(ResolveGhostIter π E L rm b l st ltys bk rs ig i)
  | prove_place_cond ?E ?L ?bk ?lt1 ?lt2 => constr:(ProvePlaceCond E L bk lt1 lt2)
  | prove_with_subtype ?E ?L ?wl ?pm ?P => constr:(ProveWithSubtype E L wl pm P)
  | weak_subtype ?E ?L ?r1 ?r2 ?ty1 ?ty2 => constr:(Subtype E L r1 r2 ty1 ty2)
  | mut_subtype ?E ?L ?ty1 ?ty2 => constr:(MutSubtype E L ty1 ty2)
  | mut_eqtype ?E ?L ?ty1 ?ty2 => constr:(MutEqtype E L ty1 ty2)
  | subtype_adt ?E ?L ?P1 ?P2 => constr:(SubtypeADT E L P1 P2)
  | owned_subtype ?π ?E ?L ?wl ?r1 ?r2 ?ty1 ?ty2 => constr:(OwnedSubtype π E L wl r1 r2 ty1 ty2)
  | weak_subltype ?E ?L ?k ?r1 ?r2 ?lt1 ?lt2 => constr:(SubLtype E L k r1 r2 lt1 lt2)
  | mut_subltype ?E ?L ?lt1 ?lt2 => constr:(MutSubLtype E L lt1 lt2)
  | mut_eqltype ?E ?L ?lt1 ?lt2 => constr:(MutEqLtype E L lt1 lt2)
  | owned_subltype_step ?π ?E ?L ?l ?r1 ?r2 ?lt1 ?lt2 => constr:(OwnedSubltypeStep π E L l r1 r2 lt1 lt2)
  | cast_ltype_to_type ?E ?L ?lt => constr:(CastLtypeToType E L lt)
  | typed_array_access ?π ?E ?L ?base ?off ?st ?lt ?r ?bk => constr:(TypedArrayAccess π E L base off st lt r bk)
  | find_observation ?rt ?γ ?m => constr:(FindObservation rt γ m)
  | find_delayed_observation ?E ?L ?rt ?γ ?m ?κ => constr:(FindDelayedObservation E L rt γ m κ)
  | stratify_ltype ?π ?E ?L ?mu ?mdu ?ma ?m ?l ?lt ?r ?b =>
      constr:(StratifyLtype π E L mu mdu ma m l lt r b)
  | stratify_ltype_post_hook ?π ?E ?L ?m ?l ?lt ?r ?b =>
      constr:(StratifyLtypePostHook π E L m l lt r b)
  | stratify_ltype_array_iter ?π ?E ?L ?mu ?mdu ?ma ?m ?l ?ig ?def ?len ?iml ?rs ?b =>
      constr:(StratifyLtypeArrayIter π E L mu mdu ma m l ig def len iml rs b)
  | interpret_typing_hint ?E ?L ?orty ?bmin ?ty ?r =>
      constr:(InterpretTypingHint E L orty bmin ty r)
  | typed_context_fold ?P ?E ?L ?m ?tctx ?acc =>
      constr:(TypedContextFold P E L m tctx acc)
  | typed_pre_context_fold ?π ?E ?L ?m =>
      constr:(TypedPreContextFold π E L m)
  | typed_context_fold_step ?P ?π ?E ?L ?m ?l ?lt ?r ?ls ?acc =>
      constr:(TypedContextFoldStep P π E L m l lt r ls acc)
  | relate_list ?E ?L ?idx ?a ?b ?n ?R =>
      constr:(RelateList E L idx a b n R)
  | fold_list ?E ?L ?idx ?a ?n ?R =>
      constr:(FoldList E L idx a n R)
  | _ => fail "unknown judgement" c
  end.


Declare Scope rr_hidden.

Notation "'typed_value' π x 'HIDDEN_CONT'" := (typed_value π x _) (only printing): rr_hidden.
Notation "'typed_place' E L f l lto ro b1 b2 K 'HIDDEN_CONT'" := (typed_place E L f l lto ro b1 b2 K _) (only printing): rr_hidden.

Notation "'subsume_full' E L wl P1 P2 'HIDDEN_CONT'" := (subsume_full E L wl P1 P2 _) (only printing): rr_hidden.
Notation "'resolve_ghost' π E L rm f l lt k r 'HIDDEN_CONT'" := (resolve_ghost π E L rm f l lt k r _) (only printing): rr_hidden.
Notation "'prove_with_subtype' E L wl pm P 'HIDDEN_CONT'" := (prove_with_subtype E L wl pm P _) (only printing): rr_hidden.
Notation "'introduce_with_hooks' E L P 'HIDDEN_CONT'" := (introduce_with_hooks E L P _) (only printing): rr_hidden.
Notation "'stratify_ltype' π E L mu mdu ma m l lt r b 'HIDDEN_CONT'" := (stratify_ltype π E L mu mdu ma m l lt r b _) (only printing): rr_hidden.


Notation "'typed_context_fold_step' step π E L m l lt r ls 'HIDDEN_ACC' 'HIDDEN_CONT'" := (typed_context_fold_step step π E L m l lt r ls _ _) (only printing) : rr_hidden.
Notation "'typed_context_fold' step E L m ls 'HIDDEN_ACC' 'HIDDEN_CONT'" := (typed_context_fold step E L m ls _ _) (only printing) : rr_hidden.
Notation "'weak_subltype' E L b r1 r2 lt1 lt2 'HIDDEN_CONT'" := (weak_subltype E L b r1 r2 lt1 lt2 _) (only printing) : rr_hidden.

Notation "'typed_block' 'HIDDEN_INV' f l rf R ϝ" := (typed_block _ f l rf R ϝ) (only printing, at level 100) : rr_hidden.

Global Open Scope rr_hidden.
