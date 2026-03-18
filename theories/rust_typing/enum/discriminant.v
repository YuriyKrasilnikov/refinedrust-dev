From refinedrust Require Export type ltypes.
From refinedrust Require Import uninit int int_rules.
From refinedrust Require Import struct.def struct.subtype programs.
From refinedrust.enum Require Import def.
From refinedrust Require Import options.

Section discriminant.
  Context `{!typeGS Σ}.

  Program Definition enum_discriminant_t {rt} (en : enum rt) : type rt := {|
    st_own π r v :=
      ∃ tag, ⌜en.(enum_tag) r = Some tag⌝ ∗
      v ◁ᵥ{π, MetaNone} (els_lookup_tag en.(enum_els) tag) @ int en.(enum_els).(els_tag_it);
    st_has_op_type ot mt := is_int_ot ot en.(enum_els).(els_tag_it);
    st_syn_type := IntSynType en.(enum_els).(els_tag_it);
  |}%I.
  Next Obligation.
    intros. apply populate. apply (enum_xt_inhabited en).
  Qed.
  Next Obligation.
    simpl. intros.
    iIntros "(%tag & %Htag & Hv)".
    iApply (ty_has_layout with "Hv").
  Qed.
  Next Obligation.
    simpl. intros. eapply (@ty_op_type_stable _ _ _ (int _) _ mt).
    rewrite ty_has_op_type_unfold. done.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    simpl. intros ???????? Hv. iIntros "(%tag & %Htag & Hv)".
    iPoseProof (ty_memcast_compat _ _ _ mt with "Hv") as "Ha".
    { rewrite ty_has_op_type_unfold. apply Hv. }
    destruct mt; eauto.
  Qed.
Next Obligation.
    intros ?? mt ly Hst.
    apply syn_type_has_layout_int_inv in Hst as ->.
    done.
  Qed.

  Definition typed_discriminant_end_cont_t : Type :=
    llctx → val → ∀ (rt : RT), type rt → rt → iProp Σ.
  Definition typed_discriminant_end (π : thread_id) (E : elctx) (L : llctx) (l : loc) {rt: RT} (lt : ltype rt) (r : place_rfn rt) (b2 : bor_kind) (els : enum_layout_spec) (T : typed_discriminant_end_cont_t) :=
    (∀ F, ⌜lftE ⊆ F⌝ → ⌜↑rrustN ⊆ F⌝ → ⌜lft_userE ⊆ F⌝ → ⌜shrE ⊆ F⌝ →
    rrust_ctx -∗ elctx_interp E -∗ llctx_interp L -∗
      (* given ownership of the read location *)
      l ◁ₗ[π, b2] r @ lt ={F}=∗
      ∃ q v discr,
        ⌜GetEnumDiscriminantLocSt l els `has_layout_loc` els.(els_tag_it)⌝ ∗
        ⌜v `has_layout_val` els.(els_tag_it)⌝ ∗
        (GetEnumDiscriminantLocSt l els) ↦{q} v ∗
        ▷ v ◁ᵥ{π, MetaNone} discr @ (int els.(els_tag_it)) ∗
        (* prove the continuation after the client is done *)
        logical_step F (
          (* assuming that the client provides the ownership back... *)
          (GetEnumDiscriminantLocSt l els) ↦{q} v ={F}=∗
          ∃ (L' : llctx) (rt3 : RT) (ty3 : type rt3) (r3 : rt3),
            v ◁ᵥ{ π, MetaNone} r3 @ ty3 ∗
            llctx_interp L' ∗
            l ◁ₗ[π, b2] r @ lt ∗
            T L' v rt3 ty3 r3))%I.
  Class TypedDiscriminantEnd (π : thread_id) (E : elctx) (L : llctx) (l : loc) {rt} (lt : ltype rt) (r : place_rfn rt) (b2 : bor_kind) (els : enum_layout_spec) : Type :=
    typed_discriminant_end_proof T : iProp_to_Prop (typed_discriminant_end π E L l lt r b2 els T).

  Lemma typed_discriminant_end_enum_ltype π E L l {rt rte} (en : enum rt) tag (lte : ltype rte) (re : rte) r b2 els (T : typed_discriminant_end_cont_t) :
    typed_discriminant_end π E L l (EnumLtype en tag lte re) (#r) b2 els T :-
    exhale (⌜en.(enum_els) = els⌝);
    ∀ v,
    return (T L v rt  (enum_discriminant_t en) (r)).
  Proof.
  Admitted.
  Global Instance typed_discriminant_end_enum_ltype_inst π E L l {rt rte} (en : enum rt) tag (lte : ltype rte) (re : rte) r b2 els:
    TypedDiscriminantEnd π E L l (EnumLtype en tag lte re) (#r) b2 els :=
    λ T, i2p (typed_discriminant_end_enum_ltype π E L l en tag lte re r b2 els T).

  Lemma typed_discriminant_end_enum π E L l {rt} (en : enum rt) r b2 els (T : typed_discriminant_end_cont_t) :
    typed_discriminant_end π E L l (◁ enum_t en) (#r) b2 els T :-
    exhale (⌜en.(enum_els) = els⌝);
    ∀ v,
    return (T L v rt (enum_discriminant_t en) (r)).
  Proof.
  Admitted.
  Global Instance typed_discriminant_end_enum_inst π E L l {rt} (en : enum rt) r b2 els:
    TypedDiscriminantEnd π E L l (◁ enum_t en)%I (#r) b2 els :=
    λ T, i2p (typed_discriminant_end_enum π E L l en r b2 els T).

  Lemma type_discriminant E L f e els T' (T : typed_val_expr_cont_t) :
    IntoPlaceCtx E f e T' →
    (** Decompose the expression *)
    T' L (λ L' K l,
      (** Find the type assignment *)
      find_in_context (FindLoc l) (λ '(existT rto (lt1, r1, b, π)),
      (** Check the place access *)
      typed_place E L' f l lt1 r1 UpdStrong b K (λ (L1 : llctx) (κs : list lft) (l2 : loc) (b2 : bor_kind) bmin rti (lt2 : ltype rti) (ri2 : place_rfn rti) (updcx : place_update_ctx rti rto _ _),
        (** Stratify *)
        stratify_ltype_unblock π E L1 StratRefoldOpened l2 lt2 ri2 b2 (λ L2 R rt3 lt3 ri3,
        (** Certify that this stratification is allowed, or otherwise commit to a strong update *)
        prove_place_cond E L2 bmin lt2 lt3 (λ upd,
        (** Finish reading *)
        typed_discriminant_end π E L2 l2 lt3 ri3 b2 els (λ L3 v rt3 ty3 r3,
        typed_place_finish π E L3 updcx upd (llft_elt_toks κs) l b lt3 ri3 (λ L4, T L4 v MetaNone _ (ty3) r3))
      )))))%I
    ⊢ typed_val_expr E L f (EnumDiscriminant els e)%E T.
  Proof.
    (*iIntros "[% Hread]" (Φ) "#(LFT & TIME & LLCTX) #HE HL HΦ".*)
    (*wp_bind.*)
    (*iApply ("Hread" $! _ ⊤ with "[//] [//] [//] [//] [$TIME $LFT $LLCTX] HE HL").*)
    (*iIntros (l) "Hl".*)
    (*iApply ewp_fupd.*)
    (*rewrite /Use. wp_bind.*)
    (*iApply (wp_logical_step with "TIME Hl"); [solve_ndisj.. | ].*)
    (*iMod (persistent_time_receipt_0) as "#Hp".*)
    (*iMod (additive_time_receipt_0) as "Ha".*)
    (*iApply (wp_skip_credits with "TIME Ha Hp"); first done.*)
    (*iNext. iIntros "Hcred Hat".*)
    (*iIntros "(%v & %q & %π & %rt & %ty & %r & %Hlyv & %Hv & Hl & Hv & Hcl)".*)
    (*iModIntro. iApply (wp_logical_step with "TIME Hcl"); [solve_ndisj.. | ].*)
    (*iApply (wp_deref_credits with "TIME Hat Hp Hl") => //; try by eauto using val_to_of_loc.*)
    (*{ destruct o; naive_solver. }*)
    (*iIntros "!> %st Hl Hcred2 Hat Hcl".*)
    (*iMod ("Hcl" with "Hl Hv") as "(%L' & %rt' & %ty' & %r' & HL & Hv & HT)"; iModIntro.*)
    (*iDestruct "Hcred2" as "(Hcred1' & Hcred2)".*)
    (*iMod ("HT" with "[] HE HL [$Hat $Hcred2]") as "(%L3 & HL & HT)"; first done.*)
    (*by iApply ("HΦ" with "HL Hv HT").*)
  (*Qed.*)
  Admitted.

End discriminant.

Section subtype.
  Context `{!typeGS Σ}.

  Lemma enum_discriminant_t_simplify_hyp {rt} (en : enum rt) v π r T :
    (∀ tag, ⌜enum_tag en r = Some tag⌝ -∗
      v ◁ᵥ{π, MetaNone} els_lookup_tag (enum_els en) tag @ int (els_tag_it (enum_els en)) -∗
      T)
    ⊢ simplify_hyp (v ◁ᵥ{π, MetaNone} r @ enum_discriminant_t en) T.
  Proof.
    iIntros "HT Hv".
    iEval (rewrite /ty_own_val/=) in "Hv".
    iDestruct "Hv" as "(_ & %tag & %Htag & Hv)".
    by iApply ("HT" with "[] Hv").
  Qed.
  Definition enum_discriminant_t_simplify_hyp_inst := [instance @enum_discriminant_t_simplify_hyp with 100%N].
  Global Existing Instance enum_discriminant_t_simplify_hyp_inst.

  Lemma type_incl_enum_discriminant_int {rt} (en : enum rt) r tag  :
    en.(enum_tag) r = Some tag →
    ⊢ type_incl r (els_lookup_tag (enum_els en) tag) (enum_discriminant_t en) (int (els_tag_it (enum_els en))).
  Proof.
    intros Htag.
    iApply type_incl_simple_type; simpl; last done.
    iIntros "!>" (??) "(%tag' & % & (_ & Hv))".
    simplify_eq. done.
  Qed.

  Lemma weak_subtype_enum_discriminant_int E L {rt} (en : enum rt) r i it T :
    weak_subtype E L r i (enum_discriminant_t en) (int it) T :-
      ∃ tag,
      exhale (⌜en.(enum_tag) r = Some tag⌝);
      exhale (⌜i = els_lookup_tag en.(enum_els) tag⌝);
      exhale (⌜it = en.(enum_els).(els_tag_it)⌝);
      return T.
  Proof.
    iIntros "(%tag & %Htag & -> & -> & HT)".
    iIntros (??) "#CTX HE HL".
    iFrame.
    by iApply type_incl_enum_discriminant_int.
  Qed.
  Definition weak_subtype_enum_discriminant_int_inst := [instance @weak_subtype_enum_discriminant_int].
  Global Existing Instance weak_subtype_enum_discriminant_int_inst.
End subtype.

Section ops.
  Context `{!typeGS Σ}.

  Lemma type_relop_discr_discr E L f {rt} (en : enum rt) it v1 v2 (x1 x2 : rt) op π (T : typed_val_expr_cont_t) :
    (⌜π = f.1⌝ ∗ ∀ tag1 tag2,
    ⌜en.(enum_tag) x1 = Some tag1⌝ -∗
    ⌜en.(enum_tag) x2 = Some tag2⌝ -∗
    typed_bin_op E L f v1 (v1 ◁ᵥ{π, MetaNone} (els_lookup_tag en.(enum_els) tag1) @ int en.(enum_els).(els_tag_it))%I v2 (v2 ◁ᵥ{π, MetaNone} (els_lookup_tag en.(enum_els) tag2) @ int en.(enum_els).(els_tag_it)) op (IntOp it) (IntOp it) T) ⊢
    typed_bin_op E L f v1 (v1 ◁ᵥ{π, MetaNone} x1 @ enum_discriminant_t en) v2 (v2 ◁ᵥ{π, MetaNone} x2 @ enum_discriminant_t en) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros "(-> & HT)".
    rewrite /ty_own_val/=.
    iIntros "(_ & %tag1 & % & Hv1) (_ & %tag2 & % & Hv2)".
    iApply ("HT" with "[//] [//] [$Hv1] [$Hv2]").
  Qed.
  Definition type_relop_discr_discr_inst := [instance @type_relop_discr_discr].
  Global Existing Instance type_relop_discr_discr_inst.
End ops.

Section switch.
  Context `{!typeGS Σ}.

  Inductive destruct_hint_switch_enum :=
  (* We did a case analysis *)
  | DestructHintSwitchEnumCase {rt} (r : rt) (n : string)
  (* The case was already known *)
  | DestructHintSwitchEnumKnown {rt} (r : rt) (n : string)
  .

  Lemma type_switch_enum E L f {rt} (en : enum rt) r (it : int_type) m ss def fn R ϝ v:
    ⌜it = en.(enum_els).(els_tag_it)⌝ ∗
    case_destruct r (λ c b,
      ∃ tag, ⌜enum_tag en c = Some tag⌝ ∗
        li_trace (if b then DestructHintSwitchEnumCase c tag else DestructHintSwitchEnumKnown c tag) (
        li_tactic (compute_map_lookup_goal (list_to_map (els_tag_int en.(enum_els))) tag false) (λ idx,
        li_tactic (compute_map_lookup_goal m (default 0%Z idx) false) (λ o,
        match o with
        | Some mi =>
           ∃ s, ⌜ss !! mi = Some s⌝ ∗
           normalize_spatial_context E L True (λ L2, typed_stmt E L2 f s fn R ϝ)
        | None =>
          normalize_spatial_context E L True (λ L2, typed_stmt E L2 f def fn R ϝ)
        end))))
    ⊢ typed_switch E L f v _ (enum_discriminant_t en) r it m ss def fn R ϝ.
  Proof.
    unfold li_trace.
    iIntros "HT Hit". rewrite /ty_own_val/=.
    iDestruct "Hit" as "(_ & %tag & %Htag & _ & %Hv)".
    iDestruct "HT" as "(-> & Hc)".
    rewrite /compute_map_lookup_goal.
    iDestruct "Hc" as "(%b & %tag' & %Htag' & %idx & <- & %res & <- & Ha)".
    simplify_eq.
    iExists _. iR.
    unfold els_lookup_tag. case_match.
    - iDestruct "Ha" as "(%s & % & HT)".
      iExists _. iR.
      iIntros (?) "#CTX #HE HL Hf Hpost".
      iMod ("HT" with "[] CTX HE HL [//]") as "(%L2 & HL & HT)"; first done.
      iApply ("HT" with "CTX HE HL Hf Hpost").
    - iIntros (?) "#CTX #HE HL Hf Hpost".
      iMod ("Ha" with "[] CTX HE HL [//]") as "(%L2 & HL & HT)"; first done.
      iApply ("HT" with "CTX HE HL Hf Hpost").
  Qed.
  Global Instance type_switch_enum_inst E L f {rt} (en : enum rt) r v it : TypedSwitch E L f v _ (enum_discriminant_t en) r it :=
    λ m ss def fn R ϝ, i2p (type_switch_enum E L f en r it m ss def fn R ϝ v).

End switch.
