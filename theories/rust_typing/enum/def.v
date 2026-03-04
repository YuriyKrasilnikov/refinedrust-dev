From refinedrust Require Export type.
From refinedrust Require Import uninit_def int.
From refinedrust Require Import struct.def struct.subtype.
From refinedrust Require Import options.

(** * Enums *)
(** Enum support is currently WIP as some of the typing rules are incomplete *)

Section union.
  Context `{!typeGS Σ}.

  (* TODO move *)
  Lemma ly_size_layout_of_union_member ul ly mem :
    layout_of_union_member mem ul = Some ly →
    ly_size ly ≤ ly_size ul.
  Proof.
    rewrite {2}/ly_size/ul_layout.
    rewrite /layout_of_union_member.
    intros (i & Hidx & Ha)%bind_Some.
    eapply max_list_elem_of_le.
    apply list_elem_of_fmap.
    exists ly. split; first done.
    rewrite -list_lookup_fmap in Ha.
    by eapply list_elem_of_lookup_2.
  Qed.

  Lemma max_list_pow (n : nat) l :
    1 ≤ n →
    n ^ (max_list l) = max 1 (max_list ((λ x, n^x) <$> l)).
  Proof.
    intros ?.
    induction l as [ | x l IH]; simpl; first done.
    rewrite Nat_pow_max; last done.
    rewrite IH.
    rewrite Nat.max_assoc. rewrite [_ `max` 1]Nat.max_comm.
    rewrite -Nat.max_assoc. done.
  Qed.

  Lemma ly_align_log_union_layout (ul : union_layout) :
    ly_align_log ul = max_list (ly_align_log <$> (ul_members ul).*2).
  Proof. rewrite /ly_align_log//. Qed.
  Lemma ly_align_union_layout (ul : union_layout) :
    ly_align ul = 1 `max` max_list (ly_align <$> (ul_members ul).*2).
  Proof.
    rewrite /ly_align. rewrite ly_align_log_union_layout.
    rewrite max_list_pow; last lia.
    f_equiv. f_equiv.
    rewrite -list_fmap_compose list_fmap_compose//.
  Qed.
  Lemma aligned_to_max_list x l al :
    x ∈ al →
    l `aligned_to` 2^ max_list al →
    l `aligned_to` 2^ x.
  Proof.
    induction al as [ | y al IH] in x |-*.
    { intros ?%elem_of_nil. done. }
    intros [ -> | Hel ]%elem_of_cons.
    - simpl. intros ?%aligned_to_2_max_l; done.
    - intros ?%aligned_to_2_max_r. by eapply IH.
  Qed.

  Lemma has_layout_loc_layout_of_union_member ul ly mem l :
    layout_of_union_member mem ul = Some ly →
    l `has_layout_loc` ul →
    l `has_layout_loc` ly.
  Proof.
    rewrite /layout_of_union_member.
    intros (i & Hidx & Ha)%bind_Some.
    rewrite /has_layout_loc /ly_align.
    rewrite ly_align_log_union_layout.
    apply aligned_to_max_list.
    apply list_elem_of_fmap.
    exists ly. split; first done.
    rewrite -list_lookup_fmap in Ha.
    by eapply list_elem_of_lookup_2.
  Qed.

  Definition active_union_rest_ly (ul : union_layout) (ly : layout) := Layout (ly_size ul - ly.(ly_size)) 0.
  Lemma has_layout_loc_active_union_rest_ly ul ly l :
    l `has_layout_loc` (active_union_rest_ly ul ly).
  Proof.
    rewrite /has_layout_loc /aligned_to.
    rewrite /active_union_rest_ly /ly_align /=.
    apply Z.divide_1_l.
  Qed.
  Lemma ly_size_active_union_rest_ly ul ly :
    ly_size (active_union_rest_ly ul ly) = ly_size ul - ly.(ly_size).
  Proof. done. Qed.

  (** [active_union_t ty uls] basically wraps [ty] to lay it out in [uls], asserting that a union currently is in variant [variant].
      This is not capturing the allowed union layouting in Rust in full generality (Rust may freely choose the offsets of the variants),
      but we are anyways already not handling tags correctly, so who cares... *)
  (* TODO rather factor out into a padded type, as in RefinedC? *)
  Program Definition active_union_t {rt} (ty : type rt) (variant : string) (uls : union_layout_spec) : type rt := {|
    ty_xt_inhabited := ty_xt_inhabited ty;
    ty_metadata_kind := MetadataNone;
    ty_own_val π r m v :=
      (∃ ul ly,
        ⌜m = MetaNone⌝ ∗
        ⌜use_union_layout_alg uls = Some ul⌝ ∗
        ⌜layout_of_union_member variant ul = Some ly⌝ ∗
        ⌜syn_type_has_layout (ty_syn_type ty MetaNone) ly⌝ ∗
        take ly.(ly_size) v ◁ᵥ{π, MetaNone} r @ ty ∗
        drop ly.(ly_size) v ◁ᵥ{π, MetaNone} () @ uninit (UntypedSynType $ active_union_rest_ly ul ly))%I;
    ty_syn_type _ := uls;
    _ty_has_op_type ot mt :=
      (* only untyped reads are allowed *)
      (* TODO maybe make this more precise. Typed ops would be allowed for the first segment *)
      ∃ ul, use_union_layout_alg uls = Some ul ∧ ot = UntypedOp ul;
    ty_shr κ π r m l :=
      (∃ ul ly,
        ⌜m = MetaNone⌝ ∗
        ⌜use_union_layout_alg uls = Some ul⌝ ∗
        ⌜layout_of_union_member variant ul = Some ly⌝ ∗
        ⌜l `has_layout_loc` ul⌝ ∗
        l ◁ₗ{π, MetaNone, κ} r @ ty ∗
        (l +ₗ ly.(ly_size)) ◁ₗ{π, MetaNone, κ} () @ uninit (UntypedSynType $ active_union_rest_ly ul ly))%I;
    _ty_ghost_drop π r :=
      ty_ghost_drop ty π r;
    _ty_lfts := ty_lfts ty;
    _ty_wf_E := ty_wf_E ty;
    ty_sidecond := True;
  |}.
  Next Obligation.
    iIntros (rt ty var uls π r m v) "(%ul & %ly & -> & %Halg & %Hly & %Hst & Hv & Hvr)".
    iExists ul.
    iSplitR. { iPureIntro. by apply use_union_layout_alg_Some_inv. }
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hv0"; first done.
    rewrite uninit_own_spec. iDestruct "Hvr" as "(_ & % & %Halg1 & %Hv1)".
    iPureIntro. apply syn_type_has_layout_untyped_inv in Halg1 as (-> & _ & _).
    move: Hv0 Hv1. apply ly_size_layout_of_union_member in Hly.
    rewrite /has_layout_val/active_union_rest_ly.
    rewrite length_take length_drop.
    rewrite {4}/ly_size.
    lia.
  Qed.
  Next Obligation.
    intros ??? uls ot mt (ul & Hul & ->).
    simpl. by eapply use_union_layout_alg_Some_inv.
  Qed.
  Next Obligation.
    eauto.
  Qed.
  Next Obligation.
    eauto.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    iIntros (?????????) "(%ul & %ly & -> & % & % & % & _)". iExists ul.
    iSplitR; first done. iPureIntro. by eapply use_union_layout_alg_Some_inv.
  Qed.
  Next Obligation.
    iIntros (rt ty variant uls E κ l ly π r m q ?) "CTX #Hna Htok %Halg %Hly #Hlb Hb".
    set (bor_contents :=
      (∃ (ul : union_layout) ly',
        ⌜m = MetaNone⌝ ∗
        ⌜use_union_layout_alg uls = Some ul⌝ ∗
        ⌜layout_of_union_member variant ul = Some ly'⌝ ∗
        ⌜syn_type_has_layout (ty_syn_type ty MetaNone) ly'⌝ ∗
        ∃ v : val, l ↦ v ∗ take (ly_size ly') v ◁ᵥ{ π, MetaNone} r @ ty ∗ drop (ly_size ly') v ◁ᵥ{ π, MetaNone} .@ uninit (UntypedSynType (active_union_rest_ly ul ly')))%I).
    iPoseProof (bor_iff _ _ bor_contents with "[] Hb") as "Hb".
    { iNext. iModIntro. rewrite /bor_contents. iSplit.
      - iIntros "(%v & Hl & %ul & %ly' & ? & ? & ? & ? & ?)"; eauto with iFrame.
      - iIntros "(%ul & %ly' & -> & ? & ? & ? & %v & ? & ? & ?)"; eauto with iFrame. }
    rewrite /bor_contents.
    iDestruct "CTX" as "#(LFT & LLCTX)".
    rewrite -lft_tok_sep. iDestruct "Htok" as "(Htok & Htok1)".
    iApply fupd_logical_step.
    iMod (bor_exists with "LFT Hb") as "(%ul & Hb)"; first done.
    iMod (bor_exists with "LFT Hb") as "(%ly' & Hb)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hul & Hb)"; first done.
    iMod (bor_persistent with "LFT Hul Htok") as "(>-> & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hul & Hb)"; first done.
    iMod (bor_persistent with "LFT Hul Htok") as "(>%Hul & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hly & Hb)"; first done.
    iMod (bor_persistent with "LFT Hly Htok") as "(>%Hul_ly & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hst & Hb)"; first done.
    iMod (bor_persistent with "LFT Hst Htok") as "(>%Hst & Htok)"; first done.

    specialize (ly_size_layout_of_union_member _ _ _ Hul_ly) as ?.
    apply use_layout_alg_union_Some_inv in Halg as (ul' & Halg & ->).
    assert (ul' = ul) as -> by naive_solver.

    (* now split the values in the borrow *)
    iPoseProof (bor_iff _ _ ((∃ v1 : val, l ↦ v1 ∗ v1 ◁ᵥ{π, MetaNone} r @ ty) ∗ (∃ v2 : val, (l +ₗ ly_size ly') ↦ v2 ∗ v2 ◁ᵥ{ π, MetaNone} .@ uninit (UntypedSynType (active_union_rest_ly ul ly')))) with "[] Hb") as "Hb".
    { iNext. iModIntro. iSplit.
      - iIntros "(%v & Hl & Ha & Hb)".
        rewrite -{1}(take_drop (ly_size ly') v).
        rewrite heap_pointsto_app. iDestruct "Hl" as "(Hl1 & Hl2)".
        iPoseProof (ty_own_val_has_layout with "Ha") as "%Hlyv"; first done.
        rewrite /has_layout_val length_take in Hlyv.
        iSplitL "Hl1 Ha". { iExists _. iFrame. }
        iPoseProof (ty_has_layout with "Hb") as "(%ly2 & %Hst2 & %Hlyv2)".
        apply syn_type_has_layout_untyped_inv in Hst2 as (-> & ? & ? & ?).
        move: Hlyv2. rewrite /has_layout_val length_drop /active_union_rest_ly {2}/ly_size/= => Hlyv2.
        rewrite length_take. rewrite Nat.min_l; last lia.
        eauto with iFrame.
      - iIntros "((%v1 & Hl1 & Hv1) & (%v2 & Hl2 & Hv2))".
        iExists (v1 ++ v2).
        iPoseProof (ty_own_val_has_layout with "Hv1") as "%Hlyv"; first done.
        iPoseProof (ty_has_layout with "Hv2") as "(%ly2 & %Hst2 & %Hlyv2)".
        apply syn_type_has_layout_untyped_inv in Hst2 as (-> & ? & ? & ?).
        move: Hlyv2. rewrite /has_layout_val /active_union_rest_ly {1}/ly_size/= => Hlyv2.
        rewrite /has_layout_val in Hlyv.
        rewrite heap_pointsto_app. rewrite Hlyv. iFrame.
        iSplitL "Hv1". { rewrite take_app_length'; first done. lia. }
        rewrite drop_app_length'; last lia. done. }
    iMod (bor_sep with "LFT Hb") as "(Hb1 & Hb2)"; first done.

    (* now share both parts *)
    iDestruct "Htok" as "(Htok11 & Htok12)".
    iDestruct "Htok1" as "(Htok21 & Htok22)".

    iPoseProof (ty_share _ E with "[$LFT $LLCTX] Hna [Htok11 Htok21] [] [] [] Hb1") as "Hb1"; first done.
    { rewrite ty_lfts_unfold. rewrite -lft_tok_sep. iFrame. }
    { done. }
    { iPureIntro. by eapply has_layout_loc_layout_of_union_member. }
    { iApply (loc_in_bounds_shorten_suf with "Hlb"). done. }

    iPoseProof (ty_share _ E with "[$LFT $LLCTX] Hna [Htok12] [] [] [] Hb2") as "Hb2"; first done.
    { simpl. rewrite right_id. iFrame. }
    { simpl. iPureIntro. apply syn_type_has_layout_untyped; first done.
      - rewrite /active_union_rest_ly/layout_wf/ly_align/=. apply Z.divide_1_l.
      - rewrite /active_union_rest_ly {1}/ly_size. apply use_union_layout_alg_size in Hul. lia.
      - rewrite /ly_align_in_bounds/ly_align/active_union_rest_ly/ly_align_log/=.
        unfold_common_caesium_defs. simpl. nia.
    }
    { iPureIntro. apply has_layout_loc_active_union_rest_ly. }
    { iApply (loc_in_bounds_offset with "Hlb").
      - done.
      - simpl. lia.
      - simpl. rewrite ly_size_active_union_rest_ly. lia. }

    iApply (logical_step_compose with "Hb1").
    iApply (logical_step_compose with "Hb2").
    iApply logical_step_intro.
    iModIntro.
    iIntros "(Hun & Htok1) (Hty & Htok2)".
    simpl. rewrite right_id.
    rewrite -lft_tok_sep.
    rewrite ty_lfts_unfold.
    iDestruct "Htok2" as "(? & ?)". by iFrame.
  Qed.
  Next Obligation.
    iIntros (rt ty variant uls κ κ' π r m l) "#Hincl Hb".
    iDestruct "Hb" as "(%ul & %ly & -> & ? & ? & ? & Ha & Hb)".
    iExists ul, ly. iFrame.
    iR.
    iSplitL "Ha". { iApply ty_shr_mono; done. }
    iApply ty_shr_mono; done.
  Qed.
  Next Obligation.
    iIntros (??????????) "Hb".
    iDestruct "Hb" as "(%ul & %ly & -> & %Halg & %Hly & ? & Hv & _)".
    iPoseProof (ty_own_ghost_drop with "Hv") as "Ha"; last iApply (logical_step_wand with "Ha"); eauto.
  Qed.
  Next Obligation.
    intros rt ty variant uls ot mt st π r m v (ul & Hul & ->).
    iIntros "Hv".
    destruct mt; first done; last done.
    by rewrite mem_cast_UntypedOp.
  Qed.
  Next Obligation.
    intros ??? uls ly mt _ Hst.
    apply syn_type_has_layout_union_inv in Hst as (variants & ul & -> & Hul & Hf).
    exists ul. split; last done.
    by eapply use_union_layout_alg_Some.
  Qed.
End union.

Section type_incl.
  Context `{!typeGS Σ}.

  Lemma active_union_type_incl {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) r1 r2 variant1 variant2 uls :
    variant1 = variant2 →
    type_incl r1 r2 ty1 ty2 -∗
    type_incl r1 r2 (active_union_t ty1 variant1 uls) (active_union_t ty2 variant2 uls).
  Proof.
    iIntros (->) "(%Hst & #Hsc & #Hincl & #Hincl2)".
    iSplitR. { simpl. done. }
    iSplitR. { simpl. eauto. }
    iSplitR; iModIntro.
    - iIntros (π m v) "Hv". rewrite {3 4}/ty_own_val/=.
      iDestruct "Hv" as "(%ul & %ly & -> & %Huls & %Hly & % & Hv1 & Hv2)".
      rewrite -Hst. iExists ul, ly. iR. iR. iR. iR. iSplitL "Hv1".
      + iApply "Hincl". done.
      + done.
    - iIntros (κ π m l) "Hl". rewrite {3 4}/ty_shr/=.
      iDestruct "Hl" as "(%ul & %ly & -> & %Huls & %Hly & %Hl & Hl1 & Hl2)".
      iExists ul, ly. iR. iR. iR. iR. iSplitL "Hl1".
      + iApply "Hincl2". done.
      + done.
  Qed.
End type_incl.

Section enum.
  Context `{!typeGS Σ}.

  Import EqNotations.

  (* NOTE: for now, we only support untyped reads from enums.
      To handle this more accurately, we should probably figure out the proper model for enums with niches etc first. *)
  Definition is_enum_ot {rt} (en : enum rt) (ot : op_type) (mt : memcast_compat_type) :=
    match ot with
    | UntypedOp ly =>
        ∃ el : struct_layout, use_enum_layout_alg en.(enum_els) = Some el ∧
        ly = el
        (*f∧ oldr (λ '(v, st) P,*)
            (*∃ rty ly',*)
            (*en.(enum_tag_ty) v = Some rty ∧*)
            (*syn_type_has_layout st ly' ∧*)
            (*ty_has_op_type (projT2 rty) (UntypedOp ly') mt*)
          (*) True (en.(enum_els).(els_variants))*)
    | _ => False
    end.
  Global Typeclasses Opaque is_enum_ot.


  (* NOTE: in principle, we might want to formulate this with [ex_plain_t] as an existential abstraction over a struct.
     However, here the inner type also depends on the outer refinement, which is not supported by [ex_plain_t] right now. *)
  Program Definition enum_t {rt} (e : enum rt) : type rt := {|
    ty_xt_inhabited := enum_xt_inhabited e;
    ty_metadata_kind := MetadataNone;
    ty_own_val π r m v :=
      (∃ el tag,
      ⌜m = MetaNone⌝ ∗
      ⌜use_enum_layout_alg e.(enum_els) = Some el⌝ ∗
      ⌜(e.(enum_tag) r) = Some tag⌝ ∗
      (* we cannot directly borrow the variant or data fields while in this interpretation *)
      v ◁ᵥ{π, MetaNone} -[#(els_lookup_tag e.(enum_els) tag); #(e.(enum_r) r)] @ struct_t (sls_of_els e.(enum_els))
        +[int e.(enum_els).(els_tag_it); active_union_t (e.(enum_ty) r) tag (uls_of_els e.(enum_els))])%I;
    ty_shr κ π r m l :=
      (∃ ly tag,
      ⌜m = MetaNone⌝ ∗
      ⌜syn_type_has_layout e.(enum_els) ly⌝ ∗
      ⌜e.(enum_tag) r = Some tag⌝ ∗
      l ◁ₗ{π, MetaNone, κ} -[#(els_lookup_tag e.(enum_els) tag); #(e.(enum_r) r)] @ struct_t (sls_of_els e.(enum_els))
        +[int e.(enum_els).(els_tag_it); active_union_t (e.(enum_ty) r) tag (uls_of_els e.(enum_els))])%I;
    ty_syn_type _ := e.(enum_els);
    _ty_has_op_type ot mt :=
      is_enum_ot e ot mt;
    ty_sidecond := True%I;
    _ty_ghost_drop π r :=
      (* TODO *)
      True%I;
    _ty_lfts := e.(enum_lfts);
    _ty_wf_E := e.(enum_wf_E);
  |}.
  Next Obligation.
    iIntros (rt e π r m v).
    iIntros "(%el & %tag & -> & %Halg & %Htag & Hv)".
    (*specialize (syn_type_has_layout_els_sls _ _ Halg) as (sl & Halg' & ->).*)
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv".
    { simpl. by apply use_struct_layout_alg_Some_inv. }
    iExists el. iPureIntro; split; last done.
    by eapply use_enum_layout_alg_Some_inv.
  Qed.
  Next Obligation.
    rewrite /is_enum_ot. simpl.
    intros rt en ot mt Hot.
    destruct ot as [ | | | | ly| ]; try done.
    destruct Hot as (el & Halg & ->).
    simpl. by apply use_enum_layout_alg_Some_inv.
  Qed.
  Next Obligation.
    eauto.
  Qed.
  Next Obligation.
    eauto.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    iIntros (rt e κ π l m r) "(%ly & %tag & -> & %Halg & %Htag & Hl)".
    iPoseProof (ty_shr_aligned with "Hl") as "(%ly' & %Hly & %Halg')". simpl in *.
    specialize (syn_type_has_layout_els_sls _ _ Halg) as (sl & Halg'' & ->).
    apply use_struct_layout_alg_Some_inv in Halg''.
    assert (ly' =  sl) as -> by by eapply syn_type_has_layout_inj.
    iExists sl. done.
  Qed.
  Next Obligation.
    iIntros (rt e E κ l ly π r m q ?) "#CTX #Hna Htok %Halg %Hly Hlb Hb".
    iAssert (&{κ} ((∃ (el : struct_layout) (tag : string), ⌜m = MetaNone⌝ ∗ ⌜use_enum_layout_alg (enum_els e) = Some el⌝ ∗ ⌜e.(enum_tag) r = Some tag⌝ ∗ ∃ v : val, l ↦ v ∗ v ◁ᵥ{π, MetaNone} -[# (els_lookup_tag e.(enum_els) tag); # (e.(enum_r) r)] @ struct_t (sls_of_els (enum_els e)) +[int (els_tag_it (enum_els e)); active_union_t (e.(enum_ty) r) tag (uls_of_els (enum_els e))])))%I with "[Hb]" as "Hb".
    { iApply (bor_iff with "[] Hb"). iNext. iModIntro.
      iSplit.
      - iIntros "(%v & Hl & % & % & ? & ? & ?)". eauto 8 with iFrame.
      - iIntros "(% & % & -> & ? & ? & % & ? & ?)". eauto 8 with iFrame. }
    simpl. iEval (rewrite -lft_tok_sep) in "Htok". iDestruct "Htok" as "(Htok1 & Htok2)".
    iApply fupd_logical_step.
    iDestruct "CTX" as "(LFT & LLCTX)".
    iMod (bor_exists_tok with "LFT Hb Htok1") as "(%ly' & Hb & Htok1)"; first done.
    iMod (bor_exists_tok with "LFT Hb Htok1") as "(%tag & Hb & Htok1)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Halg & Hb)"; first done.
    iMod (bor_persistent with "LFT Halg Htok1") as "(>-> & Htok1)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Halg & Hb)"; first done.
    iMod (bor_persistent with "LFT Halg Htok1") as "(>%Halg' & Htok1)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Htag & Hb)"; first done.
    iMod (bor_persistent with "LFT Htag Htok1") as "(>%Htag & Htok1)"; first done.
    iPoseProof (list_incl_lft_incl_list (ty_lfts (e.(enum_ty) r)) (enum_lfts e)) as "Hincl".
    { etrans; last eapply (enum_lfts_complete _ e r). done. }
    iMod (lft_incl_acc with "Hincl Htok2") as "(%q' & Htok2 & Htok2_cl)"; first done.
    iPoseProof (lft_tok_lb with "Htok1 Htok2") as "(%q'' & Htok1 & Htok2 & Htok_cl)".
    iCombine ("Htok1 Htok2") as "Htok".
    rewrite !lft_tok_sep.
    specialize (syn_type_has_layout_els_sls _ _ Halg) as (sl & Halg'' & ->).
    iPoseProof (ty_share _ E _ _ _ _ _ _ q'' with "[$] Hna [Htok] [] [] Hlb Hb") as "Hstep"; first done.
    { simpl. rewrite !ty_lfts_unfold/=ty_lfts_unfold/=. rewrite right_id. done. }
    { simpl. iPureIntro. by apply use_struct_layout_alg_Some_inv. }
    { done. }
    simpl.
    rewrite ty_lfts_unfold/=ty_lfts_unfold/=.
    iApply logical_step_fupd.
    iApply (logical_step_wand with "Hstep").
    iModIntro. iIntros "(Hl & Htok)".
    rewrite right_id -lft_tok_sep. iDestruct "Htok" as "(Htok1 & Htok2)".
    iPoseProof ("Htok_cl" with "Htok1 Htok2") as "(Htok1 & Htok2)".
    iMod ("Htok2_cl" with "Htok2") as "Htok2".
    rewrite -lft_tok_sep. iFrame.
    iExists _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (rt e κ κ' π r m l) "#Hincl (%ly & %tag & -> & ? & ? & Hl)".
    iExists ly, tag. iFrame. iR.
    iApply (ty_shr_mono with "Hincl Hl").
  Qed.
  Next Obligation.
    intros. iIntros "_". by iApply logical_step_intro.
  Qed.
  Next Obligation.
    iIntros (rt en ot mt st π r m v Hot) "Hl".
    iDestruct "Hl" as "(%ly & %tag & -> & %Hst & %Htag & Ha)".
    destruct mt; first done; first last.
    { destruct ot; done. }
    iExists ly, tag. iR. iR. iR.

    iApply (ty_memcast_compat _ _ _ MCCopy with "Ha").
    rewrite ty_has_op_type_unfold. simpl. rewrite /is_struct_ot/=.
    (*split; first done.*)
    destruct ot as [ | | | | ly' | ]; try done.
    (*
    rewrite ty_has_op_type_unfold.
    rewrite /is_enum_ot in Hot.
    destruct Hot as (el & Hel & ->).
    exists el. split; first done. split; first done.
    split.
    { exists (els_tag_it (enum_els en)). simpl. split_and!.
      - eapply syn_type_has_layout_int; done.
      - done.
      - apply it_size_bounded. }
    split; last done.
    apply use_enum_layout_alg_inv in Hel as (ul & variants & Hul & Hel & Hvariants).
    exists ul.
    assert (syn_type_has_layout (uls_of_els (enum_els en)) ul) as Hul'.
    { eapply syn_type_has_layout_union; last done. done. }
    split; first done.
    exists ul. split; last done.
    eapply use_union_layout_alg_Some; done.
     *)
  Qed.
  Next Obligation.
    intros ?? ly mt _ Hst.
    apply syn_type_has_layout_enum_inv in Hst as (el & ul & variants & Hul & Hsl & -> & Hf).
    simpl. exists el. split; last done.
    by eapply use_enum_layout_alg_Some.
  Qed.

  Lemma enum_t_copyable {rt} (e : enum rt):
    (∀ r : rt, Copyable ((e.(enum_ty) r))) →
    Copyable (enum_t e).
  Proof.
    (* TODO *)
  Admitted.

  Global Instance enum_t_sized {rt} (e : enum rt) :
    TySized (enum_t e).
  Proof.
    econstructor; done.
  Qed.
End enum.

Global Hint Extern 10 (Copyable _) => (refine (enum_t_copyable _ _); intros []; apply _) : typeclass_instances.

Section ne.
  Context `{!typeGS Σ}.

  Import EqNotations.
  Class EnumNonExpansive {rt1 rt2} (F : type rt1 → enum rt2) := {
    enum_ne_els :
      ∀ ty ty' : type rt1, st_of ty MetaNone = st_of ty' MetaNone → enum_els (F ty) = enum_els (F ty');
    enum_ne_lft_mor :
      DirectLftMorphism (λ ty, (F ty).(enum_lfts)) (λ ty, (F ty).(enum_wf_E));
    (* the tag of the variant should not depend on the ty *)
    enum_ne_tag_consistent :
      ∀ ty ty', (F ty).(enum_tag) = (F ty').(enum_tag);
    (* the rt of the variant should not depend on the ty *)
    enum_ne_rt_consistent :
      ∀ ty ty' r, (F ty).(enum_rt) r = (F ty').(enum_rt) r;
    (* the refinement of the variant should not depend on the ty *)
    enum_ne_r_consistent :
      ∀ ty ty' r, rew [RT_rt] (enum_ne_rt_consistent ty ty' r) in (F ty).(enum_r) r = (F ty').(enum_r) r;

    (* the functor on types is non-expansive *)
    enum_ne_ty_dist :
      ∀ r n ty ty',
      TypeDist n ty ty' →
      TypeDist
        n
        (rew [λ x, type x] (enum_ne_rt_consistent ty ty' r) in ((F ty).(enum_ty) r : type (enum_rt (F ty) r)))
        ((F ty').(enum_ty) r);
    (* same for Dist2, for the sharing predicate *)
    (* [enum_ne_ty_dist] and [enum_ne_ty_dist2] are incomparable in strength *)
    enum_ne_ty_dist2 :
      ∀ r n ty ty',
      TypeDist2 n ty ty' →
      TypeDist2
        n
        (rew [λ x, type x] (enum_ne_rt_consistent ty ty' r) in ((F ty).(enum_ty) r : type (enum_rt (F ty) r)))
        ((F ty').(enum_ty) r);
  }.
  Lemma enum_ne_lookup_tag_consistent {rt1 rt2} (F : type rt1 → enum rt2) ty ty' r :
    EnumNonExpansive F →
    st_of ty MetaNone = st_of ty' MetaNone →
    enum_lookup_tag (F ty) r = enum_lookup_tag (F ty') r.
  Proof.
    intros Hne Hd.
    unfold enum_lookup_tag.
    erewrite enum_ne_els; last apply Hd.
    erewrite enum_ne_tag_consistent; done.
  Qed.

  Global Instance enum_ne_const {rt1 rt2} (en : enum rt2) :
    EnumNonExpansive (λ _ : type rt1, en).
  Proof.
    unshelve econstructor.
    - done.
    - done.
    - apply _.
    - done.
    - done.
    - done.
    - done.
  Qed.

  Class EnumContractive {rt1 rt2} (F : type rt1 → enum rt2) := {
    enum_contr_els :
      ∀ ty ty' : type rt1, enum_els (F ty) = enum_els (F ty');
    enum_contr_lft_mor :
      DirectLftMorphism (λ ty, (F ty).(enum_lfts)) (λ ty, (F ty).(enum_wf_E));
    (* the tag of the variant should not depend on the ty *)
    enum_contr_tag_consistent :
      ∀ ty ty', (F ty).(enum_tag) = (F ty').(enum_tag);
    (* the rt of the variant should not depend on the ty *)
    enum_contr_rt_consistent :
      ∀ ty ty' r, (F ty).(enum_rt) r = (F ty').(enum_rt) r;
    (* the refinement of the variant should not depend on the ty *)
    enum_contr_r_consistent :
      ∀ ty ty' r, rew [RT_rt] (enum_contr_rt_consistent ty ty' r) in (F ty).(enum_r) r = (F ty').(enum_r) r;

    enum_contr_ty_dist :
      ∀ r n ty ty',
      TypeDist2 n ty ty' →
      TypeDist
        n
        (rew [λ x, type x] (enum_contr_rt_consistent ty ty' r) in ((F ty).(enum_ty) r : type (enum_rt (F ty) r)))
        ((F ty').(enum_ty) r);
    (* same for Dist2, for the sharing predicate *)
    (* [enum_contr_ty_dist] and [enum_contr_ty_dist2] are incomparable in strength *)
    enum_contr_ty_dist2 :
      ∀ r n ty ty',
      TypeDistLater2 n ty ty' →
      TypeDist2
        n
        (rew [λ x, type x] (enum_contr_rt_consistent ty ty' r) in ((F ty).(enum_ty) r : type (enum_rt (F ty) r)))
        ((F ty').(enum_ty) r);
  }.
  Lemma enum_contractive_lookup_tag_consistent {rt1 rt2} (F : type rt1 → enum rt2) ty ty' r :
    EnumContractive F →
    enum_lookup_tag (F ty) r = enum_lookup_tag (F ty') r.
  Proof.
    intros Hne.
    unfold enum_lookup_tag.
    erewrite enum_contr_els.
    erewrite enum_contr_tag_consistent; done.
  Qed.

  Local Lemma enum_el_val_unfold {rt} (ty : type rt) π i fields v r tag uls :
    struct_own_el_val π i fields v r (active_union_t ty tag uls) ≡
      (∃ (ly0 : layout), ⌜snd <$> fields !! i = Some ly0⌝ ∗ ⌜syn_type_has_layout uls ly0⌝ ∗
        (∃ (ul : union_layout) (ly : layout),
        ⌜use_union_layout_alg uls = Some ul⌝ ∗
        ⌜layout_of_union_member tag ul = Some ly⌝ ∗
        ⌜syn_type_has_layout (st_of ty MetaNone) ly⌝ ∗
        (∃ r' : rt, place_rfn_interp_owned r r' ∗
          take (ly_size ly) v ◁ᵥ{π, MetaNone} r' @ ty) ∗
        drop (ly_size ly) v ◁ᵥ{π, MetaNone} .@ uninit (UntypedSynType (active_union_rest_ly ul ly))))%I.
  Proof.
    rewrite /struct_own_el_val{1}/ty_own_val/=.
    iSplit.
    - iIntros "(%r' & %ly & Hrfn & $ & $ & %ul & %ly' & _ & ? & ? & ? & ? & ?)".
      iExists ul, ly'. iFrame.
    - iIntros "(%ly' & ? & ? & %ul & %ly & ? & ? & ? & (%r' & ? & ?) & ?)".
      iExists r', ly'. by iFrame.
  Qed.

  Local Lemma enum_el_shr_unfold {rt} (ty : type rt) π κ i fields l r tag uls :
    struct_own_el_shr π κ i fields l r (active_union_t ty tag uls) ≡
    (∃ (ly : layout), ⌜snd <$> fields !! i = Some ly⌝ ∗ ⌜syn_type_has_layout uls ly⌝ ∗ True ∗
      (∃ (ul : union_layout) (ly0 : layout),
      ⌜use_union_layout_alg uls = Some ul⌝ ∗
      ⌜layout_of_union_member tag ul = Some ly0⌝ ∗
      ⌜(l +ₗ offset_of_idx fields i) `has_layout_loc` ul⌝ ∗
      (∃ r' : rt, place_rfn_interp_shared r r' ∗
        (l +ₗ offset_of_idx fields i) ◁ₗ{π, MetaNone, κ} r'@ty) ∗
      (l +ₗ offset_of_idx fields i +ₗ ly_size ly0) ◁ₗ{π, MetaNone, κ} .@
      uninit (UntypedSynType (active_union_rest_ly ul ly0))))%I.
  Proof.
    rewrite /struct_own_el_shr{1}/ty_shr/=.
    iSplit.
    - iIntros "(%r' & %ly & Hrfn & ? & ? & _ & %ul & %ly' & _ & ? & ? & ? & ? & ?)".
      iExists ly. iFrame.
    - iIntros "(%ly' & ? & ? & _ & %ul & %ly & ? & ? & ? & (%r' & ? & ?) & ?)".
      iExists r', ly'. iFrame. done.
  Qed.

  Global Instance enum_t_ne {rt1 rt2} (F : type rt1 → enum rt2) :
    EnumNonExpansive F →
    TypeNonExpansive (λ ty : type rt1, enum_t (F ty)).
  Proof.
    intros Hen. constructor.
    - done.
    - simpl. intros. erewrite enum_ne_els; done.
    - apply ty_lft_morphism_of_direct.
      rewrite /=ty_lfts_unfold/=.
      rewrite /=ty_wf_E_unfold.
      apply enum_ne_lft_mor.
    - rewrite !ty_has_op_type_unfold.
      intros ty ty' Hst Hot ot mt. simpl.
      unfold is_enum_ot.
      destruct ot as [ | | | | ly | ]; try done.
      do 4 f_equiv.
      erewrite enum_ne_els; first done. done.
    - simpl. eauto.
    - intros n ty ty' Hd.
      iIntros (π r m v). rewrite /ty_own_val/=.
      do 6 f_equiv.
      { erewrite enum_ne_els; first done. apply Hd. }
      erewrite enum_ne_els; last apply Hd.

      erewrite enum_ne_tag_consistent. f_equiv; first done.
      eapply struct_t_own_val_dist. simpl.
      constructor; last constructor; last constructor; first done.
      intros ???.
      rewrite !enum_el_val_unfold.
      do 7 f_equiv.
      intros ly.
      do 3 f_equiv.
      { simpl.
        f_equiv.
        eapply (enum_ne_ty_dist r) in Hd.
        destruct Hd as [Hst _ _ _].
        rewrite -Hst.
        generalize (enum_ne_rt_consistent ty ty' r) as Heq.
        destruct Heq. done. }
      f_equiv. simpl.
      assert (∀ ty, (∃ r' : enum_rt (F ty) r, ⌜enum_r (F ty) r = r'⌝ ∗ take (ly_size ly) v0 ◁ᵥ{π, MetaNone} r' @ enum_ty (F ty) r)%I
        ≡ (take (ly_size ly) v0 ◁ᵥ{π, MetaNone} enum_r (F ty) r @ enum_ty (F ty) r)%I) as Heq.
      { iIntros (?). iSplit.
        - iIntros "(% & <- & $)".
        - iIntros "Ha". iExists _. iFrame. done. }
      rewrite !Heq.
      clear -Hen Hd.
      eapply (enum_ne_ty_dist r) in Hd.
      destruct Hd as [_ _ Hv _].
      rewrite -Hv.
      clear.
      rewrite -(enum_ne_r_consistent ty ty' r).
      generalize (enum_ne_rt_consistent ty ty' r); intros Heq.
      destruct Heq.
      done.
    - intros n ty ty' Hd.
      iIntros (κ π r m l). rewrite /ty_shr/=.
      do 6 f_equiv.
      { erewrite enum_ne_els; first done. apply Hd. }
      erewrite enum_ne_els; last apply Hd.

      f_equiv. { erewrite enum_ne_tag_consistent. done. }
      eapply struct_t_shr_dist. simpl.
      constructor; last constructor; last constructor; first done.
      intros ???.

      rewrite !enum_el_shr_unfold.
      do 12 f_equiv.
      assert (∀ ty, (∃ r' : enum_rt (F ty) r, ⌜enum_r (F ty) r = r'⌝ ∗ (l0 +ₗ offset_of_idx fields i) ◁ₗ{π, MetaNone, κ} r'@enum_ty (F ty) r)%I
        ≡ ((l0 +ₗ offset_of_idx fields i) ◁ₗ{π, MetaNone, κ} enum_r (F ty) r @enum_ty (F ty) r)%I) as Heq.
      { iIntros (?). iSplit.
        - iIntros "(% & <- & $)".
        - iIntros "Ha". iExists _. iFrame. done. }
      rewrite !Heq.
      clear -Hen Hd.

      eapply (enum_ne_ty_dist2 r) in Hd.
      destruct Hd as [_ _ _ Hshr].
      rewrite -Hshr.
      clear.
      rewrite -(enum_ne_r_consistent ty ty' r).
      generalize (enum_ne_rt_consistent ty ty' r); intros Heq.
      destruct Heq.
      done.
    - rewrite ty_ghost_drop_unfold. solve_type_proper.
  Qed.

  Global Instance enum_t_contr {rt1 rt2} (F : type rt1 → enum rt2) :
    EnumContractive F →
    TypeContractive (λ ty : type rt1, enum_t (F ty)).
  Proof.
    intros Hen. constructor.
    - done.
    - simpl. intros. erewrite enum_contr_els; done.
    - apply ty_lft_morphism_of_direct.
      rewrite /=ty_lfts_unfold/=.
      rewrite /=ty_wf_E_unfold.
      apply enum_contr_lft_mor.
    - rewrite !ty_has_op_type_unfold.
      intros ty ty' ot mt. simpl.
      unfold is_enum_ot.
      destruct ot as [ | | | | ly | ]; try done.
      do 3 f_equiv.
      erewrite enum_contr_els; last done.
    - simpl. eauto.
    - intros n ty ty' Hd.
      iIntros (π r m v). rewrite /ty_own_val/=.
      do 6 f_equiv.
      { erewrite enum_contr_els; first done. }
      erewrite (enum_contr_els _ ty').

      erewrite enum_contr_tag_consistent. f_equiv; first done.
      eapply struct_t_own_val_dist. simpl.
      constructor; last constructor; last constructor; first done.
      intros ???.
      rewrite !enum_el_val_unfold.
      do 7 f_equiv.
      intros ly.
      do 3 f_equiv.
      { simpl.
        f_equiv.
        eapply (enum_contr_ty_dist r) in Hd.
        destruct Hd as [Hst _ _ _].
        rewrite -Hst.
        generalize (enum_contr_rt_consistent ty ty' r) as Heq.
        destruct Heq. done. }
      f_equiv. simpl.
      assert (∀ ty, (∃ r' : enum_rt (F ty) r, ⌜enum_r (F ty) r = r'⌝ ∗ take (ly_size ly) v0 ◁ᵥ{π, MetaNone} r' @ enum_ty (F ty) r)%I
        ≡ (take (ly_size ly) v0 ◁ᵥ{π, MetaNone} enum_r (F ty) r @ enum_ty (F ty) r)%I) as Heq.
      { iIntros (?). iSplit.
        - iIntros "(% & <- & $)".
        - iIntros "Ha". iExists _. iFrame. done. }
      rewrite !Heq.
      clear -Hen Hd.
      eapply (enum_contr_ty_dist r) in Hd.
      destruct Hd as [_ _ Hv _].
      rewrite -Hv.
      clear.
      rewrite -(enum_contr_r_consistent ty ty' r).
      generalize (enum_contr_rt_consistent ty ty' r); intros Heq.
      destruct Heq.
      done.
    - intros n ty ty' Hd.
      iIntros (κ π r m l). rewrite /ty_shr/=.
      do 6 f_equiv.
      { erewrite enum_contr_els; first done. }
      erewrite (enum_contr_els _ ty').

      f_equiv. { erewrite enum_contr_tag_consistent. done. }
      eapply struct_t_shr_dist. simpl.
      constructor; last constructor; last constructor; first done.
      intros ???.

      rewrite !enum_el_shr_unfold.
      do 12 f_equiv.
      assert (∀ ty, (∃ r' : enum_rt (F ty) r, ⌜enum_r (F ty) r = r'⌝ ∗ (l0 +ₗ offset_of_idx fields i) ◁ₗ{π, MetaNone, κ} r'@enum_ty (F ty) r)%I
        ≡ ((l0 +ₗ offset_of_idx fields i) ◁ₗ{π, MetaNone,κ} enum_r (F ty) r @enum_ty (F ty) r)%I) as Heq.
      { iIntros (?). iSplit.
        - iIntros "(% & <- & $)".
        - iIntros "Ha". iExists _. iFrame. done. }
      rewrite !Heq.
      clear -Hen Hd.

      eapply (enum_contr_ty_dist2 r) in Hd.
      destruct Hd as [_ _ _ Hshr].
      rewrite -Hshr.
      clear.
      rewrite -(enum_contr_r_consistent ty ty' r).
      generalize (enum_contr_rt_consistent ty ty' r); intros Heq.
      destruct Heq.
      done.
    - rewrite ty_ghost_drop_unfold. solve_type_proper.
  Qed.

End ne.
