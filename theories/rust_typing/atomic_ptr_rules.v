From refinedrust Require Export atomic_int atomic_int_rules.
From refinedrust Require Import int shr_ref options alias_ptr.

(** Typing rules for atomic operations on [at_ex_plain_t]-wrapped pointer types.

    Provides [TypedAtomicLoadVal], [TypedAtomicStoreVal], [TypedAtomicRmwVal],
    and [TypedCasVal] instances for [alias_ptr_t] with [PtrOp]. *)

(** * Helper: open atomic invariant from [shr_ref] for ptr *)

Section shr_ref_at_ex_acc_ptr.
  Context `{!typeGS Σ}.
  Context {Y : RT} (P : at_ex_inv_def loc Y).

  Lemma shr_ref_at_ex_acc_ptr E (κ : lft) (π : thread_id)
      (r' : Y) (l : loc) (q : Qp) :
    lftE ⊆ E ∖ ↑(shrN.@l) →
    ↑(shrN.@l) ⊆ E →
    lft_ctx -∗
    £ 1 -∗
    q.[κ] -∗
    (□ |={lftE}=> ty_shr (∃at; P, alias_ptr_t) κ π r' MetaNone l)
    ={E, E∖↑(shrN.@l)}=∗
    ∃ (l_stored : loc),
      P.(at_inv_P) π l_stored r' ∗
      (l ↦: ty_own_val alias_ptr_t π l_stored MetaNone) ∗
      (∀ l' : loc,
          (l ↦: ty_own_val alias_ptr_t π l' MetaNone) ∗ P.(at_inv_P) π l' r'
          ={E∖↑(shrN.@l), E}=∗ q.[κ]).
  Proof.
    iIntros (??) "#LFT Hcred Hκ #Hshr".
    iMod (fupd_mask_mono lftE with "Hshr") as "Hshr'"; first set_solver.
    iEval (unfold ty_shr, at_ex_plain_t) in "Hshr'".
    iDestruct "Hshr'" as "(Hsc & #Hbor & %ly & %Hly & %Halg)".
    iMod (rr_at_bor_acc with "LFT Hbor Hκ") as "(HP & Hvs)"; [done..|].
    iApply (lc_fupd_add_later with "Hcred").
    do 2 iModIntro.
    iDestruct "HP" as (l_stored) "(Hmapsto & HP)".
    iExists l_stored. iFrame.
    iIntros (l') "(Hmapsto & HP)".
    iApply ("Hvs" with "[Hmapsto HP]").
    iNext. iExists l'. iFrame.
  Qed.
End shr_ref_at_ex_acc_ptr.

(** * Atomic load for ptr *)

Section atomic_load_ptr.
  Context `{!typeGS Σ}.
  Context {Y : RT} (P : at_ex_inv_def loc Y).

  Lemma typed_atomic_load_atomic_ptr E L f
      (v : val) (κ : lft) (r : place_rfn Y)
      (T : typed_val_expr_cont_t) :
    ⌜lctx_lft_alive E L κ⌝ ∗
    ⌜((ot_layout PtrOp).(ly_size) ≤ bytes_per_addr)%nat⌝ ∗
    find_in_context FindCreditStore (λ '(c, a),
      ⌜fast_lia_hint (1 ≤ c)⌝ ∗
      (credit_store (c - 1) a -∗
        ∀ (l_loaded : loc) (v_loaded : val),
          ⌜val_to_loc v_loaded = Some l_loaded⌝ -∗
          T L v_loaded MetaNone loc alias_ptr_t l_loaded))
    ⊢ typed_atomic_load E L f v
        (v ◁ᵥ{f.1, MetaNone} r @ shr_ref κ (∃at; P, alias_ptr_t))
        PtrOp T.
  Proof.
    rewrite /typed_atomic_load /FindCreditStore /fast_lia_hint.
    iIntros "(%Halive & %Hbpa & Ha) Hv".
    iDestruct "Ha" as ([c a]) "(Hstore & %Hn & HT)". simpl.
    iIntros (Φ) "#(LFT & LLCTX) #HE HL Hf HΦ".
    iEval (rewrite /ty_own_val /=) in "Hv".
    iDestruct "Hv" as "(%l & %ly & %r' & %Hm & %Hv_eq & %Halg & %Hly_loc & #Hlb & #Hsc & #Hrfn & #Hshr)".
    subst v.
    iPoseProof (credit_store_scrounge 1 with "Hstore") as "(Hcred & Hstore)"; first lia.
    iPoseProof ("HT" with "Hstore") as "HT".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iMod (lctx_lft_alive_tok_noend κ with "HE HL") as (q') "(Hκ & HL & Hclose_lft)";
      [solve_ndisj | done | ].
    iApply (wpe_atomic ⊤ (⊤ ∖ ↑shrN.@l)).
    iMod (shr_ref_at_ex_acc_ptr ⊤ with "LFT Hcred Hκ Hshr") as
      (l_stored) "(Hinv & Hpoints & Hclose)"; [solve_ndisj | solve_ndisj | ].
    iDestruct "Hpoints" as (v_old) "(Hmapsto & #Hown)".
    iEval (rewrite /ty_own_val /=) in "Hown".
    iDestruct "Hown" as "(%Hmeta & %Hv_eq & %Hin_usize)".
    (* Derive val_to_loc from the equality *)
    have Hval_l : val_to_loc v_old = Some l_stored.
    { rewrite Hv_eq. apply val_to_of_loc. }
    apply syn_type_has_layout_ptr_inv in Halg. subst ly.
    iModIntro.
    iApply (wp_deref _ _ _ l PtrOp 1 f.1 _ ScOrd with "Hmapsto").
    { left; done. }
    { apply val_to_of_loc. }
    { rewrite /ot_layout. done. }
    { rewrite /has_layout_val /ot_layout /=. apply val_to_loc_length. by eexists. }
    iApply physical_step_intro. iNext. iIntros (st) "Hmapsto".
    iMod ("Hclose" $! l_stored with "[Hmapsto Hinv]") as "Hκ".
    { iFrame "Hinv". iExists v_old. iFrame "Hmapsto".
      rewrite /ty_own_val /=. iPureIntro. exact (conj Hmeta (conj Hv_eq Hin_usize)). }
    iMod ("Hclose_lft" with "Hκ HL") as "HL".
    iPoseProof ("HL_cl" with "HL") as "HL".
    rewrite Hv_eq (mem_cast_id_loc l_stored).
    iAssert ((val_of_loc l_stored) ◁ᵥ{f.1, MetaNone} l_stored @ alias_ptr_t)%I as "Hv_ret".
    { rewrite /ty_own_val /=. iPureIntro. exact (conj Hmeta (conj eq_refl Hin_usize)). }
    iModIntro. iApply ("HΦ" with "HL Hf Hv_ret [HT]").
    { iApply ("HT" $! l_stored (val_of_loc l_stored) with "[%]").
      apply val_to_of_loc. }
  Qed.

  Global Program Instance typed_atomic_load_val_atomic_ptr_inst E L f v κ r :
    TypedAtomicLoadVal E L f v (shr_ref κ (∃at; P, alias_ptr_t)) r PtrOp :=
    λ T, i2p (typed_atomic_load_atomic_ptr E L f v κ r T).
End atomic_load_ptr.

(** * Atomic store for ptr *)

Section atomic_store_ptr.
  Context `{!typeGS Σ}.
  Context {Y : RT} (P : at_ex_inv_def loc Y).

  Lemma typed_atomic_store_atomic_ptr E L f
      (v_ptr : val) (v_val : val) (l_new : loc)
      (κ : lft) (r : place_rfn Y)
      (T : typed_write_cont_t) :
    ⌜lctx_lft_alive E L κ⌝ ∗
    ⌜((ot_layout PtrOp).(ly_size) ≤ bytes_per_addr)%nat⌝ ∗
    find_in_context FindCreditStore (λ '(c, a),
      ⌜fast_lia_hint (1 ≤ c)⌝ ∗
      (credit_store (c - 1) a -∗
        ∃ x, ⌜r = #x⌝ ∗ P.(at_inv_P) f.1 l_new x ∗ T L))
    ⊢ typed_atomic_store E L f
        v_ptr (v_ptr ◁ᵥ{f.1, MetaNone} r @ shr_ref κ (∃at; P, alias_ptr_t))
        v_val (v_val ◁ᵥ{f.1, MetaNone} l_new @ alias_ptr_t)
        PtrOp T.
  Proof.
    rewrite /typed_atomic_store /FindCreditStore /fast_lia_hint.
    iIntros "(%Halive & %Hbpa & Ha) Hv_ptr Hv_val".
    iDestruct "Ha" as ([c a]) "(Hstore & %Hn & HT)". simpl.
    iIntros (s fn R ϝ) "Hcont".
    iIntros (Ψ) "#(LFT & LLCTX) #HE HL Hf HΨ".
    iEval (rewrite /ty_own_val /=) in "Hv_ptr".
    iDestruct "Hv_ptr" as "(%l & %ly & %r' & %Hm & %Hv_eq & %Halg & %Hly_loc & #Hlb & #Hsc & #Hrfn & #Hshr)".
    subst v_ptr.
    iEval (rewrite /ty_own_val /=) in "Hv_val".
    iDestruct "Hv_val" as "(%Hmeta_val & %Hv_val_eq & %Hin_usize_val)".
    iPoseProof (credit_store_scrounge 1 with "Hstore") as "(Hcred & Hstore)"; first lia.
    iPoseProof ("HT" with "Hstore") as "(%x & %Hr_eq & Hinv_new & HT)".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iMod (lctx_lft_alive_tok_noend κ with "HE HL") as (q') "(Hκ & HL & Hclose_lft)";
      [solve_ndisj | done | ].
    subst r.
    iDestruct "Hrfn" as "%Hrfn_eq". subst r'.
    iApply wps_assign.
    { left; done. }
    { apply val_to_of_loc. }
    iMod (shr_ref_at_ex_acc_ptr ⊤ with "LFT Hcred Hκ Hshr") as
      (l_stored) "(Hinv & Hpoints & Hclose)"; [solve_ndisj | solve_ndisj | ].
    iDestruct "Hpoints" as (v_old) "(Hmapsto & #Hown)".
    iEval (rewrite /ty_own_val /=) in "Hown".
    iDestruct "Hown" as "(%Hmeta & %Hv_old_eq & %Hin_usize)".
    apply syn_type_has_layout_ptr_inv in Halg. subst ly.
    iMod (fupd_mask_subseteq ∅) as "Hcl_rest"; first set_solver.
    iModIntro.
    iSplitR.
    { iPureIntro. rewrite /has_layout_val /ot_layout /=.
      apply val_to_loc_length. rewrite Hv_val_eq. eexists. apply val_to_of_loc. }
    iSplitL "Hmapsto".
    { iExists v_old. iFrame "Hmapsto". iPureIntro. split.
      - rewrite /has_layout_val /ot_layout /=.
        apply val_to_loc_length. rewrite Hv_old_eq. eexists. apply val_to_of_loc.
      - done. }
    iApply physical_step_intro. iNext. iIntros "Hmapsto".
    iMod "Hcl_rest" as "_".
    iMod ("Hclose" $! l_new with "[Hmapsto Hinv_new]") as "Hκ".
    { iFrame "Hinv_new". iExists v_val. iFrame "Hmapsto".
      rewrite /ty_own_val /=. iPureIntro.
      exact (conj Hmeta_val (conj Hv_val_eq Hin_usize_val)). }
    iMod ("Hclose_lft" with "Hκ HL") as "HL".
    iPoseProof ("HL_cl" with "HL") as "HL".
    by iApply ("Hcont" $! L with "HT [$LFT $LLCTX] HE HL Hf").
  Qed.

  Global Program Instance typed_atomic_store_val_atomic_ptr_inst E L f v_ptr v_val l_new κ r :
    TypedAtomicStoreVal E L f v_ptr (shr_ref κ (∃at; P, alias_ptr_t)) r v_val alias_ptr_t l_new PtrOp :=
    λ T, i2p (typed_atomic_store_atomic_ptr E L f v_ptr v_val l_new κ r T).
End atomic_store_ptr.

(** * Atomic RMW for ptr (Phase A: RmwXchg only) *)

Section atomic_rmw_ptr.
  Context `{!typeGS Σ}.
  Context {Y : RT} (P : at_ex_inv_def loc Y).

  Lemma typed_atomic_rmw_atomic_ptr E L f
      (v1 : val) (v2 : val) (l_arg : loc)
      (op : atomic_rmw_op)
      (κ : lft) (r : place_rfn Y)
      (T : typed_val_expr_cont_t) :
    ⌜lctx_lft_alive E L κ⌝ ∗
    ⌜((ot_layout PtrOp).(ly_size) ≤ bytes_per_addr)%nat⌝ ∗
    ⌜op = RmwXchg⌝ ∗
    find_in_context FindCreditStore (λ '(c, a),
      ⌜fast_lia_hint (1 ≤ c)⌝ ∗
      (credit_store (c - 1) a -∗
        ∃ x, ⌜r = #x⌝ ∗
        (∀ (l_old : loc) (v_old : val) (v_new : val),
          ⌜v_old = val_of_loc l_old⌝ -∗
          ⌜atomic_rmw_eval op PtrOp v_old v2 = Some v_new⌝ -∗
          ⌜val_to_loc v_new = Some l_arg⌝ -∗
          P.(at_inv_P) f.1 l_old x -∗
          P.(at_inv_P) f.1 l_arg x ∗
          T L v_old MetaNone loc alias_ptr_t l_old)))
    ⊢ typed_atomic_rmw E L f v1 (v1 ◁ᵥ{f.1, MetaNone} r @ shr_ref κ (∃at; P, alias_ptr_t))
                                v2 (v2 ◁ᵥ{f.1, MetaNone} l_arg @ alias_ptr_t)
                                op PtrOp T.
  Proof.
    rewrite /typed_atomic_rmw /FindCreditStore /fast_lia_hint.
    iIntros "(%Halive & %Hbpa & %Hop & Ha) Hv1 Hv2".
    iDestruct "Ha" as ([c a]) "(Hstore & %Hn & HT)". simpl.
    iIntros (Φ) "#(LFT & LLCTX) #HE HL Hf HΦ".
    iEval (rewrite /ty_own_val /=) in "Hv1".
    iDestruct "Hv1" as "(%l & %ly & %r' & %Hm & %Hv_eq & %Halg & %Hly_loc & #Hlb & #Hsc & #Hrfn & #Hshr)".
    subst v1.
    iEval (rewrite /ty_own_val /=) in "Hv2".
    iDestruct "Hv2" as "(%Hmeta_val & %Hv2_eq & %Hin_usize_val)".
    iPoseProof (credit_store_scrounge 1 with "Hstore") as "(Hcred & Hstore)"; first lia.
    iPoseProof ("HT" with "Hstore") as "(%x & %Hr_eq & HT)".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iMod (lctx_lft_alive_tok_noend κ with "HE HL") as (q') "(Hκ & HL & Hclose_lft)";
      [solve_ndisj | done | ].
    subst r.
    iDestruct "Hrfn" as "%Hrfn_eq". subst r'.
    iApply (wpe_atomic ⊤ (⊤ ∖ ↑shrN.@l)).
    iMod (shr_ref_at_ex_acc_ptr ⊤ with "LFT Hcred Hκ Hshr") as
      (l_old) "(Hinv & Hpoints & Hclose)"; [solve_ndisj | solve_ndisj | ].
    iDestruct "Hpoints" as (v_old) "(Hmapsto & #Hown)".
    iEval (rewrite /ty_own_val /=) in "Hown".
    iDestruct "Hown" as "(%Hmeta & %Hv_old_eq & %Hin_usize)".
    apply syn_type_has_layout_ptr_inv in Halg. subst ly.
    (* For RmwXchg: v_new = v2 *)
    subst op.
    have Heval : atomic_rmw_eval RmwXchg PtrOp v_old v2 = Some v2 by done.
    have Hval_l_new : val_to_loc v2 = Some l_arg.
    { rewrite Hv2_eq. apply val_to_of_loc. }
    (* Layout facts *)
    have Hly_old : has_layout_val v_old (ot_layout PtrOp).
    { rewrite /has_layout_val /ot_layout /=. apply val_to_loc_length.
      rewrite Hv_old_eq. eexists. apply val_to_of_loc. }
    have Hly_arg : has_layout_val v2 (ot_layout PtrOp).
    { rewrite /has_layout_val /ot_layout /=. apply val_to_loc_length.
      rewrite Hv2_eq. eexists. apply val_to_of_loc. }
    iModIntro.
    iApply (wp_atomic_rmw RmwXchg _ _ v_old v2 with "Hmapsto").
    { apply val_to_of_loc. }
    { rewrite /ot_layout. done. }
    { exact Hly_old. }
    { exact Hly_arg. }
    { exact Hbpa. }
    { exact Heval. }
    { exact Hly_arg. }
    iApply physical_step_intro. iNext. iIntros "Hmapsto".
    iSpecialize ("HT" $! l_old v_old v2 with "[//] [//] [//] Hinv").
    iDestruct "HT" as "(Hinv_new & HT)".
    iMod ("Hclose" $! l_arg with "[Hmapsto Hinv_new]") as "Hκ".
    { iFrame "Hinv_new". iExists v2. iFrame "Hmapsto".
      rewrite /ty_own_val /=. iPureIntro.
      exact (conj Hmeta_val (conj Hv2_eq Hin_usize_val)). }
    iMod ("Hclose_lft" with "Hκ HL") as "HL".
    iPoseProof ("HL_cl" with "HL") as "HL".
    iAssert (v_old ◁ᵥ{f.1, MetaNone} l_old @ alias_ptr_t)%I as "Hv_ret".
    { rewrite /ty_own_val /=. iPureIntro. exact (conj Hmeta (conj Hv_old_eq Hin_usize)). }
    iModIntro. iApply ("HΦ" with "HL Hf Hv_ret [HT]").
    iExact "HT".
  Qed.

  Global Program Instance typed_atomic_rmw_val_atomic_ptr_inst E L f v1 v2 l_arg op κ r :
    TypedAtomicRmwVal E L f v1 (shr_ref κ (∃at; P, alias_ptr_t)) r v2 alias_ptr_t l_arg op PtrOp :=
    λ T, i2p (typed_atomic_rmw_atomic_ptr E L f v1 v2 l_arg op κ r T).
End atomic_rmw_ptr.

(** * CAS for ptr *)

Section cas_ptr.
  Context `{!typeGS Σ}.
  Context {Y : RT} (P : at_ex_inv_def loc Y).

  Lemma typed_cas_atomic_ptr E L f
      (v1 : val) (v2 : val) (l2 : loc) (v3 : val) (l3 : loc)
      (κ : lft) (r : place_rfn Y)
      (T : typed_val_expr_cont_t) :
    ⌜lctx_lft_alive E L κ⌝ ∗
    ⌜((ot_layout PtrOp).(ly_size) ≤ bytes_per_addr)%nat⌝ ∗
    find_in_context FindCreditStore (λ '(c, a),
      ⌜fast_lia_hint (1 ≤ c)⌝ ∗
      (credit_store (c - 1) a -∗
        ∃ x, ⌜r = #x⌝ ∗
        (∀ (l_old : loc) (v_old : val),
          ⌜v_old = val_of_loc l_old⌝ -∗
          P.(at_inv_P) f.1 l_old x -∗
          (⌜l_old.(loc_a) = l2.(loc_a)⌝ -∗
            P.(at_inv_P) f.1 l3 x ∗ T L v_old MetaNone loc alias_ptr_t l_old) ∧
          (⌜l_old.(loc_a) ≠ l2.(loc_a)⌝ -∗
            P.(at_inv_P) f.1 l_old x ∗ T L v_old MetaNone loc alias_ptr_t l_old))))
    ⊢ typed_cas E L f v1 (v1 ◁ᵥ{f.1, MetaNone} r @ shr_ref κ (∃at; P, alias_ptr_t))
                         v2 (v2 ◁ᵥ{f.1, MetaNone} l2 @ alias_ptr_t)
                         v3 (v3 ◁ᵥ{f.1, MetaNone} l3 @ alias_ptr_t)
                         PtrOp T.
  Proof.
    rewrite /typed_cas /find_in_context /FindCreditStore /fast_lia_hint.
    iIntros "(%Halive & %Hbpa & Ha) Hv1 Hv2 Hv3".
    iDestruct "Ha" as ([c a]) "(Hstore & %Hn & HT)". simpl.
    iIntros (Φ) "#(LFT & LLCTX) #HE HL Hf HΦ".
    iEval (rewrite /ty_own_val /=) in "Hv1".
    iDestruct "Hv1" as "(%l & %ly & %r' & %Hm1 & %Hv1_eq & %Halg & %Hly_loc & #Hlb & #Hsc & #Hrfn & #Hshr)".
    subst v1.
    iEval (rewrite /ty_own_val /=) in "Hv2".
    iDestruct "Hv2" as "(%Hmeta2 & %Hv2_eq & %Hin_usize2)".
    iEval (rewrite /ty_own_val /=) in "Hv3".
    iDestruct "Hv3" as "(%Hmeta3 & %Hv3_eq & %Hin_usize3)".
    iPoseProof (credit_store_scrounge 1 with "Hstore") as "(Hcred & Hstore)"; first lia.
    iPoseProof ("HT" with "Hstore") as "(%x & %Hr_eq & HT)".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iMod (lctx_lft_alive_tok_noend κ with "HE HL") as (q') "(Hκ & HL & Hclose_lft)";
      [solve_ndisj | done | ].
    subst r. iDestruct "Hrfn" as "%Hrfn_eq". subst r'.
    apply syn_type_has_layout_ptr_inv in Halg. subst ly.
    iApply (wpe_atomic ⊤ (⊤ ∖ ↑shrN.@l)).
    iMod (shr_ref_at_ex_acc_ptr ⊤ with "LFT Hcred Hκ Hshr") as
      (l_old) "(Hinv & Hpoints & Hclose)"; [solve_ndisj | solve_ndisj | ].
    iDestruct "Hpoints" as (vo) "(Hl & #Hown)".
    iEval (rewrite /ty_own_val /=) in "Hown".
    iDestruct "Hown" as "(%Hmeta & %Hvo_eq & %Hin_usize)".
    (* Pre-compute layout facts *)
    have Hval_l_old : val_to_loc vo = Some l_old.
    { rewrite Hvo_eq. apply val_to_of_loc. }
    have Hval_l2 : val_to_loc v2 = Some l2.
    { rewrite Hv2_eq. apply val_to_of_loc. }
    have Hly_vo : has_layout_val vo (ot_layout PtrOp).
    { rewrite /has_layout_val /ot_layout /=. apply val_to_loc_length. by eexists. }
    have Hly_ve : has_layout_val v2 (ot_layout PtrOp).
    { rewrite /has_layout_val /ot_layout /=. apply val_to_loc_length. by eexists. }
    have Hlen_vd : length v3 = (ot_layout PtrOp).(ly_size).
    { rewrite /ot_layout /=. apply val_to_loc_length.
      rewrite Hv3_eq. eexists. apply val_to_of_loc. }
    (* val_to_Z_ot PtrOp = loc_a <$> val_to_loc *)
    have Hzot_vo : val_to_Z_ot vo PtrOp = Some (l_old.(loc_a)).
    { rewrite /val_to_Z_ot Hval_l_old /=. done. }
    have Hzot_v2 : val_to_Z_ot v2 PtrOp = Some (l2.(loc_a)).
    { rewrite /val_to_Z_ot Hval_l2 /=. done. }
    iSpecialize ("HT" $! l_old vo with "[//] Hinv").
    iModIntro.
    destruct (decide (l_old.(loc_a) = l2.(loc_a))) as [Heq | Hneq].
    - (* SUCCESS *)
      iApply (wp_cas_suc _ v2 v3 vo (l_old.(loc_a)) (l2.(loc_a)) with "Hl").
      { apply val_to_of_loc. }
      { rewrite /ot_layout. done. }
      { exact Hzot_vo. }
      { exact Hzot_v2. }
      { exact Hly_ve. }
      { exact Hlen_vd. }
      { exact Hbpa. }
      { exact Heq. }
      iApply physical_step_intro. iNext. iIntros "Hl_new".
      iDestruct "HT" as "[HT_suc _]".
      iDestruct ("HT_suc" with "[//]") as "(Hinv_new & HT)".
      iMod ("Hclose" $! l3 with "[Hl_new Hinv_new]") as "Hκ".
      { iFrame "Hinv_new". iExists v3. iFrame "Hl_new".
        rewrite /ty_own_val /=. iPureIntro.
        exact (conj Hmeta3 (conj Hv3_eq Hin_usize3)). }
      iMod ("Hclose_lft" with "Hκ HL") as "HL".
      iPoseProof ("HL_cl" with "HL") as "HL".
      iAssert (vo ◁ᵥ{f.1, MetaNone} l_old @ alias_ptr_t)%I as "Hv_ret".
      { rewrite /ty_own_val /=. iPureIntro. exact (conj Hmeta (conj Hvo_eq Hin_usize)). }
      iModIntro. iApply ("HΦ" with "HL Hf Hv_ret [HT]").
      iExact "HT".
    - (* FAILURE *)
      iApply (wp_cas_fail _ v2 v3 vo (l_old.(loc_a)) (l2.(loc_a)) with "Hl").
      { apply val_to_of_loc. }
      { rewrite /ot_layout. done. }
      { exact Hzot_vo. }
      { exact Hzot_v2. }
      { exact Hly_ve. }
      { exact Hlen_vd. }
      { exact Hbpa. }
      { exact Hneq. }
      iApply physical_step_intro. iNext. iIntros "Hl_same".
      iDestruct "HT" as "[_ HT_fail]".
      iDestruct ("HT_fail" with "[//]") as "(Hinv_same & HT)".
      iMod ("Hclose" $! l_old with "[Hl_same Hinv_same]") as "Hκ".
      { iFrame "Hinv_same". iExists vo. iFrame "Hl_same".
        rewrite /ty_own_val /=. iPureIntro. exact (conj Hmeta (conj Hvo_eq Hin_usize)). }
      iMod ("Hclose_lft" with "Hκ HL") as "HL".
      iPoseProof ("HL_cl" with "HL") as "HL".
      iAssert (vo ◁ᵥ{f.1, MetaNone} l_old @ alias_ptr_t)%I as "Hv_ret".
      { rewrite /ty_own_val /=. iPureIntro. exact (conj Hmeta (conj Hvo_eq Hin_usize)). }
      iModIntro. iApply ("HΦ" with "HL Hf Hv_ret [HT]").
      iExact "HT".
  Qed.

  Global Program Instance typed_cas_val_atomic_ptr_inst E L f v1 r v2 l2 v3 l3 κ :
    TypedCasVal E L f v1 (shr_ref κ (∃at; P, alias_ptr_t)) r v2 alias_ptr_t l2 v3 alias_ptr_t l3 PtrOp :=
    λ T, i2p (typed_cas_atomic_ptr E L f v1 v2 l2 v3 l3 κ r T).
End cas_ptr.
