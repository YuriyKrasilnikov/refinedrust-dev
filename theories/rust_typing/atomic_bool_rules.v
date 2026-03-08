From refinedrust Require Export atomic_int atomic_int_rules.
From refinedrust Require Import int shr_ref options.

(** Typing rules for atomic operations on [at_ex_plain_t]-wrapped bool types.

    Provides [TypedAtomicLoadVal], [TypedAtomicStoreVal], [TypedAtomicRmwVal],
    and [TypedCasVal] instances for [bool_t] with [BoolOp]. *)

(** * Helper: open atomic invariant from [shr_ref] for bool *)

Section shr_ref_at_ex_acc_bool.
  Context `{!typeGS Σ}.
  Context {Y : RT} (P : at_ex_inv_def bool Y).

  Lemma shr_ref_at_ex_acc_bool E (κ : lft) (π : thread_id)
      (r' : Y) (l : loc) (q : Qp) :
    lftE ⊆ E ∖ ↑(shrN.@l) →
    ↑(shrN.@l) ⊆ E →
    lft_ctx -∗
    £ 1 -∗
    q.[κ] -∗
    (□ |={lftE}=> ty_shr (∃at; P, bool_t) κ π r' MetaNone l)
    ={E, E∖↑(shrN.@l)}=∗
    ∃ (b : bool),
      P.(at_inv_P) π b r' ∗
      (l ↦: ty_own_val bool_t π b MetaNone) ∗
      (∀ b' : bool,
          (l ↦: ty_own_val bool_t π b' MetaNone) ∗ P.(at_inv_P) π b' r'
          ={E∖↑(shrN.@l), E}=∗ q.[κ]).
  Proof.
    iIntros (??) "#LFT Hcred Hκ #Hshr".
    iMod (fupd_mask_mono lftE with "Hshr") as "Hshr'"; first set_solver.
    iEval (unfold ty_shr, at_ex_plain_t) in "Hshr'".
    iDestruct "Hshr'" as "(Hsc & #Hbor & %ly & %Hly & %Halg)".
    iMod (rr_at_bor_acc with "LFT Hbor Hκ") as "(HP & Hvs)"; [done..|].
    iApply (lc_fupd_add_later with "Hcred").
    do 2 iModIntro.
    iDestruct "HP" as (b) "(Hmapsto & HP)".
    iExists b. iFrame.
    iIntros (b') "(Hmapsto & HP)".
    iApply ("Hvs" with "[Hmapsto HP]").
    iNext. iExists b'. iFrame.
  Qed.
End shr_ref_at_ex_acc_bool.

(** * Atomic load for bool *)

Section atomic_load_bool.
  Context `{!typeGS Σ}.
  Context {Y : RT} (P : at_ex_inv_def bool Y).

  Lemma typed_atomic_load_atomic_bool E L f
      (v : val) (κ : lft) (r : place_rfn Y)
      (T : typed_val_expr_cont_t) :
    ⌜lctx_lft_alive E L κ⌝ ∗
    ⌜((ot_layout BoolOp).(ly_size) ≤ bytes_per_addr)%nat⌝ ∗
    find_in_context FindCreditStore (λ '(c, a),
      ⌜fast_lia_hint (1 ≤ c)⌝ ∗
      (credit_store (c - 1) a -∗
        ∀ (b : bool) (v_loaded : val),
          ⌜val_to_bool v_loaded = Some b⌝ -∗
          T L v_loaded MetaNone bool bool_t b))
    ⊢ typed_atomic_load E L f v
        (v ◁ᵥ{f.1, MetaNone} r @ shr_ref κ (∃at; P, bool_t))
        BoolOp T.
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
    iMod (shr_ref_at_ex_acc_bool ⊤ with "LFT Hcred Hκ Hshr") as
      (b) "(Hinv & Hpoints & Hclose)"; [solve_ndisj | solve_ndisj | ].
    iDestruct "Hpoints" as (v_old) "(Hmapsto & #Hown)".
    iEval (rewrite /ty_own_val /=) in "Hown".
    iDestruct "Hown" as "(%Hmeta & %Hval_b)".
    apply syn_type_has_layout_bool_inv in Halg. subst ly.
    iModIntro.
    iApply (wp_deref _ _ _ l BoolOp 1 f.1 _ ScOrd with "Hmapsto").
    { left; done. }
    { apply val_to_of_loc. }
    { rewrite /ot_layout. done. }
    { apply val_to_bool_length in Hval_b.
      rewrite /has_layout_val /ot_layout /bool_layout /ly_size. lia. }
    iApply physical_step_intro. iNext. iIntros (st) "Hmapsto".
    iMod ("Hclose" $! b with "[Hmapsto Hinv]") as "Hκ".
    { iFrame "Hinv". iExists v_old. iFrame "Hmapsto".
      rewrite /ty_own_val /=. iPureIntro. split; done. }
    iMod ("Hclose_lft" with "Hκ HL") as "HL".
    iPoseProof ("HL_cl" with "HL") as "HL".
    rewrite (mem_cast_id_bool _ _ Hval_b).
    iAssert (v_old ◁ᵥ{f.1, MetaNone} b @ bool_t)%I as "Hv_ret".
    { rewrite /ty_own_val /=. iPureIntro. exact (conj Hmeta Hval_b). }
    iModIntro. iApply ("HΦ" with "HL Hf Hv_ret [HT]").
    { iApply ("HT" $! b v_old with "[//]"). }
  Qed.

  Global Program Instance typed_atomic_load_val_atomic_bool_inst E L f v κ r :
    TypedAtomicLoadVal E L f v (shr_ref κ (∃at; P, bool_t)) r BoolOp :=
    λ T, i2p (typed_atomic_load_atomic_bool E L f v κ r T).
End atomic_load_bool.

(** * Atomic store for bool *)

Section atomic_store_bool.
  Context `{!typeGS Σ}.
  Context {Y : RT} (P : at_ex_inv_def bool Y).

  Lemma typed_atomic_store_atomic_bool E L f
      (v_ptr : val) (v_val : val) (b_new : bool)
      (κ : lft) (r : place_rfn Y)
      (T : typed_write_cont_t) :
    ⌜lctx_lft_alive E L κ⌝ ∗
    ⌜((ot_layout BoolOp).(ly_size) ≤ bytes_per_addr)%nat⌝ ∗
    find_in_context FindCreditStore (λ '(c, a),
      ⌜fast_lia_hint (1 ≤ c)⌝ ∗
      (credit_store (c - 1) a -∗
        ∃ x, ⌜r = #x⌝ ∗ P.(at_inv_P) f.1 b_new x ∗ T L))
    ⊢ typed_atomic_store E L f
        v_ptr (v_ptr ◁ᵥ{f.1, MetaNone} r @ shr_ref κ (∃at; P, bool_t))
        v_val (v_val ◁ᵥ{f.1, MetaNone} b_new @ bool_t)
        BoolOp T.
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
    iDestruct "Hv_val" as "(%Hmeta_val & %Hval_b_val)".
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
    iMod (shr_ref_at_ex_acc_bool ⊤ with "LFT Hcred Hκ Hshr") as
      (b) "(Hinv & Hpoints & Hclose)"; [solve_ndisj | solve_ndisj | ].
    iDestruct "Hpoints" as (v_old) "(Hmapsto & #Hown)".
    iEval (rewrite /ty_own_val /=) in "Hown".
    iDestruct "Hown" as "(%Hmeta & %Hval_b)".
    apply syn_type_has_layout_bool_inv in Halg. subst ly.
    iMod (fupd_mask_subseteq ∅) as "Hcl_rest"; first set_solver.
    iModIntro.
    iSplitR.
    { iPureIntro. apply val_to_bool_length in Hval_b_val.
      rewrite /has_layout_val /ot_layout /bool_layout /ly_size. lia. }
    iSplitL "Hmapsto".
    { iExists v_old. iFrame "Hmapsto". iPureIntro. split.
      - apply val_to_bool_length in Hval_b.
        rewrite /has_layout_val /ot_layout /bool_layout /ly_size. lia.
      - done. }
    iApply physical_step_intro. iNext. iIntros "Hmapsto".
    iMod "Hcl_rest" as "_".
    iMod ("Hclose" $! b_new with "[Hmapsto Hinv_new]") as "Hκ".
    { iFrame "Hinv_new". iExists v_val. iFrame "Hmapsto".
      rewrite /ty_own_val /=. iPureIntro. split; done. }
    iMod ("Hclose_lft" with "Hκ HL") as "HL".
    iPoseProof ("HL_cl" with "HL") as "HL".
    by iApply ("Hcont" $! L with "HT [$LFT $LLCTX] HE HL Hf").
  Qed.

  Global Program Instance typed_atomic_store_val_atomic_bool_inst E L f v_ptr v_val b_new κ r :
    TypedAtomicStoreVal E L f v_ptr (shr_ref κ (∃at; P, bool_t)) r v_val bool_t b_new BoolOp :=
    λ T, i2p (typed_atomic_store_atomic_bool E L f v_ptr v_val b_new κ r T).
End atomic_store_bool.

(** * Atomic RMW for bool *)

Section atomic_rmw_bool.
  Context `{!typeGS Σ}.
  Context {Y : RT} (P : at_ex_inv_def bool Y).

  (** [atomic_rmw_eval] on bool types always succeeds for supported operations
      (Xchg, And, Or, Xor, Nand). *)
  Lemma atomic_rmw_eval_bool_total (op : atomic_rmw_op)
      (v_old v_arg : val) (b_old b_arg : bool) :
    val_to_bool v_old = Some b_old →
    val_to_bool v_arg = Some b_arg →
    op = RmwXchg ∨ op = RmwAnd ∨ op = RmwOr ∨ op = RmwXor ∨ op = RmwNand →
    ∃ v_new b_new,
      atomic_rmw_eval op BoolOp v_old v_arg = Some v_new ∧
      val_to_bool v_new = Some b_new.
  Proof.
    intros Hbo Hba Hop.
    destruct op; rewrite /atomic_rmw_eval;
      try (exfalso; destruct Hop as [|[|[|[|]]]]; discriminate).
    - (* RmwXchg *) eexists _, _. split; [done | exact Hba].
    - (* RmwAnd *) rewrite Hbo Hba /=.
      eexists _, _. split; [done | apply val_to_of_bool].
    - (* RmwOr *) rewrite Hbo Hba /=.
      eexists _, _. split; [done | apply val_to_of_bool].
    - (* RmwXor *) rewrite Hbo Hba /=.
      eexists _, _. split; [done | apply val_to_of_bool].
    - (* RmwNand *) rewrite Hbo Hba /=.
      eexists _, _. split; [done | apply val_to_of_bool].
  Qed.

  (** Atomic RMW through a shared reference to [at_ex_plain_t]-wrapped bool.
      Supports only [RmwXchg], [RmwAnd], [RmwOr], [RmwXor], [RmwNand] —
      the operations defined by [atomic_rmw_eval] for [BoolOp].
      Other ops (Add, Sub, Max, Min) cause stuck execution. *)
  Lemma typed_atomic_rmw_atomic_bool E L f
      (v1 : val) (v2 : val) (b_arg : bool)
      (op : atomic_rmw_op)
      (κ : lft) (r : place_rfn Y)
      (T : typed_val_expr_cont_t) :
    ⌜lctx_lft_alive E L κ⌝ ∗
    ⌜((ot_layout BoolOp).(ly_size) ≤ bytes_per_addr)%nat⌝ ∗
    ⌜op = RmwXchg ∨ op = RmwAnd ∨ op = RmwOr ∨ op = RmwXor ∨ op = RmwNand⌝ ∗
    find_in_context FindCreditStore (λ '(c, a),
      ⌜fast_lia_hint (1 ≤ c)⌝ ∗
      (credit_store (c - 1) a -∗
        ∃ x, ⌜r = #x⌝ ∗
        (∀ (b_old : bool) (v_old : val) (b_new : bool) (v_new : val),
          ⌜val_to_bool v_old = Some b_old⌝ -∗
          ⌜atomic_rmw_eval op BoolOp v_old v2 = Some v_new⌝ -∗
          ⌜val_to_bool v_new = Some b_new⌝ -∗
          P.(at_inv_P) f.1 b_old x -∗
          P.(at_inv_P) f.1 b_new x ∗
          T L v_old MetaNone bool bool_t b_old)))
    ⊢ typed_atomic_rmw E L f v1 (v1 ◁ᵥ{f.1, MetaNone} r @ shr_ref κ (∃at; P, bool_t))
                                v2 (v2 ◁ᵥ{f.1, MetaNone} b_arg @ bool_t)
                                op BoolOp T.
  Proof.
    rewrite /typed_atomic_rmw /FindCreditStore /fast_lia_hint.
    iIntros "(%Halive & %Hbpa & %Hop & Ha) Hv1 Hv2".
    iDestruct "Ha" as ([c a]) "(Hstore & %Hn & HT)". simpl.
    iIntros (Φ) "#(LFT & LLCTX) #HE HL Hf HΦ".
    iEval (rewrite /ty_own_val /=) in "Hv1".
    iDestruct "Hv1" as "(%l & %ly & %r' & %Hm & %Hv_eq & %Halg & %Hly_loc & #Hlb & #Hsc & #Hrfn & #Hshr)".
    subst v1.
    iEval (rewrite /ty_own_val /=) in "Hv2".
    iDestruct "Hv2" as "(%Hmeta_val & %Hval_b_val)".
    iPoseProof (credit_store_scrounge 1 with "Hstore") as "(Hcred & Hstore)"; first lia.
    iPoseProof ("HT" with "Hstore") as "(%x & %Hr_eq & HT)".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iMod (lctx_lft_alive_tok_noend κ with "HE HL") as (q') "(Hκ & HL & Hclose_lft)";
      [solve_ndisj | done | ].
    subst r.
    iDestruct "Hrfn" as "%Hrfn_eq". subst r'.
    iApply (wpe_atomic ⊤ (⊤ ∖ ↑shrN.@l)).
    iMod (shr_ref_at_ex_acc_bool ⊤ with "LFT Hcred Hκ Hshr") as
      (b_old) "(Hinv & Hpoints & Hclose)"; [solve_ndisj | solve_ndisj | ].
    iDestruct "Hpoints" as (v_old) "(Hmapsto & #Hown)".
    iEval (rewrite /ty_own_val /=) in "Hown".
    iDestruct "Hown" as "(%Hmeta & %Hval_b)".
    apply syn_type_has_layout_bool_inv in Halg. subst ly.
    (* Compute v_new via atomic_rmw_eval_bool_total *)
    have [v_new [b_new [Heval Hval_b_new]]] :=
      atomic_rmw_eval_bool_total op v_old v2 b_old b_arg Hval_b Hval_b_val Hop.
    (* Establish layout facts in pure Coq *)
    have Hly_old : has_layout_val v_old (ot_layout BoolOp)
      by (apply val_to_bool_length in Hval_b;
          rewrite /has_layout_val /ot_layout /bool_layout /ly_size; lia).
    have Hly_arg : has_layout_val v2 (ot_layout BoolOp)
      by (apply val_to_bool_length in Hval_b_val;
          rewrite /has_layout_val /ot_layout /bool_layout /ly_size; lia).
    have Hly_new : has_layout_val v_new (ot_layout BoolOp)
      by (apply val_to_bool_length in Hval_b_new;
          rewrite /has_layout_val /ot_layout /bool_layout /ly_size; lia).
    iModIntro.
    iApply (wp_atomic_rmw op _ _ v_old v_new with "Hmapsto").
    { apply val_to_of_loc. }
    { rewrite /ot_layout. done. }
    { exact Hly_old. }
    { exact Hly_arg. }
    { exact Hbpa. }
    { exact Heval. }
    { exact Hly_new. }
    iApply physical_step_intro. iNext. iIntros "Hmapsto".
    iSpecialize ("HT" $! b_old v_old b_new v_new with "[//] [//] [//] Hinv").
    iDestruct "HT" as "(Hinv_new & HT)".
    iMod ("Hclose" $! b_new with "[Hmapsto Hinv_new]") as "Hκ".
    { iFrame "Hinv_new". iExists v_new. iFrame "Hmapsto".
      rewrite /ty_own_val /=. iPureIntro. split; done. }
    iMod ("Hclose_lft" with "Hκ HL") as "HL".
    iPoseProof ("HL_cl" with "HL") as "HL".
    iAssert (v_old ◁ᵥ{f.1, MetaNone} b_old @ bool_t)%I as "Hv_ret".
    { rewrite /ty_own_val /=. iPureIntro. exact (conj Hmeta Hval_b). }
    iModIntro. iApply ("HΦ" with "HL Hf Hv_ret [HT]").
    iExact "HT".
  Qed.

  Global Program Instance typed_atomic_rmw_val_atomic_bool_inst E L f v1 v2 b_arg op κ r :
    TypedAtomicRmwVal E L f v1 (shr_ref κ (∃at; P, bool_t)) r v2 bool_t b_arg op BoolOp :=
    λ T, i2p (typed_atomic_rmw_atomic_bool E L f v1 v2 b_arg op κ r T).
End atomic_rmw_bool.

(** * CAS for bool *)

Section cas_bool.
  Context `{!typeGS Σ}.
  Context {Y : RT} (P : at_ex_inv_def bool Y).

  Lemma typed_cas_atomic_bool E L f
      (v1 : val) (v2 : val) (b2 : bool) (v3 : val) (b3 : bool)
      (κ : lft) (r : place_rfn Y)
      (T : typed_val_expr_cont_t) :
    ⌜lctx_lft_alive E L κ⌝ ∗
    ⌜((ot_layout BoolOp).(ly_size) ≤ bytes_per_addr)%nat⌝ ∗
    find_in_context FindCreditStore (λ '(c, a),
      ⌜fast_lia_hint (1 ≤ c)⌝ ∗
      (credit_store (c - 1) a -∗
        ∃ x, ⌜r = #x⌝ ∗
        (∀ (b_old : bool) (v_old : val),
          ⌜val_to_bool v_old = Some b_old⌝ -∗
          P.(at_inv_P) f.1 b_old x -∗
          (⌜bool_to_Z b_old = bool_to_Z b2⌝ -∗
            P.(at_inv_P) f.1 b3 x ∗ T L v_old MetaNone bool bool_t b_old) ∧
          (⌜bool_to_Z b_old ≠ bool_to_Z b2⌝ -∗
            P.(at_inv_P) f.1 b_old x ∗ T L v_old MetaNone bool bool_t b_old))))
    ⊢ typed_cas E L f v1 (v1 ◁ᵥ{f.1, MetaNone} r @ shr_ref κ (∃at; P, bool_t))
                         v2 (v2 ◁ᵥ{f.1, MetaNone} b2 @ bool_t)
                         v3 (v3 ◁ᵥ{f.1, MetaNone} b3 @ bool_t)
                         BoolOp T.
  Proof.
    rewrite /typed_cas /find_in_context /FindCreditStore /fast_lia_hint.
    iIntros "(%Halive & %Hbpa & Ha) Hv1 Hv2 Hv3".
    iDestruct "Ha" as ([c a]) "(Hstore & %Hn & HT)". simpl.
    iIntros (Φ) "#(LFT & LLCTX) #HE HL Hf HΦ".
    iEval (rewrite /ty_own_val /=) in "Hv1".
    iDestruct "Hv1" as "(%l & %ly & %r' & %Hm1 & %Hv1_eq & %Halg & %Hly_loc & #Hlb & #Hsc & #Hrfn & #Hshr)".
    subst v1.
    iEval (rewrite /ty_own_val /=) in "Hv2".
    iDestruct "Hv2" as "(%Hmeta2 & %Hval_b2)".
    iEval (rewrite /ty_own_val /=) in "Hv3".
    iDestruct "Hv3" as "(%Hmeta3 & %Hval_b3)".
    iPoseProof (credit_store_scrounge 1 with "Hstore") as "(Hcred & Hstore)"; first lia.
    iPoseProof ("HT" with "Hstore") as "(%x & %Hr_eq & HT)".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iMod (lctx_lft_alive_tok_noend κ with "HE HL") as (q') "(Hκ & HL & Hclose_lft)";
      [solve_ndisj | done | ].
    subst r. iDestruct "Hrfn" as "%Hrfn_eq". subst r'.
    apply syn_type_has_layout_bool_inv in Halg. subst ly.
    iApply (wpe_atomic ⊤ (⊤ ∖ ↑shrN.@l)).
    iMod (shr_ref_at_ex_acc_bool ⊤ with "LFT Hcred Hκ Hshr") as
      (b_old) "(Hinv & Hpoints & Hclose)"; [solve_ndisj | solve_ndisj | ].
    iDestruct "Hpoints" as (vo) "(Hl & #Hown)".
    iEval (rewrite /ty_own_val /=) in "Hown".
    iDestruct "Hown" as "(%Hmeta & %Hval_b)".
    (* Pre-compute layout facts *)
    have Hly_vo : has_layout_val vo (ot_layout BoolOp)
      by (apply val_to_bool_length in Hval_b;
          rewrite /has_layout_val /ot_layout /bool_layout /ly_size; lia).
    have Hly_ve : has_layout_val v2 (ot_layout BoolOp)
      by (apply val_to_bool_length in Hval_b2;
          rewrite /has_layout_val /ot_layout /bool_layout /ly_size; lia).
    have Hlen_vd : length v3 = (ot_layout BoolOp).(ly_size)
      by (apply val_to_bool_length in Hval_b3;
          rewrite /ot_layout /bool_layout /ly_size; lia).
    (* val_to_Z_ot BoolOp = bool_to_Z <$> val_to_bool *)
    have Hzot_vo : val_to_Z_ot vo BoolOp = Some (bool_to_Z b_old)
      by (rewrite /val_to_Z_ot Hval_b /=; done).
    have Hzot_v2 : val_to_Z_ot v2 BoolOp = Some (bool_to_Z b2)
      by (rewrite /val_to_Z_ot Hval_b2 /=; done).
    iSpecialize ("HT" $! b_old vo with "[//] Hinv").
    iModIntro.
    destruct (decide (bool_to_Z b_old = bool_to_Z b2)) as [Heq | Hneq].
    - (* SUCCESS *)
      iApply (wp_cas_suc _ v2 v3 vo (bool_to_Z b_old) (bool_to_Z b2) with "Hl").
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
      iMod ("Hclose" $! b3 with "[Hl_new Hinv_new]") as "Hκ".
      { iFrame "Hinv_new". iExists v3. iFrame "Hl_new".
        rewrite /ty_own_val /=. iPureIntro. split; done. }
      iMod ("Hclose_lft" with "Hκ HL") as "HL".
      iPoseProof ("HL_cl" with "HL") as "HL".
      iAssert (vo ◁ᵥ{f.1, MetaNone} b_old @ bool_t)%I as "Hv_ret".
      { rewrite /ty_own_val /=. iPureIntro. exact (conj Hmeta Hval_b). }
      iModIntro. iApply ("HΦ" with "HL Hf Hv_ret [HT]").
      iExact "HT".
    - (* FAILURE *)
      iApply (wp_cas_fail _ v2 v3 vo (bool_to_Z b_old) (bool_to_Z b2) with "Hl").
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
      iMod ("Hclose" $! b_old with "[Hl_same Hinv_same]") as "Hκ".
      { iFrame "Hinv_same". iExists vo. iFrame "Hl_same".
        rewrite /ty_own_val /=. iPureIntro. split; done. }
      iMod ("Hclose_lft" with "Hκ HL") as "HL".
      iPoseProof ("HL_cl" with "HL") as "HL".
      iAssert (vo ◁ᵥ{f.1, MetaNone} b_old @ bool_t)%I as "Hv_ret".
      { rewrite /ty_own_val /=. iPureIntro. exact (conj Hmeta Hval_b). }
      iModIntro. iApply ("HΦ" with "HL Hf Hv_ret [HT]").
      iExact "HT".
  Qed.

  Global Program Instance typed_cas_val_atomic_bool_inst E L f v1 r v2 b2 v3 b3 κ :
    TypedCasVal E L f v1 (shr_ref κ (∃at; P, bool_t)) r v2 bool_t b2 v3 bool_t b3 BoolOp :=
    λ T, i2p (typed_cas_atomic_bool E L f v1 v2 b2 v3 b3 κ r T).
End cas_bool.
