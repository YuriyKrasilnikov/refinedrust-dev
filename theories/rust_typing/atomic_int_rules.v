From refinedrust Require Export atomic_int.
From refinedrust Require Import int alias_ptr shr_ref options.

(** Typing rules for atomic operations on [at_ex_plain_t]-wrapped integer types.

    Provides [TypedAtomicLoadVal], [TypedAtomicStoreVal], [TypedAtomicRmwVal],
    and [TypedCasVal] instances that handle invariant opening, WP application,
    and invariant closing. Generic over the invariant [P], covering
    [atomic_int_t it] and any custom [at_ex_plain_t] over [int it]. *)

(** * Helper: [wp_atomic] lifted to sealed [WPe] level *)

Section wpe_atomic_helper.
  Context `{!typeGS Σ}.

  (** Avoids the unseal/reseal problem when applying [wp_atomic] in a context
      where the goal is sealed [WPe]. Without this wrapper, [iApply wp_atomic]
      unfolds [expr_wp_def] during unification, leaving a raw [WP] goal that
      cannot be re-sealed for subsequent lemmas like [wp_deref]. *)
  Lemma wpe_atomic E1 E2 e π Φ
      `{!Atomic (stuckness_to_atomicity NotStuck) (to_rtexpr π e)} :
    (|={E1,E2}=> expr_wp E2 π (λ v, |={E2,E1}=> Φ v) e) ⊢ expr_wp E1 π Φ e.
  Proof.
    rewrite !expr_wp_unfold /expr_wp_def.
    exact (wp_atomic NotStuck E1 E2 (to_rtexpr π e) Φ).
  Qed.
End wpe_atomic_helper.

(** * Atomic load *)

Section atomic_load.
  Context `{!typeGS Σ}.
  Context {Y : RT} (P : at_ex_inv_def Z Y).

  (** Helper: open atomic invariant directly from [shr_ref]'s persistent [ty_shr].
      Avoids constructing [l ◁ₗ[Shared κ]] which causes [ty_shr] folding/unfolding
      mismatch in the Iris proof mode.  Replicates the logic of [at_ex_plain_t_acc_shared]
      but takes the persistent [ty_shr] hypothesis directly. *)
  Lemma shr_ref_at_ex_acc E (it : int_type) (κ : lft) (π : thread_id)
      (r' : Y) (l : loc) (q : Qp) :
    lftE ⊆ E ∖ ↑(shrN.@l) →
    ↑(shrN.@l) ⊆ E →
    lft_ctx -∗
    £ 1 -∗
    q.[κ] -∗
    (□ |={lftE}=> ty_shr (∃at; P, int it) κ π r' MetaNone l)
    ={E, E∖↑(shrN.@l)}=∗
    ∃ (z : Z),
      P.(at_inv_P) π z r' ∗
      (l ↦: ty_own_val (int it) π z MetaNone) ∗
      (∀ z' : Z,
          (l ↦: ty_own_val (int it) π z' MetaNone) ∗ P.(at_inv_P) π z' r'
          ={E∖↑(shrN.@l), E}=∗ q.[κ]).
  Proof.
    iIntros (??) "#LFT Hcred Hκ #Hshr".
    iMod (fupd_mask_mono lftE with "Hshr") as "Hshr'"; first set_solver.
    iEval (unfold ty_shr, at_ex_plain_t) in "Hshr'".
    iDestruct "Hshr'" as "(Hsc & #Hbor & %ly & %Hly & %Halg)".
    iMod (rr_at_bor_acc with "LFT Hbor Hκ") as "(HP & Hvs)"; [done..|].
    iApply (lc_fupd_add_later with "Hcred").
    do 2 iModIntro.
    iDestruct "HP" as (z) "(Hmapsto & HP)".
    iExists z. iFrame.
    iIntros (z') "(Hmapsto & HP)".
    iApply ("Hvs" with "[Hmapsto HP]").
    iNext. iExists z'. iFrame.
  Qed.

  (** Atomic load through a shared reference to [at_ex_plain_t]-wrapped integer.
      Accepts [shr_ref κ (∃at; P, int it)] directly — this is what the automation
      produces when evaluating [move{PtrOp}("__3")] for a shared reference to an
      atomic type.

      Phase 1: unfold [shr_ref] value ownership → extract location [l] and
               persistent [ty_shr] of [at_ex_plain_t].
      Phase 2: open atomic invariant via [rr_at_bor_acc] under reduced mask.
      Phase 3: [wp_deref ScOrd] — read value atomically.
      Phase 4: close invariant, restore lifetime, pass to continuation. *)
  Lemma typed_atomic_load_atomic_int E L f (it : int_type)
      (v : val) (κ : lft) (r : place_rfn Y)
      (T : typed_val_expr_cont_t) :
    ⌜lctx_lft_alive E L κ⌝ ∗
    find_in_context FindCreditStore (λ '(c, a),
      ⌜fast_lia_hint (1 ≤ c)⌝ ∗
      (credit_store (c - 1) a -∗
        ∀ (z : Z) (v_loaded : val),
          ⌜val_to_Z v_loaded it = Some z⌝ -∗
          T L v_loaded MetaNone Z (int it) z))
    ⊢ typed_atomic_load E L f v
        (v ◁ᵥ{f.1, MetaNone} r @ shr_ref κ (∃at; P, int it))
        (IntOp it) T.
  Proof.
    (** Phase 1 — Setup: unfold [shr_ref], extract location and [ty_shr] *)
    rewrite /typed_atomic_load /FindCreditStore /fast_lia_hint.
    iIntros "(%Halive & Ha) Hv".
    iDestruct "Ha" as ([c a]) "(Hstore & %Hn & HT)". simpl.
    iIntros (Φ) "#(LFT & LLCTX) #HE HL Hf HΦ".
    (* Unfold shr_ref value ownership *)
    iEval (rewrite /ty_own_val /=) in "Hv".
    iDestruct "Hv" as "(%l & %ly & %r' & %Hm & %Hv_eq & %Halg & %Hly_loc & #Hlb & #Hsc & #Hrfn & #Hshr)".
    subst v.
    iPoseProof (credit_store_scrounge 1 with "Hstore") as "(Hcred & Hstore)"; first lia.
    iPoseProof ("HT" with "Hstore") as "HT".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iMod (lctx_lft_alive_tok_noend κ with "HE HL") as (q') "(Hκ & HL & Hclose_lft)";
      [solve_ndisj | done | ].

    (** Phase 2 — Open: open atomic invariant directly from [Hshr] *)
    iApply (wpe_atomic ⊤ (⊤ ∖ ↑shrN.@l)).
    iMod (shr_ref_at_ex_acc ⊤ with "LFT Hcred Hκ Hshr") as
      (z) "(Hinv & Hpoints & Hclose)"; [solve_ndisj | solve_ndisj | ].
    iDestruct "Hpoints" as (v_old) "(Hmapsto & #Hown)".
    iEval (rewrite /ty_own_val /=) in "Hown".
    iDestruct "Hown" as "(%Hmeta & %Hval_z)".
    (* has_layout_loc: already known from shr_ref unfolding *)
    apply syn_type_has_layout_int_inv in Halg. subst ly.
    iModIntro.

    (** Phase 3 — Operate: [wp_deref ScOrd] *)
    iApply (wp_deref _ _ _ l (IntOp it) 1 f.1 _ ScOrd with "Hmapsto").
    { left; done. }
    { apply val_to_of_loc. }
    { rewrite /ot_layout. done. }
    { apply val_to_Z_length in Hval_z.
      rewrite /has_layout_val /ot_layout /it_layout /ly_size. lia. }
    iApply physical_step_intro. iNext. iIntros (st) "Hmapsto".

    (** Phase 4 — Close: atomic borrow, lifetime, continuation *)
    iMod ("Hclose" $! z with "[Hmapsto Hinv]") as "Hκ".
    { iFrame "Hinv". iExists v_old. iFrame "Hmapsto".
      rewrite /ty_own_val /=. iPureIntro. split; done. }
    iMod ("Hclose_lft" with "Hκ HL") as "HL".
    iPoseProof ("HL_cl" with "HL") as "HL".
    rewrite (mem_cast_id_int _ _ _ Hval_z).
    iAssert (v_old ◁ᵥ{f.1, MetaNone} z @ (int it))%I as "Hv_ret".
    { rewrite /ty_own_val /=. iPureIntro. exact (conj Hmeta Hval_z). }
    iModIntro. iApply ("HΦ" with "HL Hf Hv_ret [HT]").
    { iApply ("HT" $! z v_old with "[//]"). }
  Qed.

  Global Program Instance typed_atomic_load_val_atomic_int_inst E L f it v κ r :
    TypedAtomicLoadVal E L f v (shr_ref κ (∃at; P, int it)) r (IntOp it) :=
    λ T, i2p (typed_atomic_load_atomic_int E L f it v κ r T).
End atomic_load.

(** * Atomic store *)

Section atomic_store.
  Context `{!typeGS Σ}.
  Context {Y : RT} (P : at_ex_inv_def Z Y).

  (** Atomic store through a shared reference to [at_ex_plain_t]-wrapped integer.
      Accepts [shr_ref κ (∃at; P, int it)] directly — this is what the automation
      produces when evaluating [move{PtrOp}("__3")] for a shared reference to an
      atomic type.

      Phase 1: unfold [shr_ref] value ownership → extract location [l] and
               persistent [ty_shr] of [at_ex_plain_t].
      Phase 2: open atomic invariant via [shr_ref_at_ex_acc] under reduced mask,
               apply [wps_assign].
      Phase 3: physical step — write [v_val] to [l].
      Phase 4: close invariant, restore lifetime, pass to continuation. *)
  Lemma typed_atomic_store_atomic_int E L f (it : int_type)
      (v_ptr : val) (v_val : val) (n : Z)
      (κ : lft) (r : place_rfn Y)
      (T : typed_write_cont_t) :
    ⌜lctx_lft_alive E L κ⌝ ∗
    find_in_context FindCreditStore (λ '(c, a),
      ⌜fast_lia_hint (1 ≤ c)⌝ ∗
      (credit_store (c - 1) a -∗
        ∃ x, ⌜r = #x⌝ ∗ P.(at_inv_P) f.1 n x ∗ T L))
    ⊢ typed_atomic_store E L f
        v_ptr (v_ptr ◁ᵥ{f.1, MetaNone} r @ shr_ref κ (∃at; P, int it))
        v_val (v_val ◁ᵥ{f.1, MetaNone} n @ int it)
        (IntOp it) T.
  Proof.
    (** Phase 1 — Setup: unfold [shr_ref], extract location and [ty_shr] *)
    rewrite /typed_atomic_store /FindCreditStore /fast_lia_hint.
    iIntros "(%Halive & Ha) Hv_ptr Hv_val".
    iDestruct "Ha" as ([c a]) "(Hstore & %Hn & HT)". simpl.
    iIntros (s fn R ϝ) "Hcont".
    iIntros (Ψ) "#(LFT & LLCTX) #HE HL Hf HΨ".
    (* Unfold shr_ref value ownership *)
    iEval (rewrite /ty_own_val /=) in "Hv_ptr".
    iDestruct "Hv_ptr" as "(%l & %ly & %r' & %Hm & %Hv_eq & %Halg & %Hly_loc & #Hlb & #Hsc & #Hrfn & #Hshr)".
    subst v_ptr.
    iEval (rewrite /ty_own_val /=) in "Hv_val".
    iDestruct "Hv_val" as "(%Hmeta_val & %Hval_z_val)".
    iPoseProof (credit_store_scrounge 1 with "Hstore") as "(Hcred & Hstore)"; first lia.
    iPoseProof ("HT" with "Hstore") as "(%x & %Hr_eq & Hinv_new & HT)".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iMod (lctx_lft_alive_tok_noend κ with "HE HL") as (q') "(Hκ & HL & Hclose_lft)";
      [solve_ndisj | done | ].
    (* Link r' to x via place_rfn_interp_shared *)
    subst r.
    iDestruct "Hrfn" as "%Hrfn_eq". subst r'.

    (** Phase 2 — Apply [wps_assign], open invariant under reduced mask *)
    iApply wps_assign.
    { left; done. }
    { apply val_to_of_loc. }
    (* Open invariant: ⊤ → ⊤∖↑(shrN.@l) *)
    iMod (shr_ref_at_ex_acc ⊤ with "LFT Hcred Hκ Hshr") as
      (z) "(Hinv & Hpoints & Hclose)"; [solve_ndisj | solve_ndisj | ].
    iDestruct "Hpoints" as (v_old) "(Hmapsto & #Hown)".
    iEval (rewrite /ty_own_val /=) in "Hown".
    iDestruct "Hown" as "(%Hmeta & %Hval_z)".
    (* has_layout_loc: already known from shr_ref unfolding *)
    apply syn_type_has_layout_int_inv in Halg. subst ly.
    (* Reduce mask further: ⊤∖↑N → ∅ *)
    iMod (fupd_mask_subseteq ∅) as "Hcl_rest"; first set_solver.
    iModIntro.
    (* Provide: ⌜has_layout_val v_val⌝ ∗ l↦|ly| *)
    iSplitR.
    { iPureIntro. apply val_to_Z_length in Hval_z_val.
      rewrite /has_layout_val /ot_layout /it_layout /ly_size. lia. }
    iSplitL "Hmapsto".
    { iExists v_old. iFrame "Hmapsto". iPureIntro. split.
      - apply val_to_Z_length in Hval_z.
        rewrite /has_layout_val /ot_layout /it_layout /ly_size. lia.
      - done. }

    (** Phase 3 — Physical step: write [v_val] to [l] *)
    iApply physical_step_intro. iNext. iIntros "Hmapsto".

    (** Phase 4 — Close: invariant, lifetime, continuation *)
    (* Restore mask: ∅ → ⊤∖↑N *)
    iMod "Hcl_rest" as "_".
    (* Close invariant with new value n: ⊤∖↑N → ⊤ *)
    iMod ("Hclose" $! n with "[Hmapsto Hinv_new]") as "Hκ".
    { iFrame "Hinv_new". iExists v_val. iFrame "Hmapsto".
      rewrite /ty_own_val /=. iPureIntro. split; done. }
    iMod ("Hclose_lft" with "Hκ HL") as "HL".
    iPoseProof ("HL_cl" with "HL") as "HL".
    by iApply ("Hcont" $! L with "HT [$LFT $LLCTX] HE HL Hf").
  Qed.

  Global Program Instance typed_atomic_store_val_atomic_int_inst E L f it v_ptr v_val n κ r :
    TypedAtomicStoreVal E L f v_ptr (shr_ref κ (∃at; P, int it)) r v_val (int it) n (IntOp it) :=
    λ T, i2p (typed_atomic_store_atomic_int E L f it v_ptr v_val n κ r T).
End atomic_store.

(** * Atomic read-modify-write *)

Section atomic_rmw.
  Context `{!typeGS Σ}.
  Context {Y : RT} (P : at_ex_inv_def Z Y).

  (** One instance covers all RMW operations — [op] is universally quantified. *)
  Lemma typed_atomic_rmw_atomic_int E L f (it : int_type)
      (v1 : val) (l1 : loc) (v2 : val) (n_arg : Z)
      (op : atomic_rmw_op)
      (κ : lft) (x : Y)
      (T : typed_val_expr_cont_t) :
    ⌜lctx_lft_alive E L κ⌝ ∗
    l1 ◁ₗ[f.1, Shared κ] (#x) @ (◁ (∃at; P, int it)) ∗
    find_in_context FindCreditStore (λ '(c, a),
      ⌜fast_lia_hint (1 ≤ c)⌝ ∗
      (credit_store (c - 1) a -∗
        ∀ (r : Z) (v_old : val) (r_new : Z) (v_new : val),
          ⌜val_to_Z v_old it = Some r⌝ -∗
          ⌜atomic_rmw_eval op (IntOp it) v_old v2 = Some v_new⌝ -∗
          ⌜val_to_Z v_new it = Some r_new⌝ -∗
          P.(at_inv_P) f.1 r x -∗
          P.(at_inv_P) f.1 r_new x ∗
          T L v_old MetaNone Z (int it) r))
    ⊢ typed_atomic_rmw E L f v1 (v1 ◁ᵥ{f.1, MetaNone} l1 @ alias_ptr_t)
                                v2 (v2 ◁ᵥ{f.1, MetaNone} n_arg @ int it)
                                op (IntOp it) T.
  Proof.
  Admitted.

  Global Program Instance typed_atomic_rmw_val_atomic_int_inst E L f it v1 l1 v2 n_arg op κ x :
    TypedAtomicRmwVal E L f v1 alias_ptr_t l1 v2 (int it) n_arg op (IntOp it) :=
    λ T, i2p (typed_atomic_rmw_atomic_int E L f it v1 l1 v2 n_arg op κ x T).
End atomic_rmw.

(** * Compare-and-swap *)

Section cas.
  Context `{!typeGS Σ}.
  Context {Y : RT} (P : at_ex_inv_def Z Y).

  Lemma typed_cas_atomic_int E L f (it : int_type)
      (v1 : val) (l1 : loc) (v2 : val) (l2 : loc) (v3 : val) (n3 : Z)
      (κ : lft) (x : Y)
      (T : typed_val_expr_cont_t) :
    ⌜lctx_lft_alive E L κ⌝ ∗
    l1 ◁ₗ[f.1, Shared κ] (#x) @ (◁ (∃at; P, int it)) ∗
    find_in_context (FindLoc l2) (λ '(existT rt2 (lt2, r2, b2, π2)),
      ⌜π2 = f.1⌝ ∗
      find_in_context FindCreditStore (λ '(c, a),
        ⌜fast_lia_hint (1 ≤ c)⌝ ∗
        (credit_store (c - 1) a -∗
          (∀ (r : Z),
            P.(at_inv_P) f.1 r x -∗
            P.(at_inv_P) f.1 n3 x ∗
            T L (val_of_bool true) MetaNone bool bool_t true) ∧
          T L (val_of_bool false) MetaNone bool bool_t false)))
    ⊢ typed_cas E L f v1 (v1 ◁ᵥ{f.1, MetaNone} l1 @ alias_ptr_t)
                         v2 (v2 ◁ᵥ{f.1, MetaNone} l2 @ alias_ptr_t)
                         v3 (v3 ◁ᵥ{f.1, MetaNone} n3 @ int it)
                         (IntOp it) T.
  Proof.
  Admitted.

  Global Program Instance typed_cas_val_atomic_int_inst E L f it v1 l1 v2 l2 v3 n3 κ x :
    TypedCasVal E L f v1 alias_ptr_t l1 v2 alias_ptr_t l2 v3 (int it) n3 (IntOp it) :=
    λ T, i2p (typed_cas_atomic_int E L f it v1 l1 v2 l2 v3 n3 κ x T).
End cas.
