From refinedrust Require Export atomic_int.
From refinedrust Require Import int alias_ptr options.

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

  Lemma typed_atomic_load_atomic_int E L f (it : int_type)
      (v : val) (l : loc) (κ : lft) (x : Y)
      (T : typed_val_expr_cont_t) :
    ⌜lctx_lft_alive E L κ⌝ ∗
    l ◁ₗ[f.1, Shared κ] (#x) @ (◁ (∃at; P, int it)) ∗
    find_in_context FindCreditStore (λ '(c, a),
      ⌜fast_lia_hint (1 ≤ c)⌝ ∗
      (credit_store (c - 1) a -∗
        ∀ (r : Z) (v_loaded : val),
          ⌜val_to_Z v_loaded it = Some r⌝ -∗
          T L v_loaded MetaNone Z (int it) r))
    ⊢ typed_atomic_load E L f v (v ◁ᵥ{f.1, MetaNone} l @ alias_ptr_t)
                                (IntOp it) T.
  Proof.
    (** Phase 1 — Setup: unfold, enter WP, acquire resources *)
    rewrite /typed_atomic_load /FindCreditStore /fast_lia_hint.
    iIntros "(%Halive & #Hl & Ha) Hv".
    iDestruct "Ha" as ([c a]) "(Hstore & %Hn & HT)". simpl.
    iIntros (Φ) "#(LFT & LLCTX) #HE HL Hf HΦ".
    iMod (learn_from_hyp_proof with "[] Hv") as "(Hv & #(%_ & %Hval & %Husize))".
    { iPureIntro. solve_ndisj. }
    subst v.
    iPoseProof (credit_store_scrounge 1 with "Hstore") as "(Hcred & Hstore)"; first lia.
    iPoseProof ("HT" with "Hstore") as "HT".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iMod (lctx_lft_alive_tok_noend κ with "HE HL") as (q') "(Hκ & HL & Hclose_lft)";
      [solve_ndisj | done | ].

    (** Phase 2 — Open: atomic invariant under reduced mask *)
    iApply (wpe_atomic ⊤ (⊤ ∖ ↑shrN.@l)).
    iMod (at_ex_plain_t_acc_shared ⊤ with "LFT Hcred Hκ Hl") as
      (r) "(Hinv & Hpoints & Hclose)"; [solve_ndisj | solve_ndisj | ].
    iDestruct "Hpoints" as (v_old) "(Hmapsto & #Hown)".
    iEval (rewrite /ty_own_val /=) in "Hown".
    iDestruct "Hown" as "(%Hmeta & %Hval_z)".
    (* Extract has_layout_loc from persistent shared borrow *)
    iPoseProof "Hl" as "Hl2".
    iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hl2".
    iDestruct "Hl2" as (ly_loc Halg_loc Hly_loc) "_".
    apply syn_type_has_layout_int_inv in Halg_loc. subst ly_loc.
    iModIntro.

    (** Phase 3 — Operate: [wp_deref ScOrd] *)
    iApply (wp_deref _ _ _ l (IntOp it) 1 f.1 _ ScOrd with "Hmapsto").
    { left; done. }
    { apply val_to_of_loc. }
    { rewrite /ot_layout. done. }
    { apply val_to_Z_length in Hval_z.
      rewrite /has_layout_val /ot_layout /it_layout /ly_size. lia. }
    iApply physical_step_intro. iNext. iIntros (st) "Hmapsto".

    (** Phase 4 — Close: invariant, lifetime, continuation *)
    iMod ("Hclose" $! r with "[Hmapsto Hinv]") as "Hκ".
    { iFrame "Hinv". iExists v_old. iFrame "Hmapsto".
      rewrite /ty_own_val /=. iPureIntro. split; done. }
    iMod ("Hclose_lft" with "Hκ HL") as "HL".
    iPoseProof ("HL_cl" with "HL") as "HL".
    rewrite (mem_cast_id_int _ _ _ Hval_z).
    iAssert (v_old ◁ᵥ{f.1, MetaNone} r @ (int it))%I as "Hv_ret".
    { rewrite /ty_own_val /=. iPureIntro. exact (conj Hmeta Hval_z). }
    iModIntro. iApply ("HΦ" with "HL Hf Hv_ret [HT]").
    { iApply ("HT" $! r v_old with "[//]"). }
  Qed.

  Global Program Instance typed_atomic_load_val_atomic_int_inst E L f it v l κ x :
    TypedAtomicLoadVal E L f v alias_ptr_t l (IntOp it) :=
    λ T, i2p (typed_atomic_load_atomic_int E L f it v l κ x T).
End atomic_load.

(** * Atomic store *)

Section atomic_store.
  Context `{!typeGS Σ}.
  Context {Y : RT} (P : at_ex_inv_def Z Y).

  Lemma typed_atomic_store_atomic_int E L f (it : int_type)
      (v_ptr : val) (l : loc) (v_val : val) (n : Z)
      (κ : lft) (x : Y)
      (T : typed_write_cont_t) :
    ⌜lctx_lft_alive E L κ⌝ ∗
    l ◁ₗ[f.1, Shared κ] (#x) @ (◁ (∃at; P, int it)) ∗
    find_in_context FindCreditStore (λ '(c, a),
      ⌜fast_lia_hint (1 ≤ c)⌝ ∗
      (credit_store (c - 1) a -∗ T L))
    ⊢ typed_atomic_store E L f
        v_ptr (v_ptr ◁ᵥ{f.1, MetaNone} l @ alias_ptr_t)
        v_val (v_val ◁ᵥ{f.1, MetaNone} n @ int it)
        (IntOp it) T.
  Proof.
  Admitted.

  Global Program Instance typed_atomic_store_val_atomic_int_inst E L f it v_ptr l v_val n κ x :
    TypedAtomicStoreVal E L f v_ptr alias_ptr_t l v_val (int it) n (IntOp it) :=
    λ T, i2p (typed_atomic_store_atomic_int E L f it v_ptr l v_val n κ x T).
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
        ∀ (r : Z) (v_old : val),
          ⌜val_to_Z v_old it = Some r⌝ -∗
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
          T L (val_of_bool true) MetaNone bool bool_t true ∧
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
