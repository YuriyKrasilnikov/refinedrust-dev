From refinedrust Require Export type ltypes programs.
From iris.base_logic Require Import ghost_map.
From refinedrust Require Import uninit int ltype_rules.
From refinedrust Require Import options.

(** Atomic borrow: wraps an indexed borrow token in an Iris concurrent invariant.
    Unlike [na_bor], does not require a thread_id [π] — the invariant is globally
    accessible via atomic mask-changing updates. *)
Definition at_bor `{!typeGS Σ}
           (κ : lft) (N : namespace) (P : iProp Σ) :=
  (∃ i, &{κ,i}P ∗ inv N (idx_bor_own 1 i))%I.

Notation "&at{ κ , N }" := (at_bor κ N)
    (format "&at{ κ , N }") : bi_scope.

Section at_bor.
  Context `{!typeGS Σ}
          (N : namespace) (P : iProp Σ).

  Global Instance at_bor_ne κ n : Proper (dist n ==> dist n) (at_bor κ N).
  Proof. solve_proper. Qed.
  Global Instance at_bor_contractive κ : Contractive (at_bor κ N).
  Proof. solve_contractive. Qed.
  Global Instance at_bor_proper κ : Proper ((⊣⊢) ==> (⊣⊢)) (at_bor κ N).
  Proof. solve_proper. Qed.

  Lemma at_bor_iff κ P' :
    ▷ □ (P ↔ P') -∗ &at{κ, N} P -∗ &at{κ, N} P'.
  Proof.
    iIntros "HPP' H". iDestruct "H" as (i) "[HP ?]". iExists i. iFrame.
    iApply (idx_bor_iff with "HPP' HP").
  Qed.

  Global Instance at_bor_persistent κ : Persistent (&at{κ,N} P) := _.

  Lemma bor_at κ E : ↑lftN ⊆ E → &{κ}P ={E}=∗ &at{κ,N}P.
  Proof.
    iIntros (?) "HP". rewrite bor_unfold_idx. iDestruct "HP" as (i) "[#? Hown]".
    iExists i. iFrame "#". iApply (inv_alloc N with "[Hown]"). auto.
  Qed.

  (** Opening an atomic borrow is mask-changing: [={E, E∖↑N}=∗].
      Precondition [↑lftN ⊆ E ∖ ↑N] (not just [↑lftN ⊆ E]) because
      [idx_bor_acc] runs inside the open invariant where the mask is [E∖↑N]. *)
  Lemma at_bor_acc q κ E :
    ↑lftN ⊆ E ∖ ↑N →
    ↑N ⊆ E →
    lft_ctx -∗ &at{κ,N}P -∗ q.[κ] ={E, E∖↑N}=∗
            ▷P ∗ (▷P ={E∖↑N, E}=∗ q.[κ]).
  Proof.
    iIntros (??) "#LFT #HP Hκ".
    iDestruct "HP" as (i) "(#Hpers & #Hinv)".
    iInv "Hinv" as ">Hown" "Hclose".
    iMod (idx_bor_acc with "LFT Hpers Hown Hκ") as "[HP Hclose']"; first done.
    iIntros "{$HP} !> HP".
    iMod ("Hclose'" with "HP") as "[Hown $]". iApply "Hclose". by iFrame.
  Qed.

  Lemma at_bor_shorten κ κ': κ ⊑ κ' -∗ &at{κ',N}P -∗ &at{κ,N}P.
  Proof.
    iIntros "Hκκ' H". iDestruct "H" as (i) "[H ?]". iExists i. iFrame.
    iApply (idx_bor_shorten with "Hκκ' H").
  Qed.

  Lemma at_bor_fake E κ: ↑lftN ⊆ E → lft_ctx -∗ [†κ] ={E}=∗ &at{κ,N}P.
  Proof.
    iIntros (?) "#LFT #H†". iApply (bor_at with "[>]"); first done.
    by iApply (bor_fake with "LFT H†").
  Qed.
End at_bor.
Global Typeclasses Opaque at_bor.


Record at_ex_inv_def `{!typeGS Σ} (X : RT) (Y : RT) : Type := at_mk_ex_inv_def' {
  at_inv_xr_inh : Inhabited (RT_xt Y);

  at_inv_P : thread_id → X → Y → iProp Σ;

  at_inv_P_lfts : list lft;
  at_inv_P_wf_E : elctx;
}.

Definition at_mk_ex_inv_def `{!typeGS Σ} {X Y : RT} `{!Inhabited (RT_xt Y)}
  (inv_P : thread_id → X → Y → iProp Σ)

  inv_P_lfts
  (inv_P_wf_E : elctx)

  := at_mk_ex_inv_def' _ _ _ _ _
       inv_P inv_P_lfts inv_P_wf_E.

Global Arguments at_inv_P {_ _ _ _}.
Global Arguments at_inv_P_lfts {_ _ _ _}.
Global Arguments at_inv_P_wf_E {_ _ _ _}.

Class AtExInvDefNonExpansive `{!typeGS Σ} {rt X Y : RT} (F : type rt → at_ex_inv_def X Y) : Type := {
  at_ex_inv_def_ne_lft_mor : DirectLftMorphism (λ ty, (F ty).(at_inv_P_lfts)) (λ ty, (F ty).(at_inv_P_wf_E));

  at_ex_inv_def_ne_val_own :
    ∀ (n : nat) (ty ty' : type rt),
      TypeDist n ty ty' →
      ∀ π x y,
        (F ty).(at_inv_P) π x y ≡{n}≡ (F ty').(at_inv_P) π x y;
}.

Class AtExInvDefContractive `{!typeGS Σ} {rt X Y : RT} (F : type rt → at_ex_inv_def X Y) : Type := {
  at_ex_inv_def_contr_lft_mor : DirectLftMorphism (λ ty, (F ty).(at_inv_P_lfts)) (λ ty, (F ty).(at_inv_P_wf_E));

  at_ex_inv_def_contr_val_own :
    ∀ (n : nat) (ty ty' : type rt),
      TypeDist2 n ty ty' →
      ∀ π x y,
        (F ty).(at_inv_P) π x y ≡{n}≡ (F ty').(at_inv_P) π x y;
}.

Section insts.
  Context `{!typeGS Σ}.

  Global Instance at_ex_inv_def_contractive_const {rt X Y} (v : at_ex_inv_def X Y) :
    AtExInvDefContractive (λ _ : type rt, v).
  Proof.
    constructor.
    - apply (direct_lft_morph_make_const _ _).
    - eauto.
  Qed.

  Global Instance at_ex_inv_def_ne_const {rt X Y} (v : at_ex_inv_def X Y) :
    AtExInvDefNonExpansive (λ _ : type rt, v).
  Proof.
    constructor.
    - apply (direct_lft_morph_make_const _ _).
    - eauto.
  Qed.
End insts.

Section at_ex.
  Context `{!typeGS Σ}.
  Context (X Y : RT) (P : at_ex_inv_def X Y).

  Program Definition at_ex_plain_t (ty : type X) : type Y := {|
    ty_metadata_kind := ty.(ty_metadata_kind);
    ty_own_val π r m v := ∃ x : X, P.(at_inv_P) π x r ∗ ty.(ty_own_val) π x m v;
    ty_shr κ π r m l :=
      ty.(ty_sidecond) ∗
      &at{κ, shrN.@l}(∃ x, l ↦: ty.(ty_own_val) π x m ∗ P.(at_inv_P) π x r) ∗
      (∃ ly : layout, ⌜l `has_layout_loc` ly⌝ ∗ ⌜syn_type_has_layout (ty_syn_type ty m) ly⌝);

    ty_syn_type := ty.(ty_syn_type);
    _ty_has_op_type ot mt := ty_has_op_type ty ot mt;
    ty_sidecond := ty.(ty_sidecond);

    _ty_lfts := P.(at_inv_P_lfts) ++ ty_lfts ty;
    _ty_wf_E := P.(at_inv_P_wf_E) ++ ty_wf_E ty;
  |}%I.

  (* ty_xt_inhabited *)
  Next Obligation.
    intros. apply P.
  Defined.

  (* ty_has_layout *)
  Next Obligation.
    iIntros (?????) "(% & _ & ?)".
    by iApply ty_has_layout.
  Qed.

  (* _ty_op_type_stable *)
  Next Obligation.
    iIntros (????).
    by eapply ty_op_type_stable.
  Qed.

  (* ty_own_val_sidecond *)
  Next Obligation.
    iIntros (?????) "(% & _ & ?)".
    by iApply ty_own_val_sidecond.
  Qed.

  (* ty_shr_sidecond *)
  Next Obligation.
    iIntros (??????) "($ & _ & _)".
  Qed.

  (* ty_shr_persistent *)
  Next Obligation. unfold TCNoResolve. apply _. Qed.

  (* ty_shr_aligned *)
  Next Obligation.
    iIntros (??????) "(_ &  _ & (%ly & % & %))".
    eauto.
  Qed.

  (* ty_share — uses bor_at instead of bor_na, no na_own needed *)
  Next Obligation.
    iIntros (ty E κ l ly π r m q ?) "#(LFT & LLCTX) _ Htok %Halg %Hly Hlb Hbor".
    iEval (setoid_rewrite bi.sep_exist_l) in "Hbor".
    iEval (setoid_rewrite bi_exist_comm) in "Hbor".

    rewrite lft_intersect_list_app -!lft_tok_sep.
    iDestruct "Htok" as "(Htok & ? & ?)".

    iApply fupd_logical_step; iApply logical_step_intro.

    iPoseProof (bor_iff _ _ (∃ x: X, l ↦: ty_own_val ty π x m ∗ P.(at_inv_P) π x r) with "[] Hbor") as "Hbor".
    { iNext. iModIntro. iSplit; [iIntros "(% & % & ? & ? & ?)" | iIntros "(% & (% & ? & ?) & ?)"]; eauto with iFrame. }

    iMod (bor_get_persistent _ (ty_sidecond ty) with "LFT [] Hbor Htok") as "(Hty & Hbor & Htok)"; first solve_ndisj.
    { iIntros "Hinv".
      iDestruct "Hinv" as (v) "((% & Hl & HP) & Hv)".
      iPoseProof (ty_own_val_sidecond with "HP") as "#>Hsc".
      iModIntro; iSplit; [iNext | done].
      iExists v; iFrame. }

    iMod (bor_at with "Hbor") as "Hbor"; first solve_ndisj.

    iModIntro; iFrame "∗ #".
    iExists ly; eauto with iFrame.
  Qed.

  (* ty_shr_mono *)
  Next Obligation.
    iIntros (ty κ κ' π r ? l) "Hincl ($ & Hbor & %ly & ? & ?)".
    iFrame. iApply (at_bor_shorten with "Hincl Hbor").
  Qed.

  (* _ty_memcast_compat *)
  Next Obligation.
    iIntros (ty ot mt st π r m v Hot) "(%x & ? & Hv)".
    iPoseProof (ty_memcast_compat with "Hv") as "Hm"; first done.
    destruct mt; eauto with iFrame.
  Qed.

  Next Obligation.
    intros ty ly mt Heq Hst.
    rewrite ty_has_op_type_unfold.
    by apply _ty_has_op_type_untyped.
  Qed.

End at_ex.

Section contr.
  Context `{!typeGS Σ}.

  Global Instance at_ex_inv_def_contractive {rt X Y : RT}
    (P : type rt → at_ex_inv_def X Y)
    (F : type rt → type X) :
    AtExInvDefContractive P →
    TypeContractive F →
    TypeContractive (λ ty, at_ex_plain_t X Y (P ty) (F ty)).
  Proof.
    intros HP HF.
    constructor; simpl.
    - apply HF.
    - apply HF.
    - destruct HP as [Hlft _].
      destruct HF as [_ _ Hlft' _ _ _ _].
      apply ty_lft_morphism_of_direct.
      apply ty_lft_morphism_to_direct in Hlft'.
      simpl in *.
      rewrite ty_wf_E_unfold.
      rewrite ty_lfts_unfold.
      apply direct_lft_morphism_app; done.
    - rewrite ty_has_op_type_unfold. eapply HF.
    - simpl. eapply HF.
    - intros n ty ty' ?.
      intros π r m v. rewrite /ty_own_val/=.
      do 3 f_equiv.
      { apply HP; done. }
      apply HF; done.
    - intros n ty ty' Hd.
      intros ?????. rewrite /ty_shr/=.
      do 1 f_equiv.
      { rewrite type_ctr_sidecond; first done.
        apply Hd. }
      do 1 f_equiv.
      { f_contractive. do 3 f_equiv.
        - do 4 solve_type_proper_step.
          unfold_sidx.
          eapply type_dist_later2_dist2; first done.
          unfold CanSolve. lia.
        - apply HP.
          eapply type_dist_later2_dist2; first done.
          unfold_sidx.
          unfold CanSolve. lia. }
      do 5 f_equiv.
      apply HF.
  Qed.

  Global Instance at_ex_inv_def_ne {rt X Y : RT}
    (P : type rt → at_ex_inv_def X Y)
    (F : type rt → type X)
    :
    AtExInvDefNonExpansive P →
    TypeNonExpansive F →
    TypeNonExpansive (λ ty, at_ex_plain_t X Y (P ty) (F ty)).
  Proof.
    intros HP HF.
    constructor; simpl.
    - apply HF.
    - apply HF.
    - destruct HP as [Hlft _].
      destruct HF as [_ _ Hlft' _ _ _ _].
      apply ty_lft_morphism_of_direct.
      apply ty_lft_morphism_to_direct in Hlft'.
      simpl in *.
      rewrite ty_wf_E_unfold.
      rewrite ty_lfts_unfold.
      apply direct_lft_morphism_app; done.
    - rewrite ty_has_op_type_unfold. intros.
      eapply HF; first done.
      rewrite ty_has_op_type_unfold. done.
    - simpl. eapply HF.
    - intros n ty ty' ?.
      intros π r m v. rewrite /ty_own_val/=.
      do 3 f_equiv.
      { apply HP; done. }
      apply HF; done.
    - intros n ty ty' Hd.
      intros ?????. rewrite /ty_shr/=.
      do 1 f_equiv.
      { rewrite type_ne_sidecond; first done; apply Hd. }
      do 1 f_equiv.
      { f_contractive. do 3 f_equiv.
        - do 4 solve_type_proper_step.
          eapply type_dist2_dist; first done.
          unfold_sidx.
          unfold CanSolve. lia.
        - apply HP.
          eapply type_dist2_dist; first done.
          unfold_sidx.
          unfold CanSolve. lia. }
      do 5 f_equiv.
      apply HF. apply Hd.
  Qed.
End contr.

Notation "'∃at;' P ',' τ" := (at_ex_plain_t _ _ P τ) (at level 40) : stdpp_scope.

Section at_subtype.
  Context `{!typeGS Σ}.
  Context {rt X : RT} (P : at_ex_inv_def rt X).

  Lemma owned_subtype_at_ex_plain_t π E L (ty : type rt) (r : rt) (r' : X) T :
    (prove_with_subtype E L false ProveDirect (P.(at_inv_P) π r r') (λ L1 _ R, R -∗ T L1))
    ⊢ owned_subtype π E L false r r' ty (∃at; P, ty) T.
  Proof.
    unfold owned_subtype, prove_with_subtype.
    iIntros "HT".
    iIntros (????) "#CTX #HE HL".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L2 & % & %R2 & >(Hinv & HR2) & HL & HT)".
    iExists L2. iFrame. iPoseProof ("HT" with "HR2") as "$". iModIntro.
    iSplitR; last iSplitR.
    - simpl. iPureIntro. eapply syn_type_size_eq_refl.
    - simpl. eauto.
    - iIntros (v) "Hv0".
      iEval (rewrite /ty_own_val/=).
      eauto with iFrame.
  Qed.
  Definition owned_subtype_at_ex_plain_t_inst := [instance @owned_subtype_at_ex_plain_t].
  Global Existing Instance owned_subtype_at_ex_plain_t_inst.

  Lemma at_ex_plain_t_acc_owned F π (ty : type rt) (l : loc) (x : X) :
    lftE ⊆ F →
    l ◁ₗ[π, Owned] #x @ (◁ (∃at; P, ty)) ={F}=∗
    ∃ r : rt, P.(at_inv_P) π r x ∗
    l ◁ₗ[π, Owned] #r @ (◁ ty) ∗
    (∀ rt' (lt' : ltype rt') (r' : place_rfn rt'),
      l ◁ₗ[π, Owned] r' @ lt' -∗
      ⌜ltype_st lt' = ty_syn_type ty MetaNone⌝ -∗
      l ◁ₗ[π, Owned] r' @
        (OpenedLtype lt' (◁ ty) (◁ ∃at; P, ty)
          (λ (r : rt) (x : X), P.(at_inv_P) π r x)
          (λ r x, True)))%I.
  Proof.
    iIntros (?) "Hb".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & %x' & Hrfn & Hb)".
    iMod (fupd_mask_mono with "Hb") as "Hb"; first done.

    unfold ty_own_val, at_ex_plain_t at 2.
    iDestruct "Hb" as "(%v & Hl & %r & HP & Hv)".

    iDestruct "Hrfn" as "<-".
    iModIntro. iExists r. iFrame.
    iSplitL "Hl Hv".
    { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly. iFrame "#%".
      iExists r. iSplitR; first done. iModIntro. eauto with iFrame. }

    iIntros (rt' lt' r') "Hb %Hst".
    rewrite ltype_own_opened_unfold /opened_ltype_own.
    iExists ly. rewrite Hst.
    do 5 iR; iFrame.

    clear -Halg Hly.
    iApply logical_step_intro.
    iIntros (r' r'' κs) "HP".
    iSplitR; first done.
    iIntros "Hdead Hl".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly' & _ & _ & Hsc' & _ & %r0 & -> & >Hb)".
    iDestruct "Hb" as "(%v' & Hl & Hv)".
    iMod ("HP" with "Hdead" ) as "HP".
    iModIntro.
    rewrite ltype_own_core_equiv. simp_ltypes.
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iExists ly. simpl. iFrame "#%". iFrame.
    done.
  Qed.

  Lemma typed_place_at_ex_plain_t_owned E L f l (ty : type rt) x K `{!TCDone (K ≠ [])} T :
    (∀ r, introduce_with_hooks E L (P.(at_inv_P) f.1 r x)
      (λ L2, typed_place E L2 f l
              (OpenedLtype (◁ ty) (◁ ty) (◁ (∃at; P, ty)) (λ (r : rt) (x : X), P.(at_inv_P) f.1 r x) (λ r x, True))
              (#r) UpdStrong (Owned) K
        (λ L2 κs li b2 bmin' rti ltyi ri updcx,
          T L2 κs li b2 bmin' rti ltyi ri
            (λ L3 upd cont, updcx L3 upd (λ upd',
            cont (@mkPUpd _ _ _ UpdStrong _
              upd'.(pupd_lt) upd'.(pupd_rfn) upd'.(pupd_R) UpdStrong
              I I)))
        )))
    ⊢ typed_place E L f l (◁ (∃at; P, ty))%I (#x) UpdStrong (Owned) K T.
  Proof.
    unfold introduce_with_hooks, typed_place.
    iIntros "HT". iIntros (F ???) "#CTX #HE HL Hf Hb Hcont".
    iApply fupd_place_to_wp.
    iMod (at_ex_plain_t_acc_owned with "Hb") as "(%r & HP & Hb & Hcl)"; first done.
    iPoseProof ("Hcl" with "Hb []") as "Hb"; first done.
    iMod ("HT" with "[] HE HL HP") as "(%L2 & HL & HT)"; first done.
    iApply ("HT" with "[//] [//] CTX HE HL Hf Hb").
    iModIntro. iIntros (L' κs l2 b2 bmin0 rti ltyi ri updcx) "Hl Hc".
    iApply ("Hcont" with "Hl").
    iIntros (upd) "#Hincl Hl2 %Hsteq ? ?".
    iMod ("Hc" with "Hincl Hl2 [//] [$] [$]") as "Hc".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hc" with "HL Hf Hcont") as (upd') "(Hl & %Hsteq' & Hcond & ? & ? & ? & ? & ?)".
    iFrame. simp_ltypes. done.
  Qed.
  Definition typed_place_at_ex_plain_t_owned_inst := [instance @typed_place_at_ex_plain_t_owned].
  Global Existing Instance typed_place_at_ex_plain_t_owned_inst | 15.

  (** Shared access to [at_ex_plain_t] is mask-changing because opening an
      Iris concurrent invariant reduces the mask. The caller gets raw resources
      under the open invariant and must close it via the returned viewshift. *)
  Lemma at_ex_plain_t_acc_shared E π (ty : type rt) q κ l (x : X) :
    lftE ⊆ E ∖ ↑(shrN.@l) →
    ↑shrN.@l ⊆ E →
    lft_ctx -∗
    £ 1 -∗
    q.[κ] -∗
    l ◁ₗ[π, Shared κ] (#x) @ (◁ (∃at; P, ty)) ={E, E∖↑(shrN.@l)}=∗
    ∃ (r : rt),
      P.(at_inv_P) π r x ∗
      (l ↦: ty_own_val ty π r MetaNone) ∗
      (∀ r' : rt,
          (l ↦: ty_own_val ty π r' MetaNone) ∗ P.(at_inv_P) π r' x
          ={E∖↑(shrN.@l), E}=∗ q.[κ]).
  Proof.
    iIntros (??) "#LFT Hcred Hq #Hb".
    iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hb".
    iDestruct "Hb" as (ly Halg Hly) "(Hsc & Hlb & %v & -> & #Hb)".

    iMod (fupd_mask_mono with "Hb") as "#Hb'"; first done; iClear "Hb".
    iEval (unfold ty_shr, at_ex_plain_t) in "Hb'".
    iDestruct "Hb'" as "(Hscr & Hbor & %ly' & %Hly' & %Halg')".

    iMod (at_bor_acc with "LFT Hbor Hq") as "(HP & Hvs)"; [done..|].

    iApply (lc_fupd_add_later with "Hcred").
    do 2 iModIntro.
    iDestruct "HP" as (%r) "(Hl & HP)".
    iExists r. iFrame.
    iIntros (r') "(Hl & HP)".
    iApply ("Hvs" with "[Hl HP]").
    iNext. iExists r'. iFrame.
  Qed.

End at_subtype.
