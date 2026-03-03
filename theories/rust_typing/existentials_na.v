From refinedrust Require Export type ltypes programs.
From iris.base_logic Require Import ghost_map.
From refinedrust Require Import uninit int ltype_rules.
From refinedrust Require Import options.

(** A copy of [na_borrow]  from the lifetime logic for our version of thread-local invariants *)
Definition na_bor `{!typeGS Σ}
           (κ : lft) (π : thread_id) (N : namespace) (P : iProp Σ) :=
  (∃ i, &{κ,i}P ∗ na_inv π N (idx_bor_own 1 i))%I.

Notation "&na{ κ , π , N }" := (na_bor κ π N)
    (format "&na{ κ , π , N }") : bi_scope.

Section na_bor.
  Context `{!typeGS Σ}
          (π : thread_id) (N : namespace) (P : iProp Σ).

  Global Instance na_bor_ne κ n : Proper (dist n ==> dist n) (na_bor κ π N).
  Proof. solve_proper. Qed.
  Global Instance na_bor_contractive κ : Contractive (na_bor κ π N).
  Proof. solve_contractive. Qed.
  Global Instance na_bor_proper κ : Proper ((⊣⊢) ==> (⊣⊢)) (na_bor κ π N).
  Proof. solve_proper. Qed.

  Lemma na_bor_iff κ P' :
    ▷ □ (P ↔ P') -∗ &na{κ, π, N} P -∗ &na{κ, π, N} P'.
  Proof.
    iIntros "HPP' H". iDestruct "H" as (i) "[HP ?]". iExists i. iFrame.
    iApply (idx_bor_iff with "HPP' HP").
  Qed.

  Global Instance na_bor_persistent κ : Persistent (&na{κ,π,N} P) := _.

  Lemma bor_na κ E : ↑lftN ⊆ E → na_own π ∅ -∗ &{κ}P ={E}=∗ &na{κ,π,N}P.
  Proof.
    iIntros (?) "Hna HP". rewrite bor_unfold_idx. iDestruct "HP" as (i) "[#? Hown]".
    iExists i. iFrame "#". iApply (na_inv_alloc π E N with "Hna [Hown]"). auto.
  Qed.

  Lemma na_bor_acc q κ E F :
    ↑lftN ⊆ E → ↑N ⊆ E → ↑N ⊆ F →
    lft_ctx -∗ &na{κ,π,N}P -∗ q.[κ] -∗ na_own π F ={E}=∗
            ▷P ∗ na_own π (F ∖ ↑N) ∗
            (▷P -∗ na_own π (F ∖ ↑N) ={E}=∗ q.[κ] ∗ na_own π F).
  Proof.
    iIntros (???) "#LFT#HP Hκ Hnaown".
    iDestruct "HP" as (i) "(#Hpers&#Hinv)".
    iMod (na_inv_acc with "Hinv Hnaown") as "(>Hown&Hnaown&Hclose)"; try done.
    iMod (idx_bor_acc with "LFT Hpers Hown Hκ") as "[HP Hclose']"; first done.
    iIntros "{$HP $Hnaown} !> HP Hnaown".
    iMod ("Hclose'" with "HP") as "[Hown $]". iApply "Hclose". by iFrame.
  Qed.

  Lemma na_bor_shorten κ κ': κ ⊑ κ' -∗ &na{κ',π,N}P -∗ &na{κ,π,N}P.
  Proof.
    iIntros "Hκκ' H". iDestruct "H" as (i) "[H ?]". iExists i. iFrame.
    iApply (idx_bor_shorten with "Hκκ' H").
  Qed.

  Lemma na_bor_fake E κ: ↑lftN ⊆ E → lft_ctx -∗ na_own π ∅ -∗ [†κ] ={E}=∗ &na{κ,π,N}P.
  Proof.
    iIntros (?) "#LFT #Hna #H†". iApply (bor_na with "Hna [>]"); first done.
    by iApply (bor_fake with "LFT H†").
  Qed.
End na_bor.
Global Typeclasses Opaque na_bor.


Record na_ex_inv_def `{!typeGS Σ} (X : RT) (Y : RT) : Type := na_mk_ex_inv_def' {
  na_inv_xr_inh : Inhabited (RT_xt Y);

  (* NOTE: Make persistent part (Timeless) + non-persistent part inside &na *)
  na_inv_P : thread_id → X → Y → iProp Σ;

  na_inv_P_lfts : list lft;
  na_inv_P_wf_E : elctx;
}.

(* Stop Typeclass resolution for the [inv_P_pers] argument, to make it more deterministic. *)
Definition na_mk_ex_inv_def `{!typeGS Σ} {X Y : RT} `{!Inhabited (RT_xt Y)}
  (inv_P : thread_id → X → Y → iProp Σ)

  inv_P_lfts
  (inv_P_wf_E : elctx)

  := na_mk_ex_inv_def' _ _ _ _ _
       inv_P inv_P_lfts inv_P_wf_E.

Global Arguments na_inv_P {_ _ _ _}.
Global Arguments na_inv_P_lfts {_ _ _ _}.
Global Arguments na_inv_P_wf_E {_ _ _ _}.

(** Smart constructor for persistent and timeless [P] *)
Program Definition na_mk_pers_ex_inv_def
  `{!typeGS Σ} {X : RT} {Y : RT}
  `{!Inhabited (RT_xt Y)}
  (P : X → Y → iProp Σ) :=
    na_mk_ex_inv_def (λ _, P) [] [] (* _ *).

Class NaExInvDefNonExpansive `{!typeGS Σ} {rt X Y : RT} (F : type rt → na_ex_inv_def X Y) : Type := {
  ex_inv_def_ne_lft_mor : DirectLftMorphism (λ ty, (F ty).(na_inv_P_lfts)) (λ ty, (F ty).(na_inv_P_wf_E));

  ex_inv_def_ne_val_own :
    ∀ (n : nat) (ty ty' : type rt),
      TypeDist n ty ty' →
      ∀ π x y,
        (F ty).(na_inv_P) π x y ≡{n}≡ (F ty').(na_inv_P) π x y;
}.

Class NaExInvDefContractive `{!typeGS Σ} {rt X Y : RT} (F : type rt → na_ex_inv_def X Y) : Type := {
  ex_inv_def_contr_lft_mor : DirectLftMorphism (λ ty, (F ty).(na_inv_P_lfts)) (λ ty, (F ty).(na_inv_P_wf_E));

  ex_inv_def_contr_val_own :
    ∀ (n : nat) (ty ty' : type rt),
      TypeDist2 n ty ty' →
      ∀ π x y,
        (F ty).(na_inv_P) π x y ≡{n}≡ (F ty').(na_inv_P) π x y;
}.

Section insts.
  Context `{!typeGS Σ}.

  Global Instance na_ex_inv_def_contractive_const {rt X Y} (v : na_ex_inv_def X Y) :
    NaExInvDefContractive (λ _ : type rt, v).
  Proof.
    constructor.
    - apply (direct_lft_morph_make_const _ _).
    - eauto.
  Qed.

  Global Instance na_ex_inv_def_ne_const {rt X Y} (v : na_ex_inv_def X Y) :
    NaExInvDefNonExpansive (λ _ : type rt, v).
  Proof.
    constructor.
  - apply (direct_lft_morph_make_const _ _).
    - eauto.
  Qed.

  (* TODO: instance for showing non-expansiveness from contractiveness *)

End insts.

Section na_ex.
  Context `{!typeGS Σ}.
  Context (X Y : RT) (P : na_ex_inv_def X Y).

  Program Definition na_ex_plain_t (ty : type X) : type Y := {|
    ty_metadata_kind := ty.(ty_metadata_kind);
    ty_own_val π r m v := ∃ x : X, P.(na_inv_P) π x r ∗ ty.(ty_own_val) π x m v;
    ty_shr κ π r m l :=
      (* TODO: Add persistant part that cannot depends on the refined value *)
      ty.(ty_sidecond) ∗
      &na{κ, π, shrN.@l}(∃ x, l ↦: ty.(ty_own_val) π x m ∗ P.(na_inv_P) π x r) ∗
      (∃ ly : layout, ⌜l `has_layout_loc` ly⌝ ∗ ⌜syn_type_has_layout (ty_syn_type ty m) ly⌝);

    ty_syn_type := ty.(ty_syn_type);
    _ty_has_op_type ot mt := ty_has_op_type ty ot mt;
    ty_sidecond := ty.(ty_sidecond);
    ty_ghost_drop _ _ := True%I;

    _ty_lfts := P.(na_inv_P_lfts) ++ ty_lfts ty;
    _ty_wf_E := P.(na_inv_P_wf_E) ++ ty_wf_E ty;
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

  (* ty_share *)
  Next Obligation.
    iIntros (ty E κ l ly π r m q ?) "#(LFT & LLCTX) #Hna Htok %Halg %Hly Hlb Hbor".
    iEval (setoid_rewrite bi.sep_exist_l) in "Hbor".
    iEval (setoid_rewrite bi_exist_comm) in "Hbor".

    rewrite lft_intersect_list_app -!lft_tok_sep.
    iDestruct "Htok" as "(Htok & ? & ?)".

    iApply fupd_logical_step; iApply logical_step_intro.

    iPoseProof (bor_iff _ _ (∃ x: X, l ↦: ty_own_val ty π x m ∗ P.(na_inv_P) π x r) with "[] Hbor") as "Hbor".
    { iNext. iModIntro. iSplit; [iIntros "(% & % & ? & ? & ?)" | iIntros "(% & (% & ? & ?) & ?)"]; eauto with iFrame. }

    iMod (bor_get_persistent _ (ty_sidecond ty) with "LFT [] Hbor Htok") as "(Hty & Hbor & Htok)"; first solve_ndisj.
    { iIntros "Hinv".
      iDestruct "Hinv" as (v) "((% & Hl & HP) & Hv)".
      iPoseProof (ty_own_val_sidecond with "HP") as "#>Hsc".
      iModIntro; iSplit; [iNext | done].
      iExists v; iFrame. }

    iMod (bor_na with "Hna Hbor") as "Hbor"; first solve_ndisj.

    iModIntro; iFrame "∗ #".
    iExists ly; eauto with iFrame.
  Qed.

  (* ty_shr_mono *)
  Next Obligation.
    iIntros (ty κ κ' π r ? l) "Hincl ($ & Hbor & %ly & ? & ?)".
    iFrame. iApply (na_bor_shorten with "Hincl Hbor").
  Qed.

  (* ty_own_ghost_drop *)
  Next Obligation.
    iIntros (???????) "Hv".
    by iApply logical_step_intro.
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

End na_ex.

Section contr.
  Context `{!typeGS Σ}.

  Global Instance na_ex_inv_def_contractive {rt X Y : RT}
    (P : type rt → na_ex_inv_def X Y)
    (F : type rt → type X) :
    NaExInvDefContractive P →
    TypeContractive F →
    TypeContractive (λ ty, na_ex_plain_t X Y (P ty) (F ty)).
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
    - intros n ty ty' Hd.
      intros. done.
  Qed.

  Global Instance na_ex_inv_def_ne {rt X Y : RT}
    (P : type rt → na_ex_inv_def X Y)
    (F : type rt → type X)
    :
    NaExInvDefNonExpansive P →
    TypeNonExpansive F →
    TypeNonExpansive (λ ty, na_ex_plain_t X Y (P ty) (F ty)).
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
    - intros n ty ty' Hd.
      intros. done.
  Qed.
End contr.

Notation "'∃na;' P ',' τ" := (na_ex_plain_t _ _ P τ) (at level 40) : stdpp_scope.

Section na_subtype.
  Context `{!typeGS Σ}.
  Context {rt X : RT} (P : na_ex_inv_def rt X).

  Lemma owned_subtype_na_ex_plain_t π E L (ty : type rt) (r : rt) (r' : X) T :
    (prove_with_subtype E L false ProveDirect (P.(na_inv_P) π r r') (λ L1 _ R, R -∗ T L1))
    ⊢ owned_subtype π E L false r r' ty (∃na; P, ty) T.
  Proof.
    unfold owned_subtype, prove_with_subtype.

    (* Nothing has changed *)
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
  Definition owned_subtype_na_ex_plain_t_inst := [instance @owned_subtype_na_ex_plain_t].
  Global Existing Instance owned_subtype_na_ex_plain_t_inst.

  (* TODO move *)
  Lemma opened_na_ltype_acc_owned π {rt_cur rt_inner} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) Cpre Cpost l r :
    l ◁ₗ[π, Owned] r @ OpenedNaLtype lt_cur lt_inner Cpre Cpost -∗
    l ◁ₗ[π, Owned] r @ lt_cur ∗
    (∀ rt_cur' (lt_cur' : ltype rt_cur') r',
      l ◁ₗ[π, Owned] r' @ lt_cur' -∗
      ⌜ltype_st lt_cur' = ltype_st lt_cur⌝ -∗
      l ◁ₗ[π, Owned] r' @ OpenedNaLtype lt_cur' lt_inner Cpre Cpost).
  Proof.
    rewrite ltype_own_opened_na_unfold /opened_na_ltype_own.
    iIntros "(%ly & ? & ? & ? & ? & $ & Hcl)".
    iIntros (rt_cur' lt_cur' r') "Hown %Hst".
    rewrite ltype_own_opened_na_unfold /opened_ltype_own.
    iExists ly. rewrite Hst. eauto with iFrame.
  Qed.
  Lemma typed_place_opened_na_owned E L f {rt_cur rt_inner} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) Cpre Cpost r l P''' T :
    typed_place E L f l lt_cur r UpdStrong (Owned) P''' (λ L' κs l2 b2 bmin rti ltyi ri updcx,
      T L' κs l2 b2 bmin rti ltyi ri
        (λ L2 upd cont, updcx L2 upd (λ upd',
          cont (mkPUpd _ UpdStrong
            upd'.(pupd_rt)
            (OpenedNaLtype upd'.(pupd_lt) lt_inner Cpre Cpost)
            upd'.(pupd_rfn)
            upd'.(pupd_R)
            UpdStrong
            I I))
        ))
    ⊢ typed_place E L f l (OpenedNaLtype lt_cur lt_inner Cpre Cpost) r UpdStrong (Owned) P''' T.
  Proof.
    unfold introduce_with_hooks, typed_place.

    (* Nothing has changed *)
    iIntros "HT". iIntros (Φ F ??) "#CTX #HE HL Hf Hl HR".
    iPoseProof (opened_na_ltype_acc_owned with "Hl") as "(Hl & Hcl)".
    iApply ("HT" with "[//] [//] CTX HE HL Hf Hl").
    iIntros (L' ??????? updcx) "Hl Hv".
    iApply ("HR" with "Hl").
    iIntros (upd) "#Hincl Hl2 %Hsteq ? Hcond".
    iMod ("Hv" with "Hincl Hl2 [//] [$] Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hs" with "HL Hf Hcont") as (upd') "(Hl & %Hsteq2 & Hcond & ? & ? & ? & HL & Hcont)".
    iFrame. simpl.
    iPoseProof ("Hcl" with "Hl [//]") as "$".
    done.
  Qed.
  Definition typed_place_opened_na_owned_inst := [instance @typed_place_opened_na_owned].
  Global Existing Instance typed_place_opened_na_owned_inst | 5.

  Lemma na_ex_plain_t_acc_owned F π (ty : type rt) (l : loc) (x : X) :
    lftE ⊆ F →
    l ◁ₗ[π, Owned] #x @ (◁ (∃na; P, ty)) ={F}=∗
    ∃ r : rt, P.(na_inv_P) π r x ∗
    l ◁ₗ[π, Owned] #r @ (◁ ty) ∗
    (∀ rt' (lt' : ltype rt') (r' : place_rfn rt'),
      l ◁ₗ[π, Owned] r' @ lt' -∗
      ⌜ltype_st lt' = ty_syn_type ty MetaNone⌝ -∗
      l ◁ₗ[π, Owned] r' @
        (OpenedLtype lt' (◁ ty) (◁ ∃na; P, ty)
          (λ (r : rt) (x : X), P.(na_inv_P) π r x)
          (λ r x, True)))%I.
  Proof.
    (* Nothing has changed *)
    iIntros (?) "Hb".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hb" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & %x' & Hrfn & Hb)".
    iMod (fupd_mask_mono with "Hb") as "Hb"; first done.

    unfold ty_own_val, na_ex_plain_t at 2.
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

  Lemma typed_place_na_ex_plain_t_owned E L f l (ty : type rt) x K `{!TCDone (K ≠ [])} T :
    (∀ r, introduce_with_hooks E L (P.(na_inv_P) f.1 r x)
      (λ L2, typed_place E L2 f l
              (OpenedLtype (◁ ty) (◁ ty) (◁ (∃na; P, ty)) (λ (r : rt) (x : X), P.(na_inv_P) f.1 r x) (λ r x, True))
              (#r) UpdStrong (Owned) K
        (λ L2 κs li b2 bmin' rti ltyi ri updcx,
          T L2 κs li b2 bmin' rti ltyi ri
            (λ L3 upd cont, updcx L3 upd (λ upd',
            cont (@mkPUpd _ _ _ UpdStrong _
              upd'.(pupd_lt) upd'.(pupd_rfn) upd'.(pupd_R) UpdStrong
              I I)))
        )))
    ⊢ typed_place E L f l (◁ (∃na; P, ty))%I (#x) UpdStrong (Owned) K T.
  Proof.
    unfold introduce_with_hooks, typed_place.

    (* Nothing has changed *)
    iIntros "HT". iIntros (F ???) "#CTX #HE HL Hf Hb Hcont".
    iApply fupd_place_to_wp.
    iMod (na_ex_plain_t_acc_owned with "Hb") as "(%r & HP & Hb & Hcl)"; first done.
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
  Definition typed_place_na_ex_plain_t_owned_inst := [instance @typed_place_na_ex_plain_t_owned].
  Global Existing Instance typed_place_na_ex_plain_t_owned_inst | 15.

  Lemma na_ex_plain_t_acc_shared E F π (ty : type rt) q κ l (x : X) :
    lftE ⊆ E →
    ↑shrN.@l ⊆ E →
    (shr_locsE l 1 ⊆ F) →

    lft_ctx -∗
    na_own π F -∗
    £ 1 -∗ (* Required: P.(na_inv_P) is not Timeless *)

    q.[κ] -∗
    l ◁ₗ[π, Shared κ] (#x) @ (◁ (∃na; P, ty)) ={E}=∗

    ∃ (r : rt),
      P.(na_inv_P) π r x ∗
      (l ◁ₗ[π, Owned] (#r) @ (◁ ty)) ∗
      &na{κ,π,shrN.@l} (∃ r' : rt, l ↦: ty_own_val ty π r' MetaNone ∗ na_inv_P P π r' x) ∗

      ( ∀ r' : rt,
          l ◁ₗ[π, Owned] #r' @ (◁ ty) ∗ P.(na_inv_P) π r' x ={E}=∗
          q.[κ] ∗ na_own π F ).
  Proof.
    iIntros (???) "#LFT Hna Hcred Hq #Hb".
    iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hb".
    iDestruct "Hb" as (ly Halg Hly) "(Hsc & Hlb & %v & -> & #Hb)".

    iMod (fupd_mask_mono with "Hb") as "#Hb'"; first done; iClear "Hb".
    iEval (unfold ty_shr, na_ex_plain_t) in "Hb'".
    iDestruct "Hb'" as "(Hscr & Hbor & %ly' & %Hly' & %Halg')".

    iMod (na_bor_acc with "LFT Hbor Hq Hna") as "((%r & Hl & HP) & Hna & Hvs)"; [ set_solver.. |].
    iApply (lc_fupd_add_later with "Hcred").

    do 2 iModIntro; iExists r; iFrame.

    iSplitL "Hl".
    { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly => /=.
      iFrame (Halg Hly) "Hlb Hscr". iExists r; iR.
      by iModIntro. }

    iR; iIntros (r') "(Hl & HP)".
    iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hl".
    iDestruct "Hl" as (???) "(_ & _ &  (% & <- & Hl)) /=".
    iMod (fupd_mask_mono with "Hl") as "Hl"; first solve_ndisj.

    iApply ("Hvs" with "[Hl HP] Hna").
    iExists r'; iFrame.
  Qed.

  (**
     This emits owned ownership of [l] into the context, leaving an indirection via [ShadowedLtype] here.
     We cannot directly put [OpenedLtype] here, as we can't have shared ownership of [OpenedLtype].
   *)
  Lemma typed_place_na_ex_plain_t_shared E L (f : frame_path) l (ty : type rt) x κ bmin K `{!TCDone (K ≠ [])} (T : place_cont_t X bmin) :
    find_in_context (FindNaOwn f.1) (λ mask : coPset,
      ⌜↑shrN.@l ⊆ mask⌝ ∗
      prove_with_subtype E L false ProveDirect (£ 1) (λ L1 _ R, R -∗
        li_tactic (lctx_lft_alive_count_goal E L1 κ) (λ '(κs, L2),
          ∀ r, introduce_with_hooks E L2
            (P.(na_inv_P) f.1 r x ∗
            l ◁ₗ[f.1, Owned] (#r) @
              (OpenedNaLtype (◁ ty) (◁ ty)
                (λ rfn, P.(na_inv_P) f.1 rfn x)
                (λ _, na_own f.1 (↑shrN.@l) ∗ llft_elt_toks κs)) ∗
            na_own f.1 (mask ∖ ↑shrN.@l))
            (λ L3,
              typed_place E L3 f l
                (ShadowedLtype (AliasLtype _ (ty_syn_type ty MetaNone) l) #tt (◁ (∃na; P, ty))) (#x) (bmin) (Shared κ) K
                (λ L4 κs li b2 bmin' rti ltyi ri updcx,
                  T L4 κs li b2 bmin' rti ltyi ri
                  (λ L3 upd cont, updcx L3 upd (λ upd',
                    cont (mkPUpd X _ _
                      upd'.(pupd_lt) upd'.(pupd_rfn) upd'.(pupd_R)
                      upd'.(pupd_performed)
                      upd'.(pupd_eq_1)
                      upd'.(pupd_eq_2)
                      )))
                )))))
    ⊢ typed_place E L f l (◁ (∃na; P, ty))%I (#x) bmin (Shared κ) K T.
  Proof.
    rewrite /find_in_context.
    iDestruct 1 as (mask) "(Hna & % & HT) /=".

    rewrite /typed_place /introduce_with_hooks.
    iIntros (Φ ???) "#(LFT & LLCTX) #HE HL Hf Hl Hcont".

    rewrite /prove_with_subtype.
    iApply fupd_place_to_wp.

    iMod ("HT" with "[] [] [] [$LFT $LLCTX] HE HL")
        as "(% & % & % & >(Hcred & HR) & HL & HT)"; [ done.. |].
    iSpecialize ("HT" with "HR").

    rewrite /li_tactic /lctx_lft_alive_count_goal.
    iDestruct "HT" as (???) "HT".

    iMod (fupd_mask_subseteq (lftE ∪ shrE)) as "Hf'"; first done.
    iMod (lctx_lft_alive_count_tok with "HE HL") as (q) "(Htok & Htokcl & HL)"; [ solve_ndisj.. |].
    iPoseProof (na_own_split with "Hna") as "(Hna & Hna')"; first done.
    iMod (na_ex_plain_t_acc_shared with "LFT Hna Hcred Htok Hl") as (r) "(HP & Hl & #Hbor & Hvs)"; [ try solve_ndisj.. |].

    iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hl".
    iDestruct "Hl" as (ly Halg Hly) "(#Hsc & #Hlb & (% & <- & Hl))".

    iMod ("HT" with "[] HE HL [$HP Hl Htokcl Hvs Hna']") as "HT"; first solve_ndisj.
    { rewrite ltype_own_opened_na_unfold /opened_na_ltype_own.
      iFrame.
      iExists ly; repeat iR.

      iSplitL "Hl".
      { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iExists ly; repeat iR.
        by iExists r; iR. }

      iApply logical_step_intro.

      iIntros (r') "Hinv Hl".
      iEval (rewrite ltype_own_ofty_unfold /lty_of_ty_own) in "Hl".
      iDestruct "Hl" as (ly' Halg' Hly') "(_ & #Hlb' & (% & <- & Hl))".

      iMod ("Hvs" with "[Hl Hinv]") as "(? & ?)".
      { iFrame.
        rewrite ltype_own_ofty_unfold /lty_of_ty_own.
        iExists ly'; repeat iR.
        by iExists r'; iR. }

      iFrame.
      by iApply "Htokcl". }

    iDestruct "HT" as (?) "(HL & HT)".

    iApply ("HT" with "[//] [//] [$LFT $LLCTX] HE HL Hf []").
    { rewrite ltype_own_shadowed_unfold /shadowed_ltype_own.

      iSplitL.
      { rewrite ltype_own_alias_unfold /alias_lty_own.
        iExists ly. by repeat iR. }

      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly; repeat iR.
      iExists x; repeat iR.

      rewrite /ty_shr /na_ex_plain_t.
      repeat iR.
      by iExists ly; repeat iR. }

    iMod "Hf'" as "_".
    iIntros "!>" (? ? ? ? ? ? ? ? updcx) "Hl Ha".
    iApply ("Hcont" with "Hl").

    iIntros (upd) "#Hincl Hl2 %Hsteq ? Hcond".
    iMod ("Ha" with "Hincl Hl2 [//] [$] Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hs" with "HL Hf Hcont") as (upd') "(Hl & %Hsteq' & Hcond & ? & ? & ? & HL & Hcont)".
    iFrame. simpl. simp_ltypes. iR.
    iApply (typed_place_cond_trans with "[] Hcond").
    iApply typed_place_cond_shadowed_r.
    iApply typed_place_cond_refl_ofty.
  Qed.
  Definition typed_place_na_ex_plain_t_shared_inst := [instance @typed_place_na_ex_plain_t_shared].
  Global Existing Instance typed_place_na_ex_plain_t_shared_inst | 15.

End na_subtype.
