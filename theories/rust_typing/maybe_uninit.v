From refinedrust Require Export type ltypes programs .
From refinedrust Require Import uninit.
From refinedrust Require Import options.

(** * A type modelled after Rust's MaybeUninit *)
(** We do not represent this directly with a union abstraction for simplicity, but rather directly define what the Rust memory representation of [MaybeUninit] is. *)

Section type.
  Context `{!typeGS Σ}.

  (** We refine by [option (place_rfn rt)] in order to borrow the optional contents.
     Note that this really makes it isomorphic to [MaybeUninit<T>] in our model,
     which is a union and thus would also get the place wrapper. *)
  Program Definition maybe_uninit {rt} (T : type rt) : type (option (place_rfn rt)) := {|
    ty_metadata_kind := T.(ty_metadata_kind);
    ty_own_val π r m v :=
      match r with
      | Some r' => ∃ r'', place_rfn_interp_owned r' r'' ∗ T.(ty_own_val) π r'' m v
      | None => (uninit (T.(ty_syn_type) m)).(ty_own_val) π () m v
      end%I;
    ty_syn_type := T.(ty_syn_type);
    _ty_has_op_type ot mt :=
      ∃ ly,
      syn_type_has_layout (T.(ty_syn_type) MetaNone) ly ∧ ot_layout ot = ly ∧
      match mt with
      | MCId => ot = UntypedOp ly
      | MCCopy => ty_has_op_type T ot MCCopy
      | MCNone => True
      end;
    ty_shr κ π r m l :=
      match r with
      | Some r' => ∃ r'', place_rfn_interp_shared r' r'' ∗ T.(ty_shr) κ π r'' m l
      | None => (uninit (T.(ty_syn_type) m)).(ty_shr) κ π () m l
      end%I;
    ty_ghost_drop π r :=
      match r with
      | None => True
      | Some r =>
          ∃ r', place_rfn_interp_owned r r' ∗ ty_ghost_drop T π r'
      end%I;
    ty_sidecond := True;
    _ty_lfts := ty_lfts T;
    _ty_wf_E := ty_wf_E T;
  |}.
  Next Obligation.
    iIntros (rt T π r m v) "Hv". destruct r as [r | ].
    - iDestruct "Hv" as "(%r'' & Hrfn & Hv)".
      iApply (ty_has_layout with "Hv").
    - iApply (ty_has_layout with "Hv").
  Qed.
  Next Obligation.
    simpl; iIntros (rt T ot mt Hot).
    destruct Hot as (ly & Hot & <- & Hmt). done.
  Qed.
  Next Obligation.
    iIntros (rt T π r m v) "_". done.
  Qed.
  Next Obligation.
    iIntros (rt T ? π r m v) "_". done.
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    iIntros (rt T κ π l r m) "Hl". destruct r as [r | ].
    - iDestruct "Hl" as "(%r'' & Hrfn & Hl)". iApply (ty_shr_aligned with "Hl").
    - iPoseProof (ty_shr_aligned with "Hl") as "Ha".
      done.
  Qed.
  Next Obligation.
    iIntros (rt T E κ l ly π [r | ] m ? ?) "#CTX #Hna Htok %Hst %Hly #Hlb Hb".
    -
      iAssert (&{κ} (∃ r', place_rfn_interp_owned r r' ∗ ∃ v : val, l ↦ v ∗ v ◁ᵥ{π, m} r' @ T))%I with "[Hb]" as "Hb".
      { iApply (bor_iff with "[] Hb"). iNext. iModIntro. iSplit.
        - iIntros "(%v & ? & %r' & ? & ?)". eauto with iFrame.
        - iIntros "(%r' & ? & %v & ? & ?)". eauto with iFrame. }
      iDestruct "CTX" as "(LFT & LLCTX)".
      iApply fupd_logical_step.
      rewrite -lft_tok_sep. iDestruct "Htok" as "(Htok1 & Htok2)".
      iMod (bor_exists_tok with "LFT Hb Htok1") as "(%r' & Hb & Htok1)"; first done.
      iMod (bor_sep with "LFT Hb") as "(Hrfn & Hb)"; first done.
      iMod (place_rfn_interp_owned_share with "LFT Hrfn Htok1") as "(Hrfn & Htok1)"; first done.
      iCombine ("Htok1 Htok2") as "Htok". rewrite lft_tok_sep.
      rewrite ty_lfts_unfold.
      iPoseProof (ty_share _ E with "[$LFT $LLCTX] Hna Htok [//] [//] Hlb Hb") as "Hstep"; first done.
      iApply (logical_step_wand with "Hstep").
      iIntros "!> (Hl & $)". eauto with iFrame.
    - rewrite -lft_tok_sep. iDestruct "Htok" as "[Htok1 Htok2]".
      (*iAssert (&{κ} (ty_sidecond T ∗ ∃ v : val, l ↦ v ∗ v ◁ᵥ{π} .@ uninit (ty_syn_type T)))%I with "[Hb]" as "Hb".*)
      (*{ iApply (bor_iff with "[] Hb"). iNext. iModIntro. iSplit.*)
        (*- iIntros "(%v & ? & ? & ?)". eauto with iFrame.*)
        (*- iIntros "($ & ?)". done. }*)
      (*iDestruct "CTX" as "(LFT & TIME & LLCTX)".*)
      (*iApply fupd_logical_step. iMod (bor_sep with "LFT Hb") as "(_ & Hb)"; first done.*)
      iPoseProof ((uninit _).(ty_share) with "CTX Hna [Htok1] [] [//] [//] Hb") as "Ha"; simpl; first done.
      { rewrite right_id. done. }
      { done. }
      iApply (logical_step_wand with "Ha"). iIntros "(? & Htok1)".
      rewrite right_id. iFrame.
  Qed.
  Next Obligation.
    iIntros (rt T κ κ' π r m l) "#Hincl Ha".
    destruct r as [r | ]; last by iApply ty_shr_mono.
    iDestruct "Ha" as "(%r'' & ? & Hv)".
    iExists _. iFrame. by iApply ty_shr_mono.
  Qed.
  Next Obligation.
    iIntros (rt ty π r m v F ?) "Hv".
    rewrite /ty_own_val/=.
    destruct r as [r' | ]; first last.
    { by iApply logical_step_intro. }
    iDestruct "Hv" as "(%r'' & Hinterp & Hv)".
    iApply (logical_step_wand with "[Hv]").
    { iApply (ty_own_ghost_drop with "Hv"); done. }
    iIntros "Ha".
    iExists _. iFrame.
  Qed.
  Next Obligation.
    iIntros (rt T ot mt st π r m v (ly & Hst & <- & Hmt)) "Ha".
    destruct mt; [done | | ].
    - (* copy *)
      destruct r as [r | ]; simpl; first last.
      { by iApply uninit_memcast. }
      iDestruct "Ha" as "(%r'' & Hrfn & Hv)".
      iExists r''. iFrame.
      iApply ty_memcast_compat_copy; done.
    - rewrite Hmt. simpl.
      iPureIntro.
      rewrite /mem_cast_id/=. intros ?.
      rewrite mem_cast_UntypedOp//.
  Qed.
  Next Obligation.
    intros ?? ly mt Heq Hst.
    simpl. exists ly. split_and!; [done.. | ].
    destruct mt; [done | | done].
    rewrite ty_has_op_type_unfold.
    by apply _ty_has_op_type_untyped.
  Qed.

  Global Instance maybe_uninit_sized {rt} (ty : type rt) :
    TySized ty →
    TySized (maybe_uninit ty).
  Proof.
    intros Hsz. econstructor; simpl.
    - apply Hsz.
    - apply Hsz.
  Qed.
End type.

Section ne.
  Context `{!typeGS Σ}.

  Global Instance maybe_uninit_ne {rt} :
    TypeNonExpansive (maybe_uninit (rt:=rt)).
  Proof.
    constructor; simpl.
    - done.
    - done.
    - eapply ty_lft_morph_make_id.
      + rewrite {1}ty_lfts_unfold//.
      + rewrite {1}ty_wf_E_unfold//.
    - rewrite ty_has_op_type_unfold/=.
      intros ?? -> Hot.
      intros ot mt.
      do 4 f_equiv.
      f_equiv.
      rewrite ty_has_op_type_unfold Hot//.
    - done.
    - solve_type_proper.
    - solve_type_proper.
    - solve_type_proper.
  Qed.
End ne.

Section subtype.
  Context `{!typeGS Σ}.

  (** Subtyping *)
  Lemma type_incl_maybe_uninit_Some {rt} (ty : type rt) (x : rt) :
    ⊢ type_incl x (Some (#x)) ty (maybe_uninit ty).
  Proof.
    iSplitR; first done. iSplitR; first iModIntro. { simpl. eauto. }
    iSplit; iModIntro.
    - iIntros (π m v) "Hv". iExists x. eauto with iFrame.
    - iIntros (κ π m l) "Hl". iExists x. eauto with iFrame.
  Qed.

  Lemma type_incl_Some_maybe_uninit {rt} (ty : type rt) (x : rt) :
    ty_sidecond ty -∗
    type_incl (Some (#x)) x (maybe_uninit ty) ty.
  Proof.
    iIntros "#Hsc". iSplitR; first done. iSplitR; first iModIntro. { simpl; eauto. }
    iSplit; iModIntro.
    - rewrite {1}/ty_own_val/=. iIntros (π m v) "(% & <- & Hv)". done.
    - rewrite {1}/ty_shr/=. iIntros (κ π m v) "(% & <- & Hl)". done.
  Qed.

  Lemma type_incl_maybe_uninit_None {rt} (ty : type rt) `{!TySized ty} :
    ⊢ type_incl () None (uninit (ty.(ty_syn_type) MetaNone)) (maybe_uninit ty).
  Proof.
    iSplitR.
    { iPureIntro. intros m. simpl. apply ty_sized_syn_type_eq. }
    iSplitR; first iModIntro. { simpl. eauto. }
    iSplit; iModIntro.
    - iIntros (π m v) "Hv". simpl.
      iEval (rewrite /ty_own_val/=).
      rewrite (ty_sized_syn_type_eq _ m). done.
    - iIntros (κ π m l) "Hl".
      iEval (rewrite /ty_shr/=).
      rewrite (ty_sized_syn_type_eq _ m). done.
  Qed.

  Lemma type_incl_None_maybe_uninit {rt} (ty : type rt) `{!TySized ty} :
    ⊢ type_incl None () (maybe_uninit ty) (uninit (ty.(ty_syn_type) MetaNone)).
  Proof.
    iSplitR.
    { iPureIntro. intros m. simpl. apply ty_sized_syn_type_eq. }
    iSplitR; first iModIntro. { simpl. eauto. }
    iSplit; iModIntro.
    - iIntros (π m v) "Hv". simpl.
      iEval (rewrite /ty_own_val/=).
      rewrite (ty_sized_syn_type_eq _ m). done.
    - iIntros (κ π m l) "Hl".
      iEval (rewrite /ty_shr/=).
      rewrite (ty_sized_syn_type_eq _ m). done.
  Qed.

End subtype.

Section rules.
  Context `{!typeGS Σ}.

  (** subtyping rules: *)

  Lemma weak_subtype_None_maybe_uninit E L {rt} (ty : type rt) `{!TySized ty} (r2 : unit) T :
    ⌜r2 = tt⌝ ∗ T ⊢ weak_subtype E L None r2 (maybe_uninit ty) (uninit (ty.(ty_syn_type) MetaNone)) T.
  Proof.
    iIntros "(-> & HT)" (??) "#CTX #HE HL". iFrame. by iApply type_incl_None_maybe_uninit.
  Qed.
  Definition weak_subtype_None_maybe_uninit_inst := [instance @weak_subtype_None_maybe_uninit].
  Global Existing Instance weak_subtype_None_maybe_uninit_inst.

  (* a variant that works in case the goal is an evar *)
  Lemma weak_subtype_None_maybe_uninit_evar E L {rt} (ty : type rt) `{!TySized ty} (r2 : unit) (ty2 : type unit) `{!IsProtected ty2} T :
    ⌜r2 = tt⌝ ∗ ⌜ty2 = (uninit (ty.(ty_syn_type) MetaNone))⌝ ∗ T ⊢ weak_subtype E L None r2 (maybe_uninit ty) ty2 T.
  Proof.
    iIntros "(-> & -> & HT)". iApply weak_subtype_None_maybe_uninit. iR; done.
  Qed.
  Definition weak_subtype_None_maybe_uninit_evar_inst := [instance @weak_subtype_None_maybe_uninit_evar].
  Global Existing Instance weak_subtype_None_maybe_uninit_evar_inst.

  Lemma weak_subtype_maybe_uninit_None E L {rt} (ty : type rt) `{!TySized ty} r2 T :
    ⌜r2 = None⌝ ∗ T ⊢ weak_subtype E L () r2 (uninit (ty.(ty_syn_type) MetaNone)) (maybe_uninit ty) T.
  Proof.
    iIntros "(-> & HT)" (??) "#CTX #HE HL". iFrame. by iApply type_incl_maybe_uninit_None.
  Qed.
  Definition weak_subtype_maybe_uninit_None_inst := [instance @weak_subtype_maybe_uninit_None].
  Global Existing Instance weak_subtype_maybe_uninit_None_inst.

  Lemma weak_subtype_Some_maybe_uninit E L {rt} (ty : type rt) (x : place_rfn rt) r2 T :
    (∃ x', ⌜x = #x'⌝ ∗ ⌜r2 = x'⌝ ∗ ty_sidecond ty ∗ T) ⊢ weak_subtype E L (Some x) r2 (maybe_uninit ty) ty T.
  Proof.
    iIntros "(%x' & -> & -> & Hsc & HT)" (??) "#CTX #HE HL". iFrame. by iApply type_incl_Some_maybe_uninit.
  Qed.
  Definition weak_subtype_Some_maybe_uninit_inst := [instance @weak_subtype_Some_maybe_uninit].
  Global Existing Instance weak_subtype_Some_maybe_uninit_inst.

  (* a variant that works in case the goal is an evar *)
  Lemma weak_subtype_Some_maybe_uninit_evar E L {rt} (ty : type rt) (x : place_rfn rt) r2 ty2 `{!IsProtected ty2} T :
    (∃ x', ⌜x = #x'⌝ ∗ ⌜r2 = x'⌝ ∗ ⌜ty2 = ty⌝ ∗ ty_sidecond ty ∗ T) ⊢ weak_subtype E L (Some x) r2 (maybe_uninit ty) ty2 T.
  Proof.
    iIntros "(%x' & -> & -> & -> & Hsc & HT)" (??) "#CTX #HE HL". iFrame. by iApply type_incl_Some_maybe_uninit.
  Qed.
  Definition weak_subtype_Some_maybe_uninit_evar_inst := [instance @weak_subtype_Some_maybe_uninit_evar].
  Global Existing Instance weak_subtype_Some_maybe_uninit_evar_inst.

  Lemma weak_subtype_maybe_uninit_Some E L {rt} (ty : type rt) (x : rt) r2 T :
    ⌜r2 = Some #x⌝ ∗ T ⊢ weak_subtype E L x r2 ty (maybe_uninit ty) T.
  Proof.
    iIntros "(-> & HT)" (??) "#CTX #HE HL". iFrame. iApply type_incl_maybe_uninit_Some.
  Qed.
  Definition weak_subtype_maybe_uninit_Some_inst := [instance @weak_subtype_maybe_uninit_Some].
  Global Existing Instance weak_subtype_maybe_uninit_Some_inst.

  Lemma weak_subltype_maybe_uninit_ghost E L {rt} (ty : type rt) γ r2 T :
    ⌜r2 = #(Some (👻 γ))⌝ ∗ T
    ⊢ weak_subltype E L (Owned) (👻 γ) r2 (◁ ty) (◁ (maybe_uninit ty)) T.
  Proof.
    iIntros "(-> & HT)".
    iIntros (??) "#CTX #HE HL". iFrame. iModIntro.
    iSplitR; first done.
    iModIntro. simp_ltypes.
    rewrite -bi.persistent_sep_dup.
    iModIntro. iIntros (π l) "Hl".
    rewrite !ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Hst & %Hly & Hsc & Hlb & %r' & Hrfn & Hl)".
    iMod "Hl" as "(%v & Hl & Hv)".
    iModIntro. iExists ly. iR. iR. iSplitR. { rewrite /maybe_uninit. done. }
    iFrame. iExists (Some (👻 γ)). iR. iModIntro.
    rewrite {2}/ty_own_val/=.
    eauto with iFrame.
  Qed.
  Definition weak_subltype_maybe_uninit_ghost_inst := [instance @weak_subltype_maybe_uninit_ghost].
  Global Existing Instance weak_subltype_maybe_uninit_ghost_inst | 40.

  Lemma owned_subtype_uninit_maybe_uninit π E L pers {rt} (ty : type rt) (st : syn_type) T :
    li_tactic (compute_layout_goal st) (λ ly1,
      li_tactic (compute_layout_goal (ty_syn_type ty MetaNone)) (λ ly2,
        ⌜ly_size ly1 = ly_size ly2⌝ ∗ T L))
    ⊢ owned_subtype π E L pers () None (uninit st) (maybe_uninit ty) T.
  Proof.
    rewrite /compute_layout_goal.
    iIntros "(%ly1 & %Halg1 & %ly2 & %Halg2 & %Hsz & HT)".
    iIntros (????) "#CTX #HE HL". iExists L. iModIntro. iFrame.
    iApply bi.intuitionistically_intuitionistically_if. iModIntro.
    iSplit; last iSplitR.
    { iPureIntro. simpl. by eapply syn_type_size_eq_prove. }
    { simpl. done. }
    iIntros (v) "Hv". rewrite !uninit_own_spec.
    iDestruct "Hv" as "(_ & %ly &  %Hst & %Hly)".
    assert (ly1 = ly) as <- by by eapply syn_type_has_layout_inj.
    rewrite /ty_own_val/=. iApply uninit_own_spec.
    iR.
    iExists _. iR.
    iPureIntro. rewrite /has_layout_val -Hsz//.
  Qed.
  Definition owned_subtype_uninit_maybe_uninit_inst := [instance @owned_subtype_uninit_maybe_uninit].
  Global Existing Instance owned_subtype_uninit_maybe_uninit_inst.

  (* reading/writing:
     does this need special handling?

     We certainly need some handling for read/write rules to inject into maybe_uninit when necessary, esp. below arrays.
  *)
  (* TODO: add these rules *)


  (** borrowing rules: *)
  (* for now, just don't allow borrowing maybe_uninit directly and handle it specially.
     TODO: in future, have an annotation for borrowing that enforces invariants. *)
  (* TODO: add the override *)



End rules.



  (*
     What happens with borrowing?
     - if it is Some, I want to create a borrow for the whole thing.
        To do that, I will probably need a place rule that just makes a maybeuninit into the inner type for the place access, and in the continuation wraps it again.
     - what happens with the blocked then? I cannot wrap a blocked directly in this type.
       In principle, this is fine from the perspective of the mutref contract, because the borrow enforces that I actually get a T back, so it is fine to put a Some there.
       Should I just bubble the blocked up (i.e. use openedltype/coreable)?
       In principle I know that I will get a maybe_uninit T back after the borrow ends, so this is fine intuitively. The only diff is how the ghost resolution does stuff. (NOTE: here ghost resolution would need to descend below the maybeuninit. But I have the right infrastructure for that, we just need to add a ghost_resolve instance for ◁ (maybe_uninit T)
       So I guess the place instance will just work via openedltype.
   *)

  (*
     How will the write of an initialized element to a maybeuninit location look?
     - in principle, if we can write strongly, just write. OpenedLtype closing should later apply the subtyping rule for injection into maybe_uninit.

     - for an array_ltype, subtyping should work elementwise. The openedltype in that case will require to go to an array where every field has the same type. Afterwards, that can be folded to an array_type again.


     TODO one thing to think about: we can't do refinement type updates for array_ltype, so we need to do the injection already at time of writing.
     How should writing work?
      - have: current type of place (ltype), type of value to write
      - options for rules we can use:
        + do a strong write, just put in the current value at its type.
        + do a strong write, but just put in a value_t for the written value and assemble ownership later on when needed.
        + directly adapt the type via subtyping so they match
      - we can also combine the options:
        + have specific instances (high priority) for particular combinations of types, and use one of the other options as default if they don't match.
          -> already doing that currently for writing to a mutltype etc.
          -> for maybe_uninit: have two specific instances for writing to it.
        + and then, as a fallback: just do a strong write (or decide based on the type change).

   *)

  (* Issue for borrowing:
     if we borrow a maybe_uninit T but really need a T, we need to know that and commit to it ahead of time (when borrowing) because of restricted subtyping.
     Solutions:
     - actually do a reborrow when subtyping, since the refinement gives us enough information
        then there's a lot of stuff happening there. it also needs later credits. so this gets quite fragile.
     - can we do the previous thing without reborrowing? could this ability be directly built into mut refs?
        in principle, stuff like this that is enabled by the refinements should be more natural.
        Point is: our refinement model is too inflexible. we need more leverage to say that the other case (None) is vacuous because of refinement info.
          - this is not quite true, because the lender will still expect the maybe_uninit back, not the full thing.
            in a sense, this case is really similar to the [u8; 2] ≈ u16 case. It's basically equivalent according to the intuitive notion of subtyping (taking into account the refinement) but it doesn't hold in our model.
     - have custom rules and just say that we generally borrow the T instead of the maybe_uninit when the refinement says so.
        this makes it a bit less flexible, but it's probably fine. the annoying part is that we have to duplicate the borrowing logic a bit.
     => TODO which of these makes most sense?
   *)
