From refinedrust Require Export type.
From refinedrust Require Import util hlist axioms.
From refinedrust Require Import uninit_def.
From refinedrust Require Import options.

(** * Struct types *)
(** Basic design notes:
   - parameterized by a (heterogeneous) list of [type]s.
   - for refinements, use a heterogeneous list, indexed by the refinement.
   - parameterize by the [struct_layout_spec] *)

(** We define [is_struct_ot] not just on the syntactic type, but also directly involve the component types [tys],
  because this stratifies the recursion going on and we anyways need to define a relation involving the [mt] for the semantic types. *)
Definition is_struct_ot `{typeGS Σ} (sls : struct_layout_spec)
    {rts : list RT} (tys : hlist type rts) (ot : op_type) (mt : memcast_compat_type) :=
  match ot with
  | StructOp sl ots =>
      length (sls.(sls_fields)) = length rts ∧
      (* padding bits will be garbled, so we cannot fulfill MCId *)
      mt ≠ MCId ∧
      (* sl is a valid layout for this sls *)
      use_struct_layout_alg sls = Some sl ∧
      length ots = length rts ∧
      (* pointwise, the members have the right op_type and a layout matching the optype *)
      foldr (λ ty, and (let '(ty, ot) := ty in
     ty_has_op_type (projT2 ty : type _) ot mt ∧
          syn_type_has_layout ((projT2 ty).(ty_syn_type) MetaNone) (ot_layout ot)))
        True (zip (hzipl _ tys) ots)
  | UntypedOp ly =>
      (* lyis a valid layout for this sls *)
      ∃ sl, use_struct_layout_alg sls = Some sl ∧ ly = sl
  | _ => False
  end.
Global Typeclasses Opaque is_struct_ot.

Lemma is_struct_ot_layout `{typeGS Σ} sls sl {rts} (tys : hlist type rts) ot mt :
  use_struct_layout_alg sls = Some sl →
  is_struct_ot sls tys ot mt → ot_layout ot = sl.
Proof. move => ? ?. destruct ot => //; naive_solver. Qed.

(** ** Full structs *)
Section structs.
  Context `{!typeGS Σ}.

  Implicit Types (rt : RT).

  Definition struct_own_el_val (π : thread_id) (i : nat) (fields : field_list) (v : val) {rt} (r : place_rfn rt) (ty : type rt) : iProp Σ :=
    ∃ (r' : rt) (ly0 : layout), place_rfn_interp_owned r r' ∗
      ⌜snd <$> fields !! i = Some ly0⌝ ∗
      ⌜syn_type_has_layout (ty_syn_type ty MetaNone) ly0⌝ ∗
      v ◁ᵥ{ π, MetaNone} r' @ ty.
  Definition struct_own_el_loc (π : thread_id) (q : Qp) (v : val) (i : nat) (fields : field_list) (l : loc) {rt} (r : place_rfn rt) (ty : type rt) : iProp Σ :=
    ∃ (r' : rt) (ly : layout), place_rfn_interp_owned r r' ∗
      ⌜snd <$> fields !! i = Some ly⌝ ∗
      ⌜syn_type_has_layout (ty_syn_type ty MetaNone) ly⌝ ∗
      ty_sidecond ty ∗
      (l +ₗ offset_of_idx fields i) ↦{q} v ∗
      ⌜v `has_layout_val` ly ⌝ ∗
      v ◁ᵥ{ π, MetaNone} r' @ ty.
  Definition struct_own_el_loc' (π : thread_id) (q : Qp) (v : val) (i : nat) (fields : field_list) (l : loc) {rt} (r : place_rfn rt) (ty : type rt) (ly : layout) : iProp Σ :=
    ⌜v `has_layout_val` ly⌝ ∗
    ⌜snd <$> fields !! i = Some ly⌝ ∗
    (l +ₗ offset_of_idx fields i) ↦{q} v ∗
    ∃ (r' : rt), place_rfn_interp_owned r r' ∗
      ⌜syn_type_has_layout (ty_syn_type ty MetaNone) ly⌝ ∗
      ty_sidecond ty ∗
      v ◁ᵥ{ π, MetaNone} r' @ ty.
  Definition struct_own_el_shr (π : thread_id) (κ : lft) (i : nat) (fields : field_list) (l : loc) {rt} (r : place_rfn rt) (ty : type rt) : iProp Σ :=
    ∃ (r' : rt) (ly : layout), place_rfn_interp_shared r r' ∗
      ⌜snd <$> fields !! i = Some ly⌝ ∗
      ⌜syn_type_has_layout (ty.(ty_syn_type) MetaNone) ly⌝ ∗
      ty_sidecond ty ∗
      (l +ₗ Z.of_nat (offset_of_idx fields i)) ◁ₗ{π, MetaNone, κ} r' @ ty.

  Definition struct_make_uninit_type (ly : layout) : sigT (λ rt : RT, (type rt * place_rfn rt)%type) :=
    existT (unit : RT) (uninit (UntypedSynType ly), #()).

  Lemma struct_own_val_extract_pointsto' π q sls sl l (tys : list (sigT (λ rt, type rt * place_rfn rt)%type)) ys :
    use_struct_layout_alg sls = Some sl →
    length tys = length (sls_fields sls) →
    loc_in_bounds l 0 (ly_size sl) -∗
    ([∗ list] i↦a;x ∈ pad_struct (sl_members sl) tys struct_make_uninit_type;ys,
      struct_own_el_loc' π q x.1 i (sl_members sl) l (projT2 a).2 (projT2 a).1 x.2) -∗
    l ↦{q} (mjoin ys.*1) ∗ ⌜Forall2 (λ (v : val) (ly : layout), v `has_layout_val` ly) ys.*1 ((sl_members sl).*2)⌝ ∗
      ([∗ list] i↦v';ty ∈ reshape (ly_size <$> (sl_members sl).*2) (mjoin ys.*1);
            pad_struct (sl_members sl) tys (λ ly0 : layout, existT (unit : RT) (uninit (UntypedSynType ly0), # ())),
      struct_own_el_val π i sl.(sl_members) v' (projT2 ty).2 (projT2 ty).1).
  Proof.
    iIntros (??) "#Hlb Hl".

    do 3 rewrite big_sepL2_sep. iDestruct "Hl" as "(Hlyv & Hsl & Hl & Hb)".
    rewrite !big_sepL2_elim_l.
    iDestruct "Hlyv" as "%Hlyv". iDestruct "Hsl" as "%Hsl".
    iPoseProof (big_sepL2_length with "Hb") as "%Hlen_eq".
    rewrite pad_struct_length in Hlen_eq.

    set (vs := ys.*1). set (lys := ys.*2).

    assert (Forall2 (λ (v : val) (ly : layout), v `has_layout_val` ly) vs ((sl_members sl).*2)).
    { rewrite Forall2_fmap_r.
      apply Forall2_same_length_lookup.
      split. { rewrite Hlen_eq /vs length_fmap//. }
      intros i v' [n ly'] Hlook1 Hlook2.
      apply list_lookup_fmap_Some in Hlook1 as ([v1 ly1] & -> & Hlook1) .
      simpl. specialize (Hsl _ _ Hlook1). move: Hsl.
      rewrite Hlook2 /= => [= ->]. apply (Hlyv _ _ Hlook1). }

    iSplitL "Hl".
    { iApply heap_pointsto_reshape_sl. { apply mjoin_has_struct_layout. done. }
      rewrite reshape_join. { iFrame "Hlb". by iApply big_sepL_fmap. }
      apply Forall2_same_length_lookup.
      split. { rewrite !length_fmap//. }
      intros i v' sz Hlook1 Hlook2.
      apply list_lookup_fmap_Some in Hlook1 as ([v1 ly1] & -> & Hlook1) .
      simpl. specialize (Hsl _ _ Hlook1). move: Hsl.
      apply list_lookup_fmap_Some in Hlook2 as (ly' & -> & Hlook).
      rewrite list_lookup_fmap in Hlook. rewrite Hlook => [=->].
      apply (Hlyv _ _ Hlook1). }

    iR.
    iAssert (
      [∗ list] i ↦ y2; y1 ∈ vs; pad_struct (sl_members sl) tys struct_make_uninit_type,
        let 'existT rt (ty, r0) := y1 in ∃ (r' : (rt : RT)) (ly : layout), place_rfn_interp_owned r0 r' ∗
            ⌜snd <$> sl_members sl !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ty_syn_type ty MetaNone) ly⌝ ∗ ty_sidecond ty ∗ y2 ◁ᵥ{ π, MetaNone} r' @ ty)%I with "[Hb]" as "Hb".
    { iApply big_sepL2_flip. rewrite big_sepL2_fmap_r. iApply (big_sepL2_wand with "Hb").
      iApply big_sepL2_intro. { rewrite pad_struct_length Hlen_eq //. }
      iModIntro. iIntros (k [? []] [v1 ly1] ? Hlook2) "(%r' & ? & ? & ? & ?)".
      iExists _,_. iFrame. iPureIntro. apply (Hsl _ _ Hlook2). }
    rewrite reshape_join; first last.
    { apply Forall2_same_length_lookup. rewrite !length_fmap Hlen_eq. split; first done.
      intros ??? Hlook1 Hlook2.
      apply list_lookup_fmap_Some in Hlook1 as ([v1 ly1] & -> & Hlook1).
      specialize (Hlyv _ _ Hlook1). rewrite Hlyv.
      specialize (Hsl _ _ Hlook1). simpl in *.
      apply list_lookup_fmap_Some in Hlook2 as (ly2 & -> & Hlook2).
      rewrite list_lookup_fmap in Hlook2. f_equiv.
      rewrite Hsl in Hlook2. injection Hlook2 as [= ->]; done. }
    iApply (big_sepL2_wand with "Hb").
    iApply big_sepL2_intro. { rewrite pad_struct_length Hlen_eq length_fmap //. }
    iModIntro. iIntros (?? [? []] ? ?). iIntros "(% & % & ? & ? & ? & ? & ?)".
    rewrite /struct_own_el_val.
    eauto with iFrame.
  Qed.

  Lemma struct_own_val_extract_pointsto π q sls sl l (tys : list (sigT (λ rt, type rt * place_rfn rt)%type)) :
    use_struct_layout_alg sls = Some sl →
    length tys = length (sls_fields sls) →
    loc_in_bounds l 0 (ly_size sl) -∗
    ([∗ list] i↦ty ∈ pad_struct (sl_members sl) tys struct_make_uninit_type,
      ∃ v, struct_own_el_loc π q v i sl.(sl_members) l (projT2 ty).2 (projT2 ty).1) -∗
    ∃ v : val, l ↦{q} v ∗ ⌜v `has_layout_val` sl⌝ ∗
      ([∗ list] i↦v';ty ∈ reshape (ly_size <$> (sl_members sl).*2) v; pad_struct (sl_members sl) tys struct_make_uninit_type,
      struct_own_el_val π i sl.(sl_members) v' (projT2 ty).2 (projT2 ty).1).
  Proof.
    iIntros (??) "#Hlb Hl".
    iAssert (
      [∗ list] i↦ty ∈ pad_struct (sl_members sl) tys (λ ly0, existT (unit : RT) (uninit (UntypedSynType ly0), # ())),
      ∃ (y : val * layout),
      struct_own_el_loc' π q y.1 i sl.(sl_members) l (projT2 ty).2 (projT2 ty).1 y.2)%I with "[Hl]" as "Hl".
    { iApply (big_sepL_wand with "Hl"). iApply big_sepL_intro.
      iModIntro. iIntros (k [? []] Hlook). iIntros "(%v & % & %ly0 & ? & ? & ? & ? & ? & ? & ?)".
      iExists (v, ly0). rewrite /struct_own_el_loc'. eauto with iFrame. }
    rewrite big_sepL_exists. iDestruct "Hl" as "(%ys & Hl)".
    iExists (mjoin ys.*1).
    iPoseProof (struct_own_val_extract_pointsto' with "Hlb Hl") as "(Hl & %Ha & Hs)"; [done.. | ].
    iFrame. iPureIntro. by apply mjoin_has_struct_layout.
  Qed.

  Lemma struct_own_val_join_pointsto π q sls sl l v (tys : list (sigT (λ rt, type rt * place_rfn rt)%type)) :
    use_struct_layout_alg sls = Some sl →
    length tys = length (sls_fields sls) →
    v `has_layout_val` sl →
    l ↦{q} v -∗
    ([∗ list] i↦v';ty ∈ reshape (ly_size <$> (sl_members sl).*2) v; pad_struct (sl_members sl) tys struct_make_uninit_type,
        struct_own_el_val π i sl.(sl_members) v' (projT2 ty).2 (projT2 ty).1) -∗
    ([∗ list] i↦ty ∈ pad_struct (sl_members sl) tys struct_make_uninit_type,
      ∃ v, struct_own_el_loc π q v i sl.(sl_members) l (projT2 ty).2 (projT2 ty).1).
  Proof.
    iIntros (???) "Hl Hv".
    rewrite heap_pointsto_reshape_sl; last done.
    iDestruct "Hl" as "(_ & Hp)".
    iPoseProof (big_sepL_extend_r (pad_struct (sl_members sl) tys struct_make_uninit_type) with "Hp") as "Hp".
    { rewrite pad_struct_length length_reshape !length_fmap//. }
    iPoseProof (big_sepL2_sep_1 with "Hv Hp") as "Ha".
    iApply big_sepL2_elim_l. iApply (big_sepL2_wand with "Ha").
    iApply big_sepL2_intro.
    { rewrite pad_struct_length length_reshape !length_fmap//. }
    iModIntro. iIntros (k v' [rt [ty r']] Hlook1 Hlook2).
    iIntros "((%r'' & %ly' & Hrfn & %Hlook3 & %Hst & Hv) & Hp)".
    iExists v', r'', ly'. iPoseProof (ty_own_val_sidecond with "Hv") as "#$".
    iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
    iFrame. done.
  Qed.

  (** We use a [hlist] for the list of types and a [plist] for the refinement, to work around universe problems.
     See also the [ltype] definition. Using just [hlist] will cause universe problems, while using [plist] in the [lty]
     inductive will cause strict positivity problems. *)
  (*#[universes(polymorphic)]*)
  Program Definition struct_t {rts : list RT} (sls : struct_layout_spec) (tys : hlist type rts) : type (plistRT rts) := {|
    (* TODO: support metadata for last struct field *)
    ty_metadata_kind := MetadataNone;
    ty_own_val π r m v :=
      (∃ sl,
        ⌜m = MetaNone⌝ ∗
        ⌜use_struct_layout_alg sls = Some sl⌝ ∗
        ⌜length rts = length sls.(sls_fields)⌝ ∗
        ⌜v `has_layout_val` sl⌝ ∗
        (* the padding fields get the uninit type *)
        [∗ list] i ↦ v';ty ∈ reshape (ly_size <$> sl.(sl_members).*2) v; pad_struct sl.(sl_members) (hpzipl rts tys r) struct_make_uninit_type,
          struct_own_el_val π i sl.(sl_members) v' (projT2 ty).2 (projT2 ty).1
          )%I;
    ty_sidecond := ⌜length rts = length (sls_fields sls)⌝;
    _ty_has_op_type ot mt :=
      is_struct_ot sls tys ot mt;
    ty_syn_type _ := sls : syn_type;
    ty_shr κ π r m l :=
      (∃ sl,
        ⌜m = MetaNone⌝ ∗
        ⌜use_struct_layout_alg sls = Some sl⌝ ∗
        ⌜length rts = length sls.(sls_fields)⌝ ∗
        ⌜l `has_layout_loc` sl⌝ ∗
        loc_in_bounds l 0 (ly_size sl) ∗
        [∗ list] i ↦ ty ∈ pad_struct sl.(sl_members) (hpzipl rts tys r) struct_make_uninit_type,
          struct_own_el_shr π κ i sl.(sl_members) l (projT2 ty).2 (projT2 ty).1)%I;
    ty_ghost_drop π r :=
      ([∗ list] x ∈ hpzipl rts tys r,
        ∃ r' : RT_rt (projT1 x), place_rfn_interp_owned ((projT2 x).2) r' ∗
        ty_ghost_drop (projT2 x).1 π r')%I;
    _ty_lfts := mjoin (fmap (λ ty, ty_lfts (projT2 ty)) (hzipl rts tys));
    _ty_wf_E := mjoin (fmap (λ ty, ty_wf_E (projT2 ty)) (hzipl rts tys));
  |}.
  Next Obligation.
    intros. induction tys as [ | ?? ty tys IH]; simpl.
    - refine (populate nil_tt).
    - refine (populate (cons_pair _ _)).
      { refine inhabitant. }
      apply IH.
  Defined.
  Next Obligation.
    iIntros (rts sls tys π r m v) "(%sl & -> & %Halg & %Hlen & %Hly & ?)".
    iExists sl. iPureIntro. split; last done.
    by apply use_struct_layout_alg_Some_inv.
  Qed.
  Next Obligation.
    iIntros (rts sls tys ot mt Hot).
    destruct ot.
    all: simpl in *.
    all: try done.
    - destruct Hot as (Hlen & Halg & Hlen' & Hmem).
      simpl. by apply use_struct_layout_alg_Some_inv.
    - destruct Hot as (sl & Halg & ->).
      simpl. by apply use_struct_layout_alg_Some_inv.
  Qed.
  Next Obligation.
    iIntros (rts sls tys π r m v) "(%sl & -> & ? & $ & _)".
  Qed.
  Next Obligation.
    iIntros (rts sls tys ? π r m v) "(%sl & -> & ? & $ & _)".
  Qed.
  Next Obligation. unfold TCNoResolve. apply _. Qed.
  Next Obligation.
    iIntros (rts sls tys κ π l m r) "(%sl & -> & %Halg & %Hly & % & Hmem)".
    iExists sl. iSplitR; first done. iPureIntro.
    by apply use_struct_layout_alg_Some_inv.
  Qed.
  Next Obligation.
    (* sharing *)
    iIntros (rts sls tys E κ l ly π r m q ?) "#(LFT & LLCTX) #Hna Htok %Hst %Hly #Hlb Hl".
    rewrite -lft_tok_sep. iDestruct "Htok" as "(Htok & Htok')".
    iApply fupd_logical_step.

    (* reshape the borrow - we must not freeze the existential over v to initiate recursive sharing *)
    iPoseProof (bor_iff _ _ (∃ sl, ⌜m = MetaNone⌝ ∗ ⌜use_struct_layout_alg sls = Some sl⌝ ∗ ⌜length rts = length (sls_fields sls)⌝ ∗
      [∗ list] i↦ty ∈ pad_struct (sl_members sl) (hpzipl rts tys r) struct_make_uninit_type,
        ∃ v, struct_own_el_loc π 1 v i sl.(sl_members) l (projT2 ty).2 (projT2 ty).1)%I with "[] Hl") as "Hb".
    { iNext. iModIntro. iSplit.
      - iIntros "(%v & Hl & %sl & -> & %Hst' & %Hlen & %Hv & Hv)".
        iExists sl. iR. iR. iR.
        iApply (struct_own_val_join_pointsto with "Hl Hv"); [done | | done].
        rewrite length_hpzipl//.

      - iIntros "(%sl & -> & %Hst' & %Hlen & Hl)".
        assert (ly = sl) as ->.
        { apply use_struct_layout_alg_Some_inv in Hst'. by eapply syn_type_has_layout_inj. }

        iPoseProof (struct_own_val_extract_pointsto with "Hlb Hl") as "(%v & Hl & %Hlyv & Hv)".
        { done. }
        { rewrite length_hpzipl//. }
        iExists v. by iFrame.
    }

    iMod (bor_exists with "LFT Hb") as "(%sl & Hb)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Heq & Hb)"; first done.
    iMod (bor_persistent with "LFT Heq Htok") as "(>-> & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hst & Hb)"; first done.
    iMod (bor_persistent with "LFT Hst Htok") as "(>%Hst' & Htok)"; first done.
    iMod (bor_sep with "LFT Hb") as "(Hlen & Hb)"; first done.
    iMod (bor_persistent with "LFT Hlen Htok") as "(>%Hlen & Htok)"; first done.
    iMod (bor_big_sepL with "LFT Hb") as "Hb"; first done.
    iCombine "Htok Htok'" as "Htok". rewrite lft_tok_sep.
    (* fracture the tokens over the big_sep *)
    set (len := length (sl_members sl)).
    set (κ' := lft_intersect_list (mjoin ((λ ty, ty_lfts (projT2 ty)) <$> hzipl rts tys))).
    iPoseProof (Fractional_split_big_sepL (λ q, q.[_]%I) len with "Htok") as "(%qs & %Hlen' & Htoks & Hcl_toks)".
    iAssert ([∗ list] i ↦ ty; q' ∈ (pad_struct (sl_members sl) (hpzipl rts tys r) struct_make_uninit_type); qs,
      &{κ} ((∃ (r' : (projT1 ty : RT)) (ly : layout), place_rfn_interp_owned (projT2 ty).2 r' ∗ ⌜snd <$> sl.(sl_members) !! i = Some ly⌝ ∗ ⌜syn_type_has_layout (ty_syn_type (projT2 ty).1 MetaNone) ly⌝ ∗ ty_sidecond (projT2 ty).1 ∗ ∃ v, (l +ₗ offset_of_idx sl.(sl_members) i) ↦ v ∗ ⌜v `has_layout_val` ly⌝ ∗ v ◁ᵥ{ π, MetaNone} r' @ (projT2 ty).1)) ∗
      q'.[κ ⊓ κ'])%I with "[Htoks Hb]" as "Hb".
    { iApply big_sepL2_sep_sepL_r; iFrame. iApply big_sepL2_const_sepL_l.
      iSplitR. { rewrite pad_struct_length Hlen' //. }
      (* we also need to push down the existential over v *)
      iApply (big_sepL_wand with "Hb"); iApply big_sepL_intro.
      iModIntro. iIntros (? [? []] ?) "Ha". iApply (bor_iff with "[] Ha").
      iNext. iModIntro. iSplit.
      - iIntros "(%v & % & % & ? & ? & ? & ? & ? & ? & ?)". eauto with iFrame.
      - iIntros "(% & % & ? & ? & ? & ? & Hl)". iDestruct "Hl" as "(%v & ? & ? & ?)".
        rewrite /struct_own_el_loc; eauto with iFrame.
    }

    assert (ly = sl) as ->.
    { apply use_struct_layout_alg_Some_inv in Hst'. by eapply syn_type_has_layout_inj. }
    iAssert ([∗ list] i ↦ ty; q' ∈ (pad_struct (sl_members sl) (hpzipl rts tys r) struct_make_uninit_type); qs,
      logical_step E (
        struct_own_el_shr π κ i sl.(sl_members) l (projT2 ty).2 (projT2 ty).1 ∗ q'.[κ ⊓ κ']))%I with "[Hb]" as "Hb".
    { iApply (big_sepL2_wand with "Hb"). iApply big_sepL2_intro.
      { rewrite pad_struct_length Hlen' //. }
      iModIntro. iIntros (k x q0 Hlook1 Hlook2) "(Hb & Htok)".
      iApply fupd_logical_step.
      destruct x as [rt [ty r']]. set (κ'' := lft_intersect_list (ty_lfts ty)).
      iMod (lft_incl_acc _ _ (κ ⊓ κ'') with "[] Htok") as "(%q' & Htok & Hvs)"; first done.
      { iApply lft_intersect_mono; first iApply lft_incl_refl.
        rewrite /κ' /κ''.
        iApply list_incl_lft_incl_list.
        apply pad_struct_lookup_Some in Hlook1; first last.
        { rewrite length_hpzipl Hlen. erewrite struct_layout_spec_has_layout_fields_length; done. }
        destruct Hlook1 as (n & ly & ? & [ (? & Hlook) | (-> & Heq)]).
        - simpl in Hlook.
          apply (hpzipl_lookup_inv_hzipl_pzipl _ _ r) in Hlook as (Hlook & _).
          apply list_subseteq_mjoin. apply list_elem_of_fmap.
          exists (existT _ ty). split; first done.
          apply list_elem_of_lookup_2 in Hlook. done.
        - injection Heq => Heq1 Heq2 ?. subst.
          apply existT_inj in Heq1 as ->.
          apply existT_inj in Heq2 as ->.
          rewrite ty_lfts_unfold; simpl.
          set_solver.
      }
      rewrite -{1}lft_tok_sep. iDestruct "Htok" as "(Htok1 & Htok2)".
      iMod (bor_exists_tok with "LFT Hb Htok1") as "(%r'' & Hb & Htok1)"; first done.
      iMod (bor_exists_tok with "LFT Hb Htok1") as "(%ly' & Hb & Htok1)"; first done.
      iMod (bor_sep with "LFT Hb") as "(Hrfn & Hb)"; first done.
      iMod (place_rfn_interp_owned_share with "LFT Hrfn Htok1") as "(Ha & Htok1)"; first done.
      iMod (bor_sep with "LFT Hb") as "(Hly & Hb)"; first done.
      iMod (bor_persistent with "LFT Hly Htok1") as "(>%Hly' & Htok1)"; first done.
      iMod (bor_sep with "LFT Hb") as "(Hst & Hb)"; first done.
      iMod (bor_persistent with "LFT Hst Htok1") as "(>%Hst'' & Htok1)"; first done.
      iMod (bor_sep with "LFT Hb") as "(Hsc & Hb)"; first done.
      iMod (bor_persistent with "LFT Hsc Htok1") as "(>Hsc & Htok1)"; first done.

      iPoseProof (bor_iff _ _ (∃ v : val, (l +ₗ offset_of_idx (sl_members sl) k) ↦ v ∗ v ◁ᵥ{π, MetaNone} r'' @ ty) with "[] Hb") as "Hb".
      { iNext. iModIntro. iSplit.
        - iIntros "(%v & Hl & %Hlyv & Hv)". iExists v. iFrame.
        - iIntros "(%v & Hl & Hv)". iExists v.
          iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
          iFrame. done. }

      iCombine "Htok1 Htok2" as "Htok". rewrite lft_tok_sep. iModIntro.
      subst κ''. rewrite ty_lfts_unfold.
      iPoseProof (ty_share with "[$LFT $LLCTX] Hna Htok [] [] [] Hb") as "Hb"; first done.
      - done.
      - iPureIntro. by apply struct_layout_field_aligned.
      - iApply loc_in_bounds_sl_offset; done.
      - iApply logical_step_fupd.
        iApply (logical_step_wand with "Hb"). iIntros "(? & Htok)".
        iMod ("Hvs" with "Htok").
        iFrame. iModIntro. simpl.
        by iExists _.
    }
    iPoseProof (logical_step_big_sepL2 with "Hb") as "Hb".
    iModIntro. iApply (logical_step_wand with "Hb"). iIntros "Hb".
    iPoseProof (big_sepL2_sep_sepL_r with "Hb") as "(Hb & Htok)".
    iPoseProof ("Hcl_toks" with "Htok") as "$".
    iPoseProof (big_sepL2_const_sepL_l with "Hb") as "(_ & Hb)".
    iExists _. do 5 iR. done.
  Qed.
  Next Obligation.
    (* monotonicity of sharing *)
    iIntros (rts sls tys κ κ' π r m l) "#Hincl (%sl & -> & %Hsl & %Hlen & %Hly & Hlb & Hb)".
    iExists sl. do 4 iR. iFrame.
    iApply (big_sepL_wand with "Hb"). iApply big_sepL_intro.
    iModIntro. iIntros (k [rt [ty r']] Hlook).
    iIntros "(%r'' & %ly & ? & ? & ? & ? & Hb)".
    iExists _, _. iFrame.
    iApply (ty_shr_mono with "Hincl Hb").
  Qed.
  Next Obligation.
    iIntros (rts sls tys π r m v F ?). simpl.
    iIntros "(%sl & -> & %Halg & %Hlen & %Hlyv & Hv)".
    iPoseProof (big_sepL_to_exists_l with "Hv") as "Hv".
    iPoseProof (pad_struct_focus_no_uninit with "Hv") as "(Hv & _)".
    { rewrite length_hpzipl. rewrite named_fields_field_names_length (struct_layout_spec_has_layout_fields_length sls); done. }
    { specialize (sl_nodup sl). rewrite bool_decide_spec. done. }
    iApply logical_step_big_sepL.
    iApply (big_sepL_impl with "Hv").
    iModIntro. iIntros (? [rt [lt r1]] ?).
    iIntros "(%j & % & % & % & % & % & Hv)".
    iDestruct "Hv" as "(% & % & Hrfn & % & % & Hv)".
    simpl. iPoseProof (ty_own_ghost_drop _ _ _ _ _ _ F with "Hv") as "Hv"; first done.
    iApply (logical_step_wand with "Hv").
    iIntros "$". done.
  Qed.
  Next Obligation.
    iIntros (rts sls tys ot mt st π r m v Hot).
    apply (mem_cast_compat_Untyped) => ?.
    iIntros "(%sl & -> & %Halg & %Hlen & %Hsl & Hmem)".
    destruct ot as [ | | | sl' ots | | ]; try done.
    destruct Hot as (Hlen' & ? & Halg' & Hlen_ots & Hot%Forall_fold_right).
    assert (sl' = sl) as ->. { by eapply struct_layout_spec_has_layout_inj. }
    destruct mt.
    - done.
    - iExists sl. do 3 iR.
      iSplitR. { rewrite /has_layout_val mem_cast_length. done. }
      assert (length (field_names (sl_members sl)) = length (sls_fields sls)) as Hlen2.
      { by eapply struct_layout_spec_has_layout_fields_length. }
      (* we memcast the value and need to show that it is preserved *)
      iAssert ⌜∀ i v' n ly,
           reshape (ly_size <$> (sl_members sl).*2) v !! i = Some v' →
           sl_members sl !! i = Some (Some n, ly) → v' `has_layout_val` ly⌝%I as %?. {
        iIntros (i v' n ly Hv' Hly).
        (* lookup the corresponding index and type assignment for the member *)
        have [|rt Hlook]:= lookup_lt_is_Some_2 rts (field_idx_of_idx (sl_members sl) i).
        { have := field_idx_of_idx_bound sl i _ _ ltac:(done). lia. }
        edestruct (hpzipl_lookup rts tys r) as [ty [r' Hlook2]]; first done.
        iDestruct (big_sepL2_lookup with "Hmem") as "Hv"; [done| |].
        { apply/pad_struct_lookup_Some. { rewrite length_hpzipl Hlen. done. }
          naive_solver. }
        (* lookup the ot *)
        have [|ot ?]:= lookup_lt_is_Some_2 ots (field_idx_of_idx (sl_members sl) i).
        { have := field_idx_of_idx_bound sl i _ _ ltac:(done). lia. }
        iDestruct "Hv" as "(%r'' & %ly0 & Hrfn & %Ha & % & Hv)".
        iPoseProof (ty_has_layout with "Hv") as "(%ly' & %Halg'' & %Hly')".
        enough (ly' = ly) as ->; first done.
        assert (ly0 = ly') as -> by by eapply syn_type_has_layout_inj.
        rewrite Hly in Ha. by injection Ha.
      }
      iFrame. iApply (big_sepL2_impl' with "Hmem"); [by rewrite !length_reshape |done|].
      iIntros "!>" (k v1 ty1 v2 ty2 Hv1 Hty1 Hv2 Hty2) "Hv"; simplify_eq.
      destruct ty1 as (rt1 & ty1 & r1).
      rewrite mem_cast_struct_reshape // in Hv2; last congruence.
      move: Hv2 => /lookup_zip_with_Some [?[?[?[Hpad Hv']]]]. simplify_eq.
      rewrite Hv1 in Hv'. simplify_eq.
      iDestruct "Hv" as "(%r' & % & Hrfn & %Hlook & % & Hv)". iExists r', _. iFrame.
      move: Hty1 => /pad_struct_lookup_Some[|n[?[Hlook2 Hor1]]].
      { rewrite length_hpzipl Hlen. done. }
      move: Hpad => /pad_struct_lookup_Some[|?[?[? Hor2]]]. { rewrite length_fmap. congruence. } simplify_eq.
      destruct Hor1 as [[??] | [? ?]], Hor2 as [[? Hl] |[? ?]]; simplify_eq.
      + rewrite list_lookup_fmap in Hl. move: Hl => /fmap_Some[ot [??]]. simplify_eq.
        iSplitR; first done. iSplitR; first done.
        iApply ty_memcast_compat_copy; [|done]. destruct n as [n|] => //.
        (* lookup layout in sl *)
        (*have [|p ?]:= lookup_lt_is_Some_2 (field_members (sl_members sl)) (field_idx_of_idx (sl_members sl) k).*)
        (*{ have := field_idx_of_idx_bound sl k _ _ ltac:(done). rewrite field_members_length. lia. }*)
        simpl in *.
        move: Hot => /(Forall_lookup_1 _ _ (field_idx_of_idx (sl_members sl) k) (existT _ ty1, ot)).
        (*destruct p as [p ?].*)
        move => [|??]; last done.
        apply/lookup_zip_with_Some. eexists _, _. split_and!; [done| |done].
        (*apply/lookup_zip_with_Some. eexists _, _.*)
        (*split; first done. split; last done.*)
        match goal with
        | H : hpzipl rts _ _ !! _ = Some _ |- _ => eapply (hpzipl_lookup_inv_hzipl_pzipl rts tys r) in H as [-> _]
        end. done.
      + unfold struct_make_uninit_type in *.
        match goal with | H : existT _ _ = existT _ _ |- _ => rename H into Heq end.
        injection Heq => Heq1 Heq2 ?. subst.
        apply existT_inj in Heq1. apply existT_inj in Heq2. subst.
        do 3 iR.
        iExists _; iPureIntro. split; first done.
        rewrite /has_layout_val length_replicate.
        rewrite Hlook2 in Hlook. injection Hlook as [= ->].
        done.
    - iPureIntro. done.
  Qed.
  Next Obligation.
    intros ??? ly mt _ Hst.
    apply syn_type_has_layout_struct_inv in Hst as (fields & sl & -> & Halg & Hf).
    simpl. exists sl. split; last done.
    by eapply use_struct_layout_alg_Some.
  Qed.


  (* Useful lemmas for proving properties about our interpretation of enums *)
  Lemma struct_t_own_val_dist {rts1 rts2} sls (Ts1 : hlist type rts1) (Ts2 : hlist type rts2) r1 r2 v π m n :
    Forall2 (λ '(existT _ (T1, r1)) '(existT _ (T2, r2)),
        ∀ i fields v,
          struct_own_el_val π i fields v r1 T1 ≡{n}≡ struct_own_el_val π i fields v r2 T2
    ) (hpzipl _ Ts1 r1) (hpzipl _ Ts2 r2) →
    (v ◁ᵥ{π, m} r1 @ struct_t sls Ts1)%I ≡{n}≡ (v ◁ᵥ{π, m} r2 @ struct_t sls Ts2)%I.
  Proof.
    intros Hel.
    specialize (Forall2_length  _ _ _ Hel) as Hlen.
    rewrite !length_hpzipl in Hlen.
    rewrite /ty_own_val/=.
    f_equiv => sl.
    apply sep_ne_proper => Hmeta.
    apply sep_ne_proper => Halg.
    rewrite Hlen.
    apply sep_ne_proper => Hlen'.
    f_equiv.
    specialize (struct_layout_spec_has_layout_fields_length _ _ Halg) as Hlen2.
    rewrite -field_members_length -Hlen' in Hlen2. clear Hlen'.

    subst m.
    elim: (sl_members sl) rts1 rts2 Ts1 Ts2 r1 r2 Hlen2 Hel Hlen v => //.
    intros [m ?] s IH rts1 rts2 Ts1 Ts2 r1 r2 Hlen2 Hel Hlen v; csimpl.
    destruct m; simpl in *.
    + destruct rts1 as [ | rt1 rts1]; destruct rts2 as [ | rt2 rts2]; try done.
      inv_hlist Ts1 => T1 Ts1.
      inv_hlist Ts2 => T2 Ts2.
      destruct r1 as [r1' r1]. destruct r2 as [r2' r2].
      simpl.
      intros Hel. apply Forall2_cons_inv in Hel as [Hel1 Hel].
      f_equiv. { apply Hel1. }
      eapply IH.
      { simpl in *. lia. }
      { done. }
      { simpl in *. lia. }
    + f_equiv. eapply IH; done.
  Qed.
  Lemma struct_t_shr_dist {rts1 rts2} sls (Ts1 : hlist type rts1) (Ts2 : hlist type rts2) r1 r2 l π κ m n :
    Forall2 (λ '(existT _ (T1, r1)) '(existT _ (T2, r2)),
        ∀ i fields l,
          struct_own_el_shr π κ i fields l r1 T1 ≡{n}≡ struct_own_el_shr π κ i fields l r2 T2
    ) (hpzipl _ Ts1 r1) (hpzipl _ Ts2 r2) →
    (l ◁ₗ{π, m, κ} r1 @ struct_t sls Ts1)%I ≡{n}≡ (l ◁ₗ{π, m, κ} r2 @ struct_t sls Ts2)%I.
  Proof.
    intros Hel.
    specialize (Forall2_length  _ _ _ Hel) as Hlen.
    rewrite !length_hpzipl in Hlen.
    rewrite /ty_shr/=.
    f_equiv => sl.
    apply sep_ne_proper => Hmeta.
    apply sep_ne_proper => Halg.
    rewrite Hlen.
    apply sep_ne_proper => Hlen'.
    f_equiv. f_equiv.
    specialize (struct_layout_spec_has_layout_fields_length _ _ Halg) as Hlen2.
    rewrite -field_members_length -Hlen' in Hlen2. clear Hlen'.
    subst m.

    elim: (sl_members sl) rts1 rts2 Ts1 Ts2 r1 r2 Hlen2 Hel Hlen l => //.
    intros [m ly] s IH rts1 rts2 Ts1 Ts2 r1 r2 Hlen2 Hel Hlen l; csimpl.
    destruct m; simpl in *.
    + destruct rts1 as [ | rt1 rts1]; destruct rts2 as [ | rt2 rts2]; try done.
      inv_hlist Ts1 => T1 Ts1.
      inv_hlist Ts2 => T2 Ts2.
      destruct r1 as [r1' r1]. destruct r2 as [r2' r2].
      simpl.
      intros Hel. apply Forall2_cons_inv in Hel as [Hel1 Hel].
      f_equiv. { apply Hel1. }
      rewrite /struct_own_el_shr/=.
      unfold offset_of_idx; simpl.
      setoid_rewrite <-shift_loc_assoc_nat.
      eapply IH.
      { simpl in *. lia. }
      { done. }
      { simpl in *. lia. }
    + f_equiv.
      rewrite /struct_own_el_shr/=.
      unfold offset_of_idx; simpl.
      setoid_rewrite <-shift_loc_assoc_nat.
      apply IH; done.
  Qed.

  Global Instance struct_t_ne {rt} {rts : list RT} sls (Ts : type rt → hlist type rts) :
    HTypeNonExpansive Ts →
    TypeNonExpansive (λ ty, struct_t (sls (st_of ty MetaNone)) (Ts ty)).
  Proof.
    intros HT. constructor.
    - simpl. done.
    - simpl. intros ?? Hst _. rewrite Hst. done.
    - apply ty_lft_morphism_of_direct.
      rewrite ty_wf_E_unfold/=.
      rewrite ty_lfts_unfold/=.
      simpl.
      destruct HT as [HT' Hne ->].
      induction rts as [ | rt1 rts IH].
      + inv_hlist HT'. intros _. simpl.
        apply direct_lft_morph_make_const.
      + inv_hlist HT' => T1 HT.
        intros [Hne1 Hne]%HTForall_cons_inv.
        simpl. apply direct_lft_morphism_app.
        { eapply ty_lft_morphism_to_direct.
          apply Hne1. }
        by apply IH.
    - move => ty ty' Hst Hot ot mt /=. rewrite ty_has_op_type_unfold/= /is_struct_ot.
      rewrite Hst.
      destruct HT as [Ts' Hne ->].
      destruct ot as [ | | | sl ots | ly | ] => //=.
      apply and_proper => Hsl.
      f_equiv. apply and_proper => Halg. apply and_proper => Hots. rewrite -!Forall_fold_right.
      erewrite <-struct_layout_spec_has_layout_fields_length in Hsl; last done.
      rewrite -field_members_length in Hsl.

      elim: (field_members (sl_members sl)) ots rts Ts' Hne Hsl Hots => //; csimpl.
      { intros ots rts Ts' Hne Heq Hlen. destruct rts; last done.
        inv_hlist Ts'. intros _. destruct ots; done. }
      move => [m ?] s IH ots rts Ts' Hne Hlen1 Hlen2.
      destruct rts as [ | rt1 rts]; first done. destruct ots as [ | ot ots]; first done.
      inv_hlist Ts' => T1 Ts'.
      intros Ha.
      apply HTForall_cons_inv in Ha as (Hne1 & Hne2).
      simplify_eq/=; rewrite !Forall_cons/=; f_equiv.
      { solve_type_proper. }
      eapply IH; done.
    - simpl. intros ?? Hst. rewrite Hst. done.
    - intros n ty ty' Hd.
      destruct HT as [Ts' Hne ->].
      iIntros (π r m v). rewrite /ty_own_val/=.
      f_equiv => sl.
      rewrite type_dist_st.
      rewrite /struct_own_el_val.
      apply sep_ne_proper => Hmeta. subst m.
      apply sep_ne_proper => Halg. apply sep_ne_proper => Hlen.
      f_equiv.
      specialize (struct_layout_spec_has_layout_fields_length _ _ Halg) as Hlen2.
      rewrite -field_members_length -Hlen in Hlen2. clear Hlen.
      elim: (sl_members sl) rts Ts' Hne r Hlen2 v => //.
      intros [m ?] s IH rts Ts' Hne r Hlen v; csimpl.
      destruct m; simpl in *.
      + destruct rts as [ | rt1 rts]; first done.
        inv_hlist Ts' => T1 Ts'.
        intros [Hne1 Hne]%HTForall_cons_inv.
        simpl. f_equiv. { rewrite /struct_own_el_val. solve_type_proper. }
        eapply IH; first done. simpl in Hlen. lia.
      + f_equiv. eapply IH; done.
    - intros n ty ty' Hd.
      destruct HT as [Ts' Hne ->].
      iIntros (κ π r m l). rewrite /ty_shr /= /struct_own_el_shr/=.
      rewrite type_dist2_st.
      f_equiv => sl.
      apply sep_ne_proper => Hmeta. subst m.
      apply sep_ne_proper => Halg. apply sep_ne_proper => Hlen.
      f_equiv.
      f_equiv.
      specialize (struct_layout_spec_has_layout_fields_length _ _ Halg) as Hlen2.
      rewrite -field_members_length -Hlen in Hlen2. clear Hlen.
      elim: (sl_members sl) rts Ts' Hne r Hlen2 l => //.
      intros [m ly] s IH rts Ts' Hne r Hlen l; csimpl.
      destruct m; simpl in *.
      + destruct rts as [ | rt1 rts]; first done.
        inv_hlist Ts' => T1 Ts'.
        intros [Hne1 Hne]%HTForall_cons_inv.
        simpl. f_equiv. { solve_type_proper. }
        cbn. setoid_rewrite <-shift_loc_assoc_nat.
        eapply IH; first done. simpl in Hlen. lia.
      + f_equiv. setoid_rewrite <-shift_loc_assoc_nat. apply IH; done.
    - intros n ty ty' Hd.
      destruct HT as [Ts' Hne ->].
      iIntros (π r). rewrite /ty_ghost_drop/=.
      elim: rts Ts' Hne r => //.
      { simpl. intros Ts'. inv_hlist Ts'. simpl. done. }
      intros rt' rts IH Ts' Hne r.
      inv_hlist Ts'. intros T1 Ts'.
      intros [Hne1 Hne]%HTForall_cons_inv.
      simpl. f_equiv.
      { solve_type_proper. }
      apply IH; done.
  Qed.

  (* For this to be contractive, the [sls] must not depend on the recursive type *)
  (* TODO reduce duplication? *)
  Global Instance struct_t_contr {rt} {rts : list RT} sls (Ts : type rt → hlist type rts) :
    TCDone (∀ st1 st2, sls st1 = sls st2) →
    HTypeContractive Ts →
    TypeContractive (λ ty, struct_t (sls (st_of ty MetaNone)) (Ts ty)).
  Proof.
    intros Hst HT. constructor.
    - done.
    - simpl. intros. erewrite Hst. done.
    - apply ty_lft_morphism_of_direct.
      simpl.
      rewrite ty_wf_E_unfold/=.
      rewrite ty_lfts_unfold/=.
      destruct HT as [HT' Hne ->].
      induction rts as [ | rt1 rts IH].
      + inv_hlist HT'. intros _. simpl.
        apply direct_lft_morph_make_const.
      + inv_hlist HT' => T1 HT.
        intros [Hne1 Hne]%HTForall_cons_inv.
        simpl. apply direct_lft_morphism_app; last by apply IH.
        eapply ty_lft_morphism_to_direct.
        apply Hne1.
    - move => ty ty' ot mt /=. rewrite ty_has_op_type_unfold/= /is_struct_ot.
      erewrite Hst.
      destruct HT as [Ts' Hne ->].
      destruct ot as [ | | | sl ots | ly | ] => //=.
      apply and_proper => Hsl.
      f_equiv. apply and_proper => Halg. apply and_proper => Hots. rewrite -!Forall_fold_right.
      erewrite <-struct_layout_spec_has_layout_fields_length in Hsl; last done.
      rewrite -field_members_length in Hsl.

      elim: (field_members (sl_members sl)) ots rts Ts' Hne Hsl Hots => //; csimpl.
      { intros ots rts Ts' Hne Heq Hlen. destruct rts; last done.
        inv_hlist Ts'. intros _. destruct ots; done. }
      move => [m ?] s IH ots rts Ts' Hne Hlen1 Hlen2.
      destruct rts as [ | rt1 rts]; first done. destruct ots as [ | ot ots]; first done.
      inv_hlist Ts' => T1 Ts'.
      intros Ha.
      apply HTForall_cons_inv in Ha as (Hne1 & Hne2).
      simplify_eq/=; rewrite !Forall_cons/=; f_equiv.
      { solve_type_proper. }
      eapply IH; done.
    - simpl. intros. erewrite Hst. done.
    - intros n ty ty' Hd.
      destruct HT as [Ts' Hne ->].
      iIntros (π r m v). rewrite /ty_own_val/=.
      f_equiv => sl.
      rewrite /struct_own_el_val.
      erewrite Hst.
      apply sep_ne_proper => Hmeta. subst m.
      apply sep_ne_proper => Halg. apply sep_ne_proper => Hlen.
      f_equiv.
      specialize (struct_layout_spec_has_layout_fields_length _ _ Halg) as Hlen2.
      rewrite -field_members_length -Hlen in Hlen2. clear Hlen.
      elim: (sl_members sl) rts Ts' Hne r Hlen2 v => //.
      intros [m ?] s IH rts Ts' Hne r Hlen v; csimpl.
      destruct m; simpl in *.
      + destruct rts as [ | rt1 rts]; first done.
        inv_hlist Ts' => T1 Ts'.
        intros [Hne1 Hne]%HTForall_cons_inv.
        simpl. f_equiv. { rewrite /struct_own_el_val. solve_type_proper. }
        eapply IH; first done. simpl in Hlen. lia.
      + f_equiv. eapply IH; done.
    - intros n ty ty' Hd.
      destruct HT as [Ts' Hne ->].
      iIntros (κ π r m l). rewrite /ty_shr /= /struct_own_el_shr/=.
      erewrite Hst.
      f_equiv => sl.
      apply sep_ne_proper => Hmeta. subst m.
      apply sep_ne_proper => Halg. apply sep_ne_proper => Hlen.
      f_equiv.
      f_equiv.
      specialize (struct_layout_spec_has_layout_fields_length _ _ Halg) as Hlen2.
      rewrite -field_members_length -Hlen in Hlen2. clear Hlen.
      elim: (sl_members sl) rts Ts' Hne r Hlen2 l => //.
      intros [m ly] s IH rts Ts' Hne r Hlen l; csimpl.
      destruct m; simpl in *.
      + destruct rts as [ | rt1 rts]; first done.
        inv_hlist Ts' => T1 Ts'.
        intros [Hne1 Hne]%HTForall_cons_inv.
        simpl. f_equiv. { solve_type_proper. }
        cbn. setoid_rewrite <-shift_loc_assoc_nat.
        eapply IH; first done. simpl in Hlen. lia.
      + f_equiv. setoid_rewrite <-shift_loc_assoc_nat. apply IH; done.
    - intros n ty ty' Hd.
      destruct HT as [Ts' Hne ->].
      iIntros (π r). rewrite /ty_ghost_drop/=.
      elim: rts Ts' Hne r => //.
      { simpl. intros Ts'. inv_hlist Ts'. simpl. done. }
      intros rt' rts IH Ts' Hne r.
      inv_hlist Ts'. intros T1 Ts'.
      intros [Hne1 Hne]%HTForall_cons_inv.
      simpl. f_equiv.
      { solve_type_proper. }
      apply IH; done.
  Qed.

  (* variant with constant sls *)
  Global Instance struct_t_contr' {rt} {rts : list RT} sls (Ts : type rt → hlist type rts) :
    HTypeContractive Ts →
    TypeContractive (λ ty, struct_t sls (Ts ty)).
  Proof.
    intros. eapply (struct_t_contr (λ _, _)); done.
  Qed.
End structs.

(** Hint Extern in case we cannot determine the constantness syntactically.
  This can be expensive, so we prefer the other one. *)
Global Hint Extern 100 (TypeContractive (λ ty, struct_t _ _)) =>
  match goal with
  | |- TypeContractive (λ ty : type ?T, struct_t ?sls _) =>
      let c := constr:(λ ty : type T, sls) in
      let sls' := eval cbv in c in
      match sls' with
      | (λ _, ?sls) =>
        eapply (struct_t_contr' sls)
      end
  end: typeclass_instances.

Global Hint Unfold struct_t : tyunfold.

Section init.
  Context `{!typeGS Σ}.
  Lemma struct_val_has_layout sls sl vs :
    Forall3 (λ '(_, ly) '(_, st) v, syn_type_has_layout st ly ∧ v `has_layout_val` ly) (named_fields (sl_members sl)) (sls_fields sls)  vs →
    mjoin (pad_struct (sl_members sl) vs (λ ly : layout, replicate (ly_size ly) ☠%V)) `has_layout_val` sl.
  Proof.
    rewrite {2}/has_layout_val{2}/ly_size/=.
    generalize (sls_fields sls) as fields => fields. clear sls.
    generalize (sl_members sl) as mems => mems. clear sl.
    induction mems as [ | [oname ly] mems IH] in vs, fields |-*; simpl; first done.
    destruct oname as [ name | ].
    - (* named *)
      intros Hf. apply Forall3_cons_inv_l in Hf as ([name2 st] & fields' & v & vs' & -> & -> & [Hst Hv] & Hf).
      rewrite length_app. erewrite IH; last done.
      simpl. rewrite Hv. done.
    - intros Hf. rewrite length_app length_replicate. erewrite IH; last done. done.
  Qed.

  Lemma struct_init_val π sls sl vs {rts : list RT} (tys : hlist type rts) (rs : plist (@id RT) rts) :
    use_struct_layout_alg sls = Some sl →
    length rts = length (sls_fields sls) →
    ([∗ list] i↦v;Ty ∈ vs;hpzipl rts tys rs, let 'existT rt (ty, r) := Ty in
      ∃ (name : string) (st : syn_type) (ly : layout),
        ⌜sls_fields sls !! i = Some (name, st)⌝ ∗ ⌜syn_type_has_layout st ly⌝ ∗
        ⌜syn_type_has_layout (ty_syn_type ty MetaNone) ly⌝ ∗ v ◁ᵥ{ π, MetaNone} r @ ty) -∗
    mjoin (pad_struct (sl_members sl) vs (λ ly : layout, replicate (ly_size ly) ☠%V)) ◁ᵥ{ π, MetaNone} (λ (X : RT) (a : X), # a) -<$> rs @ struct_t sls tys.
  Proof.
    iIntros (Hsl Hlen) "Hv".
    rewrite {2}/ty_own_val /=/struct_own_el_val/=.
    iExists sl. iR. iR. iR.

    apply use_struct_layout_alg_inv in Hsl as (field_lys & Halg & Hfields).
    specialize (struct_layout_alg_pad_align _ _ _ _ Halg) as Hpad.
    specialize (sl_size sl) as Hsize.
    apply struct_layout_alg_has_fields in Halg.
    move: Halg Hfields Hlen Hpad Hsize.
    rewrite /sl_has_members. intros ->.
    rewrite /has_layout_val [ly_size sl]/ly_size/=.
    intros Hsts Hlen Hpad Hsize.

    iSplit.
    { iApply bi.pure_mono; first apply (struct_val_has_layout sls).
      move: Hsts Hlen.
      generalize (sls_fields sls) as sts. generalize (sl_members sl) as mems.
      intros mems sts.
      generalize (named_fields mems) as lys. clear mems. intros lys Hsts Hlen.
      iInduction vs as [ | v vs] "IH" forall (rts tys rs sts lys Hsts Hlen).
      { destruct rts as [ | rt rts]; inv_hlist tys; [destruct rs | destruct rs as [r rs]]; simpl; last done.
        destruct sts; last done. apply Forall2_nil_inv_l in Hsts as ->. iPureIntro. constructor. }
      destruct rts as [ | rt rts]; inv_hlist tys; [destruct rs | destruct rs as [r rs]]; simpl; first done.
      intros ty tys.
      destruct sts as [ | st sts]; first done. simpl.
      iDestruct "Hv" as "((%name & %st' & %ly & %Hst & %Hst' & %Hst'' & Hv) & Hvs)".
      injection Hst as [= ->].
      iPoseProof (ty_own_val_has_layout with "Hv") as "%Hly"; first done.
      apply Forall2_cons_inv_l in Hsts as ([name2 ly'] & lys' & [-> Hst] & Hsts & ->).
      simpl. assert (ly' = ly) as -> by by eapply syn_type_has_layout_inj.
      iPoseProof ("IH" with "[//] [] Hvs") as "%Hf".
      { iPureIntro. simpl in *. lia. }
      iPureIntro. econstructor; last done. split; done. }
    move: Hsts Hlen Hpad Hsize.
    generalize (sls_fields sls) as sts. generalize (sl_members sl) as mems.
    intros mems sts Hsts Hlen Hpad Hsize.
    iInduction mems as [ | [name ly] mems] "IH" forall (rts tys rs sts vs Hsts Hlen Hpad Hsize); first done.
    destruct name as [ name | ].
    - (* named field *)
      simpl in Hsts. apply Forall2_cons_inv_r in Hsts as ([name2 st] & sts' & [-> Hst] & Hsts & ->).
      destruct rts as [ | rt rts]; first done.
      inv_hlist tys. intros ty tys. destruct rs as [r rs].
      simpl. destruct vs as [ | v vs]; first done. simpl.
      iDestruct "Hv" as "((%name3 & %st' & %ly' & %Heq & %Hst1 & %Hst2 & Hv) & Hvs)".
      injection Heq as [= <- <-].
      assert (ly' = ly) as -> by by eapply (syn_type_has_layout_inj st).
      iPoseProof (ty_own_val_has_layout with "Hv") as "%Hly"; first done.
      rewrite -Hly.
      iSplitL "Hv".
      { iExists _, _. iR.  iR. iR. rewrite take_app_length. done. }
      rewrite drop_app_length.
      iApply ("IH" with "[//] [] [] [] Hvs").
      + simpl in *. iPureIntro. lia.
      + inversion Hpad. done.
      + simpl in Hsize. iPureIntro. rewrite /fmap. lia.
    - (* padding *)
      simpl in Hsts. simpl.
      iSplitR; first last.
      { rewrite drop_app_length'; first last. { rewrite length_replicate//. }
        iApply ("IH" with "[//] [//] [] [] Hv").
        - inversion Hpad. done.
        - simpl in Hsize. rewrite /fmap. iPureIntro. lia. }
      iExists tt, _. iR. iR.
      assert (syn_type_has_layout (UntypedSynType ly) ly).
      { apply syn_type_has_layout_untyped; first done.
        - inversion Hpad; subst. apply layout_wf_align_log_0. done.
        - simpl in Hsize. rewrite MaxInt_eq. lia.
        - apply ly_align_in_bounds_1. inversion Hpad; subst. done. }
      iR. rewrite take_app_length'; first last. { rewrite length_replicate//. }
      rewrite uninit_own_spec.
      iR.
      iExists ly. iR.
      rewrite /has_layout_val length_replicate //.
  Qed.

  Lemma struct_zst_empty_typed π sls sl :
    struct_layout_spec_has_layout sls sl →
    sls.(sls_fields) = [] →
    sl.(sl_members) = [] →
    ⊢ zst_val ◁ᵥ{π, MetaNone} -[] @ struct_t sls +[].
  Proof.
    intros Hsl Hfields Hmem.
    rewrite /ty_own_val/=.
    iExists sl. iR. iR. rewrite Hfields. iR.
    iSplitR. { iPureIntro. rewrite /has_layout_val /ly_size /layout_of Hmem //. }
    by rewrite Hmem.
  Qed.
End init.

Section sized.
  Context `{!typeGS Σ}.

  Global Instance struct_t_sized {rts} (tys : hlist type rts) sls :
    TySized (struct_t sls tys).
  Proof.
    econstructor.
    - done.
    - done.
  Qed.
End sized.

Section copy.
  Context `{!typeGS Σ}.


  Local Instance struct_t_copy_pers {rts} (tys : hlist type rts) sls m :
    TCHForall (λ _, Copyable) tys →
    ∀ π v r, Persistent (v ◁ᵥ{π, m} r @ struct_t sls tys).
  Proof.
    iIntros (Hcopy).
    iIntros (???).
      apply bi.exist_persistent => sl.
      apply bi_sep_persistent_pure_l => Hmeta. subst m.
      apply bi_sep_persistent_pure_l => Halg.
      apply bi_sep_persistent_pure_l => Hlen. apply bi.sep_persistent; first apply _.
      apply big_sepL2_persistent_strong => _ k v' [rt [ty r']] Hlook1 Hlook2.
      apply pad_struct_lookup_Some in Hlook2 as (n & ly & ? & Hlook2); first last.
      { rewrite length_hpzipl. erewrite struct_layout_spec_has_layout_fields_length; done. }
      destruct Hlook2 as [[? Hlook2] | [-> Hlook2]].
      + simpl in Hlook2.
        apply (hpzipl_lookup_inv_hzipl_pzipl _ _ r) in Hlook2 as [Hlook21 Hlook22].
        eapply TCHForall_nth_hzipl in Hcopy; last apply Hlook21.
        eapply bi.exist_persistent => r0.
        eapply bi.exist_persistent => ly'.
        eapply bi.sep_persistent.
        { apply _. }
        apply _.
      + injection Hlook2 => [= ? _] _ _; subst.
        apply existT_inj in Hlook2 as [= -> ->].
        simpl. apply _.
  Qed.

  Local Definition fields_size (fields : list (option string * layout)) :=
    sum_list (ly_size <$> fields.*2).

  Lemma struct_t_copy_ind π (qs1 qs2 qs1' : list Qp) vs1 (tys1 : list (sigT (λ rt, type rt * place_rfn rt)%type)) (tys2 : list (sigT (λ rt, type rt * place_rfn rt)%type)) fields1 fields2 all_fields κ l E F  :
    Forall (λ ty, Copyable (projT2 ty).1) tys2 →
    lftE ∪ ↑shrN ⊆ E →
    all_fields = fields1 ++ fields2 →
    shr_locsE l (fields_size all_fields + 1) ⊆ F →
    length (named_fields fields2) = length tys2 →
    length (named_fields fields1) = length tys1 →
    length vs1 = length qs1 →
    length qs1 = length qs1' →
    length vs1 = length fields1 →
    rrust_ctx -∗
    ([∗ list] i↦ty;q ∈ pad_struct fields2 tys2 struct_make_uninit_type; qs2,
      struct_own_el_shr π κ (length fields1 + i) all_fields l (projT2 ty).2 (projT2 ty).1 ∗ q.[κ]) -∗

    (▷ [∗ list] i ↦ ty; '(v', q') ∈ pad_struct fields1 tys1 struct_make_uninit_type; zip vs1 qs1',
      struct_own_el_loc π q' v' i all_fields l (projT2 ty).2 (projT2 ty).1
    ) -∗

    ([∗ list] i ↦ v; '(q, q') ∈ vs1; (zip qs1 qs1'),
      ▷ (l +ₗ offset_of_idx all_fields i) ↦{q'} v ={E}=∗ q.[κ]) -∗

    |={E}=> ∃ qs2' vs2,
    ⌜length qs2' = length qs2⌝ ∗ ⌜length vs2 = length qs2⌝ ∗
    (* we get ownership of all the components *)
    (▷ [∗ list] i ↦ ty; '(v', q') ∈ pad_struct all_fields (tys1 ++ tys2) struct_make_uninit_type; zip (vs1 ++ vs2) (qs1' ++ qs2'),
        struct_own_el_loc π q' v' i all_fields l (projT2 ty).2 (projT2 ty).1) ∗
    (* if we give back the components, we get back the na token and lifetime tokens *)
    ([∗ list] i ↦ v; '(q, q') ∈ vs1 ++ vs2; (zip (qs1 ++ qs2) (qs1' ++ qs2')),
      ▷ (l +ₗ offset_of_idx all_fields i) ↦{q'} v ={E}=∗ q.[κ]
    ).
  Proof.
    iIntros (Hcopy ? Hf Hshr Hlen1 Hlen2 Hlen3 Hlen4 Hlen5) "#CTX Hshr Hloc Hcl". subst all_fields.
    iInduction fields2 as [ | field2 fields2] "IH" forall (tys2 fields1 tys1 vs1 qs1 qs1' qs2 Hshr Hlen1 Hlen2 Hlen3 Hlen4 Hlen5 Hcopy); simpl.
    { destruct qs2; last done. iModIntro.
      iExists [], []. simpl. destruct tys2; last done.
      rewrite !right_id.
      iFrame. done. }

    destruct field2 as [[n | ] ly]; simpl.
    - (* named field *)
      destruct tys2 as [ | ty2 tys2]; simpl; first done.
      destruct qs2 as [ | q2 qs2]; first done.
      simpl. iDestruct "Hshr" as "((Hshr1 & Htok1) & Hshr)".
      inversion Hcopy; subst.
      (* now we share this element *)
      iDestruct "Hshr1" as "(%r'1 & %ly1 & Hrfn & %Hly1' & %Hly1 & Hsc & Hshr1)".
      assert (ly1 = ly) as ->.
      { move: Hly1'. rewrite !lookup_app_r; [ | lia..].
        rewrite !right_id !Nat.sub_diag. simpl. intros [= ->]; done. }

      iMod (copy_shr_acc with "CTX Hshr1 Htok1") as "Ha".
      { done. }
      iDestruct "Ha" as "(%lyl & >%Hstl & >%Hlyl & %q2' & %v1 & (Hl & Hv) & Hlcl)".
      set (fields1' := fields1 ++ [(Some n, ly)]).
      set (tys1' := tys1 ++ [ty2]).
      set (vs1' := vs1 ++ [v1]).
      set (qs1a := qs1 ++ [q2]).
      set (qs1a' := qs1' ++ [q2']).
      iPoseProof (ty_own_val_has_layout with "Hv") as "#Ha"; first done.
      iDestruct "Ha" as ">%Hlyv".
      iSpecialize ("IH" $! tys2 fields1' tys1' vs1' qs1a qs1a' qs2 with "[] [] [] [] [] [] [] [Hshr] [Hloc Hl Hv Hrfn Hsc] [Hcl Hlcl]").
      { subst fields1'. rewrite -app_assoc. done. }
      { iPureIntro. simpl in *. lia. }
      { iPureIntro. simpl in *.  subst fields1' tys1'.
        move: Hlen2. rewrite !named_fields_field_names_length.
        rewrite /field_names omap_app/= !length_app /=. lia. }
      { iPureIntro. subst vs1' qs1a. rewrite !length_app/=. lia. }
      { iPureIntro. subst qs1a qs1a'. rewrite !length_app/=. lia. }
      { iPureIntro. subst vs1' fields1'. rewrite !length_app/=. lia. }
      { done. }
      { (* need to shift the indices etc *)
        iPoseProof (big_sepL2_length with "Hshr") as "%Hlen7".
        iApply (big_sepL2_wand with "Hshr"). iApply big_sepL2_intro; first done.
        iModIntro. iIntros (? [? []] ? ? ?).
        rewrite /struct_own_el_shr. simpl.
        iIntros "((% & % & ? & Hlook & ? & ? & Hl) & $)".
        iExists _, _. iFrame.
        rewrite /fields1' length_app -Nat.add_assoc -!app_assoc/=. iFrame. }
      { iNext. subst tys1' fields1' vs1' qs1a'.
        rewrite zip_app; last lia.
        rewrite pad_struct_snoc_Some; first last.
        { move: Hlen2. rewrite !named_fields_field_names_length. lia. }
        iApply (big_sepL2_app with "[Hloc]").
        { rewrite -app_assoc. done. }
        simpl. iSplitL; last done.
        rewrite /struct_own_el_loc.
        iExists _, _. iFrame "∗ %".
        iSplitR. {
          iPureIntro. rewrite pad_struct_length. rewrite lookup_app_l.
          - rewrite !lookup_app_r; [ | lia..]. rewrite !right_id !Nat.sub_diag//.
            simpl. f_equiv. by eapply syn_type_has_layout_inj.
          - rewrite length_app/=. lia.
        }
        rewrite pad_struct_length -app_assoc/=. iFrame.
      }
      { rewrite /vs1' /qs1a /qs1a'.
        rewrite zip_app; last done.
        subst fields1'. rewrite -!app_assoc.
        iApply (big_sepL2_app with "Hcl").
        simpl. iSplitL; last done.
        iIntros "Hl".
        rewrite Hlen5.
        by iMod ("Hlcl" with "Hl") as "$".
      }
      { iMod "IH" as "(%qs2' & %vs2 & % & % & Hl & Hcl)".
        iModIntro. iExists (q2' :: qs2'), (v1 :: vs2).
        rewrite /vs1'/qs1a'/= -!app_assoc /=. iFrame.
        iPureIntro. split; lia.
      }
    - (* unnamed fields *)
      (*destruct tys2 as [ | ty2 tys2]; simpl; first done.*)
      destruct qs2 as [ | q2 qs2]; first done.
      simpl. iDestruct "Hshr" as "((Hshr1 & Htok1) & Hshr)".
      (* now we share this element *)
      iDestruct "Hshr1" as "(%r'1 & %ly1 & Hrfn & %Hly1' & %Hly1 & Hsc & Hshr1)".
      assert (ly1 = ly) as ->.
      { move: Hly1'. rewrite !lookup_app_r; [ | lia..].
        rewrite !right_id !Nat.sub_diag. simpl. intros [= ->]; done. }

      iMod (copy_shr_acc with "CTX Hshr1 Htok1") as "Ha".
      { done. }
      iDestruct "Ha" as "(%lyl & >%Hstl & >%Hlyl & %q2' & %v1 & (Hl & Hv) & Hlcl)".
      set (fields1' := fields1 ++ [(None, ly)]).
      (*set (tys1' := tys1 ++ [ty2]).*)
      set (vs1' := vs1 ++ [v1]).
      set (qs1a := qs1 ++ [q2]).
      set (qs1a' := qs1' ++ [q2']).
      iPoseProof (ty_own_val_has_layout with "Hv") as "#Ha"; first done.
      iDestruct "Ha" as ">%Hlyv".
      iSpecialize ("IH" $! tys2 fields1' tys1 vs1' qs1a qs1a' qs2 with "[] [] [] [] [] [] [] [Hshr] [Hloc Hl Hv Hrfn Hsc] [Hcl Hlcl]").
      { subst fields1'. rewrite -app_assoc. done. }
      { iPureIntro. simpl in *. lia. }
      { iPureIntro. simpl in *.  subst fields1'.
        move: Hlen2. rewrite !named_fields_field_names_length.
        rewrite /field_names omap_app/= !length_app /=. lia. }
      { iPureIntro. subst vs1' qs1a. rewrite !length_app/=. lia. }
      { iPureIntro. subst qs1a qs1a'. rewrite !length_app/=. lia. }
      { iPureIntro. subst vs1' fields1'. rewrite !length_app/=. lia. }
      { iPureIntro. done. }
      { (* need to shift the indices etc *)
        iPoseProof (big_sepL2_length with "Hshr") as "%Hlen7".
        iApply (big_sepL2_wand with "Hshr"). iApply big_sepL2_intro; first done.
        iModIntro. iIntros (? [? []] ? ? ?).
        rewrite /struct_own_el_shr. simpl.
        iIntros "((% & % & ? & Hlook & ? & ? & Hl) & $)".
        iExists _, _. iFrame.
        rewrite /fields1' length_app -Nat.add_assoc -!app_assoc/=. iFrame. }
      { iNext. subst fields1' vs1' qs1a'.
        rewrite zip_app; last lia.
        rewrite pad_struct_snoc_None; first last.
        iApply (big_sepL2_app with "[Hloc]").
        { rewrite -app_assoc. done. }
        simpl. iSplitL; last done.
        rewrite /struct_own_el_loc.
        iExists _, _. iFrame "∗ %".
        iSplitR. {
          iPureIntro. rewrite pad_struct_length. rewrite lookup_app_l.
          - rewrite !lookup_app_r; [ | lia..]. rewrite !right_id !Nat.sub_diag//.
            simpl. f_equiv. by eapply syn_type_has_layout_inj.
          - rewrite length_app/=. lia.
        }
        rewrite pad_struct_length -app_assoc/=. iFrame.
      }
      { rewrite /vs1' /qs1a /qs1a'.
        rewrite zip_app; last done.
        subst fields1'. rewrite -!app_assoc.
        iApply (big_sepL2_app with "Hcl").
        simpl. iSplitL; last done.
        iIntros "Hl".
        rewrite Hlen5.
        by iMod ("Hlcl" with "Hl") as "$".
      }
      { iMod "IH" as "(%qs2' & %vs2 & % & % & Hl & Hcl)".
        iModIntro. iExists (q2' :: qs2'), (v1 :: vs2).
        rewrite /vs1'/qs1a'/= -!app_assoc /=. iFrame.
        iPureIntro. split; lia.
      }
  Qed.

  Lemma struct_t_copy_ind' π (qs : list Qp) (tys : list (sigT (λ rt, type rt * place_rfn rt)%type)) fields κ l E F  :
    Forall (λ ty, Copyable (projT2 ty).1) tys →
    lftE ∪ ↑shrN ⊆ E →
    shr_locsE l (fields_size fields + 1) ⊆ F →
    length (named_fields fields) = length tys →
    rrust_ctx -∗
    ([∗ list] i↦ty;q ∈ pad_struct fields tys struct_make_uninit_type; qs,
      struct_own_el_shr π κ i fields l (projT2 ty).2 (projT2 ty).1 ∗ q.[κ]) -∗
    |={E}=> ∃ qs' vs,
    ⌜length qs' = length qs⌝ ∗ ⌜length vs = length qs⌝ ∗
    (* we get ownership of all the components *)
    (▷ [∗ list] i ↦ ty; '(v', q') ∈ pad_struct fields tys struct_make_uninit_type; zip vs qs',
        struct_own_el_loc π q' v' i fields l (projT2 ty).2 (projT2 ty).1) ∗
    (* if we give back the components, we get back the na token and lifetime tokens *)
    ([∗ list] i ↦ v; '(q, q') ∈ vs; zip qs qs',
      (▷ (l +ₗ offset_of_idx fields i) ↦{q'} v) ={E}=∗ q.[κ]).
  Proof.
    iIntros (????) "CTX Hloc".
    iMod (struct_t_copy_ind _ [] qs [] [] [] tys [] fields fields  with "CTX Hloc [] []") as "Ha"; try done.
    by iNext.
  Qed.

  Lemma struct_t_copy_acc π (tys : list (sigT (λ rt, type rt * place_rfn rt)%type)) fields q κ l E :
    Forall (λ ty, Copyable (projT2 ty).1) tys →
    lftE ∪ ↑shrN ⊆ E →
    length (named_fields fields) = length tys →
    rrust_ctx -∗
    q.[κ] -∗
    ([∗ list] i↦ty ∈ pad_struct fields tys struct_make_uninit_type, struct_own_el_shr π κ i fields l (projT2 ty).2 (projT2 ty).1) -∗
    |={E}=> ∃ q' vs,
    ⌜length vs = length fields⌝ ∗
    (* we get ownership of all the components *)
    (▷ [∗ list] i ↦ ty; v' ∈ pad_struct fields tys struct_make_uninit_type; vs,
        struct_own_el_loc π q' v' i fields l (projT2 ty).2 (projT2 ty).1) ∗
    (* if we give back the components, we get back the na token and lifetime tokens *)
    (([∗ list] i ↦ v ∈ vs, (▷ (l +ₗ offset_of_idx fields i) ↦{q'} v)) ={E}=∗ q.[κ]).
  Proof.
    iIntros (???) "#CTX Htok Hloc".
    iPoseProof (Fractional_split_big_sepL (λ q, q.[κ])%I (length fields) with "Htok") as "(%qs & %Hlen_eq & Htoks & Htoks_cl)".
    iMod (struct_t_copy_ind' with "CTX [Hloc Htoks]") as "(%qs' & %vs & %Hlen1 & %Hlen2 & Hloc & Hcl)"; [ done.. | | ].
    { iApply big_sepL2_sep. iSplitL "Hloc".
      1: iApply big_sepL_extend_r; last done.
      2: iApply big_sepL_extend_l; last iApply "Htoks".
      all: rewrite pad_struct_length; done. }

    set (q' := foldr Qp.min 1%Qp qs').
    assert (∀ i q, qs' !! i = Some q → (q' ≤ q)%Qp) as Hmin.
    { intros i q0 Hlook.
      induction qs' as [ | q2 qs' IH] in i, Hlook, q' |-*; first done.
      subst q'. destruct i as [ | i]; simpl in *.
      - injection Hlook as ->. apply Qp.le_min_l.
      - etrans;first  apply Qp.le_min_r. by eapply IH.  }

    iAssert (([∗ list] i↦ty;vq ∈ pad_struct fields tys struct_make_uninit_type; zip vs qs',
       ▷ struct_own_el_loc π q' vq.1 i fields l (projT2 ty).2 (projT2 ty).1 ∗
      (▷ (l +ₗ offset_of_idx fields i) ↦{q'} vq.1 -∗ ▷ (l +ₗ offset_of_idx fields i) ↦{vq.2} vq.1)))%I with "[Hloc]" as "Hloc".
    { rewrite big_sepL2_later; first last. { rewrite pad_struct_length length_zip_with. lia. }
      iApply (big_sepL2_wand with "Hloc"). iApply big_sepL2_intro. { rewrite pad_struct_length length_zip_with. lia. }
      iModIntro. iIntros (k [rt [ty r]] [v q''] Hlook1 Hlook2) "Hloc".
      simpl. rewrite /struct_own_el_loc.
      iDestruct "Hloc" as "(%r' & %ly & Hrfn & Hlook & Hst & Hty & Hl & Hlyv & Hv)".
      iPoseProof (Fractional_fractional_le (λ q, _) q'' q' with "Hl") as "(Hl & Hal)".
      { eapply (Hmin k). apply lookup_zip in Hlook2. apply Hlook2. }
      iFrame.
    }

    rewrite big_sepL2_sep. iDestruct "Hloc" as "(Hloc & Hcl_loc)".
    iPoseProof (big_sepL2_elim_l with "Hcl_loc") as "Hcl_loc".
    rewrite -big_sepL2_later; first last. { rewrite pad_struct_length length_zip_with. lia. }
    rewrite -(big_sepL2_fmap_r (λ x, x.1) (λ _ _ y2, struct_own_el_loc _ _ y2 _ _ _ _ _)).
    rewrite fst_zip; first last. { lia. }

    iModIntro. iExists q', vs. iFrame.
    iSplitR. { iPureIntro. lia. }

    iIntros "Hloc".
    iPoseProof (big_sepL2_length with "Hcl") as "%Hlen".
    rewrite length_zip_with in Hlen.
    iPoseProof (big_sepL2_to_zip with "Hcl") as "Hcl".
    rewrite [zip qs qs']zip_flip zip_fmap_r zip_assoc_r -list_fmap_compose big_sepL_fmap.

    iPoseProof (big_sepL_extend_r qs with "Hcl_loc") as "Hcl_loc".
    { rewrite length_zip_with. lia. }
    iPoseProof (big_sepL2_to_zip with "Hcl_loc") as "Hcl_loc".
    iPoseProof (big_sepL_sep_2 with "Hcl Hcl_loc") as "Hcl".

    iPoseProof (big_sepL_extend_r qs' with "Hloc") as "Hloc".
    { lia. }
    iPoseProof (big_sepL2_to_zip with "Hloc") as "Hloc".
    iPoseProof (big_sepL_extend_r qs with "Hloc") as "Hloc".
    { rewrite length_zip_with. lia. }
    iPoseProof (big_sepL2_to_zip with "Hloc") as "Hloc".
    iPoseProof (big_sepL_sep_2 with "Hcl Hloc") as "Hcl".
    rewrite zip_assoc_l big_sepL_fmap.

    iAssert ([∗ list] i ↦ y ∈ qs, True ={E}=∗ (y).[κ])%I with "[Hcl]" as "Hcl".
    { iApply big_sepL2_elim_l. iApply big_sepL2_from_zip; first last.
      { iApply (big_sepL2_elim_l). iApply big_sepL2_from_zip; first last.
        { iApply (big_sepL_wand with "Hcl").
          iApply big_sepL_intro. iModIntro. iIntros (k [v [q1' q1]] Hlook) "Ha Hna"; simpl.
          iDestruct "Ha" as "((Ha & Hcl) & Hl)".
          iPoseProof ("Hcl" with "Hl") as "Hl".
          iApply ("Ha" with "Hl"). }
        rewrite length_zip_with. lia. }
      lia. }

    (* now collapse the whole sequence *)
    set (P i := (|={E}=> ([∗ list] q ∈ (drop i qs), q.[κ]))%I).
    iPoseProof (big_sepL_eliminate_sequence_rev P with "Hcl [] []") as "Ha".
    { iModIntro. rewrite drop_all. done. }
    { rewrite /P. iModIntro. iIntros (i q1 Hlook) ">Htoks Hvs".
      erewrite (drop_S _ _ i); last done; simpl. iFrame.
      by iApply "Hvs".
    }
    iMod "Ha" as "Htoks".
    by iPoseProof ("Htoks_cl" with "Htoks") as "$".
  Qed.

  Global Instance struct_t_copy {rts} (tys : hlist type rts) sls :
    TCHForall (λ _, Copyable) tys →
    Copyable (struct_t sls tys).
  Proof.
    iIntros (Hcopy). split; first apply _.
    iIntros (κ π E l r m q ?) "#CTX Hshr Htok".
    rewrite /ty_shr /=.
    iDestruct "Hshr" as (sl) "(-> & %Halg' & %Hlen & %Hly & #Hlb & #Hb)".
    (*simpl in Halg.*)
    specialize (use_struct_layout_alg_Some_inv _ _ Halg') as Halg2.
    (*assert (ly = sl) as -> by by eapply syn_type_has_layout_inj.*)
    (*iR.*)
    iMod (struct_t_copy_acc _ (hpzipl rts tys r) (sl_members sl) with "CTX Htok Hb") as "(%q' & %vs & % & Hs & Hcl)".
    { clear -Hcopy. induction rts as [ | rt rts IH] in tys, r, Hcopy |-*; simpl.
      - inv_hlist tys. destruct r. constructor.
      - inv_hlist tys => ty tys. destruct r as [r1 r].
        inversion 1. subst. repeat match goal with | H : existT _ _ = existT _ _ |- _ => apply existT_inj in H end. subst.
        econstructor; first done. by apply IH.
    }
    { done. }
    { rewrite length_hpzipl. rewrite named_fields_field_names_length. erewrite struct_layout_spec_has_layout_fields_length; done. }

    (* now we need to pull the pointsto *)
    (*iPoseProof (big_sepL2_impl _ (λ i (ty : sigT (λ rt : Type, type rt * place_rfn rt)%type) v', struct_own_el_loc' _ π q' v' i (sl_members sl) l (projT2 ty).2 (projT2 ty).1) with "Hs") as "Hs".*)
    iAssert ((|={E}=> ∃ lys, ⌜length lys = length vs⌝ ∗ ▷ [∗ list] i↦ty;v' ∈ pad_struct (sl_members sl) (hpzipl rts tys r) struct_make_uninit_type;(zip vs lys),
      struct_own_el_loc' π q' v'.1 i (sl_members sl) l (projT2 ty).2 (projT2 ty).1 v'.2)%I) with "[Hs]" as ">(%lys & % & Hs)".
    { iAssert ((▷ ([∗ list] i↦ty;v' ∈ pad_struct (sl_members sl) (hpzipl rts tys r) struct_make_uninit_type;vs,
        ∃ ly : layout, struct_own_el_loc' π q' v' i (sl_members sl) l (projT2 ty).2 (projT2 ty).1 ly))%I) with "[Hs]" as "Hs".
        { iNext.  iApply (big_sepL2_wand with "Hs"). iApply big_sepL2_intro. { rewrite pad_struct_length. lia. }
          iModIntro. iIntros (? [? []] ? ? ?) "(% & % & ? & ? & ? & ? & ? & ? & ?)". rewrite /struct_own_el_loc'. eauto with iFrame. }
        rewrite big_sepL2_exists_r. iDestruct "Hs" as "(%l3 & >%Hlen2 & Ha)".
        iExists l3. iR. iModIntro. iNext. done. }
    iPoseProof (struct_own_val_extract_pointsto' with "Hlb Hs") as "(Hl & >%Hlyv & Hs)".
    { done. }
    { rewrite length_hpzipl. done. }

    rewrite fst_zip in Hlyv; last lia.
    iExists sl. iR. iR.
    iExists q', (mjoin vs). simpl. iFrame.
    iSplitL "Hl Hs".
    { iModIntro. iNext. rewrite fst_zip; last lia. iFrame. iR. iR. iR.
      iPureIntro. by apply mjoin_has_struct_layout. }
    iModIntro. iIntros "Hpts".
    iApply ("Hcl" with "[Hpts]").
    iApply big_sepL_later. iNext. rewrite heap_pointsto_reshape_sl; last by apply mjoin_has_struct_layout.
    iDestruct "Hpts" as "(_ & Hpts)". rewrite reshape_join; first done.
    rewrite Forall2_fmap_r. eapply Forall2_impl; first done.
    done.
  Qed.
End copy.
