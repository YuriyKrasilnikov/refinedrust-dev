From stdpp Require Import gmap.
From caesium Require Import lang proofmode derived lifting.
From refinedrust Require Export base type lft_contexts annotations ltypes programs.
From refinedrust Require Import ltype_rules.
From refinedrust Require Import options.

(** * Core rules of the type system *)

Section find.
  Context `{typeGS Σ}.

  Implicit Types (rt : RT).

  (* NOTE: find_in_context instances should always have a sep conj in their premise, even if the LHS is just [True].
      This is needed by the liFindInContext/ liFindHypOrTrue automation!
  *)

  (** Instances so that Lithium knows what to search for when needing to provide something *)
  (** For locations and values, we use the ones that also find a refinement type, since it may be desirable to change it (consider e.g. changing to uninit) *)
  Global Instance related_to_loc l π b {rt} (lt : ltype rt) (r : place_rfn rt) : RelatedTo (l ◁ₗ[π, b] r @ lt)  | 100 :=
    {| rt_fic := FindLocP l |}.
  Global Instance related_to_val v m π {rt} (ty : type rt) (r : rt) : RelatedTo (v ◁ᵥ{π, m} r @ ty)  | 100 :=
    {| rt_fic := FindValP v |}.

  Global Instance related_to_named_lfts M : RelatedTo (named_lfts M) | 100 :=
    {| rt_fic:= FindNamedLfts |}.

  Global Instance related_to_gvar_pobs {rt} γ (r : rt) : RelatedTo (gvar_pobs γ r) | 100 :=
    {| rt_fic := FindGvarPobsP γ |}.

  Global Instance related_to_credit_store n m : RelatedTo (credit_store n m) | 100 :=
    {| rt_fic := FindCreditStore |}.

  Global Instance related_to_na_own π E : RelatedTo (na_own π E) | 100 :=
    {| rt_fic := FindNaOwn π |}.

  Global Instance related_to_freeable l n q k : RelatedTo (freeable_nz l n q k) | 100 :=
    {| rt_fic := FindFreeable l |}.

  Global Instance related_to_loc_in_bounds l pre suf : RelatedTo (loc_in_bounds l pre suf) | 100 :=
    {| rt_fic := FindLocInBounds l |}.

  Global Instance related_to_local_live f x st l : RelatedTo (x is_live{f, st} l) | 100 :=
    {| rt_fic := FindLocal f x |}.

  Global Instance related_to_alloc_locals f locals : RelatedTo (allocated_locals f locals) | 100 :=
    {| rt_fic := FindFrameLocals f |}.

  (** Value ownership *)
  Lemma find_in_context_type_val_id v T :
    (∃ π m rt (ty : type rt) r, v ◁ᵥ{π, m} r @ ty ∗ T (existT rt (ty, r, π, m)))
    ⊢ find_in_context (FindVal v) T.
  Proof. iDestruct 1 as (π m rt ty r) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_type_val_id_inst v :
    FindInContext (FindVal v) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_val_id v T).

  Lemma find_in_context_type_valp_id v T :
    (∃ π m rt (ty : type rt) r, v ◁ᵥ{π, m} r @ ty ∗ T (v ◁ᵥ{π, m} r @ ty))
    ⊢ find_in_context (FindValP v) T.
  Proof. iDestruct 1 as (π m rt ty r) "(Hl & HT)". iExists (v ◁ᵥ{π, m} r @ ty)%I => /=. iFrame. Qed.
  Global Instance find_in_context_type_valp_id_inst v :
    FindInContext (FindValP v) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_valp_id v T).

  Lemma find_in_context_type_valp_loc l T :
    (∃ π rt (lt : ltype rt) r, l ◁ₗ[π, Owned] r @ lt ∗ T (l ◁ₗ[π, Owned] r @ lt))
    ⊢ find_in_context (FindValP (val_of_loc l)) T.
  Proof. iDestruct 1 as (π rt lt r) "(Hl & HT)". iExists (l ◁ₗ[π, Owned] r @ lt)%I. iFrame. Qed.
  Global Instance find_in_context_type_valp_loc_inst l :
    FindInContext (FindValP (val_of_loc l)) FICSyntactic | 5 :=
    λ T, i2p (find_in_context_type_valp_loc l T).

  Lemma find_in_context_type_val_with_rt_id {rt} v π m T :
    (∃ (ty : type rt) r, v ◁ᵥ{π, m} r @ ty ∗ T (ty, r, m))
  ⊢ find_in_context (FindValWithRt rt v π) T.
  Proof. iDestruct 1 as (ty r) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_type_val_with_rt_id_inst {rt} π m v :
    FindInContext (FindValWithRt rt v π) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_val_with_rt_id v π m T).

  (* TODO: generalize to different rt to handle typaram instantiation?*)
  Lemma own_val_subsume_id v π m {rt} (r1 r2 : rt) (ty1 ty2 : type rt) T :
    ⌜r1 = r2⌝ ∗ ⌜ty1 = ty2⌝ ∗ T
    ⊢ subsume (Σ := Σ) (v ◁ᵥ{π, m} r1 @ ty1) (v ◁ᵥ{π, m} r2 @ ty2) T.
  Proof.
    iIntros "(-> & -> & $)"; eauto.
  Qed.
  Definition own_val_subsume_id_inst v π m {rt} (r1 r2 : rt) (ty1 ty2 : type rt) :
    Subsume (v ◁ᵥ{π, m} r1 @ ty1) (v ◁ᵥ{π, m} r2 @ ty2) :=
    λ T, i2p (own_val_subsume_id v π m r1 r2 ty1 ty2 T).

  (** Location ownership *)
  Lemma find_in_context_type_loc_id l T:
    (∃ π rt (lt : ltype rt) r (b : bor_kind), l ◁ₗ[π, b] r @ lt ∗ T (existT rt (lt, r, b, π)))
    ⊢ find_in_context (FindLoc l) T.
  Proof. iDestruct 1 as (π rt lt r b) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_type_loc_id_inst l :
    FindInContext (FindLoc l) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_loc_id l T).

  Lemma find_in_context_type_opt_loc_id l T:
    (∃ π rt (lt : ltype rt) r (b : bor_kind), l ◁ₗ[π, b] r @ lt ∗ T (Some (existT rt (lt, r, b, π))))
    ⊢ find_in_context (FindOptLoc l) T.
  Proof. iDestruct 1 as (π rt lt r b) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_type_opt_loc_id_inst l :
    FindInContext (FindOptLoc l) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_opt_loc_id l T).
  Lemma find_in_context_type_opt_loc_none l T:
    (True ∗ T None)
    ⊢ find_in_context (FindOptLoc l) T.
  Proof. iDestruct 1 as "[_ HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_type_opt_loc_none_inst l :
    FindInContext (FindOptLoc l) FICSyntactic | 10 :=
    λ T, i2p (find_in_context_type_opt_loc_none l T).

  Lemma find_in_context_type_locp_loc l T :
    (∃ π rt (lt : ltype rt) r (b : bor_kind), l ◁ₗ[π, b] r @ lt ∗ T (l ◁ₗ[π, b] r @ lt))
    ⊢ find_in_context (FindLocP l) T.
  Proof. iDestruct 1 as (π rt lt r b) "[Hl HT]". iExists (l ◁ₗ[π, b] r @ lt)%I => /=. iFrame. Qed.
  Global Instance find_in_context_type_locp_loc_inst l :
    FindInContext (FindLocP l) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_locp_loc l T).
  Lemma find_in_context_type_locp_val (l : loc) T :
    (∃ π m rt (ty : type rt) r , l ◁ᵥ{π, m} r @ ty ∗ T (l ◁ᵥ{π, m} r @ ty))
    ⊢ find_in_context (FindLocP l) T.
  Proof. iDestruct 1 as (π m rt ty r) "[Hl HT]". iExists (l ◁ᵥ{π, m} r @ ty)%I => /=. iFrame. Qed.
  (* NOTE: important: has lower priority! If there's a location assignment available, should just use that. *)
  Global Instance find_in_context_type_locp_val_inst l :
    FindInContext (FindLocP l) FICSyntactic | 2 :=
    λ T, i2p (find_in_context_type_locp_val l T).

  Lemma find_in_context_type_loc_with_rt_id {rt} l π T:
    (∃ (lt : ltype rt) r (b : bor_kind), l ◁ₗ[π, b] r @ lt ∗ T (lt, r, b))
    ⊢ find_in_context (FindLocWithRt rt l π) T.
  Proof. iDestruct 1 as (lt r b) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_type_loc_with_rt_id_inst {rt} π l :
    FindInContext (FindLocWithRt rt l π) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_type_loc_with_rt_id l π T).

  (** Variables *)
  Lemma subsume_local_live x f st1 st2 l1 l2 T :
    subsume (x is_live{f, st1} l1) (x is_live{f, st2} l2) T :-
      exhale (⌜st1 = st2⌝);
      exhale (⌜l1 = l2⌝);
      return T.
  Proof.
    iIntros "(<- & <- & $) $".
  Qed.
  Definition subsume_local_live_inst := [instance @subsume_local_live].
  Global Existing Instance subsume_local_live_inst.

  Lemma find_in_context_local f x T:
    (∃ st l, x is_live{f, st} l ∗ T (st, l))
    ⊢ find_in_context (FindLocal f x) T.
  Proof. iDestruct 1 as (st l) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_local_inst f x :
    FindInContext (FindLocal f x) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_local f x T).

  (** Allocated locals *)
  Lemma subsume_frame_locals f1 f2 locals1 locals2 T :
    ⌜f1 = f2⌝ ∗ ⌜locals1 = locals2⌝ ∗ T ⊢ subsume (allocated_locals f1 locals1) (allocated_locals f2 locals2) T.
  Proof.
    iIntros "(<- & <- & HT)".
    iIntros "Ha". iFrame.
  Qed.
  Definition subsume_frame_locals_inst := [instance subsume_frame_locals].
  Global Existing Instance subsume_frame_locals_inst.

  Lemma find_in_context_frame_locals f T :
    (∃ locals, allocated_locals f locals ∗ T locals)
    ⊢ find_in_context (FindFrameLocals f) T.
  Proof. iDestruct 1 as (locals) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_frame_locals_inst f :
    FindInContext (FindFrameLocals f) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_frame_locals f T).

  (** NamedLfts *)
  Lemma subsume_named_lfts M M' `{!ContainsProtected M'} T:
    ⌜M = M'⌝ ∗ T ⊢ subsume (Σ := Σ) (named_lfts M) (named_lfts M') T.
  Proof. iIntros "(-> & $) $". Qed.
  Definition subsume_named_lfts_inst := [instance subsume_named_lfts].
  Global Existing Instance subsume_named_lfts_inst.

  (* Low priority instance for strong updates, in particular when doing loop proofs *)
  Lemma subsume_named_lfts_trivial M M' T:
    T ⊢ subsume (Σ := Σ) (named_lfts M) (named_lfts M') T.
  Proof. iIntros "$ Hb". iApply "Hb". Qed.
  Definition subsume_named_lfts_trivial_inst := [instance subsume_named_lfts_trivial].
  Global Existing Instance subsume_named_lfts_trivial_inst | 100.

  Lemma find_in_context_named_lfts T:
    (∃ M, named_lfts M ∗ T M) ⊢
    find_in_context FindNamedLfts T.
  Proof. iDestruct 1 as (M) "[Hn HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_named_lfts_inst :
    FindInContext FindNamedLfts FICSyntactic | 1 :=
    λ T, i2p (find_in_context_named_lfts T).

  (** CreditStore *)
  Lemma subsume_credit_store_evar n m n' m' T `{!ContainsProtected (credit_store n' m')}:
    ⌜n = n'⌝ ∗ ⌜m = m'⌝ ∗ T ⊢ subsume (Σ := Σ) (credit_store n m) (credit_store n' m') T.
  Proof.
    iIntros "(<- & <- & HT) $ //".
  Qed.
  Global Instance subsume_credit_store_evar_inst n m n' m' `{!ContainsProtected (credit_store n' m')} : Subsume (credit_store n m) (credit_store n' m') | 10 :=
    λ T, i2p (subsume_credit_store_evar n m n' m' T).

  Lemma subsume_credit_store n m n' m' T :
    ⌜fast_lia_hint (n' ≤ n)⌝ ∗ ⌜fast_lia_hint (m' ≤ m)⌝ ∗ T ⊢ subsume (Σ := Σ) (credit_store n m) (credit_store n' m') T.
  Proof.
    rewrite /fast_lia_hint.
    iIntros "(% & % & HT) Hc".
    iFrame. iApply (credit_store_mono with "Hc"); done.
  Qed.
  Global Instance subsume_credit_store_inst n m n' m' : Subsume (credit_store n m) (credit_store n' m') :=
    λ T, i2p (subsume_credit_store n m n' m' T).

  Lemma find_in_context_credit_store T :
    (∃ n m, credit_store n m ∗ T (n, m)) ⊢
    find_in_context FindCreditStore T.
  Proof.
    iDestruct 1 as (n m) "[Hc HT]". iExists (n, m). by iFrame.
  Qed.
  Global Instance find_in_context_credit_store_inst :
    FindInContext FindCreditStore FICSyntactic | 1 :=
    λ T, i2p (find_in_context_credit_store T).

  (** NaOwn *)
  Lemma subsume_na_own π E E' T :
    ⌜E' ⊆ E⌝ ∗ T ⊢ subsume (Σ := Σ) (na_own π E) (na_own π E') T.
  Proof.
    iIntros "(%Heq & $) Hna".
    by iDestruct (na_own_acc with "Hna") as "($ & Hna)".
  Qed.
  Global Instance subsume_na_own_inst π E E' : Subsume (na_own π E) (na_own π E') :=
    λ T, i2p (subsume_na_own π E E' T).

  Lemma find_in_context_na_own π T :
    (∃ E, na_own π E ∗ T E) ⊢
    find_in_context (FindNaOwn π) T.
  Proof.
    iDestruct 1 as (E) "[Hna HT]". iExists _. by iFrame.
  Qed.
  Global Instance find_in_context_na_own_inst π :
    FindInContext (FindNaOwn π) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_na_own π T).

  Lemma find_in_context_opt_na_own_some π T :
    (∃ E, na_own π E ∗ T (Some E)) ⊢
    find_in_context (FindOptNaOwn π) T.
  Proof.
    iDestruct 1 as (E) "[Hna HT]". iExists _. by iFrame.
  Qed.
  Global Instance find_in_context_opt_na_own_some_inst π :
    FindInContext (FindOptNaOwn π) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_opt_na_own_some π T).

  Lemma find_in_context_opt_na_own_none π T :
    True ∗ T None
    ⊢ find_in_context (FindOptNaOwn π) T.
  Proof.
    iIntros "(_ & ?)".
    iExists _; iFrame.
    by rewrite /FindOptNaOwn.
  Qed.
  Global Instance find_in_context_opt_na_own_none_inst π :
    FindInContext (FindOptNaOwn π) FICSyntactic | 2 :=
    λ T, i2p (find_in_context_opt_na_own_none π T).

  (** FindOptLftDead *)
  Lemma subsume_lft_dead κ1 κ2 T :
    ⌜κ1 = κ2⌝ ∗ T ⊢ subsume (Σ := Σ) ([† κ1]) ([† κ2]) T.
Proof. iIntros "(-> & $)". eauto. Qed.
  Global Instance subsume_lft_dead_inst κ1 κ2 :
    Subsume ([† κ1]) ([† κ2]) := λ T, i2p (subsume_lft_dead κ1 κ2 T).

  Lemma find_in_context_opt_lft_dead κ T :
    [† κ] ∗ T true
    ⊢ find_in_context (FindOptLftDead κ) T.
  Proof.
    iIntros "(Hdead & HT)". iExists true. iFrame.
  Qed.
  Definition find_in_context_opt_lft_dead_inst := [instance @find_in_context_opt_lft_dead with FICSyntactic].
  Global Existing Instance find_in_context_opt_lft_dead_inst | 1.

  (* dummy instance in case we don't find it *)
  Lemma find_in_context_opt_lft_dead_none κ T :
    True ∗ T false
    ⊢ find_in_context (FindOptLftDead κ) T.
  Proof.
    iIntros "(_ & HT)". iExists false. iFrame. simpl. done.
  Qed.
  Definition find_in_context_opt_lft_dead_none_inst := [instance @find_in_context_opt_lft_dead_none with FICSyntactic].
  Global Existing Instance find_in_context_opt_lft_dead_none_inst | 10.

  Lemma find_in_context_lft_dead κ T :
    [† κ] ∗ T ()
    ⊢ find_in_context (FindLftDead κ) T.
  Proof.
    iIntros "(Hdead & HT)". iExists (). iFrame.
  Qed.
  Definition find_in_context_lft_dead_inst := [instance @find_in_context_lft_dead with FICSyntactic].
  Global Existing Instance find_in_context_lft_dead_inst.

  (** FindGuarded *)
  Lemma subsume_guarded prepaid1 prepaid2 P1 P2 T :
    ⌜prepaid1 = prepaid2⌝ ∗ ⌜P1 = P2⌝ ∗ T ⊢ subsume (Σ := Σ) (guarded prepaid1 P1) (guarded prepaid2 P2) T.
  Proof. iIntros "(-> & -> & $)". eauto. Qed.
  Definition subsume_guarded_inst := [instance @subsume_guarded].
  Global Existing Instance subsume_guarded_inst.

  (** FindOptGuarded *)
  Lemma find_in_context_opt_guarded T :
    (∃ prepaid P, guarded prepaid P ∗ T (Some (prepaid, P)))
    ⊢ find_in_context (FindOptGuarded) T.
  Proof.
    iIntros "(% & % & Hg & HT)". iExists _. iFrame.
  Qed.
  Definition find_in_context_opt_guarded_inst := [instance @find_in_context_opt_guarded with FICSyntactic].
  Global Existing Instance find_in_context_opt_guarded_inst | 1.

  (* dummy instance in case we don't find it *)
  Lemma find_in_context_opt_guarded_none T :
    True ∗ T None
    ⊢ find_in_context (FindOptGuarded) T.
  Proof.
    iIntros "(_ & HT)". iExists None. iFrame. simpl. done.
  Qed.
  Definition find_in_context_opt_guarded_none_inst := [instance @find_in_context_opt_guarded_none with FICSyntactic].
  Global Existing Instance find_in_context_opt_guarded_none_inst | 10.

  (** Freeable *)
  Lemma subsume_freeable l1 q1 n1 k1 l2 q2 n2 k2 T :
    ⌜l1 = l2⌝ ∗ ⌜n1 = n2⌝ ∗ ⌜q1 = q2⌝ ∗ ⌜k1 = k2⌝ ∗ T
    ⊢ subsume (freeable_nz l1 n1 q1 k1) (freeable_nz l2 n2 q2 k2) T.
  Proof.
    iIntros "(-> & -> & -> & -> & $)". eauto.
  Qed.
  Global Instance subsume_freeable_inst l1 q1 n1 k1 l2 q2 n2 k2 :
    Subsume (freeable_nz l1 n1 q1 k1) (freeable_nz l2 n2 q2 k2) :=
    λ T, i2p (subsume_freeable l1 q1 n1 k1 l2 q2 n2 k2 T).

  Lemma find_in_context_freeable l T :
    (∃ q n k, freeable_nz l n q k ∗ T (n, q, k))
    ⊢ find_in_context (FindFreeable l) T.
  Proof.
    iDestruct 1 as (q n k) "(Ha & HT)".
    iExists (n, q, k). by iFrame.
  Qed.
  Global Instance find_in_context_freeable_inst l :
    FindInContext (FindFreeable l) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_freeable l T).

  Lemma simplify_hyp_freeable l n q k T :
    ((freeable_nz l n q k) -∗ T)
    ⊢ simplify_hyp (freeable l n q k) T.
  Proof.
    iIntros "Ha Hf". iApply "Ha".
    destruct n; done.
  Qed.
  Global Instance simplify_hyp_freeable_inst l n q k :
    SimplifyHyp (freeable l n q k) (Some 0%N) :=
    λ T, i2p (simplify_hyp_freeable l n q k T).


  (** FindOptGvarRel *)
  Lemma find_in_context_opt_gvar_rel γ T :
    (∃ rt (γ' : gname), RelEq (T:=rt) γ' γ ∗ T (inl (rt, γ')))
    ⊢ find_in_context (FindOptGvarRelEq γ) T.
  Proof.
    iIntros "(%rt & %γ' & Hobs & HT)".
    iExists _ => /=. iFrame.
  Qed.
  Definition find_in_context_opt_gvar_rel_inst := [instance @find_in_context_opt_gvar_rel with FICSyntactic].
  Global Existing Instance find_in_context_opt_gvar_rel_inst | 1.
  (* we have a dummy instance with lower priority for the case that we cannot find an observation in the context *)
  Lemma find_in_context_opt_gvar_rel_dummy γ T :
    (True ∗ T (inr ())) ⊢ find_in_context (FindOptGvarRelEq γ) T.
  Proof.
    iIntros "[_ HT]".
    iExists _ => /=. iFrame.
  Qed.
  Definition find_in_context_opt_gvar_rel_dummy_inst := [instance @find_in_context_opt_gvar_rel_dummy with FICSyntactic].
  Global Existing Instance find_in_context_opt_gvar_rel_dummy_inst | 10.

  Lemma subsume_gvar_rel {rt} γ1' γ1 γ2' γ2 T :
    ⌜γ1' = γ2'⌝ ∗ ⌜γ1 = γ2⌝ ∗ T ⊢ subsume (Σ := Σ) (RelEq (T:=rt) γ1' γ1) (RelEq (T:=rt) γ2' γ2) T.
  Proof.
    iIntros "(-> & -> & $)".
    iIntros "Hrel". rewrite /RelEq. iDestruct "Hrel" as "(% & % & ? & ? & %HR')".
    iExists _, _. iFrame. iPureIntro. by apply HR'.
  Qed.
  Definition subsume_gvar_rel_inst := [instance @subsume_gvar_rel].
  Global Existing Instance subsume_gvar_rel_inst.

  (** FindOptInheritGvarRel *)
  Lemma find_in_context_opt_inherit_gvar_rel γ T :
    (∃ rt (γ' : gname) κs, Inherit κs (RelEq (T:=rt) γ' γ) ∗ T (inl (κs, rt, γ')))
    ⊢ find_in_context (FindOptInheritGvarRelEq γ) T.
  Proof.
    iIntros "(%rt & %γ' & %κs & Hobs & HT)".
    iExists _ => /=. iFrame.
  Qed.
  Definition find_in_context_opt_inherit_gvar_rel_inst := [instance @find_in_context_opt_inherit_gvar_rel with FICSyntactic].
  Global Existing Instance find_in_context_opt_inherit_gvar_rel_inst | 1.
  (* we have a dummy instance with lower priority for the case that we cannot find an observation in the context *)
  Lemma find_in_context_opt_inherit_gvar_rel_dummy γ T :
    (True ∗ T (inr ())) ⊢ find_in_context (FindOptInheritGvarRelEq γ) T.
  Proof.
    iIntros "[_ HT]".
    iExists _ => /=. iFrame.
  Qed.
  Definition find_in_context_opt_inherit_gvar_rel_dummy_inst := [instance @find_in_context_opt_inherit_gvar_rel_dummy with FICSyntactic].
  Global Existing Instance find_in_context_opt_inherit_gvar_rel_dummy_inst | 10.

  (** FindOptGvarPobs *)
  Lemma find_in_context_opt_gvar_pobs γ T :
    (∃ rt (r : rt), gvar_pobs γ r ∗ T (inl (existT rt r)))
    ⊢ find_in_context (FindOptGvarPobs γ) T.
  Proof.
    iIntros "(%rt & %r & Hobs & HT)".
    iExists _ => /=. iFrame.
  Qed.
  Definition find_in_context_opt_gvar_pobs_inst := [instance @find_in_context_opt_gvar_pobs with FICSyntactic].
  Global Existing Instance find_in_context_opt_gvar_pobs_inst | 1.
  (* we have a dummy instance with lower priority for the case that we cannot find an observation in the context *)
  Lemma find_in_context_opt_gvar_pobs_dummy γ T :
    (True ∗ T (inr ())) ⊢ find_in_context (FindOptGvarPobs γ) T.
  Proof.
    iIntros "[_ HT]".
    iExists _ => /=. iFrame.
  Qed.
  Definition find_in_context_opt_gvar_pobs_dummy_inst := [instance @find_in_context_opt_gvar_pobs_dummy with FICSyntactic].
  Global Existing Instance find_in_context_opt_gvar_pobs_dummy_inst | 10.

  (** FindOptObsList *)
  Lemma find_in_context_opt_obs_list γs T :
    (∃ rt (rs : list rt), ObsList γs rs ∗ T (inl (existT rt rs)))
    ⊢ find_in_context (FindOptObsList γs) T.
  Proof.
    iIntros "(%rt & %r & Hobs & HT)".
    iExists _ => /=. iFrame.
  Qed.
  Definition find_in_context_opt_obs_list_inst := [instance @find_in_context_opt_obs_list with FICSyntactic].
  Global Existing Instance find_in_context_opt_obs_list_inst | 1.
  (* we have a dummy instance with lower priority for the case that we cannot find an observation in the context *)
  Lemma find_in_context_opt_obs_list_dummy γ T :
    (True ∗ T (inr ())) ⊢ find_in_context (FindOptObsList γ) T.
  Proof.
    iIntros "[_ HT]".
    iExists _ => /=. iFrame.
  Qed.
  Definition find_in_context_opt_obs_list_dummy_inst := [instance @find_in_context_opt_obs_list_dummy with FICSyntactic].
  Global Existing Instance find_in_context_opt_obs_list_dummy_inst | 10.

  (** FindObsList *)
  Lemma find_in_context_obs_list γs T :
    (∃ rt (rs : list rt), ObsList γs rs ∗ T ((existT rt rs)))
    ⊢ find_in_context (FindObsList γs) T.
  Proof.
    iIntros "(%rt & %r & Hobs & HT)".
    iExists _ => /=. iFrame.
  Qed.
  Definition find_in_context_obs_list_inst := [instance @find_in_context_obs_list with FICSyntactic].
  Global Existing Instance find_in_context_obs_list_inst | 1.

  (** FindOptInheritGvarPobs *)
  Lemma find_in_context_opt_inherit_gvar_pobs γ T :
    (∃ rt (r : rt) κs, Inherit κs (gvar_pobs γ r) ∗ T (inl (κs, existT rt r)))
    ⊢ find_in_context (FindOptInheritGvarPobs γ) T.
  Proof.
    iIntros "(%rt & %r & %κs & Hobs & HT)".
    iExists _ => /=. iFrame.
  Qed.
  Definition find_in_context_opt_inherit_gvar_pobs_inst := [instance @find_in_context_opt_inherit_gvar_pobs with FICSyntactic].
  Global Existing Instance find_in_context_opt_inherit_gvar_pobs_inst | 1.
  (* we have a dummy instance with lower priority for the case that we cannot find an observation in the context *)
  Lemma find_in_context_opt_inherit_gvar_pobs_dummy γ T :
    (True ∗ T (inr ())) ⊢ find_in_context (FindOptInheritGvarPobs γ) T.
  Proof.
    iIntros "[_ HT]".
    iExists _ => /=. iFrame.
  Qed.
  Definition find_in_context_opt_inherit_gvar_pobs_dummy_inst := [instance @find_in_context_opt_inherit_gvar_pobs_dummy with FICSyntactic].
  Global Existing Instance find_in_context_opt_inherit_gvar_pobs_dummy_inst | 10.

  (** FindGvarPobs *)
  Lemma find_in_context_gvar_pobs γ T :
    (∃ rt (r : rt), gvar_pobs γ r ∗ T ((existT rt r)))
    ⊢ find_in_context (FindGvarPobs γ) T.
  Proof.
    iIntros "(%rt & %r & Hobs & HT)".
    iExists _ => /=. iFrame.
  Qed.
  Global Instance find_in_context_gvar_pobs_inst γ :
    FindInContext (FindGvarPobs γ) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_gvar_pobs γ T).

  Lemma find_in_context_gvar_pobs_p_pobs γ T :
    (∃ rt (r : rt), gvar_pobs γ r ∗ T (gvar_pobs γ r))
    ⊢ find_in_context (FindGvarPobsP γ) T.
  Proof.
    iIntros "(%rt & %r & Hobs & HT)".
    iExists (gvar_pobs γ r) => /=. iFrame.
  Qed.
  Global Instance find_in_context_gvar_pobs_p_pobs_inst γ :
    FindInContext (FindGvarPobsP γ) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_gvar_pobs_p_pobs γ T).

  Lemma find_in_context_gvar_pobs_p_obs γ T :
    (∃ rt (r : rt), gvar_obs γ r ∗ T (gvar_obs γ r))
    ⊢ find_in_context (FindGvarPobsP γ) T.
  Proof.
    iIntros "(%rt & %r & Hobs & HT)".
    iExists (gvar_obs γ r) => /=. iFrame.
  Qed.
  Global Instance find_in_context_gvar_pobs_p_obs_inst γ :
    FindInContext (FindGvarPobsP γ) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_gvar_pobs_p_obs γ T).

  Lemma subsume_gvar_pobs {rt} γ (r1 r2 : rt) T :
    ⌜r1 = r2⌝ ∗ T ⊢ subsume (Σ := Σ) (gvar_pobs γ r1) (gvar_pobs γ r2) T.
  Proof. iIntros "(-> & $) $". Qed.
  Global Instance subsume_gvar_pobs_inst {rt} γ (r1 r2 : rt) : Subsume (gvar_pobs γ r1) (gvar_pobs γ r2) :=
    λ T, i2p (subsume_gvar_pobs γ r1 r2 T).

  Lemma subsume_full_gvar_obs_pobs E L {rt} step γ (r1 r2 : rt) T :
    (⌜r1 = r2⌝ ∗ (gvar_pobs γ r2 -∗ T L (True)%I)) ⊢ subsume_full E L step (gvar_obs γ r1) (gvar_pobs γ r2) T.
  Proof.
    iIntros "(-> & HT)".
    iIntros (????) "#CTX #HE HL Hobs". iMod (gvar_obs_persist with "Hobs") as "#Hobs".
    iExists _, _. iPoseProof ("HT" with "Hobs") as "$". iFrame.
    iApply maybe_logical_step_intro. eauto with iFrame.
  Qed.
  Global Instance subsume_full_gvar_obs_pobs_inst E L {rt} step γ (r1 r2 : rt) : SubsumeFull E L step (gvar_obs γ r1) (gvar_pobs γ r2) :=
    λ T, i2p (subsume_full_gvar_obs_pobs E L step γ r1 r2 T).

  (** FindInherit *)
  Lemma find_in_context_inherit κ P T :
    (Inherit κ P ∗ T tt) ⊢
    find_in_context (FindInherit κ P) T.
  Proof.
    iIntros "(Hinh & HT)". iExists tt. by iFrame.
  Qed.
  Definition find_in_context_inherit_inst := [instance @find_in_context_inherit with FICSyntactic].
  Global Existing Instance find_in_context_inherit_inst | 1.

  (** FindLocInBounds *)
  Lemma find_in_context_loc_in_bounds l T :
    (∃ pre suf, loc_in_bounds l pre suf ∗ T (loc_in_bounds l pre suf))
    ⊢ find_in_context (FindLocInBounds l) T.
  Proof. iDestruct 1 as (pre suf) "[??]". iExists (loc_in_bounds _ _ _) => /=. iFrame. Qed.
  Global Instance find_in_context_loc_in_bounds_inst l :
    FindInContext (FindLocInBounds l) FICSyntactic | 1 :=
    λ T, i2p (find_in_context_loc_in_bounds l T).

  Lemma find_in_context_loc_in_bounds_loc l T :
    (∃ π k rt (lt : ltype rt) r, l ◁ₗ[π, k] r @ lt ∗ T (l ◁ₗ[π, k] r @ lt))
    ⊢ find_in_context (FindLocInBounds l) T.
  Proof. iDestruct 1 as (?????) "[??]". iExists (ltype_own _ _ _ _ _) => /=. iFrame. Qed.
  Global Instance find_in_context_loc_in_bounds_loc_inst l :
    FindInContext (FindLocInBounds l) FICSyntactic | 10 :=
    λ T, i2p (find_in_context_loc_in_bounds_loc l T).

  Lemma subsume_loc_in_bounds (l1 l2 : loc) (pre1 suf1 pre2 suf2 : nat) T :
    ⌜l1.(loc_p) = l2.(loc_p)⌝ ∗ ⌜(l1.(loc_a) + pre2 ≤ l2.(loc_a) + pre1)%Z⌝ ∗ ⌜(l2.(loc_a) + suf2 ≤ l1.(loc_a) + suf1)%Z⌝ ∗ T
    ⊢ subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) T.
  Proof.
    iIntros "(% & % & % & $)". by iApply loc_in_bounds_offset.
  Qed.
  Global Instance subsume_loc_in_bounds_inst (l1 l2 : loc) (pre1 suf1 pre2 suf2 : nat) :
    Subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) | 100 :=
    λ T, i2p (subsume_loc_in_bounds l1 l2 pre1 suf1 pre2 suf2 T).

  Lemma subsume_loc_in_bounds_evar1 (l1 l2 : loc) (pre1 suf1 pre2 suf2 : nat) T `{!IsProtected pre2} :
    ⌜pre1 = pre2⌝ ∗ subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre1 suf2) T
    ⊢ subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) T.
  Proof. iIntros "(-> & $)". Qed.
  Global Instance subsume_loc_in_bounds_evar1_inst (l1 l2 : loc) (pre1 suf1 pre2 suf2 : nat) `{!IsProtected pre2} :
    Subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) | 20 :=
    λ T, i2p (subsume_loc_in_bounds_evar1 l1 l2 pre1 suf1 pre2 suf2 T).
  Lemma subsume_loc_in_bounds_evar2 (l1 l2 : loc) (pre1 suf1 pre2 suf2 : nat) T `{!IsProtected suf2} :
    ⌜suf1 = suf2⌝ ∗ subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf1) T
    ⊢ subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) T.
  Proof. iIntros "(-> & $)". Qed.
  Global Instance subsume_loc_in_bounds_evar2_inst (l1 l2 : loc) (pre1 suf1 pre2 suf2 : nat) `{!IsProtected suf2} :
    Subsume (loc_in_bounds l1 pre1 suf1) (loc_in_bounds l2 pre2 suf2) | 20 :=
    λ T, i2p (subsume_loc_in_bounds_evar2 l1 l2 pre1 suf1 pre2 suf2 T).

  (* TODO: maybe generalize this to have a TC or so so? *)
  Lemma subsume_place_loc_in_bounds π (l1 l2 : loc) {rt} (lt : ltype rt) k r (pre suf : nat) T :
    ⌜l1 = l2⌝ ∗ ⌜pre = 0%nat⌝ ∗ li_tactic (compute_layout_goal (ltype_st lt)) (λ ly,
      l1 ◁ₗ[π, k] r @ lt -∗
      subsume (loc_in_bounds l1 0%nat (ly_size ly)) (loc_in_bounds l2 pre suf) T)
    ⊢ subsume (l1 ◁ₗ[π, k] r @ lt) (loc_in_bounds l2 pre suf) T.
  Proof.
    rewrite /compute_layout_goal. iIntros "(-> & -> & %ly & %Halg & HT)".
    iIntros "Ha". iPoseProof (ltype_own_loc_in_bounds with "Ha") as "#Hb"; first done.
    iPoseProof ("HT" with "Ha Hb") as "$".
  Qed.
  Definition subsume_place_loc_in_bounds_inst := [instance @subsume_place_loc_in_bounds].
  Global Existing Instance subsume_place_loc_in_bounds_inst.
End find.

Section iterate.
  Context `{!typeGS Σ}.

  (** Iteration for stripping all guards in the context *)
  Variant strip_guarded := StripGuarded.

  Lemma iterate_with_hooks_strip_guarded E L T :
    (find_in_context FindOptGuarded (λ g,
      match g with
      | None => T L StripGuarded
      | Some (prepaid, P) =>
          introduce_with_hooks E L (guarded prepaid P) (λ L2,
            iterate_with_hooks E L2 StripGuarded T)
      end))
    ⊢ iterate_with_hooks E L StripGuarded T.
  Proof.
    iIntros "(%g & Hg & HT)".
    iIntros (??) "#CTX #HE HL".
    destruct g as [[prepaid P] | ]; simpl.
    - simpl. iMod ("HT" with "[//] CTX HE HL Hg") as "(%L2 & HL & HT)".
      by iApply "HT".
    - by iFrame.
  Qed.
  Definition iterate_with_hooks_strip_guarded_inst := [instance @iterate_with_hooks_strip_guarded].
  Global Existing Instance iterate_with_hooks_strip_guarded_inst.
End iterate.

Section introduce.
  Context `{!typeGS Σ}.

  (** Introduce with Hooks *)
  Lemma introduce_with_hooks_sep E L P1 P2 T :
    introduce_with_hooks E L P1 (λ L', introduce_with_hooks E L' P2 T) ⊢
    introduce_with_hooks E L (P1 ∗ P2) T.
  Proof.
    iIntros "Ha" (F ?) "#CTX #HE HL [HP1 HP2]".
    iMod ("Ha" with "[//] CTX HE HL HP1") as "(%L' & HL & Ha)".
    iApply ("Ha" with "[//] CTX HE HL HP2").
  Qed.
  Definition introduce_with_hooks_sep_inst := [instance @introduce_with_hooks_sep].
  Global Existing Instance introduce_with_hooks_sep_inst.

  Lemma introduce_with_hooks_exists {X} E L (Φ : X → iProp Σ) T :
    (∀ x, introduce_with_hooks E L (Φ x) T) ⊢
    introduce_with_hooks E L (∃ x, Φ x) T.
  Proof.
    iIntros "Ha" (F ?) "#CTX #HE HL (%x & HP)".
    iApply ("Ha" with "[//] CTX HE HL HP").
  Qed.
  Definition introduce_with_hooks_exists_inst := [instance @introduce_with_hooks_exists].
  Global Existing Instance introduce_with_hooks_exists_inst.

  (* low priority base instances so that other more specialized instances trigger first *)
  Lemma introduce_with_hooks_base_learnable E L P `{HP : !LearnFromHyp P} T :
    (P -∗ introduce_with_hooks E L (learn_from_hyp_Q) T) ⊢
    introduce_with_hooks E L P T.
  Proof.
    iIntros "HT" (F ?) "#CTX #HE HL HP".
    iMod (learn_from_hyp_proof with "[//] HP") as "(HP & Hlearn)".
    iMod ("HT" with "HP [] CTX HE HL Hlearn") as "Ha"; first done.
    done.
  Qed.
  Definition introduce_with_hooks_base_learnable_inst := [instance @introduce_with_hooks_base_learnable].
  Global Existing Instance introduce_with_hooks_base_learnable_inst | 100.

  Lemma introduce_with_hooks_base E L P T :
    (P -∗ T L) ⊢
    introduce_with_hooks E L P T.
  Proof.
    iIntros "HT" (F ?) "#CTX #HE HL HP".
    iSpecialize ("HT" with "HP").
    iModIntro. iExists L. iFrame.
  Qed.
  Definition introduce_with_hooks_base_inst := [instance @introduce_with_hooks_base].
  Global Existing Instance introduce_with_hooks_base_inst | 101.

  Lemma introduce_with_hooks_direct E L P T :
    (P -∗ T L) ⊢
    introduce_with_hooks E L (introduce_direct P) T.
  Proof.
    iApply introduce_with_hooks_base.
  Qed.
  Definition introduce_with_hooks_direct_inst := [instance @introduce_with_hooks_direct].
  Global Existing Instance introduce_with_hooks_direct_inst | 1.

  (** credit related instances *)
  Lemma introduce_with_hooks_credits E L n T :
    find_in_context (FindCreditStore) (λ '(c, a),
      credit_store (n + c) a -∗ T L) ⊢
    introduce_with_hooks E L (£ n) T.
  Proof.
    rewrite /FindCreditStore. iIntros "Ha".
    iDestruct "Ha" as ([c a]) "(Hstore & HT)". simpl.
    iIntros (??) "#CTX #HE HL Hc".
    iPoseProof (credit_store_donate with "Hstore Hc") as "Hstore".
    iExists _. iFrame. iApply ("HT" with "Hstore").
  Qed.
  Definition introduce_with_hooks_credits_inst := [instance @introduce_with_hooks_credits].
  Global Existing Instance introduce_with_hooks_credits_inst | 10.

  Lemma introduce_with_hooks_tr E L n T :
    find_in_context (FindCreditStore) (λ '(c, a),
      credit_store c (n + a) -∗ T L)
    ⊢ introduce_with_hooks E L (tr n) T.
  Proof.
    rewrite /FindCreditStore. iIntros "Ha".
    iDestruct "Ha" as ([c a]) "(Hstore & HT)". simpl.
    iIntros (??) "#CTX #HE HL Hc".
    iPoseProof (credit_store_acc with "Hstore") as "(Hcred & Hat & Hcl)".
    iPoseProof ("Hcl" $! _ (n + a)%nat with "Hcred [Hat Hc]") as "Hstore".
    { rewrite -Nat.add_succ_r. rewrite tr_split. iFrame. }
    iExists _. iFrame. iApply ("HT" with "Hstore").
  Qed.
  Definition introduce_with_hooks_tr_inst := [instance @introduce_with_hooks_tr].
  Global Existing Instance introduce_with_hooks_tr_inst | 10.

  (** non-atomic token related instances *)
  Lemma introduce_with_hooks_na_own E L π mask T :
    find_in_context (FindOptNaOwn π) (λ res,
      match res with
      | None => na_own π mask -∗ T L
      | Some mask' =>
          ⌜mask' ## mask⌝ ∗ (na_own π (mask' ∪ mask) -∗ T L)
      end)
    ⊢ introduce_with_hooks E L (na_own π mask) T.
  Proof.
    rewrite /FindOptNaOwn. iIntros "(%res & Ha)".
    destruct res as [mask'|]; simpl; iIntros (??) "#CTX #HE HL Hna".
    - iDestruct "Ha" as "(Hna' & % & HT)".
      iExists _; iFrame.
      iApply "HT".
      by iApply na_own_union; [ done | iFrame ].
    - iDestruct "Ha" as "(_ & HT)".
      iExists _; iFrame.
      by iApply "HT".
  Qed.
  Definition introduce_with_hooks_na_own_inst := [instance @introduce_with_hooks_na_own].
  Global Existing Instance introduce_with_hooks_na_own_inst | 10.

  Lemma introduce_with_hooks_boringly_exist E L {A} P T :
    introduce_with_hooks E L (☒ (∃ a : A, P a)) T :-
      ∀ a,
        return (introduce_with_hooks E L (☒ P a) T).
  Proof.
    unfold introduce_with_hooks.
    iIntros "HT".
    iIntros (??) "CTX HE HL Ha".
    rewrite boringly_exists.
    iDestruct "Ha" as "(%a & Ha)".
    iApply ("HT" with "[//] CTX HE HL Ha").
  Qed.
  Definition introduce_with_hooks_boringly_exist_inst := [instance @introduce_with_hooks_boringly_exist].
  Global Existing Instance introduce_with_hooks_boringly_exist_inst.

  Lemma introduce_with_hooks_boringly_sep E L P1 P2 T :
    introduce_with_hooks E L (☒ (P1 ∗ P2)) T :-
      return (introduce_with_hooks E L (☒ P1 ∗ ☒ P2) T).
  Proof.
    unfold introduce_with_hooks.
    iIntros "HT".
    iIntros (??) "CTX HE HL Ha".
    rewrite boringly_sep.
    iApply ("HT" with "[//] CTX HE HL Ha").
  Qed.
  Definition introduce_with_hooks_boringly_sep_inst := [instance @introduce_with_hooks_boringly_sep].
  Global Existing Instance introduce_with_hooks_boringly_sep_inst.

  Lemma introduce_with_hooks_boringly_persistent E L P `{!Persistent P} T :
    introduce_with_hooks E L (☒ P) T :-
      return (introduce_with_hooks E L P T).
  Proof.
    unfold introduce_with_hooks.
    iIntros "HT".
    iIntros (??) "CTX HE HL Ha".
    rewrite boringly_persistent.
    iApply ("HT" with "[//] CTX HE HL Ha").
  Qed.
  Definition introduce_with_hooks_boringly_persistent_inst := [instance @introduce_with_hooks_boringly_persistent].
  Global Existing Instance introduce_with_hooks_boringly_persistent_inst.

  Lemma introduce_with_hooks_agree {A} {P' : A → iProp Σ} P `{Hag : !LiAgree P P'} E L b `{!CheckOwnInContext (P' b)} T :
    introduce_with_hooks E L (P) T :-
      exhale (P' b);
      inhale (P' b);
      inhale (⌜Hag.(li_agree_elem) = b⌝);
      return (T L).
  Proof.
    unfold introduce_with_hooks.
    iIntros "(Hb & HT)".
    iIntros (??) "CTX HE HL Ha".
    iPoseProof (Hag.(li_agree_to_pred) with "Ha") as "Ha".
    iPoseProof (li_agree_agree with "Ha Hb") as "<-".
    iSpecialize ("HT" with "Ha [//]"). by iFrame.
  Qed.
  Definition introduce_with_hooks_agree_inst := [instance @introduce_with_hooks_agree].
  Global Existing Instance introduce_with_hooks_agree_inst.

  (** Rules to handle disjunctions in some cases where one of the sides has a guard that can be refuted *)
  Lemma introduce_with_hooks_disj_guard_l E L guard P1 P2 `{!TCDone (¬ guard)} T :
    introduce_with_hooks E L ((⌜guard⌝ ∗ P1) ∨ P2) T :-
      return introduce_with_hooks E L P2 T.
  Proof.
    iIntros "HT".
    iIntros (??) "CTX HE HL [(% & ?) | HP]"; first done.
    iApply ("HT" with "[//] CTX HE HL HP").
  Qed.
  Definition introduce_with_hooks_disj_guard_l_inst := [instance @introduce_with_hooks_disj_guard_l].
  Global Existing Instance introduce_with_hooks_disj_guard_l_inst.
  Lemma introduce_with_hooks_disj_guard_r E L guard P1 P2 `{!TCDone (¬ guard)} T :
    introduce_with_hooks E L (P1 ∨ (⌜guard⌝ ∗ P2)) T :-
      return introduce_with_hooks E L P1 T.
  Proof.
    iIntros "HT".
    iIntros (??) "CTX HE HL [HP | (% & ?)]"; last done.
    iApply ("HT" with "[//] CTX HE HL HP").
  Qed.
  Definition introduce_with_hooks_disj_guard_r_inst := [instance @introduce_with_hooks_disj_guard_r].
  Global Existing Instance introduce_with_hooks_disj_guard_r_inst.

  Lemma introduce_with_hooks_guarded (E : elctx) (L : llctx) (P : iProp Σ) T :
    find_in_context (FindCreditStore) (λ '(c, a),
      ⌜fast_lia_hint (1 ≤ c)⌝ ∗ (credit_store (c - 1)%nat a -∗
        introduce_with_hooks E L P T)) ⊢
    introduce_with_hooks E L (guarded false P) T.
  Proof.
    rewrite /guarded/FindCreditStore/fast_lia_hint/=.
    iIntros "Ha" (??) "CTX HE HL (_ & HP)".
    iDestruct "Ha" as ([n m]) "(Hc & % & Ha)".
    simpl.
    iPoseProof (credit_store_scrounge 1 with "Hc") as "(Hc1 & Hc)"; first lia.
    iMod (lc_fupd_elim_later with "Hc1 HP") as "HP".
    iApply ("Ha" with "Hc [//] CTX HE HL HP").
  Qed.
  Definition introduce_with_hooks_guarded_inst := [instance @introduce_with_hooks_guarded].
  Global Existing Instance introduce_with_hooks_guarded_inst.

  Lemma introduce_with_hooks_guarded_prepaid (E : elctx) (L : llctx) (P : iProp Σ) T :
    introduce_with_hooks E L (tr 1 ∗ P) T ⊢
    introduce_with_hooks E L (guarded true P) T.
  Proof.
    rewrite /guarded.
    iIntros "Ha" (??) "CTX HE HL ((Hcred & Htr) & HP)".
    iDestruct "Hcred" as "(Hc1 & Hcred)".
    iMod (lc_fupd_elim_later with "Hc1 HP") as "HP".
    iApply ("Ha" with "[//] CTX HE HL").
    iFrame.
  Qed.
  Definition introduce_with_hooks_guarded_prepaid_inst := [instance @introduce_with_hooks_guarded_prepaid].
  Global Existing Instance introduce_with_hooks_guarded_prepaid_inst.
End introduce.

Section prove_subtype.
  Context `{!typeGS Σ}.

  (** ** prove_with_subtype *)
  (* We could make this an instance, but do not want to: it would sometimes make goals unprovable where stepping in manually would help *)
  Lemma prove_with_subtype_default E L step pm P T :
    P ∗ T L [] True ⊢
    prove_with_subtype E L step pm P T.
  Proof.
    iIntros "(? & ?)".
    iIntros (????) "???". iModIntro.
    iExists _, _, _. iFrame.
    iApply maybe_logical_step_intro. iL.
    destruct pm; eauto with iFrame.
  Qed.

  Lemma prove_with_subtype_sep E L step pm P1 P2 T :
    prove_with_subtype E L step pm P1 (λ L' κs R1, prove_with_subtype E L' step pm P2 (λ L'' κs2 R2, T L'' (κs ++ κs2) (R1 ∗ R2)))
    ⊢ prove_with_subtype E L step pm (P1 ∗ P2) T.
  Proof.
    iIntros "Hs" (F ???) "#CTX #HE HL".
    iMod ("Hs" with "[//] [//] [//] CTX HE HL") as "(%L' & %κs1 & %R1 & Ha & HL & Hs)".
    iMod ("Hs" with "[//] [//] [//] CTX HE HL") as "(%L'' & %κs2 & %R2 & Hb & ? & ?)".
    iExists L'', (κs1 ++ κs2), (R1 ∗ R2)%I. iFrame.
    iApply (maybe_logical_step_compose with "Ha").
    iApply (maybe_logical_step_compose with "Hb").
    iApply maybe_logical_step_intro.
    iIntros "!> (Ha2 & $) (Ha1 & $)".
    destruct pm; first by iFrame.
    rewrite lft_dead_list_app. iIntros "(Ht1 & Ht2)".
    iMod ("Ha1" with "Ht1") as "$". iMod ("Ha2" with "Ht2") as "$". done.
  Qed.
  Definition prove_with_subtype_sep_inst := [instance @prove_with_subtype_sep].
  Global Existing Instance prove_with_subtype_sep_inst.

  Lemma prove_with_subtype_exists {X} E L step pm (Φ : X → iProp Σ) T :
    (∃ x, prove_with_subtype E L step pm (Φ x) T)
    ⊢ prove_with_subtype E L step pm (∃ x, Φ x) T.
  Proof.
    iIntros "(%x & Hs)" (F ???) "#CTX #HE HL".
    iMod ("Hs" with "[//] [//] [//] CTX HE HL") as "(%L' & %κs & %R & Hs & ? & ?)".
    iExists L', κs, R. iFrame.
    iApply (maybe_logical_step_wand with "[] Hs").
    destruct pm. { iIntros "(? & ?)". eauto with iFrame. }
    iIntros "(Ha & $) Htok". iMod ("Ha" with "Htok") as "?". eauto with iFrame.
  Qed.
  Definition prove_with_subtype_exists_inst := [instance @prove_with_subtype_exists].
  Global Existing Instance prove_with_subtype_exists_inst.

  Lemma prove_with_subtype_pers E L step pm (P : iProp Σ) T :
    (□ P) ∧ T L [] True ⊢
    prove_with_subtype E L step pm (□ P) T.
  Proof.
    iIntros "[#HP HT]".
    iApply prove_with_subtype_default.
    by iFrame.
  Qed.
  Definition prove_with_subtype_pers_inst := [instance @prove_with_subtype_pers].
  Global Existing Instance prove_with_subtype_pers_inst.

  (* No corresponding lemma for [∀] -- this doesn't work, because we cannot commute the quantifier over the existential quantifiers in [prove_with_subtype] *)

  (** For ofty location ownership, we have special handling to stratify first, if possible.
      This only happens in the [ProveWithStratify] proof mode though, because we sometimes directly want to get into [Subsume]. *)
  Lemma prove_with_subtype_ofty_step π E L (l : loc) bk {rt} (ty : type rt) (r : place_rfn rt) T :
    find_in_context (FindLoc l) (λ '(existT rt' (lt', r', bk', π')),
      ⌜π = π'⌝ ∗
      stratify_ltype π E L StratMutNone StratNoUnfold StratRefoldFull StratifyUnblockOp l lt' r' bk' (λ L2 R2 rt2 lt2 r2,
        (* can't take a step, because we already took one. *)
        (*owned_subltype_step E L false (l ◁ₗ[π, bk'] r' @ lt') (l ◁ₗ[π, bk] r @ ◁ ty) T*)
        match ltype_blocked_lfts lt2 with
        | [] =>
            (* we could unblock everything, directly subsume *)
            ⌜bk = bk'⌝ ∗ weak_subltype E L2 bk r2 r lt2 (◁ ty) (T L2 [] R2)
        | κs =>
            ⌜bk = bk'⌝ ∗
            trigger_tc (SimpLtype (ltype_core lt2)) (λ lt2',
            weak_subltype E L2 bk r2 r lt2' (◁ ty) (T L2 κs R2))
        end))
    ⊢ prove_with_subtype E L true ProveWithStratify (l ◁ₗ[π, bk] r @ (◁ ty))%I T.
  Proof.
    rewrite /FindLoc.
    iIntros "Ha". iDestruct "Ha" as ([rt' [[[lt' r'] bk'] π']]) "(Hl & <- & Ha)". simpl.
    iIntros (????) "#CTX #HE HL". iMod ("Ha" with "[//] [//] [//] CTX HE HL Hl") as "(%L2 & %R2 & %rt2 & %lt2 & %r2 & HL & %Hsteq & Hstep & HT)".
    destruct (decide (ltype_blocked_lfts lt2 = [])) as [-> | Hneq].
    - iDestruct "HT" as "(<- & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(#Hincl & HL & HT)".
      iExists _, [], _. iFrame.
      simpl. iModIntro. iApply logical_step_fupd. iApply (logical_step_wand with "Hstep").
      iIntros "(Hl & $)".
      iDestruct "Hincl" as "(_ & Hincl & _)".
      iMod (ltype_incl'_use with "Hincl Hl"); first done.
      iModIntro. by iIntros "_ !>".
    - iAssert (⌜bk = bk'⌝ ∗ trigger_tc (SimpLtype (ltype_core lt2)) (λ lt2', weak_subltype E L2 bk r2 r lt2' (◁ ty) (T L2 (ltype_blocked_lfts lt2) R2)))%I with "[HT]" as "(<- & HT)".
      { destruct (ltype_blocked_lfts lt2); done. }
      iDestruct "HT" as "(%lt2' & %Heq & HT)".
      destruct Heq as [<-].
      iMod ("HT" with "[//] CTX HE HL") as "(#Hincl & HL & HT)".
      iModIntro. iExists _, _, _. iFrame.
      iApply (logical_step_wand with "Hstep").
      iIntros "(Hl & $)".
      iIntros "Hdead".
      iPoseProof (imp_unblockable_blocked_dead lt2) as "Hunblock".
      iDestruct "Hincl" as "(_ & Hincl & _)".
      iMod (imp_unblockable_use with "Hunblock Hdead Hl") as "Hl"; first done.
      by iMod (ltype_incl'_use with "Hincl Hl") as "$".
  Qed.
  Definition prove_with_subtype_ofty_step_inst := [instance @prove_with_subtype_ofty_step].
  Global Existing Instance prove_with_subtype_ofty_step_inst | 500.

  Lemma prove_with_subtype_pure E L step pm (P : Prop) T :
    ⌜P⌝ ∗ T L [] True ⊢ prove_with_subtype E L step pm (⌜P⌝) T.
  Proof.
    iIntros "(% & HT)". iIntros (????) "#CTX #HE HL".
    iExists L, [], True%I. iFrame.
    destruct pm.
    - by iApply maybe_logical_step_intro.
    - iIntros "!>". iApply maybe_logical_step_intro. iSplitL; last done.
      iIntros "_ !>". done.
  Qed.
  Definition prove_with_subtype_pure_inst := [instance @prove_with_subtype_pure].
  Global Existing Instance prove_with_subtype_pure_inst | 50.

  Lemma prove_with_subtype_simplify_goal E L step pm P T (n : N) {SG : SimplifyGoal P (Some n)} :
    prove_with_subtype E L step pm (SG True).(i2p_P) T
    ⊢ prove_with_subtype E L step pm P T.
  Proof.
    iIntros "Ha" (????) "#CTX #HE HL".
    iMod ("Ha" with "[//] [//] [//] CTX HE HL") as "(%L' & %κs & %R & Ha & HL & HT)".
    unfold SimplifyGoal in SG.
    destruct SG as [P' Ha].
    iExists L', κs, R. iFrame.
    iApply (maybe_logical_step_wand with "[] Ha").
    iIntros "(Ha & $)".
    destruct pm.
    - iPoseProof (Ha with "Ha") as "Ha".
      rewrite /simplify_goal. iDestruct "Ha" as "($ & _)".
    - iIntros "Hdead". iMod ("Ha" with "Hdead") as "Ha".
      iPoseProof (Ha with "Ha") as "Ha".
      rewrite /simplify_goal. iDestruct "Ha" as "($ & _)".
      done.
  Qed.
  Global Instance prove_with_subtype_simplify_goal_inst E L step pm P {SG : SimplifyGoal P (Some 0%N)} :
    ProveWithSubtype E L step pm P := λ T, i2p (prove_with_subtype_simplify_goal E L step pm P T 0).

  (** Note: run fully-fledged simplification only after context search *)
  Global Instance prove_with_subtype_simplify_goal_full_inst E L step pm P n {SG : SimplifyGoal P (Some n)} :
    ProveWithSubtype E L step pm P | 1001 := λ T, i2p (prove_with_subtype_simplify_goal E L step pm P T n).

  (* Make low priority to enable overrides before we initiate context search. *)
  Lemma prove_with_subtype_find_direct E L step pm P T `{!CheckOwnInContext P} :
    P ∗ T L [] True%I
    ⊢ prove_with_subtype E L step pm P T.
  Proof.
    iIntros "(HP & HT)". iIntros (????) "#CTX #HE HL".
    iExists L, [], True%I. iFrame.
    iApply maybe_logical_step_intro. iSplitL; last done.
    destruct pm; first done. iIntros "!> _ !>". done.
  Qed.
  Definition prove_with_subtype_find_direct_inst := [instance @prove_with_subtype_find_direct].
  Global Existing Instance prove_with_subtype_find_direct_inst | 1000.

  Lemma prove_with_subtype_primitive E L step pm P `{Hrel : !RelatedTo P} T :
    find_in_context Hrel.(rt_fic) (λ a,
      subsume_full E L step (fic_Prop Hrel.(rt_fic) a) P (λ L, T L []))
    ⊢ prove_with_subtype E L step pm P T.
  Proof.
    iIntros "(%a & Ha & Hsub)" (????) "#CTX #HE HL".
    iMod ("Hsub" with "[//] [//] [//] CTX HE HL Ha") as "(%L2 & %R & Ha & ? & ?)".
    iModIntro. iExists _, _, _. iFrame.
    iApply (maybe_logical_step_wand with "[] Ha").
    iIntros "(? & $)".
    destruct pm; first done. iIntros "_ !>". done.
  Qed.
  (* only after running full simplification *)
  Definition prove_with_subtype_primitive_inst := [instance @prove_with_subtype_primitive].
  Global Existing Instance prove_with_subtype_primitive_inst | 1002.

  Lemma prove_with_subtype_case_destruct E L step pm {A} (b : A) P T :
    case_destruct b (λ b r, (prove_with_subtype E L step pm (P b r) T))
    ⊢ prove_with_subtype E L step pm (case_destruct b P) T.
  Proof.
    rewrite /case_destruct. apply prove_with_subtype_exists.
  Qed.
  Definition prove_with_subtype_case_destruct_inst := [instance @prove_with_subtype_case_destruct].
  Global Existing Instance prove_with_subtype_case_destruct_inst.

  Lemma prove_with_subtype_if_decide_true E L step pm P `{!Decision P} `{!CanSolve P} P1 P2 T :
    prove_with_subtype E L step pm P1 T ⊢
    prove_with_subtype E L step pm (if (decide P) then P1 else P2) T.
  Proof. rewrite decide_True; done. Qed.
  Definition prove_with_subtype_if_decide_true_inst := [instance @prove_with_subtype_if_decide_true].
  Global Existing Instance prove_with_subtype_if_decide_true_inst.
  Lemma prove_with_subtype_if_decide_false E L step pm P `{!Decision P} `{!CanSolve (¬ P)} P1 P2 T :
    prove_with_subtype E L step pm P2 T ⊢
    prove_with_subtype E L step pm (if (decide P) then P1 else P2) T.
  Proof. rewrite decide_False; done. Qed.
  Definition prove_with_subtype_if_decide_false_inst := [instance @prove_with_subtype_if_decide_false].
  Global Existing Instance prove_with_subtype_if_decide_false_inst.

  Lemma prove_with_subtype_li_trace E L step pm {M} (m : M) P T :
    li_trace m (prove_with_subtype E L step pm P T)
    ⊢ prove_with_subtype E L step pm (li_trace m P) T.
  Proof.
    rewrite /li_trace. done.
  Qed.
  Definition prove_with_subtype_li_trace_inst := [instance @prove_with_subtype_li_trace].
  Global Existing Instance prove_with_subtype_li_trace_inst.

  Lemma prove_with_subtype_scrounge_credits E L step pm (n : nat) T :
    find_in_context (FindCreditStore) (λ '(c, a),
      ⌜fast_lia_hint (n ≤ c)⌝ ∗ (credit_store (c - n)%nat a -∗ T L [] True%I))
    ⊢ prove_with_subtype E L step pm (£ n) T.
  Proof.
    iIntros "Ha". rewrite /FindCreditStore /fast_lia_hint.
    iDestruct "Ha" as ([c a]) "(Hstore  & %Hn & HT)". simpl.
    iPoseProof (credit_store_scrounge n with "Hstore") as "(Hcred & Hstore)"; first lia.
    iPoseProof ("HT" with "Hstore") as "HT".
    iIntros (????) "CTX HE HL". iModIntro. iExists _, _, _. iFrame.
    iApply maybe_logical_step_intro.
    iSplitL; last done.
    destruct pm; first done. iIntros "_ !>". done.
  Qed.
  Definition prove_with_subtype_scrounge_credits_inst := [instance @prove_with_subtype_scrounge_credits].
  Global Existing Instance prove_with_subtype_scrounge_credits_inst | 10.

  Lemma prove_with_subtype_scrounge_tr E L step pm (n : nat) T :
    find_in_context (FindCreditStore) (λ '(c, a),
      ⌜fast_lia_hint (n ≤ a)⌝ ∗ (credit_store c (a - n)%nat -∗ T L [] True%I))
    ⊢ prove_with_subtype E L step pm (tr n) T.
  Proof.
    iIntros "Ha". rewrite /FindCreditStore /fast_lia_hint.
    iDestruct "Ha" as ([c a]) "(Hstore  & %Hn & HT)". simpl.
    iPoseProof (credit_store_acc with "Hstore") as "(Hcred & Hat & Hcl)".
    replace (S a) with (S (a - n) + n)%nat by lia.
    iDestruct "Hat" as "(Hat & Hat')".
    iPoseProof ("Hcl" with "Hcred Hat") as "Hstore".
    iPoseProof ("HT" with "Hstore") as "HT".
    iIntros (????) "CTX HE HL". iModIntro. iExists _, _, _. iFrame.
    iApply maybe_logical_step_intro.
    iSplitL; last done.
    destruct pm; first done. iIntros "_ !>". done.
  Qed.
  Definition prove_with_subtype_scrounge_tr_inst := [instance @prove_with_subtype_scrounge_tr].
  Global Existing Instance prove_with_subtype_scrounge_tr_inst | 10.

  (** Rules to handle disjunctions in some cases where one of the sides has a guard that can be proved or refuted *)
  Lemma prove_with_subtype_disj_guard_l_right E L b pm guard P1 P2 `{!TCDone (¬ guard)} T  :
    prove_with_subtype E L b pm ((⌜guard⌝ ∗ P1) ∨ P2) T :-
      return prove_with_subtype E L b pm P2 T.
  Proof.
    unfold prove_with_subtype.
    iIntros "HT".
    iIntros (????) "CTX HE HL".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L2 & % & %R & Hstep & $ & $)".
    iApply (maybe_logical_step_wand with "[] Hstep").
    destruct pm.
    - iIntros "(? & $)". iRight. by iFrame.
    - iIntros "(Ha & $) Hdead".
      iMod ("Ha" with "Hdead") as "?".
      iRight. by iFrame.
  Qed.
  Definition prove_with_subtype_disj_guard_l_right_inst := [instance @prove_with_subtype_disj_guard_l_right].
  Global Existing Instance prove_with_subtype_disj_guard_l_right_inst.
  Lemma prove_with_subtype_disj_guard_r_left E L b pm guard P1 P2 `{!TCDone (¬ guard)} T  :
    prove_with_subtype E L b pm (P1 ∨ (⌜guard⌝ ∗ P2)) T :-
      return prove_with_subtype E L b pm P1 T.
  Proof.
    unfold prove_with_subtype.
    iIntros "HT".
    iIntros (????) "CTX HE HL".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L2 & % & %R & Hstep & $ & $)".
    iApply (maybe_logical_step_wand with "[] Hstep").
    destruct pm.
    - iIntros "(? & $)". iLeft. by iFrame.
    - iIntros "(Ha & $) Hdead".
      iMod ("Ha" with "Hdead") as "?".
      iLeft. by iFrame.
  Qed.
  Definition prove_with_subtype_disj_guard_r_left_inst := [instance @prove_with_subtype_disj_guard_r_left].
  Global Existing Instance prove_with_subtype_disj_guard_r_left_inst.

  (** Below rules are lower priority because they might make a goal unprovable *)
  Lemma prove_with_subtype_disj_guard_l_left E L b pm guard P1 P2 `{!TCDone guard} T  :
    prove_with_subtype E L b pm ((⌜guard⌝ ∗ P1) ∨ P2) T :-
      return prove_with_subtype E L b pm P1 T.
  Proof.
    unfold prove_with_subtype.
    iIntros "HT".
    iIntros (????) "CTX HE HL".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L2 & % & %R & Hstep & $ & $)".
    iApply (maybe_logical_step_wand with "[] Hstep").
    destruct pm.
    - iIntros "(? & $)". iLeft. by iFrame.
    - iIntros "(Ha & $) Hdead".
      iMod ("Ha" with "Hdead") as "?".
      iLeft. by iFrame.
  Qed.
  Definition prove_with_subtype_disj_guard_l_left_inst := [instance @prove_with_subtype_disj_guard_l_left].
  Global Existing Instance prove_with_subtype_disj_guard_l_left_inst | 100.
  Lemma prove_with_subtype_disj_guard_r_right E L b pm guard P1 P2 `{!TCDone guard} T  :
    prove_with_subtype E L b pm (P1 ∨ (⌜guard⌝ ∗ P2)) T :-
      return prove_with_subtype E L b pm P2 T.
  Proof.
    unfold prove_with_subtype.
    iIntros "HT".
    iIntros (????) "CTX HE HL".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L2 & % & %R & Hstep & $ & $)".
    iApply (maybe_logical_step_wand with "[] Hstep").
    destruct pm.
    - iIntros "(? & $)". iRight. by iFrame.
    - iIntros "(Ha & $) Hdead".
      iMod ("Ha" with "Hdead") as "?".
      iRight. by iFrame.
  Qed.
  Definition prove_with_subtype_disj_guard_r_right_inst := [instance @prove_with_subtype_disj_guard_r_right].
  Global Existing Instance prove_with_subtype_disj_guard_r_right_inst | 100.

  (** Do a case analysis when proving if_iNone/if_iSome *)
  Inductive destruct_hint_prove : Type :=
  | DestructHintProve {A} (a : A)
  | DestructHintProveKnown {A} (a : A)
  .
  Lemma prove_with_subtype_destruct {A} (a : A) P E L step pm T :
    prove_with_subtype E L step pm P T :-
      c, b ← destruct a;
      trace (if b then DestructHintProve c else DestructHintProveKnown c);
      return (prove_with_subtype E L step pm P T).
  Proof.
    iIntros "(%b & HT)". done.
  Qed.

  (** Instances for Option *)
  (** first some simplification instances that trigger if we shouldn't destruct. *)
  Lemma simplify_goal_if_iSome_Some {A} (x : A) Φ T :
    (Φ x ∗ T) ⊢@{iProp Σ} simplify_goal (if_iSome (Some x) Φ) T.
  Proof. simpl. done. Qed.
  Definition simplify_goal_if_iSome_Some_inst := [instance @simplify_goal_if_iSome_Some with 0%N].
  Global Existing Instance simplify_goal_if_iSome_Some_inst.
  Lemma simplify_goal_if_iSome_None {A} (Φ : A → iProp Σ) T :
    T ⊢@{iProp Σ} simplify_goal (if_iSome None Φ) T.
  Proof. simpl. iIntros "$". Qed.
  Definition simplify_goal_if_iSome_None_inst := [instance @simplify_goal_if_iSome_None with 0%N].
  Global Existing Instance simplify_goal_if_iSome_None_inst.
  Lemma simplify_goal_if_iNone_None {A} Φ T :
    (Φ ∗ T) ⊢@{iProp Σ} simplify_goal (if_iNone (A:=A) None Φ) T.
  Proof. simpl. done. Qed.
  Definition simplify_goal_if_iNone_None_inst := [instance @simplify_goal_if_iNone_None with 0%N].
  Global Existing Instance simplify_goal_if_iNone_None_inst.
  Lemma simplify_goal_if_iNone_Some {A} (x : A) Φ T :
    (T) ⊢@{iProp Σ} simplify_goal (if_iNone (A:=A) (Some x) Φ) T.
  Proof. simpl. iIntros "$". Qed.
  Definition simplify_goal_if_iNone_Some_inst := [instance @simplify_goal_if_iNone_Some with 0%N].
  Global Existing Instance simplify_goal_if_iNone_Some_inst.

  (* Otherwise, destruct *)
  Definition prove_with_subtype_destruct_if_iSome {A} (x : option A) P :=
    prove_with_subtype_destruct x (if_iSome x P).
  Definition prove_with_subtype_destruct_if_iSome_inst := [instance @prove_with_subtype_destruct_if_iSome].
  Global Existing Instance prove_with_subtype_destruct_if_iSome_inst | 100.

  Definition prove_with_subtype_destruct_if_iNone {A} (x : option A) P :=
    prove_with_subtype_destruct x (if_iNone x P).
  Definition prove_with_subtype_destruct_if_iNone_inst := [instance @prove_with_subtype_destruct_if_iNone].
  Global Existing Instance prove_with_subtype_destruct_if_iNone_inst | 100.

  (** Instances for Result *)
  Lemma simplify_goal_if_iOk_Ok {A B} (x : A) Φ T :
    (Φ x ∗ T) ⊢@{iProp Σ} simplify_goal (if_iOk (B:=B) (Ok x) Φ) T.
  Proof. simpl. done. Qed.
  Definition simplify_goal_if_iOk_Ok_inst := [instance @simplify_goal_if_iOk_Ok with 0%N].
  Global Existing Instance simplify_goal_if_iOk_Ok_inst.
  Lemma simplify_goal_if_iOk_Err {A B} (x : B) (Φ : A → iProp Σ) T :
    T ⊢@{iProp Σ} simplify_goal (if_iOk (Err x) Φ) T.
  Proof. simpl. iIntros "$". Qed.
  Definition simplify_goal_if_iOk_Err_inst := [instance @simplify_goal_if_iOk_Err with 0%N].
  Global Existing Instance simplify_goal_if_iOk_Err_inst.
  Lemma simplify_goal_if_iErr_Err {A B} (x : B) Φ T :
    (Φ x ∗ T) ⊢@{iProp Σ} simplify_goal (if_iErr (A:=A) (Err x) Φ) T.
  Proof. simpl. done. Qed.
  Definition simplify_goal_if_iErr_Err_inst := [instance @simplify_goal_if_iErr_Err with 0%N].
  Global Existing Instance simplify_goal_if_iErr_Err_inst.
  Lemma simplify_goal_if_iErr_Ok {A B} (x : A) Φ T :
    (T) ⊢@{iProp Σ} simplify_goal (if_iErr (B:=B) (Ok x) Φ) T.
  Proof. simpl. iIntros "$". Qed.
  Definition simplify_goal_if_iErr_Ok_inst := [instance @simplify_goal_if_iErr_Ok with 0%N].
  Global Existing Instance simplify_goal_if_iErr_Ok_inst.

  Definition prove_with_subtype_destruct_if_iOk {A B} (x : result A B) P :=
    prove_with_subtype_destruct x (if_iOk x P).
  Definition prove_with_subtype_destruct_if_iOk_inst := [instance @prove_with_subtype_destruct_if_iOk].
  Global Existing Instance prove_with_subtype_destruct_if_iOk_inst | 100.

  Definition prove_with_subtype_destruct_if_iErr {A B} (x : result A B) P :=
    prove_with_subtype_destruct x (if_iErr x P).
  Definition prove_with_subtype_destruct_if_iErr_inst := [instance @prove_with_subtype_destruct_if_iErr].
  Global Existing Instance prove_with_subtype_destruct_if_iErr_inst | 100.

  (** Instances for bool *)
  Lemma simplify_goal_if_iTrue_true Φ T :
    (Φ ∗ T) ⊢@{iProp Σ} simplify_goal (if_iTrue true Φ) T.
  Proof. simpl. done. Qed.
  Definition simplify_goal_if_iTrue_true_inst := [instance @simplify_goal_if_iTrue_true with 0%N].
  Global Existing Instance simplify_goal_if_iTrue_true_inst.
  Lemma simplify_goal_if_iTrue_false (Φ : iProp Σ) T :
    T ⊢@{iProp Σ} simplify_goal (if_iTrue false Φ) T.
  Proof. simpl. iIntros "$". Qed.
  Definition simplify_goal_if_iTrue_false_inst := [instance @simplify_goal_if_iTrue_false with 0%N].
  Global Existing Instance simplify_goal_if_iTrue_false_inst.
  Lemma simplify_goal_if_iFalse_false Φ T :
    (Φ ∗ T) ⊢@{iProp Σ} simplify_goal (if_iFalse false Φ) T.
  Proof. simpl. done. Qed.
  Definition simplify_goal_if_iFalse_false_inst := [instance @simplify_goal_if_iFalse_false with 0%N].
  Global Existing Instance simplify_goal_if_iFalse_false_inst.
  Lemma simplify_goal_if_iFalse_true Φ T :
    (T) ⊢@{iProp Σ} simplify_goal (if_iFalse true Φ) T.
  Proof. simpl. iIntros "$". Qed.
  Definition simplify_goal_if_iFalse_true_inst := [instance @simplify_goal_if_iFalse_true with 0%N].
  Global Existing Instance simplify_goal_if_iFalse_true_inst.

  Definition prove_with_subtype_destruct_if_iTrue (b : bool) P :=
    prove_with_subtype_destruct b (if_iTrue b P).
  Definition prove_with_subtype_destruct_if_iTrue_inst := [instance @prove_with_subtype_destruct_if_iTrue].
  Global Existing Instance prove_with_subtype_destruct_if_iTrue_inst | 100.

  Definition prove_with_subtype_destruct_if_ifalse (b : bool) P :=
    prove_with_subtype_destruct b (if_iFalse b P).
  Definition prove_with_subtype_destruct_if_ifalse_inst := [instance @prove_with_subtype_destruct_if_ifalse].
  Global Existing Instance prove_with_subtype_destruct_if_ifalse_inst | 100.

  (** Guarded *)
  Lemma prove_with_subtype_guarded E L b pm wl P T :
    prove_with_subtype E L b pm (maybe_creds wl ∗ P) T ⊢
    prove_with_subtype E L b pm (guarded wl P) T.
  Proof.
    iIntros "HT" (????) "#CTX HE HL".
    iMod ("HT" with "[] [] [] CTX HE HL") as "(%L2 & % & % & Hs & HL & HT)"; [done.. | ].
    iModIntro. iExists _, _, _. iFrame.
    iApply (maybe_logical_step_wand with "[] Hs").
    iIntros "(Ha & $)".
    unfold guarded. destruct pm.
    - iDestruct "Ha" as "(Hcred & HP)". iFrame.
    - iIntros "Hd". iMod ("Ha" with "Hd") as "Ha".
      iDestruct "Ha" as "(Hcred & HP)". by iFrame.
  Qed.
  Definition prove_with_subtype_guarded_inst := [instance @prove_with_subtype_guarded].
  Global Existing Instance prove_with_subtype_guarded_inst.
End prove_subtype.

Section subsume.
  Context `{!typeGS Σ}.

  (** Simplify instances *)
  Lemma simplify_goal_guarded wl P T :
    maybe_creds wl ∗ P ∗ T
    ⊢ simplify_goal (guarded wl P) T.
  Proof.
    rewrite /simplify_goal /guarded.
    iIntros "($ & $ & $)".
  Qed.
  Definition simplify_goal_guarded_inst := [instance @simplify_goal_guarded with 100%N].
  Global Existing Instance simplify_goal_guarded_inst.

  Lemma simplify_goal_lft_dead_list κs T :
    ([∗ list] κ ∈ κs, [† κ]) ∗ T ⊢ simplify_goal (lft_dead_list κs) T.
  Proof.
    rewrite /simplify_goal. iFrame. eauto.
  Qed.
  Global Instance simplify_goal_lft_dead_list_inst κs :
    SimplifyGoal (lft_dead_list κs) (Some 0%N) := λ T, i2p (simplify_goal_lft_dead_list κs T).

  (** ** SubsumeFull instances *)
  (** We have low-priority instances to escape into subtyping judgments *)
  (* TODO should make compatible with mem_casts? *)
  (*
  Lemma subsume_full_own_val {rt1 rt2} π E L step v (ty1 : type rt1) (ty2 : type rt2) r1 r2 T :
    weak_subtype E L r1 r2 ty1 ty2 (T L True) -∗
    subsume_full E L step (v ◁ᵥ{π} r1 @ ty1) (v ◁ᵥ{π} r2 @ ty2) T.
  Proof.
    iIntros "HT" (F ?) "#CTX #HE HL Hv".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & HL & HT)".
    iDestruct "Hincl" as "(_ & _ & #Hincl & _)".
    iExists _, True%I. iFrame.
    iApply maybe_logical_step_intro. rewrite right_id.
    by iPoseProof ("Hincl" with "Hv") as "$".
  Qed.
  (* low priority, more specific instances should trigger first *)
  Global Instance subsume_full_own_val_inst {rt1 rt2} π E L step v (ty1 : type rt1) (ty2 : type rt2) r1 r2 :
    SubsumeFull E L step (v ◁ᵥ{π} r1 @ ty1) (v ◁ᵥ{π} r2 @ ty2) | 100 :=
    λ T, i2p (subsume_full_own_val π E L step v ty1 ty2 r1 r2 T).
  *)

  Lemma subsume_full_value_evar π E L step v {rt} (ty : type rt) (r1 r2 : rt) m1 m2 T :
    ⌜r1 = r2⌝ ∗ ⌜m1 = m2⌝ ∗ T L True%I
    ⊢ subsume_full E L step (v ◁ᵥ{π, m1} r1 @ ty) (v ◁ᵥ{π, m2} r2 @ ty) T.
  Proof.
    iIntros "(-> & -> & HT)". by iApply subsume_full_id.
  Qed.
  Global Instance subsume_full_value_evar_inst π E L step v {rt} (ty : type rt) (r1 r2 : rt) m1 m2 :
    SubsumeFull E L step (v ◁ᵥ{π, m1} r1 @ ty) (v ◁ᵥ{π, m2} r2 @ ty) | 5 :=
    λ T, i2p (subsume_full_value_evar π E L step v ty r1 r2 m1 m2 T).


  Lemma owned_subtype_default {rt} π E L (ty1 ty2 : type rt) r1 r2 b T :
    ⌜fast_eq_hint (ty1 = ty2)⌝ ∗ ⌜r1 = r2⌝ ∗ T L
    ⊢ owned_subtype π E L b r1 r2 ty1 ty2 T.
  Proof.
    iIntros "(<- & <- & HT)".
    iApply owned_subtype_id.
    iFrame. done.
  Qed.
  (*Definition owned_subtype_default_inst := [instance @owned_subtype_default].*)
  (*Global Existing Instance owned_subtype_default_inst | 1000.*)

  Lemma subsume_full_owned_subtype π E L step v {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) r1 r2 m1 m2 T :
    ⌜m1 = MetaNone⌝ ∗ ⌜m2 = MetaNone⌝ ∗ owned_subtype π E L false r1 r2 ty1 ty2 (λ L', T L' True%I)
    ⊢ subsume_full E L step (v ◁ᵥ{π, m1} r1 @ ty1) (v ◁ᵥ{π, m2} r2 @ ty2) T.
  Proof.
    iIntros "(-> & -> & HT)" (????) "#CTX #HE HL Hv".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L' & Hincl & HL & HT)".
    iDestruct "Hincl" as "(_ & _ & Hincl)".
    iPoseProof ("Hincl" with "Hv") as "Hv".
    iExists _, _. iFrame. iApply maybe_logical_step_intro.
    by iFrame.
  Qed.
  Definition subsume_full_owned_subtype_inst := [instance @subsume_full_owned_subtype].
  Global Existing Instance subsume_full_owned_subtype_inst | 100.

  (* TODO: how does the evar thing work here? *)
  Lemma subsume_full_own_loc_bk_evar {rt1 rt2} π E L step l (lt1 : ltype rt1) (lt2 : ltype rt2) b1 b2 r1 r2 `{!ContainsProtected b2} T :
    ⌜b1 = b2⌝ ∗ subsume_full E L step (l ◁ₗ[π, b1] r1 @ lt1) (l ◁ₗ[π, b2] r2 @ lt2) T
    ⊢ subsume_full E L step (l ◁ₗ[π, b1] r1 @ lt1) (l ◁ₗ[π, b2] r2 @ lt2) T.
  Proof. iIntros "(-> & HT)". done. Qed.
  Definition subsume_full_own_loc_bk_evar_inst := [instance @subsume_full_own_loc_bk_evar].
  Global Existing Instance subsume_full_own_loc_bk_evar_inst | 1000.

  Lemma subsume_full_own_loc_owned {rt1 rt2} π E L l (lt1 : ltype rt1) (lt2 : ltype rt2) r1 r2 T :
    owned_subltype_step π E L l r1 r2 lt1 lt2 T
    ⊢ subsume_full E L true (l ◁ₗ[π, Owned] r1 @ lt1) (l ◁ₗ[π, Owned] r2 @ lt2) T.
  Proof.
    iIntros "HT" (????) "#CTX #HE HL Hl".
    iMod ("HT" with "[//] CTX HE HL Hl") as "(%L' & %R & Hstep & %Hly & HL & HT)".
    iExists L', R. by iFrame.
  Qed.
  Definition subsume_full_own_loc_owned_inst := [instance @subsume_full_own_loc_owned].
  Global Existing Instance subsume_full_own_loc_owned_inst | 1001.

  (* TODO should make compatible with location simplification *)
  Lemma subsume_full_own_loc {rt1 rt2} π E L step l (lt1 : ltype rt1) (lt2 : ltype rt2) b1 b2 r1 r2 T :
    ⌜lctx_bor_kind_direct_incl E L b2 b1⌝ ∗ weak_subltype E L b2 r1 r2 lt1 lt2 (T L True%I)
    ⊢ subsume_full E L step (l ◁ₗ[π, b1] r1 @ lt1) (l ◁ₗ[π, b2] r2 @ lt2) T.
  Proof.
    iIntros "(%Hincl & HT)" (F ???) "#CTX #HE HL Hl".
    iPoseProof (lctx_bor_kind_direct_incl_use with "HE HL") as "#Hincl"; first done.
    iPoseProof (ltype_bor_kind_direct_incl with "Hincl Hl") as "Hl".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl' & HL & HT)".
    iMod (ltype_incl_use with "Hincl' Hl") as "Hl"; first done.
    iExists _, True%I. iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Definition subsume_full_own_loc_inst := [instance @subsume_full_own_loc].
  Global Existing Instance subsume_full_own_loc_inst | 1002.

  (** Weaker Subsume instances for compatibility *)
  Lemma subsume_own_loc {rt} π l (lt1 : ltype rt) (lt2 : ltype rt) b1 b2 r1 r2 T :
    subsume (l ◁ₗ[π, b1] r1 @ lt1) (l ◁ₗ[π, b2] r2 @ lt2) T :-
      exhale (⌜b1 = b2⌝);
      exhale (⌜lt1 = lt2⌝);
      exhale (⌜r1 = r2⌝);
      return T.
  Proof.
    iIntros "(-> & -> & -> & HT) Ha". iFrame.
  Qed.
  Definition subsume_own_loc_inst := [instance @subsume_own_loc].
  Global Existing Instance subsume_own_loc_inst.


  (** ** Subtyping instances: [weak_subtype] *)
  Lemma weak_subtype_id E L {rt} (ty : type rt) r T :
    T ⊢ weak_subtype E L r r ty ty T.
  Proof.
    iIntros "$" (??) "?? $". iApply type_incl_refl.
  Qed.
  Lemma weak_subtype_subtype_l {rt1 rt2 rt1'} (ty1 : type rt1) (ty1' : type rt1') (ty2 : type rt2) r1 r1' r2 E L T :
    subtype E L r1 r1' ty1 ty1' →
    weak_subtype E L r1' r2 ty1' ty2 T -∗
    weak_subtype E L r1 r2 ty1 ty2 T.
  Proof.
    iIntros (Hsub) "HT". rewrite /weak_subtype.
    iIntros (??) "#CTX #HE HL".
    iPoseProof (subtype_acc with "HE HL") as "#Hincl1"; first done.
    iMod ("HT" with "[] CTX HE HL") as "(#Hincl2 & $ & $)"; first done.
    iModIntro. iApply type_incl_trans; done.
  Qed.
  Lemma weak_subtype_subtype_r {rt1 rt2 rt2'} (ty1 : type rt1) (ty2' : type rt2') (ty2 : type rt2) r1 r2' r2 E L T :
    subtype E L r2' r2 ty2' ty2 →
    weak_subtype E L r1 r2' ty1 ty2' T -∗
    weak_subtype E L r1 r2 ty1 ty2 T.
  Proof.
    iIntros (Hsub) "HT". rewrite /weak_subtype.
    iIntros (??) "#CTX #HE HL".
    iPoseProof (subtype_acc with "HE HL") as "#Hincl1"; first done.
    iMod ("HT" with "[] CTX HE HL") as "(#Hincl2 & $ & $)"; first done.
    iModIntro. iApply type_incl_trans; done.
  Qed.

  Lemma weak_subtype_evar2 E L {rt} (ty ty2 : type rt) r r2 `{!ContainsProtected ty2} T :
    ⌜ty = ty2⌝ ∗ weak_subtype E L r r2 ty ty T ⊢ weak_subtype E L r r2 ty ty2 T.
  Proof. iIntros "(<- & $)". Qed.
  Definition weak_subtype_evar2_inst := [instance @weak_subtype_evar2].
  Global Existing Instance weak_subtype_evar2_inst | 1000.

  Lemma weak_subtype_default E L {rt} (ty1 ty2 : type rt) r1 r2 T :
    ⌜r1 = r2⌝ ∗ mut_subtype E L ty1 ty2 T
    ⊢ weak_subtype E L r1 r2 ty1 ty2 T.
  Proof.
    iIntros "(<- & %Heq & ?)".
    iApply weak_subtype_subtype_l; first done.
    by iApply weak_subtype_id.
  Qed.
  Definition weak_subtype_default_inst := [instance @weak_subtype_default].
  Global Existing Instance weak_subtype_default_inst | 1001.

  (** ** Subtyping instances: [mut_subtype] *)
  Lemma mut_subtype_evar E L {rt} (ty ty2 : type rt) `{!ContainsProtected ty2} T :
    ⌜ty = ty2⌝ ∗ T ⊢ mut_subtype E L ty ty2 T.
  Proof. iIntros "(<- & $)". iPureIntro. reflexivity. Qed.
  Definition mut_subtype_evar_inst := [instance @mut_subtype_evar].
  Global Existing Instance mut_subtype_evar_inst | 1000.

  Lemma mut_subtype_default E L {rt} (ty ty2 : type rt) T :
    mut_eqtype E L ty ty2 T ⊢ mut_subtype E L ty ty2 T.
  Proof.
    iIntros "(%Heq & $)".
    iPureIntro. by apply full_eqtype_subtype_l.
  Qed.
  Definition mut_subtype_default_inst := [instance @mut_subtype_default].
  Global Existing Instance mut_subtype_default_inst | 1001.

  (** ** Subtyping instances: [mut_eqtype] *)
  Lemma mut_eqtype_evar E L {rt} (ty ty2 : type rt) `{!ContainsProtected ty2} T :
    ⌜ty = ty2⌝ ∗ T ⊢ mut_eqtype E L ty ty2 T.
  Proof. iIntros "(<- & $)". iPureIntro. reflexivity. Qed.
  Definition mut_eqtype_evar_inst := [instance @mut_eqtype_evar].
  Global Existing Instance mut_eqtype_evar_inst | 1000.

  Lemma mut_eqtype_default E L {rt} (ty ty2 : type rt) T :
    ⌜fast_eq_hint (ty = ty2)⌝ ∗ T ⊢ mut_eqtype E L ty ty2 T.
  Proof. iIntros "(<- & $)". iPureIntro. reflexivity. Qed.
  Definition mut_eqtype_default_inst := [instance @mut_eqtype_default].
  Global Existing Instance mut_eqtype_default_inst | 1001.


  (** ** Subtyping instances: [weak_subltype] *)
  (* Instances for [weak_subltype] include:
      - identity
      - folding/unfolding
      - structural lifting
      - lifetime subtyping; below Uniq, we can only replace by equivalences. Thus, we need to prove subtyping in both directions. We may want to have a dedicated judgment for that.
     We, however, cannot trigger [resolve_ghost], as it needs to open stuff up and thus needs steps.

     The instances, especially for folding/unfolding, should use the structure of the second lt (the target) as guidance for incrementally manipulating the first one.
     After making the heads match, structurally descend.
   *)

  Lemma weak_subltype_id E L {rt} (lt : ltype rt) k r T :
    T ⊢ weak_subltype E L k r r lt lt T.
  Proof. iIntros "$" (??) "_ _ $". iApply ltype_incl_refl. Qed.

  Lemma weak_subltype_evar2 E L {rt} (lt1 lt2 : ltype rt) k r1 r2  `{!ContainsProtected lt2} T :
    ⌜lt1 = lt2⌝ ∗ weak_subltype E L k r1 r2 lt1 lt1 T ⊢ weak_subltype E L k r1 r2 lt1 lt2 T.
  Proof. iIntros "(<- & $)". Qed.
  Definition weak_subltype_evar2_inst := [instance @weak_subltype_evar2].
  Global Existing Instance weak_subltype_evar2_inst | 1000.

  (* Escape into the stronger subtyping judgment. Note: should not be used when lt2 is an evar. *)
  Lemma weak_subltype_default E L {rt} (lt1 lt2 : ltype rt) k r1 r2 T :
    ⌜r1 = r2⌝ ∗ mut_subltype E L lt1 lt2 T
    ⊢ weak_subltype E L k r1 r2 lt1 lt2 T.
  Proof.
    iIntros "(<- & %Hsub & HT)" (??) "#CTX #HE HL".
    iPoseProof (full_subltype_acc with "CTX HE HL") as "#Hsub"; first done.
    iFrame. done.
  Qed.
  Definition weak_subltype_default_inst := [instance @weak_subltype_default].
  Global Existing Instance weak_subltype_default_inst | 1001.

  Lemma weak_subltype_ofty_ofty_owned_in E L {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) r1 r2 T :
    (∃ r2', ⌜r2 = #r2'⌝ ∗ weak_subtype E L r1 r2' ty1 ty2 T)
    ⊢ weak_subltype E L (Owned) (#r1) r2 (◁ ty1) (◁ ty2) T.
  Proof.
    iIntros "(%r2' & -> & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    by iApply type_ltype_incl_owned_in.
  Qed.
  Definition weak_subltype_ofty_ofty_owned_in_inst := [instance @weak_subltype_ofty_ofty_owned_in].
  Global Existing Instance weak_subltype_ofty_ofty_owned_in_inst | 10.

  Lemma weak_subltype_ofty_ofty_shared_in E L {rt1 rt2} (ty1 : type rt1) (ty2 : type rt2) κ r1 r2 T :
    (∃ r2', ⌜r2 = #r2'⌝ ∗ weak_subtype E L r1 r2' ty1 ty2 T)
    ⊢ weak_subltype E L (Shared κ) (#r1) (r2) (◁ ty1) (◁ ty2) T.
  Proof.
    iIntros "(%r2' & -> & HT)" (??) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(Hincl & $ & $)".
    by iApply type_ltype_incl_shared_in.
  Qed.
  Definition weak_subltype_ofty_ofty_shared_in_inst := [instance @weak_subltype_ofty_ofty_shared_in].
  Global Existing Instance weak_subltype_ofty_ofty_shared_in_inst | 10.

  (* Note: no similar rule for Uniq -- we can just get strong subtyping through the base lemmas *)

  (** ** Subtyping instances: [mut_eqltype] *)
  Lemma mut_eqltype_base_evar E L {rt} (lt1 lt2 : ltype rt)`{!ContainsProtected lt2}  T :
    ⌜lt1 = lt2⌝ ∗ T
    ⊢ mut_eqltype E L lt1 lt2 T.
  Proof.
    iIntros "(<- & $)". iPureIntro. reflexivity.
  Qed.
  Definition mut_eqltype_base_evar_inst := [instance @mut_eqltype_base_evar].
  Global Existing Instance mut_eqltype_base_evar_inst | 1000.

  Lemma mut_eqltype_default E L {rt} (lt1 lt2 : ltype rt)  T :
    ⌜fast_eq_hint (lt1 = lt2)⌝ ∗ T
    ⊢ mut_eqltype E L lt1 lt2 T.
  Proof.
    iIntros "(<- & $)". iPureIntro. reflexivity.
  Qed.
  Definition mut_eqltype_default_inst := [instance @mut_eqltype_default].
  Global Existing Instance mut_eqltype_default_inst | 1001.

  Lemma mut_eqltype_ofty E L {rt} (ty1 ty2 : type rt) T :
    mut_eqtype E L ty1 ty2 T
    ⊢ mut_eqltype E L (◁ ty1) (◁ ty2) T.
  Proof.
    iIntros "(%Heqt & $)".
    iPureIntro. eapply full_eqtype_eqltype. done.
  Qed.
  Definition mut_eqltype_ofty_inst := [instance @mut_eqltype_ofty].
  Global Existing Instance mut_eqltype_ofty_inst | 5.

  (** ** Subtyping instances: [mut_subltype] *)
  Lemma mut_subltype_id E L {rt} (lt : ltype rt) T :
    T ⊢ mut_subltype E L lt lt T.
  Proof. iIntros "$". iPureIntro. reflexivity. Qed.
  (*Global Instance mut_subltype_refl_inst E L {rt} (lt : ltype rt) : MutSubLtype E L lt lt | 1 :=*)
    (*λ T, i2p (mut_subltype_id E L lt T).*)

  Lemma mut_subltype_base_evar E L {rt} (lt1 lt2 : ltype rt) `{!ContainsProtected lt2} T :
    ⌜lt1 = lt2⌝ ∗ T
    ⊢ mut_subltype E L lt1 lt2 T.
  Proof.
    iIntros "(<- & $)". iPureIntro. reflexivity.
  Qed.
  Definition mut_subltype_base_evar_inst := [instance @mut_subltype_base_evar].
  Global Existing Instance mut_subltype_base_evar_inst | 1000.

  Lemma mut_subltype_default E L {rt} (lt1 lt2 : ltype rt) T :
    mut_eqltype E L lt1 lt2 T
    ⊢ mut_subltype E L lt1 lt2 T.
  Proof.
    iIntros "(%Heq & $)". iPureIntro. by apply full_eqltype_subltype_l.
  Qed.
  Definition mut_subltype_default_inst := [instance @mut_subltype_default].
  Global Existing Instance mut_subltype_default_inst | 1001.

  (** ** Subtyping instances: [owned_subltype_step] *)

  (** ** casts *)
  Lemma cast_ltype_to_type_id E L {rt} (ty : type rt) T :
    T ty ⊢ cast_ltype_to_type E L (◁ ty) T.
  Proof.
    iIntros "HT". iExists ty. iFrame "HT". done.
  Qed.
  Global Instance cast_ltype_to_type_id_inst E L {rt} (ty : type rt) :
    CastLtypeToType E L (◁ ty)%I :=
    λ T, i2p (cast_ltype_to_type_id E L ty T).

  (** ** prove_place_cond *)
  Lemma prove_place_cond_ofty_refl E L bmin {rt} (ty : type rt) T :
    T (mkPUKRes UpdBot opt_place_update_eq_refl opt_place_update_eq_refl) ⊢
    prove_place_cond E L bmin (◁ ty) (◁ ty) T.
  Proof.
    iIntros "HT" (F ?) "#CTX HE $". iExists _. iFrame.
    iSplitR. { iApply upd_bot_min. }
    iSplitR. { iApply typed_place_cond_refl_ofty. }
    done.
  Qed.
  (* high-priority instance for reflexivity *)
  Definition prove_place_cond_ofty_refl_inst := [instance @prove_place_cond_ofty_refl].
  Global Existing Instance prove_place_cond_ofty_refl_inst | 2.

  (* Low priority instances for strong and weak updates *)
  Lemma prove_place_cond_strong_trivial E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) T :
    ⌜ltype_st lt1 = ltype_st lt2⌝ ∗ T (mkPUKRes (allowed:=UpdStrong) UpdStrong I I)
    ⊢ prove_place_cond E L UpdStrong lt1 lt2 T.
  Proof.
    iIntros "(% & HT)". unfold prove_place_cond.
    iIntros (??) "#CTX #HE HL".
    iFrame. done.
  Qed.
  Definition prove_place_cond_strong_trivial_inst := [instance @prove_place_cond_strong_trivial].
  Global Existing Instance prove_place_cond_strong_trivial_inst | 1000.
  Lemma prove_place_cond_weak_trivial E L {rt} (lt1 lt2 : ltype rt)  T :
    ⌜ltype_st lt1 = ltype_st lt2⌝ ∗ T (mkPUKRes (allowed:=UpdWeak) UpdWeak eq_refl eq_refl)
    ⊢ prove_place_cond E L UpdWeak lt1 lt2 T.
  Proof.
    iIntros "(% & HT)". unfold prove_place_cond.
    iIntros (??) "#CTX #HE HL".
    iFrame. done.
  Qed.
  Definition prove_place_cond_weak_trivial_inst := [instance @prove_place_cond_weak_trivial].
  Global Existing Instance prove_place_cond_weak_trivial_inst | 1000.

  (** Lemmas to eliminate BlockedLtype on either side *)
  Lemma prove_place_cond_blocked_r_Uniq E L {rt rt2} (ty : type rt) (lt : ltype rt2) κs κ' T :
    ⌜lctx_place_update_kind_outlives E L (UpdUniq κs) [κ']⌝ ∗ prove_place_cond E L (UpdUniq κs) lt (◁ ty) (λ upd,
      (* [upd] might be too short, before [κ'] *)
      T (mkPUKRes (UpdUniq κs) upd.(puk_res_eq_2) upd.(puk_res_eq_2)))
    ⊢ prove_place_cond E L (UpdUniq κs) lt (BlockedLtype ty κ') T.
  Proof.
    iIntros "(%Hincl & HT)".
    iIntros (F ?) "#CTX HE HL".
    iPoseProof (lctx_place_update_kind_outlives_use with "HE HL") as "#Hincl"; first done.
    iMod ("HT" with "[//] CTX HE HL") as "($ & %upd & #Hincl' & Hcond & %Hst & HT)".
    iExists _. iFrame. simpl.
    iSplitR. { iApply lft_list_incl_refl. }
    rewrite Hst. simp_ltypes. iL.
    destruct upd as [upd ? Heq2]; try done. simpl.
    unfold opt_place_update_eq in Heq2.
    simpl in *. subst rt2.
    iPoseProof (typed_place_cond_incl with "Hincl' Hcond") as "Hcond".
    by iApply typed_place_cond_blocked_r_Uniq.
  Qed.
  Definition prove_place_cond_blocked_r_Uniq_inst := [instance @prove_place_cond_blocked_r_Uniq].
  Global Existing Instance prove_place_cond_blocked_r_Uniq_inst | 5.

  Lemma prove_place_cond_blocked_r_Strong E L {rt rt2} (lt : ltype rt2) (ty : type rt) κ' T :
    prove_place_cond E L UpdStrong lt (◁ ty) (λ upd,
     (* [upd] might be too short, before [κ'] *)
      T (mkPUKRes (UpdStrong) I upd.(puk_res_eq_2))) ⊢
    prove_place_cond E L UpdStrong lt (BlockedLtype ty κ') T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "($ & %upd & #Hincl & Hcond & %Ht & HT)".
    iExists _. iFrame. done.
  Qed.
  Definition prove_place_cond_blocked_r_Strong_inst := [instance @prove_place_cond_blocked_r_Strong].
  Global Existing Instance prove_place_cond_blocked_r_Strong_inst | 5.
  (* no shared lemma *)

  Lemma prove_place_cond_blocked_l E L {rt rt2} (ty : type rt) (lt : ltype rt2) b κ'  T :
    prove_place_cond E L b (◁ ty)%I lt T ⊢
    prove_place_cond E L b (BlockedLtype ty κ') lt T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "($ & (%upd & #Hincl & Hcond & %Hst & T))".
    iExists _. iModIntro. iFrame "∗ #".
    iL. by iApply typed_place_cond_blocked_l.
  Qed.
  Definition prove_place_cond_blocked_l_inst := [instance @prove_place_cond_blocked_l].
  Global Existing Instance prove_place_cond_blocked_l_inst | 5.

  (** Lemmas to eliminate ShrBlockedLtype on either side *)
  Lemma prove_place_cond_shrblocked_r_Uniq E L {rt rt2} (ty : type rt) (lt : ltype rt2) κs κ' T :
    ⌜lctx_place_update_kind_outlives E L (UpdUniq κs) [κ']⌝ ∗ prove_place_cond E L (UpdUniq κs) lt (◁ ty) (λ upd,
      (* [upd] might be too short, before [κ'] *)
      T (mkPUKRes (UpdUniq κs) upd.(puk_res_eq_2) upd.(puk_res_eq_2)))
    ⊢ prove_place_cond E L (UpdUniq κs) lt (ShrBlockedLtype ty κ') T.
  Proof.
    iIntros "(%Hincl & HT)".
    iIntros (F ?) "#CTX HE HL".
    iPoseProof (lctx_place_update_kind_outlives_use with "HE HL") as "#Hincl"; first done.
    iMod ("HT" with "[//] CTX HE HL") as "($ & %upd & #Hincl' & Hcond & %Hst & HT)".
    iExists _. iFrame. simpl.
    iSplitR. { iApply lft_list_incl_refl. }
    rewrite Hst. simp_ltypes. iL.
    destruct upd as [upd ? Heq2]; try done. simpl.
    unfold opt_place_update_eq in Heq2.
    simpl in *. subst rt2.
    iPoseProof (typed_place_cond_incl with "Hincl' Hcond") as "Hcond".
    by iApply typed_place_cond_shrblocked_r_Uniq.
  Qed.
  Definition prove_place_cond_shrblocked_r_Uniq_inst := [instance @prove_place_cond_shrblocked_r_Uniq].
  Global Existing Instance prove_place_cond_shrblocked_r_Uniq_inst | 5.

  Lemma prove_place_cond_shrblocked_r_Strong E L {rt rt2} (lt : ltype rt2) (ty : type rt) κ' T :
    prove_place_cond E L UpdStrong lt (◁ ty) (λ upd,
     (* [upd] might be too short, before [κ'] *)
      T (mkPUKRes (UpdStrong) I upd.(puk_res_eq_2))) ⊢
    prove_place_cond E L UpdStrong lt (ShrBlockedLtype ty κ') T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "($ & %upd & #Hincl & Hcond & %Ht & HT)".
    iExists _. iFrame. done.
  Qed.
  Definition prove_place_cond_shrblocked_r_Strong_inst := [instance @prove_place_cond_shrblocked_r_Strong].
  Global Existing Instance prove_place_cond_shrblocked_r_Strong_inst | 5.
  (* no shared lemma *)

  Lemma prove_place_cond_shrblocked_l E L {rt rt2} (ty : type rt) (lt : ltype rt2) b κ'  T :
    prove_place_cond E L b (◁ ty)%I lt T ⊢
    prove_place_cond E L b (ShrBlockedLtype ty κ') lt T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "($ & (%upd & #Hincl & Hcond & %Hst & T))".
    iExists _. iModIntro. iFrame "∗ #".
    iL. by iApply typed_place_cond_shrblocked_l.
  Qed.
  Definition prove_place_cond_shrblocked_l_inst := [instance @prove_place_cond_shrblocked_l].
  Global Existing Instance prove_place_cond_shrblocked_l_inst | 5.

  (** Lemmas to eliminate Coreable on either side *)
  Lemma prove_place_cond_coreable_r_Strong E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κs T :
    prove_place_cond E L UpdStrong lt1 lt2 (λ upd,
      (T (mkPUKRes (allowed:=UpdStrong) UpdStrong I I))) ⊢
    prove_place_cond E L UpdStrong lt1 (CoreableLtype κs lt2) T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "($ & %upd & ? & Hcond & % & HT)".
    iExists _. iFrame. done.
  Qed.
  Definition prove_place_cond_coreable_r_Strong_inst := [instance @prove_place_cond_coreable_r_Strong].
  Global Existing Instance prove_place_cond_coreable_r_Strong_inst | 5.

  (* κ needs to outlive all the κ' ∈ κs *)
  Lemma prove_place_cond_coreable_r_Uniq E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κs κ T :
    ⌜lctx_place_update_kind_outlives E L (UpdUniq κ) κs⌝ ∗
      prove_place_cond E L (UpdUniq κ) lt1 lt2 (λ upd,
      (* [upd] might be too short, before [κ'] *)
      T (mkPUKRes (UpdUniq κ) upd.(puk_res_eq_2) upd.(puk_res_eq_2)))
    ⊢ prove_place_cond E L (UpdUniq κ) lt1 (CoreableLtype κs lt2) T.
  Proof.
    iIntros "(%Hal & HT)". iIntros (F ?) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(HL & %upd & #Hincl & Hcond & % & HT)".
    iPoseProof (lctx_place_update_kind_outlives_use with "HE HL") as "#Hal".
    { apply Hal. }
    iFrame "HL". iExists _. iFrame. simpl.
    iSplitR. { iApply lft_list_incl_refl. }
    destruct upd as [upd Heq1 Heq2]; try done. simpl in *.
    unfold opt_place_update_eq in Heq2. simpl in *. subst rt2.
    destruct upd; try done. iL.
    iPoseProof (typed_place_cond_incl with "Hincl Hcond") as "Hcond".
    by iApply typed_place_cond_coreable_r_Uniq.
  Qed.
  Definition prove_place_cond_coreable_r_Uniq_inst := [instance @prove_place_cond_coreable_r_Uniq].
  Global Existing Instance prove_place_cond_coreable_r_Uniq_inst | 5.

  Lemma prove_place_cond_coreable_l E L {rt1 rt2} (lt1 : ltype rt1) (lt2 : ltype rt2) κs b T :
    prove_place_cond E L b lt1 lt2 T
    ⊢ prove_place_cond E L b (CoreableLtype κs lt1) lt2 T.
  Proof.
    iIntros "HT". iIntros (F ?) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(HL & %upd & Hincl & Hcond & % & HT)".
    iFrame. iL.
    by iApply typed_place_cond_coreable_l.
  Qed.
  Definition prove_place_cond_coreable_l_inst := [instance @prove_place_cond_coreable_l].
  Global Existing Instance prove_place_cond_coreable_l_inst | 5.

  (* NOTE: unfolding lemmas should have lower priority than the primitive ones. *)

  (** find obs *)
  Import EqNotations.
  Lemma find_observation_direct (rt : RT) γ (T : find_observation_cont_t rt) :
    find_in_context (FindOptGvarPobs γ) (λ res,
      match res with
      | inr _ => find_observation rt γ FindObsModeRel T
      | inl (existT rt' r) => ∃ (Heq : rt' = rt), T (Some (#(rew Heq in r)))
      end)%I
    ⊢ find_observation rt γ FindObsModeDirect T.
  Proof.
    iDestruct 1 as ([[rt' r] | ]) "(Hobs & HT)"; simpl.
    - iDestruct "HT" as (->) "HT". iIntros (??). iModIntro.
      iLeft. eauto with iFrame.
    - iIntros (??). by iApply "HT".
  Qed.
  Definition find_observation_direct_inst := [instance @find_observation_direct].
  Global Existing Instance find_observation_direct_inst.

  Lemma find_observation_rel (rt : RT) γ (T : find_observation_cont_t rt) :
    find_in_context (FindOptGvarRelEq γ) (λ res,
      match res with
      | inr _ => T None
      | inl (rt', γ') =>
          ∃ (Heq : RT_rt rt' = RT_rt rt), T (Some (PlaceGhost γ'))
      end)%I
    ⊢ find_observation rt γ FindObsModeRel T.
  Proof.
    iDestruct 1 as ([[rt' γ'] | ]) "(Hobs & HT)"; simpl.
    - iDestruct "HT" as (Heq) "HT".
      unfold find_observation, find_observation_result.
      iIntros (??). rewrite /RelEq. iDestruct "Hobs" as "(%v1 & %v2 & ?)".
      iLeft. iExists (👻 γ'). iFrame.
      iExists (rew [id] Heq in v1).
      iExists (rew [id] Heq in v2).
      destruct Heq. done.
    - iIntros (??). iRight. done.
  Qed.
  Definition find_observation_rel_inst := [instance @find_observation_rel].
  Global Existing Instance find_observation_rel_inst.

  (** find delayed observation *)
  Lemma find_delayed_observation_direct E L (rt : RT) γ κ (T : find_delayed_observation_cont_t rt) :
    find_in_context (FindOptInheritGvarPobs γ) (λ res,
      match res with
      | inr _ => find_delayed_observation E L rt γ FindObsModeRel κ T
      | inl (κs, existT rt' r) =>
          li_tactic (check_lctx_lft_incl_goal E L (lft_intersect_list κs) κ) (λ b,
            if b then
              ∃ (Heq : rt' = rt), T (Some (#(rew Heq in r)))
            else False)
      end)%I
    ⊢ find_delayed_observation E L rt γ FindObsModeDirect κ T.
  Proof.
    iDestruct 1 as ([[κs [rt' r]] | ]) "(Hobs & HT)"; simpl.
    - unfold check_lctx_lft_incl_goal.
      iDestruct "HT" as (b) "(%Hincl & HT)". iIntros (??) "HE HL".
      destruct b; last done.
      iDestruct "HT" as "(%Heq & HT)".
      iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HLcl)".
      iPoseProof (Hincl with "HL HE") as "#Hincl".
      iPoseProof ("HLcl" with "HL") as "HL".
      iFrame "HL".
      iLeft. unfold find_observation_result. destruct Heq.
      iPoseProof (Inherit_mono with "[] Hobs") as "Hobs"; last by iFrame.
      simpl. rewrite right_id. done.
    - iIntros (??). by iApply "HT".
  Qed.
  Definition find_delayed_observation_direct_inst := [instance @find_delayed_observation_direct].
  Global Existing Instance find_delayed_observation_direct_inst.

  Lemma find_delayed_observation_rel E L (rt : RT) γ κ (T : find_observation_cont_t rt) :
    find_in_context (FindOptInheritGvarRelEq γ) (λ res,
      match res with
      | inr _ => T None
      | inl (κs, rt', γ') =>
          li_tactic (check_lctx_lft_incl_goal E L (lft_intersect_list κs) κ) (λ b,
            if b then
              ∃ (Heq : RT_rt rt' = RT_rt rt), T (Some (PlaceGhost γ'))
            else False)
      end)%I
    ⊢ find_delayed_observation E L rt γ FindObsModeRel κ T.
  Proof.
    iDestruct 1 as ([a | ]) "(Hobs & HT)"; simpl.
    - destruct a as ((κs & rt') & γ').
      unfold check_lctx_lft_incl_goal.
      iDestruct "HT" as (b) "(%Hincl & HT)". iIntros (??) "HE HL".
      destruct b; last done.
      iDestruct "HT" as "(%Heq & HT)".
      iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HLcl)".
      iPoseProof (Hincl with "HL HE") as "#Hincl".
      iPoseProof ("HLcl" with "HL") as "HL".
      iFrame "HL".
      iLeft. unfold find_observation_result.
      iExists (👻 γ'). iFrame.
      iPoseProof (Inherit_mono _ [κ] with "[] Hobs") as "Hobs".
      { simpl. rewrite right_id. done. }
      iApply (Inherit_update with "[] Hobs").
      rewrite /RelEq.
      iIntros (?) "(%v1 & %v2 & Ha)". iModIntro.
      iExists (rew [id] Heq in v1).
      iExists (rew [id] Heq in v2).
      destruct Heq. done.
    - iIntros (??) "HE HL". iModIntro. iFrame.
  Qed.
  Definition find_delayed_observation_rel_inst := [instance @find_delayed_observation_rel].
  Global Existing Instance find_delayed_observation_rel_inst.


  (** ** resolve_ghost *)
  (* One note: these instances do not descend recursively -- that is the task of the stratify_ltype call that is triggering the resolution. resolve_ghost instances should always resolve at top-level, or at the level of atoms of stratify_ltype's traversal (in case of user-defined types) *)
  Import EqNotations.

  (* a trivial low-priority instance, in case no other instance triggers.
    In particular, we should also make sure that custom instances for user-defined types get priority. *)
  Lemma resolve_ghost_id {rt} π E L l (lt : ltype rt) rm lb k r (T : llctx → place_rfn rt → iProp Σ → bool → iProp Σ) :
    match rm with
    | ResolveAll =>
        match r with
        | PlaceIn _ => T L r True false
        | _ => False
        end
    | ResolveTry =>
        T L r True false
    end
    ⊢ resolve_ghost π E L rm lb l lt k r T.
  Proof.
    iIntros "HT" (F ??) "#CTX #HE HL Hl".
    destruct rm.
    - destruct r; last done.
      iExists L, _, True%I, _. iFrame.
      iApply maybe_logical_step_intro. by iFrame.
    - destruct r.
      + iExists L, _, True%I, _. iFrame. iApply maybe_logical_step_intro. by iFrame.
      + iExists L, _, True%I, _. iFrame. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Global Instance resolve_ghost_id_inst {rt} π E L l (lt : ltype rt) rm lb k r :
    ResolveGhost π E L rm lb l lt k r | 200 := λ T, i2p (resolve_ghost_id π E L l lt rm lb k r T).

  Lemma resolve_ghost_ofty {rt} π E L l (ty : type rt) γ rm lb b T :
    find_observation rt γ FindObsModeDirect (λ or,
      match or with
      | None =>
          ⌜fast_eq_hint (rm = ResolveTry)⌝ ∗ T L (PlaceGhost γ) True false
      | Some r =>
          (* try again in case we should descend into the type or we have still got a PlaceGhost *)
          resolve_ghost π E L rm lb l (◁ ty)%I b r T
      end)
    ⊢ resolve_ghost π E L rm lb l (◁ ty)%I b (PlaceGhost γ) T.
  Proof.
    iIntros "HT". iIntros (F ??) "#CTX #HE HL Hl".
    iMod ("HT" with "[//]") as "HT". iDestruct "HT" as "[(%r & Hobs & HT) | (-> & HT)]".
    - iPoseProof (ltype_own_ofty_use_obs with "Hl Hobs") as "Hl".
      iMod ("HT" with "[] [] CTX HE HL [$]") as "Ha"; [done.. | ].
      done.
    - iExists L, _, True%I, _. iFrame. iApply maybe_logical_step_intro. eauto with iFrame.
  Qed.
  Definition resolve_ghost_ofty_inst := [instance @resolve_ghost_ofty].
  Global Existing Instance resolve_ghost_ofty_inst | 7.

  (* Low-priority default instance. Can be overridden in case we want to descend into the type for deeper resolution, for instance for ADTs. See the instances in [existentials.v]. *)
  Lemma resolve_ghost_ofty_default {rt} (ty : type rt) π E L l r rm lb bk T :
    T L (# r) True false
    ⊢ resolve_ghost π E L rm lb l (◁ ty)%I bk (# r) T.
  Proof.
    iIntros "HT".
    iIntros (???) "CTX HE HL Hl". iFrame.
    iModIntro. iApply maybe_logical_step_intro. by iFrame.
  Qed.
  Definition resolve_ghost_ofty_default_inst := [instance @resolve_ghost_ofty_default].
  Global Existing Instance resolve_ghost_ofty_default_inst | 1000.

  (** Nice lemma: we can also partially resolve on [BlockedLtype] *)
  Lemma blocked_ltype_resolve_partially {rt} (ty : type rt) π bk l κ γ r :
    Inherit [κ] (find_observation_result γ r) -∗
    l ◁ₗ[π, bk] PlaceGhost γ @ BlockedLtype ty κ -∗
    l ◁ₗ[π, bk] r @ BlockedLtype ty κ.
  Proof.
    iIntros "Hinh".
    rewrite !ltype_own_blocked_unfold/blocked_lty_own.
    destruct bk.
    - iIntros "(%ly & %Hst & %Hly & Hsc & Hlb & Hb)".
      iFrame "Hlb Hsc". iR. iR.
      iIntros "#Hdead".
      unfold Inherit. simpl. rewrite right_id.
      iMod ("Hinh" with "[] Hdead") as "HP"; first done.
      iMod ("Hb" with "Hdead") as "(%r' & Hrfn & Hb)".
      iPoseProof (place_rfn_interp_owned_find_observation with "Hrfn HP") as "Hrfn".
      by iFrame.
    - iIntros "(%ly & %Hst & %Hly & Hsc & Hlb & Hb)".
      done.
    - iIntros "(%ly & %Hst & %Hly & Hsc & Hlb & Hb & Hcred)".
      iFrame "Hlb Hsc Hcred". iR. iR.
      iIntros "#Hdead".
      unfold Inherit. simpl. rewrite right_id.
      iMod ("Hinh" with "[] Hdead") as "HP"; first done.
      iMod ("Hb" with "Hdead") as "(Hrfn & Hb)".
      iPoseProof (place_rfn_interp_mut_find_observation with "Hrfn HP") as "Hrfn".
      by iFrame.
  Qed.
  Lemma resolve_ghost_blocked {rt} π E L rm lb l (ty : type rt) κ bk γ T :
    find_observation rt γ FindObsModeDirect (λ o,
    match o with
    | Some r =>
        resolve_ghost π E L rm lb l (BlockedLtype ty κ) bk r T
    | None =>
      find_delayed_observation E L rt γ FindObsModeDirect κ (λ o,
        match o with
        | Some r =>
            resolve_ghost π E L rm lb l (BlockedLtype ty κ) bk r T
        | None =>
            T L (PlaceGhost γ) True false
        end)
    end)
    ⊢ resolve_ghost π E L rm lb l (BlockedLtype ty κ) bk (PlaceGhost γ) T.
  Proof.
    iIntros "HT". iIntros (???) "#CTX #HE HL Hl".
    iMod ("HT" with "[]") as "Ha"; first done.
    iDestruct "Ha" as "[(% & Hres & HT) | HT]".
    - iPoseProof (blocked_ltype_resolve_partially with "[Hres] Hl") as "Hl".
      { rewrite /Inherit. iIntros (??) "_". by iFrame. }
      by iApply ("HT" with "[] [] CTX HE HL Hl").
    - iMod ("HT" with "[] HE HL") as "(HT & HL)"; first done.
      iDestruct "HT" as "[(%r & Hinh & HT) | HT]"; first last.
      { iFrame. iApply maybe_logical_step_intro. by iFrame. }
      iPoseProof (blocked_ltype_resolve_partially with "Hinh Hl") as "Hl".
      by iApply ("HT" with "[] [] CTX HE HL Hl").
  Qed.
  Definition resolve_ghost_blocked_inst := [instance @resolve_ghost_blocked].
  Global Existing Instance resolve_ghost_blocked_inst.

  (** ** ltype stratification *)
  (* TODO change the ResolveTry and also make it a parameter of stratify *)

  (* when we recursively want to descend, we cannot let the resolution use the logical step *)
  Lemma stratify_ltype_resolve_ghost_rec {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) b r T :
    resolve_ghost π E L ResolveTry false l lt b r (λ L1 r R progress,
      if progress then
      stratify_ltype π E L1 mu mdu ma ml l lt r b
        (λ L2 R' rt' lt' r', T L2 (R ∗ R') rt' lt' r')
      else
        (* otherwise treat this as a leaf *)
        R -∗ stratify_ltype_post_hook π E L1 ml l lt r b T)
    ⊢ stratify_ltype π E L mu mdu ma ml l lt r b T.
  Proof.
    iIntros "Hres". iIntros (????) "#CTX #HE HL Hl".
    iMod ("Hres" with "[] [] CTX HE HL Hl") as "(%L1 & %r1 & %R & %prog & >(Hl & HR) & HL & HP)"; [done.. | ].
    destruct prog.
    - iPoseProof ("HP" with "[//] [//] [//] CTX HE HL Hl") as ">Hb".
      iDestruct "Hb" as "(%L2 & %R' & %rt' & %lt' & %r' & HL & Hcond & Hb & HT)".
      iModIntro. iExists L2, _, rt', lt', r'. iFrame "Hcond HT HL".
      iApply (logical_step_wand with "Hb"). iIntros "($ & $)". done.
    - by iApply (stratify_ltype_id _ _ _ mu mdu ma with "(HP HR) [//] [//] [//] CTX HE HL").
  Qed.
  (* at a leaf, we can use the logical step to do the resolution -- this allows to descend deeper into the type, which is useful for custom user-defined types *)
  Lemma stratify_ltype_resolve_ghost_leaf {rt} π E L mu mdu ma {M} (ml : M) rm l (lt : ltype rt) b r T :
    resolve_ghost π E L rm true l lt b r (λ L1 r R progress, T L1 R _ lt r)
    ⊢ stratify_ltype π E L mu mdu ma ml l lt r b T.
  Proof.
    iIntros "Hres". iIntros (????) "#CTX #HE HL Hl".
    iMod ("Hres" with "[] [] CTX HE HL Hl") as "(%L1 & %r1 & %R & %prog & Hl & HL & HR)"; [done.. | ].
    simpl. iModIntro. iExists L1, _, _, lt, r1.
    iFrame. done.
  Qed.

  (* This should have a lower priority than the leaf instances we call for individual [ml] -- those should instead use [stratify_ltype_resolve_ghost_leaf]. *)
  Global Instance stratify_ltype_resolve_ghost_inst {rt} π E L mu mdu ma {M} (ml : M) l (lt : ltype rt) b γ :
    StratifyLtype π E L mu mdu ma ml l lt (PlaceGhost γ) b | 100 := λ T, i2p (stratify_ltype_resolve_ghost_rec π E L mu mdu ma ml l lt b (PlaceGhost γ) T).

  Lemma stratify_ltype_blocked {rt} π E L mu mdu ma {M} (ml : M) l (ty : type rt) κ r b `{!StratifyLtypeShouldUnblock ml} T :
    resolve_ghost π E L ResolveTry false l (BlockedLtype ty κ) b r (λ L1 r R progress,
      if progress then
        stratify_ltype π E L1 mu mdu ma ml l (BlockedLtype ty κ) r b
          (λ L2 R' rt' lt' r', T L2 (R ∗ R') rt' lt' r')
      else R -∗
      find_in_context (FindOptLftDead κ) (λ found,
        if found then stratify_ltype π E L1 mu mdu ma ml l (◁ ty)%I r b T
        else stratify_ltype_post_hook π E L1 ml l (BlockedLtype ty κ) r b T))
    ⊢ stratify_ltype π E L mu mdu ma ml l (BlockedLtype ty κ) r b T.
  Proof.
    iIntros "HT". iIntros (????) "#CTX #HE HL Hl".
    iMod ("HT" with "[] [] CTX HE HL Hl") as "(%L1 & %r1 & %R & %prog & >(Hl & HR) & HL & HP)"; [done.. | ].
    destruct prog.
    - iPoseProof ("HP" with "[//] [//] [//] CTX HE HL Hl") as ">Hb".
      iDestruct "Hb" as "(%L2 & %R' & %rt' & %lt' & %r' & HL & Hcond & Hb & HT)".
      iModIntro. iExists L2, _, rt', lt', r'. iFrame "Hcond HT HL".
      iApply (logical_step_wand with "Hb"). iIntros "($ & $)". done.
    - rewrite /FindOptLftDead.
      iSpecialize ("HP" with "HR").
      iDestruct "HP" as "(%found & Hdead & Hp)". destruct found.
      + iMod (unblock_blocked with "Hdead Hl") as "Hl"; first done.
        iPoseProof ("Hp" with "[//] [//] [//] [//] HE HL Hl") as ">Hb".
        iDestruct "Hb" as "(%L' & %R2 & %rt' & %lt' & %r' & Hl & Hstep & HT)".
        iModIntro. iExists L', _, rt', lt', r'. iFrame.
      + iApply (stratify_ltype_id _ _ _ mu mdu ma with "Hp [] [] [] [] HE HL"); done.
  Qed.
  Definition stratify_ltype_blocked_inst := [instance @stratify_ltype_blocked].
  Global Existing Instance stratify_ltype_blocked_inst | 5.

  Lemma stratify_ltype_coreable {rt} π E L mu mdu ma {M} (ml : M) l (lt_full lt_full' : ltype rt) κs r b `{Hsimp: !SimpLtype (ltype_core lt_full) lt_full'} `{!StratifyLtypeShouldUnblock ml} T :
    resolve_ghost π E L ResolveTry false l (CoreableLtype κs lt_full) b r (λ L1 r R progress,
      if progress then
        stratify_ltype π E L1 mu mdu ma ml l (CoreableLtype κs lt_full) r b
          (λ L2 R' rt' lt' r', T L2 (R ∗ R') rt' lt' r')
      (* TODO also make optional *)
      else R -∗ lft_dead_list κs ∗ stratify_ltype π E L1 mu mdu ma ml l (lt_full')%I r b T)
    ⊢ stratify_ltype π E L mu mdu ma ml l (CoreableLtype κs lt_full) r b T.
  Proof.
    iIntros "HT". iIntros (????) "#CTX #HE HL Hl".
    iMod ("HT" with "[] [] CTX HE HL Hl") as "(%L1 & %r1 & %R & %prog & >(Hl & HR) & HL & HP)"; [done.. | ].
    destruct prog.
    - iPoseProof ("HP" with "[//] [//] [//] CTX HE HL Hl") as ">Hb".
      iDestruct "Hb" as "(%L2 & %R' & %rt' & %lt' & %r' & HL & Hcond & Hb & HT)".
      iModIntro. iExists L2, _, rt', lt', r'. iFrame "Hcond HT HL".
      iApply (logical_step_wand with "Hb"). iIntros "($ & $)". done.
    - iSpecialize ("HP" with "HR").
      iDestruct "HP" as "(Hdead & Hp)".
      iMod (unblock_coreable with "Hdead Hl") as "Hl"; first done.
      destruct Hsimp. subst.
      iPoseProof ("Hp" with "[//] [//] [//] [//] HE HL Hl") as ">Hb".
      iDestruct "Hb" as "(%L' & %R2 & %rt' & %lt' & %r' & Hl & %Hst & HT)".
      iModIntro. iExists L', _, rt', lt', r'. iFrame.
      iPureIntro. rewrite -Hst ltype_core_syn_type_eq. by simp_ltypes.
  Qed.
  Definition stratify_ltype_coreable_inst := [instance @stratify_ltype_coreable].
  Global Existing Instance stratify_ltype_coreable_inst | 5.

  Lemma stratify_ltype_shrblocked {rt} π E L mu mdu ma {M} (ml : M) l (ty : type rt) κ r b `{!StratifyLtypeShouldUnblock ml} T :
    resolve_ghost π E L ResolveTry false l (ShrBlockedLtype ty κ) b r (λ L1 r R progress,
      if progress then
        stratify_ltype π E L1 mu mdu ma ml l (ShrBlockedLtype ty κ) r b
          (λ L2 R' rt' lt' r', T L2 (R ∗ R') rt' lt' r')
      else R -∗
      find_in_context (FindOptLftDead κ) (λ found,
        if found then stratify_ltype π E L1 mu mdu ma ml l (◁ ty)%I r b T
        else stratify_ltype_post_hook π E L1 ml l (ShrBlockedLtype ty κ) r b T))
    ⊢ stratify_ltype π E L mu mdu ma ml l (ShrBlockedLtype ty κ) r b T.
  Proof.
    iIntros "HT". iIntros (????) "#CTX #HE HL Hl".
    iMod ("HT" with "[] [] CTX HE HL Hl") as "(%L1 & %r1 & %R & %prog & >(Hl & HR) & HL & HP)"; [done.. | ].
    destruct prog.
    - iPoseProof ("HP" with "[//] [//] [//] CTX HE HL Hl") as ">Hb".
      iDestruct "Hb" as "(%L2 & %R' & %rt' & %lt' & %r' & HL & Hcond & Hb & HT)".
      iModIntro. iExists L2, _, rt', lt', r'. iFrame "Hcond HT HL".
      iApply (logical_step_wand with "Hb"). iIntros "($ & $)". done.
    - rewrite /FindOptLftDead.
      iSpecialize ("HP" with "HR").
      iDestruct "HP" as "(%found & Hdead & Hp)". destruct found.
      + iMod (unblock_shrblocked with "Hdead Hl") as "Hl"; first done.
        iPoseProof ("Hp" with "[//] [//] [//] [//] HE HL Hl") as ">Hb".
        iDestruct "Hb" as "(%L' & %R2 & %rt' & %lt' & %r' & Hl & Hstep & HT)".
        iModIntro. iExists L', _, rt', lt', r'. iFrame.
      + iApply (stratify_ltype_id _ _ _ mu mdu ma with "Hp [] [] [] [] HE HL"); done.
  Qed.
  Definition stratify_ltype_shrblocked_inst := [instance @stratify_ltype_shrblocked].
  Global Existing Instance stratify_ltype_shrblocked_inst | 5.

  (* NOTE: we make the assumption that, even for fully-owned places, we want to keep the invariant structure, and not just unfold it completely and forget about the invariants. This is why we keep it open when the refinement type is different, even though we could in principle also close it to any lt_cur'.

    Is there a better criterion for this than the refinement type?
    - currently, prove_place_cond requires the refinement type to be the same, even for Owned.
    - for some of the subtyping we may want to allow the subtyping to actually be heterogeneous.

    Points in the design space:
    - [aggressive] just fold every time we can, by always proving a subtyping.
    - [aggressive unless Owned] fold every time as long as the place cond is provable.
        + in particular: fold if we can get back a lifetime token.
    - [relaxed]
    -

    Some thoughts on stuff that would be good:
    - make stratification more syntax-guided, i.e. have a "goal" ltype?
      + this would make the behavior when we moved stuff out beforehand much more predictable, eg. for value_t: don't just have a general rule for stratifying value every time, but only when we actually want to have something there.
  *)


  Lemma stratify_ltype_opened_Owned {M} (ml : M) {rt_cur rt_inner rt_full} π E L mu mdu ma l
      (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
      (Cpre Cpost : rt_inner → rt_full → iProp Σ) r `{!StratifyLtypeShouldCloseInv ml Owned} (T : stratify_ltype_cont_t) :
    stratify_ltype π E L mu mdu ma ml l lt_cur r (Owned) (λ L' R rt_cur' lt_cur' (r' : place_rfn rt_cur'),
      if decide (ma = StratNoRefold)
        then (* keep it open *)
          T L' R _ (OpenedLtype lt_cur' lt_inner lt_full Cpre Cpost) r'
        else
          trigger_tc (SimpLtype (ltype_core lt_cur')) (λ lt_cur'',
          (* fold the invariant *)
          ∃ ri,
            (* show that the core of lt_cur' is a subtype of lt_inner and then fold to lt_full *)
            weak_subltype E L' (Owned) (r') (#ri) (lt_cur'') lt_inner (
              (* re-establish the invariant *)
              ∃ rf, prove_with_subtype E L' true ProveWithStratify (Cpre ri rf) (λ L'' κs R2,
              (* either fold to coreable, or to the core of lt_full *)
              match ltype_blocked_lfts lt_cur', κs with
              | [], [] =>
                    trigger_tc (SimpLtype (ltype_core lt_full)) (λ lt_full',
                    (T L'' (Cpost ri rf ∗ R2 ∗ R) rt_full lt_full' (#rf)))
              | κs', _ =>
                    (T L'' (Cpost ri rf ∗ R2 ∗ R) rt_full (CoreableLtype (κs' ++ κs) lt_full) (#rf))
              end))))
    ⊢ stratify_ltype π E L mu mdu ma ml l (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) r (Owned) T.
  Proof.
    iIntros "Hstrat". iIntros (F ???) "#CTX #HE HL Hl".
    rewrite ltype_own_opened_unfold /opened_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hlb & %Hst1 & %Hst2 & Hl & Hcl)".
    iMod ("Hstrat" with "[//] [//] [//] CTX HE HL Hl") as "(%L2 & %R & %rt_cur' & %lt_cur' & %r' & HL & %Hst & Hstep & HT)".
    destruct (decide (ma = StratNoRefold)) as [-> | ].
    - (* don't fold *)
      iModIntro.
      iExists _, _, _, _, _. iFrame.
      iSplitR. { iPureIntro. simp_ltypes. done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro.
      iIntros "(Hl & $)".
      rewrite ltype_own_opened_unfold /opened_ltype_own.
      iExists ly. iFrame.
      rewrite -Hst.
      iSplitR. { done. }
      iSplitR; first done. iSplitR; first done.
      iSplitR; first done. done.
    - (* fold it again *)
      iDestruct "HT" as "(%lt_cur'' & %Heq & HT)". destruct Heq as [<-].
      iDestruct "HT" as "(%ri & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Hincl & HL & %rf & HT)".
      iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L3 & %κs & %R2 & Hstep' & HL & HT)".
      iPoseProof (imp_unblockable_blocked_dead lt_cur') as "(_ & #Hb)".
      set (κs' := ltype_blocked_lfts lt_cur').
      destruct (decide (κs = [] ∧ κs' = [])) as [[-> ->] | ].
      + iDestruct "HT" as "(% & %Heq & HT)". destruct Heq as [<-].
        iExists L3, _, _, _, _. iFrame.
        iSplitR. { iPureIntro. rewrite ltype_core_syn_type_eq. rewrite -Hst2 -Hst1 //. }
        iApply logical_step_fupd.
        iApply (logical_step_compose with "Hstep").
        iPoseProof (logical_step_mask_mono _ F with "Hcl") as "Hcl"; first done.
        iApply (logical_step_compose with "Hcl").
        iApply (logical_step_compose with "Hstep'").
        iApply logical_step_intro.
        iIntros "!> (Hpre & $) Hcl (Hl & $)".
        iPoseProof ("Hb" with "[] Hl") as "Hl". { by iApply big_sepL_nil. }
        iMod (fupd_mask_mono with "Hl") as "Hl"; first done.
        rewrite ltype_own_core_equiv.
        iMod (ltype_incl_use with "Hincl Hl") as "Hl"; first done.
        simpl.
        iPoseProof ("Hcl" with "Hpre") as "(Hpost & Hvs')".
        iMod (fupd_mask_mono with "(Hvs' [] Hl)") as "Ha"; first done.
        { by iApply lft_dead_list_nil. }
        rewrite ltype_own_core_equiv. by iFrame.
      + iAssert (T L3 (Cpost ri rf ∗ R2 ∗ R) rt_full (CoreableLtype (κs' ++ κs) lt_full) #rf)%I with "[HT]" as "HT".
        { destruct κs, κs'; naive_solver. }
        iExists L3, _, _, _, _. iFrame.
        iSplitR. { iPureIntro.
          simp_ltypes. rewrite -Hst2 -Hst1. done. }
        iApply logical_step_fupd.
        iApply (logical_step_compose with "Hstep").
        iPoseProof (logical_step_mask_mono _ F with "Hcl") as "Hcl"; first done.
        iApply (logical_step_compose with "Hcl").
        iApply (logical_step_compose with "Hstep'").
        iApply logical_step_intro.
        iIntros "!> (Hpre & $) Hcl (Hl & $)".
        rewrite ltype_own_coreable_unfold /coreable_ltype_own.
        iPoseProof ("Hcl" with "Hpre") as "($ & Hvs')".
        iModIntro.
        iExists ly.
        iSplitR. { rewrite -Hst2 -Hst1. done. }
        iSplitR; first done. iSplitR; first done.
        iIntros "Hdead".
        rewrite lft_dead_list_app. iDestruct "Hdead" as "(Hdead' & Hdead)".
        (* unblock lt_cur' *)
        iPoseProof (imp_unblockable_blocked_dead lt_cur') as "(_ & #Hub)".
        iMod ("Hub" with "Hdead' Hl") as "Hl".
        (* shift to lt_inner *)
        rewrite !ltype_own_core_equiv.
        iMod (ltype_incl_use with "Hincl Hl") as "Hl"; first done.
        (* shift to the core of lt_full *)
        iMod ("Hvs'" with "Hdead Hl") as "Hl".
        eauto.
  Qed.
  Definition stratify_ltype_opened_Owned_inst := [instance @stratify_ltype_opened_Owned].
  Global Existing Instance stratify_ltype_opened_Owned_inst.

  (* NOTE what happens with the inclusion sidecondition for the κs when we shorten the outer reference?
     - we should not shorten after unfolding (that also likely doesn't work with OpenedLtype -- we cannot arbitrarily modify the lt_inner/lt_full)
     - if we are borrowing at a lifetime which doesn't satisfy this at the borrow time, that is a bug, as we are violating the contract of the outer reference.
     So: this sidecondition does not restrict us in any way. *)
  Lemma stratify_ltype_opened_Uniq {M} (ml : M) {rt_cur rt_inner rt_full} π E L mu mdu ma l
      (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full)
      (Cpre Cpost : rt_inner → rt_full → iProp Σ) r κ γ `{!StratifyLtypeShouldCloseInv ml (Uniq κ γ) } T :
    stratify_ltype π E L mu mdu ma ml l lt_cur r (Owned) (λ L' R rt_cur' lt_cur' (r' : place_rfn rt_cur'),
      if decide (ma = StratNoRefold)
        then (* keep it open *)
          T L' R _ (OpenedLtype lt_cur' lt_inner lt_full Cpre Cpost) r'
        else
          (* fold the invariant *)
          ∃ ri,
            (* show that lt_cur' is a subtype of lt_inner and then fold to lt_full *)
            weak_subltype E L' (Owned) (r') (#ri) (lt_cur') lt_inner (
              (* re-establish the invariant *)
              ∃ rf,
              prove_with_subtype E L' true ProveWithStratify (Cpre ri rf) (λ L'' κs R2,
              (* either fold to coreable, or to the core of lt_full *)
              match κs, ltype_blocked_lfts lt_cur' with
              | [], [] =>
                    trigger_tc (SimpLtype (ltype_core lt_full)) (λ lt_full',
                    (T L'' (Cpost ri rf ∗ R2 ∗ R) rt_full lt_full' (#rf)))
              | _, κs' =>
                    (* inclusion sidecondition: require that all the blocked stuff ends before κ *)
                    ([∗ list] κ' ∈ κs ++ κs', ⌜lctx_lft_incl E L'' κ' κ⌝) ∗
                    (T L'' (Cpost ri rf ∗ R2 ∗ R) rt_full (CoreableLtype (κs ++ κs') lt_full) (#rf))
              end)))
    ⊢ stratify_ltype π E L mu mdu ma ml l (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) r (Uniq κ γ) T.
  Proof.
    iIntros "Hstrat". iIntros (F ???) "#CTX #HE HL Hl".
    rewrite ltype_own_opened_unfold /opened_ltype_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hlb & %Hst1 & %Hst2 & Hl & Hcl)".
    iMod ("Hstrat" with "[//] [//] [//] CTX HE HL Hl") as "(%L2 & %R & %rt_cur' & %lt_cur' & %r' & HL & %Hst & Hstep & HT)".
    destruct (decide (ma = StratNoRefold)).
    - (* don't fold *)
      iModIntro. iExists _, _, _, _, _. iFrame.
      iSplitR. { iPureIntro. simp_ltypes. done. }
      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro.
      iIntros "(Hl & $)".
      rewrite ltype_own_opened_unfold /opened_ltype_own.
      iExists ly. iFrame.
      rewrite -Hst.
      iSplitR. { done. }
      iSplitR; first done. iSplitR; first done.
      iSplitR; first done. done.
    - (* fold it again *)
      iDestruct "HT" as "(%ri & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(#Hincl & HL & %rf & HT)".
      iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L3 & %κs & %R2 & Hstep' & HL & HT)".
      iPoseProof (imp_unblockable_blocked_dead lt_cur') as "#(_ & Hub)".
      set (κs' := ltype_blocked_lfts lt_cur').
      destruct (decide (κs = [] ∧ κs' = [])) as [[-> ->] | ].
      + iDestruct "HT" as "(% & %Heq & HT)". destruct Heq as [<-].
        iExists L3, _, _, _, _. iFrame.
        iSplitR. { iPureIntro. rewrite ltype_core_syn_type_eq. rewrite -Hst2 -Hst1 //. }
        iApply logical_step_fupd.
        iApply (logical_step_compose with "Hstep").
        iPoseProof (logical_step_mask_mono _ F with "Hcl") as "Hcl"; first done.
        iApply (logical_step_compose with "Hcl").
        iApply (logical_step_compose with "Hstep'").
        iApply logical_step_intro.
        iIntros "!> (Hpre & $) Hcl (Hl & $)".
        (* instantiate own_lt_cur' with ownership of lt_cur' *)
        iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
        iMod ("Hcl" $! (λ π _ l, l ◁ₗ[π, Owned] r' @ lt_cur')%I [] with "Hpre [] Hl []") as "Ha".
        { by iApply big_sepL_nil. }
        { iModIntro. iIntros "_ Hb".
          iMod ("Hub" with "[] Hb") as "Hb". { iApply big_sepL_nil. done. }
          rewrite !ltype_own_core_equiv.
          iApply (ltype_incl_use_core with "Hincl Hb"); first done. }
        iDestruct "Ha" as "($ & Hobs & Hcl)".
        iMod ("Hcl" with "[] Hobs") as "Hl".
        { iApply big_sepL_nil. done. }
        iMod "Hcl_F" as "_". rewrite ltype_own_core_equiv. done.
      + iAssert (([∗ list] κ' ∈ κs ++ κs', ⌜lctx_lft_incl E L3 κ' κ⌝) ∗ T L3 (Cpost ri rf ∗ R2 ∗ R) rt_full (CoreableLtype (κs ++ κs') lt_full) (PlaceIn rf))%I with "[HT]" as "HT".
        { destruct κs, κs'; naive_solver. }
        iDestruct "HT" as "(#Hincl1 & HT)".
        iPoseProof (big_sepL_lft_incl_incl with "HE HL Hincl1") as "#Hincl2".
        iExists L3, _, _, _, _. iFrame.
        iSplitR. { iPureIntro. simp_ltypes. rewrite -Hst2 -Hst1. done. }
        iApply logical_step_fupd.
        iApply (logical_step_compose with "Hstep").
        iPoseProof (logical_step_mask_mono _ F with "Hcl") as "Hcl"; first done.
        iApply (logical_step_compose with "Hcl").
        iApply (logical_step_compose with "Hstep'").
        iApply logical_step_intro.
        iIntros "!> (Hpre & $) Hcl (Hl & $)".
        iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
        iMod ("Hcl" $! (λ π _ l, l ◁ₗ[π, Owned] r' @ lt_cur')%I (κs ++ κs') with "[Hpre] [] Hl []") as "Ha".
        { rewrite lft_dead_list_app. iIntros "(Hdead & _)". by iApply "Hpre". }
        { done. }
        { iModIntro. iIntros "#Hdead Hb".
          rewrite lft_dead_list_app. iDestruct "Hdead" as "(_ & Hdead)".
          iMod ("Hub" with "Hdead Hb") as "Hb".
          rewrite !ltype_own_core_equiv.
          iApply (ltype_incl_use_core with "Hincl Hb"); first done. }
        iDestruct "Ha" as "($ & Hobs & Hcl)".
        iMod "Hcl_F" as "_".
        iModIntro. rewrite ltype_own_coreable_unfold /coreable_ltype_own.
        iExists ly. rewrite -Hst2 -Hst1. iSplitR; first done.
        iSplitR; first done. iSplitR; first done. iFrame.
  Qed.
  Definition stratify_ltype_opened_Uniq_inst := [instance @stratify_ltype_opened_Uniq].
  Global Existing Instance stratify_ltype_opened_Uniq_inst.

  Lemma stratify_ltype_shadowed_shared {M} (ml : M) {rt_cur rt_full} π E L mu mdu ma l
      (lt_cur : ltype rt_cur) (lt_full : ltype rt_full) (r_cur : place_rfn rt_cur) r_full κ `{!StratifyLtypeShouldCloseInv ml (Shared κ)} T :
    stratify_ltype π E L mu mdu ma ml l lt_cur r_cur (Shared κ) (λ L' R rt_cur' lt_cur' (r_cur' : place_rfn rt_cur'),
      if decide (ma = StratNoRefold)
        then (* keep it open *)
          T L' R rt_full (ShadowedLtype lt_cur' r_cur' lt_full) r_full
        else
          (T L' R rt_full (lt_full) (r_full))
      )
    ⊢ stratify_ltype π E L mu mdu ma ml l (ShadowedLtype lt_cur r_cur lt_full) r_full (Shared κ) T.
  Proof.
    iIntros "Hstrat".
    iIntros (????) "#CTX #HE HL Hl".
    rewrite ltype_own_shadowed_unfold /shadowed_ltype_own. iDestruct "Hl" as "(Hcur & Hfull)".
    iMod ("Hstrat" with "[//] [//] [//] CTX HE HL Hcur") as "(%L' & %R & %rt' & %lt' & %r' & HL & %Hst' & Ha & HT)".
    iModIntro. case_decide.
    - iExists _, _, _, _, _. iFrame. simp_ltypes.
      iR. iApply (logical_step_wand with "Ha").
      iIntros "(Ha & $)". rewrite ltype_own_shadowed_unfold /shadowed_ltype_own.
      iFrame.
    - iExists _, _, _, _, _. iFrame. simp_ltypes.
      iR. iApply (logical_step_wand with "Ha").
      iIntros "(Ha & $)". iFrame.
  Qed.
  Definition stratify_ltype_shadowed_shared_inst := [instance @stratify_ltype_shadowed_shared].
  Global Existing Instance stratify_ltype_shadowed_shared_inst.

  Lemma stratify_ltype_opened_na_Owned {rt_cur rt_inner} π E L mu mdu ma {M} (ml : M) l
      (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner)
      (Cpre Cpost : rt_inner → iProp Σ) r `{!StratifyLtypeShouldCloseInv ml Owned} (T : stratify_ltype_cont_t) :
    stratify_ltype π E L mu mdu ma ml l lt_cur r (Owned)
      (λ L' R rt_cur' lt_cur' (r' : place_rfn rt_cur'),
        if decide (ma = StratNoRefold)
        then (* keep it open *)
          T L' R _ (OpenedNaLtype lt_cur' lt_inner Cpre Cpost) r'
        else (* fold the invariant *)
          ∃ ri,
            (* show that the core of lt_cur' is a subtype of lt_inner *)
            weak_subltype E L' (Owned) (r') (#ri) lt_cur' lt_inner (
              (* re-establish the invariant *)
              prove_with_subtype E L' true ProveDirect (Cpre ri)
                (λ L'' _ R2, T L'' (Cpost ri ∗ R2 ∗ R) unit (AliasLtype unit (ltype_st lt_inner) l) #tt)))
    ⊢ stratify_ltype π E L mu mdu ma ml l (OpenedNaLtype lt_cur lt_inner Cpre Cpost) r (Owned) T.
  Proof.
    rewrite /stratify_ltype /weak_subltype /prove_with_subtype.

    iIntros "Hstrat" (F ???) "#CTX #HE HL Hl".
    rewrite ltype_own_opened_na_unfold /opened_na_ltype_own.

    iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hlb & %Hst & Hl & Hcl)".
    iMod ("Hstrat" with "[//] [//] [//] CTX HE HL Hl") as "(%L2 & %R & %rt_cur' & %lt_cur' & %r' & HL & %Hst' & Hstep & HT)".

    destruct (decide (ma = StratNoRefold)) as [-> | ].
    - (* don't fold *)
      iModIntro.
      iExists _, _, _, _, _; iFrame; iR.

      iApply (logical_step_compose with "Hstep").
      iApply logical_step_intro.
      iIntros "(Hl & $)".

      rewrite ltype_own_opened_na_unfold /opened_na_ltype_own.
      iExists ly; iFrame.
      rewrite -Hst'; do 3 iR.
      done.

    - (* fold it again *)
      iDestruct "HT" as "(%ri & HT)".
      iMod ("HT" with "[//] CTX HE HL") as "(Hincl & HL & HT)".
      iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L3 & %κs & %R2 & Hstep' & HL & HT)".

      iExists L3, _, _, _, _; iFrame.
      iSplitR.
      { by simp_ltypes. }

      iApply logical_step_fupd.
      iApply (logical_step_compose with "Hstep").
      iPoseProof (logical_step_mask_mono with "Hcl") as "Hcl"; first done.
      iApply (logical_step_compose with "Hcl").
      iApply (logical_step_compose with "Hstep'").
      iApply logical_step_intro.

      iIntros "!> (Hpre & $) Hcl (Hl & $)".
      iMod (ltype_incl_use with "Hincl Hl") as "Hl"; first done.

      iPoseProof ("Hcl" with "Hpre Hl") as "Hvs".
      iSplitL "".
      { rewrite ltype_own_alias_unfold /alias_lty_own.
        rewrite -Hst.

        by iExists ly; repeat iR. }

      iMod (fupd_mask_mono with "Hvs") as "Hvs"; first set_solver.
      done.
  Qed.
  Definition stratify_ltype_opened_na_Owned_inst := [instance @stratify_ltype_opened_na_Owned].
  Global Existing Instance stratify_ltype_opened_na_Owned_inst.

  (* NOTE: instances for descending below MutLty, etc., are in the respective type's files. *)

  (** Unblock stratification: We define instances for the leaves of the unblocking stratifier *)

  (* On an ofty leaf, do a ghost resolution.
    This will also trigger resolve_ghost instances for custom-user defined types.
    This needs to have a lower priority than custom user-defined instances (e.g. for [◁ value_t]), so we give it a high cost. *)
  Global Instance stratify_ltype_unblock_ofty_in_inst {rt} π E L mu mdu ma l (ty : type rt) (r : rt) b :
    StratifyLtype π E L mu mdu ma StratifyUnblockOp l (◁ ty)%I (#r) b | 100 :=
    λ T, i2p (stratify_ltype_resolve_ghost_leaf π E L mu mdu ma StratifyUnblockOp ResolveTry l (◁ ty)%I b (#r) T).

  (* Also trigger resolve instances for ADTs. *)
  Global Instance stratify_ltype_resolve_ofty_in_inst {rt} π E L mu mdu ma l (ty : type rt) (r : rt) b :
    StratifyLtype π E L mu mdu ma StratifyResolveOp l (◁ ty)%I (#r) b | 100 :=
    λ T, i2p (stratify_ltype_resolve_ghost_leaf π E L mu mdu ma StratifyResolveOp ResolveTry l (◁ ty)%I b (#r) T).

  (** ** place typing *)

  (** *** Instances for unblocking & updating refinements *)
  (** Note: all of these instances should have higher priority than the id instances,
        so that the client of [typed_place] does not have to do this.
      TODO: can we find an elegant way to do this for nested things (eliminate a stratify_ltype)?
        e.g. when something below is blocked and we need to unblock it, or we need to update the refinement.
        currently, the client has to do this...
        Problem why we can't directly do it: we need at least one step of computation to do it, and typed_place does not always take a step.
    *)

  (* TODO: some of this is really duplicated with stratify, in particular the unblocking and the ltype unfolding. Could we have an instance that just escapes into a shallow version of stratify that requires no logstep in order avoid duplication? *)

  (* TODO: we probably want to generalize this to not immediately require a dead token for κ,
    but rather have a "dead" context and spawn a sidecondition for inclusion in one of the dead lifetimes? *)
  Lemma typed_place_blocked_unblock {rt} f E L l (ty : type rt) κ (r : place_rfn rt) bmin0 b P T :
    [† κ] ∗ typed_place E L f l (◁ ty) r bmin0 b P T
    ⊢ typed_place E L f l (BlockedLtype ty κ) r bmin0 b P T.
  Proof.
    iIntros "(Hdead & Hp)". iIntros (????) "#(LFT & LLCTX) #HE HL Hf Hl HΦ".
    iApply fupd_place_to_wp.
    iMod (unblock_blocked with "Hdead Hl") as "Hl"; first done.
    iModIntro.
    iApply ("Hp" with "[//] [//] [$LFT $LLCTX] HE HL Hf Hl").
    iIntros (L' κs l2 bmin b2 rti tyli ri updcx) "Hl2 Hs HT HL Hf".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _ _ with "Hl2 [Hs] HT HL Hf").
    iIntros (upd) "#Hincl Hl2 %Hst HR Hcond".
    iMod ("Hs" with "Hincl Hl2 [//] HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hs" with "HL Hf Hcont") as (upd') "(Hl & %Hst' & Hcond & Htoks & HR' & ? & ? &?)".
    iFrame.
    simp_ltypes. iR.
    by iApply typed_place_cond_blocked_l.
  Qed.
  Definition typed_place_blocked_unblock_inst := [instance @typed_place_blocked_unblock].
  Global Existing Instance typed_place_blocked_unblock_inst | 5.

  Lemma typed_place_shrblocked_unblock {rt} f E L l (ty : type rt) κ (r : place_rfn rt) bmin0 b P T :
    [† κ] ∗ typed_place E L f l (◁ ty) r bmin0 b P T
    ⊢ typed_place E L f l (ShrBlockedLtype ty κ) r bmin0 b P T.
  Proof.
    iIntros "(Hdead & Hp)". iIntros (????) "#(LFT & LLCTX) #HE HL Hf Hl HΦ".
    iApply fupd_place_to_wp.
    iMod (unblock_shrblocked with "Hdead Hl") as "Hl"; first done.
    iModIntro.
    iApply ("Hp" with "[//] [//] [$LFT $LLCTX] HE HL Hf Hl").
    iIntros (L' κs l2 b2 bmin rti tyli ri updcx) "Hl2 Hs HT HL Hf".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _ _ with "Hl2 [Hs] HT HL Hf").
    iIntros (upd) "#Hincl Hl2 %Hst HR Hcond".
    iMod ("Hs" with "Hincl Hl2 [//] HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hs" with "HL Hf Hcont") as (upd') "(Hl & %Hst' & Hcond & Htoks & HR & ?)".
    iFrame.
    simp_ltypes. iR.
    by iApply typed_place_cond_shrblocked_l.
  Qed.
  Definition typed_place_shrblocked_unblock_inst := [instance @typed_place_shrblocked_unblock].
  Global Existing Instance typed_place_shrblocked_unblock_inst | 5.

  Lemma typed_place_coreable_unblock {rt} f E L l (lt lt' : ltype rt) κs (r : place_rfn rt) bmin0 b P `{Hsimp : !SimpLtype (ltype_core lt) lt'} T :
    lft_dead_list κs ∗ typed_place E L f l lt' r bmin0 b P T
    ⊢ typed_place E L f l (CoreableLtype κs lt) r bmin0 b P T.
  Proof.
    destruct Hsimp as [<-].
    iIntros "(Hdead & Hp)". iIntros (????) "#(LFT & LLCTX) #HE HL Hf Hl HΦ".
    iApply fupd_place_to_wp.
    iMod (unblock_coreable with "Hdead Hl") as "Hl"; first done.
    iModIntro.
    iApply ("Hp" with "[//] [//] [$LFT $LLCTX] HE HL Hf Hl").
    iIntros (L' κs' l2 b2 bmin rti tyli ri updcx) "Hl2 Hs HT HL Hf".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _ _ with "Hl2 [Hs] HT HL Hf").
    iIntros (upd) "#Hincl Hl2 %Hst HR Hcond".
    iMod ("Hs" with "Hincl Hl2 [//] HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hs" with "HL Hf Hcont") as (upd') "(Hl & %Hst' & Hcond & Htoks & HR & ?)".
    iFrame. simp_ltypes.
    rewrite ltype_core_syn_type_eq in Hst'. rewrite Hst'. iR.
    iApply typed_place_cond_coreable_l.
    iApply typed_place_cond_trans; last done.
    iApply typed_place_cond_core.
  Qed.
  Definition typed_place_coreable_unblock_inst := [instance @typed_place_coreable_unblock].
  Global Existing Instance typed_place_coreable_unblock_inst | 5.

  Lemma typed_place_resolve_ghost {rt} f E L l (lt : ltype rt) bmin0 b γ P T :
    ⌜lctx_bor_kind_alive E L b⌝ ∗
    resolve_ghost f.1 E L ResolveAll false l lt b (PlaceGhost γ) (λ L' r R progress,
      introduce_with_hooks E L' R (λ L'', typed_place E L'' f l lt r bmin0 b P T))
    ⊢ typed_place E L f l lt (PlaceGhost γ) bmin0 b P T.
  Proof.
    iIntros "(%Hw & Hres)". iIntros (????) "#CTX #HE HL Hf Hl HΦ".
    iApply fupd_place_to_wp.
    iMod ("Hres" with "[] [] CTX HE HL Hl") as "(%L' & %r & %R & %prog & Hstep & HL & HP)"; [done.. | ].
    iMod "Hstep" as "(Hl & HR)".
    iMod ("HP" with "[] CTX HE HL HR") as "(%L'' & HL & HP)"; first done.
    iModIntro. iApply ("HP" with "[//] [//] CTX HE HL Hf Hl").
    iIntros (L1 κs l2 b2 bmin rti tyli ri updcx) "Hl2 Hs HT HL".
    iApply ("HΦ" $! _ _ _ _ _ _ _ _ _ with "Hl2 [Hs] HT HL").
    iIntros (upd) "#Hincl Hl2 %Hst HR Hcond".
    iMod ("Hs" with "Hincl Hl2 [//] HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hcont".
    iApply ("Hs" with "HL"). simp_ltypes. done.
  Qed.
  (* this needs to have a lower priority than place_blocked_unblock *)
  Definition typed_place_resolve_ghost_inst := [instance @typed_place_resolve_ghost].
  Global Existing Instance typed_place_resolve_ghost_inst | 8.

  (** *** Place access instances *)

  Import EqNotations.


  (* instances for Opened *)
  Lemma typed_place_opened_owned E L f {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost r l P  T :
    (* no weak access possible -- we currently don't have the machinery to restore and fold invariants at this point, though we could in principle enable this *)
    typed_place E L f l lt_cur r UpdStrong (Owned) P (λ L' κs l2 b2 bmin rti ltyi ri updcx,
      T L' κs l2 b2 bmin rti ltyi ri
        (λ L2 upd cont,
          updcx L2 upd (λ upd',
            cont (mkPUpd _ UpdStrong
            (upd').(pupd_rt)
            (OpenedLtype (upd').(pupd_lt) lt_inner lt_full Cpre Cpost)
            (upd').(pupd_rfn)
            (upd').(pupd_R)
            UpdStrong I I))))
    ⊢ typed_place E L f l (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) r UpdStrong (Owned) P T.
  Proof.
    iIntros "HT". iIntros (Φ F ??) "#CTX #HE HL Hf Hl HR".
    iPoseProof (opened_ltype_acc_owned with "Hl") as "(Hl & Hcl)".
    iApply ("HT" with "[//] [//] CTX HE HL Hf Hl").
    iIntros (L' ??????? updcx) "Hl Hv".
    iApply ("HR" with "Hl").
    iIntros (upd) "Hincl Hl %Hst HR Hcond". simpl.
    iMod ("Hv" with "Hincl Hl [//] HR Hcond") as "Hv".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hv" with "HL Hf Hcont") as (upd') "(Hl & %Hst' & Hcond & Htoks & ? & ? & ?)".
    iFrame.
    iPoseProof ("Hcl" with "Hl [//]") as "Hl".
    eauto with iFrame.
  Qed.

  (* By default, don't descend below [Opened] if we don't make another place access *)
  Definition typed_place_opened_owned_guarded π E L {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost r l P `{!TCDone (P ≠ [])} :=
    typed_place_opened_owned π E L lt_cur lt_inner lt_full Cpre Cpost r l P.
  Definition typed_place_opened_owned_guarded_inst := [instance @typed_place_opened_owned_guarded].
  Global Existing Instance typed_place_opened_owned_guarded_inst | 5.

  (* But we can enable always descending with a config flag. *)
  Definition typed_place_opened_owned_config π E L {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost r l P `{!CheckConfig rr_config_dont_fold_places} :=
    typed_place_opened_owned π E L lt_cur lt_inner lt_full Cpre Cpost r l P.
  Definition typed_place_opened_owned_config_inst := [instance @typed_place_opened_owned_config].
  Global Existing Instance typed_place_opened_owned_config_inst | 5.

  Lemma typed_place_opened_uniq f E L {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost r l κ γ P T :
    (* no weak access possible -- we currently don't have the machinery to restore and fold invariants at this point, though we could in principle enable this *)
    typed_place E L f l lt_cur r UpdStrong (Owned) P (λ L' κs l2 b2 bmin rti ltyi ri updcx,
      T L' κs l2 b2 bmin rti ltyi ri
        (λ L2 upd cont,
          updcx L2 upd (λ upd',
            cont (mkPUpd _ UpdStrong
            (upd').(pupd_rt)
            (OpenedLtype (upd').(pupd_lt) lt_inner lt_full Cpre Cpost)
            (upd').(pupd_rfn)
            (upd').(pupd_R)
            UpdStrong I I))))
    ⊢ typed_place E L f l (OpenedLtype lt_cur lt_inner lt_full Cpre Cpost) r UpdStrong (Uniq κ γ) P T.
  Proof.
    iIntros "HT". iIntros (Φ F ??) "#CTX #HE HL Hf Hl HR".
    iPoseProof (opened_ltype_acc_uniq with "Hl") as "(Hl & Hcl)".
    iApply ("HT" with "[//] [//] CTX HE HL Hf Hl").
    iIntros (L' ??????? updcx) "Hl Hv".
    iApply ("HR" with "Hl").
    iIntros (upd) "Hincl Hl %Hst HR Hcond". simpl.
    iMod ("Hv" with "Hincl Hl [//] HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hs" with "HL Hf Hcont") as (upd') "(Hl & %Hst' & Hcond & Htoks & ? & ? & ?)".
    simpl.
    iFrame.
    iPoseProof ("Hcl" with "Hl [//]") as "Hl".
    eauto with iFrame.
  Qed.

  (* By default, don't descend below [Opened] if we don't make another place access *)
  Definition typed_place_opened_uniq_guarded π E L {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost r l κ γ P `{!TCDone (P ≠ [])} :=
    typed_place_opened_uniq π E L lt_cur lt_inner lt_full Cpre Cpost r l κ γ P.
  Definition typed_place_opened_uniq_guarded_inst := [instance @typed_place_opened_uniq_guarded].
  Global Existing Instance typed_place_opened_uniq_guarded_inst | 5.

  (* But we can enable always descending with a config flag. *)
  Definition typed_place_opened_uniq_config π E L {rt_cur rt_inner rt_full} (lt_cur : ltype rt_cur) (lt_inner : ltype rt_inner) (lt_full : ltype rt_full) Cpre Cpost r l κ γ P `{!CheckConfig rr_config_dont_fold_places} :=
    typed_place_opened_uniq π E L lt_cur lt_inner lt_full Cpre Cpost r l κ γ P.
  Definition typed_place_opened_uniq_config_inst := [instance @typed_place_opened_uniq_config].
  Global Existing Instance typed_place_opened_uniq_config_inst | 5.

  Lemma typed_place_shadowed_shared f E L {rt_cur rt_full} (lt_cur : ltype rt_cur) (lt_full : ltype rt_full) r_cur (r_full : place_rfn rt_full) bmin0 l κ P (T : place_cont_t rt_full bmin0) :
    (* sidecondition needed for the weak update *)
    ⌜lctx_place_update_kind_outlives E L bmin0 (ltype_blocked_lfts lt_full)⌝ ∗
    typed_place E L f l lt_cur (#r_cur) bmin0 (Shared κ) P (λ L' κs l2 b2 bmin rti ltyi ri updcx,
      T L' κs l2 b2 bmin rti ltyi ri
        (λ L2 upd cont,
          updcx L2 upd (λ upd',
            cont (mkPUpd _ bmin0
            rt_full
            (ShadowedLtype (upd').(pupd_lt) (upd').(pupd_rfn) lt_full)
            r_full
            (upd').(pupd_R)
            (* TODO: basically, we can unblock at _any_ lifetime. so we could strengthen this. *)
            bmin0 opt_place_update_eq_refl opt_place_update_eq_refl)))
    )
    ⊢ typed_place E L f l (ShadowedLtype lt_cur (#r_cur) lt_full) r_full bmin0 (Shared κ) P T.
  Proof.
    iIntros "(%Houtl & HT)".
    iIntros (????) "#CTX #HE HL Hf Hl Hc".
    iPoseProof (lctx_place_update_kind_outlives_use _ _ _ _ Houtl with "HE HL") as "#Houtl'".
    iPoseProof (shadowed_ltype_acc_cur with "Hl") as "(Hcur & Hcl)".
    iApply ("HT" with "[//] [//] CTX HE HL Hf Hcur").
    iIntros (L' κs l2 b2 bmin rti ltyi ri updcx) "Hl Hcc".
    iApply ("Hc" with "Hl").

    iIntros (upd) "Hincl Hl %Hst HR Hcond". simpl in *.
    iMod ("Hcc" with "Hincl Hl [//] HR Hcond") as "Hs".
    iModIntro. iIntros (? cont) "HL Hf Hcont".
    iMod ("Hs" with "HL Hf Hcont") as (upd') "(Hl & %Hst' & Hcond' & Htoks & HR & ? & ?)".
    simpl.
    iPoseProof ("Hcl" with "[] Hl") as "Hl".
    { done. }
    simpl. iFrame. simpl. iFrame.
    simp_ltypes. iR.
    iSplitL; last iApply place_update_kind_incl_refl.
    iApply typed_place_cond_shadowed_update_cur. done.
  Qed.
  Definition typed_place_shadowed_shared_inst := [instance @typed_place_shadowed_shared].
  Global Existing Instance typed_place_shadowed_shared_inst | 5.

  (* TODO: OpenedNaType *)

  (** Typing hints *)
  Lemma interpret_typing_hint_ignore orty E L bmin {rt} (ty : type rt) r (T : interpret_typing_hint_cont_t bmin rt) :
    T rt ty r (mkPUKRes UpdBot eq_refl opt_place_update_eq_refl)
    ⊢ interpret_typing_hint E L orty bmin ty r T.
  Proof.
    iIntros "HT".
    iIntros (????) "#CTX #HE HL".
    iFrame. iSplitL.
    { iApply type_incl_refl. }
    iSplitL.
    { iApply typed_place_cond_refl_ofty. }
    iApply upd_bot_min.
  Qed.
  Definition interpret_typing_hint_none := interpret_typing_hint_ignore None.
  Definition interpret_typing_hint_none_inst := [instance @interpret_typing_hint_none].
  Global Existing Instance interpret_typing_hint_none_inst.

  Lemma interpret_typing_hint_some_strong E L rty {rt} (ty : type rt) r (T : interpret_typing_hint_cont_t UpdStrong rt) :
    find_in_context (FindNamedLfts) (λ M, named_lfts M -∗
      (** Interpret the type annotation *)
      li_tactic (interpret_rust_type_goal M rty) (λ '(existT rt2 ty2),
      (* TODO it would be really nice to have a stronger form of subtyping here that also supports unfolding/folding of invariants *)
      ∃ r2, weak_subtype E L r r2 ty ty2 (
        T rt2 ty2 r2 (mkPUKRes (allowed:=UpdStrong) UpdStrong I I))))
    ⊢ interpret_typing_hint E L (Some rty) UpdStrong ty r T.
  Proof.
    iIntros "HT".
    rewrite /FindNamedLfts.
    iDestruct "HT" as "(%M & HM & HT)". iPoseProof ("HT" with "HM") as "Ha".
    rewrite /interpret_rust_type_goal. iDestruct "Ha" as "(%rt2 & %ty2 & %r2 & HT)".
    iIntros (????) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(#Hincl3 & HL & HT)".
    iModIntro. iPoseProof "Hincl3" as "(%Hsteq' & _)".
    set (updstrong := mkPUKRes (allowed:=UpdStrong)(rt1:=rt)(rt2:=rt2) UpdStrong I I).
    iExists rt2, ty2, r2, updstrong. by iFrame "HL HT".
  Qed.
  Definition interpret_typing_hint_some_strong_inst := [instance @interpret_typing_hint_some_strong].
  Global Existing Instance interpret_typing_hint_some_strong_inst.

  Lemma interpret_typing_hint_some_weak E L rty {rt} (ty : type rt) r (T : interpret_typing_hint_cont_t UpdWeak rt) :
    find_in_context (FindNamedLfts) (λ M, named_lfts M -∗
      (** Interpret the type annotation *)
      li_tactic (interpret_rust_type_goal M rty) (λ '(existT rt2 ty2),
      (* TODO it would be really nice to have a stronger form of subtyping here that also supports unfolding/folding of invariants *)
      ∃ (Heq : rt = rt2),
      ∃ r2, weak_subtype E L r r2 ty ty2 (
        T rt2 ty2 r2 (mkPUKRes (allowed:=UpdWeak) UpdWeak Heq Heq))))
    ⊢ interpret_typing_hint E L (Some rty) UpdWeak ty r T.
  Proof.
    iIntros "HT".
    rewrite /FindNamedLfts.
    iDestruct "HT" as "(%M & HM & HT)". iPoseProof ("HT" with "HM") as "Ha".
    rewrite /interpret_rust_type_goal. iDestruct "Ha" as "(%rt2 & %ty2 & %Heq & %r2 & HT)".
    subst.
    iIntros (????) "#CTX #HE HL".
    iMod ("HT" with "[//] CTX HE HL") as "(#Hincl3 & HL & HT)".
    iModIntro. iPoseProof "Hincl3" as "(%Hsteq' & _)".
    set (updstrong := mkPUKRes (allowed:=UpdWeak)(rt1:=rt2)(rt2:=rt2) UpdWeak eq_refl eq_refl).
    iExists rt2, ty2, r2, updstrong. iFrame "HL HT".
    iR. done.
  Qed.
  Definition interpret_typing_hint_some_weak_inst := [instance @interpret_typing_hint_some_weak].
  Global Existing Instance interpret_typing_hint_some_weak_inst.


  (** typing of expressions *)
  Lemma typed_val_expr_wand E L f e T1 T2 :
    typed_val_expr E L f e T1 -∗
    (∀ L' v m rt ty r, T1 L' v m rt ty r -∗ T2 L' v m rt ty r) -∗
    typed_val_expr E L f e T2.
  Proof.
    iIntros "He HT" (Φ) "#LFT #HE HL Hf HΦ".
    iApply ("He" with "LFT HE HL Hf"). iIntros (L' v m rt ty r) "HL Hf Hv Hty".
    iApply ("HΦ" with "HL Hf Hv"). by iApply "HT".
  Qed.

  Lemma typed_if_wand E L v (P T1 T2 T1' T2' : iProp Σ):
    typed_if E L v P T1 T2 -∗
    ((T1 -∗ T1') ∧ (T2 -∗ T2')) -∗
    typed_if E L v P T1' T2'.
  Proof.
    iIntros "Hif HT Hv". iDestruct ("Hif" with "Hv") as (b ?) "HC".
    iExists _. iSplit; first done. destruct b.
    - iDestruct "HT" as "[HT _]". by iApply "HT".
    - iDestruct "HT" as "[_ HT]". by iApply "HT".
  Qed.

  Lemma typed_bin_op_wand E L f v1 P1 Q1 v2 P2 Q2 op ot1 ot2 T:
    typed_bin_op E L f v1 Q1 v2 Q2 op ot1 ot2 T -∗
    (P1 -∗ Q1) -∗
    (P2 -∗ Q2) -∗
    typed_bin_op E L f v1 P1 v2 P2 op ot1 ot2 T.
  Proof.
    iIntros "H Hw1 Hw2 H1 H2".
    iApply ("H" with "[Hw1 H1]"); [by iApply "Hw1"|by iApply "Hw2"].
  Qed.

  Lemma typed_un_op_wand E L f v P Q op ot T:
    typed_un_op E L f v Q op ot T -∗
    (P -∗ Q) -∗
    typed_un_op E L f v P op ot T.
  Proof.
    iIntros "H Hw HP". iApply "H". by iApply "Hw".
  Qed.

  Lemma typed_unop_simplify E L f v P n ot {SH : SimplifyHyp P (Some n)} op T:
    (SH (find_in_context (FindValP v) (λ P, typed_un_op E L f v P op ot T))).(i2p_P)
    ⊢ typed_un_op E L f v P op ot T.
  Proof.
    rewrite /typed_un_op.
    iIntros "Hs Hv".
    iPoseProof (i2p_proof with "Hs Hv") as "Ha".
    rewrite /FindValP/find_in_context/=.
    iDestruct "Ha" as (P') "[HP HT]". by iApply ("HT" with "[$]").
  Qed.
  Definition typed_unop_simplify_inst := [instance typed_unop_simplify].
  Global Existing Instance typed_unop_simplify_inst | 1000.

  Lemma typed_binop_simplify E L f v1 P1 v2 P2 o1 o2 ot1 ot2 {SH1 : SimplifyHyp P1 o1} {SH2 : SimplifyHyp P2 o2} `{!TCOneIsSome o1 o2} op T:
    let G1 := (SH1 (find_in_context (FindValP v1) (λ P, typed_bin_op E L f v1 P v2 P2 op ot1 ot2 T))).(i2p_P) in
    let G2 := (SH2 (find_in_context (FindValP v2) (λ P, typed_bin_op E L f v1 P1 v2 P op ot1 ot2 T))).(i2p_P) in
    let G :=
       match o1, o2 with
     | Some n1, Some n2 => if (n2 ?= n1)%N is Lt then G2 else G1
     | Some n1, _ => G1
     | _, _ => G2
       end in
    G
    ⊢ typed_bin_op E L f v1 P1 v2 P2 op ot1 ot2 T.
  Proof.
    iIntros "/= Hs Hv1 Hv2".
    destruct o1 as [n1|], o2 as [n2|] => //. 1: case_match.
    1,3,4: iPoseProof (i2p_proof with "Hs Hv1") as (P) "[Hv Hsub]".
    4,5,6: iPoseProof (i2p_proof with "Hs Hv2") as (P) "[Hv Hsub]".
    all: by simpl in *; iApply ("Hsub" with "[$]").
  Qed.
  Definition typed_binop_simplify_inst := [instance typed_binop_simplify].
  Global Existing Instance typed_binop_simplify_inst | 1000.

  Lemma type_val_context v π (T : typed_value_cont_t) :
    (find_in_context (FindVal v) (λ '(existT rt (ty, r, π', m')),
      ⌜π = π'⌝ ∗ T m' rt ty r)) ⊢
    typed_value π v T.
  Proof.
    iDestruct 1 as ([rt [[[ty r] π'] m']]) "(Hv & <- & HT)". simpl in *.
    iIntros "LFT". iExists _, _, _. iFrame.
  Qed.
  Global Instance type_val_context_inst v π :
    TypedValue π v | 100 := λ T, i2p (type_val_context v π T).

  Lemma type_val E L f v T :
    typed_value f.1 v (T L v) ⊢
    typed_val_expr E L f (Val v) T.
  Proof.
    iIntros "HT" (Φ) "#LFT #HE HL Hf HΦ".
    iDestruct ("HT" with "LFT") as "(%rt & %ty & %r & %m & Hty & HT)".
    iApply wpe_value. iApply ("HΦ" with "HL Hf Hty HT").
  Qed.

  Fixpoint interpret_rust_types (M : gmap string lft) (tys : list rust_type) (T : list (sigT type) → iProp Σ) :  iProp Σ :=
    match tys with
    | [] => T []
    | ty :: tys =>
        li_tactic (interpret_rust_type_goal M ty)
          (λ ty, interpret_rust_types M tys (λ tys, T (ty :: tys)))
    end.
  Lemma interpret_rust_types_elim M tys T :
    interpret_rust_types M tys T -∗
    ∃ tys, T tys.
  Proof.
    iIntros "Ha". iInduction tys as [ | ty tys] "IH" forall (T); simpl.
    - iExists []. done.
    - rewrite /li_tactic/interpret_rust_type_goal.
      iDestruct "Ha" as "(%rt & %ty' & Ha)".
      iPoseProof ("IH" with "Ha") as "(%tys' & HT)".
      eauto.
  Qed.

  Lemma type_call E L f T ef eκs etys es :
    (∃ M, named_lfts M ∗
    li_tactic (compute_map_lookups_nofail_goal M eκs) (λ eκs',
    interpret_rust_types M etys (λ atys,
    named_lfts M -∗
    typed_val_expr E L f ef (λ L' vf m rtf tyf rf,
        foldr (λ e T L'' vl tys, typed_val_expr E L'' f e (λ L''' v m rt ty r,
          ⌜m = MetaNone⌝ ∗
          T L''' (vl ++ [v]) (tys ++ [existT rt (ty, r)])))
            (λ L'' vl tys, typed_call E L'' f eκs' atys vf (vf ◁ᵥ{f.1, m} rf @ tyf) vl tys (λ L v rt ty r,
              v ◁ᵥ{f.1, MetaNone} r @ ty ∗ T L v MetaNone _ ty r))
              es L' [] []))))
    ⊢ typed_val_expr E L f (CallE ef eκs etys es) T.
  Proof.
    rewrite /compute_map_lookups_nofail_goal.
    iIntros "(%M & Hnamed & %eκs' & _ & He)".
    iPoseProof (interpret_rust_types_elim with "He") as "(%tys & He)".
    iIntros (Φ) "#CTX #HE HL Hf HΦ".
    rewrite /CallE.
    iApply wp_call_bind. iApply ("He" with "Hnamed CTX HE HL Hf"). iIntros (L' vf mf rtf tyf rf) "HL Hf Hvf HT".
    iAssert ([∗ list] v;rty∈[];([] : list $ @sigT RT (λ rt, (type rt * rt)%type)), let '(existT rt (ty, r)) := rty in v ◁ᵥ{f.1, MetaNone} r @ ty)%I as "-#Htys". { done. }
    move: {2 3 5} ([] : list val) => vl.
    generalize (@nil (@sigT RT (fun rt : RT => prod (@type Σ _ rt) rt))) at 2 3 as tys'; intros tys'.
    iInduction es as [|e es] "IH" forall (L' vl tys') => /=. 2: {
      iApply ("HT" with "CTX HE HL Hf"). iIntros (L'' v m rt ty r) "HL Hf Hv (-> & Hnext)".
      iApply ("IH" with "HΦ HL Hf Hvf Hnext").
      iFrame. by iApply big_sepL2_nil.
    }
    unfold typed_call.
    iApply ("HT" with "Hvf Htys CTX HE HL Hf [-]").
    iIntros (?????) "HL Hf".
    iIntros "(Hv & HT)".
    iApply ("HΦ" with "HL Hf Hv HT").
  Qed.

  Lemma type_bin_op E L f o e1 e2 ot1 ot2 T :
    typed_val_expr E L f e1 (λ L1 v1 m1 rt1 ty1 r1,
      typed_val_expr E L1 f e2 (λ L2 v2 m2 rt2 ty2 r2,
      ⌜m1 = m2⌝ ∗
      typed_bin_op E L2 f v1 (v1 ◁ᵥ{f.1, m1} r1 @ ty1) v2 (v2 ◁ᵥ{f.1, m2} r2 @ ty2) o ot1 ot2 T))
    ⊢ typed_val_expr E L f (BinOp o ot1 ot2 e1 e2) T.
  Proof.
    iIntros "He1" (Φ) "#LFT #HE HL Hf HΦ".
    wpe_bind. iApply ("He1" with "LFT HE HL Hf"). iIntros (L1 v1 m1 rt1 ty1 r1) "HL Hf Hv1 He2".
    wpe_bind. iApply ("He2" with "LFT HE HL Hf"). iIntros (L2 v2 m2 rt2 ty2 r2) "HL Hf Hv2 (<- & Hop)".
    iApply ("Hop" with "Hv1 Hv2 LFT HE HL Hf HΦ").
  Qed.

  Lemma type_un_op E L f o e ot T :
    typed_val_expr E L f e (λ L' v m rt ty r,
      typed_un_op E L' f v (v ◁ᵥ{f.1, m} r @ ty) o ot T)
    ⊢ typed_val_expr E L f (UnOp o ot e) T.
  Proof.
    iIntros "He" (Φ) "#LFT #HE HL Hf HΦ".
    wpe_bind. iApply ("He" with "LFT HE HL Hf"). iIntros (L' v m rt ty r) "HL Hf Hv Hop".
    by iApply ("Hop" with "Hv LFT HE HL Hf").
  Qed.

  Lemma type_check_bin_op E L f o e1 e2 ot1 ot2 T :
    typed_val_expr E L f e1 (λ L1 v1 m1 rt1 ty1 r1,
      typed_val_expr E L1 f e2 (λ L2 v2 m2 rt2 ty2 r2,
      ⌜m1 = m2⌝ ∗ typed_check_bin_op E L2 f v1 (v1 ◁ᵥ{f.1, m1} r1 @ ty1) v2 (v2 ◁ᵥ{f.1, m2} r2 @ ty2) o ot1 ot2 T))
    ⊢ typed_val_expr E L f (CheckBinOp o ot1 ot2 e1 e2) T.
  Proof.
    iIntros "He1" (Φ) "#LFT #HE HL Hf HΦ".
    wpe_bind. iApply ("He1" with "LFT HE HL Hf"). iIntros (L1 v1 m1 rt1 ty1 r1) "HL Hf Hv1 He2".
    wpe_bind. iApply ("He2" with "LFT HE HL Hf"). iIntros (L2 v2 m2 rt2 ty2 r2) "HL Hf Hv2 (<- & Hop)".
    iApply ("Hop" with "Hv1 Hv2 LFT HE HL Hf HΦ").
  Qed.

  Lemma type_check_un_op E L f o e ot T :
    typed_val_expr E L f e (λ L' v m rt ty r,
      typed_check_un_op E L' f v (v ◁ᵥ{f.1, m} r @ ty) o ot T)
    ⊢ typed_val_expr E L f (CheckUnOp o ot e) T.
  Proof.
    iIntros "He" (Φ) "#LFT #HE HL Hf HΦ".
    wpe_bind. iApply ("He" with "LFT HE HL Hf"). iIntros (L' v m rt ty r) "HL Hf Hv Hop".
    by iApply ("Hop" with "Hv LFT HE HL Hf").
  Qed.

  Lemma type_ife E L f e1 e2 e3 T:
    typed_val_expr E L f e1 (λ L' v m rt ty r,
      typed_if E L' v (v ◁ᵥ{f.1, m} r @ ty) (typed_val_expr E L' f e2 T) (typed_val_expr E L' f e3 T))
    ⊢ typed_val_expr E L f (IfE BoolOp e1 e2 e3) T.
  Proof.
    iIntros "He1" (Φ) "#LFT #HE HL Hf HΦ".
    wpe_bind. iApply ("He1" with "LFT HE HL Hf"). iIntros (L1 v1 m1 rt1 ty1 r1) "HL Hf Hv1 Hif".
    iDestruct ("Hif" with "Hv1") as "HT".
    iDestruct "HT" as (b) "(% & HT)".
    iApply wp_if_bool; [done|..].
    iApply physical_step_intro. iNext.
    destruct b; by iApply ("HT" with "LFT HE HL Hf").
  Qed.

  Lemma type_annot_expr E L f n {A} (a : A) e T:
    typed_val_expr E L f e (λ L' v m rt ty r,
      typed_annot_expr E L' f.1 n a v (v ◁ᵥ{f.1, m} r @ ty) T)
    ⊢ typed_val_expr E L f (AnnotExpr n a e) T.
  Proof.
    iIntros "He" (Φ) "#LFT #HE HL Hf HΦ".
    wpe_bind. iApply ("He" with "LFT HE HL Hf"). iIntros (L' v m rt ty r) "HL Hf Hv HT".
    iDestruct ("HT" with "LFT HE HL Hv") as "HT".
    iInduction n as [|n] "IH" forall (Φ). {
      rewrite /AnnotExpr/=.
      iApply fupd_wpe.
      iMod "HT" as "(%L2 & %m' & % & % & % & HL & Hv & HT)".
      iApply wpe_value.
      by iApply ("HΦ" with "[$] [$] [$]").
    }
    rewrite annot_expr_S_r. wpe_bind.
    iApply wp_skip.
    iApply physical_step_fupd_l.
    iApply physical_step_intro_lc.
    iModIntro. iIntros "(Hcred & Hcred1)".
    iModIntro. iNext.
    iApply fupd_wpe. iMod "HT".
    iMod (lc_fupd_elim_later with "Hcred1 HT") as ">HT". iModIntro.
    iApply ("IH" with "HΦ Hf HT").
  Qed.

  Lemma type_logical_and E L f e1 e2 T:
    typed_val_expr E L f e1 (λ L1 v1 m1 rt1 ty1 r1,
      typed_if E L1 v1 (v1 ◁ᵥ{f.1, m1} r1 @ ty1)
       (typed_val_expr E L1 f e2 (λ L2 v2 m2 rt2 ty2 r2,
        typed_if E L2 v2 (v2 ◁ᵥ{f.1, m2} r2 @ ty2)
           (typed_value f.1 (val_of_bool true) (T L2 (val_of_bool true)))
           (typed_value f.1 (val_of_bool false) (T L2 (val_of_bool false)))))
       (typed_value f.1 (val_of_bool false) (T L1 (val_of_bool false))))
    ⊢ typed_val_expr E L f (e1 &&{BoolOp, BoolOp, U8} e2)%E T.
  Proof.
    iIntros "HT". rewrite /LogicalAnd. iApply type_ife.
    iApply (typed_val_expr_wand with "HT"). iIntros (L1 v m rt ty r) "HT".
    iApply (typed_if_wand with "HT"). iSplit; iIntros "HT".
    2: { iApply type_val. by rewrite !val_of_bool_i2v. }
    iApply type_ife.
    iApply (typed_val_expr_wand with "HT"). iIntros (L2 v2 m2 rt2 ty2 r2) "HT".
    iApply (typed_if_wand with "HT").
    iSplit; iIntros "HT"; iApply type_val; by rewrite !val_of_bool_i2v.
  Qed.

  Lemma type_logical_or E L f e1 e2 T:
    typed_val_expr E L f e1 (λ L1 v1 m1 rt1 ty1 r1,
      typed_if E L1 v1 (v1 ◁ᵥ{f.1, m1} r1 @ ty1)
      (typed_value f.1 (val_of_bool true) (T L1 (val_of_bool true)))
      (typed_val_expr E L1 f e2 (λ L2 v2 m2 rt2 ty2 r2,
        typed_if E L2 v2 (v2 ◁ᵥ{f.1, m2} r2 @ ty2)
          (typed_value f.1 (val_of_bool true) (T L2 (val_of_bool true)))
          (typed_value f.1 (val_of_bool false) (T L2 (val_of_bool false))))))
    ⊢ typed_val_expr E L f (e1 ||{BoolOp, BoolOp, U8} e2)%E T.
  Proof.
    iIntros "HT". rewrite /LogicalOr. iApply type_ife.
    iApply (typed_val_expr_wand with "HT"). iIntros (L1 v m rt ty r) "HT".
    iApply (typed_if_wand with "HT"). iSplit; iIntros "HT".
    1: { iApply type_val. by rewrite !val_of_bool_i2v. }
    iApply type_ife.
    iApply (typed_val_expr_wand with "HT"). iIntros (L2 v2 m2 rt2 ty2 r2) "HT".
    iApply (typed_if_wand with "HT").
    iSplit; iIntros "HT"; iApply type_val; by rewrite !val_of_bool_i2v.
  Qed.

  (** Similar to type_assign, use is formulated with a skip over the expression, in order to allow
    on-demand unblocking. We can't just use any of the potential place access steps, because there might not be any (if it's just a location). So we can't easily use any of the other steps around.
   *)
  Lemma type_use m E L f ot e o (T : typed_val_expr_cont_t) :
    ⌜if o is Na2Ord then False else True⌝ ∗
      typed_read E L f e ot m (λ L2 v rt ty r,
        introduce_with_hooks E L2 (tr 2 ∗ £ num_cred) (λ L3,
          T L3 v MetaNone rt ty r))
    ⊢ typed_val_expr E L f (Use o ot true e)%E T.
  Proof.
    iIntros "[% Hread]" (Φ) "#(LFT & LLCTX) #HE HL Hf HΦ".
    unfold Use.
    wpe_bind.
    iApply ("Hread" $! _ ⊤ with "[//] [//] [//] [//] [$LFT $LLCTX] HE HL Hf").
    iIntros (l) "Hl".
    iApply wpe_fupd.
    rewrite /Use. wpe_bind.
    iApply wpe_fupd.
    iApply (wpe_logical_step with "Hl"); [solve_ndisj.. | ].
    iMod (tr_zero) as "Ha".
    iApply wp_skip.
    iApply (physical_step_intro_tr with "Ha").
    iNext. iIntros "Hat Hcred!>".
    iIntros "(%v & %q & %rt & %ty & %r & %Hlyv & %Hv & Hl & Hv & Hcl)".
    iModIntro. iApply (wpe_logical_step with "Hcl"); [solve_ndisj.. | ].
    iApply (wp_deref with "Hl") => //; try by eauto using val_to_of_loc.
    { destruct o; naive_solver. }
    iApply (physical_step_intro_tr with "Hat").
    iIntros "!> Hat Hcred2 !> %st Hl Hcl".
    iMod ("Hcl" with "Hl Hv") as "(%L' & %rt' & %ty' & %r' & HL & Hf & Hv & HT)".
    iMod ("HT" with "[] [$] HE HL [Hat Hcred2]") as "(%L3 & HL & HT)"; first done.
    { iSplitL "Hat".
      - iApply tr_weaken; last done.
        simpl. unfold num_laters_per_step; lia.
      - iApply lc_weaken; last done.
        simpl. unfold num_laters_per_step, num_cred; lia. }
    by iApply ("HΦ" with "HL Hf Hv HT").
  Qed.
  Lemma type_copy E L f ot e o (T : typed_val_expr_cont_t) :
    ⌜if o is Na2Ord then False else True⌝ ∗
      typed_read E L f e ot ReadDoCopy (λ L2 v rt ty r,
        introduce_with_hooks E L2 (tr 2 ∗ £ num_cred) (λ L3,
          T L3 v MetaNone rt ty r))
    ⊢ typed_val_expr E L f (copy{ot, o} e)%E T.
  Proof.
    unfold Copy.
    apply type_use.
  Qed.
  Lemma type_move E L f ot e o (T : typed_val_expr_cont_t) :
    ⌜if o is Na2Ord then False else True⌝ ∗
      typed_read E L f e ot ReadDoMove (λ L2 v rt ty r,
        introduce_with_hooks E L2 (tr 2 ∗ £ num_cred) (λ L3,
          T L3 v MetaNone rt ty r))
    ⊢ typed_val_expr E L f (move{ot, o} e)%E T.
  Proof.
    unfold Move.
    apply type_use.
  Qed.

  (* TODO move *)
  Lemma num_laters_per_step_linear n m :
    num_laters_per_step (n + m) = num_laters_per_step n + num_laters_per_step m.
  Proof.
    rewrite /num_laters_per_step/=. lia.
  Qed.

  (* This lemma is about AssignSE, which adds a skip around the LHS expression.
     The reason is that we might need to unblock e1 first and only after that get access to the location we need for justifying the actual write
      - so we can't just use the actual write step,
      - and we also cannot use the place access on the LHS itself, because that might not even take a step (if it's just a location).
     *)
  Lemma type_assign E L f ot e1 e2 s fn R o ϝ :
    typed_val_expr E L f e2 (λ L' v m rt ty r,
      ⌜m = MetaNone⌝ ∗
      ⌜if o is Na2Ord then False else True⌝ ∗
      typed_write E L' f e1 ot v ty r (λ L2,
        introduce_with_hooks E L2 (tr 2 ∗ £ num_cred) (λ L3,
        typed_stmt E L3 f s fn R ϝ)))
    ⊢ typed_stmt E L f (e1 <-{ot, o} e2; s) fn R ϝ.
  Proof.
    iIntros "He". iIntros (?) "#(LFT & LLCTX) #HE HL Hf Hcont".
    wps_bind. iApply ("He" with "[$LFT $LLCTX] HE HL Hf").
    iIntros (L' v rt ty r m) "HL Hf Hv (-> & % & He1)".
    wps_bind. iApply ("He1" $! _ ⊤ with "[//] [//] [//] [//] [$LFT $LLCTX] HE HL Hf"). iIntros (l) "HT".
    unfold AssignSE. wps_bind.
    iSpecialize ("HT" with "Hv").
    iApply (wpe_logical_step with "HT"); [solve_ndisj.. | ].
    iMod (tr_zero) as "Ha".
    iApply wp_skip.
    iApply (physical_step_intro_tr with "Ha").
    iNext. iIntros "Ha Hcred !> (Hly & Hl & Hcl)".
    iApply wps_assign; rewrite ?val_to_of_loc //. { destruct o; naive_solver. }
    iMod (fupd_mask_subseteq) as "Hcl_m"; last iApply fupd_intro.
    { destruct o; solve_ndisj. }
    iFrame.
    iMod "Hcl_m" as "_".
    iApply (physical_step_step_upd with "Hcl").
    iApply (physical_step_intro_tr with "Ha").
    iNext. iIntros "Ha Hcred' !> Hcl".
    iMod (fupd_mask_subseteq) as "Hcl_m"; last iApply fupd_intro.
    { destruct o; solve_ndisj. }
    iIntros "Hl".
    (*rewrite num_laters_per_step_linear.*)
    (*iDestruct "Hcred'" as "(Hcred2 & Hcred')".*)
    iMod "Hcl_m" as "_".
    iMod ("Hcl" with "Hl") as "(%L'' & HL & Hf & Hs)".
    iMod ("Hs" with "[] [$] HE HL [Ha Hcred']") as "(%L3 & HL & HT)"; first done.
    { iSplitL "Ha".
      - iApply tr_weaken; last done. simpl. unfold num_laters_per_step; lia.
      -  iApply lc_weaken; last done. simpl. unfold num_cred, num_laters_per_step; lia. }
    by iApply ("HT" with "[$LFT $LLCTX] HE HL Hf").
  Qed.

  Lemma type_mut_addr_of E L f e (T : typed_val_expr_cont_t) :
    typed_addr_of_mut E L f e (λ L v rt ty r, T L v MetaNone rt ty r)
    ⊢ typed_val_expr E L f (&raw{Mut} e)%E T.
  Proof.
    iIntros "HT" (?) "#CTX #HE HL Hf Hcont".
    rewrite /Raw. wpe_bind.
    iApply ("HT" $! _ ⊤ with "[//] [//] [//] CTX HE HL Hf").
    iIntros (l) "HT".
    iDestruct "CTX" as "(LFT & LLCTX)".
    iApply (wpe_logical_step with "HT"); [done.. | ].
    iApply wp_skip. iApply physical_step_intro. iNext.
    iDestruct 1 as (L' rt ty r) "(Hl & HL & Hf & HT)".
    iApply ("Hcont" with "HL Hf Hl HT").
  Qed.
  (* Corresponding lemmas for borrows are in references.v *)


  Import EqNotations.
  (** Entry point for checking reads *)
  Lemma type_read E L f T T' e ot m :
    (** Decompose the expression *)
    IntoPlaceCtx E f e T' →
    T' L (λ L' K l,
      (** Find the type assignment *)
      find_in_context (FindLoc l) (λ '(existT rto (lt1, r1, b, π)),
      ⌜π = f.1⌝ ∗
      (** Check the place access *)
      typed_place E L' f l lt1 r1 UpdStrong b K (λ (L1 : llctx) (κs : list lft) (l2 : loc) (b2 : bor_kind) bmin rti (lt2 : ltype rti) (ri2 : place_rfn rti) (updcx : place_update_ctx rti rto bmin UpdStrong),
        (** Stratify *)
        stratify_ltype_unblock f.1 E L1 StratRefoldOpened l2 lt2 ri2 b2 (λ L2 R rt3 lt3 ri3,
        (** Omitted from the paper: Certify that this stratification is allowed, or otherwise commit to a strong update *)
        prove_place_cond E L2 bmin lt2 lt3 (λ upd,
        (** Require the stratified place to be a value type *)
        (* TODO remove this and instead have a [ltype_read_as] TC or so. Currently this will prevent us from reading from ShrBlocked*)
        cast_ltype_to_type E L2 lt3 (λ ty3,
        (** Finish reading *)
        typed_read_end f.1 E L2 l2 (◁ ty3) ri3 b2 bmin ot m (λ L3 v rt3 ty3 r3 rt2' lt2' ri2' upd2,
        typed_place_finish f.1 E L3 updcx (place_update_kind_res_trans upd upd2) (R ∗ llft_elt_toks κs) l b lt2' ri2' (λ L4,
          T L4 v _ ty3 r3))
      ))))))%I
    ⊢ typed_read E L f e ot m T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ F ????) "#CTX #HE HL Hf HΦ".
    iApply (HT' with "CTX HE HL Hf HT'").
    iIntros (L' K l) "HL Hf". iDestruct 1 as ([rt ([[ty r] π] & ?)]) "(Hl & -> & HP)".
    iApply ("HP" with "[//] [//] CTX HE HL Hf Hl").
    iIntros (L'' κs l2 b2 bmin rti tyli ri updcx) "Hl2 Hs HT HL Hf".
    iApply "HΦ".
    iPoseProof ("HT" with "[//] [//] [//] CTX HE HL Hl2") as "Hb".
    iApply fupd_logical_step. iApply logical_step_fupd.
    iMod "Hb" as "(%L2 & %R & %rt2' & %lt2' & %ri2 & HL & %Hst & Hl2 & HT)".
    iMod ("HT" with "[//] CTX HE HL") as "(HL & %upd & #Hincl & Hcond & %Hst' & HT)".
    iApply (logical_step_wand with "Hl2").
    iIntros "!> (Hl2 & HR)".
    iDestruct "HT" as "(%ty3 & %Heqt & HT)".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Heq"; first apply Heqt.
    iPoseProof (full_eqltype_use F with "CTX HE HL") as "(Hincl' & HL)"; first done; first apply Heqt.
    iMod  ("Hincl'" with "Hl2") as "Hl2".
    iMod ("HT" with "[//] [//] [//] [//] CTX HE HL Hl2") as "Hread".
    iDestruct "Hread" as (q v rt2 ty2' r2) "(% & % & Hl2 & Hv & Hcl)".
    iModIntro. iExists v, q, _, _, _. iR. iR.
    iFrame "Hl2 Hv".
    iApply (logical_step_wand with "Hcl").
    iIntros "Hcl" (st) "Hl2 Hv".
    iMod ("Hcl" $! st with "Hl2 Hv") as (L3 rt4 ty4 r4) "(Hmv & HL & Hcl)".
    iDestruct "Hcl" as "(%rt' & %lt' & %r' & %res & Hl2 & %Hsteq & #Hincl2 & Hcond2 & Hfin)" => /=.

    set (upd_inner := typed_place_finish_upd (place_update_kind_res_trans upd res) lt' r').

    iMod ("Hs" $! upd_inner with "[] Hl2 [] [] [Hcond Hcond2]") as "Hs".
    { simpl. iApply place_update_kind_incl_lub; done. }
    { simpl. rewrite Hsteq Hst'.
      unshelve iSpecialize ("Heq" $! inhabitant inhabitant); [apply _.. | ].
      iPoseProof (ltype_eq_syn_type with "Heq") as "->".
      done. }
    { simpl. done. }
    { simpl.
      iApply (typed_place_cond_trans with "[Hcond]").
      { iApply typed_place_cond_incl; last done.
        iApply place_update_kind_max_incl_l. }
      iApply ltype_eq_place_cond_ty_trans; first iApply "Heq".
      iApply typed_place_cond_incl; last done.
      iApply place_update_kind_max_incl_r. }
    iMod ("Hs" with "HL Hf Hfin") as (upd') "(Hl & %Hst3 & Hcond'' & ? & HR' & ? & HL & Hf & HT)".
    iPoseProof ("HT" with "Hl") as "Hfin".
    iMod ("Hfin" with "[] [$] HE HL [$]") as "(%L4 & HL & HT)"; first done.
    iModIntro. iExists _, _, _, _. iFrame.
  Qed.

  (** [type_read_end] instance that does a copy *)
  Lemma type_read_ofty_copy E L {rt} π b2 bmin l (ty : type rt) r ot `{!Copyable ty} (T : typed_read_end_cont_t bmin rt) :
    (** We have to show that the type allows reads *)
    (⌜ty_has_op_type ty ot MCCopy⌝ ∗ ⌜lctx_bor_kind_alive E L b2⌝ ∗
      (** The place is left as-is *)
      ∀ v, T L v rt ty r rt (◁ ty) (#r) (mkPUKRes UpdBot opt_place_update_eq_refl opt_place_update_eq_refl))
    ⊢ typed_read_end π E L l (◁ ty) (#r) b2 bmin ot ReadDoCopy T.
  Proof.
    iIntros "(%Hot & %Hal & Hs)".
    iIntros (F ????) "#CTX #HE HL".

    set (weak_upd := (mkPUKRes UpdBot opt_place_update_eq_refl opt_place_update_eq_refl)).

    destruct b2 as [ | | ]; simpl.
    - iIntros "Hb".
      iPoseProof (ofty_ltype_acc_owned with "Hb") as "(%ly & %Halg & %Hly & Hsc & Hlb & >(%v & Hl & #Hv & Hcl))"; first done.
      iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
      specialize (ty_op_type_stable Hot) as Halg''.
      assert (ly = ot_layout ot) as ->. { by eapply syn_type_has_layout_inj. }
      iModIntro. iExists _, _, rt, _, _.
      iFrame "Hl Hv".
      iSplitR; first done. iSplitR; first done.
      iApply (logical_step_wand with "Hcl").
      iIntros "Hcl %st Hl _". iMod ("Hcl" with "Hl [//] Hsc Hv") as "Hl".
      iModIntro. iExists L, rt, ty, r.
      iPoseProof (ty_memcast_compat with "Hv") as "Ha"; first done. iFrame "Ha HL".
      iExists _, _, _, weak_upd. iFrame.
      iR. iSplitR. { iApply upd_bot_min. }
      iSplitR. { iApply typed_place_cond_refl_ofty. }
      by iApply "Hs".
    - iIntros "#Hl".
      simpl in Hal.
      iPoseProof (ofty_ltype_acc_shared with "Hl") as "(%ly & %Halg & %Hly & Hlb & >Hl')"; first done.
      assert (ly = ot_layout ot) as ->.
      { specialize (ty_op_type_stable Hot) as ?. eapply syn_type_has_layout_inj; done. }

      iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
      iMod (lctx_lft_alive_tok_noend κ with "HE HL") as (q') "(Htok & HL & Hclose)"; [solve_ndisj | done | ].
      iMod (copy_shr_acc with "CTX Hl' Htok") as "(%ly & >%Hst & >%Hly' & (%q'' & %v & (>Hll & #Hv) & Hclose_l))";
        [solve_ndisj.. | ].
      assert (ly = ot_layout ot) as ->. { by eapply syn_type_has_layout_inj. }

      iDestruct (ty_own_val_has_layout with "Hv") as "#>%Hlyv"; first done.
      iModIntro. iExists _, _, rt, _, _. iFrame "Hll Hv".
      iSplitR; first done. iSplitR; first done.
      iApply logical_step_intro. iIntros (st) "Hll Hv'".
      iMod ("Hclose_l" with "[Hv Hll]") as "Htok".
      { eauto with iFrame. }
      iMod ("Hclose" with "Htok HL") as "HL".
      iPoseProof ("HL_cl" with "HL") as "HL".
      iModIntro. iExists L, rt, ty, r.
      iPoseProof (ty_memcast_compat with "Hv'") as "Hid"; first done. simpl. iFrame.

      iExists _, _, _, weak_upd.
      iFrame "Hl".
      iR. iSplitR. { iApply upd_bot_min. }
      iSplitR. { iApply typed_place_cond_refl_ofty. }
      by iApply "Hs".
    - iIntros "Hl".
      simpl in Hal.
      iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
      iMod (fupd_mask_subseteq lftE) as "HF_cl"; first done.
      iMod (Hal with "HE HL") as (q') "(Htok & HL_cl2)"; [solve_ndisj | ].
      iPoseProof (ofty_ltype_acc_uniq with "CTX Htok HL_cl2 Hl") as "(%ly & %Halg & %Hly & Hlb & >(%v & Hl & Hv & Hcl))"; first done.
      iMod "HF_cl" as "_".
      assert (ly = ot_layout ot) as ->.
      { specialize (ty_op_type_stable Hot) as ?. eapply syn_type_has_layout_inj; done. }
      iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
      iModIntro. iExists _, _, _, _, _. iFrame.
      iSplitR; first done. iSplitR; first done.
      iApply logical_step_mask_mono; last iApply (logical_step_wand with "Hcl"); first done.
      iIntros "[Hcl _]".
      iIntros (st) "Hl #Hv".
      iMod (fupd_mask_mono with "(Hcl Hl Hv)") as "(Hl & HL)"; first done.
      iPoseProof ("HL_cl" with "HL") as "HL".
      iPoseProof (ty_memcast_compat with "Hv") as "Hid"; first done. simpl.
      iModIntro. iExists L, rt, ty, r. iFrame "Hid HL".

      iExists _, _, _, weak_upd.
      iFrame "Hl".
      iR. iSplitR. { iApply upd_bot_min. }
      iSplitR. { iApply typed_place_cond_refl_ofty. }
      by iApply "Hs".
  Qed.
  Definition type_read_ofty_copy_inst := [instance @type_read_ofty_copy].
  Global Existing Instance type_read_ofty_copy_inst | 10.

  (*
  For more generality, maybe have LtypeReadAs lty (λ ty r, ...)
    that gives us an accessor as a type?
    => this should work fine.
     - T ty .. (Shared κ) -∗ LtypeReadAs (ShrBlocked ty) T
     - T ty .. k -∗ LtypeReadAs (◁ ty) T
     -
  How does that work for moves? Well, we cannot move if it isn't an OfTy.
     so there we should really cast first.
  Note here: we should only trigger the copy instance if we can LtypeReadAs as something that is copy.
     So we should really make that a TC and make it a precondition, similar to SimplifyHyp etc.

  And similar for LtypeWriteAs lty (λ ty r, ...)?
    well, there it is more difficult, because it even needs to hold if there are Blocked things below.
    I don't think we can nicely solve that part.
   *)

  (** NOTE instance for moving is defined in value.v *)

  (** Reading products: read each of the components in sequence *)
  (* TODO check if this is the right thing to do.
  Lemma type_read_prod E L π {rt1 rt2} `{ghost_varG Σ rt1} `{ghost_varG Σ rt2} `{ghost_varG Σ ((place_rfn rt1) * (place_rfn rt2))} b2 bmin l (lt1 : lty rt1) (lt2: lty rt2) r1 r2 sl ot
    (T : val → ∀ rt', ghost_varG Σ rt' → lty rt' → place_rfn rt' → type (place_rfn rt1 * place_rfn rt2)%type → (place_rfn rt1 * place_rfn rt2) → iProp Σ) :
    typed_read_end E L π (GetMemberLoc l sl "0") rt1 lt1 r1 b2 bmin ot (λ v1 rt1' _ lt1' r1' ty1 r1t,
      typed_read_end E L π (GetMemberLoc l sl "1") rt2 lt2 r2 b2 bmin ot (λ v2 rt2' _ lt2' r2' ty2 r2t,
        li_tactic (find_gvar_inst_goal (place_rfn rt1' * place_rfn rt2')) (λ _,
        T (v1 ++ v2) (place_rfn rt1' * place_rfn rt2')%type _ (ProdLty lt1' lt2' sl) (PlaceIn (r1', r2')) (pair_t ty1 ty2 sl) (PlaceIn r1t, PlaceIn r2t)))) -∗
    typed_read_end E L π l (place_rfn rt1 * place_rfn rt2) (ProdLty lt1 lt2 sl) (PlaceIn (r1, r2)) b2 bmin ot T.
  Proof.
  Admitted.
  Global Instance type_read_prod_inst E L π {rt1 rt2} `{ghost_varG Σ rt1} `{ghost_varG Σ rt2} `{ghost_varG Σ ((place_rfn rt1) * (place_rfn rt2))} b2 bmin l (lt1 : lty rt1) (lt2: lty rt2) r1 r2 sl ot :
    TypedReadEnd E L π l (ProdLty lt1 lt2 sl) (PlaceIn (r1, r2)) b2 bmin ot | 10 :=
    λ T, i2p (type_read_prod E L π b2 bmin l lt1 lt2 r1 r2 sl ot T).

  (** We can do copy reads from shr-blocked places *)
  Lemma type_read_shr_blocked_copy E L π {rt} `{ghost_varG Σ rt} b2 bmin l (ty : type rt) r κ ot `{!Copyable ty} (T : val → ∀ rt', ghost_varG Σ rt' → lty rt' → place_rfn rt' → type rt → rt → iProp _) :
    (⌜ty.(ty_has_op_type) ot⌝ ∗ ⌜lctx_lft_alive E L κ⌝ ∗ (∀ v, T v rt _ (ShrBlockedLty ty κ) (PlaceIn r) ty r)) -∗
    typed_read_end E L π l rt (ShrBlockedLty ty κ) (PlaceIn r) b2 bmin ot T.
  Proof.
  Admitted.
  Global Instance type_read_shr_blocked_copy_inst E L π {rt} `{ghost_varG Σ rt} b2 bmin l (ty : type rt) r κ ot `{!Copyable ty} :
    TypedReadEnd E L π l (ShrBlockedLty ty κ) (PlaceIn r) b2 bmin ot | 10 :=
    λ T, i2p (type_read_shr_blocked_copy E L π b2 bmin l ty r κ ot T).
  *)



  (* TODO: potentially lemmas for reading from mut-ref and box ltypes.
      (this would be required for full generality, because shr_blocked can be below them)
   *)

  Lemma type_write E L f T T' e ot v rt (ty : type rt) r :
    IntoPlaceCtx E f e T' →
    T' L (λ L' K l, find_in_context (FindLoc l) (λ '(existT rto (lt1, r1, b, π')),
      ⌜π' = f.1⌝ ∗
      typed_place E L' f l lt1 r1 UpdStrong b K (λ (L1 : llctx) (κs : list lft) (l2 : loc) (b2 : bor_kind) (bmin : place_update_kind) rti (lt2 : ltype rti) (ri2 : place_rfn rti) (updcx : place_update_ctx rti rto bmin UpdStrong),
        (* unblock etc. TODO: this requirement is too strong. *)
        stratify_ltype_unblock f.1 E L1 StratRefoldOpened l2 lt2 ri2 b2 (λ L2 R rt3 lt3 ri3,
        (* certify that this stratification is allowed, or otherwise commit to a strong update *)
        prove_place_cond E L2 bmin lt2 lt3 (λ upd,
        (* end writing *)
        typed_write_end f.1 E L2 ot v ty r b2 bmin l2 lt3 ri3 (λ L3 (rt3' : RT) (ty3 : type rt3') (r3 : rt3') upd2,
        typed_place_finish f.1 E L3 updcx (place_update_kind_res_trans upd upd2) (R ∗ llft_elt_toks κs) l b (◁ ty3)%I (#r3) T))))))
    ⊢ typed_write E L f e ot v ty r T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ F ????) "#CTX #HE HL Hf HΦ".
    iApply (HT' with "CTX HE HL Hf HT'").
    iIntros (L' K l) "HL Hf". iDestruct 1 as ([rt1 ([[ty1 r1] π'] & ?)]) "(Hl & -> & HP)".
    iApply ("HP" with "[//] [//] CTX HE HL Hf Hl").
    iIntros (L'' κs l2 bmin b2 rti tyli ri updcx) "Hl2 Hs HT HL Hf".
    iApply ("HΦ"). iIntros "Hv".
    iPoseProof ("HT" with "[//] [//] [//] CTX HE HL Hl2") as "Hb".
    iApply fupd_logical_step. iApply logical_step_fupd.
    iMod "Hb" as "(%L2 & %R & %rt2' & %lt2' & %ri2 & HL & %Hst & Hl2 & HT)".
    iModIntro. iApply (logical_step_wand with "Hl2").
    iIntros "(Hl2 & HR)".
    iMod ("HT" with "[//] CTX HE HL") as "(HL & %upd & #Hincl2 & Hcond & %Hst_eq & HT)".
    iMod ("HT" with "[//] [//] [//] [//] CTX HE HL Hl2 Hv") as "Hwrite".
    iDestruct "Hwrite" as "(% & Hl2 & Hcl)".
    iModIntro. iFrame "Hl2". iSplitR; first done.
    iApply (logical_step_wand with "Hcl").
    iIntros "Hcl Hl2".
    iMod ("Hcl" with "Hl2") as "Hcl".
    iDestruct "Hcl" as "(%L3 & %rt3 & %ty3 & %r3 & %res & HL & Hl2 & %Hsteq & #Hincl2' & Hcond2 & Hfin)".

    set (upd_inner := typed_place_finish_upd (place_update_kind_res_trans upd res) (◁ ty3)%I (#r3)).

    iMod ("Hs" $! upd_inner with "[] Hl2 [] [] [Hcond Hcond2]") as "Hs".
    { simpl. iApply place_update_kind_incl_lub; done. }
    { simpl. rewrite Hst_eq Hsteq. simp_ltypes. done. }
    { simpl. done. }
    { simpl.
      iApply (typed_place_cond_trans with "[Hcond]").
      { iApply typed_place_cond_incl; last done.
        iApply place_update_kind_max_incl_l. }
      iApply typed_place_cond_incl; last done.
      iApply place_update_kind_max_incl_r. }
    iMod ("Hs" with "HL Hf Hfin") as (upd') "(Hl & %Hst3 & Hcond'' & ? & HR' & ? & HL & Hf & Hfin)".
    iPoseProof ("Hfin" with "Hl") as "Hfin".
    iMod ("Hfin" with "[] [$] HE HL [$]") as "(%L4 & HL & HT)"; first done.
    iModIntro. iExists _. iFrame.
  Qed.

  (* TODO: generalize to other places where we can overwrite, but which can't be folded to an ofty *)

  (** Currently have [ty2], want to write [ty]. This allows updates of the refinement type (from rt to rt2).
     This only works if the path is fully owned ([bmin = Owned]).
     We could in principle allow this also for Uniq paths by suspending the mutable reference's contract with [OpenedLtype], but currently we have decided against that. *)
  (* TODO the syntype equality requirement currently is too strong: it does not allow us to go from UntypedSynType to "proper sy types".
     Can we lift the equality requirement in our typesystem?
  *)
  Lemma type_write_ofty_strong E L {rt rt2} π l (ty : type rt) (ty2 : type rt2) r1 (r2 : rt2) v ot `{Hst_eq : !TCDone (ty_syn_type ty MetaNone = ty_syn_type ty2 MetaNone)} (T : typed_write_end_cont_t UpdStrong rt2) :
    (⌜ty_has_op_type ty ot MCNone⌝ ∗
        (ty_ghost_drop ty2 π r2 -∗ T L rt ty r1 (mkPUKRes (allowed:=UpdStrong) UpdStrong I I)))
    ⊢ typed_write_end π E L ot v ty r1 (Owned) UpdStrong l (◁ ty2) (#r2) T.
  Proof.
    iIntros "(%Hot & HT)".
    iIntros (F qL ???) "#CTX #HE HL Hl Hv".
    iPoseProof (ofty_ltype_acc_owned with "Hl") as "(%ly & %Halg & %Hly & Hsc & Hlb & >(%v0 & Hl0 & Hv0 & Hcl))"; first done.
    set (upd_strong := (mkPUKRes (allowed:=UpdStrong) UpdStrong I I)).

    iDestruct (ty_own_val_has_layout with "Hv0") as "%Hlyv0"; first done.
    iDestruct (ty_has_layout with "Hv") as "#(%ly' & % & %Hlyv)".
    assert (ly' = ly) as ->. { eapply syn_type_has_layout_inj; first done. by rewrite Hst_eq. }
    specialize (ty_op_type_stable Hot) as Halg'.
    assert (ly = ot_layout ot) as ->. { by eapply syn_type_has_layout_inj. }
    iModIntro. iSplitR; first done.
    iSplitL "Hl0".
    { iExists v0. iFrame. iSplitR; first done. done. }
    iPoseProof (ty_own_ghost_drop _ _ _ _ _ F with "Hv0") as "Hgdrop"; first done.
    iApply (logical_step_compose with "Hcl").
    iApply (logical_step_compose with "Hgdrop").
    iApply logical_step_intro.
    iIntros "Hgdrop Hcl Hl".
    iPoseProof (ty_own_val_sidecond with "Hv") as "#Hsc'".
    iMod ("Hcl" with "Hl [//] [//] Hv") as "Hl".

    iExists _, rt, ty, r1, upd_strong. iFrame.
    iSplitR. { done. }
    iR. iR.
    iApply ("HT" with "Hgdrop").
  Qed.
  Definition type_write_ofty_strong_inst := [instance @type_write_ofty_strong].
  Global Existing Instance type_write_ofty_strong_inst | 10.

  (** This does not allow updates to the refinement type, rt stays the same. *)
  (* TODO: also allow writes here if the place is not an ofty *)
  (* Write v : r1 @ ty to l : #r2 @ ◁ ty2.
     We first need to show that ty is a subtype of ty2 (in order to handl e
     Afterwards, we obtain l : #r3 @ ◁ ty2 for some r3, as well as the result of ghost-dropping r2 @ ty2. *)
  Lemma type_write_ofty_weak E L {rt} π b2 bmin l (ty ty2 : type rt) r1 r2 v ot (T : typed_write_end_cont_t bmin rt) :
    (∃ r3, owned_subtype π E L false r1 r3 ty ty2 (λ L2,
      ⌜ty_syn_type ty = ty_syn_type ty2⌝ ∗ (* TODO: would be nice to remove this requirement *)
      ⌜ty_has_op_type ty ot MCNone⌝ ∗ ⌜lctx_bor_kind_alive E L2 b2⌝ ∗
      ⌜bor_kind_writeable b2⌝ ∗
      (ty_ghost_drop ty2 π r2 -∗
        T L2 rt ty2 r3 (mkPUKRes UpdBot opt_place_update_eq_refl opt_place_update_eq_refl))))
    ⊢ typed_write_end π E L ot v ty r1 b2 bmin l (◁ ty2) (#r2) T.
  Proof.
    iIntros "(%r3 & HT)".
    iIntros (F qL ???) "#CTX #HE HL Hl Hv".
    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%L2 & Hsub & HL & %Hst_eq & %Hot & %Hal & %Hwriteable & HT)".
    iDestruct ("Hsub") as "(#%Hly_eq & _ & Hsub)".
    iPoseProof ("Hsub" with "Hv") as "Hv".

    set (weak_upd := (mkPUKRes UpdBot opt_place_update_eq_refl opt_place_update_eq_refl)).

    destruct b2 as [ | | ]; simpl.
    - iPoseProof (ofty_ltype_acc_owned with "Hl") as "(%ly & %Halg & %Hly & #Hsc & _ & >(%v0 & Hl & Hv0 & Hcl))"; first done.
      iDestruct (ty_own_val_has_layout with "Hv0") as "%"; first done.
      iDestruct (ty_has_layout with "Hv") as "(%ly'' & % & %)".
      assert (ly'' = ly) as ->. { by eapply syn_type_has_layout_inj. }
      specialize (ty_op_type_stable Hot) as ?.
      assert (ly = ot_layout ot) as ->. { eapply syn_type_has_layout_inj; first done. by rewrite -Hst_eq. }
      iModIntro. iSplitR; first done. iSplitL "Hl".
      { iExists v0. iFrame. done. }
      iPoseProof (ty_own_ghost_drop _ _ _ _ _ F with "Hv0") as "Hgdrop"; first done.
      iApply (logical_step_compose with "Hcl").
      iApply (logical_step_compose with "Hgdrop").
      iApply logical_step_intro. iIntros "Hgdrop Hcl Hl".
      (*iPoseProof (ty_own_val_sidecond with "Hv") as "#Hsc'".*)
      iMod ("Hcl" with "Hl [] [] Hv") as "Hl"; [done.. | ].
      iModIntro.
      iExists _, _, ty2, r3, weak_upd.
      iFrame.
      iR.
      iSplitR. { iApply upd_bot_min. }
      iSplitR. { iApply typed_place_cond_refl_ofty. }
      iApply ("HT" with "Hgdrop").
    - (* Shared, so it can't be writeable *)
      done.
    - simpl in Hal.
      iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
      iMod (fupd_mask_subseteq lftE) as "HF_cl"; first done.
      iMod (Hal with "HE HL") as "(%q & Htok & Htok_cl)"; first done.
      iPoseProof (ofty_ltype_acc_uniq lftE with "CTX Htok Htok_cl Hl") as "(%ly & %Halg & %Hly & Hlb & >Hb)"; first done.
      iMod "HF_cl" as "_".
      iDestruct "Hb" as "(%v0 & Hl & Hv0 & Hcl)".
      iDestruct (ty_own_val_has_layout with "Hv0") as "%"; first done.
      iDestruct (ty_has_layout with "Hv") as "(%ly'' & % & %)".
      assert (ly'' = ly) as ->. { by eapply syn_type_has_layout_inj. }
      specialize (ty_op_type_stable  Hot) as ?.
      assert (ly = ot_layout ot) as ->. { eapply syn_type_has_layout_inj; first done. by rewrite -Hst_eq. }
      iModIntro. iSplitR; first done. iSplitL "Hl".
      { iExists v0. iFrame. done. }
      iPoseProof (ty_own_ghost_drop _ _ _ _ _ F with "Hv0") as "Hgdrop"; first done.
      iApply (logical_step_compose with "Hgdrop").
      iApply (logical_step_mask_mono lftE); first done.
      iApply (logical_step_compose with "Hcl").
      iApply logical_step_intro. iIntros "[Hcl _] Hgdrop Hl".
      iMod (fupd_mask_mono with "(Hcl Hl Hv)") as "(Hl & HL)"; [done.. | ].
      iPoseProof ("HL_cl" with "HL") as "HL".
      iModIntro.
      iExists _, _, ty2, r3, weak_upd. iFrame.
      iR.
      iSplitR. { iApply upd_bot_min. }
      iSplitR. { iApply typed_place_cond_refl_ofty. }
      iApply ("HT" with "Hgdrop").
  Qed.
  Definition type_write_ofty_weak_inst := [instance @type_write_ofty_weak].
  Global Existing Instance type_write_ofty_weak_inst | 20.

  (** For now, cast other ltypes to [OfTy]. Longer term, we should have specialized rules for them. *)
  Definition type_write_end_fold_to_ofty E L {rt} π ot v (ty : type rt) r1 b2 bmin l (lt : ltype rt) r T :
    cast_ltype_to_type E L lt (λ ty',
      typed_write_end π E L ot v ty r1 b2 bmin l (◁ ty') r T)
    ⊢ typed_write_end π E L ot v ty r1 b2 bmin l lt r T.
  Proof.
    iIntros "(%ty' & %Heqt & HT)".
    iIntros (?????) "#CTX #HE HL Hl Hv".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Heq"; first apply Heqt.
    iDestruct ("Heq" $! _ _) as "(#Hincl & _)".
    iMod (ltype_incl_use with "Hincl Hl") as "Hl"; first done.
    iDestruct "Hincl" as "(%Hst & _)".
    iMod ("HT" with "[] [] [] [] CTX HE HL Hl Hv") as "(% & $ & Hstep)"; [done.. | ].
    iR. iApply (logical_step_wand with "Hstep").
    iModIntro. iIntros "HT Hl".
    iMod ("HT" with "Hl") as "(%L2 & % & % & % & % & HL & Hl & %Hst' & ? & Hcond & ?)".
    iFrame.
    rewrite Hst. iR.
    iApply ltype_eq_place_cond_ty_trans; last done.
    done.
  Qed.
  Definition type_write_end_fold_to_ofty_inst := [instance @type_write_end_fold_to_ofty].
  Global Existing Instance type_write_end_fold_to_ofty_inst | 100.

  (* TODO move *)
  (*
  Fixpoint try_fold_lty {rt} (lt : lty rt) : option (type rt) :=
    match lt with
    | BlockedLty _ _ => None
    | ShrBlockedLty _ _ => None
    | OfTy ty => Some ty
    | MutLty lt κ =>
        ty ← try_fold_lty lt;
        Some (mut_ref ty κ)
    | ShrLty lt κ =>
        (* TODO *)
        (*ty ← try_fold_lty lt;*)
        (*Some (shr_ref ty κ)*)
        None
    | BoxLty lt =>
        (* TODO *)
        (*ty ← try_fold_lty lt;*)
        (*Some (box ty)*)
        None
    | ProdLty lt1 lt2 sl =>
        ty1 ← try_fold_lty lt1;
        ty2 ← try_fold_lty lt2;
        if decide (sl = pair_layout_spec ty1 ty2) then Some (pair_t ty1 ty2) else None
    end.
  Lemma try_fold_lty_correct {rt} (lt : lty rt) (ty : type rt) :
    try_fold_lty lt = Some ty →
    ⊢ ltype_eq lt (◁ ty)%I.
  Proof.
  Abort.

  (* The following lemmas are really somewhat awkward, because of the whole "pushing down" thing: we are really overwriting the MutLty(etc.) here, not its contents. But still, we need to replicate these lemmas that are really similar, because we can't phrase the ownership generically. *)

  (* Basically for Uniq ownership. We need to take care that we are not disrupting the contract of the mutable reference that may be above it (in the b2=Uniq case). *)
  Lemma type_write_mutlty E L {rt} π (T : ∀ rt3, type rt3 → rt3 → iProp Σ) b2 bmin l (ty : type (place_rfn rt * gname)) (lt2 : lty rt) r1 r2 v κ ot :
    (* the core must be equivalent to some type, of which the type we are writing must be a subtype *)
    ∃ ty2, ⌜try_fold_lty (ltype_core (MutLty lt2 κ)) = Some ty2⌝ ∗
      (weak_subtype E L ty ty2 (⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗ ⌜lctx_bor_kind_alive E L b2⌝ ∗ ⌜bor_kind_writeable bmin⌝ ∗ T _ ty2 r1)) -∗
    typed_write_end π E L ot v _ ty r1 b2 bmin l _ (MutLty lt2 κ) (PlaceIn r2) T.
  Proof.
  Abort.
  (* No restrictions if we fully own it *)
  Lemma type_write_mutlty_strong E L {rt rt2} π (T : ∀ rt3, type rt3 → rt3 → iProp Σ) l (ty : type rt) (lt2 : lty rt2) r1 r2 v κ wl wl' ot :
    ⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗ ⌜ty_syn_type ty = PtrSynType⌝ ∗ T _ ty r1 -∗
    typed_write_end π E L ot v _ ty r1 (Owned wl) (Owned wl') l _ (MutLty lt2 κ) (PlaceIn r2) T.
  Proof.
  Abort.

  (* Same lemmas for box *)
  Lemma type_write_boxlty E L {rt} π (T : ∀ rt3, type rt3 → rt3 → iProp Σ) b2 bmin l (ty : type (place_rfn rt)) (lt2 : lty rt) r1 r2 v ot :
    (* the core must be equivalent to some type, of which the type we are writing must be a subtype *)
    ∃ ty2, ⌜try_fold_lty (ltype_core (BoxLty lt2)) = Some ty2⌝ ∗
      (weak_subtype E L ty ty2 (⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗ ⌜lctx_bor_kind_alive E L b2⌝ ∗ ⌜bor_kind_writeable bmin⌝ ∗ T _ ty2 r1)) -∗
    typed_write_end π E L ot v _ ty r1 b2 bmin l _ (BoxLty lt2) (PlaceIn r2) T.
  Proof.
  Abort.
  (* No restrictions if we fully own it *)
  Lemma type_write_boxlty_strong E L {rt rt2} π (T : ∀ rt3, type rt3 → rt3 → iProp Σ) l (ty : type rt) (lt2 : lty rt2) r1 r2 v wl wl' ot :
    ⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗ ⌜ty_syn_type ty = PtrSynType⌝ ∗ T _ ty r1 -∗
    typed_write_end π E L ot v _ ty r1 (Owned wl) (Owned wl') l _ (BoxLty lt2) (PlaceIn r2) T.
  Proof.
  Abort.

  (* Same for sharing. This works, again, because we are writing to the place the shared reference is stored in, not below the shared reference. *)
  Lemma type_write_shrlty E L {rt} π (T : ∀ rt3, type rt3 → rt3 → iProp Σ) b2 bmin l (ty : type (place_rfn rt)) (lt2 : lty rt) r1 r2 v κ ot :
    (* the core must be equivalent to some type, of which the type we are writing must be a subtype *)
    ∃ ty2, ⌜try_fold_lty (ltype_core (ShrLty lt2 κ)) = Some ty2⌝ ∗
      (weak_subtype E L ty ty2 (⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗ ⌜lctx_bor_kind_alive E L b2⌝ ∗ ⌜bor_kind_writeable bmin⌝ ∗ T _ ty2 r1)) -∗
    typed_write_end π E L ot v _ ty r1 b2 bmin l _ (ShrLty lt2 κ) (PlaceIn r2) T.
  Proof.
  Abort.
  (* No restrictions if we fully own it *)
  Lemma type_write_shrlty_strong E L {rt rt2} π (T : ∀ rt3, type rt3 → rt3 → iProp Σ) l (ty : type rt) (lt2 : lty rt2) r1 r2 v κ wl wl' ot :
    ⌜ty.(ty_has_op_type) ot MCCopy⌝ ∗ ⌜ty_syn_type ty = PtrSynType⌝ ∗ T _ ty r1 -∗
    typed_write_end π E L ot v _ ty r1 (Owned wl) (Owned wl') l _ (ShrLty lt2 κ) (PlaceIn r2) T.
  Proof.
  Abort.
   *)

  (* TODO: product typing rule.
    This will be a bit more complicated, as we essentially need to require that directly below the product, nothing is blocked.
    Of course, with nested products, this gets more complicated...
   *)

  Lemma opt_place_update_eq_strong {rt1 rt2} bmin (Heq : bmin = UpdStrong) :
    opt_place_update_eq bmin rt1 rt2.
  Proof.
    unfold opt_place_update_eq.
    rewrite Heq.
    exact I.
  Defined.

  Lemma type_addr_of_mut E L f (e : expr) (T : typed_addr_of_mut_cont_t) T' :
    IntoPlaceCtx E f e T' →
    T' L (λ L1 K l, find_in_context (FindLoc l) (λ '(existT rto (lt1, r1, b, π)),
      ⌜π = f.1⌝ ∗
      (* place *)
      typed_place E L1 f l lt1 r1 UpdStrong b K (λ L2 κs (l2 : loc) (b2 : bor_kind) (bmin : place_update_kind) rti (lt2 : ltype rti) (ri2 : place_rfn rti) updcx,
        (* We need to be able to do a strong update *)
        ∃ (Heqmin : bmin = UpdStrong),
        typed_addr_of_mut_end f.1 E L2 l2 lt2 ri2 b2 UpdStrong (λ L3 rtb tyb rb rt' lt' r',
          typed_place_finish f.1 E L3 updcx (mkPUKRes UpdStrong I (opt_place_update_eq_strong bmin Heqmin)) (llft_elt_toks κs) l b lt' r' (λ L4,
            (* in case lt2 is already an AliasLtype, the simplify_hyp instance for it will make sure that we don't actually introduce that assignment into the context *)
            l2 ◁ₗ[π, Owned] ri2 @ lt2 -∗
            T L4 l2 rtb tyb rb)))))
    ⊢ typed_addr_of_mut E L f e T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ F ???) "#CTX #HE HL Hf HΦ".
    iApply (HT' with "CTX HE HL Hf HT'").
    iIntros (L1 K l) "HL Hf". iDestruct 1 as ([rto [[[lt1 r1] b] π]]) "(Hl & -> & Hplace)" => /=.
    iApply ("Hplace" with "[//] [//] CTX HE HL Hf Hl").
    iIntros (L2 κs l2 bmin b2 rti ltyi ri updcx) "Hl2 Hs (%Heqmin & Hcont) HL Hf".
    iApply "HΦ".
    iApply logical_step_fupd.
    iSpecialize ("Hcont" with "[//] [//] [//] CTX HE HL Hl2").

    iApply (logical_step_wand with "Hcont").
    iDestruct 1 as (L3 rtb tyb rb rt' lt' r') "(Htyb & Hl2 & Hl2' & %Hst & HL & HT)".

    set (upd_strong := (mkPUKRes UpdStrong I (opt_place_update_eq_strong bmin Heqmin))).
    set (upd_inner := typed_place_finish_upd upd_strong lt' r').
    iMod ("Hs" $! upd_inner with "[] Hl2 [] [$] [$]") as "Hs".
    { simpl. by rewrite Heqmin. }
    { simpl. done. }
    iMod ("Hs" with "HL Hf HT") as (upd') "(Hl & %Hsteq & Hcond & ? & ? & ? & HL & Hf & HT)".
    iDestruct ("HT" with "Hl") as "HT".
    iMod ("HT" with "[//] [$] HE HL [$]") as "(%L4 & HL & HT)".
    iModIntro.
    iExists L4, _, tyb, rb. iFrame.
    by iApply "HT".
  Qed.
  (* NOTE: instances for [typed_addr_of_mut_end] are in alias_ptr.v *)

  (** Top-level rule for creating a mutable borrow *)
  Lemma type_borrow_mut E L f T T' e κ (orty : option rust_type) :
    (** Decompose the expression *)
    IntoPlaceCtx E f e T' →
    T' L (λ L1 K l,
      (** Find the type assignment in the context *)
      find_in_context (FindLoc l) (λ '(existT rto (lt1, r1, b, π)),
      ⌜π = f.1⌝ ∗
      (** Check the place access *)
      typed_place E L1 f l lt1 r1 UpdStrong b K (λ L2 κs (l2 : loc) (b2 : bor_kind) (bmin : place_update_kind) rti (lt2 : ltype rti) (ri2 : place_rfn rti) updcx,
        (* We need to be able to borrow at least at [κ] *)
        ⌜lctx_place_update_kind_outlives E L2 bmin [κ]⌝ ∗
        (** Omitted from paper: find the credit context to give the borrow-step a time receipt *)
        find_in_context (FindCreditStore) (λ '(n, m),
        (** Stratify *)
        stratify_ltype_unblock f.1 E L2 StratRefoldFull l2 lt2 ri2 b2 (λ L3 R rt2' lt2' ri2',
        (** Omitted from paper: Certify that this stratification is allowed *)
        prove_place_cond E L3 bmin lt2 lt2' (λ upd,
        (** finish borrow *)
        typed_borrow_mut_end f.1 E L3 κ l2 orty lt2' ri2' b2 bmin (λ (γ : gname) rt3 (lt3 : ltype rt3) (r3 : place_rfn rt3) ty4 r4 upd',
        (** return the credit store *)
        credit_store n m -∗
        typed_place_finish f.1 E L3 updcx (place_update_kind_res_trans upd upd') (R ∗ llft_elt_toks κs) l b
          lt3 r3 (λ L4, T L4 (val_of_loc l2) γ rt3 ty4 r4))))))))
    ⊢ typed_borrow_mut E L f e κ orty T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ F ????) "#CTX #HE HL Hf HΦ".
    iApply (HT' with "CTX HE HL Hf HT'").
    iIntros (L1 K l) "HL Hf". iDestruct 1 as ([rt1 [[[ty1 r1] ?] π]]) "(Hl & -> & HP)".
    iApply ("HP" $! _ F with "[//] [//] CTX HE HL Hf Hl").
    iIntros (L2 κs l2 bmin b2 rti tyli ri updcx) "Hl2 Hs HT HL2 Hf".
    iDestruct "HT" as "(%Houtl & HT)".
    iPoseProof (lctx_place_update_kind_outlives_use with "HE HL2") as "#Houtl".
    { apply Houtl. }

    iDestruct "HT" as ([n m]) "(Hstore & HT)".
    iPoseProof (credit_store_borrow_receipt with "Hstore") as "(Hat & Hstore)".
    (* bring the place type in the right shape *)
    iApply ("HΦ" with "Hat").
    iPoseProof ("HT" with "[//] [//] [//] CTX HE HL2 Hl2") as "Hb".
    iApply fupd_logical_step. iApply logical_step_fupd.
    iMod "Hb" as "(%L3 & %R & %rt' & %lt' & %r' & HL & %Hst & Hl2 & HT)".
    iMod ("HT" with "[//] CTX HE HL") as "(HL & %upd & #Hincl & Hcond & %Hsteq & HT)".

    iApply (logical_step_wand with "Hl2").
    iIntros "!> (Hl2 & HR) !> Hcred Hat".
    iPoseProof ("Hstore" with "Hat") as "Hstore".
    iPoseProof (ltype_own_has_layout with "Hl2") as "(%ly & %Halg & %Hly)".

    iMod ("HT" $! F with "[//] [//] [//] CTX HE HL Hl2 Hcred") as "Hbor".
    iDestruct "Hbor" as (γ ly' rt2 ty2 r2 upd') "(Hobs & Hbor & Hsc & %Halg' & Hlb & Hblock & #Hincl2 & Hcond' & %Hst_eq & HL & HT)".
    iSpecialize ("HT" with "Hstore").
    assert (ly' = ly) as ->. { move: Hst_eq Halg' Halg. simp_ltypes => -> ??. by eapply syn_type_has_layout_inj. }

    set (upd_inner := typed_place_finish_upd (place_update_kind_res_trans upd upd') (BlockedLtype ty2 κ)%I (👻 γ)).

    iMod ("Hs" $! upd_inner with "[] Hblock [] [] [Hcond Hcond']") as "Hs".
    { simpl. iApply place_update_kind_incl_lub; done. }
    { simpl. iPureIntro. simp_ltypes. rewrite Hsteq Hst_eq//.  }
    { simpl. done. }
    { simpl.
      iApply (typed_place_cond_trans with "[Hcond]").
      { iApply typed_place_cond_incl; last done.
        iApply place_update_kind_max_incl_l. }
      iApply typed_place_cond_incl; last done.
      iApply place_update_kind_max_incl_r. }
    iMod ("Hs" with "HL Hf HT") as (upd'') "(Hl & %Hst3 & Hcond'' & ? & HR' & ? & HL & Hf & HT)".
    iPoseProof ("HT" with "Hl") as "Hfin".
    iMod ("Hfin" with "[] [$] HE HL [$]") as "(%L4 & HL & HT)"; first done.
    iModIntro. iExists _. iFrame.
    iL. done.
  Qed.


  (* Problem:
    - mutrefs will now allow UpdStrong.
      But we still don't want to allow this, because we don't really want to open the mutref above.

      Maybe I want another level that isn't semantically different from UpdStrong, but still signifies that we shouldn't do tis.

    Maybe I should have another flag that has no semantic meaning but is purely a heuristic.
    Depending on that flag I can then decide what to actually do.

    Or I dont' emit a typing hint in the frontend if it's below a reference.

   *)

  (** Finish a mutable borrow *)
  Lemma type_borrow_mut_end_owned E L π κ l orty (rt : RT) (ty : type rt) (r : rt) bmin (T : typed_borrow_mut_end_cont_t bmin rt) :
    ⌜lctx_place_update_kind_incl E L (UpdUniq [κ]) bmin⌝ ∗
    (** The lifetime at which we borrow still needs to be alive *)
    ⌜lctx_lft_alive E L κ⌝ ∗
    (* Interpret the typing hint *)
    interpret_typing_hint E L orty bmin ty r (λ rt' ty' r' upd,
      (** Then, the place becomes blocked *)
      (∀ γ, T γ rt' (BlockedLtype ty' κ) (PlaceGhost γ) ty' r'
        (place_update_kind_res_trans upd (mkPUKRes (UpdUniq [κ]) eq_refl opt_place_update_eq_refl))))
    ⊢ typed_borrow_mut_end π E L κ l orty (◁ ty) (#r) (Owned) bmin T.
  Proof.
    simpl. iIntros "(%Hincl & %Hal & HT)".
    iIntros (F ???) "#CTX #HE HL Hl Hcred".
    iPoseProof (lctx_place_update_kind_incl_use with "HE HL") as "#Hincl1"; first apply Hincl.

    iMod ("HT" with "[//] [//] [//] CTX HE HL") as "(%rt2 & %ty2 & %r2 & %upd & HL & #Hincl2 & #Hcond1 & #Hincl3 & HT)".
    iPoseProof (type_ltype_incl_owned_in  with "Hincl2") as "Hincl2'".
    iMod (ltype_incl_use with "Hincl2' Hl") as "Hl"; first done.

    set (upd1 := (mkPUKRes (allowed:=bmin)(rt1:=rt2) (UpdUniq [κ]) eq_refl opt_place_update_eq_refl)).

    (* owned *)
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & (%r' & Hrfn & Hb))".
    iDestruct "Hrfn" as "<-".
    iDestruct "CTX" as "(LFT & LLFT)".
    iMod (fupd_mask_subseteq lftE) as "Hcl_m"; first done.
    iMod (gvar_alloc r2) as (γ) "[Hauth Hobs]".
    iMod (bor_create lftE κ (∃ r' : rt2, gvar_auth γ r' ∗ |={lftE}=> l ↦: ty2.(ty_own_val) π r' MetaNone) with "LFT [Hauth Hb]") as "[Hb Hinh]"; first solve_ndisj.
    { iNext. eauto with iFrame. }
    iMod "Hcl_m" as "_".
    iModIntro. iExists γ, ly, rt2, ty2, r2, _.
    iSpecialize ("HT" $! γ).
    iFrame "Hb HL Hlb Hsc HT".
    iSplitL "Hobs".
    { done. }
    iSplitR; first done.
    iSplitL "Hinh Hcred".
    { rewrite ltype_own_blocked_unfold /blocked_lty_own.
      iExists ly. iSplitR; first done. iSplitR; first done. iSplitR; first done.
      iFrame "Hlb". iDestruct "Hcred" as "(Hcred1 & Hcred2 & Hcred)".
      iIntros "Hdead". iMod ("Hinh" with "Hdead") as "Hinh".
      iApply (lc_fupd_add_later with "Hcred1").
      iNext.
      iDestruct "Hinh" as "(%r' & Hauth & ?)". iMod (gvar_obs_persist with "Hauth") as "Hobs".
      by iFrame. }
    iSplitR. { simpl. iApply place_update_kind_incl_lub; done. }
    iSplitL. {
      simpl. iApply typed_place_cond_trans.
      { iApply typed_place_cond_incl; last done.
        iApply place_update_kind_max_incl_l. }
      iApply typed_place_cond_incl; last iApply ofty_blocked_place_cond; last iApply place_update_kind_incl_refl.
      iApply place_update_kind_max_incl_r. }
    iPoseProof (ltype_incl_syn_type with "Hincl2'") as "->".
    by simp_ltypes.
  Qed.
  Definition type_borrow_mut_end_owned_inst := [instance @type_borrow_mut_end_owned].
  Global Existing Instance type_borrow_mut_end_owned_inst | 20.

  (* NOTE: this can't use typing hints right now, as [interpret_typing_hint] only shows inclusion, not equality *)
  Lemma type_borrow_mut_end_uniq E L π κ l orty (rt : RT) (ty : type rt) (r : rt) κ' γ bmin (T : typed_borrow_mut_end_cont_t bmin rt) :
    ⌜lctx_place_update_kind_incl E L (UpdUniq [κ]) bmin⌝ ∗
    ⌜lctx_lft_incl E L κ κ'⌝ ∗
    (** The lifetime at which we borrow still needs to be alive *)
    ⌜lctx_lft_alive E L κ⌝ ∗
    (** Then, the place becomes blocked *)
    (∀ γ, T γ rt (BlockedLtype ty κ) (PlaceGhost γ) ty r (mkPUKRes (UpdUniq [κ]) eq_refl opt_place_update_eq_refl))
    ⊢ typed_borrow_mut_end π E L κ l orty (◁ ty) (#r) (Uniq κ' γ) bmin T.
  Proof.
    simpl. iIntros "(%Hincl & %Hincl2 & %Hal & HT)".
    iIntros (F ???) "#CTX #HE HL Hl Hcred".
    iPoseProof (lctx_place_update_kind_incl_use with "HE HL") as "#Hincl1"; first apply Hincl.
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl1'"; first apply Hincl2.
    (* mutable bor: reborrow *)
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & Hcreda & Hrfn & Hb)".

    iDestruct "CTX" as "(LFT & LLFT)".
    iDestruct "Hcred" as "(Hcred1 & Hcred2 & Hcred)".
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod "Hb".
    iMod (pinned_bor_rebor_full _ _ κ with "LFT [] [Hcred1 Hcred2] Hb") as "(Hb & Hcl_b)"; [done | | | ].
    { done. }
    { iEval (rewrite lc_succ). iFrame. }
    simpl.
    iMod (gvar_alloc r) as (γ') "[Hauth' Hobs']".

    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & HL_cl)".
    iMod (Hal with "HE HL") as "(%q' & Htok & Htok_cl)"; first done.

    (* put in the refinement *)
    iMod (bor_create lftE κ (∃ r', gvar_obs γ r' ∗ gvar_auth γ' r') with "LFT [Hrfn Hauth']") as "(Hrfn & Hcl_rfn)"; first done.
    { iNext. iExists _. iFrame. }
    iMod (bor_combine with "LFT Hb Hrfn") as "Hb"; first done.

    iMod (bor_acc_cons with "LFT Hb Htok") as "(Hb & Hcl_b')"; first done.
    iDestruct "Hb" as "((%r1 & >Hauth1 & Hb1) & (%r2 & >Hobs1 & >Hauth2))".
    iPoseProof (gvar_agree with "Hauth2 Hobs'") as "->".
    iPoseProof (gvar_agree with "Hauth1 Hobs1") as "->".
    set (bor' := ((∃ r' : rt, gvar_auth γ' r' ∗ (|={lftE}=> l ↦: ty_own_val ty π r' MetaNone)))%I).
    iMod ("Hcl_b'" $! bor' with "[Hobs1 Hauth1] [Hauth2 Hb1]") as "(Ha & Htok)".
    { iNext. iIntros "Ha".
      iDestruct "Ha" as "(%r'' & Hauth & Ha)".
      iMod (gvar_update r'' with "Hauth1 Hobs1") as "(Hauth1 & Hobs1)".
      iModIntro. iNext. iSplitL "Ha Hauth1"; eauto with iFrame. }
    { iNext. iExists _. iFrame. }
    iMod ("Htok_cl" with "Htok") as "HL".
    iPoseProof ("HL_cl" with "HL") as "HL".
    iMod "Hcl_F" as "_".
    iModIntro. iExists γ', _. iSpecialize ("HT" $! γ').
    iFrame.
    iR. iR. iR.
    (* we've got some leftover credits here *)
    iSplitL "Hcl_b Hcl_rfn Hcreda".
    { rewrite ltype_own_blocked_unfold /blocked_lty_own.
      iExists _. iR. iR. iR. iR.
      iDestruct "Hcreda" as "($ & $)".
      iIntros "#Hdead". iMod ("Hcl_b" with "Hdead") as "$".
      iMod ("Hcl_rfn" with "Hdead") as "Hrfn".
      iDestruct "Hrfn" as "(%r'' & >Hobs & >Hauth)".
      iMod (gvar_obs_persist with "Hauth") as "Hauth".
      iModIntro. iExists _, _. iFrame. done. }
    iR. iL.
    iApply ofty_blocked_place_cond.
    iApply place_update_kind_incl_refl.
  Qed.
  Definition type_borrow_mut_end_uniq_inst := [instance @type_borrow_mut_end_uniq].
  Global Existing Instance type_borrow_mut_end_uniq_inst | 20.

  (* Low-priority default instance to fold to [OfTy] *)
  Lemma typed_borrow_mut_end_fold π E L κ l orty {rt} (lt : ltype rt) r b bmin T :
    cast_ltype_to_type E L lt (λ ty,
      typed_borrow_mut_end π E L κ l orty (◁ ty) r b bmin T)
    ⊢ typed_borrow_mut_end π E L κ l orty lt r b bmin T.
  Proof.
    unfold cast_ltype_to_type, typed_borrow_mut_end.
    iIntros "(%ty & %Heqt & HT)".
    iIntros (????) "#CTX #HE HL Hl Hcred".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hincl"; [apply Heqt | ].
    iDestruct ("Hincl" $! _ _) as "(Hincl1 & _)".
    iPoseProof (ltype_incl_syn_type with "Hincl1") as "%Hst0".
    iMod (ltype_incl_use with "Hincl1 Hl") as "Hl"; first done.
    iMod ("HT" with "[//] [//] [//] CTX HE HL Hl Hcred") as "(%γ & %ly & % & %ty2 & % & %res & Hrfn & ? & ? & %Hst & ? & hl & ? & Hcond & %Hst' & HL & HT)".
    iFrame. iR.
    rewrite -Hst' -Hst0. iL.
    iApply (ltype_eq_place_cond_trans with "[//] Hcond").
  Qed.
  Definition typed_borrow_mut_end_fold_inst := [instance @typed_borrow_mut_end_fold].
  Global Existing Instance typed_borrow_mut_end_fold_inst | 1000.

  Lemma type_borrow_shr E L f T T' e κ orty :
    IntoPlaceCtx E f e T' →
    T' L (λ L1 K l, find_in_context (FindLoc l) (λ '(existT rto (lt1, r1, b, π)),
      ⌜π = f.1⌝ ∗
      (* place *)
      typed_place E L1 f l lt1 r1 UpdStrong b K (λ L2 κs (l2 : loc) (b2 : bor_kind) bmin rti (lt2 : ltype rti) (ri2 : place_rfn rti) updcx,
      (* stratify *)
      stratify_ltype_unblock f.1 E L2 StratRefoldOpened l2 lt2 ri2 b2 (λ L3 R rt2' lt2' ri2',
      (* certify that this stratification is allowed, or otherwise commit to a strong update *)
      prove_place_cond E L3 bmin lt2 lt2' (λ upd,
      (* finish borrow *)
      typed_borrow_shr_end f.1 E L3 κ l2 orty lt2' ri2' b2 bmin (λ rt3 (lt3 : ltype rt3) (r3 : place_rfn rt3) (ty4 : type rt3) r4 upd',
      (* return toks *)
      typed_place_finish f.1 E L3 updcx (place_update_kind_res_trans upd upd') (R ∗ llft_elt_toks κs) l b lt3 r3
        (λ L4, T L4 (val_of_loc l2) rt3 ty4 (#r4))))))))
    ⊢ typed_borrow_shr E L f e κ orty T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ F ????) "#CTX #HE HL Hf HΦ".
    iApply (HT' with "CTX HE HL Hf HT'").
    iIntros (L1 K l) "HL Hf". iDestruct 1 as ([rt1 [[[ty1 r1] ?] π]]) "(Hl & -> & HP)".
    iApply ("HP" $! _ F with "[//] [//] CTX HE HL Hf Hl").
    iIntros (L2 κs l2 bmin b2 rti tyli ri updcx) "Hl2 Hs HT HL Hf".
    (* bring the place type in the right shape *)
    iApply ("HΦ").
    iPoseProof ("HT" with "[//] [//] [//] CTX HE HL Hl2") as "Hb".
    iApply fupd_logical_step.
    iMod "Hb" as "(%L3 & %R & %rt2' & %lt2' & %ri2 & HL & %Hst & Hl2 & HT)".
    iMod ("HT" with "[//] CTX HE HL") as "(HL & %upd & #Hincl2 & Hcond & %Hsteq & HT)".
    (* needs two logical steps: one for stratification and one for initiating sharing.
       - that means: creating a reference will now be two skips.
       - this shouldn't be very problematic. *)
    iApply (logical_step_wand with "Hl2").
    iIntros "!>(Hl2 & HR)".
    iApply fupd_logical_step.
    iPoseProof (ltype_own_has_layout with "Hl2") as "(%ly & %Halg & %Hly)".

    iPoseProof ("HT" $! F with "[//] [//] [//] [//] CTX HE HL Hl2") as ">Hb".
    iModIntro. iApply logical_step_fupd. iApply (logical_step_wand with "Hb").
    iIntros "Ha !> Hcred".
    iMod ("Ha" with "Hcred") as "(%ly' & %rt2 & %lt2 & %r2 & %ty3 & %upd' & HT)".
    iDestruct "HT" as "(Hshr & %Halg' & Hlb & Hsc & Hblocked & Hcond' & %Hsteq1 & %Hsteq2 & #Hincl & HL & HT)".
    assert (ly' = ly) as ->. {
      move: Halg' Halg.
      rewrite -Hsteq2.
      by eapply syn_type_has_layout_inj. }
    (*iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Heq"; first apply Heq.*)

    set (upd_inner := typed_place_finish_upd (place_update_kind_res_trans upd upd') lt2 (#r2)).

    iMod ("Hs" $! upd_inner with "[] Hblocked [] [] [Hcond Hcond']") as "Hs".
    { simpl. iApply place_update_kind_incl_lub; done. }
    { simpl. rewrite Hsteq Hsteq1//. }
    { simpl. done. }
    { simpl.
      iApply (typed_place_cond_trans with "[Hcond]").
      { iApply typed_place_cond_incl; last done.
        iApply place_update_kind_max_incl_l. }
      iApply typed_place_cond_incl; last done.
      iApply place_update_kind_max_incl_r. }

    iMod ("Hs" with "HL Hf HT") as (?) "(Hl & %Hst3 & Hcond'' & ? & HR' & ? & HL & Hf & HT)".
    iPoseProof ("HT" with "Hl") as "Hfin".
    iMod ("Hfin" with "[] [$] HE HL [$]") as "(%L4 & HL & HT)"; first done.
    iModIntro. iExists _. iFrame.
    iL. done.
  Qed.

  Lemma type_borrow_shr_end_owned E L π κ l orty {rt : RT} (ty : type rt) (r : rt) bmin (T : typed_borrow_shr_end_cont_t bmin rt):
    ⌜lctx_place_update_kind_incl E L (UpdUniq [κ]) bmin⌝ ∗
    ⌜lctx_lft_alive E L κ⌝ ∗
    ⌜Forall (lctx_lft_alive E L) (ty_lfts ty)⌝ ∗
    find_in_context (FindNaOwn π) (λ E,
    na_own π E -∗
    (T rt (ShrBlockedLtype ty κ) (#r) ty r (mkPUKRes (UpdUniq [κ]) eq_refl opt_place_update_eq_refl)))
    ⊢ typed_borrow_shr_end π E L κ l orty (◁ ty) (#r) (Owned) bmin T.
  Proof.
    simpl. iIntros "(%Hincl & %Hal & %Hal' & %E' & Hna & HT)".
    iPoseProof (na_own_empty with "Hna") as "#Hna'".
    iSpecialize ("HT" with "Hna").
    iIntros (F ????) "#[LFT LLCTX] #HE HL Hl".
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & Hcl_L)".
    iDestruct (Hincl with "HL HE") as "#Hincl".
    iMod (lctx_lft_alive_tok_noend (κ ⊓ (lft_intersect_list (ty_lfts ty))) with "HE HL") as "Ha"; first done.
    { eapply lctx_lft_alive_intersect; first done. by eapply lctx_lft_alive_intersect_list. }
    iDestruct "Ha" as "(%q' & Htok & HL & Hcl_L')".
    (* owned *)
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & %r' & Hrfn & Hl)".
    iMod (fupd_mask_mono with "Hl") as "(%v & Hl & Hv)"; first done.
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod (bor_create lftE κ (∃ v, l ↦ v ∗ v ◁ᵥ{π, MetaNone} r' @ ty)%I with "LFT [Hv Hl]") as "(Hb & Hinh)"; first done.
    { eauto with iFrame. }
    iMod "Hcl_F" as "_".
    (*iPoseProof (place_rfn_interp_owned_share' with "Hrfn") as "#Hrfn'".*)
    rewrite ty_lfts_unfold.
    iPoseProof (ty_share _ F with "[$LFT $LLCTX] Hna' Htok [//] [//] Hlb Hb") as "Hshr"; first done.
    iApply logical_step_fupd.
    iApply (logical_step_compose with "Hshr").
    iApply logical_step_intro.
    iModIntro. iIntros "(#Hshr & Htok) !> Hcred1".
    iMod ("Hcl_L'" with "Htok HL") as "HL".
    iPoseProof ("Hcl_L" with "HL") as "HL".
    set (upd := (mkPUKRes (UpdUniq [κ]) eq_refl opt_place_update_eq_refl)).
    iExists ly, rt, (ShrBlockedLtype ty κ), _, ty, upd.
    iFrame "Hshr Hlb Hsc HL". iSplitR; first done.
    iSplitL "Hinh Hcred1".
    { iModIntro. rewrite ltype_own_shrblocked_unfold /shr_blocked_lty_own.
      iExists ly. iFrame "Hlb Hsc". iSplitR; first done. iSplitR; first done.
      iExists r'. iSplitR; first done. iFrame "Hshr".
      iIntros "Hdead". iMod ("Hinh" with "Hdead"). iApply (lc_fupd_add_later with "Hcred1").
      iNext. eauto with iFrame. }
    iModIntro.
    iSplitR.
    { simpl. iExists eq_refl.
      simp_ltypes. iSplitR. { iIntros (??). iApply ltype_eq_refl. }
      iApply shr_blocked_imp_unblockable.
    }
    simp_ltypes. iR. iR. iR.
    iDestruct "Hrfn" as "->".
    iApply "HT".
  Qed.
  Definition type_borrow_shr_end_owned_inst := [instance @type_borrow_shr_end_owned].
  Global Existing Instance type_borrow_shr_end_owned_inst | 20.

  Lemma type_borrow_shr_end_uniq E L π κ l orty {rt : RT} (ty : type rt) (r : rt) bmin κ' γ (T : typed_borrow_shr_end_cont_t bmin rt):
    ⌜lctx_place_update_kind_incl E L (UpdUniq [κ]) bmin⌝ ∗
    ⌜lctx_lft_incl E L κ κ'⌝ ∗
    ⌜lctx_lft_alive E L κ⌝ ∗
    ⌜Forall (lctx_lft_alive E L) (ty_lfts ty)⌝ ∗
    find_in_context (FindNaOwn π) (λ E, na_own π E -∗
    (T rt (ShrBlockedLtype ty κ) (#r) ty r (mkPUKRes (UpdUniq [κ]) eq_refl opt_place_update_eq_refl)))
    ⊢ typed_borrow_shr_end π E L κ l orty (◁ ty) (#r) (Uniq κ' γ) bmin T.
  Proof.
    simpl. iIntros "(%Hincl & %Hincl2 & %Hal & %Hal' & %E' & Hna & HT)".
    iPoseProof (na_own_empty with "Hna") as "#Hna'".
    iSpecialize ("HT" with "Hna").
    (* basically, we do the same as for creating a mutable reference, but then proceed to do sharing *)
    iIntros (F ????) "#(LFT & LLCTX) #HE HL Hl".
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl2"; first apply Hincl2.
    iPoseProof (llctx_interp_acc_noend with "HL") as "(HL & Hcl_L)".
    iDestruct (Hincl with "HL HE") as "#Hincl".
    iMod (lctx_lft_alive_tok_noend (κ ⊓ (lft_intersect_list (ty_lfts ty))) with "HE HL") as "Ha"; first done.
    { eapply lctx_lft_alive_intersect; first done. by eapply lctx_lft_alive_intersect_list. }
    iDestruct "Ha" as "(%q' & Htok & HL & Hcl_L')".
    (* uniq *)
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & #Hsc & #Hlb & Hcred & Hrfn & Hl)".
    iMod (fupd_mask_subseteq lftE) as "Hcl_F"; first done.
    iMod "Hl".
    iDestruct "Hcred" as "((Hcred1 & Hcred2 & Hcred) & Hat)".
    iMod (pinned_bor_rebor_full _ _ κ with "LFT [] [Hcred1 Hcred2] Hl") as "(Hl & Hl_cl)"; first done.
    { done. }
    { iSplitL "Hcred1"; iFrame. }
    iMod "Hcl_F" as "_".

    rewrite -lft_tok_sep. iDestruct "Htok" as "(Htok1 & Htok2)".
    iMod (bor_exists_tok with "LFT Hl Htok1") as "(%r' & Hl & Htok1)"; first done.
    iMod (bor_sep with "LFT Hl") as "(Hauth & Hl)"; first done.
    iDestruct "Hcred" as "(Hcred1 & Hcred)".
    iMod (bor_fupd_later with "LFT Hl Htok1") as "Ha"; [done.. | ].
    iApply (lc_fupd_add_later with "Hcred1").
    iNext. iMod ("Ha") as "(Hl & Htok1)".

    iMod (place_rfn_interp_mut_share' with "LFT Hrfn Hauth Htok1") as "(#Hrfn & Hmut & Hauth & Htok1)"; first done.
    iPoseProof (ty_share _ F with "[$LFT $LLCTX] Hna' [Htok1 Htok2] [] [] Hlb Hl") as "Hstep".
    { done. }
    { rewrite ty_lfts_unfold -lft_tok_sep. iFrame. }
    { done. }
    { done. }
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_intro_tr with "Hat").
    iModIntro. iIntros "Hat Hcred'". iModIntro.
    iIntros "(#Hshr & Htok) Hcred1".
    iDestruct "Hrfn" as "<-".

    set (upd := (mkPUKRes (UpdUniq [κ]) eq_refl opt_place_update_eq_refl)).
    iExists ly, rt, (ShrBlockedLtype ty κ), r, ty, upd. iFrame.
    iR. iR. iR.
    rewrite lft_tok_sep.
    rewrite ty_lfts_unfold.
    iMod ("Hcl_L'" with "Htok HL") as "HL".
    iPoseProof ("Hcl_L" with "HL") as "$".

    iDestruct "Hmut" as ">Hmut". iR.
    iSplitL "Hauth Hmut Hat Hcred' Hl_cl".
    { rewrite ltype_own_shrblocked_unfold /shr_blocked_lty_own.
      iExists ly. iR. iR. iR. iR. iExists _. iR.
      iFrame "∗ #". iModIntro.
      iApply tr_weaken; last done. simpl. unfold num_laters_per_step; lia. }
    iSplitR.
    { iApply ofty_shr_blocked_place_cond. iApply place_update_kind_incl_refl. }
    iR. iR.
    done.
  Qed.
  Definition type_borrow_shr_end_uniq_inst := [instance @type_borrow_shr_end_uniq].
  Global Existing Instance type_borrow_shr_end_uniq_inst | 20.

  Lemma type_borrow_shr_end_shared E L π κ l orty {rt : RT} (ty : type rt) (r : rt) κ' bmin (T : typed_borrow_shr_end_cont_t bmin rt) :
    ⌜lctx_lft_incl E L κ κ'⌝ ∗
    (T rt (◁ ty) (#r) ty r (mkPUKRes UpdBot eq_refl opt_place_update_eq_refl))
    ⊢ typed_borrow_shr_end π E L κ l orty (◁ ty) (#r) (Shared κ') bmin T.
  Proof.
    simpl. iIntros "(%Hincl & HT)".
    iIntros (F ????) "#[LFT LLCTX] #HE HL #Hl".
    iPoseProof (lctx_lft_incl_incl with "HL HE") as "#Hincl"; first apply Hincl.
    iModIntro. iApply logical_step_intro. iIntros "Hcred".
    rewrite ltype_own_ofty_unfold /lty_of_ty_own.
    iDestruct "Hl" as "(%ly & %Halg & %Hly & Hsc & Hlb & %r' & Hrfn & #Hl)".
    iDestruct "Hl" as "-#Hl". iMod (fupd_mask_mono with "Hl") as "#Hl"; first done.
    set (upd := (mkPUKRes UpdBot eq_refl opt_place_update_eq_refl)).
    iExists ly, rt, (◁ ty)%I, r, ty, upd.
    iDestruct "Hrfn" as "<-".
    iPoseProof (ty_shr_mono with "Hincl Hl") as "$".
    iR. iFrame "Hlb Hsc". iModIntro.
    iSplitR. { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists ly. iR. iR. by iFrame "∗ #". }
    iFrame. iSplitR. { iApply typed_place_cond_refl_ofty. }
    iR. iR. iApply upd_bot_min.
  Qed.
  Definition type_borrow_shr_end_shared_inst := [instance @type_borrow_shr_end_shared].
  Global Existing Instance type_borrow_shr_end_shared_inst | 20.

  (* Low-priority default instance to fold to [OfTy] *)
  (* TODO: should have more specific instances for different ltypes, or a mechanism to extract a sharing predicate from an ltype *)
  Lemma typed_borrow_shr_end_fold π E L κ l orty {rt} (lt : ltype rt) r b bmin T :
    cast_ltype_to_type E L lt (λ ty,
      typed_borrow_shr_end π E L κ l orty (◁ ty) r b bmin T)
    ⊢ typed_borrow_shr_end π E L κ l orty lt r b bmin T.
  Proof.
    unfold cast_ltype_to_type, typed_borrow_shr_end.
    iIntros "(%ty & %Heqt & HT)".
    iIntros (?????) "#CTX #HE HL Hl".
    iPoseProof (full_eqltype_acc with "CTX HE HL") as "#Hincl"; [apply Heqt | ].
    iDestruct ("Hincl" $! _ _) as "(Hincl1 & _)".
    iPoseProof (ltype_incl_syn_type with "Hincl1") as "%Hst0".
    iMod (ltype_incl_use with "Hincl1 Hl") as "Hl"; first done.
    iMod ("HT" with "[//] [//] [//] [//] CTX HE HL Hl") as "Ha".
    iApply (logical_step_wand with "Ha").
    iModIntro. iIntros "HT Hcred".
    iMod ("HT" with "Hcred") as "(%ly & % & %lt2 & % & %ty2 & %res & Hl & %Hst1 & ? & ? & Hl' & Hcond & %Hst2 & %Hst3 & ? & HL & HT)".
    iFrame. iR.
    rewrite -Hst3 -Hst2 -Hst0. iL.
    iApply (ltype_eq_place_cond_trans with "[//] Hcond").
  Qed.
  Definition typed_borrow_shr_end_fold_inst := [instance @typed_borrow_shr_end_fold].
  Global Existing Instance typed_borrow_shr_end_fold_inst | 1000.

  (** statements *)
  Inductive CtxFoldExtract : Type :=
    | CtxFoldExtractAllInit (κ : lft)
    | CtxFoldExtractAll (κ : lft).

  Inductive CtxFoldResolve : Type :=
    | CtxFoldResolveAllInit
    | CtxFoldResolveAll.

  Inductive CtxFoldStratify : Type :=
    | CtxFoldStratifyAllInit (ma : StratifyAscendMode)
    | CtxFoldStratifyAll (ma : StratifyAscendMode).

  Inductive CtxFoldCloseInv : Type :=
    | CtxFoldCloseInvAllInit (κs : list lft)
    | CtxFoldCloseInvAll (κs : list lft).

  Lemma type_goto E L f b fn R s ϝ :
    fn.(f_code) !! b = Some s →
    introduce_with_hooks E L (£ num_cred) (λ L2,
      typed_stmt E L2 f s fn R ϝ)
    ⊢ typed_stmt E L f (Goto b) fn R ϝ.
  Proof.
    iIntros (HQ) "Hs". iIntros (?) "#CTX #HE HL Hf Hcont".
    iApply wps_goto => //.
    iApply physical_step_intro_lc. iIntros "Hcred". iIntros "!> !>".
    iMod ("Hs" with "[] CTX HE HL Hcred") as "(%L2 & HL & HT)"; first done.
    by iApply ("HT" with "CTX HE HL Hf").
  Qed.

  (** Goto a block if we have already proved it with a particular precondition [P]. *)
  (* This is not in Lithium goal shape, but that's fine since it is only manually applied by automation. *)
  (* We might also want to stratify here -- but this is difficult, because we'd need a second logical step.
     Instead, we currently insert an annotation for that in the frontend. *)
  Lemma type_goto_precond E L f P b fn R ϝ :
    typed_block P f b fn R ϝ ∗
    (* [true] so that we can deinitialize with [owned_subltype_step] *)
    prove_with_subtype E L true ProveDirect (P E L) (λ L' _ R,
      ⌜L = L'⌝ ∗ True (* TODO maybe relax and require inclusion of contexts or so. *))
    ⊢ typed_stmt E L f (Goto b) fn R ϝ.
  Proof.
    iIntros "(Hblock & Hsubt)". iIntros (?) "#CTX #HE HL Hf Hcont".
    iMod ("Hsubt" with "[] [] [] CTX HE HL") as "(%L' & % & %R2 & HP & HL & HT)"; [done.. | ].
    simpl.
    iDestruct ("HT") as "(<- & _)".
    iSpecialize ("Hblock" with "CTX HE HL Hf [HP]").
    { iApply (logical_step_wand with "HP"). iIntros "($ & _)". }
    by iApply "Hblock".
  Qed.

  Lemma typed_block_rec f fn R P b ϝ s :
    fn.(f_code) !! b = Some s →
    (□ (∀ E L, (□ typed_block P f b fn R ϝ) -∗
      introduce_with_hooks E L (P E L) (λ L2,
        typed_stmt E L2 f s fn R ϝ)))
    ⊢ typed_block P f b fn R ϝ.
  Proof.
    iIntros (Hs) "#Hb". iLöb as "IH".
    iIntros (? E L) "#CTX #HE HL Hf HP Hcont".
    iApply wps_goto; first done.
    iApply (physical_step_step_upd with "HP").
    iApply physical_step_intro. iNext.
    iIntros "HP".
    iMod ("Hb" with "IH [] CTX HE HL HP") as "(%L2 & HL & Hs)"; first done.
    by iApply ("Hs" with "CTX HE HL Hf").
  Qed.

  (** current goal: Goto.
     Instead of just jumping there, we can setup an invariant [P] on ownership and the lifetime contexts.
     Then instead prove: wp of the block, but in the context we can persistently assume the WP of the goto with the same invariant already. *)
  (* Note: these need to be manually applied. *)
  Lemma typed_goto_acc E L f fn R {A} (P : A → elctx → llctx → iProp Σ) b ϝ s :
    fn.(f_code) !! b = Some s →
    (* TODO maybe also stratify? *)
    (∃ params,
    prove_with_subtype E L true ProveDirect (P params E L) (λ L' _ R2,
      ⌜L' = L⌝ ∗ (* TODO maybe relax if we have a separate condition on lifetime contexts *)
      (* gather up the remaining ownership *)
      accu (λ Q,
      (∀ E L, (□ typed_block (λ E L, P params E L ∗ Q) f b fn R ϝ) -∗
          introduce_with_hooks E L (P params E L ∗ Q) (λ L2,
          typed_stmt E L2 f s fn R ϝ)))))
    ⊢ typed_stmt E L f (Goto b) fn R ϝ.
  Proof.
    iIntros (Hlook) "(%params & Hsubt)". iIntros (?) "#CTX #HE HL Hf Hcont".
    iMod ("Hsubt" with "[] [] [] CTX HE HL") as "(%L' & % & %R2 & Hinv & HL & HT)"; [done.. | ].
    iDestruct ("HT") as "(-> & Hrec)".
    rewrite /accu.
    iDestruct "Hrec" as "(%Q & HQ & #Hrec)".
    iApply (typed_block_rec with "Hrec CTX HE HL Hf [Hinv HQ]").
    - done.
    - iApply (logical_step_wand with "Hinv"). iIntros "(? & ?)". iFrame.
    - done.
  Qed.

  (* A variant where [P] is first instantiated with the refinement of some local variable *)
  Lemma typed_goto_acc' E L f fn R b ϝ s {rt : RT} (l : loc) {A} (P : RT_xt rt → A → elctx → llctx → iProp Σ) :
    fn.(f_code) !! b = Some s →
    find_in_context (FindLoc l) (λ '(existT rt' (lt, r, bk, π)),
    l ◁ₗ[π, bk] r @ lt -∗
    ∃ (Heq : rt = rt') (r' : RT_xt rt) (a : A),
    ⌜r = # $# (rew [RT_xt] Heq in r')⌝ ∗
    ⌜π = f.1⌝ ∗
    (* TODO maybe also stratify? *)
    prove_with_subtype E L true ProveDirect (P r' a E L) (λ L' _ R2,
      ⌜L' = L⌝ ∗ (* TODO maybe relax if we have a separate condition on lifetime contexts *)
      (* gather up the remaining ownership *)
      accu (λ Q,
      (∀ E L, (□ typed_block (λ E L, P r' a E L ∗ Q) f b fn R ϝ) -∗
          introduce_with_hooks E L (P r' a E L ∗ Q) (λ L2,
          typed_stmt E L2 f s fn R ϝ)))))
    ⊢ typed_stmt E L f (Goto b) fn R ϝ.
  Proof.
    iIntros (Hlook) "Hsubt". iIntros (?) "#CTX #HE HL Hf Hcont".
    unfold FindLoc.
    iDestruct "Hsubt" as "(%x & Hlt & HT)". simpl in *.
    destruct x as [rt' (((lt & r) & ?) & ?)].
    iDestruct ("HT" with "Hlt") as "(%Heq & %r' & %a & -> & -> & Hsubt)".
    iMod ("Hsubt" with "[] [] [] CTX HE HL") as "(%L' & % & %R2 & Hinv & HL & HT)"; [done.. | ].
    iDestruct ("HT") as "(-> & Hrec)".
    rewrite /accu.
    iDestruct "Hrec" as "(%Q & HQ & #Hrec)".
    iApply (typed_block_rec with "Hrec CTX HE HL Hf [Hinv HQ]").
    - done.
    - iApply (logical_step_wand with "Hinv"). iIntros "(? & ?)". iFrame.
    - done.
  Qed.

  Lemma type_assert E L f e s fn R ϝ :
    typed_val_expr E L f e (λ L' v m rt ty r,
      ⌜m = MetaNone⌝ ∗
      typed_assert E L' f v ty r s fn R ϝ)
    ⊢ typed_stmt E L f (assert{BoolOp}: e; s) fn R ϝ.
  Proof.
    iIntros "He". iIntros (?) "#CTX #HE HL Hf Hcont". wps_bind.
    iApply ("He" with "CTX HE HL Hf"). iIntros (L' v rt ty r m) "HL Hf Hv (-> & Hs)".
    iDestruct ("Hs" with "CTX HE HL Hf Hv") as (?) "(HL & Hf & Hs)".
    iApply wps_assert_bool; [done.. | ].
    iApply physical_step_intro; iNext.
    by iApply ("Hs" with "CTX HE HL Hf").
  Qed.

  Lemma type_if E L f e s1 s2 fn R join ϝ :
    typed_val_expr E L f e (λ L' v m rt ty r,
      typed_if E L' v (v ◁ᵥ{f.1, m} r @ ty)
          (typed_stmt E L' f s1 fn R ϝ) (typed_stmt E L' f s2 fn R ϝ))
    ⊢ typed_stmt E L f (if{BoolOp, join}: e then s1 else s2) fn R ϝ.
  Proof.
    iIntros "He". iIntros (?) "#CTX #HE HL Hf Hcont". wps_bind.
    iApply ("He" with "CTX HE HL Hf"). iIntros (L' v m rt ty r) "HL Hf Hv Hs".
    iDestruct ("Hs" with "Hv") as "(%b & % & Hs)".
    iApply wps_if_bool; [done|..].
    iApply physical_step_intro; iNext.
    by destruct b; iApply ("Hs" with "CTX HE HL Hf").
  Qed.

  Lemma type_switch E L f it e m ss def fn R ϝ:
    typed_val_expr E L f e (λ L' v ma rt ty r,
      ⌜ma = MetaNone⌝ ∗
      typed_switch E L' f v rt ty r it m ss def fn R ϝ)
    ⊢ typed_stmt E L f (Switch it e m ss def) fn R ϝ.
  Proof.
    iIntros "He" (?) "#CTX #HE HL Hf Hcont".
    have -> : (Switch it e m ss def) = (W.to_stmt (W.Switch it (W.Expr e) m (W.Stmt <$> ss) (W.Stmt def)))
      by rewrite /W.to_stmt/= -!list_fmap_compose list_fmap_id.
    iApply tac_wps_bind; first done.
    rewrite /W.to_expr /W.to_stmt /= -list_fmap_compose list_fmap_id.

    iApply ("He" with "CTX HE HL Hf"). iIntros (L' v ma rt ty r) "HL Hf Hv (-> & Hs)".
    iDestruct ("Hs" with "Hv") as (z Hn) "Hs".
    iAssert (⌜∀ i : nat, m !! z = Some i → is_Some (ss !! i)⌝%I) as %?. {
      iIntros (i ->). iDestruct "Hs" as (s ->) "_"; by eauto.
    }
    iApply wps_switch; [done|done|..].
    iApply physical_step_intro; iNext.
    destruct (m !! z) => /=.
    - iDestruct "Hs" as (s ->) "Hs". by iApply ("Hs" with "CTX HE HL Hf").
    - by iApply ("Hs" with "CTX HE HL Hf").
  Qed.

  Lemma type_exprs E L f s e fn R ϝ :
    (typed_val_expr E L f e (λ L2 v m rt ty r,
      introduce_with_hooks E L2 (v ◁ᵥ{f.1, m} r @ ty) (λ L3,
        typed_stmt E L3 f s fn R ϝ)))
    ⊢ typed_stmt E L f (ExprS e s) fn R ϝ.
  Proof.
    iIntros "Hs". iIntros (?) "#CTX #HE HL Hf Hcont". wps_bind.
    iApply ("Hs" with "CTX HE HL Hf").
    iIntros (L' v m rt ty r) "HL Hf Hv Hs".
    iApply wps_exprs.
    iApply physical_step_intro; iNext.
    iMod ("Hs" with "[] CTX HE HL Hv") as "(%L2 & HL & HT)"; first done.
    by iApply ("HT" with "CTX HE HL Hf").
  Qed.

  Definition local_fresh (x : var_name) (locals : list var_name) := x ∉ locals.
  Global Typeclasses Opaque local_fresh.
  Global Arguments local_fresh : simpl never.

  Lemma type_local_live E L f st x s fn R ϝ :
    li_tactic (compute_layout_goal st) (λ ly,
      find_in_context (FindFrameLocals f) (λ locals : list var_name,
        ⌜local_fresh x locals⌝ ∗
        (∀ l : name_hint_ty (String.append "local_" x) loc, allocated_locals f (x :: locals) -∗
              x is_live{f, st} l -∗
              l ◁ₗ[f.1, Owned] .@ (◁ uninit st) -∗
              typed_stmt E L f s fn R ϝ)))
    ⊢ typed_stmt E L f (local_live{st} x; s) fn R ϝ.
  Proof.
    unfold compute_layout_goal. destruct f as [π f].
    iIntros "(%ly & %Hst & %locals & Hlocals & %Hfresh & HT)".
    iIntros (?) "#CTX HE HL Hf Hpost". simpl.
    iApply (wps_local_live with "Hf Hlocals"); [done.. | ].
    iApply physical_step_intro. iNext.
    iIntros (l) "Hx Hframe Hlocals Hl %Hly".
    iPoseProof ("HT" with "Hlocals Hx [Hl]") as "Hs".
    { rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iExists _. iR. iR. iR.
      iPoseProof (heap_pointsto_loc_in_bounds with "Hl") as "#Hlb".
      rewrite length_replicate. iR.
      iExists _. iR. iModIntro. iExists _. iFrame.
      rewrite uninit_own_spec. iR.
      iExists _. iR. rewrite /has_layout_val length_replicate//. }
    iApply ("Hs" with "CTX HE HL Hframe Hpost").
  Qed.

  Definition remove_local (locals : list var_name) (x : var_name) :=
    list_difference locals [x].
  Global Arguments remove_local : simpl never.
  Global Typeclasses Opaque remove_local.

  Lemma type_local_dead E L f x s fn R ϝ :
    find_in_context (FindFrameLocals f) (λ locals : list var_name,
    if decide (x ∈ locals) then
      find_in_context (FindLocal f x) (λ '(st, l),
      li_tactic (simplify_local_list_goal (remove_local locals x)) (λ locals',
        prove_with_subtype E L true ProveDirect (l ◁ₗ[f.1, Owned] .@ ◁ uninit st) (λ L2 κs R2,
          introduce_with_hooks E L2 R2 (λ L3,
          li_clear l ((allocated_locals f locals' -∗ typed_stmt E L3 f s fn R ϝ))))))
    else (allocated_locals f locals -∗ typed_stmt E L f s fn R ϝ))
    ⊢ typed_stmt E L f (local_dead x; s) fn R ϝ.
  Proof.
    destruct f as [π f].
    iIntros "(%locals & Hlocals & HT)".
    case_decide.
    - iDestruct "HT" as "(%stl & Hx & HT)".
      destruct stl as [st l]. simpl in *.
      unfold LocalDeadSt.
      iIntros (?) "#CTX #HE HL Hf Hpost".
      unfold simplify_local_list_goal.
      iDestruct "HT" as "(%locals' & <- & HT)".
      iMod ("HT" with "[] [] [] CTX HE HL") as "(%L2 & %κs & %R2 & Hstep & HL & HT)"; [done.. | ].
      simpl.
      iApply wps_skip.
      iApply (physical_step_logical_step with "Hstep").
      iApply physical_step_intro. iNext.
      iIntros "(Hl & HR)".
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iDestruct "Hl" as "(%ly & %Hst & %Hlyl & _ & _ & % & <- & Ha)".
      iMod (fupd_mask_mono with "Ha") as "Ha"; first done.
      iDestruct "Ha" as "(%v & Hl & Hv)".
      iPoseProof (ty_own_val_has_layout with "Hv") as "%Hlyv"; first done.
      iApply (wps_local_dead with "Hf Hlocals Hx [Hl]").
      { simpl in Hst. done. }
      { iExists _. iFrame. done. }
      iApply physical_step_intro. iNext.
      iIntros "Hf Hlocals".
      iMod ("HT" with "[] CTX HE HL HR") as "(%L3 & HL & HT)"; first done.
      iApply ("HT" with "Hlocals CTX HE HL Hf Hpost").
    - unfold LocalDeadSt.
      iIntros (?) "#CTX #HE HL Hf Hpost".
      simpl.
      iApply wps_skip. iApply physical_step_intro. iNext.
      iApply (wps_local_dead_nop with "Hf Hlocals").
      { done. }
      iApply physical_step_intro. iNext.
      iIntros "Hf Hlocals".
      iApply ("HT" with "Hlocals CTX HE HL Hf Hpost").
  Qed.


  Lemma type_skips E L f s fn R ϝ :
    ((£num_cred -∗ typed_stmt E L f s fn R ϝ)) ⊢ typed_stmt E L f (SkipS s) fn R ϝ.
  Proof.
    iIntros "Hs". iIntros (?) "#CTX #HE HL Hf Hcont".
    iApply wps_skip.
    iApply physical_step_intro_lc; iIntros "Hcred !>!>".
    by iApply ("Hs" with "Hcred CTX HE HL Hf").
  Qed.

  Lemma type_skips' E L f s fn R ϝ :
    typed_stmt E L f s fn R ϝ ⊢ typed_stmt E L f (SkipS s) fn R ϝ.
  Proof.
    iIntros "Hs". iApply type_skips. iIntros "Hcred".
    done.
  Qed.

  Lemma typed_stmt_annot_skip {A} E L f (a : A) n s fn R ϝ :
    typed_stmt E L f s fn R ϝ ⊢ typed_stmt E L f (annot{n}: a; s) fn R ϝ.
  Proof.
    iIntros "Hs". iIntros (?) "#CTX #HE HL Hf Hcont".
    iApply wps_annot. iApply physical_stepN_intro.
    by iApply ("Hs" with "CTX HE HL Hf").
  Qed.

  Lemma typed_expr_assert_type π E L n sty v {rt} (ty : type rt) r m T :
    (∃ lfts, named_lfts lfts ∗
      (named_lfts lfts -∗ li_tactic (interpret_rust_type_goal lfts sty) (λ '(existT _ ty2),
        ∃ r2, subsume_full E L false (v ◁ᵥ{π, m} r @ ty) (v ◁ᵥ{π, m} r2 @ ty2) (λ L2 R2, R2 -∗ T L2 v m _ ty2 r2))))%I
    ⊢ typed_annot_expr E L π n (AssertTypeAnnot sty) v (v ◁ᵥ{π, m} r @ ty) T.
  Proof.
    iIntros "(%lfts & Hnamed & HT)". iPoseProof ("HT" with "Hnamed") as "HT".
    rewrite /interpret_rust_type_goal. iDestruct "HT" as "(%rt2 & %ty2 & %r2 & HT)".
    iIntros "#CTX #HE HL Hv".
    iApply step_fupdN_intro; first done. iNext.
    iMod ("HT" with "[] [] [] CTX HE HL Hv") as "(%L2 & %R2 & >(Hv & HR2) & HL & HT)"; [done.. | ].
    iModIntro. iExists _, _, _, _, _. iFrame. by iApply ("HT" with "HR2").
  Qed.
  Definition typed_expr_assert_type_inst := [instance @typed_expr_assert_type].
  Global Existing Instance typed_expr_assert_type_inst.

  (** ** Handling of lifetime-related annotations *)

  Lemma introduce_with_hooks_maybe_inherit_none E L P T :
    introduce_with_hooks E L P T
    ⊢ introduce_with_hooks E L (MaybeInherit None P) T.
  Proof.
    iIntros "HT" (??) "#CTX #HE HL Hinh".
    rewrite /MaybeInherit.
    iMod ("Hinh" with "[//]") as "HP".
    iApply ("HT" with "[//] CTX HE HL HP").
  Qed.
  Definition introduce_with_hooks_maybe_inherit_none_inst := [instance @introduce_with_hooks_maybe_inherit_none].
  Global Existing Instance introduce_with_hooks_maybe_inherit_none_inst.

  Lemma introduce_with_hooks_maybe_inherit_some E L κ P T :
    introduce_with_hooks E L (Inherit κ P) T
    ⊢ introduce_with_hooks E L (MaybeInherit (Some κ) P) T.
  Proof.
    iIntros "HT" (??) "#HE HL Hinh".
    rewrite /MaybeInherit. iApply ("HT" with "[//] HE HL Hinh").
  Qed.
  Definition introduce_with_hooks_maybe_inherit_some_inst := [instance @introduce_with_hooks_maybe_inherit_some].
  Global Existing Instance introduce_with_hooks_maybe_inherit_some_inst.


  (** Introducing inheritances *)
  Variant iterate_find_dead :=
    | IterateFindDead (κs : list lft)
  .
  Lemma iterate_with_hooks_find_dead_nil E L T :
    T L (IterateFindDead [])
    ⊢ iterate_with_hooks E L (IterateFindDead []) T.
  Proof.
    iIntros "HT". iIntros (??) "CTX HE HL".
    iModIntro. iFrame.
  Qed.
  Definition iterate_with_hooks_find_dead_nil_inst := [instance @iterate_with_hooks_find_dead_nil].
  Global Existing Instance iterate_with_hooks_find_dead_nil_inst.

  Lemma iterate_with_hooks_find_dead_cons E L κ κs T :
    find_in_context (FindOptLftDead κ) (λ dead,
      if dead
      then [† κ] -∗ T L (IterateFindDead (κ :: κs))
      else iterate_with_hooks E L (IterateFindDead (κs)) T)
    ⊢ iterate_with_hooks E L (IterateFindDead (κ :: κs)) T.
  Proof.
    iIntros "HT". iIntros (??) "CTX HE HL".
    iDestruct "HT" as "(%b & HT)".
    destruct b.
    - iDestruct "HT" as "(Hdead & HT)". iFrame. iExists _.
      iApply ("HT" with "Hdead").
    - iDestruct "HT" as "(_ & HT)" .
      by iApply ("HT" with "[] CTX HE HL").
  Qed.
  Definition iterate_with_hooks_find_dead_cons_inst := [instance @iterate_with_hooks_find_dead_cons].
  Global Existing Instance iterate_with_hooks_find_dead_cons_inst.

  Lemma introduce_with_hooks_inherit E L κs P T :
    iterate_with_hooks E L (IterateFindDead κs) (λ L2 m,
    match m with
    | IterateFindDead [] =>
      Inherit κs P -∗ T L2
    | IterateFindDead (κ :: _) =>
        ⌜fast_set_hint (κ ∈ κs)⌝ ∗ find_in_context (FindLftDead κ) (λ _,
        introduce_with_hooks E L2 P T)
    end)
    ⊢ introduce_with_hooks E L (Inherit κs P) T.
  Proof.
    rewrite /FindOptLftDead/=. iIntros "HT".
    iIntros (??) "#CTX #HE HL HP".
    iMod ("HT" with "[] CTX HE HL") as "(%L2 & %m' & HL & HT)"; first done.
    destruct m' as [[]].
    - iFrame. by iApply "HT".
    - unfold fast_set_hint. iDestruct "HT" as "(%Helem & % & Hdead & HT)".
      rewrite /Inherit.
      iMod ("HP" with "[//] [Hdead]") as "HP".
      { iApply lft_dead_lft_intersect_list. iFrame. done. }
      by iApply ("HT" with "[] CTX HE HL").
  Qed.
  Definition introduce_with_hooks_inherit_inst := [instance @introduce_with_hooks_inherit].
  Global Existing Instance introduce_with_hooks_inherit_inst.

  Lemma introduce_with_hooks_lft_toks E L κs T :
    li_tactic (llctx_release_toks_goal L κs) T ⊢
    introduce_with_hooks E L (llft_elt_toks κs) T.
  Proof.
    rewrite /li_tactic /llctx_release_toks_goal.
    iIntros "(%L' & %HL & HT)".
    iIntros (F ?) "#CTX #HE HL Htoks".
    iMod (llctx_return_elt_toks _ _ L' with "HL Htoks") as "HL"; first done.
    eauto with iFrame.
  Qed.
  Definition introduce_with_hooks_lft_toks_inst := [instance @introduce_with_hooks_lft_toks].
  Global Existing Instance introduce_with_hooks_lft_toks_inst | 10.

  Lemma introduce_with_hooks_releq rt E L γ1 γ2 T :
    find_in_context (FindOptGvarPobs γ1) (λ o,
    match o with
    | inr _ =>
        RelEq (T:=rt) γ1 γ2 -∗ T L
    | inl (existT rt' r) =>
        ∃ (Heq : RT_rt rt' = RT_rt rt),
        introduce_with_hooks E L (gvar_pobs γ2 (rew [id] Heq in r)) T
    end)
    ⊢ introduce_with_hooks E L (RelEq (T:=rt) γ1 γ2) T.
  Proof.
    iIntros "(%o & Hobs & HT)".
    iIntros (??) "CTX HE HL Hrel".
    destruct o as [[rt' r] | ]; simpl.
    - iDestruct "HT" as "(%Heq & HT)". destruct Heq.
      iPoseProof (RelEq_use_pobs with "Hobs Hrel") as "Hobs".
      iMod (gvar_obs_persist with "Hobs") as "Hobs".
      by iApply ("HT" with "[] CTX HE HL Hobs").
    - iFrame. by iApply "HT".
  Qed.
  Definition introduce_with_hooks_releq_inst := [instance @introduce_with_hooks_releq].
  Global Existing Instance introduce_with_hooks_releq_inst.

  Lemma introduce_with_hooks_rel2 rt1 rt2 E L (R : rt1 → rt2 → Prop) γ1 γ2 T :
    find_in_context (FindOptGvarPobs γ1) (λ o,
    match o with
    | inr _ =>
        Rel2 (T1:=rt1)(T2:=rt2) γ1 γ2 R -∗ T L
    | inl (existT rt' r) =>
        ∃ (Heq : RT_rt rt' = rt1),
        ∀ r2,
        introduce_with_hooks E L (⌜R (rew [id] Heq in r) r2⌝ ∗ gvar_pobs γ2 ( r2)) T
    end)
    ⊢ introduce_with_hooks E L (Rel2 (T1:=rt1)(T2:=rt2) γ1 γ2 R) T.
  Proof.
    iIntros "(%o & Hobs & HT)".
    iIntros (??) "CTX HE HL Hrel".
    destruct o as [[rt' r] | ]; simpl.
    - iDestruct "HT" as "(%Heq & HT)". destruct Heq.
      iPoseProof (Rel2_use_pobs with "Hobs Hrel") as "(%r2 & Hobs & %HR)".
      iMod (gvar_obs_persist with "Hobs") as "Hobs".
      iApply ("HT" with "[] CTX HE HL [Hobs]"); first done.
      simpl. by iFrame.
    - iFrame. by iApply "HT".
  Qed.
  Definition introduce_with_hooks_rel2_inst := [instance @introduce_with_hooks_rel2].
  Global Existing Instance introduce_with_hooks_rel2_inst.

  (** StartLft *)
  Lemma type_startlft E L f (n : string) sup_lfts s fn R ϝ :
    (∃ M, named_lfts M ∗ li_tactic (compute_map_lookups_nofail_goal M sup_lfts) (λ κs,
      ∀ κ, named_lfts (named_lft_update n κ M) -∗
      (* add a credit -- will be used by endlft *)
      introduce_with_hooks E ((κ ⊑ₗ{0%nat} κs) :: L) (£ num_cred) (λ L2,
      typed_stmt E L2 f s fn R ϝ)))
    ⊢ typed_stmt E L f (annot{1}: (StartLftAnnot n sup_lfts); s) fn R ϝ.
  Proof.
    rewrite /compute_map_lookups_nofail_goal.
    iIntros "(%M & Hnamed & %κs & %Hlook & Hcont)".
    iIntros (?) "#(LFT & LLCTX) #HE HL Hf Hcont'".
    iApply wps_annot => /=.
    iMod (llctx_startlft _ _ κs with "LFT LLCTX HL") as (κ) "HL"; [solve_ndisj.. | ].
    iApply physical_step_intro_lc; iIntros "Hcred"; iModIntro; iNext.
    iApply fupd_wps.
    iMod ("Hcont" with "[Hnamed] [] [$] HE HL Hcred") as "(%L2 & HL & HT)"; [ | done | ].
    { iApply named_lfts_update. done. }
    by iApply ("HT" with "[$LFT $LLCTX] HE HL Hf").
  Qed.

  (** Alias lifetimes: like startlft but without the atomic part *)
  Lemma type_alias_lft E L f (n : string) sup_lfts s fn R ϝ :
    (∃ M, named_lfts M ∗ li_tactic (compute_map_lookups_nofail_goal M sup_lfts) (λ κs,
      ∀ κ, named_lfts (named_lft_update n κ M) -∗ typed_stmt E ((κ ≡ₗ κs) :: L) f s fn R ϝ))
    ⊢ typed_stmt E L f (annot{1}: (AliasLftAnnot n sup_lfts); s) fn R ϝ.
  Proof.
    rewrite /compute_map_lookups_nofail_goal.
    iIntros "(%M & Hnamed & %κs & %Hlook & Hcont)".
    iIntros (?) "#(LFT & LLCTX) #HE HL Hf Hcont'".
    iApply wps_annot => /=.
    set (κ := lft_intersect_list κs).
    iAssert (llctx_interp ((κ ≡ₗ κs) :: L))%I with "[HL]" as "HL".
    { iFrame "HL". iSplit; iApply lft_incl_refl. }
    iApply physical_step_intro; iNext.
    iApply ("Hcont" $! κ with "[Hnamed] [$LFT $LLCTX] HE HL Hf").
    { iApply named_lfts_update. done. }
    done.
  Qed.

  (** EndLft *)
  (* TODO: also make endlft apply to local aliases, endlft should just remove them, without triggering anything. *)

  Variant iterate_endlft_inheritances :=
  | IterateEndlftInheritances (κ : lft) (ks : list (list lft * iProp Σ)).

  Lemma iterate_with_hooks_endlft_inheritance_nil E L κ T :
    T L (IterateEndlftInheritances κ [])
    ⊢ iterate_with_hooks E L (IterateEndlftInheritances κ []) T.
  Proof.
    iIntros "HT" (??) "CTX HE HL". iFrame. done.
  Qed.
  Definition iterate_with_hooks_endlft_inheritance_nil_inst := [instance @iterate_with_hooks_endlft_inheritance_nil].
  Global Existing Instance iterate_with_hooks_endlft_inheritance_nil_inst.

  Lemma iterate_with_hooks_endlft_inheritance_cons E L κ κs P ks T :
    (* check if this inheritance applies if [κ] dies *)
    li_tactic (check_list_elem_of_goal κ κs) (λ b,
      if b then
        find_in_context (FindInherit κs P) (λ _,
        find_in_context (FindLftDead κ) (λ _,
        introduce_with_hooks E L P (λ L2,
        iterate_with_hooks E L2 (IterateEndlftInheritances κ ks) T)))
      else iterate_with_hooks E L (IterateEndlftInheritances κ ks) T)
    ⊢ iterate_with_hooks E L (IterateEndlftInheritances κ ((κs, P) :: ks)) T.
  Proof.
    rewrite /check_list_elem_of_goal.
    iIntros "(%b & %Hel & HT)".
    destruct b.
    - iDestruct "HT" as "(% & Hinh & % & Hdead & HT)".
      simpl in *. unfold Inherit.
      iIntros (??) "#CTX #HE HL".
      simpl.
      iMod ("Hinh" with "[//] [Hdead]") as "HP".
      { iApply lft_dead_lft_intersect_list. iFrame. done. }
      iMod ("HT" with "[] CTX HE HL HP") as "(%L2 & HL & HT)"; first done.
      by iApply ("HT" with "[] CTX HE HL").
    - done.
  Qed.
  Definition iterate_with_hooks_endlft_inheritance_cons_inst := [instance @iterate_with_hooks_endlft_inheritance_cons].
  Global Existing Instance iterate_with_hooks_endlft_inheritance_cons_inst.

  Lemma type_endlft E L f (n : string) s fn R ϝ :
    (∃ M, named_lfts M ∗
      (* if this lifetime does not exist anymore, this is a nop *)
      li_tactic (compute_map_lookup_goal M n true) (λ o,
      match o with
      | Some κ =>
        (* find some credits *)
        prove_with_subtype E L false ProveDirect (£1) (λ L1 _ R2,
        (* We need to make sure there are no open borrows using tokens of this lifetime, inclusing aliases, so find the lifetimes which will be dying here *)
        li_tactic (find_implied_dying_lifetimes_goal L1 κ) (λ implied_dying,
        typed_pre_context_fold f.1 E L1 (CtxFoldCloseInvAllInit (κ :: implied_dying)) (λ L1',
        (* find the new llft context *)
        li_tactic (llctx_find_llft_goal L1' κ LlctxFindLftFull) (λ '(_, L1''),
        li_tactic (llctx_remove_dead_aliases_goal L1'' κ) (λ L2,
        (* simplify the name map *)
        li_tactic (simplify_lft_map_goal (named_lft_delete n M)) (λ M',
        named_lfts M' -∗
        (□ [† κ]) -∗
        (* extract observations from now-dead mutable references *)
        typed_pre_context_fold f.1 E L2 (CtxFoldExtractAllInit κ) (λ L3,
        (* give back credits *)
        introduce_with_hooks E L3 (R2 ∗ £num_cred ∗ tr 1) (λ L4,
        (* resolve inheritances *)
        li_tactic (find_inheritances_goal) (λ ks,
        iterate_with_hooks E L4 (IterateEndlftInheritances κ ks) (λ L5 _,
        typed_stmt E L5 f s fn R ϝ))))))))))
      | None => named_lfts M -∗ typed_stmt E L f s fn R ϝ
      end))
    ⊢ typed_stmt E L f (annot{2}: (EndLftAnnot n); s) fn R ϝ.
  Proof.
    iIntros "(%M & Hnamed & Hlook)".
    unfold compute_map_lookup_goal.
    iDestruct "Hlook" as (o) "(<- & HT)".
    destruct (M !! n) as [κ | ]; first last.
    { iIntros (?) "#CTX #HE HL Hf Hcont". iApply wps_annot.
      iApply physical_step_intro; iNext.
      iApply physical_step_intro; iNext.
      by iApply ("HT" with "Hnamed CTX HE HL Hf"). }
    unfold llctx_find_llft_goal, llctx_remove_dead_aliases_goal, li_tactic.
    iIntros (?) "#CTX #HE HL Hf Hcont".
    iMod ("HT" with "[] [] [] CTX HE HL") as "(%L2 & % & %R2 & >(Hc & HR2) & HL & HT)"; [done.. | ].
    unfold find_implied_dying_lifetimes_goal. iDestruct "HT" as "(%implied_dying & HT)".
    iApply wps_annot.
    iPoseProof ("HT" $! ⊤ with "[] [] [] CTX HE HL") as "Hstep"; [done.. | ].
    iApply (physical_step_step_upd with "Hstep").
    iApply physical_step_intro. iNext.
    iIntros "(%L3 & HL & HT)".

    iDestruct "HT" as "(%L' & % & %Hkill & Hs)".
    unfold simplify_lft_map_goal. iDestruct "Hs" as "(%L'' & %Hsub & Hs)".
    iDestruct "Hs" as "(%M' & _ & Hs)".
    iPoseProof (llctx_end_llft ⊤ with "HL") as "Ha"; [done | done | apply Hkill | ].
    iApply physical_step_fupd_l.
    iMod ("Ha"). iApply (lc_fupd_add_later with "Hc"). iNext. iMod ("Ha") as "(#Hdead & HL)".
    iPoseProof (llctx_interp_sublist with "HL") as "HL".
    { apply Hsub. }

    iPoseProof ("Hs" with "[Hnamed] Hdead") as "HT".
    { by iApply named_lfts_update. }
    iPoseProof ("HT" $! ⊤ with "[] [] [] CTX HE HL") as "Hstep"; [done.. | ].
    iModIntro.
    iApply (physical_step_step_upd with "Hstep").
    iMod (tr_zero) as "Ha".
    iApply (physical_step_intro_tr with "Ha"). iNext.
    iIntros "Ha Hcred !>".
    iIntros "(%L5 & HL & HT)".

    iMod ("HT" with "[] CTX HE HL [$HR2 Hcred Ha]") as "(%L6 & HL & HT)"; first done.
    { iFrame. iApply tr_weaken; last done. simpl. unfold num_laters_per_step; lia. }
    unfold find_inheritances_goal. iDestruct "HT" as "(%ks & HT)".
    iMod ("HT" with "[] CTX HE HL") as "(%L7 & % & HL & HT)"; first done.
    by iApply ("HT" with "CTX HE HL Hf").
  Qed.

  (** Dynamic inclusion *)
  Lemma type_dyn_include_lft E L f n1 n2 s fn R ϝ :
    (∃ M, named_lfts M ∗
      li_tactic (compute_map_lookup_nofail_goal M n1) (λ κ1,
      li_tactic (compute_map_lookup_nofail_goal M n2) (λ κ2,
      li_tactic (lctx_lft_alive_count_goal E L κ2) (λ '(κs, L'),
      Inherit [κ1] (llft_elt_toks κs) -∗
      named_lfts M -∗
      typed_stmt ((κ1 ⊑ₑ κ2) :: E) L' f s fn R ϝ))))
    ⊢ typed_stmt E L f (annot{1}: DynIncludeLftAnnot n1 n2; s) fn R ϝ.
  Proof.
    rewrite /compute_map_lookup_nofail_goal.
    iIntros "(%M & Hnamed & %κ1 & %Hlook1 & %κ2 & %Hlook2 & Hs)".
    unfold lctx_lft_alive_count_goal.
    iDestruct "Hs" as "(%κs & %L' & %Hal & Hs)".
    iIntros (?) "#(LFT & LCTX) #HE HL Hf Hcont".
    iMod (lctx_include_lft_sem with "LFT HE HL") as "(HL & #Hincl & Hinh)"; [done.. | ].
    iSpecialize ("Hs" with "Hinh").
    iApply wps_annot. iApply physical_step_intro; iNext.
    iApply ("Hs" with "Hnamed [$] [] HL Hf").
    { iFrame "HE Hincl". }
    done.
  Qed.

  (** ExtendLft *)
  Variant iterate_extend_lft :=
    | IterateExtendLft (κs : list lft)
  .
  Lemma iterate_with_hooks_extend_lft_nil E L T :
    T L (IterateExtendLft [])
    ⊢ iterate_with_hooks E L (IterateExtendLft []) T.
  Proof.
    iIntros "HT". iIntros (??) "CTX HE HL".
    iModIntro. iFrame.
  Qed.
  Definition iterate_with_hooks_extend_lft_nil_inst := [instance @iterate_with_hooks_extend_lft_nil].
  Global Existing Instance iterate_with_hooks_extend_lft_nil_inst.

  Lemma iterate_with_hooks_extend_lft_cons E L κ κs T :
    li_tactic (check_lft_is_local_goal E L κ) (λ b,
    if b then
      li_tactic (llctx_find_llft_goal L κ LlctxFindLftOwned) (λ '(κs', L'),
        iterate_with_hooks E ((κ ≡ₗ κs') :: L') (IterateExtendLft (κs' ++ κs)) T)
    else iterate_with_hooks E L (IterateExtendLft (κs)) T)
    ⊢ iterate_with_hooks E L (IterateExtendLft (κ :: κs)) T.
  Proof.
    iIntros "HT". iIntros (??) "(#LFT & #LCTX) HE HL".
    rewrite /llctx_find_llft_goal /check_lft_is_local_goal.
    iDestruct "HT" as "(%b & HT)".
    destruct b.
    - iDestruct "HT" as "(%L' & %κs' & %Hfind & HT)".
      iMod (llctx_extendlft_local_owned with "LFT HL") as "HL"; [done.. | ].
      iMod ("HT" with "[] [$] HE HL") as "(%L2 & %m & HL & HT)"; first done.
      by iFrame.
    - by iApply ("HT" with "[] [$] HE HL").
  Qed.
  Definition iterate_with_hooks_extend_lft_cons_inst := [instance @iterate_with_hooks_extend_lft_cons].
  Global Existing Instance iterate_with_hooks_extend_lft_cons_inst.

  Lemma type_extendlft E L f (n : string) s fn R ϝ :
    (∃ M, named_lfts M ∗
      li_tactic (compute_map_lookup_nofail_goal M n) (λ κ,
      iterate_with_hooks E L (IterateExtendLft [κ]) (λ L' _,
      (named_lfts M -∗ typed_stmt E L' f s fn R ϝ))))
    ⊢ typed_stmt E L f (annot{1}: (ExtendLftAnnot n); s) fn R ϝ.
  Proof.
    rewrite /compute_map_lookup_nofail_goal.
    iIntros "(%M & Hnamed & %κ & _ & Hs)".
    iIntros (?) "#CTX #HE HL Hf Hcont".
    iMod ("Hs" with "[] CTX HE HL") as "(%L2 & % & HL & HT)"; first done.
    iApply wps_annot. iApply physical_step_intro; iNext.
    by iApply ("HT" with "Hnamed [$] HE HL Hf").
  Qed.

  (** UnconstrainedLftAnnot *)
  Lemma type_unconstrained_lft E L f (n : string) s fn R ϝ sup `{!TCFastDone (UnconstrainedLftHint n sup)} :
    typed_stmt E L f (annot{1}: (StartLftAnnot n sup); s) fn R ϝ
    ⊢ typed_stmt E L f (annot{1}: (UnconstrainedLftAnnot n); s) fn R ϝ.
  Proof.
    done.
  Qed.

  (** CopyLftNameAnnot *)
  Lemma type_copy_lft_name E L f n1 n2 s fn R ϝ :
    (∃ M, named_lfts M ∗
      li_tactic (compute_map_lookup_nofail_goal M n2) (λ κ2,
      li_tactic (simplify_lft_map_goal (named_lft_update n1 κ2 (named_lft_delete n1 M))) (λ M',
        named_lfts M' -∗ typed_stmt E L f s fn R ϝ)))
    ⊢ typed_stmt E L f (annot{1}: CopyLftNameAnnot n1 n2; s) fn R ϝ.
  Proof.
    rewrite /compute_map_lookup_nofail_goal.
    iIntros "(%M & Hnamed & %κ2 & _ & Hs)".
    iIntros (?) "#CTX #HE HL Hf Hcont".
    unfold simplify_lft_map_goal. iDestruct "Hs" as "(%M' & _ & Hs)".
    iApply wps_annot. iApply physical_step_intro; iNext.
    by iApply ("Hs" with "Hnamed CTX HE HL Hf").
  Qed.

  (** We instantiate the context folding mechanism for unblocking. *)
  Definition typed_context_fold_stratify_interp (π : thread_id) := λ '(ctx, R), (type_ctx_interp π ctx ∗ R)%I.
  Lemma typed_context_fold_step_stratify π E L l {rt} (lt : ltype rt) (r : place_rfn rt) (tctx : list loc) ma acc R T :
    (* TODO: this needs a different stratification strategy *)
    stratify_ltype_unblock π E L ma l lt r (Owned)
      (λ L' R' rt' lt' r', typed_context_fold (typed_context_fold_stratify_interp π) E L' (CtxFoldStratifyAll ma) tctx ((l, mk_bltype _ r' lt') :: acc, R' ∗ R) T)
    ⊢ typed_context_fold_step (typed_context_fold_stratify_interp π) π E L (CtxFoldStratifyAll ma) l lt r tctx (acc, R) T.
  Proof.
    iIntros "Hstrat". iIntros (????) "#CTX #HE HL Hdel Hl".
    iPoseProof ("Hstrat" $! F with "[//] [//] [//] CTX HE HL Hl") as ">Hc".
    iDestruct "Hc" as "(%L' & %R' & %rt' & %lt' & %r' & HL & %Hst & Hstep & Hcont)".
    iApply ("Hcont" $! F with "[//] [//] [//] CTX HE HL [Hstep Hdel]").
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_compose with "Hdel").
    iApply logical_step_intro.
    iIntros "(Hctx & HR) (Hl & HR')".
    iFrame.
  Qed.
  Definition typed_context_fold_step_stratify_inst := [instance typed_context_fold_step_stratify].
  Global Existing Instance typed_context_fold_step_stratify_inst.

  Lemma typed_context_fold_stratify_init π E L ma T :
    li_tactic (find_spatial_locs_goal) (λ tctx,
    typed_context_fold (typed_context_fold_stratify_interp π) E L (CtxFoldStratifyAll ma) tctx ([], True%I) (λ L' m' acc, True ∗
      typed_context_fold_end (typed_context_fold_stratify_interp π) E L' acc T))
    ⊢ typed_pre_context_fold π E L (CtxFoldStratifyAllInit ma) T.
  Proof.
    rewrite /find_spatial_locs_goal.
    iIntros "(%tctx & Hf)". iApply (typed_context_fold_init (typed_context_fold_stratify_interp π) ([], True%I) π _ _ (CtxFoldStratifyAll ma)). iFrame.
    rewrite /typed_context_fold_stratify_interp/type_ctx_interp; simpl; done.
  Qed.
  Definition typed_context_fold_stratify_init_inst := [instance @typed_context_fold_stratify_init].
  Global Existing Instance typed_context_fold_stratify_init_inst.

  Lemma type_stratify_context_annot E L f s fn R ϝ :
    typed_pre_context_fold f.1 E L (CtxFoldStratifyAllInit StratNoRefold) (λ L', typed_stmt E L' f s fn R ϝ)
    ⊢ typed_stmt E L f (annot{1}: (StratifyContextAnnot); s) fn R ϝ.
  Proof.
    iIntros "HT".
    iIntros (?) "#CTX #HE HL Hf Hcont".
    iApply fupd_wps.
    iPoseProof ("HT" $! ⊤ with "[//] [//] [//] CTX HE HL") as "Hstep".
    iApply wps_annot.
    iModIntro.
    iApply (physical_step_step_upd with "Hstep").
    iApply physical_step_intro; iNext.
    iIntros "(%L' & HL & HT)".
    by iApply ("HT" with "CTX HE HL Hf").
  Qed.

  (** We instantiate the context folding mechanism for extraction of observations. *)
  Definition typed_context_fold_extract_interp (π : thread_id) := λ '(ctx, R), (type_ctx_interp π ctx ∗ R)%I.
  Lemma typed_context_fold_step_extract π E L l {rt} (lt : ltype rt) (r : place_rfn rt) (tctx : list loc) acc R κ T :
    stratify_ltype_extract π E L StratNoRefold l lt r (Owned) κ
      (λ L' R' rt' lt' r', typed_context_fold (typed_context_fold_stratify_interp π) E L' (CtxFoldExtractAll κ) tctx ((l, mk_bltype _ r' lt') :: acc, R' ∗ R) T)
    ⊢ typed_context_fold_step (typed_context_fold_extract_interp π) π E L (CtxFoldExtractAll κ) l lt r tctx (acc, R) T.
  Proof.
    iIntros "Hstrat". iIntros (????) "#CTX #HE HL Hdel Hl".
    iPoseProof ("Hstrat" $! F with "[//] [//] [//] CTX HE HL Hl") as ">Hc".
    iDestruct "Hc" as "(%L' & %R' & %rt' & %lt' & %r' & HL & %Hst & Hstep & Hcont)".
    iApply ("Hcont" $! F with "[//] [//] [//] CTX HE HL [Hstep Hdel]").
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_compose with "Hdel").
    iApply logical_step_intro.
    iIntros "(Hctx & HR) (Hl & HR')".
    iFrame.
  Qed.
  Definition typed_context_fold_step_extract_inst := [instance typed_context_fold_step_extract].
  Global Existing Instance typed_context_fold_step_extract_inst.

  Lemma typed_context_fold_extract_init π E L κ T :
    li_tactic find_spatial_locs_goal (λ tctx,
    typed_context_fold (typed_context_fold_stratify_interp π) E L (CtxFoldExtractAll κ) tctx ([], True%I) (λ L' m' acc, True ∗
      typed_context_fold_end (typed_context_fold_stratify_interp π) E L' acc T))
    ⊢ typed_pre_context_fold π E L (CtxFoldExtractAllInit κ) T.
  Proof.
    rewrite /find_spatial_locs_goal.
    iIntros "(%tctx & Hf)". iApply (typed_context_fold_init (typed_context_fold_stratify_interp π) ([], True%I) π _ _ (CtxFoldExtractAll κ)). iFrame.
    rewrite /typed_context_fold_stratify_interp/type_ctx_interp; simpl; done.
  Qed.
  Definition typed_context_fold_extract_init_inst := [instance @typed_context_fold_extract_init].
  Global Existing Instance typed_context_fold_extract_init_inst.

  (** We instantiate the context folding mechanism for resolution of observations. *)
  Definition typed_context_fold_resolve_interp (π : thread_id) := λ '(ctx, R), (type_ctx_interp π ctx ∗ R)%I.
  Lemma typed_context_fold_step_resolve π E L l {rt} (lt : ltype rt) (r : place_rfn rt) (tctx : list loc) acc R T :
    stratify_ltype_resolve π E L StratNoRefold l lt r (Owned)
      (λ L' R' rt' lt' r', typed_context_fold (typed_context_fold_resolve_interp π) E L' (CtxFoldResolveAll) tctx ((l, mk_bltype _ r' lt') :: acc, R' ∗ R) T)
    ⊢ typed_context_fold_step (typed_context_fold_resolve_interp π) π E L (CtxFoldResolveAll) l lt r tctx (acc, R) T.
  Proof.
    iIntros "Hstrat". iIntros (????) "#CTX #HE HL Hdel Hl".
    iPoseProof ("Hstrat" $! F with "[//] [//] [//] CTX HE HL Hl") as ">Hc".
    iDestruct "Hc" as "(%L' & %R' & %rt' & %lt' & %r' & HL & %Hst & Hstep & Hcont)".
    iApply ("Hcont" $! F with "[//] [//] [//] CTX HE HL [Hstep Hdel]").
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_compose with "Hdel").
    iApply logical_step_intro.
    iIntros "(Hctx & HR) (Hl & HR')".
    iFrame.
  Qed.
  Definition typed_context_fold_step_resolve_inst := [instance typed_context_fold_step_resolve].
  Global Existing Instance typed_context_fold_step_resolve_inst.

  Lemma typed_context_fold_resolve_init π E L T :
    li_tactic find_spatial_locs_goal (λ tctx,
    typed_context_fold (typed_context_fold_resolve_interp π) E L (CtxFoldResolveAll) tctx ([], True%I) (λ L' m' acc, True ∗
      typed_context_fold_end (typed_context_fold_resolve_interp π) E L' acc T))
    ⊢ typed_pre_context_fold π E L (CtxFoldResolveAllInit) T.
  Proof.
    rewrite /find_spatial_locs_goal.
    iIntros "(%tctx & Hf)". iApply (typed_context_fold_init (typed_context_fold_resolve_interp π) ([], True%I) π _ _ (CtxFoldResolveAll)). iFrame.
    rewrite /typed_context_fold_resolve_interp/type_ctx_interp; simpl; done.
  Qed.
  Definition typed_context_fold_resolve_init_inst := [instance @typed_context_fold_resolve_init].
  Global Existing Instance typed_context_fold_resolve_init_inst.

  (** We instantiate the context folding mechanism for closing invariants. *)
  Definition typed_context_fold_close_inv_interp (π : thread_id) := λ '(ctx, R), (type_ctx_interp π ctx ∗ R)%I.
  Lemma typed_context_fold_step_close_inv π E L l {rt} (lt : ltype rt) (r : place_rfn rt) (tctx : list loc) acc R κs T :
    stratify_ltype_close_inv κs π E L l lt r (Owned)
      (λ L' R' rt' lt' r', typed_context_fold (typed_context_fold_resolve_interp π) E L' (CtxFoldCloseInvAll κs) tctx ((l, mk_bltype _ r' lt') :: acc, R' ∗ R) T)
    ⊢ typed_context_fold_step (typed_context_fold_close_inv_interp π) π E L (CtxFoldCloseInvAll κs) l lt r tctx (acc, R) T.
  Proof.
    iIntros "Hstrat". iIntros (????) "#CTX #HE HL Hdel Hl".
    iPoseProof ("Hstrat" $! F with "[//] [//] [//] CTX HE HL Hl") as ">Hc".
    iDestruct "Hc" as "(%L' & %R' & %rt' & %lt' & %r' & HL & %Hst & Hstep & Hcont)".
    iApply ("Hcont" $! F with "[//] [//] [//] CTX HE HL [Hstep Hdel]").
    iApply (logical_step_compose with "Hstep").
    iApply (logical_step_compose with "Hdel").
    iApply logical_step_intro.
    iIntros "(Hctx & HR) (Hl & HR')".
    iFrame.
  Qed.
  Definition typed_context_fold_step_close_inv_inst := [instance @typed_context_fold_step_close_inv].
  Global Existing Instance typed_context_fold_step_close_inv_inst.

  Lemma typed_context_fold_close_inv_init π E L κs T :
    li_tactic find_spatial_locs_goal (λ tctx,
    typed_context_fold (typed_context_fold_close_inv_interp π) E L (CtxFoldCloseInvAll κs) tctx ([], True%I) (λ L' m' acc, True ∗
      typed_context_fold_end (typed_context_fold_close_inv_interp π) E L' acc T))
    ⊢ typed_pre_context_fold π E L (CtxFoldCloseInvAllInit κs) T.
  Proof.
    rewrite /find_spatial_locs_goal.
    iIntros "(%tctx & Hf)". iApply (typed_context_fold_init (typed_context_fold_close_inv_interp π) ([], True%I) π _ _ (CtxFoldCloseInvAll κs)). iFrame.
    rewrite /typed_context_fold_close_inv_interp/type_ctx_interp; simpl; done.
  Qed.
  Definition typed_context_fold_close_inv_init_inst := [instance @typed_context_fold_close_inv_init].
  Global Existing Instance typed_context_fold_close_inv_init_inst.

  (* Typing rule for [Return] *)
  Lemma type_return E L f e fn (R : typed_stmt_R_t) ϝ :
    typed_val_expr E L f e (λ L' v m rt ty r,
      introduce_with_hooks E L' (v ◁ᵥ{f.1, m} r @ ty) (λ L2,
      find_in_context (FindFrameLocals f) (λ locals : list var_name,
      trigger_tc (FindLocalLocs f locals) (λ locs,
      typed_context_fold (typed_context_fold_stratify_interp f.1) E L2 (CtxFoldStratifyAll StratRefoldOpened) locs ([], True%I) (λ L2 m' acc,
        introduce_with_hooks E L2 (type_ctx_interp f.1 acc.1 ∗ acc.2) (λ L3,
          prove_with_subtype E L3 true ProveDirect (
            foldr (λ (e : var_name) T,
              ∃ st l,
              e is_live{f, st} l ∗
              l ◁ₗ[f.1, Owned] (#()) @ (◁ (uninit st)) ∗ T)
            True%I
            locals) (λ L3 _ R2, introduce_with_hooks E L3 R2 (λ L4,
            (* important: when proving the postcondition [R v], we already have the ownership obtained by deinitializing the local variables [R2] available.
              The remaining goal is fully encoded by [R v], so the continuation is empty.
            *)
            R v L4
            ))))))))
    ⊢ typed_stmt E L f (return e) fn R ϝ.
  Proof.
    iIntros "He". iIntros (?) "#CTX #HE HL Hf Hcont". wps_bind.
    wpe_bind.
    iApply ("He" with "CTX HE HL Hf").
    iIntros (L' v m rt ty r) "HL Hf Hv HR".
    iApply fupd_wpe.
    iMod ("HR" with "[] CTX HE HL Hv") as "(%L2 & HL & HR)"; first done.
    iDestruct "HR" as "(%locals & Hlocals & %locs & % & HT)".
    iMod ("HT" with "[] [] [] CTX HE HL []") as "(%L3 & %acc & %m' & HL & Hstep & HT)"; [done.. | | ].
    { simpl. iApply logical_step_intro. iSplitR; last done. rewrite /type_ctx_interp. done. }
    iDestruct "CTX" as "(LFT & LLCTX)".
    iModIntro. wpe_bind.
    iApply wpe_fupd.
    iApply (wpe_logical_step with "Hstep"); [done.. | ].
    iApply wp_skip.
    iApply physical_step_intro; iNext.
    iIntros "Hacc".
    rewrite /typed_context_fold_stratify_interp.
    destruct acc as (ctx & R2).
    iMod ("HT" with "[] [$] HE HL Hacc") as "(%L4 & HL & HT)"; first done.
    iMod ("HT" with "[] [] [] [$] HE HL") as "(%L5 & % & %R3 & HP & HL & HT)"; [done.. | ].
    iApply (wpe_maybe_logical_step with "HP"); [done.. | ].
    iModIntro. iApply wp_skip.
    iApply physical_step_intro; iNext.
    iIntros "(Ha & HR2)".
    iApply wps_fupd.
    iApply wps_return.
    unfold li_tactic, llctx_find_llft_goal.
    iMod ("HT" with "[] [$] HE HL HR2") as "(%L6 & HL & HT)"; first done.

    unfold typed_stmt_post_cond.
    iSpecialize ("Hcont" $! _ v with "HL Hf Hlocals").
    clear.
    iAssert (|={⊤}=> ([∗ list] x ∈ locals, ∃ (ly : layout) (l : loc) (st : syn_type), ⌜syn_type_has_layout st ly⌝ ∗ x is_live{ f, st} l ∗ l ↦|ly|))%I with "[Ha]" as ">Ha".
    { iInduction locals as [|x locals] "IH"; csimpl in*; simplify_eq.
      { done. }
      iDestruct "Ha" as "(%st & %l & Hx & Hl & HR)".
      iMod ("IH" with "HR") as "$".
      rewrite ltype_own_ofty_unfold /lty_of_ty_own.
      iDestruct "Hl" as "(%ly' & %Halg & % & _ & _ &  % & <- & Hv)".
      simpl in Halg.
      iMod (fupd_mask_mono with "Hv") as "(%v0 & Hl & Hv)"; first done.
      iFrame.
      iPoseProof (ty_own_val_has_layout with "Hv") as "%"; first done.
      iExists _. done. }
    iApply ("Hcont" with "Ha HT").
  Qed.
End subsume.



(* This must be an hint extern because an instance would be a big slowdown . *)
Global Hint Extern 1 (Subsume (?v ◁ᵥ{_, _} ?r1 @ ?ty1) (?v ◁ᵥ{_, _} ?r2 @ ?ty2)) =>
  class_apply own_val_subsume_id_inst : typeclass_instances.


Global Typeclasses Opaque subsume_full.
Global Typeclasses Opaque credit_store.
Global Typeclasses Opaque typed_value.
Global Typeclasses Opaque typed_val_expr.

Global Typeclasses Opaque typed_bin_op.

Global Typeclasses Opaque typed_un_op.

Global Typeclasses Opaque typed_check_bin_op.

Global Typeclasses Opaque typed_check_un_op.

Global Typeclasses Opaque typed_if.

Global Typeclasses Opaque typed_call.

Global Typeclasses Opaque typed_annot_expr.

Global Typeclasses Opaque introduce_with_hooks.
Global Typeclasses Opaque iterate_with_hooks.
Global Typeclasses Opaque typed_stmt_post_cond.

Global Typeclasses Opaque typed_assert.

Global Typeclasses Opaque typed_annot_stmt.

Global Typeclasses Opaque typed_switch.

Global Typeclasses Opaque typed_place.

Global Typeclasses Opaque cast_ltype_to_type.

Global Typeclasses Opaque resolve_ghost.
Global Typeclasses Opaque resolve_ghost_adt.

Global Typeclasses Opaque find_observation.

Global Typeclasses Opaque stratify_ltype.
Global Typeclasses Opaque typed_stmt.

Global Typeclasses Opaque typed_block.


Global Typeclasses Opaque stratify_ltype_post_hook.

Global Typeclasses Opaque weak_subtype.

Global Typeclasses Opaque weak_subltype.

Global Typeclasses Opaque owned_subtype.

Global Typeclasses Opaque owned_subltype_step.

Global Typeclasses Opaque mut_subtype.
Global Typeclasses Opaque subtype_adt.

Global Typeclasses Opaque mut_subltype.

Global Typeclasses Opaque mut_eqtype.

Global Typeclasses Opaque mut_eqltype.

Global Typeclasses Opaque prove_with_subtype.

Global Typeclasses Opaque prove_place_cond.
Global Typeclasses Opaque typed_read_end.

Global Typeclasses Opaque typed_write_end.

Global Typeclasses Opaque typed_borrow_mut.

Global Typeclasses Opaque typed_borrow_mut_end.

Global Typeclasses Opaque typed_borrow_shr.

Global Typeclasses Opaque typed_borrow_shr_end.

Global Typeclasses Opaque typed_addr_of_mut.

Global Typeclasses Opaque typed_addr_of_mut_end.

Global Typeclasses Opaque interpret_typing_hint.

Global Typeclasses Opaque typed_context_fold.


Global Typeclasses Opaque typed_context_fold_end.

Global Typeclasses Opaque relate_list.

Global Typeclasses Opaque relate_hlist.

Global Typeclasses Opaque fold_list.

Global Typeclasses Opaque typed_pre_context_fold.

Global Typeclasses Opaque typed_context_fold_step.

Global Typeclasses Opaque typed_write.



Global Typeclasses Opaque llctx_release_toks_goal.

Global Typeclasses Opaque lctx_lft_alive_count_goal.

Global Typeclasses Opaque typed_place_finish.

Global Typeclasses Transparent typed_place_finish.

Global Typeclasses Opaque typed_read.

Global Typeclasses Opaque stratify_ltype_array_iter.
Global Hint Mode StratifyLtypeArrayIter + + + + + + + + + + + + + + + + + + : typeclass_instances.

Global Hint Mode ResolveGhostIter + + + + + + + + + + + + + + + : typeclass_instances.
Global Typeclasses Opaque resolve_ghost_iter.

Global Hint Mode TypedArrayAccess + + + + + + + + + + + + : typeclass_instances.
Global Typeclasses Opaque typed_array_access.
