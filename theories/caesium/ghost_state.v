From stdpp Require Import coPset.
From Stdlib Require Import QArith Qcanon.
From iris.algebra Require Import big_op gmap frac agree.
From iris.algebra Require Import csum excl auth cmra_big_op numbers.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.base_logic.lib Require Import ghost_map.
From iris.proofmode Require Export proofmode.
From caesium Require Export lang syntypes.
Set Default Proof Using "Type".
Import uPred.

(** ** Heap state *)
(* lock_stateR encoding:
   WSt             → Cinl (Excl ())              — exclusive (write-locked)
   RSt(n, me)      → Cinr (Cinl (n, agree(me)))  — n composable (reader count), me agreed (max epoch)
   PendingSt _     → Cinr (Cinr (Excl ()))        — exclusive (pending atomic commit) *)
Definition lock_stateR : cmra :=
  csumR (exclR unitO) (csumR (prodR natR (agreeR natO)) (exclR unitO)).

Definition heap_cellR : cmra :=
prodR (prodR fracR lock_stateR) (agreeR (prodO alloc_idO mbyteO)).

Definition heapUR : ucmra :=
  gmapUR addr heap_cellR.

Class heapG Σ := HeapG {
heap_heap_inG              :: inG Σ (authR heapUR);
  heap_heap_name             : gname;
  heap_alloc_meta_map_inG   :: ghost_mapG Σ alloc_id (Z * nat * alloc_kind);
  heap_alloc_meta_map_name  : gname;
  heap_alloc_alive_map_inG  :: ghost_mapG Σ alloc_id bool;
  heap_alloc_alive_map_name : gname;
  heap_fntbl_inG             :: ghost_mapG Σ addr function;
  heap_fntbl_name            : gname;
}.

Definition to_lock_stateR (lk : lock_state) : lock_stateR :=
  match lk with
  | WSt => Cinl (Excl ())
  | RSt n me => Cinr (Cinl (n, to_agree me))
  | PendingSt _ => Cinr (Cinr (Excl ()))
  end.

Definition to_heap_cellR (hc : heap_cell) : heap_cellR :=
(1%Qp, to_lock_stateR hc.(hc_lock_state), to_agree (hc.(hc_alloc_id), hc.(hc_value))).

Definition to_heapUR : heap → heapUR :=
  fmap to_heap_cellR.

Definition to_alloc_metaR (al : allocation) : (Z * nat * alloc_kind) :=
  (al.(al_start), al.(al_len), al.(al_kind)).

Definition to_alloc_meta_map : allocs → gmap alloc_id (Z * nat * alloc_kind) :=
fmap to_alloc_metaR.

Definition to_alloc_alive_map : allocs → gmap alloc_id bool :=
  fmap al_alive.

Section definitions.
  Context `{!heapG Σ} `{!FUpd (iProp Σ)}.

  (** * Allocation stuff. *)

  (** [alloc_meta id al] persistently records the information that allocation
with identifier [id] has a range corresponding to that of [a]. *)
  Definition alloc_meta_def (id : alloc_id) (al : allocation) : iProp Σ :=
    id ↪[ heap_alloc_meta_map_name ]□ to_alloc_metaR al.
  Definition alloc_meta_aux : seal (@alloc_meta_def). by eexists. Qed.
  Definition alloc_meta := unseal alloc_meta_aux.
  Definition alloc_meta_eq : @alloc_meta = @alloc_meta_def :=
    seal_eq alloc_meta_aux.

  Global Instance allocs_range_pers id al : Persistent (alloc_meta id al).
  Proof. rewrite alloc_meta_eq. by apply _. Qed.

  Global Instance allocs_range_tl id al : Timeless (alloc_meta id al).
  Proof. rewrite alloc_meta_eq. by apply _. Qed.

  (** [loc_in_bounds l pre suf] persistently records the information that location
  [l] and any of its positive offset up to [suf] (included) and
  negative offsets up to [pre] (included) are in range of the
  allocation [l] originated from (or one past the end of it). It also records
  the fact that this allocation is in bounds of allocatable memory. *)
  Definition loc_in_bounds_def (l : loc) (pre : nat) (suf : nat) : iProp Σ :=
    (∃ (id : alloc_id) (al : allocation),
    ⌜l.(loc_p) = ProvAlloc id⌝ ∗ ⌜al.(al_start) + pre ≤ l.(loc_a)⌝ ∗ ⌜l.(loc_a) + suf ≤ al_end al⌝ ∗
      ⌜allocation_in_range al⌝ ∗ alloc_meta id al) ∨
    (⌜l.(loc_p) = ProvNone⌝ ∗ ⌜0 ≤ l.(loc_a)⌝ ∗ ⌜l.(loc_a) ≤ max_alloc_end_zero⌝ ∗ ⌜pre = 0%nat⌝ ∗ ⌜suf = 0%nat⌝).
  Definition loc_in_bounds_aux : seal (@loc_in_bounds_def). by eexists. Qed.
  Definition loc_in_bounds := unseal loc_in_bounds_aux.
  Definition loc_in_bounds_eq : @loc_in_bounds = @loc_in_bounds_def :=
    seal_eq loc_in_bounds_aux.

  Global Instance loc_in_bounds_pers l pre suf : Persistent (loc_in_bounds l pre suf).
  Proof. rewrite loc_in_bounds_eq. by apply _. Qed.

  Global Instance loc_in_bounds_tl l pre suf : Timeless (loc_in_bounds l pre suf).
  Proof. rewrite loc_in_bounds_eq. by apply _. Qed.

  (** [alloc_alive id q] is a token witnessing the fact that the allocation
  with identifier [id] is still alive. *)
  Definition alloc_alive_def (id : alloc_id) (dq : dfrac) (a : bool) : iProp Σ :=
    id ↪[ heap_alloc_alive_map_name ]{dq} a.
  Definition alloc_alive_aux : seal (@alloc_alive_def). by eexists. Qed.
  Definition alloc_alive := unseal alloc_alive_aux.
  Definition alloc_alive_eq : @alloc_alive = @alloc_alive_def :=
    seal_eq alloc_alive_aux.

  Global Instance alloc_alive_tl id dq a : Timeless (alloc_alive id dq a).
  Proof. rewrite alloc_alive_eq. by apply _. Qed.
  Global Instance alloc_alive_fractional id a : Fractional (λ q, alloc_alive id (DfracOwn q) a).
  Proof.
    rewrite alloc_alive_eq. apply _.
  Qed.
  Global Instance alloc_alive_as_fractional id a q :
    AsFractional (alloc_alive id (DfracOwn q) a) (λ q, alloc_alive id (DfracOwn q) a) q.
  Proof. split; [done|]. apply _. Qed.

  (** [alloc_global l] is knowledge that the provenance of [l] is
  alive forever (i.e. corresponds to a global variable). *)
  Definition alloc_global_def (l : loc) : iProp Σ :=
    ∃ id, ⌜l.(loc_p) = ProvAlloc id⌝ ∗ alloc_alive id DfracDiscarded true.
  Definition alloc_global_aux : seal (@alloc_global_def). by eexists. Qed.
  Definition alloc_global := unseal alloc_global_aux.
  Definition alloc_global_eq : @alloc_global = @alloc_global_def :=
    seal_eq alloc_global_aux.

  Global Instance alloc_global_tl l : Timeless (alloc_global l).
  Proof. rewrite alloc_global_eq. by apply _. Qed.
  Global Instance alloc_global_pers l : Persistent (alloc_global l).
  Proof. rewrite alloc_global_eq /alloc_global_def alloc_alive_eq. by apply _. Qed.

  (** * Function table stuff. *)

  (** [fntbl_entry l f] persistently records the information that function
  [f] is stored at location [l]. NOTE: we use locations, but do not really
  store the code on the actual heap. *)
  Definition fntbl_entry_def (l : loc) (f: function) : iProp Σ :=
    ∃ a, ⌜l = fn_loc a⌝ ∗ a ↪[ heap_fntbl_name ]□ f.
  Definition fntbl_entry_aux : seal (@fntbl_entry_def). by eexists. Qed.
  Definition fntbl_entry := unseal fntbl_entry_aux.
  Definition fntbl_entry_eq : @fntbl_entry = @fntbl_entry_def :=
    seal_eq fntbl_entry_aux.

  Global Instance fntbl_entry_pers l f : Persistent (fntbl_entry l f).
  Proof. rewrite fntbl_entry_eq. by apply _. Qed.

  Global Instance fntbl_entry_tl l f : Timeless (fntbl_entry l f).
  Proof. rewrite fntbl_entry_eq. by apply _. Qed.

  (** Heap stuff. *)

  Definition heap_pointsto_mbyte_st (st : lock_state) (l : loc) (id : alloc_id)
                                  (q : Qp) (b : mbyte) : iProp Σ :=
    own heap_heap_name (◯ {[ l.(loc_a) := (q, to_lock_stateR st, to_agree (id, b)) ]}).

  Definition heap_pointsto_mbyte_def (l : loc) (q : Qp) (b : mbyte) : iProp Σ :=
    ∃ id me, ⌜l.(loc_p) = ProvAlloc id⌝ ∗ heap_pointsto_mbyte_st (RSt 0 me) l id q b.
  Definition heap_pointsto_mbyte_aux : seal (@heap_pointsto_mbyte_def). by eexists. Qed.
  Definition heap_pointsto_mbyte := unseal heap_pointsto_mbyte_aux.
  Definition heap_pointsto_mbyte_eq : @heap_pointsto_mbyte = @heap_pointsto_mbyte_def :=
    seal_eq heap_pointsto_mbyte_aux.

  Definition heap_pointsto_def (l : loc) (q : Qp) (v : val) : iProp Σ :=
    loc_in_bounds l 0 (length v) ∗
    ([∗ list] i ↦ b ∈ v, heap_pointsto_mbyte (l +ₗ i) q b)%I.
  Definition heap_pointsto_aux : seal (@heap_pointsto_def). by eexists. Qed.
  Definition heap_pointsto := unseal heap_pointsto_aux.
  Definition heap_pointsto_eq : @heap_pointsto = @heap_pointsto_def :=
    seal_eq heap_pointsto_aux.


  (** Token witnessing that [l] has an allocation identifier that is alive. *)
  Definition alloc_alive_loc_def (l : loc) : iProp Σ :=
    |={⊤, ∅}=> ((∃ id q, ⌜l.(loc_p) = ProvAlloc id⌝ ∗ alloc_alive id q true) ∨
               (∃ a q v, ⌜v ≠ []⌝ ∗ heap_pointsto (Loc l.(loc_p) a) q v)).
  Definition alloc_alive_loc_aux : seal (@alloc_alive_loc_def). by eexists. Qed.
  Definition alloc_alive_loc := unseal alloc_alive_loc_aux.
  Definition alloc_alive_loc_eq : @alloc_alive_loc = @alloc_alive_loc_def :=
    seal_eq alloc_alive_loc_aux.

  (** * Freeable *)

  Definition freeable_def (l : loc) (n : nat) (q : Qp) (k : alloc_kind) : iProp Σ :=
    ∃ id, ⌜l.(loc_p) = ProvAlloc id⌝ ∗ alloc_meta id {| al_start := l.(loc_a); al_len := n; al_alive := true; al_kind := k |} ∗
     alloc_alive id (DfracOwn q) true.
  Definition freeable_aux : seal (@freeable_def). by eexists. Qed.
  Definition freeable := unseal freeable_aux.
  Definition freeable_eq : @freeable = @freeable_def :=
    seal_eq freeable_aux.

  Global Instance freeable_timeless l n q k : Timeless (freeable l n q k).
  Proof. rewrite freeable_eq. apply _. Qed.

  Global Instance freeable_fractional l n k : Fractional (λ q, freeable l n q k).
  Proof.
    iIntros (q1 q2). rewrite freeable_eq. iSplit.
    - iIntros "(%id & % & #Hmeta & [Hal1 Hal2])".
      iSplitL "Hal1"; iExists id; by iFrame "∗ #".
    - iIntros "[(%id1 & % & #Hmeta & Hal1) (%id2 & % & _ & Hal2)]".
      assert (id1 = id2) as -> by congruence.
      iExists id2. rewrite alloc_alive_fractional. by iFrame "∗ #".
  Qed.
  Global Instance freeable_as_fractional l n k q :
    AsFractional (freeable l n q k) (λ q, freeable l n q k) q.
  Proof. split; [done|]. apply _. Qed.

  Lemma freeable_has_alloc l n q k :
    freeable l n q k -∗ ⌜∃ id, l.(loc_p) = ProvAlloc id⌝.
  Proof.
    rewrite freeable_eq. iIntros "(%id & % & _)". eauto.
  Qed.

  (** Version of [freeable] that is compatible with zero-sized allocations
    (which our allocation model does not allow for heap allocations) *)
  Definition freeable_nz (l : loc) (len : nat) (q : Qp) (k : alloc_kind) : iProp Σ :=
    match len with
    | 0%nat => True
    | _ => freeable l len q k
    end.
  Lemma freeable_freeable_nz `{!heapG Σ} l n q k :
    freeable l n q k -∗ freeable_nz l n q k.
  Proof.
    destruct n; eauto.
  Qed.

  Lemma freeable_nz_to_freeable l n q k :
    (n > 0)%nat → freeable_nz l n q k -∗ freeable l n q k.
  Proof.
    intros ?. destruct n; first lia. eauto.
  Qed.

  (** * Authoritative parts and contexts. *)

  Definition heap_ctx (h : heap) : iProp Σ :=
    own heap_heap_name (● to_heapUR h).

  Definition alloc_meta_ctx (ub : allocs) : iProp Σ :=
    ghost_map_auth heap_alloc_meta_map_name 1 (to_alloc_meta_map ub).

  Definition alloc_alive_ctx (ub : allocs) : iProp Σ :=
    ghost_map_auth heap_alloc_alive_map_name 1 (to_alloc_alive_map ub).

  Definition fntbl_ctx (fns : gmap addr function) : iProp Σ :=
    ghost_map_auth heap_fntbl_name 1 fns.

  Definition heap_state_ctx (st : heap_state) : iProp Σ :=
    ⌜heap_state_invariant st⌝ ∗
    heap_ctx st.(hs_heap) ∗
    alloc_meta_ctx st.(hs_allocs) ∗
    alloc_alive_ctx st.(hs_allocs).

End definitions.

Global Typeclasses Opaque alloc_meta loc_in_bounds alloc_alive alloc_global
  fntbl_entry heap_pointsto_mbyte heap_pointsto alloc_alive_loc
  freeable.

Notation "l ↦{ q } v" := (heap_pointsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" := (heap_pointsto l 1 v) (at level 20) : bi_scope.
Notation "l ↦{ q '}' ':' P" := (∃ v, l ↦{ q } v ∗ P v)%I
  (at level 20, q at level 50, format "l  ↦{ q '}' ':'  P") : bi_scope.
Notation "l ↦: P " := (∃ v, l ↦ v ∗ P v)%I
  (at level 20, format "l  ↦:  P") : bi_scope.

Definition heap_pointsto_layout `{!heapG Σ} (l : loc) (q : Qp) (ly : layout) : iProp Σ :=
  (∃ v, ⌜v `has_layout_val` ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗ l ↦{q} v).
Notation "l ↦{ q }| ly |" := (heap_pointsto_layout l q ly)
  (at level 20, q at level 50, format "l  ↦{ q }| ly |") : bi_scope.
Notation "l ↦| ly | " := (heap_pointsto_layout l 1%Qp ly)
  (at level 20, format "l  ↦| ly |") : bi_scope.

Section heap.
  Implicit Types h : heap.

  Lemma to_heapUR_valid h : ✓ to_heapUR h.
  Proof. intros a. rewrite lookup_fmap. by case (h !! a) => // -[?[]?]. Qed.

  Lemma lookup_to_heapUR_None h a :
    h !! a = None → to_heapUR h !! a = None.
  Proof. by rewrite /to_heapUR lookup_fmap=> ->. Qed.

  Lemma to_heapUR_insert a hc h :
    to_heapUR (<[a := hc]> h) = <[a := to_heap_cellR hc]> (to_heapUR h).
  Proof. by rewrite /to_heapUR fmap_insert. Qed.

  Lemma to_heapUR_delete h a :
    to_heapUR (delete a h) = delete a (to_heapUR h).
  Proof. by rewrite /to_heapUR fmap_delete. Qed.
End heap.

Section fntbl.
  Context `{!heapG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : state.
  Implicit Types E : coPset.

  Lemma fntbl_entry_lookup t f fn :
    fntbl_ctx t -∗ fntbl_entry f fn -∗ ⌜∃ a, f = fn_loc a ∧ t !! a = Some fn⌝.
  Proof.
    rewrite fntbl_entry_eq.
    iIntros "Hctx (%a&->&Hentry)".
    iDestruct (ghost_map_lookup with "Hctx Hentry") as %?.
    by eauto.
  Qed.
End fntbl.

Section alloc_meta.
  Context `{!heapG Σ}.
  Implicit Types am : allocs.

  Lemma alloc_meta_mono id a1 a2 :
    alloc_same_range a1 a2 →
    a1.(al_kind) = a2.(al_kind) →
    alloc_meta id a1 -∗ alloc_meta id a2.
  Proof.
    destruct a1 as [????], a2 as [????] => -[/= <- <-] <-.
    rewrite alloc_meta_eq. iIntros "$".
  Qed.

  Lemma alloc_meta_agree id a1 a2 :
    alloc_meta id a1 -∗ alloc_meta id a2 -∗ ⌜alloc_same_range a1 a2⌝.
  Proof.
    destruct a1 as [????], a2 as [????]. rewrite alloc_meta_eq /alloc_same_range.
    iIntros "H1 H2". by iDestruct (ghost_map_elem_agree with "H1 H2") as %[=->->].
  Qed.

  Lemma alloc_meta_alloc am id al :
    am !! id = None →
    alloc_meta_ctx am ==∗
    alloc_meta_ctx (<[id := al]> am) ∗ alloc_meta id al.
  Proof.
    move => Hid. rewrite alloc_meta_eq. iIntros "Hctx".
    iMod (ghost_map_insert_persist with "Hctx") as "[? $]". { by rewrite lookup_fmap fmap_None. }
    by rewrite -fmap_insert.
  Qed.

  Lemma alloc_meta_to_loc_in_bounds l id (pre suf : nat) al:
    l.(loc_p) = ProvAlloc id →
    al.(al_start) + pre ≤ l.(loc_a) ∧ l.(loc_a) + suf ≤ al_end al →
    allocation_in_range al →
    alloc_meta id al -∗ loc_in_bounds l pre suf.
  Proof.
    iIntros (?[??]?) "Hr". rewrite loc_in_bounds_eq.
    iLeft. iExists id, al. by iFrame "Hr".
  Qed.

  Lemma alloc_meta_lookup am id al :
    alloc_meta_ctx am -∗
    alloc_meta id al -∗
    ⌜∃ al', am !! id = Some al' ∧ alloc_same_range al al' ∧ al.(al_kind) = al'.(al_kind)⌝.
  Proof.
    rewrite alloc_meta_eq. iIntros "Htbl Hf".
    iDestruct (ghost_map_lookup with "Htbl Hf") as %Hlookup.
    iPureIntro. move: Hlookup. rewrite lookup_fmap fmap_Some => -[[????][?[???]]].
    by eexists _.
  Qed.

  Lemma alloc_meta_ctx_same_range am id al1 al2 :
    am !! id = Some al1 →
    alloc_same_range al1 al2 →
    al1.(al_kind) = al2.(al_kind) →
    alloc_meta_ctx am = alloc_meta_ctx (<[id := al2]> am).
  Proof.
    move => Hid [Heq1 Heq2] Heq3.
    rewrite /alloc_meta_ctx /to_alloc_meta_map fmap_insert insert_id; first done.
    rewrite lookup_fmap Hid /=. destruct al1, al2; naive_solver.
  Qed.

  Lemma alloc_meta_ctx_killed am id al :
    am !! id = Some al →
    alloc_meta_ctx am = alloc_meta_ctx (<[id := killed al]> am).
  Proof. move => ?. by apply: alloc_meta_ctx_same_range. Qed.
End alloc_meta.

Section alloc_alive.
  Context `{!heapG Σ}.
  Implicit Types am : allocs.

  Lemma alloc_alive_alloc am id al :
    am !! id = None →
    alloc_alive_ctx am ==∗
    alloc_alive_ctx (<[id := al]> am) ∗ alloc_alive id (DfracOwn 1) (al.(al_alive)).
  Proof.
    iIntros (?) "Hctx". rewrite alloc_alive_eq.
    iMod (ghost_map_insert with "Hctx") as "[? $]". { by rewrite lookup_fmap fmap_None. }
    by rewrite -fmap_insert.
  Qed.

  Lemma alloc_alive_lookup am id q a:
    alloc_alive_ctx am -∗ alloc_alive id q a -∗ ⌜∃ al, am !! id = Some al ∧ al.(al_alive) = a⌝.
  Proof.
    rewrite /alloc_alive_ctx alloc_alive_eq. iIntros "Hctx Ha".
    iDestruct (ghost_map_lookup with "Hctx Ha") as %Hlookup.
    iPureIntro. move: Hlookup. rewrite lookup_fmap fmap_Some. naive_solver.
  Qed.

  Lemma alloc_alive_kill am id al a:
    alloc_alive_ctx am -∗
    alloc_alive id (DfracOwn 1) a ==∗
    alloc_alive_ctx (<[id := killed al]> am) ∗ alloc_alive id (DfracOwn 1) false.
  Proof.
    rewrite alloc_alive_eq. iIntros "Hctx Ha".
    iMod (ghost_map_update with "Hctx Ha") as "[? $]".
    by rewrite /alloc_alive_ctx/to_alloc_alive_map fmap_insert.
  Qed.
End alloc_alive.

Section loc_in_bounds.
  Context `{!heapG Σ}.

  Lemma loc_in_bounds_shift_pre l k n :
    loc_in_bounds l k n ⊣⊢ loc_in_bounds (l +ₗ -k) 0 (k + n).
  Proof.
    rewrite loc_in_bounds_eq. iSplit.
    - iDestruct 1 as "[H1 | H1]"; first last.
      { iRight. iDestruct "H1" as "(% & % & % & -> & ->)"; simpl.
        rewrite Nat2Z.inj_0 Z.add_0_r. done. }
      iDestruct "H1" as "(%id & %al & % & % & % & % & ?)".
      iLeft. iExists _, _. simpl. iFrame "∗ %".
      iPureIntro; split; lia.
    - iDestruct 1 as "[H1 | H1]"; first last.
      { iRight. iDestruct "H1" as "(%Ha1 & %Ha2 & %Ha3 & _ & %)"; simpl.
        assert (k = 0%nat) as -> by lia. assert (n = 0%nat) as -> by lia.
        move: Ha1 Ha2 Ha3. rewrite Nat2Z.inj_0 shift_loc_0_nat => ???. done. }
      iDestruct "H1" as "(%id & %al & % & % & % & % & ?)".
      iLeft. iExists _, _. simpl in *. iFrame "∗ %".
      iPureIntro; split; lia.
  Qed.

  Lemma loc_in_bounds_shift_suf l k n :
    loc_in_bounds l k n ⊣⊢ loc_in_bounds (l +ₗ n) (k + n) 0.
  Proof.
    rewrite loc_in_bounds_eq. iSplit.
    - iDestruct 1 as "[H1 | H1]"; first last.
      { iRight. iDestruct "H1" as "(% & % & % & -> & ->)"; simpl.
        rewrite Nat2Z.inj_0 Z.add_0_r. done. }
      iDestruct "H1" as "(%id & %al & % & % & % & % & ?)".
      iLeft. iExists _, _. simpl. iFrame "∗ %".
      iPureIntro; split; lia.
    - iDestruct 1 as "[H1 | H1]"; first last.
      { iRight. iDestruct "H1" as "(%Ha1 & %Ha2 & %Ha3 & % & _)"; simpl.
        assert (k = 0%nat) as -> by lia. assert (n = 0%nat) as -> by lia.
        move: Ha1 Ha2 Ha3. rewrite Nat2Z.inj_0 shift_loc_0_nat => ???. done. }
      iDestruct "H1" as "(%id & %al & % & % & % & % & ?)".
      iLeft. iExists _, _. simpl in *. iFrame "∗ %".
      iPureIntro; split; lia.
  Qed.

  Lemma loc_in_bounds_split_pre l (k n m : nat) :
    loc_in_bounds (l +ₗ -n) m 0 ∗ loc_in_bounds l n k ⊣⊢ loc_in_bounds l (n + m) k.
  Proof.
    rewrite loc_in_bounds_eq. iSplit.
    - iIntros "[H1 H2]".
      iDestruct "H1" as "[H1 | H1]"; first last.
      { iDestruct "H1" as "(% & % & % & -> & _)".
        rewrite Nat.add_0_r. done. }
      iDestruct "H1" as (id al Hl1 Ha1 Ha2 Ha3) "#H1".
      iDestruct "H2" as "[H2 | H2]"; first last.
      { iDestruct "H2" as "(% & % & % & -> & ->)". simpl in *. congruence. }
      iDestruct "H2" as (?? Hl2 ? Hend ?) "#H2".
      move: Hl1 Hl2 => /= Hl1 Hl2. iLeft. iExists id, al.
      destruct l. unfold al_end in *. simpl in *. simplify_eq.
      iDestruct (alloc_meta_agree with "H2 H1") as %[? <-].
      iFrame "H1". iPureIntro. rewrite /shift_loc /= in Hend. naive_solver lia.
    - iIntros "H". iDestruct "H" as "[H | H]"; first last.
      { iDestruct "H" as "(% & % & % & % & ->)". replace n with 0%nat by lia.
        replace m with 0%nat by lia. rewrite shift_loc_0_nat.
        iSplit; iRight; done. }
      iDestruct "H" as (id al ????) "#H".
      iSplit; iLeft; iExists id, al; iFrame "H"; iPureIntro; split_and! => //=; lia.
  Qed.

  Lemma loc_in_bounds_split_suf l k n m :
    loc_in_bounds l k n ∗ loc_in_bounds (l +ₗ n) 0 m ⊣⊢ loc_in_bounds l k (n + m).
  Proof.
    rewrite loc_in_bounds_eq. iSplit.
    - iIntros "[H1 H2]".
      iDestruct "H1" as "[H1 | H1]"; first last.
      { iDestruct "H1" as "(% & % & % & -> & ->)".
        rewrite shift_loc_0_nat. done. }
      iDestruct "H1" as (id al Hl1 ???) "#H1".
      iDestruct "H2" as "[H2 | H2]"; first last.
      { iDestruct "H2" as "(_ & _ & _ & _ & ->)". rewrite Nat.add_0_r.
        iLeft. iExists _, _. by iFrame "% ∗". }
      iDestruct "H2" as (?? Hl2 ? Hend ?) "#H2".
      move: Hl1 Hl2 => /= Hl1 Hl2. iLeft. iExists id, al.
      destruct l. unfold al_end in *. simpl in *. simplify_eq.
      iDestruct (alloc_meta_agree with "H2 H1") as %[? <-].
      iFrame "H1". iPureIntro. rewrite /shift_loc /= in Hend. naive_solver lia.
    - iIntros "H". iDestruct "H" as "[H | H]"; first last.
      { iDestruct "H" as "(% & % & % & -> & %)". replace n with 0%nat by lia.
        replace m with 0%nat by lia. rewrite shift_loc_0_nat.
        iSplit; iRight; done. }
      iDestruct "H" as (id al ????) "#H".
      iSplit; iLeft; iExists id, al; iFrame "H"; iPureIntro; split_and! => //=; lia.
  Qed.

  Lemma loc_in_bounds_split_pre_suf l k n :
    loc_in_bounds l k 0 ∗ loc_in_bounds l 0 n ⊣⊢ loc_in_bounds l k n.
  Proof.
    rewrite -(loc_in_bounds_split_suf l k 0 n) shift_loc_0_nat//.
  Qed.

  Lemma loc_in_bounds_split_mul_S l k n m :
    loc_in_bounds l k n ∗ loc_in_bounds (l +ₗ n) 0 (n * m) ⊣⊢ loc_in_bounds l k (n * S m).
  Proof.
    have ->: (n * S m = n + n * m)%nat by lia.
    etrans; [ by apply loc_in_bounds_split_suf | done ].
  Qed.

  Lemma loc_in_bounds_shorten_suf l k n m:
    (m ≤ n)%nat ->
    loc_in_bounds l k n -∗ loc_in_bounds l k m.
  Proof.
    move => ?. rewrite -(Nat.sub_add m n) // Nat.add_comm -loc_in_bounds_split_suf. iIntros "[$ _]".
  Qed.
  Lemma loc_in_bounds_shorten_pre l k n m:
    (m ≤ n)%nat ->
    loc_in_bounds l n k -∗ loc_in_bounds l m k.
  Proof.
    move => ?. rewrite -(Nat.sub_add m n) // Nat.add_comm -loc_in_bounds_split_pre. iIntros "[_ $]".
  Qed.

  Local Lemma loc_in_bounds_offset_suf l1 l2 (suf1 suf2 : nat):
    l1.(loc_p) = l2.(loc_p) →
    l1.(loc_a) ≤ l2.(loc_a) →
    l2.(loc_a) + suf2 ≤ l1.(loc_a) + suf1 →
    loc_in_bounds l1 0 suf1 -∗ loc_in_bounds l2 0 suf2.
  Proof.
    move => ???. have ->: (l2 = l1 +ₗ (l2.(loc_a) - l1.(loc_a))).
    { rewrite /shift_loc. destruct l1, l2 => /=. f_equal; [done| lia]. }
    have -> : suf1 = (Z.to_nat (l2.(loc_a) - l1.(loc_a)) + Z.to_nat (suf1 - (l2.(loc_a) - l1.(loc_a))))%nat by lia.
    rewrite -loc_in_bounds_split_suf. iIntros "[_ Hlib]". rewrite Z2Nat.id; [|lia].
    iApply (loc_in_bounds_shorten_suf with "Hlib"). lia.
  Qed.

  Local Lemma loc_in_bounds_offset_pre l1 l2 (pre1 pre2 : nat):
    l1.(loc_p) = l2.(loc_p) →
    l2.(loc_a) ≤ l1.(loc_a) →
    l1.(loc_a) - pre1 ≤ l2.(loc_a) - pre2 →
    loc_in_bounds l1 pre1 0 -∗ loc_in_bounds l2 pre2 0.
  Proof.
    move => ???. have ->: (l2 = l1 +ₗ -(l1.(loc_a) - l2.(loc_a))).
    { rewrite /shift_loc. destruct l1, l2 => /=. f_equal; [done| lia]. }
    have -> : pre1 = (Z.to_nat (l1.(loc_a) - l2.(loc_a)) + Z.to_nat (pre1 - (l1.(loc_a) - l2.(loc_a))))%nat by lia.
    rewrite -loc_in_bounds_split_pre. iIntros "[Hlib _]". rewrite Z2Nat.id; [|lia].
    iApply (loc_in_bounds_shorten_pre with "Hlib"). lia.
  Qed.

  Lemma loc_in_bounds_offset l1 l2 (pre1 pre2 suf1 suf2 : nat):
    l1.(loc_p) = l2.(loc_p) →
    l1.(loc_a) + pre2 ≤ l2.(loc_a) + pre1 ->
    l2.(loc_a) + suf2 ≤ l1.(loc_a) + suf1 ->
    loc_in_bounds l1 pre1 suf1 -∗ loc_in_bounds l2 pre2 suf2.
  Proof.
    move => ???. iIntros "Hlib".
    destruct (decide (l1.(loc_a) ≤ l2.(loc_a))) as [ Hle | Hle].
    - iPoseProof (loc_in_bounds_shift_pre with "Hlib") as "Hlib".
      iApply (loc_in_bounds_shift_pre). iApply (loc_in_bounds_offset_suf with "Hlib").
      + done.
      + simpl. rewrite !Z.add_opp_r.
        apply Z.le_sub_le_add. rewrite [pre1 + _]Z.add_comm. done.
      + simpl. rewrite !Z.add_opp_r !Nat2Z.inj_add !Z.sub_add_simpl_r_l. done.
    - iPoseProof (loc_in_bounds_shift_suf with "Hlib") as "Hlib".
      iApply (loc_in_bounds_shift_suf). iApply (loc_in_bounds_offset_pre with "Hlib").
      + done.
      + done.
      + simpl. rewrite !Nat2Z.inj_add !Z.add_add_simpl_r_r.
        apply Z.le_sub_le_add. rewrite [pre1 + _]Z.add_comm. done.
  Qed.

  Lemma loc_in_bounds_to_heap_loc_in_bounds l heap pre suf :
    loc_in_bounds l pre suf -∗ heap_state_ctx heap -∗ ⌜heap_state_loc_in_bounds (l +ₗ -pre) suf heap⌝.
  Proof.
    rewrite loc_in_bounds_eq.
    iIntros "Hb (?&?&Hctx&?)". iDestruct "Hb" as "[Hb | Hb]".
    - iDestruct "Hb" as (id al ????) "Hb".
      iDestruct (alloc_meta_lookup with "Hctx Hb") as %[al' [?[[??]?]]].
      iLeft. iExists id, al'. iPureIntro. unfold allocation_in_range, al_end in *.
      naive_solver lia.
    - iDestruct "Hb" as "(% & % & % & -> & ->)". iRight.
      rewrite Nat2Z.inj_0; simpl. rewrite Z.add_0_r. done.
  Qed.
  Lemma loc_in_bounds_to_heap_loc_in_bounds' l heap suf :
    loc_in_bounds l 0 suf -∗ heap_state_ctx heap -∗ ⌜heap_state_loc_in_bounds l suf heap⌝.
  Proof.
    iIntros "Hb Ha". iPoseProof (loc_in_bounds_to_heap_loc_in_bounds with "Hb Ha") as "Hb".
    rewrite shift_loc_0_nat. done.
  Qed.

  Lemma loc_in_bounds_ptr_in_range l pre suf :
    loc_in_bounds l pre suf -∗
    ⌜0 ≤ l.(loc_a) - pre ∧ l.(loc_a) + suf ≤ max_alloc_end_zero⌝.
  Proof.
    rewrite loc_in_bounds_eq. iIntros "[Hlib | Hlib]".
    - iDestruct "Hlib" as (?????[??]) "?". iPureIntro.
      unfold max_alloc_end, min_alloc_start in *.
      lia.
    - iDestruct "Hlib" as "(% & % & % & -> & ->)". iPureIntro. lia.
  Qed.
  Lemma loc_in_bounds_ptr_in_range_alloc l pre suf :
    l.(loc_p) ≠ ProvNone →
    loc_in_bounds l pre suf -∗
    ⌜min_alloc_start ≤ l.(loc_a) - pre ∧ l.(loc_a) + suf ≤ max_alloc_end⌝.
  Proof.
    intros ?.
    rewrite loc_in_bounds_eq. iIntros "[Hlib | Hlib]".
    - iDestruct "Hlib" as (?????[??]) "?". iPureIntro. lia.
    - iDestruct "Hlib" as "(% & % & % & -> & ->)". iPureIntro. done.
  Qed.

  Lemma loc_in_bounds_in_range_usize l pre suf :
    loc_in_bounds l pre suf -∗ ⌜l.(loc_a) ∈ USize⌝.
  Proof.
    iIntros "Hl". iDestruct (loc_in_bounds_ptr_in_range with "Hl") as %Hrange.
    iPureIntro. move: Hrange.
    rewrite int_elem_of_it_iff.
    rewrite /min_alloc_start /bytes_per_addr /bytes_per_addr_log /=.
    move => [??]. split; cbn; first by lia.
    lia.
  Qed.

  Lemma loc_in_bounds_is_alloc l pre suf :
    loc_in_bounds l pre suf -∗
    ⌜(∃ aid, l.(loc_p) = ProvAlloc aid) ∨ (l.(loc_p) = ProvNone ∧ pre = 0%nat ∧ suf = 0%nat)⌝.
  Proof.
    rewrite loc_in_bounds_eq. iIntros "[H|H]".
    - iDestruct "H" as (id ?????) "H". iPureIntro. left. by exists id.
    - iDestruct "H" as "(% & _ & _ & % & %)". iPureIntro. right. done.
  Qed.

  Lemma loc_in_bounds_prov_none l :
    l.(loc_p) = ProvNone →
    0 ≤ l.(loc_a) →
    l.(loc_a) ≤ max_alloc_end_zero →
    ⊢ loc_in_bounds l 0 0.
  Proof.
    intros ???. rewrite loc_in_bounds_eq. iRight. done.
  Qed.

  Lemma loc_in_bounds_sl_offset sl m k l ly :
    snd <$> sl_members sl !! k = Some ly →
    loc_in_bounds l m (ly_size sl) -∗
    loc_in_bounds (l +ₗ offset_of_idx (sl_members sl) k) 0 (ly_size ly).
  Proof.
    iIntros (Hlook).
    iApply loc_in_bounds_offset.
    - done.
    - simpl. lia.
    - rewrite {2}/ly_size /=.
      elim: (sl_members sl) k l Hlook => //.
      intros [n ly0] s IH k l Hlook.
      rewrite /offset_of_idx.
      destruct k as [ | k]; simpl in *.
      + injection Hlook as [= ->]. lia.
      + eapply (IH k (l +ₗ (ly_size ly0))) in Hlook.
        simpl in Hlook. move: Hlook. rewrite /offset_of_idx /fmap. lia.
  Qed.

  Lemma loc_in_bounds_array_offset (len : nat) m (k : nat) l ly :
    k < len →
    loc_in_bounds l m (ly_size ly * len) -∗
    loc_in_bounds (l offset{ly}ₗ k) 0 (ly_size ly).
  Proof.
    iIntros (Hlen).
    iApply loc_in_bounds_offset.
    - done.
    - simpl. lia.
    - simpl.
      rewrite -Z.add_assoc.
      assert (ly_size ly * (k + 1) ≤ ly_size ly * len)%Z as Ha by nia.
      rewrite Z.mul_add_distr_l Z.mul_1_r in Ha.
      rewrite Nat2Z.inj_mul. eapply Zplus_le_compat_l. done.
  Qed.
End loc_in_bounds.

Section heap.
  Context `{!heapG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : state.
  Implicit Types E : coPset.

  Global Instance heap_pointsto_mbyte_tl l q v : Timeless (heap_pointsto_mbyte l q v).
  Proof.  rewrite heap_pointsto_mbyte_eq. apply _. Qed.

  Global Instance heap_pointsto_mbyte_frac l v :
    Fractional (λ q, heap_pointsto_mbyte l q v)%I.
  Proof.
    intros p q. rewrite heap_pointsto_mbyte_eq. iSplit.
    - iDestruct 1 as (id me) "[%Hid [H1 H2]]". iSplitL "H1"; iExists id, me; by iSplit.
    - iIntros "[H1 H2]". iDestruct "H1" as (??) "[% H1]". iDestruct "H2" as (??) "[% H2]".
      destruct l; simplify_eq/=.
      iAssert (⌜me = me0⌝)%I as %->.
      { iCombine "H1 H2" as "H". rewrite own_valid internal_cmra_valid_discrete.
        iDestruct "H" as %Hvalid. iPureIntro.
        move: Hvalid => /= /auth_frag_valid /singleton_valid.
        move => -[] /= [_ Hls] _.
        simpl in Hls. destruct Hls as [_ Hls].
        by apply to_agree_op_inv_L. }
      iExists _, _. iSplit; first done. by iSplitL "H1".
  Qed.

  Global Instance heap_pointsto_mbyte_as_fractional l q v:
    AsFractional (heap_pointsto_mbyte l q v) (λ q, heap_pointsto_mbyte l q v)%I q.
  Proof. split; [done|]. apply _. Qed.

  Global Instance heap_pointsto_timeless l q v : Timeless (l↦{q}v).
  Proof.  rewrite heap_pointsto_eq. apply _. Qed.

  Global Instance heap_pointsto_fractional l v: Fractional (λ q, l ↦{q} v)%I.
  Proof. rewrite heap_pointsto_eq. apply _. Qed.

  Global Instance heap_pointsto_as_fractional l q v:
    AsFractional (l ↦{q} v) (λ q, l ↦{q} v)%I q.
  Proof. split; first done. apply _. Qed.

  Lemma heap_pointsto_loc_in_bounds l q v:
    l ↦{q} v -∗ loc_in_bounds l 0 (length v).
  Proof. rewrite heap_pointsto_eq. iIntros "[$ _]". Qed.

  Lemma heap_pointsto_is_alloc l q v :
    l ↦{q} v -∗
    ⌜(∃ aid, l.(loc_p) = ProvAlloc aid) ∨ (l.(loc_p) = ProvNone ∧ v = [])⌝.
  Proof.
    iIntros "Hl". iPoseProof (heap_pointsto_loc_in_bounds with "Hl") as "Hlb".
    iPoseProof (loc_in_bounds_is_alloc with "Hlb") as "%Ha".
    iPoseProof (loc_in_bounds_ptr_in_range with "Hlb") as "%Hran".
    iPureIntro. rewrite /min_alloc_start in Hran. destruct Hran as [Hran _].
    destruct Ha as [ | [? ?]]; first naive_solver.
    right. destruct v; simpl in *; eauto with lia.
  Qed.

  Lemma heap_pointsto_loc_in_bounds_0 l q v:
    l ↦{q} v -∗ loc_in_bounds l 0 0.
  Proof.
    iIntros "Hl". iApply loc_in_bounds_shorten_suf; last first.
    - by iApply heap_pointsto_loc_in_bounds.
    - lia.
  Qed.

  Lemma heap_pointsto_nil l q:
    l ↦{q} [] ⊣⊢ loc_in_bounds l 0 0.
  Proof. rewrite heap_pointsto_eq/heap_pointsto_def /=. solve_sep_entails. Qed.

  Lemma heap_pointsto_cons_mbyte l b v q:
    l ↦{q} (b::v) ⊣⊢ heap_pointsto_mbyte l q b ∗ loc_in_bounds l 0 1 ∗ (l +ₗ 1) ↦{q} v.
  Proof.
    rewrite heap_pointsto_eq/heap_pointsto_def /= shift_loc_0. setoid_rewrite shift_loc_assoc.
    have Hn:(∀ n, Z.of_nat (S n) = 1 + n) by lia. setoid_rewrite Hn.
    have ->:(∀ n, S n = 1 + n)%nat by lia.
    rewrite -loc_in_bounds_split_suf.
    solve_sep_entails.
  Qed.

  Lemma heap_pointsto_cons l b v q:
    l ↦{q} (b::v) ⊣⊢ l ↦{q} [b] ∗ (l +ₗ 1) ↦{q} v.
  Proof.
    rewrite heap_pointsto_cons_mbyte !assoc. f_equiv.
    rewrite heap_pointsto_eq/heap_pointsto_def /= shift_loc_0.
    solve_sep_entails.
  Qed.

  Lemma heap_pointsto_app l v1 v2 q:
    l ↦{q} (v1 ++ v2) ⊣⊢ l ↦{q} v1 ∗ (l +ₗ length v1) ↦{q} v2.
  Proof.
    elim: v1 l.
    - move => l /=. rewrite heap_pointsto_nil shift_loc_0.
      iSplit; [ iIntros "Hl" | by iIntros "[_ $]" ].
      iSplit => //. by iApply heap_pointsto_loc_in_bounds_0.
    - move => b v1 IH l /=.
      rewrite heap_pointsto_cons IH assoc -heap_pointsto_cons.
      rewrite shift_loc_assoc.
      by have -> : (∀ n : nat, 1 + n = S n) by lia.
  Qed.

  Lemma heap_pointsto_mbyte_agree l q1 q2 v1 v2 :
    heap_pointsto_mbyte l q1 v1 ∗ heap_pointsto_mbyte l q2 v2 ⊢ ⌜v1 = v2⌝.
  Proof.
    rewrite heap_pointsto_mbyte_eq.
    iIntros "[H1 H2]".
    iDestruct "H1" as (??) "[% H1]". iDestruct "H2" as (??) "[% H2]".
    destruct l; simplify_eq/=.
    iCombine "H1 H2" as "H". rewrite own_valid internal_cmra_valid_discrete.
    iDestruct "H" as %Hvalid. iPureIntro.
    move: Hvalid => /= /auth_frag_valid /singleton_valid.
    move => -[] /= _ /to_agree_op_inv_L => ?. by simplify_eq.
  Qed.

  Lemma heap_pointsto_agree l q1 q2 v1 v2 :
    length v1 = length v2 →
    l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    elim: v1 v2 l. 1: by iIntros ([] ??)"??".
    move => ?? IH []//=???[?].
    rewrite !heap_pointsto_cons_mbyte.
    iIntros "[? [_ ?]] [? [_ ?]]".
    iDestruct (IH with "[$] [$]") as %-> => //.
    by iDestruct (heap_pointsto_mbyte_agree with "[$]") as %->.
  Qed.

  Lemma heap_pointsto_layout_has_layout l ly :
    l ↦|ly| -∗ ⌜l `has_layout_loc` ly⌝.
  Proof. iIntros "(% & % & % & ?)". done. Qed.

  Lemma heap_pointsto_ptr_in_range l q v :
    l ↦{q} v -∗ ⌜0 ≤ l.(loc_a) ∧ l.(loc_a) + length v ≤ max_alloc_end_zero⌝.
  Proof.
    iIntros "Hl". iPoseProof (heap_pointsto_loc_in_bounds with "Hl") as "Hlb".
    iPoseProof (loc_in_bounds_ptr_in_range with "Hlb") as "%Ha".
    rewrite Nat2Z.inj_0 Z.sub_0_r in Ha. done.
  Qed.

  Lemma heap_pointsto_prov_none_nil l q :
    l.(loc_p) = ProvNone →
    0 ≤ l.(loc_a) →
    l.(loc_a) ≤ max_alloc_end_zero →
    ⊢ l ↦{q} [].
  Proof.
    intros ???. rewrite heap_pointsto_eq.
    iSplit; last done. by iApply loc_in_bounds_prov_none.
  Qed.

  Lemma heap_alloc_st l h v aid :
    l.(loc_p) = ProvAlloc aid →
    heap_range_free h l.(loc_a) (length v) →
    heap_ctx h ==∗
      heap_ctx (heap_alloc l.(loc_a) v aid h) ∗
      ([∗ list] i↦b ∈ v, heap_pointsto_mbyte_st (RSt 0 0) (l +ₗ i) aid 1 b).
  Proof.
    move => Haid Hfree. destruct l as [? a]. simplify_eq/=.
    have [->|Hv] := decide(v = []); first by iIntros "$ !>" => //=.
    rewrite -big_opL_commute1 // -(big_opL_commute auth_frag) /=.
    iIntros "H". rewrite -own_op. iApply own_update; last done.
    apply auth_update_alloc.
    elim: v a Hfree {Hv} => // b bl IH a Hfree.
    rewrite (big_opL_consZ_l (λ k _, _ (_ k) _ )) /= Z.add_0_r.
    etrans. { apply (IH (a + 1)). move => a' Ha'. apply Hfree => /=. lia. }
    rewrite -insert_singleton_op; last first.
    { rewrite -None_equiv_eq big_opL_commute None_equiv_eq big_opL_None=> l' v' ?.
      rewrite lookup_singleton_None. lia. }
    rewrite /heap_alloc /heap_update -/heap_update.
    rewrite to_heapUR_insert. setoid_rewrite Z.add_assoc.
    apply alloc_local_update; last done. apply lookup_to_heapUR_None.
    rewrite heap_update_lookup_not_in_range /=; last lia.
    apply Hfree => /=. lia.
  Qed.

  Lemma heap_alloc l h v id al :
    l.(loc_p) = ProvAlloc id →
    heap_range_free h l.(loc_a) (length v) →
    al.(al_start) = l.(loc_a) →
    al.(al_len) = length v →
    allocation_in_range al →
    alloc_meta id al -∗
    alloc_alive id (DfracOwn 1) true -∗
    heap_ctx h ==∗
      heap_ctx (heap_alloc l.(loc_a) v id h) ∗
      l ↦ v ∗
      freeable l (length v) 1 al.(al_kind).
  Proof.
    iIntros (Hid Hfree Hstart Hlen Hrange) "#Hr Hal Hctx".
    iMod (heap_alloc_st with "Hctx") as "[$ Hl]" => //.
    iModIntro. rewrite heap_pointsto_eq /heap_pointsto_def.
    rewrite heap_pointsto_mbyte_eq /heap_pointsto_mbyte_def.
    iSplitR "Hal"; last first; last iSplit.
    - rewrite freeable_eq. iExists id. iFrame. iSplit => //.
      by iApply (alloc_meta_mono with "Hr").
    - rewrite loc_in_bounds_eq. iLeft. iExists id, al. iFrame "Hr".
      rewrite /al_end. iPureIntro. naive_solver lia.
    - iApply (big_sepL_impl with "Hl").
      iIntros (???) "!> H". iExists id. by iFrame.
  Qed.

  (** Decomposes CMRA inclusion on [to_lock_stateR] into structural relationships. *)
  Lemma to_lock_stateR_included ls ls'' :
    Some (to_lock_stateR ls) ≼ Some (to_lock_stateR ls'') →
    match ls with
    | WSt => ls'' = WSt
    | RSt n me => ∃ n', ls'' = RSt (n + n') me
    | PendingSt _ => ∃ hist', ls'' = PendingSt hist'
    end.
  Proof.
    intros Hincl. apply Some_included in Hincl as [Heq | Hincl].
    - (* ≡ branch: case split on lock_state constructors *)
      destruct ls as [|n me|hist], ls'' as [|n'' me''|hist''];
        simpl in Heq; try (by inversion Heq);
        try (by inversion Heq as [| ? ? Heq' |]; inversion Heq').
      + apply (inj Cinr) in Heq. apply (inj Cinl) in Heq. simpl in Heq.
        destruct Heq as [Hn Hme].
        simpl in Hn, Hme.
        apply leibniz_equiv in Hn. apply (inj to_agree) in Hme. apply leibniz_equiv in Hme. subst.
        exists O. rewrite Nat.add_0_r. done.
      + inversion Heq as [| ? ? Heq' |]. inversion Heq' as [| ? ? Heq'' |].
        exists hist''. done.
    - (* ≼ branch: only RSt/RSt survives (exclusive types → False) *)
      destruct ls as [|n me|hist], ls'' as [|n'' me''|hist'']; simpl in Hincl.
      all: try (exfalso; revert Hincl;
                first [rewrite Cinr_included | idtac];
                rewrite csum_included;
                intros [? | [(?&?&?&?&?) | (?&?&?&?&?)]]; discriminate).
      + done.
      + rewrite Cinr_included Cinl_included in Hincl.
        apply prod_included in Hincl as [Hn Hme].
        simpl in Hn, Hme.
        apply to_agree_included, leibniz_equiv in Hme. subst.
        destruct Hn as [k ->%leibniz_equiv]. by exists k.
      + by eauto.
  Qed.

  (** Converts CMRA equivalence on [to_lock_stateR] to structural equality.
      [agreeR natO] component requires explicit decomposition (not LeibnizEquiv). *)
  Lemma to_lock_stateR_equiv ls ls'' :
    to_lock_stateR ls ≡ to_lock_stateR ls'' →
    match ls with
    | WSt => ls'' = WSt
    | RSt n me => ls'' = RSt n me
    | PendingSt _ => ∃ hist', ls'' = PendingSt hist'
    end.
  Proof.
    intros Heq. destruct ls as [|n me|hist], ls'' as [|n'' me''|hist''];
      simpl in Heq; try (by inversion Heq);
      try (by inversion Heq as [| ? ? Heq' |]; inversion Heq').
    - apply (inj Cinr) in Heq. apply (inj Cinl) in Heq. simpl in Heq.
      destruct Heq as [Hn Hme]. simpl in Hn, Hme.
      apply leibniz_equiv in Hn. apply (inj to_agree) in Hme. apply leibniz_equiv in Hme. subst.
      done.
    - exists hist''. done.
  Qed.

  Lemma heap_pointsto_mbyte_lookup_q ls l aid h q b:
    heap_ctx h -∗
    heap_pointsto_mbyte_st ls l aid q b -∗
    ⌜∃ ep : nat,
        match ls with
        | RSt n me => ∃ n', h !! l.(loc_a) = Some (HeapCell aid (RSt (n+n') me) b ep)
        | WSt => h !! l.(loc_a) = Some (HeapCell aid WSt b ep)
        | PendingSt _ => ∃ hist', h !! l.(loc_a) = Some (HeapCell aid (PendingSt hist') b ep)
        end⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [[[q' ls'] dv]].
    rewrite /to_heapUR lookup_fmap fmap_Some_equiv.
    move=> [[[aid'' ls'' v' ep'] [Heq Hequiv]]] Hincl.
    move: Hincl. rewrite Hequiv /=.
    move=> /Some_pair_included_total_2 [/Some_pair_included] [_ Hincl]
      /to_agree_included ?; simplify_eq.
    apply to_lock_stateR_included in Hincl.
    exists ep'. destruct ls; naive_solver.
  Qed.

  Lemma heap_pointsto_mbyte_lookup_1 ls l aid h b:
    heap_ctx h -∗
    heap_pointsto_mbyte_st ls l aid 1%Qp b -∗
    ⌜∃ ep : nat, match ls with
      | PendingSt _ => ∃ hist', h !! l.(loc_a) = Some (HeapCell aid (PendingSt hist') b ep)
      | _ => h !! l.(loc_a) = Some (HeapCell aid ls b ep)
    end⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [[[q' ls'] dv]].
    rewrite /to_heapUR lookup_fmap fmap_Some_equiv.
    move=> [[[aid'' ls'' v' ep'] [? Hequiv]] Hincl].
    move: Hincl. rewrite Hequiv /=.
    move=> Hincl.
    apply (Some_included_exclusive _ _) in Hincl as [Hls_pair_equiv Hval]; last by destruct ls''.
    simpl in Hls_pair_equiv. destruct Hls_pair_equiv as [_ Hls_equiv].
    apply to_lock_stateR_equiv in Hls_equiv.
    apply (inj to_agree) in Hval. fold_leibniz. simplify_eq/=.
    destruct ls as [|n me|hist]; [subst ls'' | subst ls'' | destruct Hls_equiv as [hist' ->]];
      eauto.
  Qed.

  Lemma heap_pointsto_lookup_q flk l h q v:
    (∀ n me, flk (RSt n me) : Prop) →
    heap_ctx h -∗ l ↦{q} v -∗ ⌜heap_lookup_loc l v flk h⌝.
  Proof.
    iIntros (?) "Hh Hl".
    iInduction v as [|b v] "IH" forall (l) => //.
    rewrite heap_pointsto_cons_mbyte heap_pointsto_mbyte_eq /=.
    iDestruct "Hl" as "[Hb [_ Hl]]". iDestruct "Hb" as (?? Heq) "Hb".
    rewrite /heap_lookup_loc /=. iSplit; last by iApply ("IH" with "Hh Hl").
    iDestruct (heap_pointsto_mbyte_lookup_q with "Hh Hb") as %[ep [n' Hn]].
    by iExists _, _, _.
  Qed.

  Lemma heap_pointsto_lookup_1 (flk : lock_state → Prop) l h v:
    (∀ me, flk (RSt 0%nat me)) →
    heap_ctx h -∗ l ↦ v -∗ ⌜heap_lookup_loc l v flk h⌝.
  Proof.
    iIntros (?) "Hh Hl".
    iInduction v as [|b v] "IH" forall (l) => //.
    rewrite heap_pointsto_cons_mbyte heap_pointsto_mbyte_eq /=.
    iDestruct "Hl" as "[Hb [_ Hl]]". iDestruct "Hb" as (?? Heq) "Hb".
    rewrite /heap_lookup_loc /=. iSplit; last by iApply ("IH" with "Hh Hl").
    iDestruct (heap_pointsto_mbyte_lookup_1 with "Hh Hb") as %[ep Hl].
    by iExists _, _, _.
  Qed.

  Lemma heap_read_mbyte_vs h n1 n2 nf me l aid q b ep:
    h !! l.(loc_a) = Some (HeapCell aid (RSt (n1 + nf) me) b ep) →
    heap_ctx h -∗ heap_pointsto_mbyte_st (RSt n1 me) l aid q b
    ==∗ heap_ctx (<[l.(loc_a):=HeapCell aid (RSt (n2 + nf) me) b ep]> h)
        ∗ heap_pointsto_mbyte_st (RSt n2 me) l aid q b.
  Proof.
    intros Hσv. do 2 apply wand_intro_r. rewrite left_id -!own_op to_heapUR_insert.
    eapply own_update, auth_update, singleton_local_update.
    { by rewrite /to_heapUR lookup_fmap Hσv. }
    apply prod_local_update_1, prod_local_update_2, csum_local_update_r,
      csum_local_update_l.
    apply prod_local_update; simpl.
    - apply nat_local_update; lia.
    - done.
  Qed.

  Lemma heap_read_na h l q v :
    heap_ctx h -∗ l ↦{q} v ==∗
      ⌜heap_lookup_loc l v (λ st, ∃ n me, st = RSt n me) h⌝ ∗
      heap_ctx (heap_upd l v (λ st, if st is Some (RSt n me) then RSt (S n) me else WSt) h) ∗
      ∀ h2, heap_ctx h2 ==∗ ⌜heap_lookup_loc l v (λ st, ∃ n me, st = RSt (S n) me) h2⌝ ∗
        heap_ctx (heap_upd l v (λ st, if st is Some (RSt (S n) me) then RSt n me else WSt) h2) ∗ l ↦{q} v.
  Proof.
    iIntros "Hh Hv".
    iDestruct (heap_pointsto_lookup_q with "Hh Hv") as %Hat. 2: iSplitR => //. 1: by naive_solver.
    iInduction (v) as [|b v] "IH" forall (l Hat) => //=.
    { iFrame. by iIntros "!#" (?) "$ !#". }
    rewrite ->heap_pointsto_cons_mbyte, heap_pointsto_mbyte_eq.
    iDestruct "Hv" as "[Hb [Hlb Hl]]". iDestruct "Hb" as (?? Heq) "Hb".
    move: Hat. rewrite /heap_lookup_loc Heq /= => -[[? [? [? [Hin [?[n [? ?]]]]]]] ?]; simplify_eq/=.
    iMod ("IH" with "[] Hh Hl") as "{IH}[Hh IH]".
    { iPureIntro => /=. by destruct l; simplify_eq/=. }
    iDestruct (heap_pointsto_mbyte_lookup_q with "Hh Hb") as %[? [? Hin']].
    iMod (heap_read_mbyte_vs _ 0 1 with "Hh Hb") as "[Hh Hb]"; first exact Hin'.
    iModIntro. iSplitL "Hh".
    { iStopProof. f_equiv. symmetry. apply partial_alter_to_insert.
      rewrite /= Hin' //. }
    iIntros (h2) "Hh". iDestruct (heap_pointsto_mbyte_lookup_q with "Hh Hb") as %[ep' [n' Hn]].
    iMod ("IH" with "Hh") as (Hat) "[Hh Hl]". iSplitR.
    { rewrite /shift_loc /= Z.add_1_r Heq in Hat. iPureIntro. naive_solver. }
    iMod (heap_read_mbyte_vs _ 1 0 with "Hh Hb") as "[Hh Hb]".
    { rewrite heap_update_lookup_not_in_range // /shift_loc /=. lia. }
    rewrite heap_pointsto_cons_mbyte heap_pointsto_mbyte_eq. iFrame "Hl Hlb". iModIntro.
    iSplitR "Hb"; [ iStopProof | iExists _; by iFrame ].
    f_equiv. symmetry. apply partial_alter_to_insert.
    rewrite heap_update_lookup_not_in_range /shift_loc /= ?Hn ?Heq //. lia.
  Qed.

  Lemma heap_write_mbyte_vs h st1 st2 l aid b b' ep ep':
    h !! l.(loc_a) = Some (HeapCell aid st1 b ep) →
    heap_ctx h -∗ heap_pointsto_mbyte_st st1 l aid 1%Qp b
    ==∗ heap_ctx (<[l.(loc_a):=HeapCell aid st2 b' ep']> h) ∗ heap_pointsto_mbyte_st st2 l aid 1%Qp b'.
  Proof.
    intros Hσv. do 2 apply wand_intro_r. rewrite left_id -!own_op to_heapUR_insert.
    eapply own_update, auth_update, singleton_local_update.
    { by rewrite /to_heapUR lookup_fmap Hσv. }
    apply exclusive_local_update. by destruct st2.
  Qed.

  Lemma heap_write f h l v v':
    length v = length v' → (∀ me, f (Some (RSt 0 me)) = RSt 0 me) →
    heap_ctx h -∗ l ↦ v ==∗ heap_ctx (heap_upd l v' f h) ∗ l ↦ v'.
  Proof.
    iIntros (Hlen Hf) "Hh Hmt".
    iInduction (v) as [|v b] "IH" forall (l v' Hlen); destruct v' => //; first by iFrame.
    move: Hlen => [] Hlen. rewrite !heap_pointsto_cons_mbyte !heap_pointsto_mbyte_eq.
    iDestruct "Hmt" as "[Hb [$ Hl]]". iDestruct "Hb" as (?? Heq) "Hb".
    iDestruct (heap_pointsto_mbyte_lookup_1 with "Hh Hb") as %[ep_w Hin]; auto.
    iMod ("IH" with "[//] Hh Hl") as "[Hh $]".
    iMod (heap_write_mbyte_vs with "Hh Hb") as "[Hh Hb]".
    { rewrite heap_update_lookup_not_in_range /shift_loc //=. lia. }
    iModIntro => /=. iSplitR "Hb"; last (iExists _; by iFrame).
    iClear "IH". iStopProof. f_equiv => /=. symmetry.
    apply: partial_alter_to_insert.
    rewrite heap_update_lookup_not_in_range /shift_loc /= ?Heq ?Hin ?Hf //. lia.
  Qed.

  Lemma heap_write_na h l v v' :
    length v = length v' →
    heap_ctx h -∗ l ↦ v ==∗
      ⌜heap_lookup_loc l v (λ st, ∃ me, st = RSt 0 me) h⌝ ∗
      heap_ctx (heap_upd l v (λ _, WSt) h) ∗
      ∀ h2, heap_ctx h2 ==∗ ⌜heap_lookup_loc l v (λ st, st = WSt) h2⌝ ∗
        heap_ctx (heap_upd l v' (λ _, RSt 0 0) h2) ∗ l ↦ v'.
  Proof.
    iIntros (Hlen) "Hh Hv".
    iDestruct (heap_pointsto_lookup_1 with "Hh Hv") as %Hat. 2: iSplitR => //. 1: by naive_solver.
    iInduction (v) as [|b v] "IH" forall (l v' Hat Hlen) => //=; destruct v' => //.
    { iFrame. by iIntros "!#" (?) "$ !#". }
    move: Hlen => -[] Hlen.
    rewrite heap_pointsto_cons_mbyte heap_pointsto_mbyte_eq.
    iDestruct "Hv" as "[Hb [? Hl]]". iDestruct "Hb" as (?? Heq) "Hb".
    move: Hat. rewrite /heap_lookup_loc Heq /= => -[[? [? [? [Hin [??]]]]] ?]; simplify_eq/=.
    iMod ("IH" with "[] [] Hh Hl") as "{IH}[Hh IH]"; [|done|].
    { iPureIntro => /=. by destruct l; simplify_eq/=. }
    iDestruct (heap_pointsto_mbyte_lookup_1 with "Hh Hb") as %[? Hin'].
    iMod (heap_write_mbyte_vs with "Hh Hb") as "[Hh Hb]"; first exact Hin'.
    iSplitL "Hh". { rewrite /heap_upd /=. erewrite partial_alter_to_insert; first done.
                    rewrite Hin' //. }
    iIntros "!#" (h2) "Hh". iDestruct (heap_pointsto_mbyte_lookup_1 with "Hh Hb") as %[ep_n Hn].
    iMod ("IH" with "Hh") as (Hat) "[Hh Hl]". iSplitR.
    { rewrite /shift_loc /= Z.add_1_r Heq in Hat. iPureIntro. naive_solver. }
    iMod (heap_write_mbyte_vs with "Hh Hb") as "[Hh Hb]".
    { rewrite heap_update_lookup_not_in_range /shift_loc /= ?Heq ?Hin //=. lia. }
    rewrite /heap_upd !Heq /=. erewrite partial_alter_to_insert; last done.
    destruct l as [prov addr]. simpl in *.
    rewrite Z.add_1_r Heq. iFrame.
    rewrite heap_update_lookup_not_in_range; last lia. rewrite Hn /=. iFrame.
    rewrite heap_pointsto_cons_mbyte heap_pointsto_mbyte_eq. by iFrame.
  Qed.

  Lemma heap_free_free l v h :
    heap_ctx h -∗ l ↦ v ==∗ heap_ctx (heap_free l.(loc_a) (length v) h).
  Proof.
    iIntros "Hctx Hl".
    iDestruct (heap_pointsto_is_alloc with "Hl") as %[[aid Haid]|(? & ->)]; last done.
    rewrite heap_pointsto_eq /heap_pointsto_def. iDestruct "Hl" as "[_ Hl]".
    destruct l as [p a]. simplify_eq/=.
    iInduction v as [|b vl] "IH" forall (h a); simpl; first by iFrame.
    iDestruct "Hl" as "[Hb Hl]".
    rewrite heap_pointsto_mbyte_eq /heap_pointsto_mbyte_def.
    iDestruct "Hb" as (?? Heq) "Hb". simplify_eq/=.
    iEval (rewrite /shift_loc /= Z.add_0_r) in "Hb".
    iMod (own_update_2 with "Hctx Hb") as "Hctx".
    { apply auth_update_dealloc.
      change (ε : heapUR) with (∅ : heapUR).
      rewrite -(delete_singleton_eq a ((1%Qp, to_lock_stateR (RSt 0 me), to_agree (id, b)) : heap_cellR)).
      apply (delete_local_update _ _ a ((1%Qp, to_lock_stateR (RSt 0 me), to_agree (id, b)) : heap_cellR)).
      rewrite /= lookup_singleton decide_True //. }
    rewrite -to_heapUR_delete heap_free_delete.
    setoid_rewrite shift_loc_S.
    by iApply ("IH" with "Hctx Hl").
  Qed.

  Lemma heap_pointsto_reshape_sl (sl : struct_layout) v l q :
    v `has_layout_val` sl →
    l ↦{q} v ⊣⊢ loc_in_bounds l 0 (ly_size sl) ∗ ([∗ list] i ↦ v ∈ reshape (ly_size <$> (sl_members sl).*2) v, (l +ₗ offset_of_idx (sl_members sl) i) ↦{q} v).
  Proof.
    rewrite /has_layout_val {1 2}/ly_size /=.

    elim: (sl_members sl) l v; simpl.
    { intros l v Hlen. destruct v; last done.
      rewrite right_id. apply heap_pointsto_nil. }
    intros [m ly] s IH l v Hlen; simpl in Hlen.

    specialize (take_drop (ly_size ly) v) as Heq.
    rewrite -Heq.
    assert (length (take (ly_size ly) v) = ly_size ly) as Hlen2.
    { rewrite length_take. lia. }

    iSplit.
    - iIntros "Hpts". iPoseProof (heap_pointsto_loc_in_bounds with "Hpts") as "#Ha".
      simpl. iSplitR.
      { rewrite -Hlen Heq//. }
      rewrite heap_pointsto_app.
      iDestruct "Hpts" as "(Hpts1 & Hpts)".
      rewrite /offset_of_idx. simpl. setoid_rewrite <-shift_loc_assoc_nat.
      iSplitL "Hpts1".
      { simpl. rewrite shift_loc_0_nat -{4}Hlen2 take_app_length. done. }
      iPoseProof (IH with "Hpts") as "(_ & Hc)".
      { rewrite length_drop Hlen. unfold fmap. lia. }
      rewrite -{6}Hlen2.
      rewrite drop_app_length.
      rewrite length_take.
      rewrite Nat.min_l; first done.
      lia.
    - iIntros "(#Ha & Hb & Hc)".
      rewrite /offset_of_idx. simpl.
      rewrite heap_pointsto_app.
      rewrite shift_loc_0_nat. rewrite -{2}Hlen2 take_app_length. iFrame.
      iApply IH.
      { rewrite length_drop Hlen. rewrite /fmap. lia. }
      iSplitR.
      { iApply loc_in_bounds_offset_suf; last done.
        - done.
        - simpl. lia.
        - simpl. rewrite length_take /fmap. lia. }
          iEval (rewrite -{2}Hlen2) in "Hc". rewrite drop_app_length.
          iApply (big_sepL_wand with "Hc").
          iApply big_sepL_intro. iModIntro.
          iIntros (k v' Hlook) "Hp".
          rewrite shift_loc_assoc_nat.
          rewrite length_take. rewrite Nat.min_l; first done.
          lia.
  Qed.

  (* for simplicity: restricting to uniform sizes *)
  Lemma heap_pointsto_mjoin_uniform l (vs : list val) (sz : nat) q :
    (∀ v, v ∈ vs → length v = sz) →
    l ↦{q} mjoin vs ⊣⊢ loc_in_bounds l 0 (length vs * sz) ∗ ([∗ list] i ↦ v ∈ vs, (l +ₗ (sz * i)) ↦{q} v).
  Proof.
    intros Hsz.
    assert (length (mjoin vs) = length vs * sz)%nat as Hlen.
    { induction vs as [ | v vs IH]; simpl; first lia.
      rewrite length_app. rewrite Hsz; [ | apply elem_of_cons; by left].
      f_equiv. apply IH. intros. apply Hsz. apply elem_of_cons; by right. }
    induction vs as [ | v vs IH] in l, Hlen, Hsz |-*; simpl.
    { rewrite right_id. by rewrite heap_pointsto_nil. }
    iSplit.
    - iIntros "Hl". iPoseProof (heap_pointsto_loc_in_bounds with "Hl") as "#Hlb".
      rewrite heap_pointsto_app. iDestruct "Hl" as "[Hl1 Hl]".
      rewrite Z.mul_0_r shift_loc_0_nat. iFrame "Hl1".
      iSplitR. { rewrite Hlen. done. }
      iPoseProof (IH with "Hl") as "Ha".
      { intros. apply Hsz. apply elem_of_cons; by right. }
      { simpl in Hlen. rewrite length_app in Hlen. rewrite Hsz in Hlen; [ | apply elem_of_cons; by left]. lia. }
      iDestruct "Ha" as "(_ & Ha)".
      iApply (big_sepL_wand with "Ha").
      iApply big_sepL_intro. iIntros "!>" (k v' _).
      rewrite shift_loc_assoc.
      rewrite (Hsz v); [ | apply elem_of_cons; by left].
      assert ((sz + sz * k)%Z = (sz * S k)%Z) as -> by lia.
      eauto.
    - iIntros "(Hlb & Hv)".
      rewrite Z.mul_0_r shift_loc_0_nat heap_pointsto_app.
      iDestruct "Hv" as "($ & Hv)".
      iApply IH.
      { intros. apply Hsz. apply elem_of_cons; by right. }
      { simpl in Hlen. rewrite length_app in Hlen. rewrite Hsz in Hlen; [ | apply elem_of_cons; by left]. lia. }
      iSplitL "Hlb".
      + iApply (loc_in_bounds_offset with "Hlb"); first done.
        { simpl. lia. }
        { simpl. rewrite Hsz; [ | apply elem_of_cons; by left]. lia. }
      + iApply (big_sepL_wand with "Hv").
        iApply big_sepL_intro.
        iIntros "!>" (???) "Hv".
        rewrite shift_loc_assoc.
        rewrite (Hsz v); [ | apply elem_of_cons; by left].
        assert ((sz + sz * k)%Z = (sz * S k)%Z) as -> by lia.
        eauto.
  Qed.
End heap.

Section alloc_alive.
  Context `{!heapG Σ} `{!BiFUpd (iPropI Σ)}.

  Lemma alloc_alive_loc_mono (l1 l2 : loc) :
    l1.(loc_p) = l2.(loc_p) →
    alloc_alive_loc l1 -∗ alloc_alive_loc l2.
  Proof. rewrite alloc_alive_loc_eq /alloc_alive_loc_def => ->. by iIntros "$". Qed.

  Lemma heap_pointsto_alive_strong l :
    (|={⊤, ∅}=> (∃ q v, ⌜length v ≠ 0%nat⌝ ∗ l ↦{q} v)) -∗ alloc_alive_loc l.
  Proof.
    rewrite alloc_alive_loc_eq. move: l => [? a]. iIntros ">(%q&%v&%&?)". iModIntro.
    iRight. iExists a, q, _. iFrame. by destruct v.
  Qed.

  Lemma heap_pointsto_alive l q v:
    length v ≠ 0%nat →
    l ↦{q} v -∗ alloc_alive_loc l.
  Proof.
    iIntros (?) "Hl". iApply heap_pointsto_alive_strong.
    iApply fupd_mask_intro; [set_solver|]. iIntros "?".
    iExists _, _. by iFrame.
  Qed.

  Lemma alloc_global_alive l:
    alloc_global l -∗ alloc_alive_loc l.
  Proof.
    rewrite alloc_global_eq alloc_alive_loc_eq. iIntros "(%id&%&Ha)".
    iApply fupd_mask_intro; [set_solver|].
    iIntros "_". iLeft. eauto.
  Qed.

  Lemma alloc_alive_loc_to_block_alive l heap :
    alloc_alive_loc l -∗ heap_state_ctx heap ={⊤, ∅}=∗ ⌜block_alive l heap⌝.
  Proof.
    rewrite alloc_alive_loc_eq. iIntros ">[H|H]".
    - iDestruct "H" as (???) "Hl". iIntros "(Hinv&_&_&Hctx) !>".
      iLeft. iExists _. iSplit => //.
      iDestruct (alloc_alive_lookup with "Hctx Hl") as %[?[??]]. iPureIntro.
      eexists _. naive_solver.
    - iIntros "((?&Halive&?&?)&Hctx&?&?) !>".
      iDestruct "H" as (????) "H".
      iDestruct (heap_pointsto_lookup_q (λ _, True) with "Hctx H") as %Hlookup => //.
      destruct v => //. destruct Hlookup as [[id [?[?[?[??]]]]]?].
      iLeft. iExists id. iSplit; first done. iDestruct "Halive" as %Halive.
      iPureIntro. apply: (Halive _ (HeapCell _ _ _ _)). done.
  Qed.

  Lemma alloc_alive_loc_to_valid_ptr l heap :
    loc_in_bounds l 0 0 -∗ alloc_alive_loc l -∗ heap_state_ctx heap ={⊤, ∅}=∗ ⌜valid_ptr l heap⌝.
  Proof.
    iIntros "Hin Ha Hσ".
    iDestruct (loc_in_bounds_to_heap_loc_in_bounds with "Hin Hσ") as %Hlb.
    rewrite shift_loc_0_nat in Hlb.
    by iMod (alloc_alive_loc_to_block_alive with "Ha Hσ") as %?.
  Qed.
End alloc_alive.

Section alloc_new_blocks.
  Context `{!heapG Σ}.

  Lemma heap_alloc_new_block_upd σ1 l v kind σ2:
    alloc_new_block σ1 kind l v σ2 →
    heap_state_ctx σ1 ==∗ heap_state_ctx σ2 ∗ l ↦ v ∗ freeable l (length v) 1 kind.
  Proof.
    move => []; clear. move => σ l aid kind v alloc Haid ???; subst alloc.
    iIntros "Hctx". iDestruct "Hctx" as (Hinv) "(Hhctx&Hrctx&Hsctx)".
    iMod (alloc_meta_alloc  with "Hrctx") as "[$ #Hb]" => //.
    iMod (alloc_alive_alloc with "Hsctx") as "[$ Hs]" => //.
    iDestruct (alloc_meta_to_loc_in_bounds l aid 0 (length v) with "[Hb]")
      as "#Hinb" => //.
    { rewrite Z.add_0_r. done. }
    iMod (heap_alloc with "Hb Hs Hhctx") as "[Hhctx [Hv Hal]]" => //.
    iModIntro. iFrame. iPureIntro. by eapply alloc_new_block_invariant.
  Qed.

  Lemma heap_alloc_new_blocks_upd σ1 ls vs kind σ2:
    alloc_new_blocks σ1 kind ls vs σ2 →
    heap_state_ctx σ1 ==∗
      heap_state_ctx σ2 ∗
      [∗ list] l; v ∈ ls; vs, l ↦ v ∗ freeable l (length v) 1 kind.
  Proof.
    move => alloc.
    iInduction alloc as [σ|] "IH"; first by iIntros "$ !>". iIntros "Hσ".
    iMod (heap_alloc_new_block_upd with "Hσ") as "(Hσ&Hl)"; [done|..].
    iFrame. by iApply "IH".
  Qed.
End alloc_new_blocks.

Section free_blocks.
  Context `{!heapG Σ}.

  Lemma heap_free_block_upd σ1 l ly kind:
    l ↦|ly| -∗
    freeable l (ly_size ly) 1 kind -∗
    heap_state_ctx σ1 ==∗ ∃ σ2, ⌜free_block σ1 kind l ly σ2⌝ ∗ heap_state_ctx σ2.
  Proof.
    iIntros "Hl Hfree (Hinv&Hhctx&Hrctx&Hsctx)". iDestruct "Hinv" as %Hinv.
    rewrite freeable_eq. iDestruct "Hfree" as (aid Haid) "[#Hrange Hkill]".
    iDestruct "Hl" as (v Hv ?) "Hl".
    iDestruct (alloc_alive_lookup with "Hsctx Hkill") as %[[????k] [??]].
    iDestruct (alloc_meta_lookup with "Hrctx Hrange") as %[al'' [?[[??]?]]]. simplify_eq/=.
    iDestruct (heap_pointsto_lookup_1 lock_state_idle with "Hhctx Hl") as %?. { intros me. left. by exists me. }
    iExists _. iSplitR. { iPureIntro. by econstructor. }
    iMod (heap_free_free with "Hhctx Hl") as "Hhctx". rewrite Hv. iFrame => /=.
    iMod (alloc_alive_kill _ _ ({| al_start := l.(loc_a); al_len := ly_size ly; al_alive := true; al_kind := k |}) with "Hsctx Hkill") as "[$ Hd]".
    erewrite alloc_meta_ctx_same_range; [iFrame |done..].
    iPureIntro. eapply free_block_invariant => //. by eapply FreeBlock.
  Qed.

  Lemma heap_free_blocks_upd ls σ1 kind:
    ([∗ list] l ∈ ls, l.1 ↦|l.2| ∗ freeable l.1 (ly_size l.2) 1 kind) -∗
    heap_state_ctx σ1 ==∗ ∃ σ2, ⌜free_blocks σ1 kind ls σ2⌝ ∗ heap_state_ctx σ2.
  Proof.
    iInduction ls as [|[l ly] ls] "IH" forall (σ1).
    { iIntros "_ ? !>". iExists σ1. iFrame. iPureIntro. by constructor. }
    iIntros "[[Hl Hf] Hls] Hσ" => /=.
    iMod (heap_free_block_upd with "Hl Hf Hσ") as (σ2 Hfree) "Hσ".
    iMod ("IH" with "Hls Hσ") as (??) "Hσ".
    iExists _. iFrame. iPureIntro. by econstructor.
  Qed.
End free_blocks.

(** ** Thread-local state *)
Notation frame_id := nat (only parsing).
Notation frame_path := (thread_id * frame_id)%type (only parsing).
Class threadG Σ := ThreadG {
  (* ghost state tracking the current stack frame for every thread *)
  thread_current_frame_inG :: ghost_mapG Σ thread_id frame_id;
  thread_current_frame_name : gname;
  (* list of allocated local variables *)
  thread_local_vars_inG :: ghost_mapG Σ frame_path (list var_name);
  thread_local_vars_name : gname;
  (* individual points-tos for locals *)
  thread_local_var_loc :: ghost_mapG Σ (frame_path * var_name) (loc * syn_type);
  thread_local_var_loc_name : gname;
}.

Section definitions.
  Context `{!threadG Σ} `{!heapG Σ} `{!FUpd (iProp Σ)} `{!LayoutAlg}.

  (* Current frame *)
  Definition current_frame_def (π : thread_id) (i : frame_id) : iProp Σ :=
    ghost_map_elem thread_current_frame_name π (DfracOwn 1) i.
  Definition current_frame_aux π i : seal (current_frame_def π i). Proof. by eexists. Qed.
  Definition current_frame π i := (current_frame_aux π i).(unseal).
  Definition current_frame_unfold π i : current_frame π i = current_frame_def π i := (current_frame_aux π i).(seal_eq).

  (* Frame locals *)
  Definition allocated_locals_def (f : frame_path) (l : list var_name) : iProp Σ :=
    ghost_map_elem thread_local_vars_name f (DfracOwn 1) l.
  Definition allocated_locals_aux f l : seal (allocated_locals_def f l). Proof. by eexists. Qed.
  Definition allocated_locals f l := (allocated_locals_aux f l).(unseal).
  Definition allocated_locals_unfold f l : allocated_locals f l = allocated_locals_def f l := (allocated_locals_aux f l).(seal_eq).

  (* Local points-to *)
  Definition local_is_allocated_at_def (f : frame_path) (x : var_name) (st : syn_type) (l : loc) : iProp Σ :=
    ghost_map_elem thread_local_var_loc_name (f, x) (DfracOwn 1) (l, st).
  Definition local_is_allocated_at_aux f x st l : seal (local_is_allocated_at_def f x st l). Proof. by eexists. Qed.
  Definition local_is_allocated_at f x st l := (local_is_allocated_at_aux f x st l).(unseal).
  Definition local_is_allocated_at_unfold f x st l : local_is_allocated_at f x st l = local_is_allocated_at_def f x st l := (local_is_allocated_at_aux f x st l).(seal_eq).


  (* TODO probably need to add -1 or so for some of the frame id stuff *)
  Definition to_current_frame (t : gmap thread_id thread_state) : gmap thread_id frame_id :=
    (λ ts, length ts.(ts_frames)) <$> t.
  Definition thread_current_frame_auth (st : gmap thread_id thread_state) : iProp Σ :=
    ghost_map_auth thread_current_frame_name 1 (to_current_frame st).

  Definition call_frame_has_locals (cf : call_frame) (names : list var_name) :=
    (map_to_list (cf.(cf_locals))).*1 ≡ₚ names.
  Definition thread_local_vars_inv_1 (st : gmap thread_id thread_state) (m : gmap (thread_id * frame_id) (list var_name)) :=
    ∀ π i ts cf,
      (0 < i ≤ length ts.(ts_frames))%nat →
      st !! π = Some ts →
      ts.(ts_frames) !! (length ts.(ts_frames) - i)%nat = Some cf →
      ∃ names, m !! (π, i) = Some names ∧ call_frame_has_locals cf names.
  Definition thread_local_vars_inv_2 (st : gmap thread_id thread_state) (m : gmap (thread_id * frame_id) (list var_name)) :=
    ∀ π i names,
      m !! (π, i) = Some names →
      ∃ ts cf, st !! π = Some ts ∧ (0 < i ≤ length ts.(ts_frames))%nat ∧ ts.(ts_frames) !! (length ts.(ts_frames) - i)%nat = Some cf ∧ call_frame_has_locals cf names.
  Definition thread_local_vars_auth (st : gmap thread_id thread_state) : iProp Σ :=
    ∃ m, ghost_map_auth thread_local_vars_name 1 m ∗ ⌜thread_local_vars_inv_1 st m⌝ ∗ ⌜thread_local_vars_inv_2 st m⌝.

  Definition thread_local_var_loc_inv_1 (st : gmap thread_id thread_state) (m : gmap (thread_id * frame_id * var_name) (loc * syn_type)) : Prop :=
    ∀ π i x ts cf l ly,
      (0 < i ≤ length ts.(ts_frames))%nat →
      st !! π = Some ts →
      ts.(ts_frames) !! (length ts.(ts_frames) - i)%nat = Some cf →
      cf.(cf_locals) !! x = Some (l, ly) →
      ∃ synty, m !! (π, i, x) = Some (l, synty) ∧ syn_type_has_layout synty ly.
  Definition thread_local_var_loc_inv_2 (st : gmap thread_id thread_state) (m : gmap (thread_id * frame_id * var_name) (loc * syn_type)) : Prop :=
    ∀ π i x l synty,
      m !! (π, i, x) = Some (l, synty) →
      ∃ ts cf ly,
        st !! π = Some ts ∧
        (0 < i ≤ length ts.(ts_frames))%nat ∧
        ts.(ts_frames) !! (length ts.(ts_frames) - i)%nat = Some cf ∧
        cf.(cf_locals) !! x = Some (l, ly) ∧
        syn_type_has_layout synty ly.
  Definition thread_local_var_loc_freeable (m : gmap (thread_id * frame_id * var_name) (loc * syn_type)) : iProp Σ :=
    [∗ map] x ↦ y ∈ m,
      ∃ ly, ⌜syn_type_has_layout y.2 ly⌝ ∗ freeable y.1 (ly_size ly) 1 StackAlloc.
  Definition thread_local_var_loc_auth (st : gmap thread_id thread_state) : iProp Σ :=
    ∃ m, ghost_map_auth thread_local_var_loc_name 1 m ∗ thread_local_var_loc_freeable m ∗
      ⌜thread_local_var_loc_inv_1 st m⌝ ∗ ⌜thread_local_var_loc_inv_2 st m⌝.

  Definition thread_ctx (st : gmap thread_id thread_state) : iProp Σ :=
    thread_current_frame_auth st ∗
    thread_local_vars_auth st ∗
    thread_local_var_loc_auth st.
End definitions.

Notation "x 'is_live{' f ',' st '}' l" := (local_is_allocated_at f x st l) (at level 50).

Section rules.
  Context `{!threadG Σ} `{!heapG Σ} `{!FUpd (iProp Σ)} `{!LayoutAlg}.

  Lemma call_frame_has_locals_nodup cf vars :
    call_frame_has_locals cf vars →
    NoDup vars.
  Proof.
    unfold call_frame_has_locals.
    intros <-. apply NoDup_fst_map_to_list.
  Qed.
  Lemma call_frame_has_locals_alloc_var M cf x l ly :
    x ∉ M →
    call_frame_has_locals cf M →
    call_frame_has_locals (frame_alloc_var cf x l ly) (x :: M).
  Proof.
    intros Hunalloc Hlocals.
    rewrite /call_frame_has_locals/= -Hlocals.
    rewrite map_to_list_insert; first done.
    destruct (cf_locals cf !! x) eqn:Hlook; last done.
    contradict Hunalloc. rewrite -Hlocals.
    apply list_elem_of_fmap.
    eexists (_, _). split; first done.
    by apply elem_of_map_to_list.
  Qed.
  Lemma call_frame_has_locals_dealloc_var M cf x l ly :
    x ∈ M →
    cf_locals cf !! x = Some (l, ly) →
    call_frame_has_locals cf M →
    call_frame_has_locals (frame_dealloc_var cf x) (list_difference M [x]).
  Proof.
    intros Hel Hlook Hlocals.
    rewrite /call_frame_has_locals/=.
    eapply (Permutation_cons_inv (a:=x)).
    rewrite list_difference_cons_elem; cycle 1.
    { done. }
    { by eapply call_frame_has_locals_nodup. }
    rewrite -Hlocals.
    erewrite <-(map_to_list_delete (cf_locals cf)); last done.
    done.
  Qed.
  Lemma call_frame_has_locals_fresh cf M x :
    x ∉ M →
    call_frame_has_locals cf M →
    cf.(cf_locals) !! x = None.
  Proof.
    intros Hfresh Hlocals.
    destruct (cf_locals cf !! x) eqn:Heq; last done.
    exfalso. apply Hfresh. rewrite -Hlocals.
    apply list_elem_of_fmap.
    eexists (_, _). split; first done.
    apply elem_of_map_to_list. done.
  Qed.

  Lemma live_local_is_allocated st f locals x synty l :
    thread_ctx st -∗
    allocated_locals f locals -∗
    x is_live{f, synty} l -∗
    ⌜x ∈ locals⌝.
  Proof.
    iIntros "(_ & (%m1 & Hauth1 & %Hinv1 & %Hinv2) & (%m2 & Hauth2 & Hfree & %Hinv3 & %Hinv4)) Halloc Hlive".
    rewrite allocated_locals_unfold local_is_allocated_at_unfold.
    iPoseProof (ghost_map_lookup with "Hauth1 Halloc") as "%Hlook1".
    iPoseProof (ghost_map_lookup with "Hauth2 Hlive") as "%Hlook2".
    iPureIntro.
    destruct f as (π, i).
    apply Hinv2 in Hlook1 as (ts & cf & ? & ? & ? & Hl).
    apply Hinv4 in Hlook2 as (? & ? & ? & ? & ? & ? & Hloca & ?).
    simplify_eq.
    rewrite -Hl.
    eapply list_elem_of_fmap.
    eexists. split; last apply elem_of_map_to_list; last done.
    done.
  Qed.

  Lemma state_lookup_frame st π i locals :
    thread_ctx st -∗
    allocated_locals (π, i) locals -∗
    ⌜∃ ts cf, st !! π = Some ts ∧ (0 < i ≤ length ts.(ts_frames))%nat ∧ ts.(ts_frames) !! (length ts.(ts_frames) - i)%nat = Some cf ∧ call_frame_has_locals cf locals⌝.
  Proof.
    iIntros "(_ & (%m1 & Hauth1 & %Hinv1 & %Hinv2) & _) Halloc".
    rewrite allocated_locals_unfold.
    iPoseProof (ghost_map_lookup with "Hauth1 Halloc") as "%Hlook1".
    iPureIntro. apply Hinv2 in Hlook1. done.
  Qed.
  Lemma state_lookup_current_frame st π i locals :
    thread_ctx st -∗
    current_frame π i -∗
    allocated_locals (π, i) locals -∗
    ⌜∃ ts cf, st !! π = Some ts ∧ thread_get_frame ts = Some cf ∧ call_frame_has_locals cf locals ∧ i = length ts.(ts_frames)⌝.
  Proof.
    iIntros "(Ha & (%m1 & Hauth1 & %Hinv1 & %Hinv2) & _) Hframe Halloc".
    rewrite current_frame_unfold allocated_locals_unfold.
    iPoseProof (ghost_map_lookup with "Ha Hframe") as "%Hlook1".
    iPoseProof (ghost_map_lookup with "Hauth1 Halloc") as "%Hlook2".
    iPureIntro. apply Hinv2 in Hlook2.
    unfold to_current_frame in Hlook1.
    apply lookup_fmap_Some in Hlook1 as (ts & <- & ?).
    destruct Hlook2 as (? & ? & ? & ? & Hlook & ?).
    simplify_eq. rewrite Nat.sub_diag in Hlook.
    unfold thread_get_frame.
    setoid_rewrite head_lookup.
    do 2 eexists. split_and!; try done.
  Qed.

  Lemma state_current_frame st π i :
    thread_ctx st -∗
    current_frame π i -∗
    ⌜∃ ts, st !! π = Some ts ∧ length ts.(ts_frames) = i⌝.
  Proof.
    iIntros "(Ha & _) Hframe".
    rewrite current_frame_unfold.
    iPoseProof (ghost_map_lookup with "Ha Hframe") as "%Hlook".
    iPureIntro. revert Hlook.
    rewrite /to_current_frame lookup_fmap_Some.
    intros (? & ? & ?). eauto.
  Qed.

  Lemma state_lookup_var st x π i l synty :
    thread_ctx st -∗
    current_frame π i -∗
    x is_live{(π, i), synty} l -∗
    ⌜∃ ts cf ly, syn_type_has_layout synty ly ∧ st !! π = Some ts ∧ thread_get_frame ts = Some cf ∧ cf.(cf_locals) !! x = Some (l, ly)⌝.
  Proof.
    iIntros "(Ha & _ & (%m1 & Hauth1 & Hfree & %Hinv1 & %Hinv2)) Hframe Hvar".
    rewrite current_frame_unfold local_is_allocated_at_unfold.
    iPoseProof (ghost_map_lookup with "Ha Hframe") as "%Hlook1".
    iPoseProof (ghost_map_lookup with "Hauth1 Hvar") as "%Hlook2".
    iPureIntro.
    unfold to_current_frame in Hlook1.
    apply lookup_fmap_Some in Hlook1 as (ts & <- & ?).
    apply Hinv2 in Hlook2 as (? & ? & ly & ? & ? & Hframe & Hlocal & ?).
    simplify_eq.
    rewrite Nat.sub_diag in Hframe.
    eexists _, _, _.
    rewrite /thread_get_frame head_lookup.
    done.
  Qed.
  Lemma state_lookup_vars (vars : list var_name) syntys (locs : list loc) (lys : list layout) st π i :
    Forall2 syn_type_has_layout syntys lys →
    length syntys = length locs →
    (*NoDup vars →*)
    thread_ctx st -∗
    current_frame π i -∗
    ([∗ list] x; lsynty ∈ vars; zip locs syntys, x is_live{(π, i), lsynty.2} lsynty.1) -∗
    allocated_locals (π, i) vars -∗
    ⌜∃ ts cf, st !! π = Some ts ∧ thread_get_frame ts = Some cf ∧
      (map_to_list cf.(cf_locals)).*2 ≡ₚ zip locs lys⌝.
  Proof.
    iIntros (Hst Hlen) "Htctx Hframe Hlive Hlocals".
    iPoseProof (state_lookup_current_frame with "Htctx Hframe Hlocals") as "(%ts & %cf & %Hs & %Hcf & %Hframe & %Hi)".
    iExists ts, cf. iR. iR.
    iPoseProof (big_sepL2_length with "Hlive") as "%Hlen2".
    rewrite length_zip -Hlen Nat.min_id in Hlen2.
    iPoseProof (big_sepL2_Forall2_strong _ (current_frame π i ∗ thread_ctx st)%I
      (λ x lsynty, cf.(cf_locals) !! x = Some (lsynty.1, use_layout_alg' lsynty.2)) with "[] [$Hframe $Htctx] Hlive") as "%Ha".
    { iModIntro. iIntros (??? Hlook1 Hlook2) "Hlive [Hframe Htctx]".
      iPoseProof (state_lookup_var with "Htctx Hframe Hlive") as "(% & % & % & %Hsynty & %Hlook3 & %Hlook4 & %Hlook5)".
      simplify_eq. rewrite Hlook5. rewrite /use_layout_alg' Hsynty//. }
    iPureIntro.
    enough ((map_to_list (cf_locals cf)) ≡ₚ zip vars (zip locs lys)) as ->.
    { rewrite snd_zip; first done. rewrite length_zip. lia. }
    apply NoDup_Permutation.
    { apply NoDup_map_to_list. }
    { apply NoDup_zip_l. by eapply call_frame_has_locals_nodup. }
    intros [x [l ly]].
    unfold call_frame_has_locals in Hframe.
    split.
    - intros Hlook.
      assert (x ∈ vars) as Hel. { rewrite -Hframe. apply list_elem_of_fmap. eexists; split; last done; done. }
      apply list_elem_of_lookup in Hel as (j & Hlook').
      opose proof (Forall2_lookup_l _ _ _ _ _ Ha Hlook') as ([l' synty] & Hlook2 & Hlook3).
      simpl in Hlook3.
      apply elem_of_map_to_list in Hlook. simplify_eq.
      apply (list_elem_of_lookup_2 _ j).
      apply lookup_zip_Some. split; first done.
      apply lookup_zip_Some in Hlook2 as (? & Hsynty).
      apply lookup_zip_Some. split; first done.
      opose proof (Forall2_lookup_l _ _ _ _ _ Hst Hsynty) as (ly' & ? & Hly).
      rewrite /use_layout_alg' Hly//.
    - intros (j & Hlook)%list_elem_of_lookup.
      apply lookup_zip_Some in Hlook as (Hvar & Hr).
      apply lookup_zip_Some in Hr as (Hloc & Hly).
      opose proof (Forall2_lookup_l _ _ _ _ _ Ha Hvar) as ([l' synty] & Hlook & Hlook2).
      apply lookup_zip_Some in Hlook as (? & Hly').
      simplify_eq.
      apply elem_of_map_to_list.
      rewrite Hlook2. f_equiv. f_equiv; first done.
      opose proof (Forall2_lookup_l _ _ _ _ _ Hst Hly') as (ly' & ? & Hly2).
      simplify_eq.
      rewrite /use_layout_alg' Hly2//.
  Qed.

  Lemma ghost_map_auth_prove_eq {K V} `{!EqDecision K} `{!Countable K} `{!ghost_mapG Σ K V} γ q (m1 m2 : gmap K V) :
    m1 = m2 →
    ghost_map_auth γ q m1 -∗
    ghost_map_auth γ q m2.
  Proof. intros ->. eauto. Qed.

  Lemma thread_push_frame_empty π i st st' ts ts' :
    st !! π = Some ts →
    st' = <[π := ts']> st →
    ts' = thread_push_frame ts empty_frame →
    thread_ctx st -∗
    current_frame π i ==∗
    allocated_locals (π, S i) [] ∗
    current_frame π (S i) ∗
    thread_ctx st'.
  Proof.
    iIntros (Hst -> ->) "Htctx Hframe".
    iPoseProof (state_current_frame with "Htctx Hframe") as "(%ts' & % & %)".
    simplify_eq.
    iDestruct "Htctx" as "(Ha & (%m1 & Hauth1 & %Hinv1 & %Hinv2) & (%m3 & Hauth2 & Hfree & %Hinv3 & %Hinv4))".
    rewrite current_frame_unfold.
    iMod (ghost_map_update (S (length (ts_frames ts))) with "Ha Hframe") as "(Ha & Hframe)".
    iMod (ghost_map_insert (π, S (length ts.(ts_frames))) [] with "Hauth1") as "(Hauth1 & Hlocals)".
    { (* show freshness *)
      destruct (m1 !! (π, S (length (ts_frames ts)))) eqn:Heq; last done.
      apply Hinv2 in Heq as (? & ? & ? & ? & ?). simplify_eq. lia. }
    rewrite current_frame_unfold allocated_locals_unfold. iFrame.
    iSplitL.
    { iModIntro. iApply (ghost_map_auth_prove_eq with "Ha").
      rewrite /to_current_frame fmap_insert //. }
    iPureIntro. split_and!.
    - intros π' i' ?? Hlt Hlook1 Hlook2.
      apply lookup_insert_Some in Hlook1 as [(<- & <-) | (Hneq & Hlook1)]; first last.
      { odestruct (Hinv1 π' i' _ _ _ _ _) as (? & ?); try done.
        eexists. rewrite lookup_insert_ne; last congruence. done. }
      rewrite /thread_push_frame/= in Hlook2.
      rewrite /= in Hlt.
      destruct (decide (i' = S (length ts.(ts_frames)))) as [Heq | Hneq].
      + subst. rewrite Nat.sub_diag/= in Hlook2.
        injection Hlook2 as <-.
        eexists. rewrite lookup_insert_eq. split; first done.
        rewrite /call_frame_has_locals/empty_frame map_to_list_empty/=//.
      + move: Hlook2. destruct i' as [ | i']; first lia.
        simpl. rewrite lookup_cons_ne_0; last lia.
        replace (Init.Nat.pred (length (ts_frames ts) - i')) with (length (ts_frames ts) - S i')%nat by lia.
        intros Hlook2.
        opose proof (Hinv1 _ _ _ _ _ _ Hlook2) as (names & ? & ?); [lia | done | ].
        exists names. split; last done. rewrite lookup_insert_ne; first done. congruence.
    - intros π' i' names Hlook.
      apply lookup_insert_Some in Hlook as [([= <- <-]& <-) | (Hneq & Hlook)].
      { eexists _, _. rewrite lookup_insert_eq. split_and!; simpl; [done | lia | simpl; lia | | ].
        + simpl. rewrite Nat.sub_diag. done.
        + rewrite /call_frame_has_locals/empty_frame map_to_list_empty/=//. }
      destruct (decide (π = π')) as [<- | Hneq1]; first last.
      { odestruct (Hinv2 π' i' _ _) as (? & ? & ? & ? & ? & ?); first done.
        eexists _, _. rewrite lookup_insert_ne; last congruence. done. }
      eapply Hinv2 in Hlook as (? & ? & ? & ? & Hlook2 & ?).
      simplify_eq. eexists _, _.
      split_and!. { rewrite lookup_insert_eq. done. }
      all: simpl.
      + lia.
      + lia.
      + rewrite lookup_cons_ne_0; last lia.
        replace (Init.Nat.pred (S (length (ts_frames ts)) - i')) with (length (ts_frames ts) - i')%nat by lia.
        done.
      + done.
    - intros π' i' ?????? Hlook1 Hlook2 Hlook3.
      apply lookup_insert_Some in Hlook1 as [(<- & <-) | (Hneq & Hlook1)].
      + simpl in *. destruct (decide (i' = S (length (ts_frames ts)))) as [-> | ?].
        { simpl in Hlook2. rewrite Nat.sub_diag/= in Hlook2.
          injection Hlook2 as <-. simpl in Hlook3. done. }
        eapply Hinv3; [ | done | | done]; first lia.
        move: Hlook2. rewrite lookup_cons_ne_0; last lia.
        replace (Init.Nat.pred (S (length (ts_frames ts)) - i')) with (length (ts_frames ts) - i')%nat by lia.
        done.
      + eapply Hinv3; done.
    - intros π' i' ??? Hlook.
      apply Hinv4 in Hlook as (ts' & cf & ly & Hlook1 & ? & Hlook2 & Hlook3 & ?).
      destruct (decide (π' = π)) as [-> | Hneq]; first last.
      { exists ts', cf, ly. split_and!; try done; try lia.
        rewrite lookup_insert_ne; done. }
      simplify_eq. exists (thread_push_frame ts empty_frame), cf, ly.
      simpl. split_and!; try done; try lia.
      + rewrite lookup_insert_eq. done.
      + rewrite lookup_cons_ne_0; last lia.
        replace (Init.Nat.pred (S (length (ts_frames ts)) - i')) with (length (ts_frames ts) - i')%nat by lia.
        done.
  Qed.

  Lemma thread_pop_frame_empty π i st st' ts S :
    st !! π = Some ts →
    st' = <[π := pop_frame ts]> st →
    S = [] →
    thread_ctx st -∗
    current_frame π i -∗
    allocated_locals (π, i) S ==∗
    current_frame π (Nat.pred i) ∗
    thread_ctx st'.
  Proof.
    iIntros (Hst -> ->) "Htctx Hframe Hlocals".
    iPoseProof (state_lookup_current_frame with "Htctx Hframe Hlocals") as "(%ts' & %cf & % & %Hframe & %Hlocals & ->)".
    unfold thread_get_frame in Hframe.
    destruct ts' as [ts'].
    destruct ts' as [ | cf' ts']; first done.
    simpl in Hframe. injection Hframe as ->. simplify_eq.
    iDestruct "Htctx" as "(Ha & (%m1 & Hauth1 & %Hinv1 & %Hinv2) & (%m3 & Hauth2 & Hfree & %Hinv3 & %Hinv4))".
    rewrite current_frame_unfold allocated_locals_unfold.
    iMod (ghost_map_update ((length (ts'))) with "Ha Hframe") as "(Ha & Hframe)".
    iMod (ghost_map_delete with "Hauth1 Hlocals") as "Hauth1".
    rewrite current_frame_unfold. iFrame.
    iSplitL.
    { iModIntro. iApply (ghost_map_auth_prove_eq with "Ha").
      rewrite /to_current_frame fmap_insert //. }
    iPureIntro. split_and!.
    - intros π' i' ?? Hlt Hlook1 Hlook2.
      apply lookup_insert_Some in Hlook1 as [(<- & <-) | (Hneq & Hlook1)]; first last.
      { odestruct (Hinv1 π' i' _ _ _ _ _) as (? & ?); try done.
        eexists. rewrite lookup_delete_ne; last congruence. done. }
      simpl in *.
      setoid_rewrite lookup_delete_ne; last (intros [=]; lia).
      eapply Hinv1; [ | done | ].
      + simpl. lia.
      + simpl. rewrite lookup_cons_ne_0; last lia.
        replace (Init.Nat.pred (S (length ts') - i')) with (length ts' - i')%nat by lia.
        done.
    - intros π' i' names Hlook.
      apply lookup_delete_Some in Hlook as [Hneq Hlook].
      destruct (decide (π = π')) as [<- | Hneq1]; first last.
      { odestruct (Hinv2 π' i' _ _) as (? & ? & ? & ? & ? & ?); first done.
        eexists _, _. rewrite lookup_insert_ne; last congruence. done. }
      eapply Hinv2 in Hlook as (? & ? & ? & ? & Hlook2 & ?).
      simplify_eq. eexists _, _.
      simpl in *. assert (i' ≠ S (length ts')). { intros ->. congruence. }
      split_and!. { rewrite lookup_insert_eq. done. }
      all: simpl.
      + lia.
      + lia.
      + move: Hlook2.
        rewrite lookup_cons_ne_0; last lia.
        replace (Init.Nat.pred (S (length ts') - i')) with (length ts' - i')%nat by lia.
        done.
      + done.
    - intros π' i' ?????? Hlook1 Hlook2 Hlook3.
      apply lookup_insert_Some in Hlook1 as [(<- & <-) | (Hneq & Hlook1)].
      + simpl in *. eapply Hinv3; try done; simpl; first lia.
        rewrite lookup_cons_ne_0; last lia.
        replace (Init.Nat.pred (S (length ts') - i')) with (length ts' - i')%nat by lia.
        done.
      + eapply Hinv3; done.
    - intros π' i' ??? Hlook.
      apply Hinv4 in Hlook as (ts & cf' & ly & Hlook1 & ? & Hlook2 & Hlook3 & ?).
      destruct (decide (π' = π)) as [-> | Hneq]; first last.
      { exists ts, cf', ly. split_and!; try done; try lia.
        rewrite lookup_insert_ne; done. }
      simplify_eq. eexists _, cf', ly.
      simpl in *. rewrite lookup_insert_eq. split; first done.
      simpl.
      destruct (decide (i' = S (length ts'))) as [-> | ?].
      { exfalso. rewrite Nat.sub_diag in Hlook2. simpl in *. simplify_eq.
        move: Hlook3. rewrite /call_frame_has_locals in Hlocals.
        symmetry in Hlocals.
        apply Permutation_nil in Hlocals.
        apply fmap_nil_inv in Hlocals.
        apply map_to_list_empty_iff in Hlocals. rewrite Hlocals. done. }
      split_and!; try done; try lia.
      move: Hlook2.
      rewrite lookup_cons_ne_0; last lia.
      replace (Init.Nat.pred (S (length ts') - i')) with (length ts' - i')%nat by lia.
      done.
  Qed.


  Lemma thread_frame_allocate_var st π i ts cf x l ly synty cf' st' M  :
    syn_type_has_layout synty ly →
    st !! π = Some ts →
    thread_get_frame ts = Some cf →
    x ∉ M →
    cf' = frame_alloc_var cf x l ly →
    st' = <[π := thread_update_frame ts cf']> st →
    thread_ctx st -∗
    current_frame π i -∗
    freeable l (ly_size ly) 1 StackAlloc -∗
    allocated_locals (π, i) M ==∗
    current_frame π i ∗
    allocated_locals (π, i) (x :: M) ∗
    x is_live{(π, i), synty} l ∗
    thread_ctx st'.
  Proof.
    iIntros (Hly Hthread Hframe Hunalloc -> ->) "Htctx Hframe Hfree Hlocals".
    iPoseProof (state_lookup_current_frame with "Htctx Hframe Hlocals") as "(%ts' & %cf' & %Hts & %Hcf & %Hlocals & ->)".
    unfold thread_get_frame, call_frame_has_locals in *.
    simplify_eq.
    rewrite head_lookup in Hframe.
    iDestruct "Htctx" as "(Ha & (%m1 & Hauth1 & %Hinv1 & %Hinv2) & (%m2 & Hauth2 & Hfrees & %Hinv3 & %Hinv4))".
    rewrite current_frame_unfold !allocated_locals_unfold local_is_allocated_at_unfold.
    iMod (ghost_map_update with "Hauth1 Hlocals") as "(Hauth1 & $)".
    iMod (ghost_map_insert with "Hauth2") as "(Hauth2 & $)".
    { destruct (m2 !! (π, length ts.(ts_frames), x)) as [[l1 synty1] | ] eqn:Heq; last done.
      apply Hinv4 in Heq as (? & ? & ? & ? & ? & Ha & Hb & _).
      simplify_eq. rewrite Nat.sub_diag in Ha. simplify_eq.
      erewrite call_frame_has_locals_fresh in Hb; last done; done. }
    iFrame. simpl.
    iSplitL "Ha".
    { iModIntro.
      unfold thread_current_frame_auth.
      iApply (ghost_map_auth_prove_eq with "Ha").
      unfold to_current_frame.
      rewrite fmap_insert.
      symmetry. apply insert_id.
      rewrite lookup_fmap Hthread.
      rewrite /thread_update_frame /=.
      rewrite length_tl. f_equiv.
      apply lookup_lt_Some in Hframe.
      lia. }
    specialize (lookup_lt_Some _ _ _ Hframe) as ?.
    destruct ts as [ts].
    destruct ts as [ | cf' ts]; first done.
    simpl in *. injection Hframe as [= ->].
    assert (m2 !! (π, S (length ts), x) = None) as Hm2.
    { destruct (m2 !! (π, S (length ts), x)) as [ [] | ]eqn:Heq; last done.
      eapply Hinv4 in Heq as (? & ? & ? & ? & ? & Hlook & Ha & ?).
      simplify_eq. simpl in *.
      rewrite Nat.sub_diag in Hlook. simpl in Hlook. injection Hlook as <-.
      erewrite call_frame_has_locals_fresh in Ha; done. }
    iSplitR; first (iPureIntro; split); last iSplitL; last (iPureIntro; split).
    - intros π' i' ?? Hlt Hlook1 Hlook2.
      apply lookup_insert_Some in Hlook1 as [(<- & <-) | (Hneq & Hlook1)]; first last.
      { odestruct (Hinv1 π' i' _ _ _ _ _) as (? & ?); try done.
        eexists. rewrite lookup_insert_ne; last congruence. done. }
      rewrite /thread_update_frame/= in Hlook2.
      rewrite /= in Hlt.
      destruct (decide (i' = S (length ts))) as [Heq | Hneq].
      + subst. rewrite Nat.sub_diag/= in Hlook2.
        injection Hlook2 as <-.
        eexists. rewrite lookup_insert_eq. split; first done.
        by apply call_frame_has_locals_alloc_var.
      + move: Hlook2. destruct i' as [ | i']; first lia.
        simpl. rewrite lookup_cons_ne_0; last lia.
        intros Hlook2.
        setoid_rewrite lookup_insert_ne; last congruence.
        eapply Hinv1; [ | done | ]; simpl; first lia.
        rewrite lookup_cons_ne_0; last lia.
        done.
    - intros π' i' names Hlook.
      apply lookup_insert_Some in Hlook as [([= <- <-]& <-) | (Hneq & Hlook)].
      { eexists _, _. rewrite lookup_insert_eq. split_and!; simpl; [done | lia | simpl; lia | | ].
        + simpl. rewrite Nat.sub_diag. done.
        + by apply call_frame_has_locals_alloc_var. }
      destruct (decide (π = π')) as [<- | Hneq1]; first last.
      { odestruct (Hinv2 π' i' _ _) as (? & ? & ? & ? & ? & ?); first done.
        eexists _, _. rewrite lookup_insert_ne; last congruence. done. }
      eapply Hinv2 in Hlook as (? & ? & ? & ? & Hlook2 & ?).
      simpl in *. simplify_eq. simpl in *.
      move: Hlook2. assert (i' ≠ S (length ts)). { intros ->. congruence. }
      rewrite lookup_cons_ne_0; last lia.
      replace (Init.Nat.pred (S (length ts) - i')) with (length ts - i')%nat by lia.
      eexists _, _.
      split_and!. { rewrite lookup_insert_eq. done. }
      all: simpl.
      + lia.
      + lia.
      + rewrite lookup_cons_ne_0; last lia.
        replace (Init.Nat.pred (S (length ts) - i')) with (length ts - i')%nat by lia.
        done.
      + done.
    - iApply big_sepM_insert; first done. iFrame. done.
    - intros π' i' x' ????? Hlook1 Hlook2 Hlook3.
      apply lookup_insert_Some in Hlook1 as [(<- & <-) | (Hneq & Hlook1)]; simpl in *; first last.
      { setoid_rewrite lookup_insert_ne; last congruence. eapply Hinv3; done. }
      destruct (decide (i' = S (length ts))) as [-> | ?]; first last.
      { setoid_rewrite lookup_insert_ne; last congruence.
        eapply Hinv3; simpl; try done; simpl; first lia.
        move: Hlook2. rewrite !lookup_cons_ne_0; [ | lia..].
        done. }
      simpl in Hlook2. rewrite Nat.sub_diag/= in Hlook2.
      injection Hlook2 as <-.
      simpl in Hlook3.
      apply lookup_insert_Some in Hlook3 as [(<- & [=<- <-]) | (Hneq & Hlook3)].
      { eexists. rewrite lookup_insert_eq; done. }
      setoid_rewrite lookup_insert_ne; last congruence.
      eapply Hinv3; simpl; try done; simpl; first lia.
      rewrite Nat.sub_diag//.
    - intros π' i' x' ?? Hlook.
      eapply lookup_insert_Some in Hlook as [([= <- <- <-] & [= <- <-]) | (Hneq & Hlook)].
      { eexists _, _, _. rewrite lookup_insert_eq. split; first done. simpl.
        rewrite Nat.sub_diag. simpl. split; first lia.
        split; first done. simpl. rewrite lookup_insert_eq; done. }
      destruct (decide (π = π')) as [<- | Hneq1]; first last.
      { setoid_rewrite lookup_insert_ne; last done. by eapply Hinv4. }

      opose proof (Hinv4 π i' _ _ _ Hlook) as (ts' & cf' & ? & ? & ? & Ha & ? & ?).
      simplify_eq. simpl in *.
      destruct (decide (i' = S (length ts))) as [-> | Hneq2]; first last.
      { setoid_rewrite lookup_insert_eq; simpl.
        eexists _, cf', _. split; first done.
        split_and!; try done; simpl; try lia.
        move: Ha. rewrite !lookup_cons_ne_0; [ | lia..].
        done. }
      setoid_rewrite lookup_insert_eq; simpl.
      eexists _, _, _.
      split; first done. simpl.
      rewrite Nat.sub_diag. simpl. split; first lia.
      split; first done. split; last done.
      simpl. rewrite lookup_insert_ne; last congruence.
      rewrite Nat.sub_diag in Ha. simpl in Ha. injection Ha as <-.
      done.
  Qed.

  Lemma frame_alloc_vars_cons cf x l ly vars ls :
    frame_alloc_var (frame_alloc_vars cf vars ls) x l ly = frame_alloc_vars cf ((x, ly) :: vars) (l :: ls).
  Proof. done. Qed.
  Lemma frame_dealloc_vars_cons cf x vars :
    frame_dealloc_var (frame_dealloc_vars cf vars) x = frame_dealloc_vars cf (x :: vars).
  Proof. done. Qed.

  Lemma thread_frame_allocate_vars st π i ts cf (vars : list (var_name * layout)) locs syntys cf' st' S :
    Forall2 syn_type_has_layout syntys vars.*2 →
    Forall (λ x, x ∉ S) vars.*1 →
    NoDup vars.*1 →
    st !! π = Some ts →
    thread_get_frame ts = Some cf →
    cf' = frame_alloc_vars cf vars locs →
    st' = <[π := thread_update_frame ts cf']> st →
    length locs = length vars →
    thread_ctx st -∗
    current_frame π i -∗
    ([∗ list] l; ly ∈ locs; vars.*2, freeable l (ly_size ly) 1 StackAlloc) -∗
    allocated_locals (π, i) S ==∗
    current_frame π i ∗
    allocated_locals (π, i) (vars.*1 ++ S) ∗
    ([∗ list] xl; synty ∈ zip (vars.*1) locs; syntys, xl.1 is_live{(π, i), synty} xl.2) ∗
    thread_ctx st'.
  Proof.
    induction vars as [ | [x ly] vars IH] in locs, syntys, cf', st', ts, cf, st, S |-*.
    { simpl. intros Hf%Forall2_length. destruct syntys; last done.
      simpl. rewrite left_id.
      iIntros (? ? Hlook Hframe -> -> ?) "Hctx $ _ $".
      rewrite insert_id; first done.
      unfold thread_update_frame, frame_alloc_vars; simpl.
      rewrite /thread_get_frame head_lookup in Hframe.
      opose proof (proj1 (hd_error_tl_repr ts.(ts_frames) cf (tail ts.(ts_frames))) _) as Heq.
      { rewrite head_lookup. done. }
      rewrite -Heq Hlook. destruct ts; done. }
    intros Hst Hfresh Hnodup Hts Hcf -> -> Hlocs.
    iIntros "Htctx Hframe Hfree Hlocals".
    simpl in Hst.
    apply Forall2_cons_inv_r in Hst as (synty1 & syntys' & Hsynty1 & Hst & ->).
    simpl in Hfresh. apply Forall_cons in Hfresh as (Hfresh1 & Hfresh).
    destruct locs as [ | l1 locs]; first done.
    simpl in Hnodup.
    apply NoDup_cons in Hnodup as [Hnodup1 Hnodup].
    simpl in Hlocs.
    iDestruct "Hfree" as "(Hfree1 & Hfree)".
    iMod (IH _ _ _ locs syntys' with "Htctx Hframe Hfree Hlocals") as "(Hframe & Hlocals & Hxs & Htctx)"; [done.. | lia | ].
    iMod (thread_frame_allocate_var _ _ _ _ _ x l1 ly synty1 with "Htctx Hframe Hfree1 Hlocals") as "(Hframe & Hlocals & Hx & Htctx)".
    { done. }
    { rewrite lookup_insert_eq//. }
    { unfold thread_get_frame, thread_update_frame. simpl. done. }
    { rewrite elem_of_app. intros [Hel1 | Hel1]; done. }
    { rewrite frame_alloc_vars_cons//. }
    { unfold thread_update_frame. simpl.
      rewrite insert_insert decide_True; last done.
      done. }
    iFrame. simpl. done.
  Qed.

  Lemma thread_frame_deallocate_var st π i ts cf x cf' st' M synty l :
    st !! π = Some ts →
    thread_get_frame ts = Some cf →
    cf' = (frame_dealloc_var cf x) →
    st' = <[π := thread_update_frame ts cf']> st →
    thread_ctx st -∗
    current_frame π i -∗
    allocated_locals (π, i) M -∗
    x is_live{(π, i), synty} l ==∗
    current_frame π i ∗
    allocated_locals (π, i) (list_difference M [x]) ∗
    freeable l (ly_size (use_layout_alg' synty)) 1 StackAlloc ∗
    thread_ctx st'.
  Proof.
    iIntros (Hthread Hframe -> ->) "Htctx Hframe Hlocals Hx".
    iPoseProof (state_lookup_current_frame with "Htctx Hframe Hlocals") as "(%ts' & %cf' & %Hts & %Hcf & %Hlocals & ->)".
    unfold thread_get_frame, call_frame_has_locals in *.
    simplify_eq.
    rewrite head_lookup in Hframe.
    iDestruct "Htctx" as "(Ha & (%m1 & Hauth1 & %Hinv1 & %Hinv2) & (%m2 & Hauth2 & Hfrees & %Hinv3 & %Hinv4))".
    rewrite current_frame_unfold !allocated_locals_unfold local_is_allocated_at_unfold.
    iPoseProof (ghost_map_lookup with "Hauth2 Hx") as "%Hlook".
    iMod (ghost_map_update with "Hauth1 Hlocals") as "(Hauth1 & $)".
    iMod (ghost_map_delete with "Hauth2 Hx") as "Hauth2".
    iFrame.
    iPoseProof (big_sepM_delete with "Hfrees") as "((%ly' & %Hst & Hfree1) & $)".
    { done. }
    simpl in *.

    unfold use_layout_alg'. rewrite Hst. iFrame "Hfree1".
    iSplitL.
    { iModIntro.
      unfold thread_current_frame_auth.
      iApply (ghost_map_auth_prove_eq with "Ha").
      unfold to_current_frame.
      rewrite fmap_insert.
      symmetry. apply insert_id.
      rewrite lookup_fmap Hthread.
      rewrite /thread_update_frame /=.
      rewrite length_tl. f_equiv.
      apply lookup_lt_Some in Hframe.
      lia. }
    iPureIntro.
    specialize (lookup_lt_Some _ _ _ Hframe) as ?.
    destruct ts as [ts].
    destruct ts as [ | cf' ts]; first done.
    simpl in *. injection Hframe as [= ->].
    opose proof (Hinv4 _ _ _ _ _ Hlook) as (? & ? & ? & Hlook1 & ? & Hlook2 & Hlook4 & ?).
    simplify_eq. simpl in *.
    rewrite Nat.sub_diag/= in Hlook2. injection Hlook2 as <-.
    assert (x ∈ M).
    { rewrite -Hlocals. apply list_elem_of_fmap.
      eexists (_, _). split; first done. by apply elem_of_map_to_list. }
    split_and!.
    - intros π' i' ?? Hlt Hlook1 Hlook2.
      apply lookup_insert_Some in Hlook1 as [(<- & <-) | (Hneq & Hlook1)]; first last.
      { odestruct (Hinv1 π' i' _ _ _ _ _) as (? & ?); try done.
        eexists. rewrite lookup_insert_ne; last congruence. done. }
      rewrite /thread_update_frame/= in Hlook2.
      rewrite /= in Hlt.
      destruct (decide (i' = S (length ts))) as [Heq | Hneq].
      + subst. rewrite Nat.sub_diag/= in Hlook2.
        injection Hlook2 as <-.
        eexists. rewrite lookup_insert_eq. split; first done.
        by eapply call_frame_has_locals_dealloc_var.
      + move: Hlook2. destruct i' as [ | i']; first lia.
        simpl. rewrite lookup_cons_ne_0; last lia.
        intros Hlook2.
        setoid_rewrite lookup_insert_ne; last congruence.
        eapply Hinv1; [ | done | ]; simpl; first lia.
        rewrite lookup_cons_ne_0; last lia.
        done.
    - intros π' i' names Hlook'.
      apply lookup_insert_Some in Hlook' as [([= <- <-]& <-) | (Hneq & Hlook')].
      { eexists _, _. rewrite lookup_insert_eq. split_and!; simpl; [done | lia | simpl; lia | | ].
        + simpl. rewrite Nat.sub_diag. done.
        + by eapply call_frame_has_locals_dealloc_var. }
      destruct (decide (π = π')) as [<- | Hneq1]; first last.
      { odestruct (Hinv2 π' i' _ _) as (? & ? & ? & ? & ? & ?); first done.
        eexists _, _. rewrite lookup_insert_ne; last congruence. done. }
      eapply Hinv2 in Hlook' as (? & ? & ? & ? & Hlook2 & ?).
      simpl in *. simplify_eq. simpl in *.
      move: Hlook2. assert (i' ≠ S (length ts)). { intros ->. congruence. }
      rewrite lookup_cons_ne_0; last lia.
      replace (Init.Nat.pred (S (length ts) - i')) with (length ts - i')%nat by lia.
      eexists _, _.
      split_and!. { rewrite lookup_insert_eq. done. }
      all: simpl.
      + lia.
      + lia.
      + rewrite lookup_cons_ne_0; last lia.
        replace (Init.Nat.pred (S (length ts) - i')) with (length ts - i')%nat by lia.
        done.
      + done.
    - intros π' i' x' ????? Hlook1 Hlook2 Hlook3.
      apply lookup_insert_Some in Hlook1 as [(<- & <-) | (Hneq & Hlook1)]; simpl in *; first last.
      { setoid_rewrite lookup_delete_ne; last congruence. eapply Hinv3; done. }
      destruct (decide (i' = S (length ts))) as [-> | ?]; first last.
      { setoid_rewrite lookup_delete_ne; last congruence.
        eapply Hinv3; simpl; try done; simpl; first lia.
        move: Hlook2. rewrite !lookup_cons_ne_0; [ | lia..].
        done. }
      simpl in Hlook2. rewrite Nat.sub_diag/= in Hlook2.
      injection Hlook2 as <-.
      simpl in Hlook3.
      apply lookup_delete_Some in Hlook3 as (Hneq & Hlook3).
      setoid_rewrite lookup_delete_ne; last congruence.
      eapply Hinv3; simpl; try done; simpl; first lia.
      rewrite Nat.sub_diag//.
    - intros π' i' x' ?? Hlook'.
      eapply lookup_delete_Some in Hlook' as (Hneq & Hlook').
      destruct (decide (π = π')) as [<- | Hneq1]; first last.
      { setoid_rewrite lookup_insert_ne; last done. by eapply Hinv4. }

      opose proof (Hinv4 π i' _ _ _ Hlook') as (ts' & cf' & ? & ? & ? & Ha & ? & ?).
      simplify_eq. simpl in *.
      destruct (decide (i' = S (length ts))) as [-> | Hneq2]; first last.
      { setoid_rewrite lookup_insert_eq; simpl.
        eexists _, cf', _. split; first done.
        split_and!; try done; simpl; try lia.
        move: Ha. rewrite !lookup_cons_ne_0; [ | lia..].
        done. }
      setoid_rewrite lookup_insert_eq; simpl.
      eexists _, _, _.
      split; first done. simpl.
      rewrite Nat.sub_diag. simpl. split; first lia.
      split; first done. split; last done.
      simpl. rewrite lookup_delete_ne; last congruence.
      rewrite Nat.sub_diag in Ha. simpl in Ha. injection Ha as <-.
      done.
  Qed.

  Lemma thread_frame_deallocate_vars st π i ts cf (vars : list var_name) cf' st' S syntys locs :
    st !! π = Some ts →
    thread_get_frame ts = Some cf →
    cf' = frame_dealloc_vars cf vars →
    st' = <[π := thread_update_frame ts cf']> st →
    length locs = length vars →
    length syntys = length vars →
    thread_ctx st -∗
    current_frame π i -∗
    allocated_locals (π, i) S -∗
    ([∗ list] x; lsynty ∈ vars; zip locs syntys, x is_live{(π, i), lsynty.2} lsynty.1) ==∗
    current_frame π i ∗
    allocated_locals (π, i) (list_difference S vars) ∗
    ([∗ list] l; synty ∈ locs; syntys, freeable l (ly_size (use_layout_alg' synty)) 1 StackAlloc) ∗
    thread_ctx st'.
  Proof.
    induction vars as [ | x vars IH] in cf', st', ts, cf, st, S, locs, syntys |-*.
    { simpl. rewrite list_difference_nil_r.
      iIntros (Hlook Hframe -> -> Hlen1 Hlen2) "Hctx $ $ _".
      destruct locs; last done.
      destruct syntys; last done.
      simpl. iR.
      rewrite insert_id; first done.
      unfold thread_update_frame; simpl.
      rewrite /thread_get_frame head_lookup in Hframe.
      opose proof (proj1 (hd_error_tl_repr ts.(ts_frames) cf (tail ts.(ts_frames))) _) as Heq.
      { rewrite head_lookup. done. }
      rewrite -Heq Hlook. destruct ts; done. }
    intros Hts Hcf -> -> Hlen1 Hlen2.
    destruct locs as [ | l locs]; first done.
    destruct syntys as [ | synty syntys]; first done.
    iIntros "Htctx Hframe Hlocals Hxs".
    simpl. iDestruct "Hxs" as "(Hx & Hxs)".
    iMod (IH with "Htctx Hframe Hlocals Hxs") as "(Hframe & Hlocals & Hfrees & Htctx)"; [done.. | | | ].
    { simpl in *. lia. }
    { simpl in *. lia. }
    iMod (thread_frame_deallocate_var with "Htctx Hframe Hlocals Hx") as "(Hframe & Hlocals & Hx & Hfree & Htctx)".
    { rewrite lookup_insert_eq//. }
    { unfold thread_get_frame, thread_update_frame. simpl. done. }
    { rewrite frame_dealloc_vars_cons//. }
    { unfold thread_update_frame.
      rewrite insert_insert decide_True; last done.
      cbn -[frame_dealloc_vars].
      done. }
    iFrame. simpl.
    rewrite -list_difference_app_r.
    rewrite (list_difference_proper_r _ _ (x :: vars)); first done.
    intros y. rewrite elem_of_app !elem_of_cons elem_of_nil right_id.
    naive_solver.
  Qed.
End rules.


(* Bundling everything up *)
Definition state_ctx `{!heapG Σ} `{!threadG Σ} `{!LayoutAlg} `{!FUpd (iProp Σ)} (σ:state) : iProp Σ :=
  heap_state_ctx σ.(st_heap) ∗
  fntbl_ctx σ.(st_fntbl) ∗
  thread_ctx σ.(st_thread)
.
