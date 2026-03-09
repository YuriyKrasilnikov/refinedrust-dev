From stdpp Require Import gmap list.
From caesium Require Export base byte layout int_type loc val struct.
Set Default Proof Using "Type".

(** * Heap and allocations. *)

(** ** Representation of the heap. *)

(** Per-byte entry in a cell's write history (weak memory).
    All bytes of a single atomic write share identical epoch/release/view.
    Redundant per-byte but uniform with Caesium's per-byte heap model. *)
Record byte_write_entry := ByteWriteEntry {
  bwe_value   : mbyte;        (** Written byte value. *)
  bwe_epoch   : nat;          (** Monotonic per-location counter. *)
  bwe_release : bool;         (** true = Release write. *)
  bwe_view    : gmap loc nat; (** Snapshot of writer's coherence at write time. *)
}.

Inductive lock_state :=
  | WSt
  | RSt (n : nat) (max_epoch : nat)
  | PendingSt (history : list byte_write_entry)
.

(** A cell is "idle" (ready for atomic write) when in RSt(0) or PendingSt. *)
Definition lock_state_idle (st : lock_state) : Prop :=
  (∃ me, st = RSt 0 me) ∨ (∃ hist, st = PendingSt hist).

Record heap_cell := HeapCell {
  hc_alloc_id   : alloc_id;   (** Allocation owning the cell. *)
  hc_lock_state : lock_state;  (** Datarace detection stuff. *)
  hc_value      : mbyte;       (** Byte value. *)
  hc_max_epoch  : nat;         (** Monotonic epoch counter, owned by the cell. *)
}.

(** Uniform accessor for the next epoch — one field access, no pattern match. *)
Definition next_epoch_of (c : heap_cell) : nat := S c.(hc_max_epoch).

Definition heap := gmap addr heap_cell.

(** ** Functions and predicates for manipulating the heap. *)

(** Predicate stating that the heap [h] contains value [v] at address [a],
and that every cell involved has an allocation identifier and a lock state
that satisfy [Paid] and [Plk] respectively. *)
Fixpoint heap_lookup (a : addr) (v : val) (Paid : alloc_id → Prop)
                     (Plk : lock_state → Prop) (h : heap) : Prop :=
  match v with
  | []     => True
  | b :: v => (∃ aid lk ep, h !! a = Some (HeapCell aid lk b ep) ∧ Paid aid ∧ Plk lk) ∧
              heap_lookup (Z.succ a) v Paid Plk h
  end.

(** Write value [v] at address [a] in heap [h]. Each cell is built by [fcell]
    which receives the new byte and the previous cell (if any).
    Use [mk_cell] / [mk_cell_weak] smart constructors for instantiation. *)
Fixpoint heap_update (a : addr) (v : val)
    (fcell : mbyte → option heap_cell → heap_cell) (h : heap) : heap :=
  match v with
  | []     => h
  | b :: v => partial_alter (λ m, Some (fcell b m)) a
              (heap_update (Z.succ a) v fcell h)
  end.

(** Smart constructor for standard writes: [faid] builds alloc_id,
    [flk] builds lock_state, [fep] builds epoch. *)
Definition mk_cell (faid : option alloc_id → alloc_id)
    (flk : option lock_state → lock_state)
    (fep : option nat → nat)
    : mbyte → option heap_cell → heap_cell :=
  λ b old, {|
    hc_alloc_id   := faid (hc_alloc_id <$> old);
    hc_lock_state := flk (hc_lock_state <$> old);
    hc_value      := b;
    hc_max_epoch  := fep (hc_max_epoch <$> old) |}.
Global Arguments mk_cell _ _ _ _ _ /.

(** Smart constructor for weak memory writes: [flk_w] additionally receives
    the new byte and old (lock_state, byte) pair for per-byte PendingSt history. *)
Definition mk_cell_weak (faid : option alloc_id → alloc_id)
    (flk_w : mbyte → option (lock_state * mbyte) → lock_state)
    (fep : option nat → nat)
    : mbyte → option heap_cell → heap_cell :=
  λ b old, {|
    hc_alloc_id   := faid (hc_alloc_id <$> old);
    hc_lock_state := flk_w b
        (option_map (λ c, (c.(hc_lock_state), c.(hc_value))) old);
    hc_value      := b;
    hc_max_epoch  := fep (hc_max_epoch <$> old) |}.
Global Arguments mk_cell_weak _ _ _ _ _ /.

Definition heap_lookup_loc (l : loc) (v : val) (Plk : lock_state → Prop)
                           (h : heap) : Prop :=
  heap_lookup l.(loc_a) v (λ aid, l.(loc_p) = ProvAlloc aid) Plk h.

Definition heap_alloc (a : addr) (v : val) (aid : alloc_id) (h : heap) : heap :=
  heap_update a v (mk_cell (λ _, aid) (λ _, RSt 0 0) (λ _, 0%nat)) h.

Definition heap_at (l : loc) (ly : layout) (v : val) (Plk : lock_state → Prop)
                   (h : heap) : Prop :=
  ((∃ aid, l.(loc_p) = ProvAlloc (aid)) ∨ (l.(loc_p) = ProvNone ∧ v = [])) ∧
  l `has_layout_loc` ly ∧ v `has_layout_val` ly ∧
  heap_lookup_loc l v Plk h.

Definition heap_upd (l : loc) v flk h :=
  heap_update l.(loc_a) v (mk_cell (default (default dummy_alloc_id (prov_alloc_id l.(loc_p)))) flk (default 0%nat)) h.

(** Predicate stating that the [n] first bytes from address [a] in [h] have
not been allocated. *)
Definition heap_range_free (h : heap) (a : addr) (n : nat) : Prop :=
  ∀ a', a ≤ a' < a + n → h !! a' = None.

(** Free [n] cells starting at [a] in [h]. *)
Fixpoint heap_free (a : addr) (n : nat) (h : heap) : heap :=
  match n with
  | O   => h
  | S n => delete a (heap_free (Z.succ a) n h)
  end.

(** ** Lemmas about the heap and related operations. *)

Lemma heap_lookup_inj_val a h v1 v2 Paid1 Paid2 Plk1 Plk2:
  length v1 = length v2 →
  heap_lookup a v1 Paid1 Plk1 h → heap_lookup a v2 Paid2 Plk2 h → v1 = v2.
Proof.
  elim: v1 v2 a; first by move => [|??] //.
  move => ?? IH [|??] //= ? [?] [[?[?[?[??]]]]?] [[?[?[?[??]]]]?]; simplify_eq.
  f_equal. by apply: IH.
Qed.

Lemma heap_lookup_is_Some a p v Paid Plk h:
  heap_lookup a v Paid Plk h →
  a ≤ p < a + length v →
  is_Some (h !! p).
Proof.
  elim: v a => /=; first lia. move => b v IH a [[aid [lk [ep [Ha _]]]] H] Hp.
  destruct (decide (p = a)) as [->|]; first naive_solver.
  apply (IH (Z.succ a)) => //. lia.
Qed.

Lemma heap_update_ext h a v fcell1 fcell2:
  (∀ b m, fcell1 b m = fcell2 b m) →
  heap_update a v fcell1 h = heap_update a v fcell2 h.
Proof.
  move => Hext. elim: v a => //= ?? IH ?. rewrite IH.
  apply: partial_alter_ext => ??. f_equal. by apply Hext.
Qed.

Lemma heap_update_lookup_not_in_range a1 a2 v fcell h:
  a1 < a2 ∨ a2 + length v ≤ a1 →
  heap_update a2 v fcell h !! a1 = h !! a1.
Proof.
  elim: v a1 a2 => // ?? IH ?? H.
  rewrite lookup_partial_alter_ne /=; first apply IH; move: H => [] /=; lia.
Qed.

Lemma heap_update_lookup_in_range a1 a2 v fcell h:
  a2 ≤ a1 < a2 + length v →
  heap_update a2 v fcell h !! a1 =
    Some (fcell (default MPoison (v !! (Z.to_nat (a1 - a2)))) (h !! a1)).
Proof.
  elim: v a1 a2.
  - move => /= a1 a2 [??]. exfalso. lia.
  - move => ?? IH a1 a2 [H1 H2]. destruct (decide (a1 = a2)) as [->|Hne].
    + rewrite lookup_partial_alter_eq -/heap_update Z.sub_diag /=.
      rewrite heap_update_lookup_not_in_range; [done | lia].
    + rewrite lookup_partial_alter_ne // -/heap_update /= IH; last first.
      { rewrite /= in H2. lia. } do 3 f_equal.
      rewrite lookup_cons_ne_0; last lia. f_equal. lia.
Qed.

Lemma heap_free_delete h a1 a2 n :
  delete a1 (heap_free a2 n h) = heap_free a2 n (delete a1 h).
Proof. elim: n a2 => //= ? IH ?. by rewrite delete_delete IH. Qed.
Lemma heap_free_comm l1 l2 n1 n2 h :
  heap_free l2 n2 (heap_free l1 n1 h) =
  heap_free l1 n1 (heap_free l2 n2 h).
Proof.
  induction n2 as [ | n2 IH] in n1, l1, l2 |-*; simpl; first done.
  rewrite -heap_free_delete.
  f_equiv. apply IH.
Qed.


Lemma heap_upd_ext h l v f1 f2:
  (∀ x, f1 x = f2 x) → heap_upd l v f1 h = heap_upd l v f2 h.
Proof. move => Hext. rewrite /heap_upd. apply heap_update_ext => b m /=. by rewrite Hext. Qed.

Lemma heap_at_inj_val l ly h v1 v2 Plk1 Plk2:
  heap_at l ly v1 Plk1 h → heap_at l ly v2 Plk2 h → v1 = v2.
Proof.
  move => [_[?[??]]] [_[?[??]]].
  apply: heap_lookup_inj_val => //. congruence.
Qed.

Lemma heap_lookup_loc_inj_val  l h v v' flk1 flk2 ly:
  v `has_layout_val` ly →
  heap_lookup_loc l v flk1 h → heap_at l ly v' flk2 h → v = v'.
Proof.
  move => ??[_[?[??]]]. apply: heap_lookup_inj_val => //. congruence.
Qed.

Lemma heap_upd_heap_at_id l v flk flk' h:
  heap_lookup_loc l v flk' h →
  (∀ st, flk (Some st) = st) →
  heap_upd l v flk h = h.
Proof.
  rewrite /heap_upd.
  elim: v l => // ?? IH ? [[?[?[?[H[H1 ?]]]]]?] Hlookup /=.
  assert (∀ l, Z.succ l.(loc_a) = (l +ₗ 1).(loc_a)) as -> by done.
  rewrite IH => //. apply: partial_alter_id'.
  by rewrite H Hlookup H1 /=.
Qed.

Lemma heap_free_lookup_in_range a p (n : nat) h:
  a ≤ p < a + n →
  heap_free a n h !! p = None.
Proof.
  elim: n a; first lia. move => n IH a [H1 H2] /=.
  rewrite lookup_delete_None.
  destruct (decide (a = p)) as [->|]; [by left|right].
  apply: IH. lia.
Qed.

Lemma heap_free_lookup_not_in_range a p (n : nat) h:
  ¬ (a ≤ p < a + n) →
  heap_free a n h !! p = h !! p.
Proof.
  elim: n a => //= n IH a H.
  destruct (decide (a = p)) as [->|]; first lia.
  rewrite lookup_delete_ne; last done. apply IH. lia.
Qed.

Lemma heap_lookup_loc_heap_free_disj_allocs s (n : nat) l v Lp h :
  (∀ a, l.(loc_a) ≤ a < l.(loc_a) + length v → a < s ∨ s + n ≤ a) →
  heap_lookup_loc l v Lp (heap_free s n h) ↔ heap_lookup_loc l v Lp h.
Proof.
  unfold heap_lookup_loc.
  induction v as [ | b v IH] in l, s, n, h |-*; simpl; first done.
  intros Hdisj. split.
  - intros [(aid & lk & ep & Hf & ? & ?) Hl].
    split; first last.
    { eapply (IH _ _ (l +ₗ 1)); last done.
      simpl. intros. eapply Hdisj. lia. }
    exists aid, lk, ep. split_and!; try done.
    rewrite -Hf.
    rewrite heap_free_lookup_not_in_range; first done.
    intros [Ha Hb].
    ospecialize (Hdisj l.(loc_a) _); lia.
  - intros [(aid & lk & ep & Hf & ? & ?) Hl].
    split; first last.
    { eapply (IH _ _ (l +ₗ 1)); last done.
      simpl. intros. eapply Hdisj. lia. }
    exists aid, lk, ep. split_and!; try done.
    rewrite -Hf.
    rewrite heap_free_lookup_not_in_range; first done.
    intros [Ha Hb].
    ospecialize (Hdisj l.(loc_a) _); lia.
Qed.

(** ** Representation of allocations. *)

(** An allocation can either be a stack allocation or a heap allocation. *)
Inductive alloc_kind : Set :=
  | HeapAlloc
  | StackAlloc
  | GlobalAlloc.

Record allocation :=
  Allocation {
    al_start : Z;           (* First valid address. *)
    al_len   : nat;         (* Number of allocated byte. *)
    al_alive : bool;        (* Is the allocation still alive. *)
    al_kind  : alloc_kind;   (* On the heap or on the stack? *)
  }.

Definition al_end (al : allocation) : Z :=
  al_start al + al_len al.

Definition allocs := gmap alloc_id allocation.

Definition alloc_same_range (al1 al2 : allocation) : Prop :=
  al1.(al_start) = al2.(al_start) ∧ al1.(al_len) = al2.(al_len).

Definition killed (al : allocation) : allocation :=
  {| al_start := al.(al_start); al_len := al.(al_len); al_alive := false; al_kind := al.(al_kind) |}.

(** Smallest allocatable address (we reserve 0 for NULL). *)
Definition min_alloc_start : Z := 1.

Notation max_alloc_end_zero := (max_int USize) (only parsing).

(** Largest allocatable address (we never allocate the last byte to always
have valid one-past pointers. *)
Definition max_alloc_end : Z := max_alloc_end_zero - 1.


(** Predicate asserting that allocation [a] is in range of the allocatable
memory (e.g., does not contain NULL). *)
Definition allocation_in_range (al : allocation) : Prop :=
  min_alloc_start ≤ al.(al_start) ∧ al_end al ≤ max_alloc_end.

Global Instance elem_of_alloc : ElemOf addr allocation :=
  λ a al, al.(al_start) ≤ a < al_end al.

(** ** Representation of the state of the heap and allocation operations. *)

Record heap_state := {
  hs_heap   : heap;
  hs_allocs : allocs;
}.

Definition alloc_id_alive (aid : alloc_id) (st : heap_state) : Prop :=
  ∃ alloc, st.(hs_allocs) !! aid = Some alloc ∧ alloc.(al_alive).

Definition block_alive (l : loc) (st : heap_state) : Prop :=
  (∃ aid, l.(loc_p) = ProvAlloc aid ∧ alloc_id_alive aid st) ∨
  (* Rust: have a virtual allocation of size zero at every non-null address,
     see the comment on [heap_state_loc_in_bounds] below *)
  (l.(loc_p) = ProvNone ∧ 0 ≤ l.(loc_a) ∧ l.(loc_a) ≤ max_alloc_end_zero).

(** The address range between [l] and [l +ₗ n] (included) is in range of the
    allocation that contains [l]. Note that we consider the 1-past-the-end
    pointer to be in range of an allocation.

   For Rust, we consider every address to have an implicit allocation of size zero.
   See also the discussions at
    https://doc.rust-lang.org/std/ptr/index.html
    https://github.com/model-checking/kani/issues/1489
    https://github.com/rust-lang/unsafe-code-guidelines/issues/93
    https://rust-lang.zulipchat.com/#narrow/stream/136281-t-lang.2Fwg-unsafe-code-guidelines/topic/MiniRust.20.22monotonicity.22.20and.20ZST.20accesses
*)
Definition heap_state_loc_in_bounds (l : loc) (n : nat) (st : heap_state) : Prop :=
  (∃ alloc_id al,
    l.(loc_p) = ProvAlloc alloc_id ∧
    st.(hs_allocs) !! alloc_id = Some al ∧
    allocation_in_range al ∧
    al.(al_start) ≤ l.(loc_a) ∧
    l.(loc_a) + n ≤ al_end al) ∨
  (* NOTE: new for Rust: zero-sized accesses are also allowed with an invalid provenance *)
  (l.(loc_p) = ProvNone ∧ 0 ≤ l.(loc_a) ∧ l.(loc_a) ≤ max_alloc_end_zero ∧ n = 0%nat).

Lemma heap_state_loc_in_bounds_zero_or_has_alloc_id l n σ:
  heap_state_loc_in_bounds l n σ →
  (l.(loc_p) = ProvNone ∧ 0 ≤ l.(loc_a) ∧ l.(loc_a) ≤ max_alloc_end_zero ∧ n = 0%nat) ∨
  (∃ aid, l.(loc_p) = ProvAlloc aid).
Proof. rewrite /heap_state_loc_in_bounds. naive_solver. Qed.

(** Checks that the location [l] is inbounds of its allocation
(one-past-the-end is allowed) and this allocation is still alive *)
Definition valid_ptr (l : loc) (st : heap_state) : Prop :=
  block_alive l st ∧ heap_state_loc_in_bounds l 0 st.

Lemma valid_ptr_in_allocation_range l σ:
  valid_ptr l σ → 0 ≤ l.(loc_a) ≤ max_alloc_end_zero.
Proof.
  move => [_] [Ha|Ha].
  - move : Ha => [?] [] ? [] ? [_ [[? ?] [? ?]]].
    unfold max_alloc_end, min_alloc_start in *.
    lia.
  - move : Ha => [? [?[??]]]. lia.
Qed.
Lemma valid_ptr_in_allocation_range_alloc l σ:
  l.(loc_p) ≠ ProvNone → valid_ptr l σ → min_alloc_start ≤ l.(loc_a) ≤ max_alloc_end.
Proof.
  move => ? [_] [Ha|Ha].
  - move : Ha => [?] [] ? [] ? [_ [[? ?] [? ?]]]. lia.
  - move : Ha => [? [?[??]]]. done.
Qed.

Lemma valid_ptr_is_alloc l σ:
  valid_ptr l σ →
  (∃ aid, l.(loc_p) = ProvAlloc aid) ∨
  l.(loc_p) = ProvNone.
Proof.
  rewrite /valid_ptr /block_alive => [[? _]]. naive_solver.
Qed.

Definition addr_in_range_alloc (a : addr) (aid : alloc_id) (st : heap_state) : Prop :=
  ∃ alloc, st.(hs_allocs) !! aid = Some alloc ∧ a ∈ alloc.

Global Instance alloc_kind_eq_dec : EqDecision alloc_kind.
Proof. solve_decision. Qed.
Global Instance allocation_eq_dec : EqDecision (allocation).
Proof. solve_decision. Qed.
Global Instance alloc_id_alive_dec aid st : Decision (alloc_id_alive aid st).
Proof.
  destruct (st.(hs_allocs) !! aid) as [alloc|] eqn: Haid.
  2: { right. move => [?[??]]. simplify_eq. }
  destruct (alloc.(al_alive)) eqn:?.
  - left. eexists _. naive_solver.
  - right. move => [?[??]]. destruct alloc; naive_solver.
Qed.
Global Instance block_alive_dec l st : Decision (block_alive l st).
Proof.
  apply or_dec.
  - destruct (l.(loc_p)) as [| aid |] eqn: Hl.
    1,3: try (right => -[?[??]]; destruct l; naive_solver).
    eapply (exists_dec_unique aid); [| apply _]. destruct l; naive_solver.
  - solve_decision.
Qed.
Global Instance heap_state_loc_in_bounds_dec l n st : Decision (heap_state_loc_in_bounds l n st).
Proof.
  apply or_dec.
  - destruct (l.(loc_p)) as [| aid |] eqn: Hl.
    1,3: (right => -[?[??]]; destruct l; naive_solver).
    destruct (st.(hs_allocs) !! aid) as [al|] eqn:?.
    2: right => -[?[?[??]]]; destruct l; naive_solver.
    eapply (exists_dec_unique aid); [ destruct l; naive_solver|].
    eapply (exists_dec_unique al); [ destruct l; naive_solver|].
    apply _.
  - solve_decision.
Qed.

(** ** Converting a value to a boolean (for conditionals). *)

Definition cast_to_bool (ot: op_type) (v: val) (st: heap_state) : option bool :=
  match ot with
  | BoolOp   => val_to_bool v
  | IntOp it => val_to_Z v it ≫= λ n, Some (bool_decide (n ≠ 0))
  | _        => None
  end.

(** ** MemCast: Transforming bytes read from memory.
  [mem_cast] should only be called with length of [v] matching [ot] *)
Fixpoint mem_cast (v : val) (ot : op_type) (st : (gset addr * heap_state)) : val :=
  default (replicate (length v) MPoison) (
  match ot with
  | PtrOp =>
    if val_to_loc v is Some l then Some v else
      (* interpret as an integer *)
      v' ← val_to_bytes v;
      a ← val_to_Z v' USize;
      Some (val_of_loc (Loc ProvNone a))
  | IntOp it => val_to_bytes v
  | CharOp => if val_to_char v is Some _ then val_to_bytes v else None
  | BoolOp => if val_to_bool v is Some _ then val_to_bytes v else None
  (* The resize technically should not be necessary since mem_cast
  should only be called if the size is equal to the length of the
  value. But adding it makes proving mem_cast_length a lot easier. *)
  | StructOp sl ots => Some $ resize (length v) MPoison $ mjoin $ zip_with (λ f x, f x)
      (pad_struct sl.(sl_members)
                  (((λ ot, λ v, mem_cast v ot st) <$> ots))
                  (λ ly _, (replicate (ly_size ly) MPoison)))
      (reshape (ly_size <$> sl.(sl_members).*2) v)
  | UntypedOp _ => Some v
  end).

Definition mem_cast_id (v : val) (ot : op_type) : Prop :=
  ∀ st, mem_cast v ot st = v.

Lemma mem_cast_length v ot st:
  length (mem_cast v ot st) = length v.
Proof.
  destruct ot => /=.
  - destruct (val_to_bool v) => /=.
    + destruct (val_to_bytes v) eqn:Hv => //=.
      * move: Hv => /length_mapM. lia.
      * by rewrite length_replicate.
    + by rewrite length_replicate.
  - destruct (val_to_bytes v) eqn:Hv => //=.
    + move: Hv => /length_mapM. lia.
    + by rewrite length_replicate.
  - case_match => //=.
    destruct (val_to_bytes v) as [v'|] eqn:Hv => //=. 2: by rewrite length_replicate.
    move: Hv => /length_mapM ->.
    destruct (val_to_Z v') eqn:Hv' => //=. 2: by rewrite length_replicate.
    move: Hv' => /val_to_Z_length /=?.
    by repeat case_match.
  - by rewrite length_resize.
  - done.
  - destruct (val_to_char v) => /=.
    + destruct (val_to_bytes v) eqn:Hv => //=.
      * move: Hv => /length_mapM. lia.
      * by rewrite length_replicate.
    + by rewrite length_replicate.
Qed.

Lemma mem_cast_id_loc l :
  mem_cast_id (val_of_loc l) PtrOp.
Proof. move => st. rewrite /mem_cast /=. by rewrite val_to_of_loc. Qed.

Lemma mem_cast_id_int it v n :
  val_to_Z v it = Some n →
  mem_cast_id v (IntOp it).
Proof. move => Hi st. rewrite /mem_cast /=. by erewrite val_to_bytes_id. Qed.

Lemma mem_cast_id_bool v b :
  val_to_bool v = Some b →
  mem_cast_id v BoolOp.
Proof. move => Hb st. rewrite /mem_cast /= Hb. by erewrite val_to_bytes_id_bool. Qed.

Lemma mem_cast_id_char v z :
  val_to_char v = Some z →
  mem_cast_id v CharOp.
Proof. move => Hb st. rewrite /mem_cast /= Hb. by erewrite val_to_bytes_id_char. Qed.

Lemma mem_cast_struct_reshape sl v st ots:
  length ots = length (field_names (sl_members sl)) →
  v `has_layout_val` sl →
  (∀ i v' n ly,
      reshape (ly_size <$> (sl_members sl).*2) v !! i = Some v' →
      sl_members sl !! i = Some (Some n, ly) →
      v' `has_layout_val` ly) →
  reshape (ly_size <$> (sl_members sl).*2) (mem_cast v (StructOp sl ots) st) =
  (zip_with (λ f x, f x)
            (pad_struct (sl_members sl) ((λ ot v, mem_cast v ot st) <$> ots) (λ ly _, replicate (ly_size ly) MPoison))
            (reshape (ly_size <$> (sl_members sl).*2) v)).
Proof.
  move => ? Hv Hly. rewrite /mem_cast/=-/mem_cast resize_all_alt. 2: {
    rewrite length_join Hv {1}/ly_size /=.
    apply: sum_list_eq.
    (* TODO: This is the same proof as below. Somehow unify these two proofs. *)
    apply Forall2_same_length_lookup_2.
    { rewrite !length_fmap length_zip_with length_reshape pad_struct_length !length_fmap. lia. }
    move => i n1 n2. rewrite !list_lookup_fmap.
    move => /fmap_Some[?[/fmap_Some[?[??]]?]]; simplify_eq.
    move => /fmap_Some[?[/lookup_zip_with_Some[?[?[?[Hs?]]]]?]].
    move: Hs => /pad_struct_lookup_Some[|n[?[? Hor]]]. { by rewrite length_fmap. }
    unfold field_list in *. simplify_eq/=.
    destruct Hor as [[? Hl] | [??]]; simplify_eq/=. 2: by rewrite length_replicate.
    move: Hl. rewrite list_lookup_fmap. move => /fmap_Some[?[??]]. simplify_eq.
    destruct n as [n|] => //. rewrite mem_cast_length. by erewrite Hly.
  }
  rewrite reshape_join //.
  apply Forall2_same_length_lookup_2.
  { rewrite length_zip_with length_reshape pad_struct_length !length_fmap. lia. }
  move => i v' sz /lookup_zip_with_Some[?[?[?[/pad_struct_lookup_Some Hl ?]]]].
  move: Hl => [|n[?[Hin2 Hor]]]. { rewrite length_fmap //. } simplify_eq.
  rewrite !list_lookup_fmap => /fmap_Some[?[/fmap_Some[?[Hin ?]]?]]. rewrite Hin2 in Hin. simplify_eq/=.
  destruct Hor as [[? Hl] |[??]]; simplify_eq. 2: by rewrite length_replicate.
  move: Hl. rewrite list_lookup_fmap => /fmap_Some[?[??]]. simplify_eq. rewrite mem_cast_length.
  destruct n => //. by apply: Hly.
Qed.

Lemma mem_cast_idemp v ot st st' :
  v `has_layout_val` (ot_layout ot) →
  op_type_wf ot →
  mem_cast (mem_cast v ot st) ot st' = mem_cast v ot st.
Proof.
  intros Hly Hwf.
  induction ot as [ | | | sl ots IH | | ] using op_type_recursor in v, Hly, Hwf|-*; simpl.
  - rewrite /mem_cast.
    destruct (val_to_bool v) as [b | ] eqn:Heq.
    + rewrite (val_to_bytes_id_bool _ b); last done. simpl.
      rewrite Heq. simpl. rewrite (val_to_bytes_id_bool _ b); done.
    + simpl. destruct v; simpl; first done. rewrite length_replicate. done.
  - rewrite /mem_cast.
    destruct (val_to_bytes v) as [v' | ] eqn:Heq; simpl.
    + erewrite val_to_bytes_idemp; done.
    + rewrite length_replicate.
      generalize (length v). intros []; done.
  - rewrite /mem_cast.
    destruct (val_to_loc v) as [l | ] eqn:Heq; simpl.
    { rewrite Heq. done. }
    destruct (val_to_bytes v) as [v' | ] eqn:Heq'; simpl.
    + destruct (val_to_Z v' USize) as [ z | ] eqn:Heq2; simpl.
      * by rewrite val_to_of_loc //.
      * destruct v; simpl; first done.
        rewrite length_replicate. done.
    + destruct v; simpl; first done.
      rewrite length_replicate //.
  - rewrite /mem_cast. fold mem_cast.
    simpl. rewrite length_resize.
    simpl in Hly.
    f_equiv. f_equiv.

    move: Hly Hwf.
    rewrite /has_layout_val /layout_of {1}/ly_size/=.
    generalize (sl_members sl) => f Hly Hwf.
    clear sl.

    induction f as [ | [name ly] f IH'] in v, ots, Hly, Hwf, IH |-*; simpl; first done.
    simpl in Hly.
    destruct name as [ name | ].
    + destruct ots as [ | ot ots]; simpl; first done.
      simpl in Hwf; destruct Hwf as ((Hwf1 & <-) & Hwf).
      rewrite take_resize.
      rewrite resize_app; first last.
      { rewrite mem_cast_length length_take//. }
      inversion IH as [ | ? IH1 ? IH2 ]; subst.

      f_equiv.
      * apply IH1; last done.
        rewrite /has_layout_val length_take. lia.
      * (* use IH *)
        specialize (IH' (drop (ly_size (ot_layout ot)) v) _ IH2).
        rewrite drop_resize_le; last lia.
        rewrite -{2}IH'; last done; first last.
        { rewrite length_drop. unfold fmap. lia. }
        f_equiv; first done.
        f_equiv; first done.
        rewrite length_drop.
        f_equiv.
        rewrite drop_app_length'; first done.
        rewrite mem_cast_length length_take. lia.
    + (* padding field *)
      f_equiv.
      rewrite drop_resize_le; last lia.
      specialize (IH' (drop (ly_size ly) v) _ IH).
      rewrite -{2}IH'; last done; first last.
      { rewrite length_drop. unfold fmap. lia. }
      f_equiv. f_equiv; first done.
      rewrite length_drop.
      f_equiv.
      rewrite drop_app_length'; first done.
      rewrite length_replicate//.
  - done.
  - rewrite /mem_cast.
    destruct (val_to_char v) as [z | ] eqn:Heq.
    + rewrite (val_to_bytes_id_char _ z); last done. simpl.
      rewrite Heq. simpl. rewrite (val_to_bytes_id_char _ z); done.
    + rewrite length_replicate.
      generalize (length v) as n. simpl.
      clear.
      intros n. case_match eqn:Heq1; last done.
      destruct (val_to_bytes _) eqn:Heq; last done.
      clear -Heq. simpl.
      destruct n; simpl in Heq. { injection Heq as <-; done. }
      done.
Qed.

Global Typeclasses Opaque mem_cast_id.
Arguments mem_cast : simpl never.

(** ** Allocation and deallocation. *)

Inductive alloc_new_block : heap_state → alloc_kind → loc → val → heap_state → Prop :=
| AllocNewBlock σ l aid kind v:
    let alloc := Allocation l.(loc_a) (length v) true kind in
    l.(loc_p) = ProvAlloc aid →
    σ.(hs_allocs) !! aid = None →
    allocation_in_range alloc →
    heap_range_free σ.(hs_heap) l.(loc_a) (length v) →
    alloc_new_block σ kind l v {|
      hs_heap   := heap_alloc l.(loc_a) v aid σ.(hs_heap);
      hs_allocs := <[aid := alloc]> σ.(hs_allocs);
    |}.

Inductive alloc_new_blocks : heap_state → alloc_kind → list loc → list val → heap_state → Prop :=
| AllocNewBlock_nil σ kind :
    alloc_new_blocks σ kind [] [] σ
| AllocNewBlock_cons σ σ' σ'' l v ls kind vs :
    alloc_new_block σ kind l v σ' →
    alloc_new_blocks σ' kind ls vs σ'' →
    alloc_new_blocks σ kind (l :: ls) (v :: vs) σ''.

Inductive free_block : heap_state → alloc_kind → loc → layout → heap_state → Prop :=
| FreeBlock σ l aid ly kind v:
    let al_alive := Allocation l.(loc_a) ly.(ly_size) true  kind in
    let al_dead  := Allocation l.(loc_a) ly.(ly_size) false kind in
    l.(loc_p) = ProvAlloc aid →
    σ.(hs_allocs) !! aid = Some al_alive →
    length v = ly.(ly_size) →
    heap_lookup_loc l v (λ st, lock_state_idle st) σ.(hs_heap) →
    free_block σ kind l ly {|
      hs_heap   := heap_free l.(loc_a) ly.(ly_size) σ.(hs_heap);
      hs_allocs := <[aid := al_dead]> σ.(hs_allocs);
    |}.

Inductive free_blocks : heap_state → alloc_kind → list (loc * layout) → heap_state → Prop :=
| FreeBlocks_nil σ kind :
    free_blocks σ kind [] σ
| FreeBlocks_cons σ σ' σ'' l ly kind ls :
    free_block σ kind l ly σ' →
    free_blocks σ' kind ls σ'' →
    free_blocks σ kind ((l, ly) :: ls) σ''.

Lemma free_block_inj hs l ly kind hs1 hs2:
  free_block hs kind l ly hs1 → free_block hs kind l ly hs2 → hs1 = hs2.
Proof. destruct l. inversion 1; simplify_eq. by inversion 1; simplify_eq/=. Qed.

Lemma free_blocks_inj hs1 hs2 hs kind ls:
  free_blocks hs kind ls hs1 → free_blocks hs kind ls hs2 → hs1 = hs2.
Proof.
  move Heq: {1}(hs) => hs' Hb.
  elim: Hb hs Heq. { move => ??? ->. by inversion 1. }
  move => ??????? Hb1 ? IH ??.
  inversion 1; simplify_eq. apply: IH; [|done].
  by apply: free_block_inj.
Qed.

Lemma free_blocks_inv_cons hs kind hs2 l ly ls :
  free_blocks hs kind ((l, ly) :: ls) hs2 →
  ∃ hs1, free_block hs kind l ly hs1 ∧ free_blocks hs1 kind ls hs2.
Proof.
  inversion 1; eauto.
Qed.
Lemma free_block_inv hs kind l ly hs':
  free_block hs kind l ly hs' →
  ∃ aid v,
  l.(loc_p) = ProvAlloc aid ∧
  hs.(hs_allocs) !! aid = Some (Allocation l.(loc_a) ly.(ly_size) true kind) ∧
  length v = ly.(ly_size) ∧
  heap_lookup_loc l v (λ st, lock_state_idle st) hs.(hs_heap) ∧
  hs' = {| hs_heap := heap_free l.(loc_a) ly.(ly_size) hs.(hs_heap); hs_allocs := <[aid := Allocation l.(loc_a) ly.(ly_size) false kind]> hs.(hs_allocs); |}.
Proof. inversion 1; eauto 10. Qed.

(** ** Heap state invariant definition. *)

(** Predicate stating that every address [a] mapped by the heap of [st] has
a corresponding allocation that encompasses [a] itself. *)
Definition heap_state_heap_cell_in_range_alloc (st : heap_state) :=
  ∀ a hc,
    st.(hs_heap) !! a = Some hc →
    addr_in_range_alloc a hc.(hc_alloc_id) st.

(** Predicate stating that every address [a] mapped by the heap of [st] has
a corresponding alive allocation. *)
Definition heap_state_heap_cell_alloc_alive (st : heap_state) :=
  ∀ a hc,
    st.(hs_heap) !! a = Some hc →
    alloc_id_alive hc.(hc_alloc_id) st.

(** Predicate stating that all allocations in [st] are in range of memory
that can be allocated. *)
Definition heap_state_alloc_in_range (st : heap_state) :=
  ∀ id a,
    st.(hs_allocs) !! id = Some a →
    allocation_in_range a.

(** Predicate stating that alive allocations of [st] are disjoint. *)
Definition heap_state_alloc_disjoint (st : heap_state) :=
  ∀ id1 id2 a1 a2,
    id1 ≠ id2 →
    st.(hs_allocs) !! id1 = Some a1 →
    st.(hs_allocs) !! id2 = Some a2 →
    alloc_id_alive id1 st →
    alloc_id_alive id2 st →
    a1 ## a2.

(** Predicate stating that every alive allocations in [st] has all of its
addresses mapped in the heap. *)
Definition heap_state_alloc_alive_in_heap (st : heap_state) :=
  ∀ id alloc,
    st.(hs_allocs) !! id = Some alloc →
    alloc_id_alive id st →
    ∀ a, a ∈ alloc → is_Some (st.(hs_heap) !! a).

(** Invariant on the [heap_state] maintained during evaluation. *)
Definition heap_state_invariant (st : heap_state) : Prop :=
  heap_state_heap_cell_in_range_alloc st ∧
  heap_state_heap_cell_alloc_alive st ∧
  heap_state_alloc_in_range st ∧
  heap_state_alloc_disjoint st ∧
  heap_state_alloc_alive_in_heap st.

(** ** Lemmas about the heap state invariant. *)

Lemma heap_state_alloc_alive_free_disjoint σ id a n b kind alloc:
  heap_state_alloc_alive_in_heap σ →
  alloc_id_alive id σ →
  heap_range_free σ.(hs_heap) a n →
  σ.(hs_allocs) !! id = Some alloc →
  Allocation a n b kind ## alloc.
Proof.
  move => Hin_heap Halive Hfree Hal p Hp1 Hp2.
  apply (Hin_heap _ _ Hal Halive) in Hp2 as [? Hp2].
  rewrite Hfree in Hp2; first done. apply Hp1.
Qed.

Lemma alloc_new_block_invariant σ1 σ2 l v kind :
  alloc_new_block σ1 kind l v σ2 →
  heap_state_invariant σ1 →
  heap_state_invariant σ2.
Proof.
  move => []; clear.
  move => σ1 l aid kind v alloc Haid Hfresh Halloc Hrange H.
  destruct H as (Hi1&Hi2&Hi3&Hi4&Hi5). split_and!.
  - move => a [id???] /= Ha. destruct (decide (aid = id)) as [->|Hne].
    + exists alloc. split => /=; first by rewrite lookup_insert_eq.
      destruct (decide (l.(loc_a) ≤ a < l.(loc_a) + length v)) as [|Hne] => //=.
      exfalso. rewrite heap_update_lookup_not_in_range in Ha; last first.
      { destruct (decide (a < l.(loc_a))); [left | right] => //. lia. }
      apply Hi1 in Ha. destruct Ha as [? [Ha ?]].
      by rewrite /= Hfresh in Ha.
    + destruct (decide (a < l.(loc_a) ∨ l.(loc_a) + length v ≤ a)).
      * rewrite heap_update_lookup_not_in_range in Ha; last done.
        apply Hi1 in Ha. destruct Ha as [?[??]].
        eexists; by rewrite lookup_insert_ne.
      * exfalso. rewrite heap_update_lookup_in_range in Ha; last lia.
        by inversion Ha.
  - move => a [id???] /= Ha. destruct (decide (aid = id)) as [->|Hne].
    + exists alloc. by rewrite lookup_insert_eq.
    + destruct (decide (a < l.(loc_a) ∨ l.(loc_a) + length v ≤ a)).
      * rewrite heap_update_lookup_not_in_range in Ha; last done.
        apply Hi2 in Ha. destruct Ha as [?[??]].
        eexists; by rewrite lookup_insert_ne.
      * exfalso. rewrite heap_update_lookup_in_range in Ha; last lia.
        by inversion Ha.
  - move => id a. destruct (decide (id = aid)) as [->|] => /=.
    + rewrite lookup_insert_eq => ?. by simplify_eq.
    + rewrite lookup_insert_ne => //=. apply Hi3.
  - move => id1 id2 al1 al2 /= Hne Hal1 Hal2 Hid1 Hid2.
    destruct (decide (id1 = aid)) as [->|];
    last (destruct (decide (id2 = aid)) as [->|]).
    + rewrite lookup_insert_eq in Hal1. rewrite lookup_insert_ne // in Hal2.
      simplify_eq => ???. eapply heap_state_alloc_alive_free_disjoint => //.
      move: Hid2 => /= [al []] /=. rewrite lookup_insert_ne //. by exists al.
    + rewrite lookup_insert_eq in Hal2. rewrite lookup_insert_ne // in Hal1.
      simplify_eq => ???. eapply heap_state_alloc_alive_free_disjoint => //.
      move: Hid1 => /= [al []] /=. rewrite lookup_insert_ne //. by exists al.
    + rewrite !lookup_insert_ne // in Hal1, Hal2. move: Hid1 Hid2.
      move => [? []] /=; rewrite lookup_insert_ne // => ??.
      move => [? []] /=; rewrite lookup_insert_ne // => ??.
      apply (Hi4 id1 id2 al1 al2) => //; by eexists.
  - move => id al /= Hal [? [/= ? Halive]] a Ha. simplify_eq.
    destruct (decide (id = aid)) as [->|].
    + rewrite lookup_insert_eq /= in Hal.
      rewrite heap_update_lookup_in_range; naive_solver.
    + rewrite lookup_insert_ne // in Hal.
      rewrite heap_update_lookup_not_in_range; last first.
      { assert (¬ (l.(loc_a) ≤ a < l.(loc_a) + length v)); last lia. move => Hin.
        assert (is_Some (hs_heap σ1 !! a)) as [? Heq].
        { eapply Hi5 => //. by eexists. }
        by rewrite Hrange in Heq. }
      eapply (Hi5 _ _ Hal); [by eexists | done |..].
Qed.

Lemma alloc_new_blocks_invariant σ1 σ2 ls vs kind :
  alloc_new_blocks σ1 kind ls vs σ2 →
  heap_state_invariant σ1 →
  heap_state_invariant σ2.
Proof.
  elim => [] // ???????? Hb Hbs IH H.
  apply IH. by eapply alloc_new_block_invariant.
Qed.

Lemma free_block_invariant σ1 σ2 l ly kind :
  free_block σ1 kind l ly σ2 →
  heap_state_invariant σ1 →
  heap_state_invariant σ2.
Proof.
  move => []; clear.
  move => σ l aid ly kind v al_a al_d Haid Hal_a Hlen Hlookup H.
  destruct H as (Hi1&Hi2&Hi3&Hi4&Hi5). split_and!.
  - move => a hc /= Hhc.
    assert (¬ (l.(loc_a) ≤ a < l.(loc_a) + length v)) as Hnot_in.
    { move => ?. rewrite heap_free_lookup_in_range // in Hhc; lia. }
    rewrite heap_free_lookup_not_in_range in Hhc; last lia.
    destruct (Hi1 _ _ Hhc) as [al [?[??]]]. exists al. split; last done.
    rewrite /= lookup_insert_ne; first done.
    move => ?; subst aid. simplify_eq. apply Hnot_in.
    unfold al_end in *. simpl in *. lia.
  - move => a hc /= Hhc.
    assert (¬ (l.(loc_a) ≤ a < l.(loc_a) + length v)) as Hnot_in.
    { move => ?. rewrite heap_free_lookup_in_range // in Hhc; lia. }
    rewrite heap_free_lookup_not_in_range in Hhc; last lia.
    destruct (Hi2 _ _ Hhc) as [al [??]]. exists al.
    rewrite lookup_insert_ne; first done.
    move => Heq. destruct (Hi1 _ _ Hhc) as [?[?[??]]].
    subst al_a. simplify_eq. unfold al_end in *. simpl in *. lia.
  - move => id al /=. destruct (decide (id = aid)) as [->|].
    + rewrite lookup_insert_eq. move => [?]. subst al.
      assert (allocation_in_range al_a); last done.
      by eapply Hi3.
    + rewrite lookup_insert_ne; last done. naive_solver.
  - move => id1 id2 al1 al2 Hne /= Hid1 Hid2 Hal1 Hal2.
    destruct (decide (id1 = aid)) as [->|];
    last (destruct (decide (id2 = aid)) as [->|]).
    + rewrite lookup_insert_eq in Hid1. rewrite lookup_insert_ne // in Hid2.
      simplify_eq. assert (al_a ## al2); last done.
      eapply (Hi4 _ _ _ _ Hne Hal_a Hid2); first by eexists.
      move: Hal2 => [?[/=]]. rewrite lookup_insert_ne //. by eexists.
    + rewrite lookup_insert_eq in Hid2. rewrite lookup_insert_ne // in Hid1.
      simplify_eq. assert (al1 ## al_a); last done.
      eapply (Hi4 _ _ _ _ Hne Hid1 Hal_a); last by eexists.
      move: Hal1 => [?[/=]]. rewrite lookup_insert_ne //. by eexists.
    + destruct Hal1 as [a1 [Ha1 ?]]. destruct Hal2 as [a2 [Ha2 ?]].
      rewrite !lookup_insert_ne // in Hid1, Hid2, Ha1, Ha2.
      apply (Hi4 id1 id2 al1 al2) => //; by eexists.
  - move => id al /= Hid [?[Hal1 Hal2]] a Ha. assert (id ≠ aid) as ?.
    { move => ?; subst id. rewrite lookup_insert_eq in Hal1. naive_solver. }
    rewrite lookup_insert_ne // in Hid, Hal1. simplify_eq.
    rewrite heap_free_lookup_not_in_range;
    first (eapply Hi5 => //; by eexists). move => ?.
    assert (al ## al_a) as Hdisj.
    { apply (Hi4 _ _ _ _ H Hid Hal_a); by eexists. }
    erewrite elem_of_disjoint in Hdisj. by eapply Hdisj.
Qed.

Lemma free_blocks_invariant σ1 σ2 ls kind :
  free_blocks σ1 kind ls σ2 →
  heap_state_invariant σ1 →
  heap_state_invariant σ2.
Proof.
  elim => [] // ??????? Hb Hbs IH H.
  apply IH. by eapply free_block_invariant.
Qed.

Lemma heap_update_heap_cell_in_range_alloc σ a v1 v2 Paid Plk faid flk fep:
  heap_state_heap_cell_in_range_alloc σ →
  heap_lookup a v1 Paid Plk σ.(hs_heap) →
  (∀ aid, faid (Some aid) = aid) →
  length v1 = length v2 →
  heap_state_heap_cell_in_range_alloc {|
    hs_heap := heap_update a v2 (mk_cell faid flk fep) σ.(hs_heap);
    hs_allocs := σ.(hs_allocs);
  |}.
Proof.
  elim: v2 v1 a => // b2 v2 IH [] // b1 v1 a1 Hσ Hcontains Hfaid [] Hlen.
  move => a2 hc H /=. rewrite /heap_lookup -/heap_lookup in Hcontains.
  move: Hcontains => [[id[?[?[Heq [??]]]]] Hcontains].
  destruct (decide (a1 = a2)) as [->|Hne].
  - rewrite lookup_partial_alter_eq -/heap_update in H. simplify_eq => /=.
    rewrite heap_update_lookup_not_in_range; last lia. rewrite Heq /= Hfaid.
    apply (Hσ a2 _ Heq).
  - rewrite lookup_partial_alter_ne // -/heap_update in H.
    by apply (IH _ _ Hσ Hcontains Hfaid Hlen a2 hc) => //.
Qed.

Lemma heap_update_heap_cell_alloc_alive σ a v1 v2 Paid Plk faid flk fep:
  heap_state_heap_cell_alloc_alive σ →
  heap_lookup a v1 Paid Plk σ.(hs_heap) →
  (∀ aid, faid (Some aid) = aid) →
  length v1 = length v2 →
  heap_state_heap_cell_alloc_alive {|
    hs_heap := heap_update a v2 (mk_cell faid flk fep) σ.(hs_heap);
    hs_allocs := σ.(hs_allocs);
  |}.
Proof.
  elim: v2 v1 a => // b2 v2 IH [] // b1 v1 a1 Hσ Hcontains Hfaid [] Hlen.
  move => a2 hc H /=. rewrite /heap_lookup -/heap_lookup in Hcontains.
  move: Hcontains => [[id[?[?[Heq [??]]]]] Hcontains].
  destruct (decide (a1 = a2)) as [->|Hne].
  - rewrite lookup_partial_alter_eq -/heap_update in H. simplify_eq => /=.
    rewrite heap_update_lookup_not_in_range; last lia. rewrite Heq /= Hfaid.
    apply (Hσ a2 _ Heq).
  - rewrite lookup_partial_alter_ne // -/heap_update in H.
    by apply (IH _ _ Hσ Hcontains Hfaid Hlen a2 hc) => //.
Qed.

Lemma heap_update_alloc_alive_in_heap σ a v1 v2 Paid Plk faid flk fep:
  heap_state_alloc_alive_in_heap σ →
  heap_lookup a v1 Paid Plk σ.(hs_heap) →
  (∀ aid, faid (Some aid) = aid) →
  length v1 = length v2 →
  heap_state_alloc_alive_in_heap {|
    hs_heap := heap_update a v2 (mk_cell faid flk fep) σ.(hs_heap);
    hs_allocs := σ.(hs_allocs);
  |}.
Proof.
  move => H Hlookup Hfaid Hlen id al /= Hal Halive p Hp.
  destruct (decide (a ≤ p < a + length v2)).
  - rewrite heap_update_lookup_in_range //=.
  - rewrite heap_update_lookup_not_in_range; last lia. by eapply H.
Qed.

Lemma heap_update_heap_state_invariant σ a v1 v2 Paid Plk faid flk fep:
  heap_state_invariant σ →
  heap_lookup a v1 Paid Plk σ.(hs_heap) →
  (∀ aid, faid (Some aid) = aid) →
  length v1 = length v2 →
  heap_state_invariant {|
    hs_heap := heap_update a v2 (mk_cell faid flk fep) σ.(hs_heap);
    hs_allocs := σ.(hs_allocs);
  |}.
Proof.
  move => [?[?[?[??]]]] ???. split_and!.
  - by eapply heap_update_heap_cell_in_range_alloc.
  - by eapply heap_update_heap_cell_alloc_alive.
  - move => *. naive_solver.
  - move => *. naive_solver.
  - by eapply heap_update_alloc_alive_in_heap.
Qed.

Lemma free_blocks_perm hs kind ls1 ls2 hs1 :
  ls1 ≡ₚ ls2 →
  heap_state_invariant hs →
  free_blocks hs kind ls1 hs1 →
  free_blocks hs kind ls2 hs1.
Proof.
  induction 1 as [ | ??? ? IH | [l1 ly1] [l2 ly2] ls | ??? ? IH1 ? IH2] in hs, hs1 |-*.
  - done.
  - intros ?. inversion 1; subst.
    econstructor; first done.
    eapply IH; last done.
    eapply free_block_invariant; done.
  - intros Hinv Ha.
    eapply free_blocks_inv_cons in Ha as (hs2 & Ha & Hb).
    eapply free_blocks_inv_cons in Hb as (hs3 & Hb & Hc).
    eapply free_block_inv in Ha as (aid1 & v1 & ? & Hal1 & Hlen1 & Hlook1 & ->).
    eapply free_block_inv in Hb as (aid2 & v2 & ? & Hal2 & Hlen2 & Hlook2 & ->).
    simpl in *.
    destruct (decide (aid1 = aid2)) as [<- | Hneq].
    { (* contradiction *) move: Hal2. rewrite lookup_insert_eq. congruence. }
    rewrite lookup_insert_ne in Hal2; last done.
    econstructor.
    { econstructor; try done.
      apply heap_lookup_loc_heap_free_disj_allocs in Hlook2; first done.
      destruct Hinv as (_ & _ & _ & Hdisj & _).
      ospecialize (Hdisj aid1 aid2 _ _ _ _ _ _ _); [done.. | by eexists | by eexists | ].
      rewrite elem_of_disjoint in Hdisj. simpl in Hdisj.
      unfold elem_of, elem_of_alloc, al_end in Hdisj. simpl in Hdisj.
      rewrite Hlen2.
      intros a []. apply dec_stable.
      intros ?%Decidable.not_or.
      eapply (Hdisj a); lia. }
    econstructor.
    { econstructor; try done.
      { simpl. rewrite lookup_insert_ne; last done. done. }
      simpl.
      apply heap_lookup_loc_heap_free_disj_allocs; last done.
      destruct Hinv as (_ & _ & _ & Hdisj & _).
      ospecialize (Hdisj aid1 aid2 _ _ _ _ _ _ _); [done.. | by eexists | by eexists | ].
      rewrite elem_of_disjoint in Hdisj. simpl in Hdisj.
      unfold elem_of, elem_of_alloc, al_end in Hdisj. simpl in Hdisj.
      rewrite Hlen1.
      intros a []. apply dec_stable.
      intros ?%Decidable.not_or.
      eapply (Hdisj a); lia. }
    simpl.
    rewrite insert_insert_ne; last done.
    rewrite heap_free_comm.
    done.
  - intros ? Ha. eapply IH2; first done.
    eapply IH1; done.
Qed.
