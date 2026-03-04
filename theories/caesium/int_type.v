From caesium Require Import base byte layout.

(** Representation of an integer type (size and signedness). *)

Notation signed := bool (only parsing).

(* hardcoding 64bit pointers for now *)
Definition bytes_per_addr_log : nat := 3%nat.
Definition bytes_per_addr : nat := (2 ^ bytes_per_addr_log)%nat.

Definition void_ptr : layout := {| ly_size := bytes_per_addr; ly_align_log := bytes_per_addr_log |}.
Notation "'void*'" := (void_ptr).

(** We define a closed set of integer types that are allowed to appear as literals in the source code,
  in order to ensure that their size fits into [isize]. *)
Inductive int_type : Set :=
  | I8 | I16 | I32 | I64 | I128
  | U8 | U16 | U32 | U64 | U128
  | ISize | USize
  | CharIt
.
Global Instance int_type_dec : EqDecision int_type.
Proof. solve_decision. Defined.

Definition it_byte_size_log (it : int_type) : nat :=
  match it with
  | I8 => 0
  | U8 => 0
  | I16 => 1
  | U16 => 1
  | I32 => 2
  | U32 => 2
  | I64 => 3
  | U64 => 3
  | I128 => 4
  | U128 => 4
  | ISize => bytes_per_addr_log
  | USize => bytes_per_addr_log
  (* u32 *)
  | CharIt => 2
  end.
Definition it_signed (it : int_type) : signed :=
  match it with
  | I8 => true
  | U8 => false
  | I16 => true
  | U16 => false
  | I32 => true
  | U32 => false
  | I64 => true
  | U64 => false
  | I128 => true
  | U128 => false
  | ISize => true
  | USize => false
  | CharIt => false
  end.

Definition it_to_signed (it : int_type) : int_type :=
  match it with
  | U8 => I8
  | U16 => I16
  | U32 => I32
  | U64 => I64
  | U128 => I128
  | USize => ISize
  | CharIt => I32
  | _ => it
  end.
Definition it_to_unsigned (it : int_type) : int_type :=
  match it with
  | I8 => U8
  | I16 => U16
  | I32 => U32
  | I64 => U64
  | I128 => U128
  | ISize => USize
  | _ => it
  end.

Definition bytes_per_int (it : int_type) : nat :=
  2 ^ it_byte_size_log it.

Definition bits_per_int (it : int_type) : Z :=
  bytes_per_int it * bits_per_byte.

Definition int_modulus (it : int_type) : Z :=
  2 ^ bits_per_int it.

Definition int_half_modulus (it : int_type) : Z :=
  2 ^ (bits_per_int it - 1).

(* Minimal representable integer. *)
Definition min_int (it : int_type) : Z :=
  if it_signed it then - int_half_modulus it else 0.

(* Maximal representable integer. *)
Definition max_int (it : int_type) : Z :=
  (if it_signed it then int_half_modulus it else int_modulus it) - 1.

(* Sealed versions of [max_int] / [min_int] in order to avoid Coq from choking on things like [max_int usize_t] *)
Definition MaxInt_def (it : int_type) := max_int it.
Definition MaxInt_aux it : seal (MaxInt_def it). by eexists. Qed.
Definition MaxInt it := (MaxInt_aux it).(unseal).
Definition MaxInt_eq it : MaxInt it = max_int it := (MaxInt_aux it).(seal_eq).

Definition MinInt_def (it : int_type) := min_int it.
Definition MinInt_aux it : seal (MinInt_def it). by eexists. Qed.
Definition MinInt it := (MinInt_aux it).(unseal).
Definition MinInt_eq it : MinInt it = min_int it := (MinInt_aux it).(seal_eq).

Global Instance int_elem_of_it : ElemOf Z int_type := λ z it, (MinInt it ≤ z ≤ MaxInt it)%Z.
Lemma int_elem_of_it_iff z it :
  z ∈ it ↔ (min_int it ≤ z ≤ max_int it)%Z.
Proof.
  rewrite /elem_of/int_elem_of_it MinInt_eq MaxInt_eq//.
Qed.
Global Instance nat_elem_of_it : ElemOf nat int_type := λ z it, (MinInt it ≤ z ≤ MaxInt it)%Z.
Lemma nat_elem_of_it_iff (n : nat) it :
  n ∈ it ↔ (min_int it ≤ n ≤ max_int it)%Z.
Proof.
  rewrite /elem_of/nat_elem_of_it MinInt_eq MaxInt_eq//.
Qed.

Definition bool_layout : layout := {| ly_size := 1; ly_align_log := 0 |}.
Definition it_layout (it : int_type) : layout :=
  Layout (bytes_per_int it) (it_byte_size_log it).

Lemma it_size_bounded I :
  (ly_size (it_layout I) ≤ MaxInt ISize)%Z.
Proof.
  rewrite MaxInt_eq.
  destruct I; done.
Qed.

Lemma IntType_align_le it :
  ly_align (it_layout it) ≤ 16.
Proof.
  rewrite /it_layout /ly_align/ly_align_log/it_byte_size_log.
  destruct it => /=; lia.
Qed.
Lemma IntType_size_le it :
  ly_size (it_layout it) ≤ 16.
Proof.
  rewrite /it_layout /ly_size/bytes_per_int/it_byte_size_log.
  destruct it => /=; lia.
Qed.
Lemma IntType_size_ge_1 it :
  1 ≤ ly_size (it_layout it).
Proof.
  rewrite /it_layout /ly_size/bytes_per_int/it_byte_size_log.
  destruct it => /=; lia.
Qed.

(*** Lemmas about [int_type] *)
(* Radium uses 64-bit pointers *)
Lemma int_elem_of_u64_usize (x : Z) :
  x ∈ U64 ↔ x ∈ USize.
Proof.
  rewrite /elem_of/int_elem_of_it.
  rewrite !MinInt_eq !MaxInt_eq.
  done.
Qed.

Lemma MaxInt_signed_lt_unsigned it :
  (MaxInt (it_to_signed it) < MaxInt (it_to_unsigned it))%Z.
Proof.
  rewrite !MaxInt_eq.
  rewrite /max_int /int_half_modulus /int_modulus /= /bits_per_int /bytes_per_int /bits_per_byte /=.
  destruct it; simpl; lia.
Qed.
Lemma MaxInt_isize_lt_usize :
  (MaxInt ISize < MaxInt USize)%Z.
Proof.
  apply (MaxInt_signed_lt_unsigned ISize).
Qed.

Lemma bytes_per_int_usize :
  bytes_per_int USize = bytes_per_addr.
Proof. done. Qed.

Lemma bytes_per_int_gt_0 it : bytes_per_int it > 0.
Proof.
  rewrite /bytes_per_int.
  destruct it; simpl; lia.
Qed.

Lemma bits_per_int_gt_0 it : bits_per_int it > 0.
Proof.
  rewrite /bits_per_int /bits_per_byte.
  suff : (bytes_per_int it > 0) by lia.
  by apply: bytes_per_int_gt_0.
Qed.

Lemma int_modulus_twice_half_modulus (it : int_type) :
  int_modulus it = 2 * int_half_modulus it.
Proof.
  rewrite /int_modulus /int_half_modulus.
  rewrite -[X in X * _]Z.pow_1_r -Z.pow_add_r; try f_equal; try lia.
  rewrite /bits_per_int /bytes_per_int.
  apply Z.le_add_le_sub_l. rewrite Z.add_0_r.
  rewrite Z2Nat.inj_pow.
  assert (0 < 2%nat ^ it_byte_size_log it * bits_per_byte); last lia.
  apply Z.mul_pos_pos; last (rewrite /bits_per_byte; lia).
  apply Z.pow_pos_nonneg; lia.
Qed.

Lemma int_half_modulus_ge_1 it :
  1 ≤ int_half_modulus it.
Proof.
  rewrite /int_half_modulus.
  assert (0 ≤ bits_per_int it -1).
  { rewrite /bits_per_int /bytes_per_int.
    specialize (Nat_pow_ge_1 (it_byte_size_log it)) => ?.
    rewrite /bits_per_byte. nia. }
  nia.
Qed.
Lemma int_modulus_ge_1 it :
  1 ≤ int_modulus it.
Proof.
  rewrite int_modulus_twice_half_modulus. specialize (int_half_modulus_ge_1 it). lia.
Qed.

Lemma MinInt_le_0 (it : int_type) : MinInt it ≤ 0.
Proof.
  rewrite MinInt_eq.
  have ? := bytes_per_int_gt_0 it. rewrite /min_int /int_half_modulus.
  destruct (it_signed it) => //. trans (- 2 ^ 7) => //.
  rewrite -Z.opp_le_mono. apply Z.pow_le_mono_r => //.
  rewrite /bits_per_int /bits_per_byte. lia.
Qed.

Lemma MaxInt_ge_127 (it : int_type) : 127 ≤ MaxInt it.
Proof.
  rewrite MaxInt_eq.
  have ? := bytes_per_int_gt_0 it.
  rewrite /max_int /int_modulus /int_half_modulus.
  rewrite /bits_per_int /bits_per_byte.
  have ->: (127 = 2 ^ 7 - 1) by []. apply Z.sub_le_mono => //.
  destruct (it_signed it); apply Z.pow_le_mono_r; lia.
Qed.

Lemma int_modulus_mod_in_range n it:
  it_signed it = false →
  (n `mod` int_modulus it) ∈ it.
Proof.
  move => Hs.
  have [|??]:= Z.mod_pos_bound n (int_modulus it). {
    apply: Z.pow_pos_nonneg => //. rewrite /bits_per_int/bits_per_byte/=. lia.
  }
  rewrite int_elem_of_it_iff.
  unfold min_int, max_int => /=.
  rewrite /int_modulus/int_half_modulus Hs.
  specialize (bits_per_int_gt_0 it).
  split; lia.
Qed.

Lemma elem_of_int_type_0_to_127 (n : Z) (it : int_type):
  0 ≤ n ≤ 127 → n ∈ it.
Proof.
  move => [??].
  have ? := MinInt_le_0 it.
  have ? := MaxInt_ge_127 it.
  split; lia.
Qed.

Lemma MinInt_unsigned_0 it :
  it_signed it = false → MinInt it = 0.
Proof.
  rewrite MinInt_eq. destruct it; simpl; done.
Qed.
Lemma MinInt_le_n128_signed it :
  it_signed it = true → (MinInt it ≤ -128%Z)%Z.
Proof.
  rewrite MinInt_eq.
  rewrite /min_int/=/int_half_modulus/bits_per_int/bytes_per_int/bits_per_byte/=.
  intros ->.
  generalize (it_byte_size_log it) as sz.
  intros sz.

  induction sz; simpl; first lia.
  rewrite Nat.add_0_r.
  rewrite Nat2Z.inj_add.
  rewrite Z.mul_add_distr_r.
  rewrite -Z.add_sub_assoc.
  rewrite Z.pow_add_r.
  - lia.
  - nia.
  - clear. induction sz; simpl; lia.
Qed.

Lemma bool_to_Z_elem_of_int_type (b : bool) (it : int_type):
  bool_to_Z b ∈ it.
Proof.
  apply elem_of_int_type_0_to_127.
  destruct b => /=; lia.
Qed.

Lemma int_type_layout_wf (it : int_type) :
  layout_wf (it_layout it).
Proof.
  rewrite /layout_wf //.
Qed.
Lemma ptr_layout_wf :
  layout_wf void*.
Proof.
  rewrite /layout_wf //.
Qed.

Definition wrap_unsigned (z : Z) (it : int_type) : Z :=
  z `mod` (int_modulus it).
Definition wrap_signed (z : Z) (it : int_type) : Z :=
  ((z + int_half_modulus it) `mod` (int_modulus it)) - int_half_modulus it.
Definition wrap_to_it (z : Z) (it : int_type) : Z :=
  if it_signed it then wrap_signed z it else wrap_unsigned z it.

(** wrap_unsigned lemmas *)
Lemma wrap_unsigned_id z it :
  it_signed it = false → z ∈ it → wrap_unsigned z it = z.
Proof.
  rewrite int_elem_of_it_iff.
  (*destruct it; simpl. intros -> [].*)
  unfold min_int, max_int in *. simpl in*.
  intros -> ?.
  rewrite /wrap_unsigned/=; rewrite Zmod_small; lia.
Qed.

Lemma wrap_unsigned_in_range z it :
  it_signed it = false → wrap_unsigned z it ∈ it.
Proof.
  opose proof* (Z_mod_lt (z) (int_modulus it)).
  { specialize (int_modulus_ge_1 it). lia. }
  rewrite int_elem_of_it_iff.
  unfold min_int, max_int; simpl.
  intros ->. rewrite /wrap_unsigned. lia.
Qed.

Lemma wrap_unsigned_add_l it n1 n2 :
  wrap_unsigned (wrap_unsigned n1 it + n2) it = wrap_unsigned (n1 + n2) it.
Proof.
  rewrite /wrap_unsigned.
  rewrite Z.add_mod_idemp_l; first done.
  unfold int_modulus.
  intros Heq%Z.pow_eq_0; first done.
  specialize (bits_per_int_gt_0 it).
  lia.
Qed.

Lemma wrap_unsigned_add_did_not_wrap it a b :
  it_signed it = false →
  a ∈ it →
  b ∈ it →
  ¬ (wrap_unsigned (a + b) it < a) →
  wrap_unsigned (a + b) it = a + b.
Proof.
  intros Hs [Ha1 Hb1] [Ha2 Hb2].
  rewrite MaxInt_eq/max_int Hs in Hb1, Hb2.
  rewrite MinInt_unsigned_0 in Ha1, Ha2; last done.

  destruct (decide (a + b ∈ it)) as [Hel | Hnel].
  { by rewrite wrap_unsigned_id. }
  intros Hno_overflow.
  destruct (decide (a + b > int_modulus it - 1)) as [Hoverflow | Hcontra]; first last.
  { (* contradiction *)
    contradict Hnel.
    split.
    - rewrite MinInt_unsigned_0; last done. lia.
    - rewrite MaxInt_eq/max_int Hs. lia. }
  contradict Hno_overflow.
  rewrite /wrap_unsigned.
  erewrite (Z.mod_in_range 1); lia.
Qed.

Lemma wrap_unsigned_add_did_wrap it a b :
  it_signed it = false →
  a ∈ it →
  b ∈ it →
  0 < b →
  wrap_unsigned (a + b) it ≤ a →
  a + b ∉ it.
Proof.
  intros Hs [Ha1 Hb1] [Ha2 Hb2] ? Hoverflow [Ha Hb].
  rewrite MaxInt_eq/max_int Hs in Hb1, Hb2, Hb.
  rewrite MinInt_unsigned_0 in Ha1, Ha2, Ha; last done.
  move: Hoverflow.

  rewrite /wrap_unsigned.
  erewrite (Z.mod_in_range 0); lia.
Qed.

Lemma wrap_unsigned_le a it :
  0 ≤ a →
  wrap_unsigned a it ≤ a.
Proof.
  unfold wrap_unsigned.
  intros. apply Z.mod_le; first done.
  rewrite /int_modulus.
  apply Z.pow_pos_nonneg; first done.
  specialize (bits_per_int_gt_0 it). lia.
Qed.

(** wrap_signed lemmas *)
Lemma wrap_signed_id z it :
  it_signed it = true → z ∈ it → wrap_signed z it = z.
Proof.
  specialize (int_modulus_twice_half_modulus it) as ?.
  rewrite int_elem_of_it_iff.
  unfold min_int, max_int in *. simpl in*.
  intros -> [].
  rewrite /wrap_signed/=; rewrite Zmod_small; lia.
Qed.

Lemma wrap_signed_in_range z it :
  it_signed it = true → wrap_signed z it ∈ it.
Proof.
  specialize (int_modulus_twice_half_modulus it) as ?.
  opose proof* (Z_mod_lt (z + int_half_modulus it) (int_modulus it)).
  { specialize (int_modulus_ge_1 it). lia. }
  rewrite int_elem_of_it_iff.
  unfold min_int, max_int in *.
  intros ->.
  rewrite /wrap_signed. simpl in *. lia.
Qed.

(** wrap_to_it lemmas *)
Lemma wrap_to_it_id z it :
  z ∈ it → wrap_to_it z it = z.
Proof.
  unfold wrap_to_it.
  destruct (it_signed it) eqn:Heq.
  - intros; by eapply wrap_signed_id.
  - intros; by eapply wrap_unsigned_id.
Qed.

Lemma wrap_to_it_in_range z it :
  wrap_to_it z it ∈ it.
Proof.
  unfold wrap_to_it.
  destruct (it_signed it) eqn:Heq.
  - by eapply wrap_signed_in_range.
  - by eapply wrap_unsigned_in_range.
Qed.
