From caesium Require Export base byte layout int_type loc struct.
Set Default Proof Using "Type".

(** * Bytes and values stored in memory *)

(** Representation of a byte stored in memory. *)
Inductive mbyte : Set :=
| MByte (b : byte)
| MPtrFrag (l : loc) (n : nat) (** Fragment [n] for location [l]. *)
| MPoison.

#[export] Instance mbyte_dec_eq : EqDecision mbyte.
Proof. solve_decision. Qed.

Program Definition mbyte_to_byte (mb : mbyte) : option (byte * option alloc_id) :=
  match mb with
  | MByte b => Some (b, None)
  | MPtrFrag l n => Some (
     {| byte_val := ((l.(loc_a) `div` 2^(8 * n)) `mod` byte_modulus) |},
     if l.(loc_p) is ProvAlloc a then Some a else None)
  | MPoison => None
  end.
Next Obligation. move => ? l n. have [] := Z_mod_lt (l.(loc_a) `div` 2 ^ (8 * n)) byte_modulus => //*. lia. Qed.

(** Representation of a value (list of bytes). *)
Definition val : Set := list mbyte.
Bind Scope val_scope with val.

(** void is the empty list *)
Definition VOID : val := [].

(** Predicate stating that value [v] has the right size according to layout [ly]. *)
Definition has_layout_val (v : val) (ly : layout) : Prop := length v = ly.(ly_size).
Notation "v `has_layout_val` n" := (has_layout_val v n) (at level 50) : stdpp_scope.
Arguments has_layout_val : simpl never.
Global Typeclasses Opaque has_layout_val.

(** ** Conversion to and from locations. *)
(* rev because we do little endian *)
Definition val_of_loc_n (n : nat) (l : loc) : val :=
  MPtrFrag l <$> rev (seq 0 n).

Definition val_of_loc : loc → val :=
  val_of_loc_n bytes_per_addr.

Definition val_to_loc_n (n : nat) (v : val) : option loc :=
  if v is MPtrFrag l _ :: _ then
    if (bool_decide (v = val_of_loc_n n l)) then Some l else None
  else None.

Definition val_to_loc : val → option loc :=
  val_to_loc_n bytes_per_addr.

Definition NULL : val := val_of_loc NULL_loc.
Global Typeclasses Opaque NULL.

Lemma val_of_loc_n_length n l:
  length (val_of_loc_n n l) = n.
Proof.
  by rewrite /val_of_loc_n length_fmap length_rev length_seq.
Qed.

Lemma val_to_of_loc_n n l:
  n ≠ 0%nat →
  val_to_loc_n n (val_of_loc_n n l) = Some l.
Proof.
  destruct n as [|n]; first done.
  rewrite /val_of_loc_n seq_S rev_unit /= bool_decide_true //.
  by rewrite /val_of_loc_n seq_S rev_unit.
Qed.

Lemma val_to_of_loc l:
  val_to_loc (val_of_loc l) = Some l.
Proof.
  by apply val_to_of_loc_n.
Qed.

Lemma val_of_to_loc_n n v l:
  val_to_loc_n n v = Some l → v = val_of_loc_n n l.
Proof.
  rewrite /val_to_loc_n.
  destruct v as [|b v'] eqn:Hv; first done.
  repeat case_match => //; case_bool_decide; naive_solver.
Qed.

Lemma val_of_to_loc v l:
  val_to_loc v = Some l → v = val_of_loc l.
Proof. apply val_of_to_loc_n. Qed.

Lemma val_to_loc_n_length n v:
  is_Some (val_to_loc_n n v) → length v = n.
Proof.
  rewrite /val_to_loc_n. move => [? H]. repeat case_match => //; simplify_eq.
  revert select (bool_decide _ = _) => /bool_decide_eq_true ->.
  by rewrite val_of_loc_n_length.
Qed.

Lemma val_to_loc_length v:
  is_Some (val_to_loc v) → length v = bytes_per_addr.
Proof. apply val_to_loc_n_length. Qed.

Global Instance val_of_loc_inj : Inj (=) (=) val_of_loc.
Proof. move => x y Heq. have := val_to_of_loc x. have := val_to_of_loc y. rewrite Heq. by simplify_eq. Qed.

Global Typeclasses Opaque val_of_loc_n val_to_loc_n val_of_loc val_to_loc.
Arguments val_of_loc : simpl never.
Arguments val_to_loc : simpl never.

Global Typeclasses Opaque val_of_loc val_to_loc.
Arguments val_of_loc : simpl never.
Arguments val_to_loc : simpl never.

(** ** Conversion to and from mathematical integers. *)

(* TODO: we currently assume little-endian, make this more generic. *)

Fixpoint val_to_Z_go v : option Z :=
  match v with
  | []           => Some 0
  | MByte b :: v => z ← val_to_Z_go v; Some (byte_modulus * z + b.(byte_val))
  | _            => None
  end.

Definition val_to_Z (v : val) (it : int_type) : option Z :=
  if bool_decide (length v = bytes_per_int it) then
    z ← val_to_Z_go v;
    if it_signed it && bool_decide (int_half_modulus it ≤ z) then
      Some (z - int_modulus it)
    else
      Some z
  else None.

Definition val_to_bytes (v : val) : option val :=
  mapM (λ b, (λ '(v, a), MByte v) <$> mbyte_to_byte b) v.

Program Fixpoint val_of_Z_go (n : Z) (sz : nat) : val :=
  match sz return _ with
  | O    => []
  | S sz => MByte {| byte_val := (n `mod` byte_modulus) |}
            :: val_of_Z_go (n / byte_modulus) sz
  end.
Next Obligation. move => n. have [] := Z_mod_lt n byte_modulus => //*. lia. Qed.

Definition val_of_Z (z : Z) (it : int_type) : option val :=
  if bool_decide (z ∈ it) then
    let n := if bool_decide (z < 0) then z + int_modulus it else z in
    Some (val_of_Z_go n (bytes_per_int it))
  else
    None.

Definition i2v (n : Z) (it : int_type) : val :=
  default (replicate (bytes_per_int it) MPoison) (val_of_Z n it).

Lemma val_of_Z_go_length z sz :
  length (val_of_Z_go z sz) = sz.
Proof. elim: sz z => //= ? IH ?. by f_equal. Qed.

Lemma val_to_of_Z_go z (sz : nat):
  0 ≤ z < 2 ^ (sz * bits_per_byte) →
  val_to_Z_go (val_of_Z_go z sz) = Some z.
Proof.
  rewrite /bits_per_byte.
  elim: sz z => /=. 1: rewrite /Z.of_nat; move => ??; f_equal; lia.
  move => sz IH z [? Hlt]. rewrite IH /byte_modulus /= -?Z_div_mod_eq_full //.
  split; [by apply Z_div_pos|]. apply Zdiv_lt_upper_bound => //.
  rewrite Nat2Z.inj_succ -Zmult_succ_l_reverse Z.pow_add_r // in Hlt.
  lia.
Qed.

Lemma val_of_Z_length z it v :
  val_of_Z z it = Some v → length v = bytes_per_int it.
Proof.
  rewrite /val_of_Z => Hv. case_bool_decide => //. simplify_eq.
  by rewrite val_of_Z_go_length.
Qed.

Lemma i2v_length n it: length (i2v n it) = bytes_per_int it.
Proof.
  rewrite /i2v. destruct (val_of_Z n it) eqn:Heq.
  - by apply val_of_Z_length in Heq.
  - by rewrite length_replicate.
Qed.

Lemma val_to_Z_length v it z:
  val_to_Z v it = Some z → length v = bytes_per_int it.
Proof. rewrite /val_to_Z. by case_decide. Qed.

Lemma val_of_Z_is_Some it z:
  z ∈ it → is_Some (val_of_Z z it).
Proof. rewrite /val_of_Z. case_bool_decide; by eauto. Qed.

Lemma val_of_Z_in_range it z v :
  val_of_Z z it = Some v → z ∈ it.
Proof. rewrite /val_of_Z. case_bool_decide; by eauto. Qed.

Lemma val_to_Z_go_in_range v n:
  val_to_Z_go v = Some n → 0 ≤ n < 2 ^ (length v * bits_per_byte).
Proof.
  elim: v n => /=.
  - move => n [] <-. split; first lia.
    apply Z.pow_pos_nonneg; lia.
  - move => ? v IH n. case_match => //.
    destruct (val_to_Z_go v) => /=; last done.
    move => [] <-. move: (IH z eq_refl).
    move: (byte_constr b). rewrite /byte_modulus /bits_per_byte.
    move => [??] [??]. split; first lia.
    have ->: S (length v) * 8 = 8 + length v * 8 by lia.
    rewrite Z.pow_add_r; lia.
Qed.

Lemma val_to_Z_in_range v it n:
  val_to_Z v it = Some n → n ∈ it.
Proof.
  rewrite /val_to_Z. case_decide as Hlen; last done.
  destruct (val_to_Z_go v) eqn:Heq => /=; last done.
  move: Heq => /val_to_Z_go_in_range.
  rewrite int_elem_of_it_iff.
  rewrite Hlen /max_int /min_int.
  rewrite /int_half_modulus /int_modulus /bits_per_int.
  destruct (it_signed it) eqn:Hsigned => /=.
  - case_decide => /=.
    + move => [??] [] ?. simplify_eq.
      assert (2 ^ (bytes_per_int it * bits_per_byte) =
              2 * 2 ^ (bytes_per_int it * bits_per_byte - 1)) as Heq.
      { rewrite Z.sub_1_r. rewrite Z.pow_pred_r => //. rewrite /bits_per_byte.
        have ? := bytes_per_int_gt_0 it. lia. }
      rewrite Heq. lia.
    + move => [??] [] ?. lia.
  - move => [??] [] ?. lia.
Qed.

Lemma val_to_Z_unsigned_nonneg v z it :
  it_signed it = false →
  val_to_Z v it = Some z →
  (0 ≤ z)%Z.
Proof.
  rewrite /val_to_Z.
  case_bool_decide; last done.
  intros Hs Hv.
  apply bind_Some in Hv as (z' & Hz & Ha).
  apply val_to_Z_go_in_range in Hz.
  rewrite Hs in Ha. simpl in Ha. simplify_eq.
  lia.
Qed.

Lemma val_to_of_Z z it v :
  val_of_Z z it = Some v → val_to_Z v it = Some z.
Proof.
  rewrite /val_of_Z /val_to_Z => Ht.
  destruct (bool_decide (z ∈ it)) eqn: Hr => //. simplify_eq.
  move: Hr => /bool_decide_eq_true[Hm HM].
  have Hlen := bytes_per_int_gt_0 it.
  rewrite MaxInt_eq /max_int in HM. rewrite MinInt_eq /min_int in Hm.
  rewrite val_of_Z_go_length val_to_of_Z_go /=.
  - case_bool_decide as H => //. clear H.
    destruct (it_signed it) eqn:Hs => /=.
    + case_decide => /=; last (rewrite bool_decide_false //; lia).
      rewrite bool_decide_true; [f_equal; lia|].
      rewrite int_modulus_twice_half_modulus. move: Hm HM.
      generalize (int_half_modulus it). move => n Hm HM. lia.
    + rewrite bool_decide_false //. lia.
  - case_bool_decide as Hneg; case_match; split; try lia.
    + rewrite int_modulus_twice_half_modulus. lia.
    + rewrite /int_modulus /bits_per_int. lia.
    + rewrite /int_half_modulus in HM.
      transitivity (2 ^ (bits_per_int it -1)); first lia.
      rewrite /bits_per_int /bytes_per_int /bits_per_byte /=.
      apply Z.pow_lt_mono_r; try lia.
    + rewrite /int_modulus /bits_per_int in HM. lia.
Qed.

Lemma val_to_Z_go_is_Some v :
  Forall (λ mb, match mb with | MByte b => True | _ => False end) v ↔
  is_Some (val_to_Z_go v).
Proof.
  induction v as [ | mb v IH]; simpl; first by eauto.
  rewrite Forall_cons. rewrite IH.
  destruct mb; try naive_solver.
  destruct (val_to_Z_go v); naive_solver.
Qed.
Lemma val_to_Z_is_Some v it :
  (Forall (λ mb, match mb with | MByte b => True | _ => False end) v ∧ length v = bytes_per_int it) ↔
  is_Some (val_to_Z v it).
Proof.
  unfold val_to_Z. case_bool_decide; last naive_solver.
  split.
  - intros [Ha%val_to_Z_go_is_Some _].
    destruct Ha as (? & ->). simpl.
    case_match; try naive_solver.
  - intros Ha. split; last done.
    apply val_to_Z_go_is_Some. destruct (val_to_Z_go v); done.
Qed.
Lemma val_to_Z_Some v it x :
  val_to_Z v it = Some x →
  Forall (λ mb, match mb with | MByte b => True | _ => False end) v ∧ length v = bytes_per_int it.
Proof.
  intros Heq. apply val_to_Z_is_Some. rewrite Heq. done.
Qed.
Lemma val_to_Z_Some_1 v it :
  Forall (λ mb, match mb with | MByte b => True | _ => False end) v →
  length v = bytes_per_int it →
  is_Some (val_to_Z v it).
Proof.
  intros ??. by apply val_to_Z_is_Some.
Qed.

Lemma val_to_Z_val_of_loc_n_None n l it:
  val_to_Z (val_of_loc_n n l) it = None.
Proof.
  destruct n as [|n].
  - rewrite /val_of_loc_n /= /val_to_Z bool_decide_false //=.
    have ? := bytes_per_int_gt_0 it. lia.
  - rewrite /val_of_loc_n seq_S rev_app_distr /= /val_to_Z.
    by case_bool_decide.
Qed.

Lemma val_to_Z_val_of_loc_None l it:
  val_to_Z (val_of_loc l) it = None.
Proof. apply val_to_Z_val_of_loc_n_None. Qed.

Lemma val_of_Z_bool_is_Some it b:
  is_Some (val_of_Z (bool_to_Z b) it).
Proof. apply: val_of_Z_is_Some. apply: bool_to_Z_elem_of_int_type. Qed.

Lemma val_of_Z_bool b it:
  val_of_Z (bool_to_Z b) it = Some (i2v (bool_to_Z b) it).
Proof. rewrite /i2v. by have [? ->]:= val_of_Z_bool_is_Some it b. Qed.

Program Definition val_of_bool (b : bool) : val :=
  [MByte (Byte (bool_to_Z b) _)].
Next Obligation. by destruct b. Qed.

Definition val_to_bool (v : val) : option bool :=
  match v with
  | [MByte (Byte 0 _)] => Some false
  | [MByte (Byte 1 _)] => Some true
  | _                    => None
  end.

Lemma val_to_of_bool b :
  val_to_bool (val_of_bool b) = Some b.
Proof. by destruct b. Qed.

Lemma val_to_bool_length v b:
  val_to_bool v = Some b → length v = 1%nat.
Proof.
  rewrite /val_to_bool. repeat case_match => //.
Qed.

Lemma val_to_bool_iff_val_to_Z v b:
  val_to_bool v = Some b ↔ val_to_Z v U8 = Some (bool_to_Z b).
Proof.
  split.
  - destruct v as [|mb []] => //=; repeat case_match => //=; by move => [<-].
  - destruct v as [|mb []] => //=; repeat case_match => //=; destruct b => //.
Qed.

Lemma val_of_bool_iff_val_of_Z v b:
  val_of_bool b = v ↔ val_of_Z (bool_to_Z b) U8 = Some v.
Proof.
  destruct b.
  - rewrite /val_of_Z/val_of_bool. rewrite bool_decide_true.
    { cbv. split; intros ?; simplify_eq; do 2 f_equal; [f_equal | ]; by apply byte_eq. }
    rewrite int_elem_of_it_iff//.
  - rewrite /val_of_Z/val_of_bool. rewrite bool_decide_true.
    { cbv. split; intros ?; simplify_eq; do 2 f_equal; [f_equal | ]; by apply byte_eq. }
    rewrite int_elem_of_it_iff//.
Qed.

Lemma i2v_bool_Some b it:
  val_to_Z (i2v (bool_to_Z b) it) it = Some (bool_to_Z b).
Proof. apply: val_to_of_Z. apply val_of_Z_bool. Qed.

Lemma val_of_bool_i2v b :
  val_of_bool b = i2v (bool_to_Z b) U8.
Proof.
  apply val_of_bool_iff_val_of_Z.
  apply val_of_Z_bool.
Qed.

Definition val_to_Z_ot (v : val) (ot : op_type) : option Z :=
  match ot with
  | IntOp it => val_to_Z v it
  | BoolOp => bool_to_Z <$> val_to_bool v
  | PtrOp => loc_a <$> val_to_loc v
  | _ => None
  end.

Lemma val_to_Z_ot_length v ot z:
  val_to_Z_ot v ot = Some z → length v = (ot_layout ot).(ly_size).
Proof.
  destruct ot => //=.
  - by move => /fmap_Some[?[/val_to_bool_length -> ?]].
  - by move => /val_to_Z_length ->.
  - move => /fmap_Some[?[??]]. apply val_to_loc_length. by eexists.
Qed.

Lemma val_to_Z_ot_to_Z z it ot v:
  val_to_Z z it = Some v →
  match ot with | BoolOp => ∃ b, it = U8 ∧ v = bool_to_Z b | IntOp it' => it = it' | _ => False end →
  val_to_Z_ot z ot = Some v.
Proof.
  move => ? Hot. destruct ot => //; simplify_eq/= => //. move: Hot => [?[??]]. simplify_eq.
  apply fmap_Some. eexists _. split; [|done]. by apply val_to_bool_iff_val_to_Z.
Qed.

Definition val_to_char (v : val) : option Z :=
  z ← val_to_Z v CharIt;
  if decide (is_valid_char z) then Some z else None.
Definition val_of_char (z : Z) :=
  val_of_Z z CharIt.

Lemma val_to_char_length v z :
  val_to_char v = Some z → length v = 4%nat.
Proof.
  rewrite /val_to_char.
  intros (z' & Hv & Hvalid)%bind_Some.
  apply val_to_Z_length in Hv. done.
Qed.

Lemma val_to_bytes_id v it n:
  val_to_Z v it = Some n →
  val_to_bytes v = Some v.
Proof.
  rewrite /val_to_Z. case_bool_decide as Heq => // /bind_Some[z [Hgo _]]. clear Heq it.
  apply mapM_Some.
  elim: v z Hgo => //= b v IH z. case_match => // /bind_Some[? [? _]]; simplify_eq.
  constructor. 2: naive_solver. apply fmap_Some. naive_solver.
Qed.

Lemma val_to_bytes_id_bool v b:
  val_to_bool v = Some b →
  val_to_bytes v = Some v.
Proof.
  rewrite /val_to_bool. repeat case_match => //.
Qed.

Lemma val_to_bytes_id_char v z:
  val_to_char v = Some z →
  val_to_bytes v = Some v.
Proof.
  rewrite /val_to_char.
  destruct (val_to_Z v CharIt) eqn:Heq; last done.
  simpl. repeat case_match => //.
  intros [= ->].
  by eapply val_to_bytes_id.
Qed.

Lemma val_to_bytes_idemp v v' :
  val_to_bytes v = Some v' →
  val_to_bytes v' = Some v'.
Proof.
  intros Ha.
  induction v as [ | b v IH] in v', Ha |-*; simpl in Ha.
  { injection Ha. intros <-. done. }
  apply bind_Some in Ha as (mb & Ha & Hb).
  apply fmap_Some in Ha as ((bt & aid) & Ha & ->).
  apply bind_Some in Hb as (v'' & Hb & [= <-]).
  apply IH in Hb. simpl. rewrite Hb. simpl. done.
Qed.

Arguments val_to_Z : simpl never.
Arguments val_of_Z : simpl never.
Global Typeclasses Opaque val_to_Z val_of_Z val_to_char val_of_char val_of_bool val_to_bool val_to_bytes.
