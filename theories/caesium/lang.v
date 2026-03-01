From iris.program_logic Require Export language ectx_language ectxi_language.
From stdpp Require Export strings.
From stdpp Require Import gmap list.
From caesium Require Export base byte layout int_type loc val heap struct.
Set Default Proof Using "Type".

(** * Definition of the language *)

Definition label := string.

(* see http://compcert.inria.fr/doc/html/compcert.cfrontend.Cop.html#binary_operation *)
Inductive bin_op : Set :=
| AddOp | SubOp | MulOp | DivOp | ModOp | AndOp | OrOp | XorOp | ShlOp
| ShrOp | EqOp (rit : int_type) | NeOp (rit : int_type) | LtOp (rit : int_type)
| GtOp (rit : int_type) | LeOp (rit : int_type) | GeOp (rit : int_type) | Comma
(* Ptr is the second argument and offset the first *)
| PtrOffsetOp (ly : layout) | PtrNegOffsetOp (ly : layout)
| PtrWrappingOffsetOp (ly : layout) | PtrWrappingNegOffsetOp (ly : layout)
| PtrDiffOp (ly : layout)
(* Unchecked operations that trigger UB on overflows *)
| UncheckedAddOp | UncheckedSubOp | UncheckedMulOp
.

Inductive un_op : Set :=
| NotBoolOp | NotIntOp | NegOp | CastOp (ot : op_type).

Inductive order : Set :=
| ScOrd | Na1Ord | Na2Ord.

Inductive atomic_rmw_op : Set :=
  | RmwXchg
  | RmwAdd | RmwSub
  | RmwAnd | RmwOr | RmwXor | RmwNand
  | RmwMaxS | RmwMinS
  | RmwMaxU | RmwMinU.

Section expr.
Local Unset Elimination Schemes.
Inductive expr :=
| Var (x : var_name)
| Val (v : val)
(* operators which wrap into the target type *)
| UnOp (op : un_op) (ot : op_type) (e : expr)
| BinOp (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : expr)
(* operators for checking whether an operation would overflow *)
| CheckUnOp (op : un_op) (ot : op_type) (e : expr)
| CheckBinOp (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : expr)
| CopyAllocId (ot1 : op_type) (e1 : expr) (e2 : expr)
| Deref (o : order) (ot : op_type) (memcast : bool) (e : expr)
| CAS (ot : op_type) (e1 e2 e3 : expr)
| AtomicRMW (op : atomic_rmw_op) (ot : op_type) (e1 e2 : expr)
| Call (f : expr) (args : list expr)
| Concat (es : list expr)
| IfE (ot : op_type) (e1 e2 e3 : expr)
(* [e_align] is the 2-logarithm of the desired alignment *)
| Alloc (e_size : expr) (e_align : expr)
| SkipE (e : expr)
| StuckE (* stuck expression *)
.
End expr.
Arguments Call _%_E _%_E.
Lemma expr_ind (P : expr → Prop) :
  (∀ (x : var_name), P (Var x)) →
  (∀ (v : val), P (Val v)) →
  (∀ (op : un_op) (ot : op_type) (e : expr), P e → P (UnOp op ot e)) →
  (∀ (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : expr), P e1 → P e2 → P (BinOp op ot1 ot2 e1 e2)) →
  (∀ (op : un_op) (ot : op_type) (e : expr), P e → P (CheckUnOp op ot e)) →
  (∀ (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : expr), P e1 → P e2 → P (CheckBinOp op ot1 ot2 e1 e2)) →
  (∀ (ot1 : op_type) (e1 e2 : expr), P e1 → P e2 → P (CopyAllocId ot1 e1 e2)) →
  (∀ (o : order) (ot : op_type) (memcast : bool) (e : expr), P e → P (Deref o ot memcast e)) →
  (∀ (ot : op_type) (e1 e2 e3 : expr), P e1 → P e2 → P e3 → P (CAS ot e1 e2 e3)) →
  (∀ (op : atomic_rmw_op) (ot : op_type) (e1 e2 : expr), P e1 → P e2 → P (AtomicRMW op ot e1 e2)) →
  (∀ (f : expr) (args : list expr), P f → Forall P args → P (Call f args)) →
  (∀ (es : list expr), Forall P es → P (Concat es)) →
  (∀ (ot : op_type) (e1 e2 e3 : expr), P e1 → P e2 → P e3 → P (IfE ot e1 e2 e3)) →
  (∀ (e_size : expr) (e_align : expr), P e_size → P e_align → P (Alloc e_size e_align)) →
  (∀ (e : expr), P e → P (SkipE e)) →
  (P StuckE) →
  ∀ (e : expr), P e.
Proof.
  move => *. generalize dependent P => P. match goal with | e : expr |- _ => revert e end.
  fix FIX 1. move => [ ^e] => ?????????? Hcall Hconcat *.
  11: { apply Hcall; [ |apply Forall_true => ?]; by apply: FIX. }
  11: { apply Hconcat. apply Forall_true => ?. by apply: FIX. }
  all: auto.
Qed.

Global Instance val_inj : Inj (=) (=) Val.
Proof. by move => ?? [->]. Qed.

(** Note that there is no explicit Fork. Instead the initial state can
contain multiple threads (like a processor which has a fixed number of
hardware threads). *)
Inductive stmt :=
| Goto (b : label)
| Return (e : expr)
(* join : label of the join point, only for informational purposes *)
| IfS (ot : op_type) (join : option label) (e : expr) (s1 s2 : stmt)
(* m: map from values of e to indices into bs, def: default *)
| Switch (it : int_type) (e : expr) (m : gmap Z nat) (bs : list stmt) (def : stmt)
| Assign (o : order) (ot : op_type) (e1 e2 : expr) (s : stmt)
(* [e_align] is the 2-logarithm of the allocation's alignment *)
| Free (e_size : expr) (e_align : expr) (e : expr) (s : stmt)
| SkipS (s : stmt)
| StuckS (* stuck statement *)
| ExprS (e : expr) (s : stmt)
| LocalLive (x : var_name) (ly : layout) (s : stmt)
| LocalDead (x : var_name) (s : stmt)
.

Arguments Switch _%_E _%_E _%_E.

Record function := {
  f_args : list (var_name * layout);
  f_code : gmap label stmt;
  f_init : label;
  f_args_nodup : NoDup f_args.*1;
}.

Definition thread_id := nat.
Record call_frame := {
  cf_locals : gmap var_name (loc * layout);
}.
Record thread_state := {
  ts_frames : list call_frame;
}.


Definition pop_frame (ts : thread_state) : thread_state :=
  {| ts_frames := tail ts.(ts_frames) |}.

Definition thread_get_frame (ts : thread_state) : option call_frame :=
  head ts.(ts_frames).

Definition frame_alloc_var (cf : call_frame) (x : var_name) (l : loc) (ly : layout) : call_frame :=
  {| cf_locals := <[x := (l, ly)]> cf.(cf_locals) |}.
Definition frame_alloc_vars (cf : call_frame) (args : list (var_name * layout)) (ls : list loc) : call_frame :=
  List.fold_right (λ '((x, ly), l) cf, frame_alloc_var cf x l ly) cf (zip args ls).

Definition frame_dealloc_var (cf : call_frame) (x : var_name) : call_frame :=
  {| cf_locals := delete x cf.(cf_locals) |}.
Definition frame_dealloc_vars (cf : call_frame) (xs : list var_name) : call_frame :=
  List.fold_right (λ x cf, frame_dealloc_var cf x) cf xs.

Definition thread_push_frame (ts : thread_state) (cf : call_frame) : thread_state :=
  {| ts_frames := cf :: ts.(ts_frames) |}.
Definition thread_update_frame (ts : thread_state) (cf : call_frame) : thread_state :=
  {| ts_frames := cf :: tail ts.(ts_frames) |}.

Definition empty_frame : call_frame := {| cf_locals := ∅ |}.
Definition initialize_new_frame (args : list (string * layout)) (lsa : list loc) : call_frame :=
  frame_alloc_vars empty_frame args lsa.

(* TODO: put both function and bytes in the same heap or make pointers disjoint *)
Record state := {
  st_heap: heap_state;
  st_fntbl: gmap addr function;
  (* thread-local state *)
  st_thread : gmap thread_id thread_state;
}.

Definition state_get_thread (σ : state) (π : thread_id) : option thread_state :=
  σ.(st_thread) !! π.

Definition heap_fmap (f : heap → heap) (σ : state) := {|
  st_heap := {| hs_heap := f σ.(st_heap).(hs_heap); hs_allocs := σ.(st_heap).(hs_allocs) |};
  st_fntbl := σ.(st_fntbl);
  st_thread := σ.(st_thread);
|}.

Inductive runtime_expr :=
(* separate from [Expr], as we need to define [of_val] *)
| RTVal (v : val)
| Expr (π : thread_id) (e : rtexpr)
| Stmt (π : thread_id) (rf : function) (s : rtstmt)
| AllocFailed
with rtexpr :=
| RTVar (x : var_name)
| RTUnOp (op : un_op) (ot : op_type) (e : runtime_expr)
| RTBinOp (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : runtime_expr)
| RTCheckUnOp (op : un_op) (ot : op_type) (e : runtime_expr)
| RTCheckBinOp (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : runtime_expr)
| RTCopyAllocId (ot1 : op_type) (e1 : runtime_expr) (e2 : runtime_expr)
| RTDeref (o : order) (ot : op_type) (memcast : bool) (e : runtime_expr)
| RTCall (f : runtime_expr) (args : list runtime_expr)
| RTCAS (ot : op_type) (e1 e2 e3 : runtime_expr)
| RTAtomicRMW (op : atomic_rmw_op) (ot : op_type) (e1 e2 : runtime_expr)
| RTConcat (es : list runtime_expr)
| RTAlloc (e_size : runtime_expr) (e_align : runtime_expr)
| RTIfE (ot : op_type) (e1 e2 e3 : runtime_expr)
| RTSkipE (e : runtime_expr)
| RTStuckE
with rtstmt :=
| RTGoto (b : label)
| RTReturn (e : runtime_expr)
| RTIfS (ot : op_type) (join : option label) (e : runtime_expr) (s1 s2 : stmt)
| RTSwitch (it : int_type) (e : runtime_expr) (m : gmap Z nat) (bs : list stmt) (def : stmt)
| RTAssign (o : order) (ot : op_type) (e1 e2 : runtime_expr) (s : stmt)
| RTFree (e_size : runtime_expr) (e_align : runtime_expr) (e : runtime_expr) (s : stmt)
| RTSkipS (s : stmt)
| RTStuckS
| RTExprS (e : runtime_expr) (s : stmt)
| RTLocalLive (x : var_name) (ly : layout) (s : stmt)
| RTLocalDead (x : var_name) (s : stmt)
.

Definition to_val (e : runtime_expr) : option val :=
  match e with
  | RTVal v => Some v
  | _ => None
  end.
Definition of_val (v : val) : runtime_expr := RTVal v.

Fixpoint to_rtexpr (π : thread_id) (e : expr) : runtime_expr :=
  match e with
  | Var x => Expr π $ RTVar x
  | Val v => RTVal v
  | UnOp op ot e => Expr π $ RTUnOp op ot (to_rtexpr π e)
  | BinOp op ot1 ot2 e1 e2 => Expr π $ RTBinOp op ot1 ot2 (to_rtexpr π e1) (to_rtexpr π e2)
  | CheckUnOp op ot e => Expr π $ RTCheckUnOp op ot (to_rtexpr π e)
  | CheckBinOp op ot1 ot2 e1 e2 => Expr π $ RTCheckBinOp op ot1 ot2 (to_rtexpr π e1) (to_rtexpr π e2)
  | CopyAllocId ot1 e1 e2 => Expr π $ RTCopyAllocId ot1 (to_rtexpr π e1) (to_rtexpr π e2)
  | Deref o ot mc e => Expr π $ RTDeref o ot mc (to_rtexpr π e)
  | Call f args => Expr π $ RTCall (to_rtexpr π f) (to_rtexpr π <$> args)
  | CAS ot e1 e2 e3 => Expr π $ RTCAS ot (to_rtexpr π e1) (to_rtexpr π e2) (to_rtexpr π e3)
  | AtomicRMW op ot e1 e2 => Expr π $ RTAtomicRMW op ot (to_rtexpr π e1) (to_rtexpr π e2)
  | Concat es => Expr π $ RTConcat (to_rtexpr π <$> es)
  | IfE ot e1 e2 e3 => Expr π $ RTIfE ot (to_rtexpr π e1) (to_rtexpr π e2) (to_rtexpr π e3)
  | Alloc e_size e_align => Expr π $ RTAlloc (to_rtexpr π e_size) (to_rtexpr π e_align)
  | SkipE e => Expr π $ RTSkipE (to_rtexpr π e)
  | StuckE => Expr π $ RTStuckE
  end.
Definition to_rtstmt (π : thread_id) (f : function) (s : stmt) : runtime_expr :=
  Stmt π f $ match s with
  | Goto b => RTGoto b
  | Return e => RTReturn (to_rtexpr π e)
  | IfS ot join e s1 s2 => RTIfS ot join (to_rtexpr π e) s1 s2
  | Switch it e m bs def => RTSwitch it (to_rtexpr π e) m bs def
  | Assign o ot e1 e2 s => RTAssign o ot (to_rtexpr π e1) (to_rtexpr π e2) s
  | Free e_size e_align e s => RTFree (to_rtexpr π e_size) (to_rtexpr π e_align) (to_rtexpr π e) s
  | SkipS s => RTSkipS s
  | StuckS => RTStuckS
  | ExprS e s => RTExprS (to_rtexpr π e) s
  | LocalLive x ly s => RTLocalLive x ly s
  | LocalDead x s => RTLocalDead x s
  end.

Lemma to_rtexpr_inj' π1 π2 e1 e2 :
  to_rtexpr π1 e1 = to_rtexpr π2 e2 → e1 = e2.
Proof.
  induction e1 in e2 |-*; destruct e2; try done.
  all: simpl; intros ?; simplify_eq.
  all: try naive_solver.
  - f_equal; [naive_solver|].
    generalize dependent args0.
    revert select (Forall _ _). elim; [by case|].
    move => ????? [|??]//. naive_solver.
  - generalize dependent es0.
    revert select (Forall _ _). elim; [by case|].
    move => ????? [|??]//. naive_solver.
Qed.
Lemma to_rtexpr_inj_strong_1 π1 π2 e1 e2 :
  to_val (to_rtexpr π1 e1) = None →
  to_rtexpr π1 e1 = to_rtexpr π2 e2 → π1 = π2 ∧ e1 = e2.
Proof.
  intros Hv Heq. split; last by eapply to_rtexpr_inj'.
  destruct e1, e2; try done.
  all: simplify_eq; done.
Qed.
Lemma to_rtexpr_inj_strong_2 π1 π2 e1 e2 :
  to_val (to_rtexpr π2 e2) = None →
  to_rtexpr π1 e1 = to_rtexpr π2 e2 → π1 = π2 ∧ e1 = e2.
Proof.
  intros Hv Heq. split; last by eapply to_rtexpr_inj'.
  destruct e1, e2; try done.
  all: simplify_eq; done.
Qed.

Global Instance to_rtexpr_inj π : Inj (=) (=) (to_rtexpr π).
Proof.
  intros ???.
  by eapply to_rtexpr_inj'.
Qed.
Global Instance to_rtstmt_inj : Inj3 (=) (=) (=) (=) to_rtstmt.
Proof.
  intros π1 f1 s1 π2 f2 s2.
  destruct s1, s2; try done.
  all: simpl; intros ?; simplify_eq.
  all: done.
Qed.

Implicit Type (π : thread_id) (l : loc) (re : rtexpr) (v : val) (h : heap) (σ : state) (ly : layout) (rs : rtstmt) (s : stmt) (sgn : signed) (rf : function).

(*** Evaluation of operations *)
Definition compute_arith_bin_op (n1 n2 : Z) (it : _) (op : _) : option Z :=
  match op with
  | AddOp => Some (n1 + n2)
  | SubOp => Some (n1 - n2)
  | MulOp => Some (n1 * n2)
  (* we need to take `quot` and `rem` here for the correct rounding
  behavior, i.e. rounding towards 0 (instead of `div` and `mod`,
  which round towards floor)*)
  | DivOp => if bool_decide (n2 ≠ 0) then Some (n1 `quot` n2) else None
  | ModOp => if bool_decide (n2 ≠ 0) then Some (n1 `rem` n2) else None
  | AndOp => Some (Z.land n1 n2)
  | OrOp => Some (Z.lor n1 n2)
  | XorOp => Some (Z.lxor n1 n2)
  (* For shift operators (`ShlOp` and `ShrOp`), behaviors are defined if:
     - lhs is nonnegative, and
     - rhs (also nonnegative) is less than the number of bits in lhs.
     See: https://en.cppreference.com/w/c/language/operator_arithmetic, "Shift operators". *)
  (* TODO: this does not match the Rust semantics *)
  | ShlOp => if bool_decide (0 ≤ n1 ∧ 0 ≤ n2 < bits_per_int it) then Some (n1 ≪ n2) else None
  (* NOTE: when lhs is negative, Coq's `≫` is not semantically equivalent to C's `>>`.
     Counterexample: Coq `-1000 ≫ 10 = 0`; C `-1000 >> 10 == -1`.
     This is because `≫` is implemented by `Z.div`. *)
  (* TODO: this does not match the Rust semantics *)
  | ShrOp => if bool_decide (0 ≤ n1 ∧ 0 ≤ n2 < bits_per_int it) then Some (n1 ≫ n2) else None
  (* unchecked ops get stuck if the result does not fit in the target integer type *)
  | UncheckedAddOp =>
      if bool_decide (n1 + n2 ∈ it) then Some (n1 + n2) else None
  | UncheckedSubOp =>
      if bool_decide (n1 - n2 ∈ it) then Some (n1 - n2) else None
  | UncheckedMulOp =>
      if bool_decide (n1 * n2 ∈ it) then Some (n1 * n2) else None
  | _ => None
  end.

Inductive eval_bin_op : bin_op → op_type → op_type → state → val → val → val → Prop :=
| PtrOffsetOpIP v1 v2 σ o l ly it:
    val_to_Z v1 it = Some o →
    val_to_loc v2 = Some l →
    (* TODO: should we have an alignment check here? *)
    heap_state_loc_in_bounds (l offset{ly}ₗ o) 0 σ.(st_heap) →

    (* added for Rust (mut_ptr::offset): *)
    (* "Both the starting and resulting pointer must be either in bounds or one byte past the end of the same [allocated object]" *)
    heap_state_loc_in_bounds l 0 σ.(st_heap) →
    (* "The computed offset, **in bytes**, cannot overflow an `isize`" *)
    ly_size ly * o ∈ ISize →

    eval_bin_op (PtrOffsetOp ly) (IntOp it) PtrOp σ v1 v2 (val_of_loc (l offset{ly}ₗ o))
| PtrNegOffsetOpIP v1 v2 σ o l ly it:
    val_to_Z v1 it = Some o →
    val_to_loc v2 = Some l →
    heap_state_loc_in_bounds (l offset{ly}ₗ -o) 0 σ.(st_heap) →
    (* TODO: should we have an alignment check here? *)

    (* added for Rust (mut_ptr::offset): *)
    (* "Both the starting and resulting pointer must be either in bounds or one byte past the end of the same [allocated object]" *)
    heap_state_loc_in_bounds l 0 σ.(st_heap) →
    (* "The computed offset, **in bytes**, cannot overflow an `isize`" *)
    ly_size ly * -o ∈ ISize →

    eval_bin_op (PtrNegOffsetOp ly) (IntOp it) PtrOp σ v1 v2 (val_of_loc (l offset{ly}ₗ -o))

| PtrWrappingOffsetOpIP v1 v2 σ o l ly it :
    val_to_Z v1 it = Some o →
    val_to_loc v2 = Some l →
    eval_bin_op (PtrWrappingOffsetOp ly) (IntOp it) (PtrOp) σ v1 v2 (val_of_loc (l wrapping_offset{ly}ₗ o))
| PtrWrappingNegOffsetOpIP v1 v2 σ o l ly it :
    val_to_Z v1 it = Some o →
    val_to_loc v2 = Some l →
    eval_bin_op (PtrWrappingNegOffsetOp ly) (IntOp it) (PtrOp) σ v1 v2 (val_of_loc (l wrapping_offset{ly}ₗ -o))

(* for `offset_from` *)
| PtrDiffOpPP v1 v2 σ l1 l2 ly v:
    val_to_loc v1 = Some l1 →
    val_to_loc v2 = Some l2 →
    (* derived from the same object, i.e., same provenance *)
    l1.(loc_p) = l2.(loc_p) →
    (* excludes the case of ZSTs (the Rust version panics in that case) *)
    0 < ly.(ly_size) →
    (* both pointers are valid, i.e. in bounds of that allocation *)
    valid_ptr l1 σ.(st_heap) →
    valid_ptr l2 σ.(st_heap) →
    val_of_Z ((l1.(loc_a) - l2.(loc_a)) `div` ly.(ly_size)) ISize = Some v →
    eval_bin_op (PtrDiffOp ly) PtrOp PtrOp σ v1 v2 v

| RelOpPP v1 v2 σ l1 l2 p1 p2 a1 a2 v b op rit:
    val_to_loc v1 = Some l1 →
    val_to_loc v2 = Some l2 →
    (* We do not compare the provenance *)
    l1 = Loc p1 a1 →
    l2 = Loc p2 a2 →
    match op with
    | LtOp rit => Some (bool_decide (a1 < a2), rit)
    | GtOp rit => Some (bool_decide (a1 > a2), rit)
    | LeOp rit => Some (bool_decide (a1 <= a2), rit)
    | GeOp rit => Some (bool_decide (a1 >= a2), rit)
    | EqOp rit => Some (bool_decide (a1 = a2), rit)
    | NeOp rit => Some (bool_decide (a1 <> a2), rit)
    | _ => None
    end = Some (b, rit) →
    val_of_Z (bool_to_Z b) rit = Some v →
    eval_bin_op op PtrOp PtrOp σ v1 v2 v
| RelOpII op v1 v2 v σ n1 n2 it b rit:
    match op with
    | EqOp rit => Some (bool_decide (n1 = n2), rit)
    | NeOp rit => Some (bool_decide (n1 ≠ n2), rit)
    | LtOp rit => Some (bool_decide (n1 < n2), rit)
    | GtOp rit => Some (bool_decide (n1 > n2), rit)
    | LeOp rit => Some (bool_decide (n1 <= n2), rit)
    | GeOp rit => Some (bool_decide (n1 >= n2), rit)
    | _ => None
    end = Some (b, rit) →
    val_to_Z v1 it = Some n1 →
    val_to_Z v2 it = Some n2 →
    (* equivalent to [val_of_bool] if using [u8] by [val_of_bool_iff_val_of_Z] *)
    val_of_Z (bool_to_Z b) rit = Some v →
    eval_bin_op op (IntOp it) (IntOp it) σ v1 v2 v
| RelOpBB op v1 v2 v σ b1 b2 b rit :
  (* relational operators on booleans -- requires that the two are actually booleans *)
  match op with
    | EqOp rit => Some (bool_decide (b1 = b2), rit)
    | NeOp rit => Some (bool_decide (b1 ≠ b2), rit)
    | _ => None
  end = Some (b, rit) →
  val_to_bool v1 = Some b1 →
  val_to_bool v2 = Some b2 →
  (* equivalent to [val_of_bool] if using [u8] by [val_of_bool_iff_val_of_Z] *)
  val_of_Z (bool_to_Z b) rit = Some v →
  eval_bin_op op BoolOp BoolOp σ v1 v2 v
| ArithOpII op v1 v2 σ n1 n2 it n v:
    compute_arith_bin_op n1 n2 it op = Some n →
    val_to_Z v1 it = Some n1 →
    val_to_Z v2 it = Some n2 →
    (* wrap *)
    val_of_Z (wrap_to_it n it) it = Some v →
    eval_bin_op op (IntOp it) (IntOp it) σ v1 v2 v
| ArithOpBB op v1 v2 σ b1 b2 b v :
    match op with
    | AndOp => Some (andb b1 b2)
    | OrOp => Some (orb b1 b2)
    | XorOp => Some (xorb b1 b2)
    | _ => None
    end = Some b →
    val_to_bool v1 = Some b1 →
    val_to_bool v2 = Some b2 →
    val_of_bool b = v →
    eval_bin_op op BoolOp BoolOp σ v1 v2 v
| CommaOp ot1 ot2 σ v1 v2:
    eval_bin_op Comma ot1 ot2 σ v1 v2 v2
.

(** Check if the result of an arithmetic operator is representable in the target integer type. *)
(* Note: this still requires the computation itself to succeed/ be mathematically defined. *)
Definition check_arith_bin_op (op : bin_op) (it : int_type) (n1 n2 : Z) : option bool :=
  option_map (λ n, bool_decide (n ∉ it)) (compute_arith_bin_op n1 n2 it op)
.

Inductive check_bin_op : bin_op → op_type → op_type → val → val → bool → Prop :=
| CheckArithOpII op v1 v2 n1 n2 it b:
    val_to_Z v1 it = Some n1 →
    val_to_Z v2 it = Some n2 →
    check_arith_bin_op op it n1 n2 = Some b →
    check_bin_op op (IntOp it) (IntOp it) v1 v2 b
.

Inductive eval_un_op : un_op → op_type → state → val → val → Prop :=
| CastOpII itt its σ vs vt i i':
    val_to_Z vs its = Some i →
    wrap_to_it i itt = i' →
    val_of_Z i' itt  = Some vt →
    eval_un_op (CastOp (IntOp itt)) (IntOp its) σ vs vt
| CastOpPP σ vs l:
    val_to_loc vs = Some l →
    eval_un_op (CastOp PtrOp) PtrOp σ vs vs
| CastOpPI it σ vs vt l:
    (* This is always possible.
       We do not require a valid provenance.
       This does not expose the provenance and thus is stricter than Rust's casts (akin to Rusts strict-provenance ptr.addr()). *)
    val_to_loc vs = Some l →
    val_of_Z l.(loc_a) it = Some vt →
    eval_un_op (CastOp (IntOp it)) PtrOp σ vs vt
| CastOpIP it σ vs vt l a:
    val_to_Z vs it = Some a →
    l = (* assign empty provenance *) Loc ProvNone a →
    val_of_loc l = vt →
    eval_un_op (CastOp PtrOp) (IntOp it) σ vs vt
| CastOpB ot σ vs vt b:
    cast_to_bool ot vs σ.(st_heap) = Some b →
    vt = val_of_bool b →
    eval_un_op (CastOp BoolOp) ot σ vs vt
| CastOpBI it σ vs vt b:
    val_to_bool vs = Some b →
    val_of_Z (bool_to_Z b) it = Some vt →
    eval_un_op (CastOp (IntOp it)) BoolOp σ vs vt
| NegOpI it σ vs vt n:
    val_to_Z vs it = Some n →
    (* wrap *)
    val_of_Z (wrap_to_it (-n) it) it = Some vt →
    eval_un_op NegOp (IntOp it) σ vs vt
| NotIntOpI it σ vs vt n:
    val_to_Z vs it = Some n →
    val_of_Z (if it_signed it then Z.lnot n else Z_lunot (bits_per_int it) n) it = Some vt →
    eval_un_op NotIntOp (IntOp it) σ vs vt
| NotBoolOpB σ vs vt b :
    val_to_bool vs = Some b →
    val_of_bool (negb b) = vt →
    eval_un_op NotBoolOp BoolOp σ vs vt
.

Definition check_arith_un_op (op : un_op) (it : int_type) (n : Z) : option bool :=
  let res :=
    match op with
    | NegOp => Some (-n)
    | _ => None
    end in
  option_map (λ n, bool_decide (n ∉ it)) res.

Inductive check_un_op : un_op → op_type → val → bool → Prop :=
| CheckArithOpI op it vs n b:
    val_to_Z vs it = Some n →
    check_arith_un_op op it n = Some b →
    check_un_op op (IntOp it) vs b
.

(** Evaluate an atomic RMW operation: compute the new value from old and argument. *)
Definition atomic_rmw_eval (op : atomic_rmw_op) (ot : op_type) (vo varg : val) : option val :=
  match op with
  | RmwXchg => Some varg
  | RmwAdd =>
      match ot with
      | IntOp it =>
          n1 ← val_to_Z vo it;
          n2 ← val_to_Z varg it;
          n ← compute_arith_bin_op n1 n2 it AddOp;
          val_of_Z (wrap_to_it n it) it
      | _ => None
      end
  | RmwSub =>
      match ot with
      | IntOp it =>
          n1 ← val_to_Z vo it;
          n2 ← val_to_Z varg it;
          n ← compute_arith_bin_op n1 n2 it SubOp;
          val_of_Z (wrap_to_it n it) it
      | _ => None
      end
  | RmwAnd =>
      match ot with
      | IntOp it =>
          n1 ← val_to_Z vo it;
          n2 ← val_to_Z varg it;
          n ← compute_arith_bin_op n1 n2 it AndOp;
          val_of_Z (wrap_to_it n it) it
      | _ => None
      end
  | RmwOr =>
      match ot with
      | IntOp it =>
          n1 ← val_to_Z vo it;
          n2 ← val_to_Z varg it;
          n ← compute_arith_bin_op n1 n2 it OrOp;
          val_of_Z (wrap_to_it n it) it
      | _ => None
      end
  | RmwXor =>
      match ot with
      | IntOp it =>
          n1 ← val_to_Z vo it;
          n2 ← val_to_Z varg it;
          n ← compute_arith_bin_op n1 n2 it XorOp;
          val_of_Z (wrap_to_it n it) it
      | _ => None
      end
  | RmwNand =>
      match ot with
      | IntOp it =>
          n1 ← val_to_Z vo it;
          n2 ← val_to_Z varg it;
          val_of_Z (wrap_to_it (Z.lnot (Z.land n1 n2)) it) it
      | _ => None
      end
  | RmwMaxS =>
      match ot with
      | IntOp it =>
          n1 ← val_to_Z vo it;
          n2 ← val_to_Z varg it;
          val_of_Z (Z.max n1 n2) it
      | _ => None
      end
  | RmwMinS =>
      match ot with
      | IntOp it =>
          n1 ← val_to_Z vo it;
          n2 ← val_to_Z varg it;
          val_of_Z (Z.min n1 n2) it
      | _ => None
      end
  | RmwMaxU | RmwMinU =>
      match ot with
      | IntOp it =>
          n1 ← val_to_Z vo it;
          n2 ← val_to_Z varg it;
          let u1 := n1 `mod` int_modulus it in
          let u2 := n2 `mod` int_modulus it in
          let r := match op with
            | RmwMaxU => if (u2 <=? u1)%Z then n1 else n2
            | RmwMinU => if (u1 <=? u2)%Z then n1 else n2
            | _ => n1 (* unreachable — outer match restricts to RmwMaxU|RmwMinU *)
          end in
          val_of_Z r it
      | _ => None
      end
  end.

(*** Evaluation of Expressions *)

Inductive expr_step : expr → thread_id → state → list Empty_set → runtime_expr → state → list runtime_expr → Prop :=
| SkipES v σ π:
    expr_step (SkipE (Val v)) π σ [] (RTVal v) σ []
| UnOpS op v σ π v' ot:
    eval_un_op op ot σ v v' →
    expr_step (UnOp op ot (Val v)) π σ [] (RTVal v') σ []
| BinOpS op v1 v2 σ π v' ot1 ot2:
    eval_bin_op op ot1 ot2 σ v1 v2 v' →
    expr_step (BinOp op ot1 ot2 (Val v1) (Val v2)) π σ [] (RTVal v') σ []
| CheckUnOpS op v σ π b ot :
    check_un_op op ot v b →
    expr_step (CheckUnOp op ot (Val v)) π σ [] (RTVal (val_of_bool b)) σ []
| CheckBinOpS op v1 v2 σ π b ot1 ot2 :
    check_bin_op op ot1 ot2 v1 v2 b →
    expr_step (CheckBinOp op ot1 ot2 (Val v1) (Val v2)) π σ [] (RTVal (val_of_bool b)) σ []
| VarS π x σ ts cf l ly :
    state_get_thread σ π = Some ts →
    thread_get_frame ts = Some cf →
    cf.(cf_locals) !! x = Some (l, ly) →
    expr_step (Var x) π σ [] (RTVal (val_of_loc l)) σ []
| DerefS o v l ot v' σ π (mc : bool):
    let start_st st := ∃ n, st = if o is Na2Ord then RSt (S n) else RSt n in
    let end_st st :=
      match o, st with
      | Na1Ord, Some (RSt n)     => RSt (S n)
      | Na2Ord, Some (RSt (S n)) => RSt n
      | ScOrd , Some st          => st
      |  _    , _                => WSt (* unreachable *)
      end
    in
    let end_expr :=
      if o is Na1Ord then
        Deref Na2Ord ot mc (Val v)
      else
        Val (if mc then mem_cast v' ot (dom σ.(st_fntbl), σ.(st_heap)) else v') in
    val_to_loc v = Some l →
    heap_at l (ot_layout ot) v' start_st σ.(st_heap).(hs_heap) →
    expr_step (Deref o ot mc (Val v)) π σ [] (to_rtexpr π end_expr) (heap_fmap (heap_upd l v' end_st) σ) []
(* TODO: look at CAS and see whether it makes sense. Also allow
comparing pointers? (see lambda rust) *)
(* corresponds to atomic_compare_exchange_strong, see https://en.cppreference.com/w/c/atomic/atomic_compare_exchange *)
| CasFailS l1 l2 vo ve σ π z1 z2 v1 v2 v3 ot:
    val_to_loc v1 = Some l1 →
    heap_at l1 (ot_layout ot) vo (λ st, ∃ n, st = RSt n) σ.(st_heap).(hs_heap) →
    val_to_loc v2 = Some l2 →
    heap_at l2 (ot_layout ot) ve (λ st, st = RSt 0%nat) σ.(st_heap).(hs_heap) →
    val_to_Z_ot vo ot = Some z1 →
    val_to_Z_ot ve ot = Some z2 →
    v3 `has_layout_val` ot_layout ot →
    ((ot_layout ot).(ly_size) ≤ bytes_per_addr)%nat →
    z1 ≠ z2 →
    expr_step (CAS ot (Val v1) (Val v2) (Val v3)) π σ []
              (RTVal (val_of_bool false)) (heap_fmap (heap_upd l2 vo (λ _, RSt 0%nat)) σ) []
| CasSucS l1 l2 ot vo ve σ π z1 z2 v1 v2 v3:
    val_to_loc v1 = Some l1 →
    heap_at l1 (ot_layout ot) vo (λ st, st = RSt 0%nat) σ.(st_heap).(hs_heap) →
    val_to_loc v2 = Some l2 →
    heap_at l2 (ot_layout ot) ve (λ st, ∃ n, st = RSt n) σ.(st_heap).(hs_heap) →
    val_to_Z_ot vo ot = Some z1 →
    val_to_Z_ot ve ot = Some z2 →
    v3 `has_layout_val` ot_layout ot →
    ((ot_layout ot).(ly_size) ≤ bytes_per_addr)%nat →
    z1 = z2 →
    expr_step (CAS ot (Val v1) (Val v2) (Val v3)) π σ []
              (RTVal (val_of_bool true)) (heap_fmap (heap_upd l1 v3 (λ _, RSt 0%nat)) σ) []
| AtomicRMWS op ot l vo σ π v1 v2 v_new:
    val_to_loc v1 = Some l →
    heap_at l (ot_layout ot) vo (λ st, st = RSt 0%nat) σ.(st_heap).(hs_heap) →
    v2 `has_layout_val` ot_layout ot →
    v_new `has_layout_val` ot_layout ot →
    ((ot_layout ot).(ly_size) ≤ bytes_per_addr)%nat →
    atomic_rmw_eval op ot vo v2 = Some v_new →
    expr_step (AtomicRMW op ot (Val v1) (Val v2)) π σ []
              (RTVal vo) (heap_fmap (heap_upd l v_new (λ _, RSt 0%nat)) σ) []
| CallS π lsa σ hs' ts ts' vf vs f fn a:
    val_to_loc vf = Some f →
    f = fn_loc a →
    σ.(st_fntbl) !! a = Some fn →
    length lsa = length fn.(f_args) →

    (* check the layout of the arguments *)
    Forall2 has_layout_val vs fn.(f_args).*2 →
    (* ensure that locations are aligned *)
    Forall2 has_layout_loc lsa fn.(f_args).*2 →

    (* initialize the arguments with the supplied values *)
    alloc_new_blocks σ.(st_heap) StackAlloc lsa vs hs' →

    (* push new frame *)
    state_get_thread σ π = Some ts →
    ts' = thread_push_frame ts (initialize_new_frame fn.(f_args) lsa) →

    expr_step (Call (Val vf) (Val <$> vs)) π σ []
      (to_rtstmt π fn (Goto fn.(f_init)))
      {| st_heap := hs'; st_fntbl := σ.(st_fntbl); st_thread := <[π := ts']> σ.(st_thread) |} []
| CallFailS π σ vf vs f fn a:
    val_to_loc vf = Some f →
    f = fn_loc a →
    σ.(st_fntbl) !! a = Some fn →
    Forall2 has_layout_val vs fn.(f_args).*2 →
    expr_step (Call (Val vf) (Val <$> vs)) π σ [] AllocFailed σ []
| ConcatS vs π σ :
    expr_step (Concat (Val <$> vs)) π σ [] (RTVal (mjoin vs)) σ []
(* for ptr::with_addr *)
| CopyAllocIdS π σ v1 v2 a it l:
    val_to_Z v1 it = Some a →
    val_to_loc v2 = Some l →
    expr_step (CopyAllocId (IntOp it) (Val v1) (Val v2)) π σ [] (RTVal (val_of_loc (Loc l.(loc_p) a))) σ []
| IfES v ot e1 e2 b π σ:
    cast_to_bool ot v σ.(st_heap) = Some b →
    expr_step (IfE ot (Val v) e1 e2) π σ [] (to_rtexpr π $ if b then e1 else e2) σ []
| AllocS v_size v_align (n_size n_align : nat) l π σ hs' :
    val_to_Z v_size USize = Some (Z.of_nat n_size) →
    val_to_Z v_align USize = Some (Z.of_nat n_align) →
    (* Rust's allocation APIs allow allocators to exhibit UB if the size is zero, so we also trigger UB here *)
    n_size > 0 →
    l `has_layout_loc` (Layout n_size n_align)  →
    alloc_new_block σ.(st_heap) HeapAlloc l (replicate n_size MPoison) hs' →
    expr_step (Alloc (Val v_size) (Val v_align)) π σ []
      (RTVal (val_of_loc l)) {| st_heap := hs'; st_fntbl := σ.(st_fntbl); st_thread := σ.(st_thread) |} []
| AllocFailS v_size v_align (n_size n_align : nat) π σ :
    val_to_Z v_size USize = Some (Z.of_nat n_size) →
    val_to_Z v_align USize = Some (Z.of_nat n_align) →
    n_size > 0 →
    expr_step (Alloc (Val v_size) (Val v_align)) π σ [] AllocFailed σ []
(* no rule for StuckE *)
.

(*** Evaluation of statements *)
Inductive stmt_step : stmt → thread_id → function → state → list Empty_set → runtime_expr → state → list runtime_expr → Prop :=
| AssignS (o : order) π rf σ s v1 v2 l v' ot:
    let start_st st := st = if o is Na2Ord then WSt else RSt 0%nat in
    let end_st _ := if o is Na1Ord then WSt else RSt 0%nat in
    let end_val  := if o is Na1Ord then v' else v2 in
    let end_stmt := if o is Na1Ord then Assign Na2Ord ot (Val v1) (Val v2) s else s in
    val_to_loc v1 = Some l →
    v2 `has_layout_val` (ot_layout ot) →
    heap_at l (ot_layout ot) v' start_st σ.(st_heap).(hs_heap) →
    stmt_step (Assign o ot (Val v1) (Val v2) s) π rf σ [] (to_rtstmt π rf end_stmt) (heap_fmap (heap_upd l end_val end_st) σ) []
| IfSS ot join v s1 s2 π rf σ b:
    cast_to_bool ot v σ.(st_heap) = Some b →
    stmt_step (IfS ot join (Val v) s1 s2) π rf σ [] (to_rtstmt π rf ((if b then s1 else s2))) σ []
| SwitchS π rf σ v n m bs s def it :
    val_to_Z v it = Some n →
    (∀ i : nat, m !! n = Some i → is_Some (bs !! i)) →
    stmt_step (Switch it (Val v) m bs def) π rf σ [] (to_rtstmt π rf (default def (i ← m !! n; bs !! i))) σ []
| GotoS π rf σ b s :
    rf.(f_code) !! b = Some s →
    stmt_step (Goto b) π rf σ [] (to_rtstmt π rf s) σ []
| ReturnS π rf σ hs v ts cf :
    state_get_thread σ π = Some ts →
    thread_get_frame ts = Some cf →
    (* Deallocate the stack. *)
    free_blocks σ.(st_heap) StackAlloc (map_to_list cf.(cf_locals)).*2 hs →
    stmt_step (Return (Val v)) π rf σ [] (RTVal v) {| st_fntbl := σ.(st_fntbl); st_heap := hs; st_thread := <[π := pop_frame ts]> σ.(st_thread) |} []
| FreeS v_size v_align (n_size n_align : nat) v l s π rf σ hs' :
    val_to_Z v_size USize = Some (Z.of_nat n_size) →
    val_to_Z v_align USize = Some (Z.of_nat n_align) →
    val_to_loc v = Some l →
    n_size > 0 →
    l `has_layout_loc` (Layout n_size n_align) →
    free_block σ.(st_heap) HeapAlloc l (Layout n_size n_align) hs' →
    stmt_step (Free (Val v_size) (Val v_align) (Val v) s) π rf σ []
      (to_rtstmt π rf s) {| st_fntbl := σ.(st_fntbl); st_heap := hs'; st_thread := σ.(st_thread) |} []
| SkipSS π rf σ s :
    stmt_step (SkipS s) π rf σ [] (to_rtstmt π rf s) σ []
| ExprSS π rf σ s v:
    stmt_step (ExprS (Val v) s) π rf σ [] (to_rtstmt π rf s) σ []
| LocalLiveS π rf σ x ly s hs' ts cf cf' l :
    (* NB: this also works for zero-sized locals *)
    l `has_layout_loc` ly  →
    alloc_new_block σ.(st_heap) StackAlloc l (replicate ly.(ly_size) MPoison) hs' →
    state_get_thread σ π = Some ts →
    thread_get_frame ts = Some cf →
    cf.(cf_locals) !! x = None →
    cf' = frame_alloc_var cf x l ly →
    stmt_step (LocalLive x ly s) π rf σ [] (to_rtstmt π rf s) {| st_fntbl := σ.(st_fntbl); st_heap := hs'; st_thread := <[π := thread_update_frame ts cf']> σ.(st_thread) |} []
| LocalLiveFailS π rf σ x ly s ts cf :
    state_get_thread σ π = Some ts →
    thread_get_frame ts = Some cf →
    cf.(cf_locals) !! x = None →
    stmt_step (LocalLive x ly s) π  rf σ [] AllocFailed σ []
| LocalDeadDeallocS π rf σ x s hs' ts cf cf' l ly :
    state_get_thread σ π = Some ts →
    thread_get_frame ts = Some cf →
    cf.(cf_locals) !! x = Some (l, ly) →

    l `has_layout_loc` ly →
    free_block σ.(st_heap) StackAlloc l ly hs' →

    cf' = frame_dealloc_var cf x →

    stmt_step (LocalDead x s) π rf σ [] (to_rtstmt π rf s) {| st_fntbl := σ.(st_fntbl); st_heap := hs'; st_thread := <[π := thread_update_frame ts cf']> σ.(st_thread) |} []
(* NOP in Rust if it has already been deallocated *)
| LocalDeadNopS π rf σ x s ts cf :
    state_get_thread σ π = Some ts →
    thread_get_frame ts = Some cf →
    cf.(cf_locals) !! x = None →

    stmt_step (LocalDead x s) π rf σ [] (to_rtstmt π rf s) σ []
(* no rule for StuckS *)
.

(*** Evaluation of runtime_expr *)
Inductive runtime_step : runtime_expr → state → list Empty_set → runtime_expr → state → list runtime_expr → Prop :=
| ExprStep e π σ κs e' σ' efs:
    expr_step e π σ κs e' σ' efs →
    runtime_step (to_rtexpr π e) σ κs e' σ' efs
| StmtStep s π rf σ κs e' σ' efs:
    stmt_step s π rf σ κs e' σ' efs →
    runtime_step (to_rtstmt π rf s) σ κs e' σ' efs
| AllocFailedStep σ :
    (* Alloc failure is nb, not ub so we go into an infinite loop*)
    runtime_step AllocFailed σ [] AllocFailed σ [].

Lemma expr_step_preserves_invariant π e1 e2 σ1 σ2 κs efs:
  expr_step e1 π σ1 κs e2 σ2 efs →
  heap_state_invariant σ1.(st_heap) →
  heap_state_invariant σ2.(st_heap).
Proof.
  move => [] // *.
  all: repeat select (heap_at _ _ _ _ _) ltac:(fun H => destruct H as [?[?[??]]]).
  all: try (rewrite /heap_fmap/=; eapply heap_update_heap_state_invariant => //).
  all: try (unfold has_layout_val in *; by etransitivity).
  - repeat eapply alloc_new_blocks_invariant => //.
  - eapply alloc_new_block_invariant => //.
Qed.

Lemma stmt_step_preserves_invariant s π rf e σ1 σ2 κs efs:
  stmt_step s π rf σ1 κs e σ2 efs →
  heap_state_invariant σ1.(st_heap) →
  heap_state_invariant σ2.(st_heap).
Proof.
  move => [] //; clear.
  - move => o *.
    revert select (heap_at _ _ _ _ _) => -[?[?[??]]].
    rewrite /heap_fmap/=. eapply heap_update_heap_state_invariant => //.
    match goal with H : _ `has_layout_val` _ |- _ => rewrite H end.
    by destruct o.
  - intros. by eapply free_blocks_invariant.
  - intros. by eapply free_block_invariant.
  - intros. eapply alloc_new_block_invariant => //.
  - intros. by eapply free_block_invariant.
Qed.

Lemma runtime_step_preserves_invariant e1 e2 σ1 σ2 κs efs:
  runtime_step e1 σ1 κs e2 σ2 efs →
  heap_state_invariant σ1.(st_heap) →
  heap_state_invariant σ2.(st_heap).
Proof.
  move => [] // *.
  - by eapply expr_step_preserves_invariant.
  - by eapply stmt_step_preserves_invariant.
Qed.

(*** evaluation contexts *)
(** for expressions*)
Inductive expr_ectx :=
| UnOpCtx (op : un_op) (ot : op_type)
| CheckUnOpCtx (op : un_op) (ot : op_type)
| BinOpLCtx (op : bin_op) (ot1 ot2 : op_type) (e2 : runtime_expr)
| BinOpRCtx (op : bin_op) (ot1 ot2 : op_type) (v1 : val)
| CheckBinOpLCtx (op : bin_op) (ot1 ot2 : op_type) (e2 : runtime_expr)
| CheckBinOpRCtx (op : bin_op) (ot1 ot2 : op_type) (v1 : val)
| CopyAllocIdLCtx (ot1 : op_type) (e2 : runtime_expr)
| CopyAllocIdRCtx (ot1 : op_type) (v1 : val)
| DerefCtx (o : order) (ot : op_type) (memcast : bool)
| CallLCtx (args : list runtime_expr)
| CallRCtx (f : val) (vl : list val) (el : list runtime_expr)
| CASLCtx (ot : op_type) (e2 e3 : runtime_expr)
| CASMCtx (ot : op_type) (v1 : val) (e3 : runtime_expr)
| CASRCtx (ot : op_type) (v1 v2 : val)
| AtomicRMWLCtx (op : atomic_rmw_op) (ot : op_type) (e2 : runtime_expr)
| AtomicRMWRCtx (op : atomic_rmw_op) (ot : op_type) (v1 : val)
| ConcatCtx (vs : list val) (es : list runtime_expr)
| IfECtx (ot : op_type) (e2 e3 : runtime_expr)
| AllocLCtx (e_align : runtime_expr)
| AllocRCtx (v_size : val)
| SkipECtx
.

Definition expr_fill_item (Ki : expr_ectx) (e : runtime_expr) : rtexpr :=
  match Ki with
  | UnOpCtx op ot => RTUnOp op ot e
  | CheckUnOpCtx op ot => RTCheckUnOp op ot e
  | BinOpLCtx op ot1 ot2 e2 => RTBinOp op ot1 ot2 e e2
  | BinOpRCtx op ot1 ot2 v1 => RTBinOp op ot1 ot2 (RTVal v1) e
  | CheckBinOpLCtx op ot1 ot2 e2 => RTCheckBinOp op ot1 ot2 e e2
  | CheckBinOpRCtx op ot1 ot2 v1 => RTCheckBinOp op ot1 ot2 (RTVal v1) e
  | CopyAllocIdLCtx ot1 e2 => RTCopyAllocId ot1 e e2
  | CopyAllocIdRCtx ot1 v1 => RTCopyAllocId ot1 (RTVal v1) e
  | DerefCtx o l mc => RTDeref o l mc e
  | CallLCtx args => RTCall e args
  | CallRCtx f vl el => RTCall (RTVal f) (((RTVal <$> vl)) ++ e :: el)
  | CASLCtx ot e2 e3 => RTCAS ot e e2 e3
  | CASMCtx ot v1 e3 => RTCAS ot (RTVal v1) e e3
  | CASRCtx ot v1 v2 => RTCAS ot (RTVal v1) (RTVal v2) e
  | AtomicRMWLCtx op ot e2 => RTAtomicRMW op ot e e2
  | AtomicRMWRCtx op ot v1 => RTAtomicRMW op ot (RTVal v1) e
  | ConcatCtx vs es => RTConcat (((RTVal <$> vs)) ++ e :: es)
  | IfECtx ot e2 e3 => RTIfE ot e e2 e3
  | AllocLCtx e_align => RTAlloc e e_align
  | AllocRCtx v_size => RTAlloc (RTVal v_size) e
  | SkipECtx => RTSkipE e
  end.

(** Statements *)
Inductive stmt_ectx :=
(* Assignment is evalutated right to left, otherwise we need to split contexts *)
| AssignRCtx (o : order) (ot : op_type) (e1 : expr) (s : stmt)
| AssignLCtx (o : order) (ot : op_type) (v2 : val) (s : stmt)
| ReturnCtx
| FreeLCtx (e_align : expr) (e : expr) (s : stmt)
| FreeMCtx (v_size : val) (e : expr) (s : stmt)
| FreeRCtx (v_size : val) (v_align : val) (s : stmt)
| IfSCtx (ot : op_type) (join : option label) (s1 s2 : stmt)
| SwitchCtx (it : int_type) (m: gmap Z nat) (bs : list stmt) (def : stmt)
| ExprSCtx (s : stmt)
.

Definition stmt_fill_item (π : thread_id) (Ki : stmt_ectx) (e : runtime_expr) : rtstmt :=
  match Ki with
  | AssignRCtx o ot e1 s => RTAssign o ot (to_rtexpr π e1) e s
  | AssignLCtx o ot v2 s => RTAssign o ot e (RTVal v2) s
  | ReturnCtx => RTReturn e
  | FreeLCtx e_align e' s => RTFree e (to_rtexpr π e_align) (to_rtexpr π e') s
  | FreeMCtx v_size e' s => RTFree (RTVal v_size) e (to_rtexpr π e') s
  | FreeRCtx v_size v_align s => RTFree (RTVal v_size) (RTVal v_align) e s
  | IfSCtx ot join s1 s2 => RTIfS ot join e s1 s2
  | SwitchCtx it m bs def => RTSwitch it e m bs def
  | ExprSCtx s => RTExprS e s
  end.

Inductive lang_ectx :=
| ExprCtx (E : expr_ectx) (π : thread_id)
| StmtCtx (E : stmt_ectx) (π : thread_id) (rf : function).

Definition lang_fill_item (Ki : lang_ectx) (e : runtime_expr) : runtime_expr :=
  match Ki with
  | ExprCtx E π => Expr π (expr_fill_item E e)
  | StmtCtx E π rf => Stmt π rf (stmt_fill_item π E e)
  end.

Lemma list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2 :
  to_val e1 = None → to_val e2 = None →
  ((RTVal <$> vl1)) ++ e1 :: el1 = ((RTVal <$> vl2)) ++ e2 :: el2 →
  vl1 = vl2 ∧ e1 = e2 ∧ el1 = el2.
Proof.
  revert vl2; induction vl1; destruct vl2; intros H1 H2; inversion 1.
  - done.
  - subst. by inversion H1.
  - subst. by inversion H2.
  - destruct (IHvl1 vl2); auto. split; f_equal; auto.
Qed.

Lemma list_expr_val_eq_false π vl1 vl2 e el :
  to_val e = None → to_rtexpr π <$> (Val <$> vl1) = ((RTVal <$> vl2)) ++ e :: el → False.
Proof.
  move => He. elim: vl2 vl1 => [[]//=*|v vl2 IH [|??]?]; csimpl in *; simplify_eq; eauto.
Qed.

Lemma of_to_val (e : runtime_expr) v : to_val e = Some v → RTVal v = e.
Proof. case: e => //. naive_solver. Qed.

Lemma val_stuck e1 σ1 κ e2 σ2 ef :
  runtime_step e1 σ1 κ e2 σ2 ef → to_val e1 = None.
Proof. destruct 1 => //. revert select (expr_step _ _ _ _ _ _ _). by destruct 1. Qed.

Global Instance fill_item_inj Ki : Inj (=) (=) (lang_fill_item Ki).
Proof. destruct Ki as [E|E ?]; destruct E; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (lang_fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki as [[]|[] ?]; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  lang_fill_item Ki1 e1 = lang_fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  move: Ki1 Ki2 => [ ^ Ki1] [ ^Ki2] He1 He2 ? //; simplify_eq; try done; f_equal.
  all: destruct Ki1E, Ki2E => //; simplify_eq => //.
  all: opose proof* list_expr_val_eq_inv as HEQ; [| | done |] => //; naive_solver.
Qed.

Lemma expr_ctx_step_val Ki e σ1 κ e2 σ2 ef :
  runtime_step (lang_fill_item Ki e) σ1 κ e2 σ2 ef → is_Some (to_val e).
Proof.
  destruct Ki as [[]|[]?]; inversion 1; simplify_eq.
  all: try (revert select (expr_step _ _ _ _ _ _ _)).
  all: try (revert select (stmt_step _ _ _ _ _ _ _ _)).
  all: inversion 1; simplify_eq/=; eauto.
  all: apply not_eq_None_Some; intros ?; by eapply list_expr_val_eq_false.
Qed.

Lemma c_lang_mixin : EctxiLanguageMixin of_val to_val lang_fill_item runtime_step.
Proof.
  split => //; eauto using of_to_val, val_stuck, fill_item_inj, fill_item_val, fill_item_no_val_inj, expr_ctx_step_val.
Qed.
Canonical Structure c_ectxi_lang := EctxiLanguage c_lang_mixin.
Canonical Structure c_ectx_lang := EctxLanguageOfEctxi c_ectxi_lang.
Canonical Structure c_lang := LanguageOfEctx c_ectx_lang.

(** * Useful instances and canonical structures *)

Global Instance mbyte_inhabited : Inhabited mbyte := populate (MPoison).
Global Instance val_inhabited : Inhabited val := _.
Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).
Global Instance stmt_inhabited : Inhabited stmt := populate (Goto "a").
Global Program Instance function_inhabited : Inhabited function :=
  populate {| f_args := []; f_code := ∅; f_init := ""; |}.
Next Obligation. apply NoDup_nil_2. Qed.
Global Instance heap_state_inhabited : Inhabited heap_state :=
  populate {| hs_heap := inhabitant; hs_allocs := inhabitant; |}.
Global Instance call_frame_inhabited : Inhabited call_frame :=
  populate {| cf_locals := inhabitant |}.
Global Instance thread_state_inhabited : Inhabited thread_state :=
  populate {| ts_frames := inhabitant |}.
Global Instance state_inhabited : Inhabited state :=
  populate {| st_heap := inhabitant; st_fntbl := inhabitant; st_thread := inhabitant |}.

Canonical Structure mbyteO := leibnizO mbyte.
Canonical Structure functionO := leibnizO function.
Canonical Structure locO := leibnizO loc.
Canonical Structure alloc_idO := leibnizO alloc_id.
Canonical Structure layoutO := leibnizO layout.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.
Canonical Structure allocationO := leibnizO allocation.

Ltac unfold_common_caesium_defs :=
  unfold
  (* Unfold [aligned_to] and [Z.divide] as lia can work with the underlying multiplication. *)
    aligned_to,
    (*Z.divide,*)
  (* Layout *)
    ly_size, ly_with_align, ly_align_log, layout_wf, it_layout,
  (* Address bounds *)
    max_alloc_end, min_alloc_start, bytes_per_addr,
  (* Integer bounds *)
    max_int, min_int, int_half_modulus, int_modulus,
    bits_per_int, bytes_per_int, bytes_per_addr_log,
  (* Other byte-level definitions *)
    bits_per_byte in *.
