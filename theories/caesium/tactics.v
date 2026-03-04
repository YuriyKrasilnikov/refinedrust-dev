From stdpp Require Import fin_maps.
From caesium Require Export notation.
Set Default Proof Using "Type".

Module W.
(*** Expressions *)
Section expr.
Local Unset Elimination Schemes.
Inductive expr :=
| Var (x : var_name)
| Loc (l : loc)
| Val (v : val)
| UnOp (op : un_op) (ot : op_type) (e : expr)
| BinOp (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : expr)
| CheckUnOp (op : un_op) (ot : op_type) (e : expr)
| CheckBinOp (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : expr)
| CopyAllocId (ot1 : op_type) (e1 e2 : expr)
| Deref (o : order) (ot : op_type) (memcast : bool) (e : expr)
| CAS (ot : op_type) (e1 e2 e3 : expr)
| AtomicRMW (op : atomic_rmw_op) (ot : op_type) (e1 e2 : expr)
| Call (f : expr) (eκs : list string) (etys : list rust_type) (args : list expr)
| Concat (es : list expr)
| IfE (op : op_type) (e1 e2 e3 : expr)
| Alloc (e_size : expr) (e_align : expr)
| SkipE (e : expr)
| StuckE
(* new constructors *)
| LogicalAnd (ot1 ot2 : op_type) (rit : int_type) (e1 e2 : expr)
| LogicalOr (ot1 ot2 : op_type) (rit : int_type) (e1 e2 : expr)
| Move (o : order) (ot : op_type) (memcast : bool) (e : expr)
| Copy (o : order) (ot : op_type) (memcast : bool) (e : expr)
| AddrOf (m : mutability) (e : expr)
| LValue (e : expr)
| GetMember (e : expr) (s : struct_layout_spec) (m : var_name)
| GetMemberUnion (e : expr) (ul : union_layout_spec) (m : var_name)
| EnumDiscriminant (els : enum_layout_spec) (e : expr)
| EnumData (els : enum_layout_spec) (variant : var_name) (e : expr)
| OffsetOf (s : struct_layout_spec) (m : var_name)
| OffsetOfUnion (ul : union_layout_spec) (m : var_name)
| AnnotExpr (n : nat) {A} (a : A) (e : expr)
| LocInfoE (a : location_info) (e : expr)
| StructInit (sls : struct_layout_spec) (fs : list (string * expr))
| EnumInit (els : enum_layout_spec) (variant : var_name) (ty : rust_enum_def) (e : expr)
| Borrow (m : mutability) (κn : string) (ty : option rust_type) (e : expr)
(* for opaque expressions*)
| Expr (e : lang.expr)
.
End expr.

Lemma expr_ind (P : expr → Prop) :
  (∀ (x : var_name), P (Var x)) →
  (∀ (l : loc), P (Loc l)) →
  (∀ (v : val), P (Val v)) →
  (∀ (op : un_op) (ot : op_type) (e : expr), P e → P (UnOp op ot e)) →
  (∀ (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : expr), P e1 → P e2 → P (BinOp op ot1 ot2 e1 e2)) →
  (∀ (op : un_op) (ot : op_type) (e : expr), P e → P (CheckUnOp op ot e)) →
  (∀ (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : expr), P e1 → P e2 → P (CheckBinOp op ot1 ot2 e1 e2)) →
  (∀ (ot1 : op_type) (e1 e2 : expr), P e1 → P e2 → P (CopyAllocId ot1 e1 e2)) →
  (∀ (o : order) (ot : op_type) (mc : bool) (e : expr), P e → P (Deref o ot mc e)) →
  (∀ (ot : op_type) (e1 e2 e3 : expr), P e1 → P e2 → P e3 → P (CAS ot e1 e2 e3)) →
  (∀ (op : atomic_rmw_op) (ot : op_type) (e1 e2 : expr), P e1 → P e2 → P (AtomicRMW op ot e1 e2)) →
  (∀ (f : expr) (eκs : list string) (etys : list rust_type) (args : list expr), P f → Forall P args → P (Call f eκs etys args)) →
  (∀ (es : list expr), Forall P es → P (Concat es)) →
  (∀ (ot : op_type) (e1 e2 e3 : expr), P e1 → P e2 → P e3 → P (IfE ot e1 e2 e3)) →
  (∀ (e_size : expr) (e_align : expr), P e_size → P e_align → P (Alloc e_size e_align)) →
  (∀ (e : expr), P e → P (SkipE e)) →
  (P StuckE) →
  (∀ (ot1 ot2 : op_type) (rit : int_type) (e1 e2 : expr), P e1 → P e2 → P (LogicalAnd ot1 ot2 rit e1 e2)) →
  (∀ (ot1 ot2 : op_type) (rit : int_type) (e1 e2 : expr), P e1 → P e2 → P (LogicalOr ot1 ot2 rit e1 e2)) →
  (∀ (o : order) (ot : op_type) (mc : bool) (e : expr), P e → P (Move o ot mc e)) →
  (∀ (o : order) (ot : op_type) (mc : bool) (e : expr), P e → P (Copy o ot mc e)) →
  (∀ (m : mutability) (e : expr), P e → P (AddrOf m e)) →
  (∀ (e : expr), P e → P (LValue e)) →
  (∀ (e : expr) (s : struct_layout_spec) (m : var_name), P e → P (GetMember e s m)) →
  (∀ (e : expr) (ul : union_layout_spec) (m : var_name), P e → P (GetMemberUnion e ul m)) →
  (∀ (e : expr) (els : enum_layout_spec), P e → P (EnumDiscriminant els e)) →
  (∀ (e : expr) (els : enum_layout_spec) (variant : var_name), P e → P (EnumData els variant e)) →
  (∀ (s : struct_layout_spec) (m : var_name), P (OffsetOf s m)) →
  (∀ (ul : union_layout_spec) (m : var_name), P (OffsetOfUnion ul m)) →
  (∀ (n : nat) (A : Type) (a : A) (e : expr), P e → P (AnnotExpr n a e)) →
  (∀ (a : location_info) (e : expr), P e → P (LocInfoE a e)) →
  (∀ (ly : struct_layout_spec) (fs : list (string * expr)), Forall P fs.*2 → P (StructInit ly fs)) →
  (∀ (els : enum_layout_spec) (variant : var_name) (ty : rust_enum_def) (e : expr), P e → P (EnumInit els variant ty e)) →
  (∀ (m : mutability) (ty : option rust_type) (κn : string) (e : expr), P e → P (Borrow m κn ty e)) →
  (∀ (e : lang.expr), P (Expr e)) → ∀ (e : expr), P e.
Proof.
  move => *. generalize dependent P => P. match goal with | e : expr |- _ => revert e end.
  fix FIX 1. move => [ ^e] => ??????????? Hcall Hconcat ?????????????????? Hstruct Henum Hbor ?.
  12: {
    apply Hcall; [ |apply Forall_true => ?]; by apply: FIX.
  }
  12: {
    apply Hconcat. apply Forall_true => ?. by apply: FIX.
  }
  30: {
    apply Hstruct. apply Forall_fmap. apply Forall_true => ?. by apply: FIX.
  }
  all: auto.
Qed.

Fixpoint to_expr `{!LayoutAlg} (e : expr) : lang.expr :=
  match e with
  | Val v => v
  | Loc l => val_of_loc l
  | Var x => lang.Var x
  | UnOp op ot e  => lang.UnOp op ot (to_expr e)
  | BinOp op ot1 ot2 e1 e2 => lang.BinOp op ot1 ot2 (to_expr e1) (to_expr e2)
  | CheckUnOp op ot e  => lang.CheckUnOp op ot (to_expr e)
  | CheckBinOp op ot1 ot2 e1 e2 => lang.CheckBinOp op ot1 ot2 (to_expr e1) (to_expr e2)
  | CopyAllocId ot1 e1 e2 => lang.CopyAllocId ot1 (to_expr e1) (to_expr e2)
  | Deref o ot mc e => lang.Deref o ot mc (to_expr e)
  | CAS ot e1 e2 e3 => lang.CAS ot (to_expr e1) (to_expr e2) (to_expr e3)
  | AtomicRMW op ot e1 e2 => lang.AtomicRMW op ot (to_expr e1) (to_expr e2)
  | Call f eκs etys args => notation.CallE (to_expr f) eκs etys (to_expr <$> args)
  | Concat es => lang.Concat (to_expr <$> es)
  | IfE ot e1 e2 e3 => lang.IfE ot (to_expr e1) (to_expr e2) (to_expr e3)
  | Alloc e_size e_align => lang.Alloc (to_expr e_size) (to_expr e_align)
  | SkipE e => lang.SkipE (to_expr e)
  | StuckE => lang.StuckE
  | LogicalAnd ot1 ot2 rit e1 e2 => notation.LogicalAnd ot1 ot2 rit (to_expr e1) (to_expr e2)
  | LogicalOr ot1 ot2 rit e1 e2 => notation.LogicalOr ot1 ot2 rit (to_expr e1) (to_expr e2)
  | Move o ot mc e => notation.Move o ot mc (to_expr e)
  | Copy o ot mc e => notation.Copy o ot mc (to_expr e)
  | AddrOf m e => notation.Raw m (to_expr e)
  | LValue e => notation.LValue (to_expr e)
  | AnnotExpr n a e => notation.AnnotExpr n a (to_expr e)
  | LocInfoE a e => notation.LocInfo a (to_expr e)
  | StructInit ly fs => notation.StructInit ly (prod_map id to_expr <$> fs)
  | EnumInit en variant ty e => notation.EnumInit en variant ty (to_expr e)
  | GetMember e s m => notation.GetMember (to_expr e) s m
  | GetMemberUnion e ul m => notation.GetMemberUnion (to_expr e) ul m
  | EnumDiscriminant els e => notation.EnumDiscriminant els (to_expr e)
  | EnumData els variant e => notation.EnumData els variant (to_expr e)
  | OffsetOf s m => notation.OffsetOf s m
  | OffsetOfUnion ul m => notation.OffsetOfUnion ul m
  | Borrow m κn ty e => notation.Ref m κn ty (to_expr e)
  | Expr e => e
  end.

Ltac of_expr e :=
  lazymatch e with
  | [] => constr:(@nil expr)
  | ?e :: ?es =>
    let e := of_expr e in
    let es := of_expr es in
    constr:(e :: es)

  | lang.Val (val.val_of_loc ?l) => constr:(Loc l)
  | notation.Raw ?m ?e =>
    let e := of_expr e in constr:(AddrOf m e)
  | notation.LValue ?e =>
    let e := of_expr e in constr:(LValue e)
  | notation.AnnotExpr ?n ?a ?e =>
    let e := of_expr e in constr:(AnnotExpr n a e)
  | notation.Ref ?m ?κn ?ty ?e =>
    let e := of_expr e in constr:(Borrow m κn ty e)
  | notation.LocInfo ?a ?e =>
    let e := of_expr e in constr:(LocInfoE a e)
  | notation.StructInit ?ly ?fs =>
    let fs := of_field_expr fs in constr:(StructInit ly fs)
  | notation.EnumInit ?en ?variant ?ty ?e =>
    let e := of_expr e in constr:(EnumInit en variant ty e)
  | notation.GetMember ?e ?s ?m =>
    let e := of_expr e in constr:(GetMember e s m)
  | notation.GetMemberUnion ?e ?ul ?m =>
    let e := of_expr e in constr:(GetMemberUnion e ul m)
  | notation.EnumDiscriminant ?els ?e =>
    let e := of_expr e in constr:(EnumDiscriminant els e)
  | notation.EnumData ?els ?variant ?e =>
    let e := of_expr e in constr:(EnumData els variant e)
  | notation.OffsetOf ?s ?m => constr:(OffsetOf s m)
  | notation.OffsetOfUnion ?ul ?m => constr:(OffsetOfUnion ul m)
  | notation.LogicalAnd ?ot1 ?ot2 ?rit ?e1 ?e2 =>
    let e1 := of_expr e1 in
    let e2 := of_expr e2 in
    constr:(LogicalAnd ot1 ot2 rit e1 e2)
  | notation.LogicalOr ?ot1 ?ot2 ?rit ?e1 ?e2 =>
    let e1 := of_expr e1 in
    let e2 := of_expr e2 in
    constr:(LogicalOr ot1 ot2 rit e1 e2)
  | notation.Move ?o ?ot ?mc ?e =>
    let e := of_expr e in constr:(Move o ot mc e)
  | notation.Copy ?o ?ot ?mc ?e =>
    let e := of_expr e in constr:(Copy o ot mc e)
  | lang.Val ?x => constr:(Val x)
  | lang.Var ?x => constr:(Var x)
  | lang.UnOp ?op ?ot ?e =>
    let e := of_expr e in constr:(UnOp op ot e)
  | lang.BinOp ?op ?ot1 ?ot2 ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(BinOp op ot1 ot2 e1 e2)
  | lang.CheckUnOp ?op ?ot ?e =>
    let e := of_expr e in constr:(CheckUnOp op ot e)
  | lang.CheckBinOp ?op ?ot1 ?ot2 ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(CheckBinOp op ot1 ot2 e1 e2)
  | lang.CopyAllocId ?ot1 ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(CopyAllocId ot1 e1 e2)
  | lang.Deref ?o ?ot ?mc ?e =>
    let e := of_expr e in constr:(Deref o ot mc e)
  | lang.CAS ?ot ?e1 ?e2 ?e3 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in let e3 := of_expr e3 in constr:(CAS ot e1 e2 e3)
  | lang.AtomicRMW ?op ?ot ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(AtomicRMW op ot e1 e2)
  | notation.CallE ?f ?eκs ?etys ?args =>
    let f := of_expr f in
    let args := of_expr args in constr:(Call f eκs etys args)
  | lang.Concat ?es =>
    let es := of_expr es in constr:(Concat es)
  | lang.IfE ?ot ?e1 ?e2 ?e3 =>
    let e1 := of_expr e1 in
    let e2 := of_expr e2 in
    let e3 := of_expr e3 in
    constr:(IfE ot e1 e2 e3)
  | lang.Alloc ?e_size ?e_align =>
    let e_size := of_expr e_size in
    let e_align := of_expr e_align in
    constr:(Alloc e_size e_align)
  | lang.SkipE ?e =>
    let e := of_expr e in constr:(SkipE e)
  | lang.StuckE => constr:(StuckE e)
  | _ => constr:(Expr e)
  end
with of_field_expr fs :=
  lazymatch fs with
  | [] => constr:(@nil (string * expr))
  | (?id, ?e) :: ?fs =>
    let e := of_expr e in
    let fs := of_field_expr fs in
    constr:((id, e) :: fs)
  end.

Inductive ectx_item :=
| UnOpCtx (op : un_op) (ot : op_type)
| BinOpLCtx (op : bin_op) (ot1 ot2 : op_type) (e2 : expr)
| BinOpRCtx (op : bin_op) (ot1 ot2 : op_type) (v1 : val)
| CheckUnOpCtx (op : un_op) (ot : op_type)
| CheckBinOpLCtx (op : bin_op) (ot1 ot2 : op_type) (e2 : expr)
| CheckBinOpRCtx (op : bin_op) (ot1 ot2 : op_type) (v1 : val)
| CopyAllocIdLCtx (ot1 : op_type) (e2 : expr)
| CopyAllocIdRCtx (ot1 : op_type) (v1 : val)
| DerefCtx (o : order) (l : op_type) (mc : bool)
| CASLCtx (ot : op_type) (e2 e3 : expr)
| CASMCtx (ot : op_type) (v1 : val) (e3 : expr)
| CASRCtx (ot : op_type) (v1 v2 : val)
| AtomicRMWLCtx (op : atomic_rmw_op) (ot : op_type) (e2 : expr)
| AtomicRMWRCtx (op : atomic_rmw_op) (ot : op_type) (v1 : val)
| CallLCtx (eκs : list string) (etys : list rust_type) (args : list expr)
| CallRCtx (f : val) (eκs : list string) (etys : list rust_type) (vl : list val) (el : list expr)
| ConcatCtx (vs : list val) (es : list expr)
| IfECtx (ot : op_type) (e2 e3 : expr)
| AllocLCtx (e_align : expr)
| AllocRCtx (v_size : val)
| SkipECtx
(* new constructors *)
| MoveCtx (o : order) (ot : op_type) (mc : bool)
| CopyCtx (o : order) (ot : op_type) (mc : bool)
| AddrOfCtx (m : mutability)
| LValueCtx
| AnnotExprCtx (n : nat) {A} (a : A)
| LocInfoECtx (a : location_info)
| BorrowCtx (m : mutability) (κn : string) (ty : option rust_type)
(* the following would not work, thus we don't have a context, but prove a specialized bind rule*)
(*| StructInitCtx (ly : struct_layout) (vfs : list (string * val)) (id : string) (efs : list (string * expr))*)
(* same for EnumInit, because it uses StructInit internally *)
| GetMemberCtx (s : struct_layout_spec) (m : var_name)
| GetMemberUnionCtx (ul : union_layout_spec) (m : var_name)
| EnumDiscriminantCtx (els : enum_layout_spec)
| EnumDataCtx (els : enum_layout_spec) (variant : var_name)
.

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | UnOpCtx op ot => UnOp op ot e
  | BinOpLCtx op ot1 ot2 e2 => BinOp op ot1 ot2 e e2
  | BinOpRCtx op ot1 ot2 v1 => BinOp op ot1 ot2 (Val v1) e
  | CheckUnOpCtx op ot => CheckUnOp op ot e
  | CheckBinOpLCtx op ot1 ot2 e2 => CheckBinOp op ot1 ot2 e e2
  | CheckBinOpRCtx op ot1 ot2 v1 => CheckBinOp op ot1 ot2 (Val v1) e
  | CopyAllocIdLCtx ot1 e2 => CopyAllocId ot1 e e2
  | CopyAllocIdRCtx ot1 v1 => CopyAllocId ot1 (Val v1) e
  | DerefCtx o l mc => Deref o l mc e
  | CASLCtx ot e2 e3 => CAS ot e e2 e3
  | CASMCtx ot v1 e3 => CAS ot (Val v1) e e3
  | CASRCtx ot v1 v2 => CAS ot (Val v1) (Val v2) e
  | AtomicRMWLCtx op ot e2 => AtomicRMW op ot e e2
  | AtomicRMWRCtx op ot v1 => AtomicRMW op ot (Val v1) e
  | CallLCtx eκs etys args => Call e eκs etys args
  | CallRCtx f eκs etys vl el => Call (Val f) eκs etys ((Val <$> vl) ++ e :: el)
  | ConcatCtx vs es => Concat ((Val <$> vs) ++ e :: es)
  | IfECtx ot e2 e3 => IfE ot e e2 e3
  | AllocLCtx e_align => Alloc e e_align
  | AllocRCtx v_size => Alloc (Val v_size) e
  | SkipECtx => SkipE e
  | MoveCtx o l mc => Move o l mc e
  | CopyCtx o l mc => Copy o l mc e
  | AddrOfCtx m => AddrOf m e
  | LValueCtx => LValue e
  | AnnotExprCtx n a => AnnotExpr n a e
  | LocInfoECtx a => LocInfoE a e
  | BorrowCtx m κn ty => Borrow m κn ty e
  | GetMemberCtx s m => GetMember e s m
  | GetMemberUnionCtx ul m => GetMemberUnion e ul m
  | EnumDiscriminantCtx els => EnumDiscriminant els e
  | EnumDataCtx els variant => EnumData els variant e
  end.

Definition fill (K : list ectx_item) (e : expr) : expr := foldl (flip fill_item) e K.
Lemma fill_app (K1 K2 : list ectx_item) e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
Proof. apply foldl_app. Qed.

Fixpoint find_expr_fill (e : expr) (bind_val : bool) : option (list ectx_item * expr) :=
  match e with
  | Var _ => None
  | Val v => if bind_val then Some ([], Val v) else None
  | Loc l => if bind_val then Some ([], Loc l) else None
  | Expr e => Some ([], Expr e)
  | StuckE => Some ([], StuckE)
  | UnOp op ot e1 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [UnOpCtx op ot], e') else Some ([], e)
  | BinOp op ot1 ot2 e1 e2 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [BinOpLCtx op ot1 ot2 e2], e')
    else if find_expr_fill e2 bind_val is Some (Ks, e') then
           if e1 is Val v then Some (Ks ++ [BinOpRCtx op ot1 ot2 v], e') else None
         else Some ([], e)
  | CheckUnOp op ot e1 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [CheckUnOpCtx op ot], e') else Some ([], e)
  | CheckBinOp op ot1 ot2 e1 e2 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [CheckBinOpLCtx op ot1 ot2 e2], e')
    else if find_expr_fill e2 bind_val is Some (Ks, e') then
           if e1 is Val v then Some (Ks ++ [CheckBinOpRCtx op ot1 ot2 v], e') else None
         else Some ([], e)
  | CopyAllocId ot1 e1 e2 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [CopyAllocIdLCtx ot1 e2], e')
    else if find_expr_fill e2 bind_val is Some (Ks, e') then
           if e1 is Val v then Some (Ks ++ [CopyAllocIdRCtx ot1 v], e') else None
         else Some ([], e)
  | CAS ot e1 e2 e3 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [CASLCtx ot e2 e3], e')
    else if find_expr_fill e2 bind_val is Some (Ks, e') then
      if e1 is Val v1 then Some (Ks ++ [CASMCtx ot v1 e3], e') else None
    else if find_expr_fill e3 bind_val is Some (Ks, e') then
      if e1 is Val v1 then if e2 is Val v2 then Some (Ks ++ [CASRCtx ot v1 v2], e') else None else None
    else Some ([], e)
  | AtomicRMW op ot e1 e2 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [AtomicRMWLCtx op ot e2], e')
    else if find_expr_fill e2 bind_val is Some (Ks, e') then
           if e1 is Val v1 then Some (Ks ++ [AtomicRMWRCtx op ot v1], e') else None
         else Some ([], e)
  | Call f eκs etys args =>
    if find_expr_fill f bind_val is Some (Ks, e') then
      Some (Ks ++ [CallLCtx eκs etys args], e') else
      (* TODO: handle arguments? *) None
  | Concat _ | OffsetOf _ _ | OffsetOfUnion _ _ | LogicalAnd _ _ _ _ _ | LogicalOr _ _ _ _ _ => None
  | IfE ot e1 e2 e3 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [IfECtx ot e2 e3], e') else Some ([], e)
  | Alloc e1 e2 =>
      if find_expr_fill e1 bind_val is Some (Ks, e') then
        Some (Ks ++ [AllocLCtx e2], e')
      else if find_expr_fill e2 bind_val is Some (Ks, e') then
        if e1 is Val v1 then Some (Ks ++ [AllocRCtx v1], e') else None
      else Some ([], e)
  | SkipE e1 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [SkipECtx], e') else Some ([], e)
  | Deref o ly mc e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [DerefCtx o ly mc], e') else Some ([], e)
  | Move o ly mc e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [MoveCtx o ly mc], e') else Some ([], e)
  | Copy o ly mc e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [CopyCtx o ly mc], e') else Some ([], e)
  | AddrOf m e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [AddrOfCtx m], e') else Some ([], e)
  | LValue e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [LValueCtx], e') else Some ([], e)
  | AnnotExpr n a e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [AnnotExprCtx n a], e') else Some ([], e)
  | LocInfoE a e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [LocInfoECtx a], e') else Some ([], e)
  | Borrow m κn ty e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [BorrowCtx m κn ty], e') else Some ([], e)
  | StructInit _ _ => None
  | EnumInit _ _ _ _ => None
  | GetMember e1 s m => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [GetMemberCtx s m], e') else Some ([], e)
  | GetMemberUnion e1 ul m => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [GetMemberUnionCtx ul m], e') else Some ([], e)
  | EnumDiscriminant els e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [EnumDiscriminantCtx els], e') else Some ([], e)
  | EnumData els variant e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [EnumDataCtx els variant], e') else Some ([], e)
  end.

Lemma find_expr_fill_correct b e Ks e':
  find_expr_fill e b = Some (Ks, e') → e = fill Ks e'.
Proof.
  elim: e Ks e' => //= *;
     repeat (try case_match; simpl in *; simplify_eq => /=);
     rewrite ?fill_app /=; f_equal; eauto.
Qed.

Lemma ectx_item_correct `{!LayoutAlg} π Ks:
  ∃ Ks', ∀ e, to_rtexpr π (to_expr (fill Ks e)) = ectxi_language.fill Ks' (to_rtexpr π (to_expr e)).
Proof.
  elim/rev_ind: Ks; [by exists []|].
  move => K Ks [Ks' IH].

  eexists (Ks' ++ ((λ a, ExprCtx a π) <$> ?[K])) => ?. rewrite fill_app ectxi_language.fill_app /= -IH.
  only [K]: (destruct K; [
    apply: [lang.UnOpCtx _ _]|
    apply: [lang.BinOpLCtx _ _ _ _]|
    apply: [lang.BinOpRCtx _ _ _ _]|
    apply: [lang.CheckUnOpCtx _ _]|
    apply: [lang.CheckBinOpLCtx _ _ _ _]|
    apply: [lang.CheckBinOpRCtx _ _ _ _]|
    apply: [lang.CopyAllocIdLCtx _ _]|
    apply: [lang.CopyAllocIdRCtx _ _]|
    apply: [lang.DerefCtx _ _ _]|
    apply: [lang.CASLCtx _ _ _]|
    apply: [lang.CASMCtx _ _ _]|
    apply: [lang.CASRCtx _ _ _]|
    apply: [lang.AtomicRMWLCtx _ _ _]|
    apply: [lang.AtomicRMWRCtx _ _ _]|
    apply: [lang.CallLCtx _]|
    apply: [lang.CallRCtx _ _ _]|
    apply: [lang.ConcatCtx _ _]|
    apply: [lang.IfECtx _ _ _]|
    apply: [lang.AllocLCtx _]|
    apply: [lang.AllocRCtx _]|
    apply: [lang.SkipECtx]|
    apply: [lang.SkipECtx; lang.DerefCtx _ _ _]|
    apply: [lang.SkipECtx; lang.DerefCtx _ _ _]|
    apply: [lang.SkipECtx]|
    apply: []|
    apply: (replicate n lang.SkipECtx)|
    apply: []|
    apply: [lang.SkipECtx; lang.SkipECtx]|
    apply: [lang.BinOpRCtx _ _ _ _]|
    apply: []|
    apply: [lang.BinOpRCtx _ _ _ _; lang.DerefCtx _ _ _]|
    apply: [lang.BinOpRCtx _ _ _ _]|..
  ]).
  move: K => [|||||||||||||||||||||||||n||||||] * //=.
  - (** Call *)
    do 2 f_equal.
    rewrite !fmap_app !fmap_cons. repeat f_equal; eauto.
    rewrite -!list_fmap_compose. by apply: list_fmap_ext.
  - (** Concat *)
    do 2 f_equal.
    rewrite !fmap_app !fmap_cons. repeat f_equal; eauto.
    rewrite -!list_fmap_compose. by apply: list_fmap_ext.
  - (** AnnotExpr *)
    elim: n; eauto.
    move => n. by rewrite /notation.AnnotExpr replicate_S_end fmap_app ectxi_language.fill_app /= => ->.
Qed.

Lemma to_expr_val_list `{!LayoutAlg} (vl : list val) :
  to_expr <$> (Val <$> vl) = lang.Val <$> vl.
Proof. elim: vl => //; csimpl => *. by f_equal. Qed.

(*** Statements *)

Section stmt.
Local Unset Elimination Schemes.
Inductive stmt :=
| Goto (b : label)
| Return (e : expr)
| IfS (ot : op_type) (join : option label) (e : expr) (s1 s2 : stmt)
| Switch (it : int_type) (e : expr) (m : gmap Z nat) (bs : list stmt) (def : stmt)
| Assign (o : order) (ot : op_type) (e1 e2 : expr) (s : stmt)
| AssignSE (o : order) (ot : op_type) (e1 e2 : expr) (s : stmt)
| Free (e_size : expr) (e_align : expr) (e : expr) (s : stmt)
| SkipS (s : stmt)
| StuckS
| ExprS (e : expr) (s : stmt)
| Assert (ot : op_type) (e : expr) (s : stmt)
| AnnotStmt (n : nat) {A} (a : A) (s : stmt)
| LocInfoS (a : location_info) (s : stmt)
| LocalLive (x : var_name) (st : syn_type) (s : stmt)
| LocalDead (x : var_name) (s : stmt)
(* for opaque statements *)
| Stmt (s : lang.stmt).
End stmt.

Lemma stmt_ind (P : stmt → Prop):
  (∀ b : label, P (Goto b)) →
  (∀ e : expr, P (Return e)) →
  (∀ (ot : op_type) (join : option label) (e : expr) (s1 : stmt), P s1 → ∀ s2 : stmt, P s2 → P (IfS ot join e s1 s2)) →
  (∀ (it : int_type) (e : expr) (m : gmap Z nat) (bs : list stmt) (def : stmt), P def → Forall P bs → P (Switch it e m bs def)) →
  (∀ (o : order) (ot : op_type) (e1 e2 : expr) (s : stmt), P s → P (Assign o ot e1 e2 s)) →
  (∀ (o : order) (ot : op_type) (e1 e2 : expr) (s : stmt), P s → P (AssignSE o ot e1 e2 s)) →
  (∀ (e_size : expr) (e_align : expr) (e : expr) (s : stmt), P s → P (Free e_size e_align e s)) →
  (∀ s : stmt, P s → P (SkipS s)) →
  (P StuckS) →
  (∀ (e : expr) (s : stmt), P s → P (ExprS e s)) →
  (∀ (ot : op_type) (e : expr) (s : stmt), P s → P (Assert ot e s)) →
  (∀ (n : nat) (A : Type) (a : A) (s : stmt), P s → P (AnnotStmt n a s)) →
  (∀ (a : location_info) (s : stmt), P s → P (LocInfoS a s)) →
  (∀ (x : var_name) (st : syn_type) (s : stmt), P s → P (LocalLive x st s)) →
  (∀ (x : var_name) (s : stmt), P s → P (LocalDead x s)) →
  (∀ s : lang.stmt, P (Stmt s)) → ∀ s : stmt, P s.
Proof.
  move => *. generalize dependent P => P. match goal with | s : stmt |- _ => revert s end.
  fix FIX 1. move => [ ^s] ??? Hswitch *. 4: {
    apply Hswitch; first by apply: FIX. elim: sbs; auto.
  }
  all: auto.
Qed.


Fixpoint to_stmt `{LayoutAlg} (s : stmt) : lang.stmt :=
  match s with
  | Goto b => lang.Goto b
  | Return e => lang.Return (to_expr e)
  | IfS ot join e s1 s2 => (if{ot, join}: to_expr e then to_stmt s1 else to_stmt s2)%E
  | Switch it e m bs def => lang.Switch it (to_expr e) m (to_stmt <$> bs) (to_stmt def)
  | Assign o ot e1 e2 s => lang.Assign o ot (to_expr e1) (to_expr e2) (to_stmt s)
  | AssignSE o ot e1 e2 s => notation.AssignSE o ot (to_expr e1) (to_expr e2) (to_stmt s)
  | Free e_size e_align e s => lang.Free (to_expr e_size) (to_expr e_align) (to_expr e) (to_stmt s)
  | SkipS s => lang.SkipS (to_stmt s)
  | StuckS => lang.StuckS
  | ExprS e s => lang.ExprS (to_expr e) (to_stmt s)
  | Assert ot e s => notation.Assert ot (to_expr e) (to_stmt s)
  | AnnotStmt n a s => notation.AnnotStmt n a (to_stmt s)
  | LocInfoS a s => notation.LocInfo a (to_stmt s)
  | LocalLive x st s => notation.LocalLiveSt x st (to_stmt s)
  | LocalDead x s => notation.LocalDeadSt x (to_stmt s)
  | Stmt s => s
  end.

Ltac of_stmt s :=
  lazymatch s with
  | [] => constr:(@nil stmt)
  | ?s :: ?ss =>
    let s := of_stmt s in
    let ss := of_stmt ss in
    constr:(s :: ss)

  | notation.AnnotStmt ?n ?a ?s =>
    let s := of_stmt s in
    constr:(AnnotStmt n a s)
  | notation.LocInfo ?a ?s =>
    let s := of_stmt s in
    constr:(LocInfoS a s)
  | notation.LocalLiveSt ?x ?st ?s =>
    let s := of_stmt s in
    constr:(LocalLive x st s)
  | notation.LocalDeadSt ?x ?s =>
    let s := of_stmt s in
    constr:(LocalDead x s)
  | (assert{?ot}: ?e ; ?s)%E =>
    let e := of_expr e in
    let s := of_stmt s in
    constr:(Assert ot e s)
  | (if{?ot, ?join}: ?e then ?s1 else ?s2)%E =>
    let e := of_expr e in
    let s1 := of_stmt s1 in
    let s2 := of_stmt s2 in
    constr:(IfS ot join e s1 s2)
  | lang.Goto ?b => constr:(Goto b)
  | lang.Return ?e =>
    let e := of_expr e in constr:(Return e)
  | lang.Switch ?it ?e ?m ?bs ?def =>
    let e := of_expr e in
    let bs := of_stmt bs in
    let def := of_stmt def in
    constr:(Switch it e m bs def)
  | lang.Assign ?o ?ot ?e1 ?e2 ?s =>
    let e1 := of_expr e1 in
    let e2 := of_expr e2 in
    let s := of_stmt s in
    constr:(Assign o ot e1 e2 s)
  | notation.AssignSE ?o ?ot ?e1 ?e2 ?s =>
    let e1 := of_expr e1 in
    let e2 := of_expr e2 in
    let s := of_stmt s in
    constr:(AssignSE o ot e1 e2 s)
  | lang.Free ?e_size ?e_align ?e ?s =>
    let e_size := of_expr e_size in
    let e_align := of_expr e_align in
    let e := of_expr e in
    let s := of_stmt s in
    constr:(Free e_size e_align e s)
  | lang.SkipS ?s =>
    let s := of_stmt s in
    constr:(SkipS s)
  | lang.StuckS => constr:(StuckS)
  | lang.ExprS ?e ?s =>
    let e := of_expr e in
    let s := of_stmt s in
    constr:(ExprS e s)
  | _ => constr:(Stmt s)
  end.

Inductive stmt_ectx :=
| AssignRCtx (o : order) (ot : op_type) (e1 : expr) (s : stmt)
| AssignLCtx (o : order) (ot : op_type) (v2 : val) (s : stmt)
| AssignSERCtx (o : order) (ot : op_type) (e1 : expr) (s : stmt)
| AssignSELCtx (o : order) (ot : op_type) (v2 : val) (s : stmt)
| ReturnCtx
| IfSCtx (ot : op_type) (join: option label) (s1 s2 : stmt)
| SwitchCtx (it : int_type) (m: gmap Z nat) (bs : list stmt) (def : stmt)
| ExprSCtx (s : stmt)
| AssertCtx (ot : op_type) (s : stmt)
| FreeLCtx (e_align : expr) (e : expr) (s : stmt)
| FreeMCtx (v_size : val) (e : expr) (s : stmt)
| FreeRCtx (v_size : val) (v_align : val) (s : stmt)
.

Definition stmt_fill (Ki : stmt_ectx) (e : expr) : stmt :=
  match Ki with
  | AssignRCtx o ot e1 s => Assign o ot e1 e s
  | AssignLCtx o ot v2 s => Assign o ot e (Val v2) s
  | AssignSERCtx o ot e1 s => AssignSE o ot e1 e s
  | AssignSELCtx o ot v2 s => AssignSE o ot e (Val v2) s
  | ReturnCtx => Return e
  | ExprSCtx s => ExprS e s
  | IfSCtx ot join s1 s2 => IfS ot join e s1 s2
  | SwitchCtx it m bs def => Switch it e m bs def
  | AssertCtx ot s => Assert ot e s
  | FreeLCtx e_align e' s => Free e e_align e' s
  | FreeMCtx v_size e' s => Free (Val v_size) e e' s
  | FreeRCtx v_size v_align s => Free (Val v_size) (Val v_align) e s
  end.

Definition find_stmt_fill (s : stmt) : option (stmt_ectx * expr) :=
  match s with
  | Goto _ | Stmt _ | AnnotStmt _ _ _ | LocInfoS _ _ | SkipS _ | StuckS | LocalLive _ _ _ | LocalDead _ _ => None
  | Return e => if e is (Val v) then None else Some (ReturnCtx, e)
  | ExprS e s => if e is (Val v) then None else Some (ExprSCtx s, e)
  | IfS ot join e s1 s2 => if e is (Val v) then None else Some (IfSCtx ot join s1 s2, e)
  | Switch it e m bs def => if e is (Val v) then None else Some (SwitchCtx it m bs def, e)
  | Assign o ot e1 e2 s => if e2 is (Val v) then if e1 is (Val v) then None else Some (AssignLCtx o ot v s, e1) else Some (AssignRCtx o ot e1 s, e2)
  | AssignSE o ot e1 e2 s => if e2 is (Val v) then if e1 is (Val v) then None else Some (AssignSELCtx o ot v s, e1) else Some (AssignSERCtx o ot e1 s, e2)
  | Assert ot e s => if e is (Val v) then None else Some (AssertCtx ot s, e)
  | Free e_size e_align e s =>
      if e_size is (Val v_size) then
        if e_align is (Val v_align) then
          if e is (Val v) then None
          else Some (FreeRCtx v_size v_align s, e)
        else Some (FreeMCtx v_size e s, e_align)
      else Some (FreeLCtx e_align e s, e_size)
  end.

Lemma find_stmt_fill_correct s Ks e:
  find_stmt_fill s = Some (Ks, e) → s = stmt_fill Ks e.
Proof.
  destruct s => *; repeat (try case_match; simpl in *; simplify_eq => //).
Qed.

Lemma stmt_fill_correct `{!LayoutAlg} Ks π rf:
  ∃ Ks', ∀ e, to_rtstmt π rf (to_stmt (stmt_fill Ks e)) = ectxi_language.fill Ks' (to_rtexpr π (to_expr e)).
Proof.
  move: Ks => [] *; [
  eexists ([StmtCtx (lang.AssignRCtx _ _ _ _) π rf])|
  eexists ([StmtCtx (lang.AssignLCtx _ _ _ _) π rf])|
  eexists ([StmtCtx (lang.AssignRCtx _ _ _ _) π rf])|
  eexists ([ExprCtx lang.SkipECtx π; StmtCtx (lang.AssignLCtx _ _ _ _) π rf])|
  eexists ([StmtCtx (lang.ReturnCtx) π rf])|
  eexists ([StmtCtx (lang.IfSCtx _ _ _ _) π rf])|
  eexists ([StmtCtx (lang.SwitchCtx _ _ _ _) π rf])|
  eexists ([StmtCtx (lang.ExprSCtx _) π rf])|
  eexists ([StmtCtx (lang.IfSCtx _ _ _ _) π rf])|
  eexists ([StmtCtx (lang.FreeLCtx _ _ _) π rf])|
  eexists ([StmtCtx (lang.FreeMCtx _ _ _) π rf])|
  eexists ([StmtCtx (lang.FreeRCtx _ _ _) π rf])|
..] => //=.
Qed.

(*** Substitution *)
Definition list_find_fast {A} (P : A → Prop) `{!∀ x, Decision (P x)} :=
  fix go (l : list A) : option A :=
    match l with
    | [] => None
    | x :: l => if decide (P x) then Some x else go l
    end.
Global Instance: Params (@list_find_fast) 3 := {}.

Lemma Forall_eq_fmap {A B} (xs : list A) (f1 f2 : A → B) :
  Forall (λ x, f1 x = f2 x) xs → f1 <$> xs = f2 <$> xs.
Proof. elim => //. csimpl. congruence. Qed.

Lemma fmap_snd_prod_map {A B C} (l : list (A * B)) (f1 f2 : B → C)  :
  f1 <$> l.*2 = f2 <$> l.*2 →
  prod_map id f1 <$> l = prod_map id f2 <$> l.
Proof. elim: l => // -[??] ? IH. csimpl => -[??]. rewrite IH //. congruence. Qed.
End W.
Arguments W.to_expr : simpl never.
Arguments W.to_stmt : simpl never.

Ltac inv_stmt_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : context [to_val (of_val _)] |- _ => rewrite to_of_val in H
  | H : stmt_step ?e _ _ _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable *)
(*      and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Ltac inv_expr_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : context [to_val (of_val _)] |- _ => rewrite to_of_val in H
  | H : expr_step ?e _ _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable *)
(*      and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Ltac solve_struct_obligations := done.

Ltac solve_fn_vars_nodup := intros; simpl; repeat econstructor; set_solver.
