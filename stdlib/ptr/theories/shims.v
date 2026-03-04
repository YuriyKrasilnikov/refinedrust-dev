From caesium Require Import lang notation.
From refinedrust Require Import annotations typing.

Program Definition ptr_write `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("dst", void* ); ("src", use_layout_alg' T_st)];
  f_code :=
    <["_bb0" :=
      (* NOTE: the rust impl uses copy_nonoverlapping and then asserts with an intrinsic that the validity invariant for T holds,
          but we don't have such a thing and should simply use a typed copy *)
      !{PtrOp} "dst" <-{use_op_alg' T_st} move{use_op_alg' T_st} "src";
      return zst_val
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Next Obligation. solve_fn_vars_nodup. Qed.


Program Definition ptr_read `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("src", void* )];
  f_code :=
    <["_bb0" :=
      local_live{T_st} "tmp";
      "tmp" <-{use_op_alg' T_st} copy{use_op_alg' T_st} (!{PtrOp} "src");
      return (move{use_op_alg' T_st} "tmp")
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Next Obligation. solve_fn_vars_nodup. Qed.

(* Our implementation does not actually do anything with the type parameter, it's just there to mirror the Rust API. *)
Program Definition ptr_without_provenance `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("addr", USize : layout)];
  f_code :=
    <["_bb0" :=
      local_live{PtrSynType} "ret";
      "ret" <-{PtrOp} (UnOp (CastOp PtrOp) (IntOp USize) (move{IntOp USize} "addr"));
      return (move{PtrOp} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Next Obligation. solve_fn_vars_nodup. Qed.

(** copy_nonoverlapping *)
(*
  This just does a bytewise untyped copy, matching the intended Rust semantics. The sequence of bytes does not have to be a valid representation at any type.

  fn copy_nonoverlapping<T>(size, src, dst) {
    let mut count: usize = 0;

    assert_unsafe_precondition!(
        is_aligned_and_not_null(src)
            && is_aligned_and_not_null(dst)
            && is_nonoverlapping(src, dst, count)
    );

    let src = src as *const U8;
    let dst = dst as *mut U8;
    // do a bytewise copy
    while count < size {
      // uses untyped read + assignment, NOT the typed assignment in surface Rust!
      *(dst.add(count)) = *src.add(count);
      count+=1;
    }
  }
 *)
Program Definition ptr_copy_nonoverlapping `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("src", void* ); ("dst", void* ); ("size", USize : layout)];
  f_code :=
    <["_bb0" :=
      local_live{IntSynType USize} "count";
      "count" <-{IntOp USize} i2v 0 USize;
      (* TODO: add safety checks *)
      annot{0}: StopAnnot;
      Goto "_bb_loop_head"
    ]>%E $
    <["_bb_loop_head" :=

      if{BoolOp}:
        (copy{IntOp USize} "count") <{IntOp USize, IntOp USize, U8} (copy{IntOp USize} "size")
      then
        Goto "_bb_loop_body"
      else
        Goto "_bb_loop_exit"
    ]>%E $
    <["_bb_loop_body" :=
        ((!{PtrOp} "dst") at_offset{use_layout_alg' T_st, PtrOp, IntOp USize} copy{IntOp USize} "count")
      <-{UntypedOp (use_layout_alg' T_st)}
        copy{UntypedOp (use_layout_alg' T_st)} (
          ((!{PtrOp} "src") at_offset{use_layout_alg' T_st, PtrOp, IntOp USize} copy{IntOp USize} "count"));
      "count" <-{IntOp USize} (copy{IntOp USize} "count") +{IntOp USize, IntOp USize} (i2v 1 USize);
      Goto "_bb_loop_head"
    ]>%E $
    <["_bb_loop_exit" :=
      annot{0}: StopAnnot;
      return zst_val
    ]>%E $
    ∅;
  f_init := "_bb0";
|}.
Next Obligation. solve_fn_vars_nodup. Qed.

Program Definition ptr_offset `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("self", void* ); ("count", ISize : layout)];
  f_code :=
    <["_bb0" :=
        local_live{PtrSynType} "ret";
        "ret" <-{PtrOp} ((copy{PtrOp} "self") at_offset{use_layout_alg' T_st, PtrOp, IntOp ISize} (copy{IntOp ISize} "count"));
        return (move{PtrOp} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0"
|}.
Next Obligation. solve_fn_vars_nodup. Qed.

Program Definition ptr_sub `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("self", void* ); ("count", USize : layout)];
  f_code :=
    <["_bb0" :=
        local_live{PtrSynType} "ret";
        "ret" <-{PtrOp} ((copy{PtrOp} "self") at_neg_offset{use_layout_alg' T_st, PtrOp, IntOp USize} (copy{IntOp USize} "count"));
        return (move{PtrOp} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0"
|}.
Next Obligation. solve_fn_vars_nodup. Qed.


Program Definition ptr_wrapping_offset `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("self", void* ); ("count", ISize : layout)];
  f_code :=
    <["_bb0" :=
        local_live{PtrSynType} "ret";
        "ret" <-{PtrOp} ((copy{PtrOp} "self") at_wrapping_offset{use_layout_alg' T_st, PtrOp, IntOp ISize} (copy{IntOp ISize} "count"));
        return (move{PtrOp} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0"
|}.
Next Obligation. solve_fn_vars_nodup. Qed.

Program Definition ptr_wrapping_add `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("self", void* ); ("count", USize : layout)];
  f_code :=
    <["_bb0" :=
        local_live{PtrSynType} "ret";
        "ret" <-{PtrOp} ((copy{PtrOp} "self") at_wrapping_offset{use_layout_alg' T_st, PtrOp, IntOp USize} (copy{IntOp USize} "count"));
        return (move{PtrOp} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0"
|}.
Next Obligation. solve_fn_vars_nodup. Qed.

Program Definition ptr_wrapping_sub `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("self", void* ); ("count", USize : layout)];
  f_code :=
    <["_bb0" :=
        local_live{PtrSynType} "ret";
        "ret" <-{PtrOp} ((copy{PtrOp} "self") at_wrapping_neg_offset{use_layout_alg' T_st, PtrOp, IntOp USize} (copy{IntOp USize} "count"));
        return (move{PtrOp} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0"
|}.
Next Obligation. solve_fn_vars_nodup. Qed.

Program Definition ptr_with_addr `{!LayoutAlg} (T_st : syn_type) : function := {|
  f_args := [("self", void* ); ("addr", USize : layout)];
  f_code :=
    <["_bb0" :=
        local_live{PtrSynType} "ret";
        "ret" <-{PtrOp} CopyAllocId (IntOp USize) (copy{IntOp USize} "addr") (copy{PtrOp} "self");
        return (move{PtrOp} "ret")
    ]>%E $
    ∅;
  f_init := "_bb0"
|}.
Next Obligation. solve_fn_vars_nodup. Qed.
