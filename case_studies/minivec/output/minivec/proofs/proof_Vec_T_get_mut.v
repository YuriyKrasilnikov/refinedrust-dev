From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_Vec_T_get_mut.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.
Lemma Vec_T_get_mut_proof (π : thread_id) :
  Vec_T_get_mut_lemma π.
Proof.
  Vec_T_get_mut_prelude.

  repeat liRStep. liShow.
  { iRename select (Inherit [κ0] _) into "Hinh1".
    iRename select (Inherit [κ1] _) into "Hinh2".
    liInst Hevar_x2 x'0.
    repeat liRStep; liShow.
    iApply (prove_with_subtype_inherit_manual with "Hinh1 []"); [shelve_sidecond |  | ].
    { rewrite Nat2Z.id. iIntros "$". }
    repeat liRStep; liShow.
    iApply (prove_with_subtype_inherit_manual with "Hinh2 []"); [shelve_sidecond | iIntros "$" | ].
    repeat liRStep; liShow.
  }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
