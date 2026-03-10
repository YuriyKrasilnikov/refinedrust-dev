From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_traits_iterator_Iterator_all.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma traits_iterator_Iterator_all_proof (π : thread_id) :
  traits_iterator_Iterator_all_lemma π.
Proof.
  traits_iterator_Iterator_all_prelude.

  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  (* picking an invariant for try_fold *)
  liInst Hevar_x0 (λ π _ iter '( *[f]), ClosInv π iter f.cur ∗ ⌜f.ghost = γ0⌝)%I.
  liInst Hevar_x2 P.
  rep 20 liRStep; liShow.
  { iRename select (∀ _, _)%I into "Hwand".
    iDestruct ("Hwand" with "[$] [$]") as "(%pclos & Hpre & Hnext & Hcl)".
    rep liRStep; liShow.
    liInst Hevar_a pclos.
    rep liRStep; liShow.
    iPoseProof ("Hcl" with "[$]") as "(%Heq & Hinv)".
    destruct res; simpl; rep liRStep. }
  rep <-! liRStep; liShow.
  { iRevert select (if_iOk _ _). iRevert select (if_iErr _ _).
    rep liRStep; liShow.
    liInst Hevar_x1 x'. liInst Hevar_x2 x'0.
    rep liRStep; liShow. liInst Hevar_x0 x'1.
    rep liRStep; liShow. }
  { iRevert select (if_iOk _ _). iRevert select (if_iErr _ _).
    rep liRStep; liShow.
    liInst Hevar_x1 (seq' ++ [e]). liInst Hevar_x2 x'1.
    rep liRStep; liShow.  }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
