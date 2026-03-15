From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_traits_iterator_Iterator_max_by.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma traits_iterator_Iterator_max_by_proof (π : thread_id) :
  traits_iterator_Iterator_max_by_lemma π.
Proof.
  traits_iterator_Iterator_max_by_prelude.

  rep liRStep; liShow.
  (* calling reduce *)
  liInst Hevar_x2 (λ π acc seq it_state '( *[(clos_state, γ')]),
    ClosInv π acc seq it_state clos_state ∗ ⌜γ' = γ⌝)%I.
  iRename select (∀ _ _ _ _, _)%I into "Hpres".
  rep 8 liRStep; liShow.
  iApply prove_with_subtype_default.
  iRename select (∀ _ _, _ -∗ _)%I into "Hinit".
  iSplitL "Hinit".
  { iIntros (??) "(Hclos & _) ?".
    iPoseProof ("Hinit" with "[$] [$]")as "($ & $)".
    done. }
  rep 3 liRStep.
  { iIntros (???? [[clos_state γ'] []] ?) "Hnext".
    iPoseProof ("Hpres" with "[$]") as "#Hpres'".
    iModIntro. iIntros "Hnext (Hinv & ->)".
    iPoseProof ("Hpres'" with "[$] [$]") as "(%pclos & Hpre & ? & Hcl)".
    rep liRStep; liShow.
    liInst Hevar_a pclos.
    rep liRStep; liShow.
    iPoseProof ("Hcl" with "[$]") as "(? & _)".
    rep liRStep; liShow. }
  rep liRStep; liShow.
  liInst Hevar_x2 x'0. liInst Hevar_x0 x'1.
  rep liRStep; liShow.
  liInst Hevar_x1 x'.
  rep liRStep; liShow.
  liInst Hevar_x3 x'2.
  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
