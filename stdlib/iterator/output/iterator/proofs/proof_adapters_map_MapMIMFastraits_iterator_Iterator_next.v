From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_adapters_map_MapMIMFastraits_iterator_Iterator_next.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma adapters_map_MapMIMFastraits_iterator_Iterator_next_proof (π : thread_id) :
  adapters_map_MapMIMFastraits_iterator_Iterator_next_lemma π.
Proof.
  adapters_map_MapMIMFastraits_iterator_Iterator_next_prelude.

  repeat liRStep. liShow.

  iRename select (traits_iterator_Iterator_Inv _ _ _) into "Hinv".
  iEval (rewrite /traits_iterator_Iterator_Inv/=) in "Hinv".
  unfold MapInv. iDestruct "Hinv" as "(%Inv & Hinv & Hinv_nested & Hsome & Hnone)".
  rep <-! liRStep; liShow. 
  rep liRStep; liShow.

  { (* obtain an element *)
    iRename select (traits_iterator_Iterator_Next _ _ _ _ _) into "Hnext".
    iPoseProof (li_sealed_use_pers with "Hsome") as "#Hsome'".
    iPoseProof (li_sealed_use_pers with "Hnone") as "#Hnone'".
    iPoseProof (boringly_intro with "Hnext") as "#Hnext_x".
    iPoseProof ("Hsome'" with "Hnext_x Hinv") as "(Hpre & Hinv_clos)".
    iPoseProof (boringly_intro with "Hpre") as "#Hpre_x".
    rep <-! liRStep. liShow.
    iRename select (FnOnce_PostMut _ _ _ _ _ _) into "Hpost".
    iPoseProof (boringly_intro with "Hpost") as "#Hpost_x".
    iPoseProof ("Hinv_clos" with "Hpost_x") as "Hinv".
    rep liRStep. liShow.
    liInst Hevar_e_inner r.
    rep liRStep. 
    iEval (rewrite /traits_iterator_Iterator_Inv/=).
    rewrite /MapInv.
    rep liRStep; liShow.
    liInst Hevar_Inv Inv.
    rep liRStep.
  }
  { (* no element *)
    iRename select (traits_iterator_Iterator_Next _ _ _ _ _) into "Hnext".
    iPoseProof (li_sealed_use_pers with "Hnone") as "#Hnone'".
    iPoseProof (boringly_intro with "Hnext") as "#Hnext_x".
    iPoseProof ("Hnone'" with "Hnext_x Hinv") as "Hinv".
    rep <-! liRStep. liShow. 
    rep liRStep. 
    iEval (rewrite /traits_iterator_Iterator_Inv/=).
    rewrite /MapInv.
    rep liRStep; liShow.
    liInst Hevar_Inv Inv.
    rep liRStep. }

  all: print_remaining_goal.
  Unshelve. 
  (* TODO: this is a bug in the contract...: For an instantiation, we also need to be able to assume that its elctx is okay. I.e., similar to how we add typaram_wf *)
  1: { admit. } 
  1: sidecond_solver.
  1: admit.
  1: sidecond_solver.
  1: admit.

  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Admitted.
End proof.
