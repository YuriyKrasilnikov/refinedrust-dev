From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_traits_iterator_Iterator_min.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma traits_iterator_Iterator_min_proof (π : thread_id) :
  traits_iterator_Iterator_min_lemma π.
Proof.
  traits_iterator_Iterator_min_prelude.

  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  liInst Hevar_x2 (λ π acc seq _ _, ⌜acc = min_list_cmp Ord_Selfastraits_iterator_Iterator_Item_spec_attrs.(Ord_Ord) seq None⌝)%I.
  rep liRStep; liShow.
  iApply prove_with_subtype_default.
  iSplitR. { iIntros (??) "_ $". iPureIntro. done. }
  rep liRStep; liShow.
  liInst Hevar_x2 x'0.
  liInst Hevar_x0 x'1.
  rep liRStep; liShow.


  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { rename select (_  = min_list_cmp _ _ _) into Heq.
    rewrite min_list_cmp_app. rewrite -Heq. simpl.
    rewrite min_by_Some_rev. f_equiv.
    case_bool_decide.
    + rewrite min_by_r_1; first done.
      intros Ha.
      eapply (ord_lt_irrefl a).
      eapply correct_ord_lt_trans; last apply Ha.
      done.
    + rewrite min_by_l_1; first done.
      rewrite -correct_ord_antisym.
      done.
      Unshelve. 2: apply _. 2: apply _. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
