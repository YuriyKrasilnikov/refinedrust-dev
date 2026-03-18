From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_traits_iterator_Iterator_fold.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma traits_iterator_Iterator_fold_proof (π : thread_id) :
  traits_iterator_Iterator_fold_lemma π.
Proof.
  traits_iterator_Iterator_fold_prelude.

  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  liInst Hevar_params self.
  liInst Hevar_seq [].
  rep <-! liRStep; liShow.
  { iRename select (∀ _, _)%I into "Hwand".
    iPoseProof ("Hwand" with "[$] [$]") as "Hwand'".
    iPoseProof ("Hwand'" with "[$]") as "(%pclos & Hpre & ? & ? & Hcl)".
    rep liRStep; liShow.
    liInst Hevar_x1 pclos.
    rep <-! liRStep; liShow.
    iPoseProof ("Hcl" with "[$]") as "(? & _)".
    rep liRStep; liShow.
    liInst Hevar_x x'1.
    rep liRStep; liShow. }
  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  liInst Hevar_x0 x'.
  rep liRStep; liShow.
  liInst Hevar_x1 seq. liInst Hevar_x2 x3.
  rep liRStep;liShow.
  liInst Hevar_x3 x6.
  rep liRStep;liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
