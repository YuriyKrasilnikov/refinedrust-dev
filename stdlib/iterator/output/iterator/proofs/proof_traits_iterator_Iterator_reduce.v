From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_traits_iterator_Iterator_reduce.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma traits_iterator_Iterator_reduce_proof (π : thread_id) :
  traits_iterator_Iterator_reduce_lemma π.
Proof.
  traits_iterator_Iterator_reduce_prelude.

  rep <-! liRStep.
  { destruct x'0 as [item | ]; last done.
    injection H24 as <-.
    rep liRStep; liShow.
    (* carry the first witness in the invariant *)
    liInst Hevar_x2 (λ π acc items iter clos, ClosInv π (Some acc) (item :: items) iter clos ∗ traits_iterator_Iterator_Next traits_iterator_Iterator_Self_spec_attrs π p self (Some item) x')%I.
    iRename select (∀ _ _, _ -∗ _)%I into "Hinit".
    iPoseProof ("Hinit" with "[$] [$]") as "(Hclos & ?)".
    rep 2 liRStep; liShow.
    iRename select (∀ _ _ _ ,_ )%I into "Hpres".
    rep <- 2 liRStep; liShow.
    { (* combine the next relation *)
      iPoseProof ("Hpres" with "[-]") as "#Hpres'".
      { iApply (iterator_next_fused_trans_cons with "[$] [$]"). }
      iPoseProof ("Hpres'" with "[$] [$]") as "(%pclos & ? & ? & Hcl)".
      iExists pclos.
      rep liRStep; liShow.
      iPoseProof ("Hcl" with "[$]") as "(? & _)".
      rep liRStep; liShow. }
    rep <-! liRStep; liShow.
    rep liRStep; liShow.
    liInst Hevar_x0 x'2.
    liInst Hevar_x2 x'1.
    rep liRStep; liShow.
    liInst Hevar_x1 (item :: x'0). simpl.
    rep liRStep; liShow.
    liInst Hevar_s1' x'.
    rep liRStep; liShow.
    liInst Hevar_x3 x'3.
    rep liRStep; liShow. }
  rep liRStep; liShow.
  destruct x'0 as [item | ]; first done.
  injection H24 as <-.
    rep liRStep; liShow.
  liInst Hevar_x0 x'.
  liInst Hevar_x2 self.
  rep liRStep; liShow.
  liInst Hevar_x3 f.
  rep liRStep; liShow.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
