From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From rrstd.iterator.iterator.generated Require Import generated_code_iterator generated_specs_iterator generated_template_traits_iterator_Iterator_try_fold.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Ltac hooks.solve_goal_final_hook ::=
  try congruence;
  refined_solver lia
.

Lemma traits_iterator_Iterator_try_fold_proof (π : thread_id) :
  traits_iterator_Iterator_try_fold_lemma π.
Proof.
  traits_iterator_Iterator_try_fold_prelude.

  rep <-! liRStep; liShow.
  rep liRStep; liShow.
  liInst Hevar_x2 self.
  liInst Hevar_seq [].
  rep <-! liRStep; liShow.

  2: { 
    rep <-! liRStep; liShow.
    rep <- 15 liRStep; liShow.
    liInst Hevar_x1 seq.
    liInst Hevar_x2 x7.

    rep liRStep; liShow. }

  (* establishing the precondition *)
  iRename select (∀ _ _ _ _, _)%I into "Hwand".
  iPoseProof ("Hwand" with "[$] [$]") as "(%pclos & Hpre & Hnext & Hcl)".
  rep liRStep; liShow.
  liInst Hevar_x1 pclos.
  rep <-! liRStep; liShow.
  { rep liRStep; liShow.
    rename select (Try_BranchFn _ _ = inl _) into Heq. rewrite Heq.
    rep liRStep; liShow.
    liInst Hevar_x x'1.
    iPoseProof ("Hcl" with "[$]") as "[Ha Hb]".
    iRevert "Ha Hb".
    rewrite Heq.
    rep liRStep; liShow. }
  { rep <-! liRStep; liShow.
    rename select (Try_BranchFn _ _ = inr _) into Heq. rewrite Heq.
    rep <-! liRStep; liShow.
    iPoseProof ("Hcl" with "[$]") as "[Ha Hb]".
    iRevert "Ha Hb".
    rewrite Heq.

    rep <-! liRStep; liShow.
    rep liRStep; liShow.
    (* TODO: maybe add Lithium instances for Next so we can instantiate evars *)
    liInst Hevar_x2 x'.
    liInst Hevar_x x'1.
    rep liRStep; liShow. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  { eapply Forall_app. solve_goal. }
  { rewrite last_app; simpl. solve_goal. }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
