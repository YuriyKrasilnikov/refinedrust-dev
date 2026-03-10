Section extra_specs.
Context `{RRGS : !refinedrustGS Σ}.
Lemma branchfn_from_output_eq {Self_rt Output_rt ResidualRt} (A: FromResidual_spec_attrs Self_rt ResidualRt) (B : Try_spec_attrs Self_rt Output_rt ResidualRt A) r :
  B.(Try_BranchFn) (B.(Try_FromOutputFn) r) = inl r.
Proof.
  by apply B.(Try_BranchLawOutput).
Qed.

Lemma branchfn_from_residual_eq {Self_rt Output_rt ResidualRt} (A: FromResidual_spec_attrs Self_rt ResidualRt) (B : Try_spec_attrs Self_rt Output_rt ResidualRt A) r x :
  B.(Try_ResidualValid) r →
  (A.(FromResidual_FromResidualFn) r = Some x) →
  B.(Try_BranchFn) x = inr r.
Proof.
  by apply B.(Try_BranchLawResidual).
Qed.

Global Instance simpl_impl_from_residual {Self_rt Output_rt ResidualRt} (A: FromResidual_spec_attrs Self_rt ResidualRt) (B : Try_spec_attrs Self_rt Output_rt ResidualRt A) x y r `{Heq : !TCDone (B.(Try_BranchFn) y = inr r)}:
  SimplImplRel (=) false (A.(FromResidual_FromResidualFn) r) (Some x) (λ T, A.(FromResidual_FromResidualFn) r = Some x → B.(Try_BranchFn) x = inr r → T).
Proof.
  intros T. 
  unfold TCDone in Heq.
  split.
  - intros Hb Hres. apply Hb; first done. 
    eapply Try_BranchLawResidual; last done. 
    by eapply Try_BranchValid.
  - intros Hb Hres ?. apply Hb. 
    done.
Qed.
End extra_specs.

Global Hint Rewrite -> @branchfn_from_residual_eq using done : lithium_rewrite.
Global Hint Rewrite -> @branchfn_from_output_eq : lithium_rewrite.
