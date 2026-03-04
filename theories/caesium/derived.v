From caesium Require Export tactics lifting proofmode.
Set Default Proof Using "Type".

Section derived.
  Context `{refinedcG Σ} `{ALG : LayoutAlg}.

  Lemma wps_annot A (a : A) n π Q Ψ s:
    (|={⊤}⧗=>^n WPs{π} s {{ Q, Ψ }}) -∗ WPs{π} (annot{ n }: a; s)%E {{ Q , Ψ }}.
  Proof using ALG.
    iIntros "Hs".
    rewrite /AnnotStmt /SkipES /=.
    iInduction n as [ | n] "IH"; simpl; first done.
    wps_bind. iApply wp_skip.
    iApply (physical_step_wand with "Hs"). iIntros "Hs".
    iApply wps_exprs.
    iApply physical_step_intro.
    iNext. iApply "IH". done.
  Qed.
End derived.
