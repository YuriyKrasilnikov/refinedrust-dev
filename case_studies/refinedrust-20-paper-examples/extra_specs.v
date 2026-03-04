Section extra_specs.
Context `{RRGS : !refinedrustGS Σ}.

(* Proved by manual induction: inductive property about the emitted elements *)
Global Program Instance iterator_learn_list T_rt p :
  IteratorLearnInductive (ListIteraTasstd_iter_Iterator_spec_attrs T_rt) p :=
  {| iterator_learn_inductive_Q s1 hist s2 := s1 = hist ++ s2 |}.
Next Obligation.
  iIntros (? [] ????) "Hx".
  iPoseProof (boringly_persistent_elim with "Hx") as "Hx".
  iInduction hist as [ | x hist] "IH" forall (s1 s2); simpl.
  { iDestruct "Hx" as "->". iPureIntro. done. } 
  iDestruct "Hx" as "(%s1' & (_ & ->) & Hx)".
  iPoseProof ("IH" with "Hx") as "->".
  done.
Qed.

End extra_specs.
