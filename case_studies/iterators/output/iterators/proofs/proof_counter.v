From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.iterators.generated Require Import generated_code_iterators generated_specs_iterators generated_template_counter.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(* !start proof(counter) *)
(* Inductive lemma about the closure state.
  TODO: develop closure inductive inference further so that this happens automatically. *)
Lemma inductive_lemma (clos_states : list (plist (RT_xt ∘ place_rfnRT) [(place_rfn Z * gname)%type : RT])) (hist : list Z) i0 γ:
  head clos_states = Some *[(i0, γ)] →
  length clos_states = S (length hist) →
  Forall (λ a, ∃ (x : gname) (x0 : Z), clos_states !! a.1 = Some -[(x0, x)] ∧ clos_states !! S a.1 = Some -[(x0 + 1, x)] ∧ MinInt usize ≤ x0 + 1 ≤ MaxInt usize) (zip (seq 0 (length hist)) hist) →
  ∀ i x, clos_states !! i = Some x → x = *[(Z.of_nat (i) + i0, γ)].
Proof.
  induction hist as [ | ? hist IH] in clos_states, i0, γ |-*; simpl.
  { destruct clos_states as [ | [[] []] []]; [done | | done]; simpl.
    intros [=] _ _. subst.
    intros [ | ]; simpl; [| done]. naive_solver. }
  destruct clos_states as [ | st1 clos_states]; first done.
  simpl. intros [= ->] ?.
  rewrite Forall_cons. simpl. intros [(γ' & ix & Heq & Hlook & ?) Hf].
  injection Heq. intros <- <-.
  ospecialize (IH clos_states (i0 + 1) γ _ _ _).
  { rewrite head_lookup. done. }
  { lia. }
  { move: Hf. rewrite -(fmap_S_seq 0) zip_fmap_l Forall_fmap.
    simpl. done. }
  intros [ | ]; simpl; first naive_solver.
  intros x Hlook'%IH.
  subst. do 2 f_equiv. lia.
Qed.
(* !end proof *)

Lemma counter_proof (π : thread_id) :
  counter_lemma π.
Proof.
  counter_prelude.

  rep <-! liRStep; liShow.
  (* !start proof(counter) *)
  repeat liRStep; liShow.
  liInst Hevar_Inv (λ _ l '( *[p]), ⌜0 ≤ p.cur⌝ ∗ ⌜int_elem_of_it (p.cur + Z.of_nat ( length l))%Z USize⌝)%I.
  rep <-! liRStep; liShow.
  opose proof (inductive_lemma clos_states _ _ _ _ _ _) as Heq; [done.. | ].
  assert (r'1 = γ) as -> by shelve_sidecond.
  rep liRStep; liShow.
  (* !end proof *)

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  (* !start proof(counter) *)
  - rename select (last clos_states = Some _) into Hlast.
    rewrite last_lookup in Hlast. apply Heq in Hlast.
    injection Hlast. done.
  - rename select (last clos_states = Some _) into Hlast.
    rewrite last_lookup in Hlast. apply Heq in Hlast.
    injection Hlast. intros ->. lia.
  (* !end proof *)

  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
