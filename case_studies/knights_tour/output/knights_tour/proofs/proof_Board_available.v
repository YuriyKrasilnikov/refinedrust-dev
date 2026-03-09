From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.knights_tour.generated Require Import generated_code_knights_tour generated_specs_knights_tour generated_template_Board_available.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma Board_available_proof (π : thread_id) :
  Board_available_lemma π.
Proof.
  Board_available_prelude.

  rep <-! liRStep; liShow.

  { rep liRStep. liShow.
    liInst Hevar_x1 (fmap (λ (x : list nat), fmap Z.of_nat x) self0).
    rep liRStep. }
  all : rep liRStep.
  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - rewrite! wrap_to_it_id; [ | solve_goal..].
    rename select (wrap_to_it p usize < _) into Hpbound.
    rename select (wrap_to_it p0 usize < _) into Hp0bound.
    rewrite wrap_to_it_id in Hpbound; last solve_goal.
    rewrite wrap_to_it_id in Hp0bound; last solve_goal.

    rewrite list_lookup_total_fmap; last solve_goal.
    rewrite length_fmap.
    rewrite Hnestedlen; last solve_goal.
    solve_goal.
  - rename select (wrap_to_it p usize < _) into Hpbound.
    rewrite wrap_to_it_id in Hpbound; last solve_goal.
    solve_goal.
  - rename select (wrap_to_it p usize < _) into Hpbound.
    rewrite wrap_to_it_id in Hpbound; last solve_goal.
    rename select (wrap_to_it p0 usize < _) into Hp0bound.
    rewrite! wrap_to_it_id in Hp0bound; [ | solve_goal..].
    rewrite list_lookup_total_fmap in Hp0bound; last solve_goal.
    rewrite length_fmap in Hp0bound.
    rewrite Hnestedlen in Hp0bound; first apply Hp0bound.
    solve_goal.
Qed.
End proof.
