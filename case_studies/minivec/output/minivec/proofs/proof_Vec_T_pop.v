From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.minivec.generated Require Import generated_code_minivec generated_specs_minivec.
From refinedrust.examples.minivec.generated Require Import generated_template_Vec_T_pop.

Set Default Proof Using "Type".

Section proof.
Context `{!refinedrustGS Σ}.

Lemma Vec_T_pop_proof (π : thread_id) :
  Vec_T_pop_lemma π.
Proof.
  generalize RR_CONFIG_DONT_FOLD_PLACES; intros ?.
  Vec_T_pop_prelude.

  rep <-! liRStep; liShow.
  apply_update (updateable_typed_array_access l (length xs - 1) (st_of T_ty MetaNone)).
  liRStepUntil typed_call.
  (* We need to manually extract it now *)
  apply_update (updateable_extract_typed_value (l offsetst{st_of T_ty MetaNone}ₗ (length xs - 1))).
  rep <-! liRStep; liShow.
  apply_update (updateable_subsume_to (l offsetst{st_of T_ty MetaNone}ₗ (length xs - 1)) (◁ uninit (st_of T_ty MetaNone))%I (# ())).
  repeat liRStep.

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.

  all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal with (nia).

  all: revert select (<#> (<$#@{_}> _) = _) => Hxs;
    specialize (project_vec_els_length' _ _ _ Hxs) as ?.
  {
    rewrite Hxs project_vec_els_insert_ge; [|lia].
    erewrite project_vec_els_lookup_mono; [solve_goal|lia|done].
  }
  { apply list_lookup_insert_Some'.
    split; solve_goal. }
  {
    rewrite last_lookup list_lookup_lookup_total_lt /=; [|lia].
    eexists _. split; [done|].
    do 3 f_equal. lia.
  }
  {
    rewrite project_vec_els_insert_ge; [|lia].
    rewrite !fmap_take.
    rewrite Hxs.
    rewrite project_vec_els_take. f_equal. lia.
  }
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
