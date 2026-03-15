From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.linkedlist.generated Require Import generated_code_linkedlist generated_specs_linkedlist generated_template_List_T_push_front.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

Lemma List_T_push_front_proof (π : thread_id) :
  List_T_push_front_lemma π.
Proof.
  List_T_push_front_prelude.

  rep <-! liRStep; liShow.
  { rep liRStep. liShow.
    liInst Hevar_locs (x' :: locs).
    liInst Hevar_rf ($#@{ T_rt } value :: <$#@{ T_rt }>self).
    move: Hlocs.
    rep liRStep. }
  { rep liRStep; liShow.
    liInst Hevar_locs (x' :: locs).
    liInst Hevar_rf ($#@{ T_rt } value :: <$#@{ T_rt }>self).
    move: Hlocs.
    rep liRStep. }

  all: print_remaining_goal.
  Unshelve. all: sidecond_solver.
  Unshelve. all: sidecond_hammer.
  - match goal with H : last locs = Some _ |- _ => rewrite last_cons H // end.
  - by apply Forall_Forall_cb.
  - erewrite list_lookup_total_correct; last by rewrite -head_lookup.
    done.
  Unshelve. all: print_remaining_sidecond.
Qed.
End proof.
