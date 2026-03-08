From caesium.program_logic Require Export adequacy weakestpre.
From iris.algebra Require Import csum excl auth cmra_big_op gmap.
From iris.base_logic.lib Require Import ghost_map.
From caesium Require Import ghost_state.
From refinedrust Require Export type.
From refinedrust Require Import programs functions struct.struct unit.
From iris.program_logic Require Export language. (* must be last to get the correct nsteps *)
Set Default Proof Using "Type".

(** * RefinedRust's adequacy proof *)

Class typePreG Σ := PreTypeG {
  type_invG                      :: invGpreS Σ;
  type_na_invG                   :: na_invG Σ;
  type_lftG                      :: lftGpreS Σ;
  type_frac_borrowG              :: frac_borG Σ;
  type_lctxG                     :: lctxGPreS Σ;
  type_ghost_varG                :: ghost_varG Σ gvar_refinement.RT;
  type_pinnedBorG                :: pinnedBorG Σ;
  type_trG                       :: trGpreS Σ;
  type_heap_heap_inG             :: inG Σ (authR heapUR);
  type_heap_alloc_meta_map_inG   :: ghost_mapG Σ alloc_id (Z * nat * alloc_kind);
  type_heap_alloc_alive_map_inG  :: ghost_mapG Σ alloc_id bool;
  type_heap_fntbl_inG            :: ghost_mapG Σ addr function;
  type_thread_current_frame_inG  :: ghost_mapG Σ nat nat;
  type_thread_local_vars_inG     :: ghost_mapG Σ (nat * nat) (list string);
  type_thread_local_var_loc_inG  :: ghost_mapG Σ (nat * nat * string) (loc * syn_type);
  type_na_map_inG                :: ghost_mapG Σ nat na_inv_pool_name;
}.

Definition typeΣ : gFunctors :=
  #[invΣ;
    na_invΣ;
    lftΣ;
    GFunctor (constRF fracR);
    lctxΣ;
    ghost_varΣ gvar_refinement.RT;
    pinnedBorΣ;
    trΣ;
    GFunctor (constRF (authR heapUR));
    ghost_mapΣ alloc_id (Z * nat * alloc_kind);
    ghost_mapΣ alloc_id bool;
    ghost_mapΣ addr function;
    ghost_mapΣ nat nat;
    ghost_mapΣ (nat * nat) (list string);
    ghost_mapΣ (nat * nat * string) (loc * syn_type);
    ghost_mapΣ nat na_inv_pool_name ].
Global Instance subG_typePreG {Σ} : subG typeΣ Σ → typePreG Σ.
Proof. solve_inG. Qed.

Definition initial_prog (main : thread_id * loc) : runtime_expr :=
  to_rtexpr main.1 (Call main.2 []).

Definition initial_heap_state :=
  {| hs_heap := ∅; hs_allocs := ∅; |}.

Definition initial_thread_state : thread_state :=
  {| ts_frames := [] |}.
Definition initial_state (num_threads : nat) (fns : gmap addr function) :=
  {| st_heap := initial_heap_state;
     st_fntbl := fns;
     st_thread := list_to_map (zip (seq 0 num_threads) (replicate num_threads initial_thread_state));
  |}.

Lemma initial_state_thread_empty num_threads fns ts π :
  st_thread (initial_state num_threads fns) !! π = Some ts →
  ts = initial_thread_state.
Proof.
  intros Hlook1.
  apply elem_of_list_to_map_2 in Hlook1.
  apply list_elem_of_lookup_1 in Hlook1 as (j & Hlook1).
  apply lookup_zip in Hlook1 as (Hlook1 & Hlook2).
  apply lookup_seq in Hlook1. simpl in Hlook1. destruct Hlook1 as (<- &?).
  apply lookup_replicate in Hlook2. simpl in Hlook2. destruct Hlook2 as (-> & ?).
  done.
Qed.

Definition main_type `{!typeGS Σ} (P : iProp Σ) :=
  fn(∀ ( *[]) : 0 | ( *[]) : [] | () : (), λ ϝ, []; λ π, P) → ∃ () : (), () @ unit_t; λ π, True.

(*Lemma na_alloc Σ `{!refinedcG Σ} `{!na_invG Σ} (num_threads : nat) :*)
  (*⊢ (|==> (∃ γ (M : gmap thread_id na_inv_pool_name), *)
      (*ghost_map_auth γ 1 M ∗ [∗ list] π ∈ seq 0 num_threads, ∃ γ' : na_inv_pool_name, ghost_map_elem γ π DfracDiscarded γ' ∗ na_invariants.na_own γ' ⊤))%I.*)

(** * The main adequacy lemma *)
Lemma refinedrust_adequacy Σ `{!typePreG Σ} `{ALG : LayoutAlg} (thread_mains : list loc) (fns : gmap addr function) n t2 σ2 obs σ:
  σ = initial_state (length thread_mains) fns →
  (* show that the main functions for the individual threads are well-typed for a provable precondition [P] *)
  (∀ {HtypeG : typeGS Σ},
    ([∗ map] k↦qs∈fns, fntbl_entry (fn_loc k) qs) ={⊤}=∗
      [∗ list] π ↦ main ∈ thread_mains, ∃ P, (val_of_loc main) ◁ᵥ{π, MetaNone} main @ function_ptr [] (@eq_refl _ [], main_type P) ∗ P) →
  (* if the whole thread pool steps for [n] steps *)
  nsteps (Λ := c_lang) n (initial_prog <$> (zip (seq 0 (length thread_mains)) thread_mains), σ) obs (t2, σ2) →
  (* then it has not gotten stuck *)
  ∀ e2, e2 ∈ t2 → not_stuck e2 σ2.
Proof.
  move => -> Hwp. apply: (wp_strong_adequacy _ _ refinedc_trgen NotStuck) . move => ? ?.
  (* heap/Caesium stuff *)
  set h := to_heapUR ∅.
  iMod (own_alloc (● h ⋅ ◯ h)) as (γh) "[Hh _]" => //.
  { apply auth_both_valid_discrete. split => //. }
  iMod(ghost_map_alloc fns) as (γf) "[Hf Hfm]".
  iMod (ghost_map_alloc_empty (V:=(Z * nat * alloc_kind))) as (γr) "Hr".
  iMod (ghost_map_alloc_empty (V:=bool)) as (γs) "Hs".
  set (HheapG := HeapG _ _ γh _ γr _ γs _ γf).

  set (num_threads := length thread_mains).
  set (initial_thread_map := list_to_map (zip (seq 0 num_threads) (replicate num_threads 0)) : gmap _ _).
  iMod (ghost_map_alloc initial_thread_map) as (γcur) "(Hcur & Hcur_thread)".
  (* TODO: instead, maybe allocate an empty frame *)
  iMod (ghost_map_alloc_empty (K:=nat * nat) (V:= list string)) as (γlocals) "Hall_locals".
  iMod (ghost_map_alloc_empty (K:= nat * nat * string) (V:= loc * syn_type)) as (γloc) "Hlocals".
  set (HthreadG := ThreadG _ _ γcur _ γlocals _ γloc).

  set (HrefinedCG := RefinedCG _ _ HheapG HthreadG _ ALG).

  (* lifetime logic stuff *)
  iMod (lft_init _ lft_userE) as "(%Hlft & #LFT)"; [solve_ndisj.. | ].
  iMod (lctx_init) as "(%Hlctx & #LCTX & _)"; [solve_ndisj.. | ].

  (* Na mapping from thread ids *)
  iAssert (|==> [∗ list] i ∈ seq 0 num_threads, ∃ γ, na_invariants.na_own γ ⊤)%I as ">Ha".
  { iApply big_sepL_bupd.
    iApply big_sepL_intro. iModIntro. iIntros (k x Hlook).
    iApply na_alloc. }
  iPoseProof (big_sepL_exists with "Ha") as "(%γnas & Hna)".
  iPoseProof (big_sepL2_length with "Hna") as "%Hna_len".
  iMod (ghost_map_alloc (list_to_map (zip (seq 0 num_threads) γnas))) as "(%γna & Hna_auth & Hna_map)".
  rewrite big_sepM_list_to_map; first last.
  { rewrite fst_zip; first apply NoDup_seq. lia. }

  set (HtypeG := TypeG _ HrefinedCG Hlft _ γna _ _ Hlctx _ _).

  iAssert (|==> [∗ list] π ∈ seq 0 num_threads, na_own π ⊤)%I with "[Hna_map Hna]" as ">Hna".
  { iApply big_sepL_bupd.
    iApply big_sepL2_elim_r. iApply (big_sepL2_wand with "Hna").
    iApply big_sepL2_from_zip. { lia. }
    iApply (big_sepL_impl with "Hna_map").
    iModIntro. iIntros (? [] Hlook).
    simpl. rewrite na_own_unfold /na_own_def.
    iIntros "Hna $". iApply (ghost_map_elem_persist with "Hna"). }

  iAssert ([∗ list] π ∈ seq 0 num_threads, current_frame π 0)%I with "[Hcur_thread]" as "Hframe".
  { rewrite big_sepM_list_to_map; first last.
    { rewrite fst_zip; first apply NoDup_seq. rewrite length_seq length_replicate. lia. }
    iPoseProof (big_sepL2_from_zip _ _  (λ _ a b, a ↪[γcur] b)%I with "Hcur_thread") as "Ha".
    { rewrite length_seq length_replicate. done. }
    rewrite big_sepL2_replicate_r; last by rewrite length_seq.
    iApply (big_sepL_impl with "Ha"). iModIntro.
    iIntros (???). rewrite current_frame_unfold. eauto. }

  move: (Hwp HtypeG) => {Hwp}.
  move => Hwp.
  iAssert (|==> [∗ map] k↦qs ∈ fns, fntbl_entry (fn_loc k) qs)%I with "[Hfm]" as ">Hfm". {
    iApply big_sepM_bupd. iApply (big_sepM_impl with "Hfm").
    iIntros "!>" (???) "Hm". rewrite fntbl_entry_eq.
    iExists _. iSplitR; [done|].
    iApply (ghost_map_elem_persist with "Hm"). }
  iMod (Hwp with "Hfm") as "Hmains".

  iModIntro. iExists c_irisG.(state_interp), (replicate (length thread_mains) (λ _, True%I)), c_irisG.(fork_post), c_irisG.(state_interp_mono).
  iSplitL "Hh Hf Hr Hs Hcur Hall_locals Hlocals"; last first. 1: iSplitL "Hmains Hna Hframe".
  Unshelve.
  - rewrite big_sepL2_fmap_l. iApply big_sepL2_replicate_r.
    { rewrite length_zip length_seq. unfold num_threads. lia. }
    iApply (big_sepL2_to_zip _ _ (λ _ a b, WP initial_prog (a, b) {{ _, True }})%I).
    rewrite -(big_sepL_zip_seq (λ (imain : nat * loc), ∃ P : iProp Σ, (imain.2 ◁ᵥ{imain.1, MetaNone} imain.2 @ function_ptr [] (eq_refl, main_type P)) ∗ P)%I 0%nat num_threads); last lia.
    iPoseProof (big_sepL2_from_zip _ _ (λ _ a (b : loc), ∃ P : iProp Σ, (b ◁ᵥ{a, MetaNone} b @ function_ptr [] (eq_refl, main_type P)) ∗ P)%I with "Hmains") as "Hmains".
    { rewrite length_seq. lia. }
    iApply (big_sepL2_wand with "Hmains").
    iPoseProof (big_sepL_extend_r with "Hna") as "Hna"; last iApply (big_sepL2_wand with "Hna").
    { rewrite length_seq. lia. }
    iPoseProof (big_sepL_extend_r with "Hframe") as "Hframe"; last iApply (big_sepL2_wand with "Hframe").
    { rewrite length_seq. lia. }
    iApply big_sepL2_intro. { rewrite length_seq. lia. }

    iIntros "!#" (π ? main Hlook1 ?) "Hframe Hna Hfn".
    apply lookup_seq in Hlook1 as (-> & ?).
    iDestruct ("Hfn") as (P) "[Hmain HP]".
    rewrite /initial_prog.
    iPoseProof (type_call_fnptr [] [] (π, 0) π 0 [] [] [] main (val_of_loc main) [] [] eq_refl _ (main_type P) [] (λ _ _ _ _ _, True%I) with "[HP Hna] Hmain [] [] [] [] Hframe []") as "Hx"; first last.
    + rewrite expr_wp_unfold. done.
    + by iIntros (?????) "HL _".
    + by iApply big_sepL_nil.
    + by iApply big_sepL_nil.
    + rewrite /rrust_ctx. iFrame "#".
    + by iApply big_sepL2_nil.
    + iExists ⊤ => /=.
      iFrame. do 2 iR.
      iIntros (??) "_ _ HL _". iModIntro. iFrame. iExists *[], -[].
      rewrite /li_tactic/ensure_evars_instantiated_goal.
      iR. iExists tt.
      iIntros (????) "#CTX #HE HL".
      iModIntro. iExists [], [], True%I.
      iFrame. iSplitR.
      { simpl. eauto. }
      iSplitR. { simpl. eauto. }
      iIntros "_". simpl. iR.
      iIntros (????) "_ _ HL". iModIntro.
      iExists [], [], True%I. iFrame.
      iSplitL "HP". { iApply maybe_logical_step_intro. eauto. }
      simpl.
      iSplitR; first done.
      iSplitR. { iPureIntro. by apply Forall_nil. }
      iSplitR. { iPureIntro. unfold shelve_hint.
        intros.
        rewrite /ty_outlives_E ty_lfts_unfold.
        rewrite ty_wf_E_unfold. apply elctx_sat_nil. }
      iIntros (v []).
      iIntros (??) "_ HL _". eauto with iFrame.
  - iFrame. iIntros (?? _ _ ?) "_ _ _". iApply fupd_mask_intro_discard => //. iPureIntro. by eauto.
  - rewrite /state_ctx /heap_state_ctx /thread_ctx /alloc_meta_ctx /to_alloc_meta_map /alloc_alive_ctx /to_alloc_alive_map.
    iFrame. iR.
    iSplitL.
    { unfold thread_current_frame_auth.
      iApply (ghost_map_auth_prove_eq with "Hcur").
      rewrite /to_current_frame /initial_thread_map/=.
      rewrite -list_to_map_fmap prod_map_zip.
      rewrite list_fmap_id.
      f_equiv. f_equiv.
      rewrite fmap_replicate//. }
    iSplitR; first iSplit; last iSplitL; [ | | by iApply big_sepM_empty | iSplit]; iPureIntro.
    + intros ???? ? Hlook1 ?. simpl.
      apply initial_state_thread_empty in Hlook1.
      subst. done.
    + done.
    + intros ???????? Hlook1 ?.
      apply initial_state_thread_empty in Hlook1.
      subst. done.
    + done.
Qed.

(*Print Assumptions refinedrust_adequacy.*)

(* clients of this:
    - create a function map with monomorphized entries of all the functions they need
        -> this we need to know upfront.
    - from the fntbl_entry we get, build the function_ptr types.
        we use Löb induction as part of that (have a later in the function_ptr type to enable that)
          the induction assumes that we already have fn_ptrs for all the functions we build, at the types that they should have.


  clients of this may also instantiate it with concrete layouts, if they can provide a layout algorithm that computes them.
 *)



(** * Helper functions for using the adequacy lemma *)
Definition fn_lists_to_fns (addrs : list addr) (fns : list function) : gmap addr function :=
  list_to_map (zip addrs fns).

Lemma fn_lists_to_fns_cons `{!refinedcG Σ} addr fn addrs fns :
  length addrs = length fns →
  addr ∉ addrs →
  ([∗ map] k↦qs ∈ fn_lists_to_fns (addr :: addrs) (fn :: fns), fntbl_entry (fn_loc k) qs) -∗
  fntbl_entry (Loc ProvFnPtr addr) fn ∗ ([∗ map] k↦qs ∈ fn_lists_to_fns addrs fns, fntbl_entry (fn_loc k) qs).
Proof.
  move => Hnotin ?.
  rewrite /fn_lists_to_fns /= big_sepM_insert //; auto.
  apply not_elem_of_list_to_map_1. rewrite fst_zip => //; lia.
Qed.

(** * Tactics for solving conditions in an adequacy proof *)

Ltac adequacy_intro_parameter :=
  repeat lazymatch goal with
         | |- ∀ _ : (), _ => case
         | |- ∀ _ : (_ * _), _ => case
         | |- ∀ _ : _, _ => move => ?
         end.

(*
Ltac adequacy_unfold_equiv :=
  lazymatch goal with
  | |- type_fixpoint _ _ ≡ type_fixpoint _ _ => apply: type_fixpoint_proper; [|move => ??]
  | |- ty_own_val _ _ ≡ ty_own_val _ _ => unfold ty_own_val => /=
  | |-  _ =@{struct_layout} _ => apply: struct_layout_eq
  end.

Ltac adequacy_solve_equiv unfold_tac :=
  first [ eassumption | fast_reflexivity | unfold_type_equiv | adequacy_unfold_equiv | f_contractive | f_equiv' | reflexivity | progress unfold_tac ].

Ltac adequacy_solve_typed_function lemma unfold_tac :=
  iApply typed_function_equiv; [
    done |
    adequacy_intro_parameter => /=; repeat (constructor; [done|]); by constructor |
    | iApply lemma => //; iExists _; repeat iSplit => //];
    adequacy_intro_parameter => /=; eexists eq_refl => /=; split_and!; [..|adequacy_intro_parameter => /=; split_and!];  repeat adequacy_solve_equiv unfold_tac.
 *)
