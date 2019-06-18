Require Import Omega.
From hahn Require Import Hahn.
From imm Require Import Events Execution
     Prog ProgToExecution ProgToExecutionProperties.
Require Import AuxDef.
Require Import AuxRel.
Require Import ImmProperties.

Lemma unique_eps_step thread state state' state''
      (EPS_STEP1 : istep thread [] state state')
      (EPS_STEP2 : istep thread [] state state'') :
  state' = state''.
Proof.
  cdes EPS_STEP1.
  cdes EPS_STEP2.
  rewrite <- ISTEP in ISTEP1. inv ISTEP1.
  inv ISTEP0.
  all: inv ISTEP2.
  all: destruct state'.
  all: destruct state''.
  all: simpls.
  all: desf.
Qed.

Lemma unique_ineps_step thread lbl state state' state''
      (STEP1 : istep thread lbl state state')
      (STEP2 : istep thread lbl state state'') :
  state' = state''.
Proof.
  cdes STEP1.
  cdes STEP2.
  rewrite <- ISTEP in ISTEP1. inv ISTEP1.
  inv ISTEP0.
  all: inv ISTEP2.
  all: destruct state'.
  all: destruct state''.
  all: simpls.
  all: desf.
Qed.

Definition stable_state :=
  set_compl
    (dom_rel (fun x y => exists thread, istep thread [] x y)).

Definition stable_lprog lprog :=
  forall thread state (INSTR : state.(instrs) = lprog)
         (REACH : (step thread)＊ (init lprog) state),
    { state' |
      ⟪ STEPS : (istep thread [])＊ state state' ⟫ /\
      ⟪ STABLE : stable_state state' ⟫ }.

Lemma get_stable thread state
      (LPST : stable_lprog state.(instrs))
      (REACH : (step thread)＊ (init state.(instrs)) state) :
  { state' |
    unique (fun state' =>
              ⟪ STEPS : (istep thread [])＊ state state' ⟫ /\
              ⟪ STABLE : stable_state state' ⟫)
    state' }.
Proof.
  edestruct LPST as [state']; eauto.
  desf.
  exists state'.
  red. splits; auto.
  clear -STEPS STABLE.
  apply clos_rt_rt1n in STEPS.
  intros y [AA BB].
  apply clos_rt_rt1n in AA.
  generalize dependent y.
  induction STEPS.
  { ins. destruct AA; auto.
    exfalso. apply STABLE.
    eexists. eauto. }
  ins.
  apply IHSTEPS; auto.
  destruct AA.
  { exfalso. apply BB.
    eexists. eauto. }
  assert (y = y0); desf.
  eapply unique_eps_step; eauto.
Qed.

Lemma terminal_stable : is_terminal ⊆₁ stable_state.
Proof.
  intros state TERM [state' HH].
  desf. cdes HH.
  assert (nth_error (instrs state) (pc state) <> None) as YY.
  { by rewrite <- ISTEP. }
  apply nth_error_Some in YY.
  red in TERM.
  rewrite INSTRS in *.
  inv ISTEP0; desf.
  all: omega.
Qed.

Definition ineps_step thread lbls (state state' : state) :=
  ⟪ NNIL : lbls <> [] ⟫ /\
  ⟪ STEP : istep thread lbls state state' ⟫.

Definition neps_step thread (state state' : state) :=
  exists lbls, ineps_step thread lbls state state'.

Definition ilbl_step thread lbls :=
  ineps_step thread lbls ⨾ (istep thread [])＊ ⨾ ⦗ stable_state ⦘.

Definition lbl_step thread (state state' : state) :=
  exists lbls, ilbl_step thread lbls state state'.

Lemma ilbl_step_in_steps thread lbls : ilbl_step thread lbls ⊆ (step thread)⁺.
Proof.
  unfold ilbl_step.
  arewrite ((istep thread [])＊ ⊆ (step thread)＊).
  { apply clos_refl_trans_mori. unfold step. basic_solver. }
  arewrite (ineps_step thread lbls ⊆ step thread).
  { unfold step, ineps_step. basic_solver. }
  rewrite <- seqA.
  rewrite <- ct_begin.
  basic_solver.
Qed.

Lemma lbl_step_in_steps thread : lbl_step thread ⊆ (step thread)⁺.
Proof.
  intros x y [lbl HH]. cdes HH.
  eapply ilbl_step_in_steps. eauto.
Qed.

Lemma lbl_steps_in_steps thread : (lbl_step thread)＊ ⊆ (step thread)＊.
Proof. rewrite lbl_step_in_steps. apply rt_of_ct. Qed.

Lemma ineps_eps_step_dom_empty thread lbls :
  dom_rel (ineps_step thread lbls) ∩₁
  dom_rel (fun x y => exists thread, istep thread [] x y) ≡₁ ∅.
Proof.
  split; [|basic_solver].
  intros x [[y AA] [z BB]].
  cdes AA.
  cdes STEP.
  cdes BB.
  rewrite <- ISTEP in ISTEP1. inv ISTEP1.
  inv ISTEP2.
  all: inv ISTEP0.
Qed.

Lemma steps_to_eps_steps_steps thread state state' state''
      (STBL : stable_state state'')
      (EPS_STEPS : (istep thread [])＊ state state')
      (    STEPS : (step thread)＊     state state'') :
  (step thread)＊ state' state''.
Proof.
  apply clos_rt_rt1n in EPS_STEPS.
  induction EPS_STEPS; auto.
  apply IHEPS_STEPS.
  clear dependent z.
  apply clos_rt_rt1n in STEPS.
  inv STEPS.
  { exfalso. apply STBL. eexists. eauto. }
  assert (y0 = y); subst.
  2: by apply clos_rt1n_rt.
  match goal with
  | H : step thread x y0 |- _ => inv H
  end.
  destruct (classic (x0 = [])); subst.
  { eapply unique_eps_step; eauto. }
  exfalso.
  eapply ineps_eps_step_dom_empty.
  split; eexists; [red; splits|]; eauto.
Qed.

Lemma ineps_step_stable_l thread lbls :
  ineps_step thread lbls ≡ ⦗ stable_state ⦘ ⨾ ineps_step thread lbls.
Proof.
  split; [|basic_solver].
  intros x y HH.
  apply seq_eqv_l. split; auto.
  intros [z AA]. desf.
  eapply ineps_eps_step_dom_empty.
  split; eexists; eauto.
Qed.

Lemma neps_step_stable_l thread :
  neps_step thread ≡ ⦗ stable_state ⦘ ⨾ neps_step thread.
Proof.
  split; [|basic_solver].
  intros x y HH.
  apply seq_eqv_l. split; auto.
  red in HH. desf.
  apply ineps_step_stable_l in HH.
  apply seq_eqv_l in HH. desf.
Qed.

Lemma lbl_step_alt thread :
  lbl_step thread ≡ neps_step thread ⨾ (istep thread [])＊ ⨾ ⦗stable_state⦘.
Proof.
  split.
  { intros x y [l [e HH]].
    eexists. split; [eexists|]; apply HH. }
  intros x y [e [[l AA] HH]].
  eexists. eexists. split; eauto.
Qed.

Lemma steps_stable_lbl_steps thread :
  ⦗stable_state⦘ ⨾ (step thread)＊ ⨾ ⦗stable_state⦘ ⊆ (lbl_step thread)＊.
Proof.
  arewrite (step thread ⊆ neps_step thread ∪ istep thread []).
  { intros x y HH. red in HH. desf.
    destruct lbls; [by right|].
    left. eexists. red.
      by splits; eauto. }
  rewrite rt_unionE.
  rewrite seqA.
  arewrite (⦗stable_state⦘ ⨾ (istep thread [])＊ ⊆ ⦗stable_state⦘).
  { rewrite rtE. rewrite seq_union_r.
    apply inclusion_union_l; [basic_solver|].
    rewrite ct_begin.
    arewrite (⦗stable_state⦘ ⨾ istep thread [] ⊆ ∅₂).
    2: basic_solver.
    intros x y HH.
    apply seq_eqv_l in HH. apply HH.
    eexists. eexists. apply HH. }
  rewrite rt_dom_ri.
  2: { rewrite neps_step_stable_l at 1. by rewrite !seqA. }
  rewrite !seqA.
  rewrite <- lbl_step_alt.
  basic_solver.
Qed.

Lemma ilbl_step_alt thread lbls (state state'' : state) 
      (ILBL_STEP : ilbl_step thread lbls state state'') :
  exists state', 
    ⟪ NNIL     : lbls <> [] ⟫ /\
    ⟪ ISTEP    : istep thread lbls state state' ⟫ /\
    ⟪ EPS_STEP : (istep thread [])＊ state' state'' ⟫ /\
    ⟪ STABLE   : stable_state state'' ⟫.
Proof. 
  edestruct ILBL_STEP. 
  unfold seq in *. 
  unfold ineps_step in *. 
  unfold eqv_rel in *.
  desf. eexists. splits; eauto. 
Qed. 

Lemma same_pos_stable state state'
      (INSTR : state.(instrs) = state'.(instrs))
      (PC : state.(pc) = state'.(pc))
      (STABLE : stable_state state) :
    stable_state state'.
Proof.
  red. red. intros [state'' STEP].
  desf. cdes STEP. inv ISTEP0; eapply STABLE.
  eexists (Build_state _ _ _ _ _ _ _).
  2: eexists (Build_state _
                          (if Event.Const.eq_dec (RegFile.eval_expr (regf state) expr) 0
                           then pc state + 1
                           else shift) _ _ _ _ _).
  all: eexists; red; splits; [by eauto|].
  all: eexists; splits; [by rewrite PC, INSTR; eauto|].
  { eapply assign; eauto; simpls. }
  eapply if_; eauto; simpls.
  desf.
Unshelve. all: eauto.
Qed.

(*****************************************
** General properties of istep and step **
*****************************************)

Lemma step_same_instrs thread state state'
      (STEP : step thread state state') :
  state'.(instrs) = state.(instrs).
Proof. cdes STEP. inv STEP0. Qed.

Lemma steps_same_instrs thread state state'
      (STEP : (step thread)＊ state state') :
  state'.(instrs) = state.(instrs).
Proof.
  induction STEP; auto.
  { eapply step_same_instrs; eauto. }
  etransitivity; eauto.
Qed.

Lemma eps_step_same_G thread state state'
      (STEP : istep thread [] state state') :
  state'.(G) = state.(G).
Proof. cdes STEP. inv ISTEP0. Qed.

Lemma eps_steps_same_G thread state state'
      (STEP : (istep thread [])＊ state state') :
  state'.(G) = state.(G).
Proof.
  induction STEP; auto.
  { eapply eps_step_same_G; eauto. }
  etransitivity; eauto.
Qed.

Lemma eps_step_in_step thread : istep thread [] ⊆ step thread.
Proof. unfold step. basic_solver. Qed.

Lemma eps_steps_in_steps thread : (istep thread [])＊ ⊆ (step thread)＊.
Proof. by rewrite eps_step_in_step. Qed.

Lemma no_step_from_terminal thread : ⦗ is_terminal ⦘ ⨾ (step thread) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfolder. intros x y [TERM STEP]. red in TERM.
  assert (nth_error (instrs x) (pc x) <> None) as NN.
  { cdes STEP. cdes STEP0. by inv ISTEP0; rewrite <- ISTEP. }
  apply nth_error_Some in NN. omega.
Qed.

Lemma no_lbl_step_from_terminal thread : ⦗ is_terminal ⦘ ⨾ (lbl_step thread) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  rewrite lbl_step_in_steps. rewrite ct_begin, <- seqA.
  rewrite no_step_from_terminal. basic_solver.
Qed.

Lemma stable_state_no_eps_step thread : ⦗stable_state⦘ ⨾ (istep thread []) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfolder. intros x y [ST STEP].
  apply ST. do 2 eexists. eauto.
Qed.

Lemma stable_state_eps_steps_refl thread :
  ⦗stable_state⦘ ⨾ (istep thread [])＊ ≡ ⦗stable_state⦘.
Proof.
  rewrite rtE, ct_begin, seq_union_r, seq_id_r.
  rewrite <- seqA. rewrite stable_state_no_eps_step.
  basic_solver.
Qed.

Lemma unique_eps_steps_to_stable thread st st' st''
      (STEP1 : ((istep thread [])＊ ⨾ ⦗stable_state⦘) st st')
      (STEP2 : ((istep thread [])＊ ⨾ ⦗stable_state⦘) st st'') :
  st'' = st'.
Proof.
  destruct_seq_r STEP1 as ST1.
  destruct_seq_r STEP2 as ST2.
  apply clos_rt_rt1n in STEP1.
  induction STEP1.
  { symmetry. eapply stable_state_eps_steps_refl.
    apply seq_eqv_l. split; eauto. }
  apply IHSTEP1.
  specialize (IHSTEP1 ST1); auto.
  apply clos_rt_rt1n in STEP2.
  destruct STEP2 as [|w].
  { exfalso.
    apply ST2. do 2 eexists. eauto. }
  assert (w = y); subst.
  2: by apply clos_rt1n_rt.
  eapply unique_eps_step; eauto.
Qed.

Lemma unique_ilbl_step thread lbl state state' state''
      (STEP1 : ilbl_step thread lbl state state')
      (STEP2 : ilbl_step thread lbl state state'') :
  state' = state''.
Proof.
  cdes STEP1.
  cdes STEP2.
  destruct STEP0 as [st0 [ST01 ST02]].
  destruct STEP3 as [st1 [ST11 ST12]].
  assert (st0 = st1); subst.
  { cdes ST01. cdes ST11. eapply unique_ineps_step; eauto. }
  eapply unique_eps_steps_to_stable; eauto.
Qed.

(* TODO: replace w/ something standard or move to AuxDef.v. *)
Lemma app_eq {A B} (f f' : A -> B) (EQ : f = f') (a : A) :
  f a = f' a.
Proof. by rewrite EQ. Qed.

Lemma unique_lbl_istep_same_G thread lbl lbl' state state' state''
      (STEP1 : istep thread lbl  state state')
      (STEP2 : istep thread lbl' state state'')
      (GEQ   : ProgToExecution.G state' = ProgToExecution.G state'') :
  lbl = lbl'.
Proof.
  cdes STEP1. cdes STEP2.
  inv ISTEP0.
  all: inv ISTEP2; rewrite <- ISTEP in ISTEP1; inv ISTEP1.
  3,4: by exfalso;
    unfold add, add_rmw in *;
    rewrite <- GEQ in UG0; rewrite UG in UG0; inv UG0;
      clear -H1; induction (acts (G state)); inv H1.
  all: assert (val = val0); desf;
    rewrite <- GEQ in UG0; rewrite UG in UG0; inv UG0;
    pose proof (app_eq _ _ H0 (ThreadEvent thread (eindex state))) as AA.
  1,2: by rewrite !upds in *; inv AA.
  rewrite updo in *; [rewrite upds in *|].
  2: { intros BB. inv BB. omega. }
  rewrite updo in *; [rewrite upds in *|].
  2: { intros BB. inv BB. omega. }
  inv AA.
Qed.

Lemma unique_lbl_istep thread lbl lbl' state state'
      (STEP1 : istep thread lbl  state state')
      (STEP2 : istep thread lbl' state state') :
  lbl = lbl'.
Proof. eapply unique_lbl_istep_same_G; eauto. Qed.

Lemma unique_lbl_ilbl_step thread lbl lbl' state state'
      (STEP1 : ilbl_step thread lbl  state state')
      (STEP2 : ilbl_step thread lbl' state state') :
  lbl = lbl'.
Proof.
  cdes STEP1.
  cdes STEP2.
  destruct STEP0 as [st0 [ST01 ST02]]. cdes ST01.
  destruct STEP3 as [st1 [ST11 ST12]]. cdes ST11.
  destruct_seq_r ST02 as STBL.
  destruct_seq_r ST12 as STBL'.
  eapply unique_lbl_istep_same_G; eauto.
  erewrite <- eps_steps_same_G with (state':=state'); eauto.
  eapply eps_steps_same_G; eauto.
Qed.

Lemma wf_thread_state_ilbl_step thread lbls state state'
      (WTS  : wf_thread_state thread state)
      (STEP : ilbl_step thread lbls state state') :
  wf_thread_state thread state'.
Proof.
  eapply wf_thread_state_steps; eauto.
  apply rtE. right. eapply ilbl_step_in_steps; eauto.
Qed.

Lemma wf_thread_state_lbl_step thread state state'
      (WTS  : wf_thread_state thread state)
      (STEP : lbl_step thread state state') :
  wf_thread_state thread state'.
Proof. cdes STEP. eapply wf_thread_state_ilbl_step; eauto. Qed.

Lemma wf_thread_state_lbl_steps thread state state'
      (WTS  : wf_thread_state thread state)
      (STEPS : (lbl_step thread)＊ state state') :
  wf_thread_state thread state'.
Proof.
  apply clos_rt_rt1n in STEPS.
  induction STEPS; auto.
  apply IHSTEPS. eapply wf_thread_state_lbl_step; eauto.
Qed.

(****************************
** Destruction of lbl_step **
*****************************)

Lemma lbl_step_cases thread lbls state state'
      (WFT : wf_thread_state thread state)
      (ILBL_STEP : ilbl_step thread lbls state state') :
  exists lbl lbl',
    ⟪ LBLS : lbls = opt_to_list lbl' ++ [lbl] ⟫ /\
    ( ( ⟪ EINDEX : state'.(eindex) = 1 + state.(eindex) ⟫ /\
        ⟪ ACTS : acts_set state'.(G) ≡₁ 
                 acts_set state.(G) ∪₁ eq (ThreadEvent thread state.(eindex)) ⟫ /\
        ⟪ GLAB : lab state'.(G) = upd (lab state.(G)) (ThreadEvent thread state.(eindex)) lbl ⟫ /\
        ⟪ LBL'none : lbl' = None ⟫ /\
        ( (exists ord loc val, ⟪ LBL_LD : lbl = Aload false ord loc val ⟫) \/
          (exists ord loc val, ⟪ LBL_LD_EX : lbl = Aload true ord loc val ⟫) \/
          (exists ord loc val, ⟪ LBL_ST : lbl = Astore Xpln ord loc val ⟫) \/
          (exists ord, ⟪ LBL_F : lbl = Afence ord ⟫) ) /\
        ⟪ GRMW : rmw state'.(G) = rmw state.(G) ⟫ ) \/
      ( ⟪ EINDEX : state'.(eindex) = 2 + state.(eindex) ⟫ /\
        ⟪ ACTS : acts_set state'.(G) ≡₁ 
                 acts_set state.(G) ∪₁ 
                 eq (ThreadEvent thread state.(eindex)) ∪₁ eq (ThreadEvent thread (1 + state.(eindex))) ⟫ /\
        ⟪ GLAB : lab state'.(G) = 
                 upd_opt (upd (lab state.(G)) (ThreadEvent thread state.(eindex)) lbl) 
                              (Some (ThreadEvent thread (1 + state.(eindex)))) lbl' ⟫ /\
        (exists xmod ordr ordw loc valr valw, 
          ⟪ LBL_LD_EX : lbl = Aload true ordr loc valr ⟫ /\
          ⟪ LBL_ST_EX : lbl' = Some (Astore xmod ordw loc valw) ⟫ ) /\
        ⟪ GRMW : rmw state'.(G) ≡ rmw state.(G) ∪ 
                 eq (ThreadEvent thread state.(eindex)) × eq (ThreadEvent thread (1 + state.(eindex))) ⟫ )).
Proof. 
  eapply ilbl_step_alt in ILBL_STEP; desf. 
  cdes ISTEP. 
  edestruct ISTEP0; desf; do 2 eexists. 

  Ltac nupd_helper UINDEX UG := 
    split;
      [ erewrite opt_to_list_none; by apply app_nil_l
      | left; splits; eauto 20;
        [ symmetry; etransitivity;
          [ erewrite Nat.add_comm; by erewrite <- UINDEX
          | symmetry; eapply steps_same_eindex; eauto;
            eapply wf_thread_state_step; eauto;
            econstructor; eauto ]
        | erewrite eps_steps_same_G; eauto;
          unfold add in UG; rewrite UG;
          unfold acts_set; simpl; basic_solver
        | erewrite eps_steps_same_G; eauto;
          unfold add in UG; rewrite UG;
          unfold acts_set; simpl; basic_solver
        | erewrite eps_steps_same_G; [|eauto];
          unfold add in UG; by rewrite UG
        ]
      ].

  1-4: nupd_helper UINDEX UG.

  Ltac upd_helper UINDEX UG := 
    split; 
      [ erewrite opt_to_list_some; unfold "++"; eauto
      | right; splits; eauto 20;
        [ symmetry; etransitivity;
          [ erewrite Nat.add_comm; by erewrite <- UINDEX
          | symmetry; eapply steps_same_eindex; eauto;
            eapply wf_thread_state_step; eauto;
            econstructor; eauto ]
        | erewrite eps_steps_same_G; eauto;
          unfold add in UG; unfold add_rmw in UG; rewrite UG;
          unfold acts_set, upd_opt; simpl;
          rewrite Nat.add_1_r; basic_solver
        | erewrite eps_steps_same_G; eauto;
          unfold add in UG; unfold add_rmw in UG; rewrite UG;
          unfold acts_set, upd_opt; simpl;
          rewrite Nat.add_1_r; basic_solver           
        | erewrite eps_steps_same_G; [|eauto];
          unfold add_rmw in UG; rewrite UG; simpl;
          rewrite Nat.add_comm; basic_solver
        ]
      ].

  all: upd_helper UINDEX UG.

Qed.

Lemma lbl_step_lbls thread lbls state state'
      (WFT : wf_thread_state thread state)
      (ILBL_STEP : ilbl_step thread lbls state state') :
  exists lbl lbl', lbls = opt_to_list lbl' ++ [lbl].
Proof. 
  edestruct lbl_step_cases as [lbl [lbl' [LBLS _]]]; eauto. 
Qed.

Lemma ineps_step_eindex_shift thread lbl st st'
      (STEP : ineps_step thread lbl st st') :
  eindex st' = eindex st + length lbl.
Proof.
  cdes STEP. erewrite istep_eindex_shift with (st':=st'); eauto.
Qed.

Lemma eps_step_eindex_same thread st st'
      (STEP : istep thread [] st st') :
  eindex st' = eindex st.
Proof. erewrite istep_eindex_shift; eauto. simpls. omega. Qed.

Lemma eps_steps_eindex_same thread st st'
      (STEP : (istep thread [])＊ st st') :
  eindex st' = eindex st.
Proof.
  induction STEP; auto.
  2: by intuition.
  erewrite eps_step_eindex_same; eauto.
Qed.

Lemma ilbl_step_eindex_shift thread lbl st st'
      (STEP : ilbl_step thread lbl st st') :
  eindex st' = eindex st + length lbl.
Proof.
  cdes STEP.
  destruct STEP0 as [st'' [ST ST']].
  destruct_seq_r ST' as BB.
  arewrite (eindex st' = eindex st'').
  { eapply eps_steps_eindex_same. eauto. }
  eapply ineps_step_eindex_shift; eauto.
Qed.

Lemma ineps_step_eindex_lt thread st st' lbl
      (STEP : ineps_step thread lbl st st') :
  eindex st < eindex st'.
Proof.
  erewrite ineps_step_eindex_shift with (st':=st'); eauto.
  cdes STEP. destruct lbl; simpls. omega.
Qed.

Lemma ilbl_step_eindex_lt thread st st' lbl
      (STEP : ilbl_step thread lbl st st') :
  eindex st < eindex st'.
Proof.
  erewrite ilbl_step_eindex_shift with (st':=st'); eauto.
  apply ilbl_step_alt in STEP. desf.
  destruct lbl; simpls. omega.
Qed.

Lemma lbl_step_eindex_lt thread st st'
      (STEP : lbl_step thread st st') :
  eindex st < eindex st'.
Proof.
  cdes STEP.
  eapply ilbl_step_eindex_lt; eauto.
Qed.

Lemma istep_eindex_lbl thread lbl lbl' st st'
      (WTS : wf_thread_state thread st)
      (STEP: istep thread (opt_to_list lbl' ++ [lbl]) st st') :
  lbl = lab (ProgToExecution.G st') (ThreadEvent thread (eindex st)).
Proof.
  cdes STEP. inv ISTEP0.
  1-2: by destruct lbl'; simpls.

  1-4: apply app_eq_unit in LABELS; desf.
  1-4: by rewrite UG; unfold add in *; simpls; rewrite upds.

  all: apply app_eq_unit2 in LABELS; desf.
  all: rewrite UG; unfold add_rmw in *; simpls.
  all: rewrite updo; [|intros BB; inv BB; omega].
  all: by rewrite upds.
Qed.

Lemma ilbl_step_eindex_lbl thread lbl lbl' st st'
      (WTS : wf_thread_state thread st)
      (STEP: ilbl_step thread (opt_to_list lbl' ++ [lbl]) st st') :
  lbl = lab (ProgToExecution.G st') (ThreadEvent thread (eindex st)).
Proof.
  edestruct lbl_step_cases with (state0:=st) (state':=st')
    as [l [l']]; eauto. desf.
  all: rewrite GLAB.
  1-4: by rewrite upds; apply app_inj_tail in LBLS; desf.
  unfold upd_opt. rewrite updo.
  2: intros BB; inv BB; omega.
  apply app_inj_tail in LBLS; desf. by rewrite upds.
Qed.

Lemma istep_eindex_lbl' thread lbl lbl' st st'
      (WTS : wf_thread_state thread st)
      (STEP: istep thread (opt_to_list (Some lbl') ++ [lbl]) st st') :
  lbl' = lab (ProgToExecution.G st') (ThreadEvent thread (1 + eindex st)).
Proof.
  assert (eindex st + 1 = 1 + eindex st) 
    as HH by omega.
  cdes STEP; inv ISTEP0;
    apply opt_to_list_app_singl_pair in LABELS; desf;
    rewrite UG; unfold add_rmw in *; simpls;
    by rewrite HH, upds.
Qed.

Lemma ilbl_step_eindex_lbl' thread lbl lbl' st st'
      (WTS : wf_thread_state thread st)
      (STEP: ilbl_step thread (opt_to_list (Some lbl') ++ [lbl]) st st') :
  lbl' = lab (ProgToExecution.G st') (ThreadEvent thread (1 + eindex st)).
Proof.
  edestruct lbl_step_cases with (state0:=st) (state':=st')
    as [l [l']]; eauto. desf.
  all: rewrite GLAB.
  by rewrite upd_opt_some, upds.
Qed.
