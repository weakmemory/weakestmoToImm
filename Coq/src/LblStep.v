Require Import Omega.
From hahn Require Import Hahn.
From imm Require Import Events Execution
     Prog ProgToExecution ProgToExecutionProperties.
Require Import AuxRel.

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

Definition stable_state thread :=
  set_compl (dom_rel (istep thread [])).

Definition stable_lprog thread lprog :=
  forall state (INSTR : state.(instrs) = lprog)
         (REACH : (step thread)＊ (init lprog) state),
    exists state',
      ⟪ STEPS : (istep thread [])＊ state state' ⟫ /\
      ⟪ STABLE : stable_state thread state' ⟫.

Lemma get_stable thread state
      (LPST : stable_lprog thread state.(instrs))
      (REACH : (step thread)＊ (init state.(instrs)) state) :
  exists ! state',
    ⟪ STEPS : (istep thread [])＊ state state' ⟫ /\
    ⟪ STABLE : stable_state thread state' ⟫.
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

Lemma terminal_stable thread : is_terminal ⊆₁ stable_state thread.
Proof.
  intros state TERM [state' HH].
  cdes HH.
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
  ineps_step thread lbls ⨾ (istep thread [])＊ ⨾ ⦗ stable_state thread ⦘.

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

Lemma ilbl_steps_in_steps thread : (lbl_step thread)＊ ⊆ (step thread)＊.
Proof. rewrite lbl_step_in_steps. apply rt_of_ct. Qed.

Lemma ineps_eps_step_dom_empty thread lbls :
  dom_rel (ineps_step thread lbls) ∩₁ dom_rel (istep thread []) ≡₁ ∅.
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

Lemma ineps_step_stable_l thread lbls :
  ineps_step thread lbls ≡ ⦗ stable_state thread ⦘ ⨾ ineps_step thread lbls.
Proof.
  split; [|basic_solver].
  intros x y HH.
  apply seq_eqv_l. split; auto.
  intros [z AA].
  eapply ineps_eps_step_dom_empty.
  split; eexists; eauto.
Qed.

Lemma neps_step_stable_l thread :
  neps_step thread ≡ ⦗ stable_state thread ⦘ ⨾ neps_step thread.
Proof.
  split; [|basic_solver].
  intros x y HH.
  apply seq_eqv_l. split; auto.
  red in HH. desf.
  apply ineps_step_stable_l in HH.
  apply seq_eqv_l in HH. desf.
Qed.

Lemma lbl_step_alt thread :
  lbl_step thread ≡ neps_step thread ⨾ (istep thread [])＊ ⨾ ⦗stable_state thread⦘.
Proof.
  split.
  { intros x y [l [e HH]].
    eexists. split; [eexists|]; apply HH. }
  intros x y [e [[l AA] HH]].
  eexists. eexists. split; eauto.
Qed.

Lemma steps_stable_lbl_steps thread :
  ⦗ stable_state thread ⦘ ⨾ (step thread)＊ ⨾ ⦗ stable_state thread ⦘ ⊆ (lbl_step thread)＊.
Proof.
  arewrite (step thread ⊆ neps_step thread ∪ istep thread []).
  { intros x y HH. red in HH. desf.
    destruct lbls; [by right|].
    left. eexists. red.
      by splits; eauto. }
  rewrite rt_unionE.
  rewrite seqA.
  arewrite (⦗stable_state thread⦘ ⨾ (istep thread [])＊ ⊆ ⦗stable_state thread⦘).
  { rewrite rtE. rewrite seq_union_r.
    apply inclusion_union_l; [basic_solver|].
    rewrite ct_begin.
    arewrite (⦗stable_state thread⦘ ⨾ istep thread [] ⊆ ∅₂).
    2: basic_solver.
    intros x y HH.
    apply seq_eqv_l in HH. apply HH.
    eexists. apply HH. }
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
    ⟪ STABLE   : stable_state thread state'' ⟫.
Proof. 
  edestruct ILBL_STEP. 
  unfold seq in *. 
  unfold ineps_step in *. 
  unfold eqv_rel in *.
  desf. eexists. splits; eauto. 
Qed. 

Lemma same_pos_stable thread state state'
      (INSTR : state.(instrs) = state'.(instrs))
      (PC : state.(pc) = state'.(pc))
      (STABLE : stable_state thread state) :
    stable_state thread state'.
Proof.
  red. red. intros [state'' STEP].
  cdes STEP. inv ISTEP0; eapply STABLE.
  eexists (Build_state _ _ _ _ _ _ _).
  2: eexists (Build_state _
                          (if Event.Const.eq_dec (RegFile.eval_expr (regf state) expr) 0
                           then pc state + 1
                           else shift) _ _ _ _ _).
  all: red; splits; [by eauto|].
  all: eexists; splits; [by rewrite PC, INSTR; eauto|].
  { eapply assign; eauto; simpls. }
  eapply if_; eauto; simpls.
  desf.
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