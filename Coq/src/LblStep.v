Require Import Omega.
From hahn Require Import Hahn.
From imm Require Import Events Execution
     Prog ProgToExecution ProgToExecutionProperties.

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
  red in TERM. desf; [by inv TERM|].
  rewrite INSTRS in *.
  inv ISTEP0; desf.
  all: omega.
Qed.

Definition ineps_step thread lbls (state state' : state) :=
  ⟪ NNIL : lbls <> [] ⟫ /\
  ⟪ STEP : istep thread lbls state state' ⟫.

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

Lemma ineps_step_dom_stable thread lbls :
  ineps_step thread lbls ⊆ ⦗ stable_state thread ⦘ ⨾ ineps_step thread lbls.
Proof.
  intros x y HH. cdes HH.
  apply seq_eqv_l. split; auto.
  intros [z AA].
  cdes STEP.
  cdes AA.
  rewrite <- ISTEP in ISTEP1. inv ISTEP1.
  inv ISTEP2.
  all: inv ISTEP0.
Qed.

Lemma steps_stable_lbl_steps thread :
  ⦗ stable_state thread ⦘ ⨾ (step thread)＊ ⨾ ⦗ stable_state thread ⦘ ⊆ (lbl_step thread)＊.
Proof.
Admitted.
