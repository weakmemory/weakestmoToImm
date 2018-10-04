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
  set_compl (codom_rel (istep thread [])).

Definition lbl_step thread (state state' : state) :=
  exists lbls state'',
    ⟪ NNIL      : lbls <> [] ⟫ /\
    ⟪ LBL_STEP  : istep thread lbls state state'' ⟫ /\
    ⟪ EPS_STEPS : (istep thread [])＊ state'' state' ⟫ /\
    ⟪ STABLE    : stable_state thread state' ⟫.

Definition stable_lprog thread lprog :=
  forall state (INSTR : state.(instrs) = lprog)
         (REACH : (step thread)＊ (init lprog) state),
    exists state',
      ⟪ STEPS : (istep thread [])＊ state state' ⟫ /\
      ⟪ STABLE : stable_state thread state' ⟫.

Lemma get_stable thread lprog state
      (LPST : stable_lprog thread lprog)
      (INSTR : state.(instrs) = lprog)
      (REACH : (step thread)＊ (init lprog) state) :
  exists ! state',
    ⟪ STEPS : (istep thread [])＊ state state' ⟫ /\
    ⟪ STABLE : stable_state thread state' ⟫.
Proof.
  edestruct LPST as [state']; eauto.
  desf.
  exists state'.
  red. splits; auto.
  clear -STEPS STABLE.
  (* TODO: follows from unique_eps_step and definition of stable_state. *)
Admitted.

Lemma terminal_stable thread : is_terminal ⊆₁ stable_state thread.
Proof.
  intros state TERM [state' HH].
  cdes HH.
  assert (nth_error (instrs state') (pc state') <> None) as YY.
  { by rewrite <- ISTEP. }
  apply nth_error_Some in YY.
  red in TERM. desf; [by inv TERM|].
  rewrite INSTRS in *.
  inv ISTEP0.
  (* TODO: First we need to fix a bug in IMM's `ifgoto` step. *)

  (* { omega. } *)
  (* desf. *)
  (* { omega. } *)
  (* clear -UPC YY TERM. *)
Admitted.

Lemma steps_stable_lbl_steps thread :
  ⦗ stable_state thread ⦘ ⨾ (step thread)＊ ⨾ ⦗ stable_state thread ⦘ ⊆ (lbl_step thread)＊.
Proof.
Admitted.