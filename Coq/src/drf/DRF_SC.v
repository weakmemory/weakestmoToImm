From hahn Require Import Hahn.
From imm Require Import Events Prog ProgToExecutionProperties RC11.
From PromisingLib Require Import Basic.
Require Import AuxDef.
Require Import AuxRel.
Require Import EventStructure.
Require Import Consistency.
Require Import Execution.
Require Import Step.
Require Import Race.
Require Import ProgES.
Require Import StepWf.
Require Import ExecutionToG.

Require Import DRF_RLX.

Set Implicit Arguments.

Theorem drf_rc11_sc P S X
      (RA_RACE_FREE : sc_ra_race_free_program P)
      (EXEC : program_execution P S X)
      (RC11 : rc11_consistent_ex S X) :
  sc_consistent_ex S X.
Proof.
Admitted.

Theorem drf_sc P S X
        (nInitProg : ~ IdentMap.In tid_init P)
        (RA_RACE_FREE : sc_ra_race_free_program P)
        (EXEC : program_execution P S X) :
  sc_consistent_ex S X.
Proof.
  eapply drf_rc11_sc; eauto.
  eapply drf_rlx; eauto.
  red. intros S' X' EXEC' RC11.
  apply ra_race_free_in_rlx_race_free, RA_RACE_FREE; auto.
  eby eapply drf_rc11_sc.
Qed.
