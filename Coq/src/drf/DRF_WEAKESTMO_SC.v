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

Require Import DRF_WEAKESTMO_RLX.
Require Import DRF_RC11_SC.

Set Implicit Arguments.

Module DRF_WEAKESTMO_SC.

Theorem DRF_WEAKESTMO_SC P S X
        (nInitProg : ~ IdentMap.In tid_init P)
        (RA_RACE_FREE : SC_RA_race_free_program P)
        (EXEC : program_execution P S X) :
  sc_consistent_x S X.
Proof.
  eapply DRF_RC11_SC.DRF_RC11_SC; eauto.
  eapply DRF_WEAKESTMO_RLX.DRF_WEAKESTMO_RLX; eauto.
  red. intros S' X' EXEC' RC11.
  apply RA_race_free_in_RLX_race_free, RA_RACE_FREE; auto.
  eby eapply DRF_RC11_SC.DRF_RC11_SC.
Qed.

End DRF_WEAKESTMO_SC.
