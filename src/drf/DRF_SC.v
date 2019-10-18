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
Require Import ExecutionToGraph.

Require Import DRF_RLX.

Require Import Race_G.
Require Import SC.

Set Implicit Arguments.

Theorem drf_rc11_sc P G
        (RA_RACE_FREE : sc_ra_race_free_program_G P)
        (RC11 : rc11_consistent G) :
  sc_consistent G.
Proof.
Admitted.

Theorem drf_sc P S X
        (nInitProg : ~ IdentMap.In tid_init P)
        (PP : ProgLoc.prog_locs (stable_prog_to_prog P) <> [])
        (RA_RACE_FREE : sc_ra_race_free_program_G (stable_prog_to_prog P))
        (EXEC : program_execution P S X) :
  sc_consistent_ex S X.
Proof.
  assert (RLX_RACE_FREE : rc11_rlx_race_free_program_G (stable_prog_to_prog P)).
  { intros G EXEC_G RC11.
    apply ra_race_free_G_in_rlx_race_free_G.
    apply RA_RACE_FREE; auto.
    eby eapply drf_rc11_sc. }
  specialize (drf_rlx nInitProg PP EXEC RLX_RACE_FREE) as RC11_ex.
  cdes RC11_ex.
  eexists. splits; eauto.
  eby eapply drf_rc11_sc.
Qed.
