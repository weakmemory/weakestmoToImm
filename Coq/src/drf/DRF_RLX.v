From hahn Require Import Hahn.
From imm Require Import Events AuxRel Prog ProgToExecutionProperties RC11.
Require Import AuxDef.
Require Import AuxRel.
Require Import EventStructure.
Require Import Consistency.
Require Import Execution.
Require Import Step.
Require Import Race.
Require Import ProgES.

Module DRF.

Definition rc11_consistent_ (S : ES.t) (X : eventid -> Prop) := True. (* TODO *)

Definition program_execution P S X :=
  ⟪ steps : (step Weakestmo)＊ (prog_es_init P) S⟫ /\
  ⟪ exec : Execution.t S X ⟫.
  

Lemma jf_in_hb P
      (pr : forall S X, program_execution P S X -> rc11_consistent_ S X -> Race.RLX_race_free S X)
      (S : ES.t)
      (steps : (step Weakestmo)＊ (prog_es_init P) S):
  S.(ES.jf) ⊆ S.(hb).
Proof.

Admitted.

Lemma rf_in_jf (S : ES.t) (X : eventid -> Prop)
      (wf : ES.Wf S)
      (exec : Execution.t S X)
      (p : S.(ES.jf) ⊆ S.(hb)):
  (⦗X⦘ ⨾ S.(ES.rf) ⨾ ⦗X⦘) ⊆ S.(ES.jf).
Proof.
  unfolder; ins; desf.
  unfold ES.rf in H0. unfolder in H0. repeat destruct H0. unfolder in p.
  specialize (p x0 y H3).
  assert (x0_in_X: X x0).
  { specialize (Execution.hb_prcl S X exec); intros; unfolder in H4; eauto with hahn. }
    specialize (ES.ewc wf); intros; unfolder in H4; specialize (H4 x x0).
    destruct H4; subst; auto.
    specialize (Execution.ex_ncf S X exec) as cf_free.
    destruct cf_free with (x := x) (y := x0); basic_solver.
Qed.

End DRF.
