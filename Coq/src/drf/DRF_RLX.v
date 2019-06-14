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
      (jf_in_hb : S.(ES.jf) ⊆ S.(hb)):
  (⦗X⦘ ⨾ S.(ES.rf) ⨾ ⦗X⦘) ⊆ S.(ES.jf).
Proof.
  unfolder; intros x y H. 
  destruct H as [x_in_X H]; destruct H as [rf_x_y  y_in_X].
  unfold ES.rf in rf_x_y; unfolder in rf_x_y.
  destruct rf_x_y as [H not_cf_x_y];
  destruct H as [z H];
  destruct H as [ew_x_z jf_z_y].
  specialize (jf_in_hb z y jf_z_y) as hb_z_y.
  assert (z_in_X: X z).
  { specialize (Execution.hb_prcl S X exec); intro H; unfolder in H; eauto with hahn. }
  specialize (ES.ewc wf). intro H. unfolder in H. specialize (H x z ew_x_z). destruct H.
  { basic_solver. }
  specialize (Execution.ex_ncf S X exec) as cf_free.
  destruct cf_free with (x := x) (y := z); basic_solver.
Qed.

Lemma po_rf_acyclic (S : ES.t) (X : eventid -> Prop)
      (wf : ES.Wf S)
      (cons : es_consistent S (m:=Weakestmo))
      (exec : Execution.t S X)
      (jf_in_hb : S.(ES.jf) ⊆ S.(hb)):
  acyclic (⦗X⦘ ⨾ S.(ES.sb) ⨾ ⦗X⦘ ∪ ⦗X⦘ ⨾ S.(ES.rf) ⨾ ⦗X⦘).
Proof.
  specialize (rf_in_jf S X wf exec jf_in_hb) as rf_in_jf.
  assert (hb_acyclic: acyclic S.(hb)).
  { apply trans_irr_acyclic.
    { eapply hb_irr; eauto. }
    eauto with hahn. }
  erewrite rf_in_jf, jf_in_hb.
  arewrite (S.(ES.sb) ⊆ S.(hb)).
  rewrite <- restr_relE, inclusion_restr.
  by rewrite unionK.
Qed. 
  
End DRF.
