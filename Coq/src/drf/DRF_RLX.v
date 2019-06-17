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
Require Import StepWf.

Module DRF.

Definition program_execution P S X :=
  ⟪ steps : (step Weakestmo)＊ (prog_es_init P) S⟫ /\
  ⟪ exec : Execution.t S X ⟫.

Definition RLX_race_free_program P :=
  (forall S X, program_execution P S X -> Race.rc11_consistent_x S X -> Race.RLX_race_free S X).

Lemma wf_es P
      (S : ES.t)
      (STEPS : (step Weakestmo)＊ (prog_es_init P) S):
  ES.Wf S.
Proof.
   specialize (clos_refl_trans_ind_left ES.t
                                       (step Weakestmo)
                                       (prog_es_init P)
                                       (ES.Wf)).
   intro H. apply H. 
   { admit.  (* apply prog_init_wf. *) }
   { admit. }
   auto.
Admitted.
  
Lemma jf_in_hb P
      (RACE_FREE : RLX_race_free_program P)
      (S : ES.t)
      (STEPS : (step Weakestmo)＊ (prog_es_init P) S):
  S.(ES.jf) ⊆ S.(hb).
Proof.
  Locate "＊". SearchAbout clos_refl_trans.
  specialize (clos_refl_trans_ind_left ES.t
                                       (step Weakestmo)
                                       (prog_es_init P)
                                       (fun s => s.(ES.jf) ⊆ s.(hb))).
  intro H. apply H. 1, 3: auto; basic_solver.
  clear H STEPS S. intros G G' STEPS IH STEP. 
  assert (WF : ES.Wf G').
  { eapply wf_es with (P := P). eapply transitive_rt. 2: apply rt_step. all: eauto. } 
  
  inversion_clear STEP as [e H]. destruct H as [e']. desc. 
  assert (q: G.(hb) ⊆ G'.(hb)). { admit. }
  inversion_clear TT as [H | [H | [H | H]]].
  1, 3: inversion_clear H; desc; rewrite JF'; basic_solver. 
  { inversion_clear H as [w]; desc.
    assert (hh : (G'.(hb)⁼ w e) \/ (not (G'.(hb)⁼ w e))) by admit. 
    destruct hh as [[eq_w_e | [ hb_w_e | hb_e_w]] | not_hb_w_e].
    { admit. }
    { inversion_clear AJF; desc. rewrite JF'. apply inclusion_union_l.
      { basic_solver. }
      unfold AddJF.jf_delta. basic_solver. }         
    { exfalso.
      inversion_clear BSTEP.
      assert (coh : (irreflexive (G'.(hb) ⨾ (G'.(eco) Weakestmo)^?))).
      { apply coh. auto. }
      destruct coh with (x := e).
      unfold "⨾". exists w. split.
      { basic_solver. }
      { apply r_step. unfold eco. apply ct_step.
        repeat apply inclusion_union_r1.
        unfold ES.rf. unfold "\". split.
        { unfold "⨾". exists w. split.
          { apply ES.ew_refl; eauto. inversion AJF. desc. admit. }
          admit.

Admitted.

Lemma rf_in_jf (S : ES.t) (X : eventid -> Prop)
      (WF : ES.Wf S)
      (EXEC : Execution.t S X)
      (JF_IN_HB : S.(ES.jf) ⊆ S.(hb)):
  (⦗X⦘ ⨾ S.(ES.rf) ⨾ ⦗X⦘) ⊆ S.(ES.jf).
Proof.
  unfolder; intros x y H. 
  destruct H as [x_in_X [rf_x_y y_in_X]].
  unfold ES.rf in rf_x_y; unfolder in rf_x_y.
  destruct rf_x_y as [[z [ew_x_z jf_z_y]] n_cf].
  specialize (JF_IN_HB z y jf_z_y) as hb_z_y.
  assert (z_in_X: X z).
  { specialize (Execution.hb_prcl S X EXEC).
    intro H. unfolder in H. eauto with hahn. }
  eapply ES.ewc in ew_x_z as H. 2: auto. destruct H.
  { basic_solver. }
  specialize (Execution.ex_ncf S X EXEC) as cf_free.
  destruct cf_free with (x := x) (y := z); basic_solver.
Qed.

Lemma po_rf_acyclic (S : ES.t) (X : eventid -> Prop)
      (WF : ES.Wf S)
      (CONS : es_consistent S (m := Weakestmo))
      (EXEC : Execution.t S X)
      (JF_IN_HB : S.(ES.jf) ⊆ S.(hb)):
  acyclic (⦗X⦘ ⨾ S.(ES.sb) ⨾ ⦗X⦘ ∪ ⦗X⦘ ⨾ S.(ES.rf) ⨾ ⦗X⦘).
Proof.
  specialize (rf_in_jf S X WF EXEC JF_IN_HB) as rf_in_jf.
  assert (hb_acyclic: acyclic S.(hb)).
  { apply trans_irr_acyclic.
    { eapply hb_irr; eauto. }
    eauto with hahn. }
  erewrite rf_in_jf, JF_IN_HB.
  arewrite (S.(ES.sb) ⊆ S.(hb)).
  rewrite <- restr_relE, inclusion_restr.
  by rewrite unionK.
Qed. 
  
End DRF.
