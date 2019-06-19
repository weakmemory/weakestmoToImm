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


Definition HB_prefix S v1 v2 := dom_rel (S.(hb)^? ⨾ (⦗eq v1⦘ ∪ ⦗eq v2⦘)). 


Lemma wf_es P
      (S : ES.t)
      (STEPS : (step Weakestmo)＊ (prog_es_init P) S):
  ES.Wf S.
Proof.
  eapply clos_refl_trans_ind_left; eauto.
  { admit. }
  ins. eapply step_wf; eauto.
Admitted.


Lemma ra_jf_in_hb S (WF : ES.Wf S) :
  ⦗Rel S⦘ ⨾ S.(ES.jf) ⨾ ⦗Acq S⦘ ⊆ S.(hb). 
Proof.
  rewrite <- sw_in_hb.
  unfold sw.
  rewrite <- inclusion_id_cr. rewrite seq_id_l.
  rewrite (dom_l WF.(ES.jfE)) at 1.
  rewrite (dom_l WF.(ES.jfD)) at 1.
  rewrite !seqA.
  arewrite (⦗Rel S⦘ ⨾ ⦗E S⦘ ⨾ ⦗W S⦘ ⊆ release S); [|done].
  unfold release, rs.
  basic_solver 20.
Qed.

Lemma codom_rel_helper {A} (r : relation A) d (IN:  codom_rel r ⊆₁ d) : r ≡ r ⨾ ⦗d⦘.
Proof.
unfolder in *; basic_solver.
Qed.

Lemma r_hb_in_imm_sb_hb S (WF : ES.Wf S) :
  ⦗R S⦘ ⨾ S.(hb) ⊆ immediate S.(ES.sb) ⨾ S.(hb)^?.
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
  intro HH. apply HH. 1, 3: auto; basic_solver.
  clear HH STEPS S. intros G G' STEPS IH STEP.
  
  assert (STEPS_G' : (step Weakestmo)＊ (prog_es_init P) G').
  { eapply transitive_rt; eauto. apply rt_step. auto. }
  
  assert (WF_G : ES.Wf G).
  { eapply wf_es; eauto. }
  assert (WF_G' : ES.Wf G').
  { eapply wf_es; eauto. } 
  
  inversion_clear STEP as [e H]. destruct H as [e']. desc. 
  assert (q: G.(hb) ⊆ G'.(hb)).
  { eapply step_hb_mon; eauto. }
  inversion_clear TT as [S | [S | [S | S]]].
  1, 3: inversion_clear S; desc; rewrite JF'; basic_solver. 
  {
    inversion S as [w]; desc.
    inversion_clear AJF. desf.
    assert (NCF: ~ (cf G') w e) by auto. 
    assert (W_w : is_w (lab G') w). 
    { eapply load_step_W; eauto. intuition. }
    assert (E_r : is_r (lab G') e) by auto.
    assert (HB : (G'.(hb)⁼ w e) \/ (not (G'.(hb)⁼ w e))) by apply classic.
    assert (JF : jf G' w e).
    { apply JF'. apply inclusion_union_r2. basic_solver. }
    assert (ACTS_MON : E G ⊆₁ E G').
    { eapply BasicStep.basic_step_nupd_acts_mon. eauto. }

    destruct HB as [[EQ_W_E | [ HB_W_E | HB_E_W]] | NOT_HB_W_E].
    { exfalso. SearchAbout ES.acts_set.
      eapply BasicStep.basic_step_acts_set_ne; eauto.
      rewrite <- EQ_W_E. auto. }
    { rewrite JF'. apply inclusion_union_l.
      { basic_solver. }
      unfold AddJF.jf_delta. basic_solver. }         
    { exfalso. eapply coh; eauto.
      eexists. split; eauto.
      apply r_step. unfold eco. apply ct_step.
        repeat apply inclusion_union_r1.
        unfold ES.rf. unfold "\". split; auto.
        unfold "⨾". exists w. split; auto.
        apply ES.ew_refl; eauto. 
        assert (SAME_W : ⦗E G' ∩₁ W G'⦘ ≡ ⦗E G ∩₁ W G⦘).
        { apply eqv_rel_more. eapply load_step_W; eauto. } 
        apply SAME_W. desf. }
    exfalso.
    set (A := HB_prefix G' e w).
    assert (PREF_EXEC : program_execution P G' A).
    { red. splits; auto. unfold A, HB_prefix. constructor.
      { rewrite cr_seq. 
        repeat rewrite dom_union, set_subset_union_l. splits.
        1, 2: basic_solver.
        rewrite hbE; basic_solver. }
      { erewrite <- dom_cross with (d := Einit G') (d' := eq e).
        apply dom_rel_mori. rewrite <- sb_in_hb.
        { rewrite  codom_rel_helper with (d := eq e).
          { apply inclusion_seq_mon; [|done].
            erewrite cross_mori with (x0 := eq e) (y0 := Eninit G'); eauto.
            { erewrite ES.sb_init; eauto with hahn. }
            rewrite BasicStep.basic_step_acts_ninit_set; eauto with hahn. }
          basic_solver. }
        unfolder. intuition. eauto with hahn. }
      1: rewrite sb_in_hb.
      2: rewrite sw_in_hb.
      1, 2: rewrite dom_rel_eqv_dom_rel; apply dom_rel_mori;
        rewrite <- seqA; apply inclusion_seq_mon; eauto with hahn;
          rewrite (rewrite_trans_seq_cr_r (hb_trans G')); eauto with hahn.
      all: admit. }
    assert (PREF_RC11 : Race.rc11_consistent_x G' A).
    { unfold Race.rc11_consistent_x. admit. }
    
    specialize (RACE_FREE G' A PREF_EXEC PREF_RC11).
    
    assert (RACE_W : Race.race G' A w).
    { unfold Race.race. unfold dom_rel. exists e. unfolder. splits.
      1, 2: unfold A; unfold HB_prefix; basic_solver 10. 
      apply or_not_and. left. apply or_not_and. left. apply and_not_or. auto. }

    assert (RACE_E : Race.race G' A e).
    { unfold Race.race. unfold dom_rel. exists w. unfolder. splits.
      1, 2: unfold A; unfold HB_prefix; basic_solver 10. 
      apply or_not_and. left. apply or_not_and. left. apply and_not_or. split.
      { unfolder in NOT_HB_W_E. intuition. }
      intro. apply ES.cf_sym in H0. auto. }
    specialize (RACE_FREE w RACE_W) as QW.
    specialize (RACE_FREE e RACE_E) as QE.
    destruct QE as [False_W | True_W]; destruct QW as [True_E | False_E].
    1, 2, 4: try unfolder in False_W; try unfolder in False_E; desf;
      unfold is_w, is_r in *; basic_solver.
    apply proj1 in True_E. apply proj1 in True_W.
    unfold Race.RLX_race_free in RACE_FREE.
    unfolder in NOT_HB_W_E. apply NOT_HB_W_E. right. left.
    apply ra_jf_in_hb; eauto with hahn. basic_solver. }
  admit. 

Admitted.

Lemma rf_in_jf (S : ES.t) (X : eventid -> Prop)
      (WF : ES.Wf S)
      (EXEC : Execution.t S X)
      (JF_IN_HB : S.(ES.jf) ⊆ S.(hb)):
  ⦗X⦘ ⨾ S.(ES.rf) ⨾ ⦗X⦘ ⊆ S.(ES.jf).
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
