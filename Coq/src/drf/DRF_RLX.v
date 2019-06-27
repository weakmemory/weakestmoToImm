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

Set Implicit Arguments.

Module DRF.

Definition program_execution P S X :=
  ⟪ STEPS : (step Weakestmo)＊ (prog_es_init P) S⟫ /\
  ⟪ EXEC : Execution.t S X ⟫.

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
  clear dependent S.
  intros S S' STEPS WF_S STEP.
  inversion STEP as [e]. desf.  
  eapply step_wf; eauto.
  admit.
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


Lemma ct_imm_split_l {A} (r : relation A)
      (IRR: irreflexive r)
      (TANS: transitive r)
      (acts : list A)
      (DOM_IN_ACTS: dom_rel r ⊆₁ (fun x : A => In x acts)):
  r ≡ immediate r ⨾ r^?.
Proof.
  split.
  2: { basic_solver. }
  rewrite ct_imm1 at 1; eauto.
  rewrite ct_begin. apply seq_mori; [done|].
  rewrite immediate_in. apply  rt_of_trans; eauto.
Qed.

Lemma hb_imm_split_l S
      (WF: ES.Wf S)
      (CONS : es_consistent S (m := Weakestmo)):
  S.(hb) ≡ immediate S.(hb) ⨾ S.(hb)^?.
Proof.
  eapply ct_imm_split_l.
  { eapply hb_irr. eauto. }
  { eauto with hahn. }
  rewrite (dom_l (hbE S WF)).
  rewrite dom_seq, dom_eqv, ES.E_alt.
  eauto.
Qed.

Lemma imm_clos_trans {A} (r : relation A) :
  immediate r⁺ ⊆ immediate r.
Proof.
  split.
  { assert (immediate r⁺ ⊆ r); eauto.
    rewrite immediateE.
    rewrite ct_begin at 1. rewrite rt_begin, seq_union_r, minus_union_l.
    rewrite seq_id_r. apply inclusion_union_l; eauto with hahn.
    erewrite inclusion_minus_mon with (r' := r ⨾ r ⨾ r＊) (s' := r ⨾ r ⨾ r＊); [|done|].
    { rewrite minus_absorb; done. }
    rewrite ct_begin at 1. rewrite ct_end, seqA.  apply seq_mori; eauto with hahn.
    rewrite <- seqA, rt_rt.
    rewrite <- ct_begin, ct_end.
    eauto with hahn. }
  intros. apply ct_step in R1. apply ct_step in R2.
  inversion H. eauto.
Qed.

Lemma imm_union {A} (r1 r2 : relation A):
  immediate (r1 ∪ r2) ⊆ immediate r1 ∪ immediate r2.
Proof.
  basic_solver 10.
Qed.  

Lemma r_hb_in_imm_sb_hb S
      (WF : ES.Wf S)
      (CONS : es_consistent S (m := Weakestmo)):
  ⦗R S⦘ ⨾ S.(hb) ⊆ immediate S.(ES.sb) ⨾ S.(hb)^?.
Proof.
  rewrite hb_imm_split_l at 1; auto.
  rewrite <- seqA. apply seq_mori; [|done]. 
  unfold hb. rewrite imm_clos_trans.
  rewrite imm_union, seq_union_r.
  apply inclusion_union_l; [basic_solver|].
  rewrite immediate_in, (dom_l (swD S WF)). type_solver. 
Qed.

Lemma dom_eqv_tr_codom {A} (r : relation A):
  dom_rel r ≡₁ codom_rel r⁻¹.
Proof.
  basic_solver.
Qed.

Lemma tr_dom_eqv_codom {A} (r : relation A):
  dom_rel r⁻¹ ≡₁ codom_rel r.
Proof.
  basic_solver.
Qed.

Lemma codom_rel_eqv_dom_rel {A} (r r' : relation A):
  codom_rel (⦗dom_rel r⦘ ⨾ r') ≡₁ codom_rel (r⁻¹ ⨾ r').
Proof.
  basic_solver.
Qed.

Lemma dom_in_seq_with_tr {A} (r: relation A):
  ⦗dom_rel r⦘ ⊆ r ⨾ r⁻¹. 
Proof.
  basic_solver.
Qed.


Lemma dom_ct {A} (r : relation A) :
  dom_rel r⁺ ≡₁ dom_rel r.
Proof.
  rewrite ct_begin.
  basic_solver 7.
Qed.

Lemma t_rmw_hb_in_hb S
      (WF : ES.Wf S)
      (CONS : es_consistent S (m := Weakestmo)):
  S.(ES.rmw)⁻¹ ⨾ S.(hb) ⊆ S.(hb)^?.
Proof.
  rewrite WF.(ES.rmwD).
  rewrite (dom_l WF.(ES.rmwEninit)).
  repeat rewrite transp_seq.
  rewrite ES.rmwi; eauto.
  rewrite !seqA, !transp_eqv_rel.
  rewrite r_hb_in_imm_sb_hb; eauto.
  rewrite <- seq_eqvK with (dom := Eninit S), seqA.
  rewrite <- seqA with (r1 := (immediate (sb S))⁻¹).
  rewrite <- transp_eqv_rel with (d := Eninit S) at 1.
  rewrite <- transp_seq.
  rewrite <- seqA with (r3 := (hb S)^?).
  arewrite !(⦗Eninit S⦘ ⨾ immediate (sb S) ⊆ immediate (sb S) ∩  ES.same_tid S).
  { erewrite <- inter_absorb_l with (r := ⦗Eninit S⦘ ⨾ immediate (sb S))
                                   (r' := immediate (sb S)); [|basic_solver].
    erewrite seq_mori; [|apply inclusion_refl2|apply immediate_in].
    rewrite ES.sb_tid; eauto with hahn. }
  rewrite transp_inter.
  erewrite transp_sym_equiv with (r := (ES.same_tid S)); [| apply ES.same_tid_sym].
  rewrite <- seqA with (r3 := (hb S)^?).
  rewrite HahnEquational.inter_trans; [| apply ES.same_tid_trans].
  rewrite ES.imm_tsb_imm_sb_in_icf; auto.
  arewrite (⦗W S⦘ ⨾ (ES.icf S)^? ≡ ⦗W S⦘).
  { erewrite  (dom_rel_helper (icf_R S CONS)). type_solver. }
  basic_solver.
Qed.


Lemma hb_prefix_cf_free (S : ES.t)
           (WF : ES.Wf S)
           (CONS : es_consistent (m := Weakestmo) S)
           (e w : eventid)
           (JF : jf S w e):
  ES.cf_free S (HB_prefix S e w).
Proof.
  unfold HB_prefix.
  red. rewrite dom_in_seq_with_tr, !seqA.
  arewrite (((hb S)^? ⨾ (⦗eq e⦘ ∪ ⦗eq w⦘))⁻¹ ⨾
             cf S ⨾
             (hb S)^? ⨾ (⦗eq e⦘ ∪ ⦗eq w⦘) ⊆ ∅₂); [|basic_solver].
  rewrite transp_seq, transp_union, transp_cr, !transp_eqv_rel, !seqA.
  rewrite !seq_union_r, !seq_union_l.
  apply inclusion_union_l; apply inclusion_union_l.
  1, 4:
    rewrite <- seqA with (r3 := (hb S)^? ⨾ ⦗eq _⦘);
    rewrite <- seqA with (r3 := ⦗eq _⦘);
    rewrite <- restr_relE;
    rewrite restr_irrefl_eq; eauto with hahn;
    rewrite !seqA;
    apply (ecf_irf S CONS).
  2:
    apply inclusion_transpE;
    rewrite !transp_seq, !transp_eqv_rel;
    rewrite !transp_cr, transp_inv, !seqA;
    rewrite transp_sym_equiv with (r := cf S); [| apply ES.cf_sym];
    rewrite transp_sym_equiv with (r := ∅₂); [| basic_solver].
  all:
    erewrite <- jf_necf; eauto;
    apply inclusion_inter_r; [basic_solver|];
    rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r; eauto with hahn. 
Qed.

Lemma jfe_in_jf (S : ES.t)
      (WF : ES.Wf S):
  S.(ES.jfe) ⊆ S.(ES.jf).
Proof.
  eauto with hahn.
Qed.

Lemma union_seq_compl_sym_trans_rr {A} (e r1 r2 : relation A)
      (SYM : symmetric e)
      (TRANS : transitive e)
      (R2_IN_CE : r2 ⊆ e):
  ((compl_rel e) ∩ (r1 ⨾ r2) ≡ (compl_rel e) ∩ r1 ⨾ r2).
Proof.
  basic_solver 10.
Qed.

Lemma compl_rel_invol {A} (r : relation A)
  (DECID : forall x y : A, Decidable.decidable (r x y)):
  (compl_rel (compl_rel r) ≡ r).
Proof.
  generalize NNPP. ins.
  unfolder. split. 
  { ins. apply H. auto. }
  ins. apply Decidable.not_not; intuition.
Qed.

Lemma union_seq_compl_equiv_rr2 {A} (e r1 r2 : relation A)
      (DECID : forall x y : A, Decidable.decidable (e x y))
      (SYM : symmetric (compl_rel e))
      (TRANS : transitive (compl_rel e))
      (R2_IN_CE : r2 ⊆ compl_rel e):
  (e ∩ (r1 ⨾ r2) ≡ e ∩ r1 ⨾ r2).
Proof.
  set (e' := compl_rel e) in *.
  arewrite (e ≡ compl_rel e').
  { apply same_rel_Symmetric. eapply compl_rel_invol; eauto. }
  apply union_seq_compl_sym_trans_rr; eauto.
Qed.

Lemma union_seq_cf_same_tid_r (S : ES.t) (m : model)
      (CONS : es_consistent S (m := m))
      (WF : ES.Wf S)
      (r1 r2 : relation eventid)
      (SAME_TID : r2 ⊆ compl_rel (ES.same_tid S))
  : S.(ES.cf) ∩ (r1 ⨾ r2) ≡ S.(ES.cf) ∩ r1 ⨾ r2.
Admitted.
    
  

Lemma cc_alt (S : ES.t) (m : model) (CONS : es_consistent S (m := m)) (WF : ES.Wf S):
  cc S ≡ S.(ES.cf) ∩ (S.(ES.jfe) ⨾ (S.(ES.sb) ∪ S.(ES.jf))＊).
Proof.
  unfold cc.
  split.
  { apply inclusion_inter_mon; auto with hahn.
    rewrite jfe_in_jf at 2; auto.
    apply inclusion_seq_mon; auto with hahn.
    rewrite crE, !seq_union_r, seq_id_r.
    apply inclusion_union_l.
    { rewrite <- rt_unit at 2. basic_solver 10. }
    rewrite <- rt_unit at 2. 
    rewrite <- rt_unit at 2. 
    basic_solver 10. }
  rewrite <- interK with (r := cf S) at 1.
  rewrite interA.
  apply inclusion_inter_mon; auto with hahn.
  rewrite rtE at 1.
  rewrite seq_union_r, seq_id_r, inter_union_r.
  apply inclusion_union_l.
  { rewrite ES.cf_same_tid. rewrite jfe_alt at 1; eauto.
    basic_solver. }
  rewrite ES.jfi_union_jfe at 1.
  rewrite <- !unionA.
  arewrite (jfi S ⊆ sb S).
  rewrite unionK.
  rewrite path_ut_last.
  rewrite seq_union_r, inter_union_r.
  apply inclusion_union_l.
  { arewrite (cf S ∩ (jfe S ⨾ (sb S)⁺) ⊆ ∅₂); [|done].
    rewrite (ct_of_trans (ES.sb_trans WF)).
    arewrite (jfe S ⊆ compl_rel(ES.same_tid S) ⨾ ⦗Eninit S⦘).
    { rewrite jfe_alt; eauto.
      rewrite ES.jf_nEinit_alt; eauto.
      basic_solver. }
    rewrite ES.sb_tid; eauto.
    rewrite ES.cf_same_tid.
    arewrite (compl_rel (ES.same_tid S) ⨾ ES.same_tid S ⊆
                        compl_rel (ES.same_tid S)); [|basic_solver].
    unfolder. intros p q HH. destruct HH as [z [NPZ SQ]]. 
    intro PQ.
    apply ES.same_tid_sym in SQ.
    generalize ES.same_tid_trans. basic_solver. }
  rewrite inclusion_inter_l2.
  repeat apply inclusion_seq_mon; eauto with hahn.
  apply (rt_of_trans (ES.sb_trans WF)).
Qed.
  
Lemma jf_in_hb P
      (RACE_FREE : RLX_race_free_program P)
      (S : ES.t)
      (STEPS : (step Weakestmo)＊ (prog_es_init P) S):
  S.(ES.jf) ⊆ S.(hb).
Proof.
  eapply clos_refl_trans_ind_left with (P := fun s => s.(ES.jf) ⊆ s.(hb)); eauto.
  { basic_solver. }
  clear dependent S.
  intros G G' STEPS IH STEP.
  assert (STEPS_G' : (step Weakestmo)＊ (prog_es_init P) G').
  { eapply transitive_rt; eauto. apply rt_step. auto. }
  assert (WF_G : ES.Wf G).
  { eapply wf_es; eauto. }
  assert (WF_G' : ES.Wf G').
  { eapply wf_es; eauto. } 
  generalize (hb_trans G'). intro HB_TRANS.    
  inversion_clear STEP as [e [e' HH]]. desf.
  assert (HB_MON: G.(hb) ⊆ G'.(hb)).
  { eapply step_hb_mon; eauto. }
  rename TT into STEP_.
  inversion STEP_ as [S | [S | [S | S]]].
  1, 3: inversion_clear S; desf; rewrite JF'; basic_solver. 
  { inversion S as [w HH]. desf.
    unfold AddJF.add_jf in AJF. desf.
    unfold AddJF.jf_delta in JF'. 
    rename rE' into eE', rR' into eR'.
    assert (wW' : is_w (lab G') w). 
    { eapply load_step_W; eauto. intuition. }
    assert (WE_JF' : jf G' w e).
    { apply JF'. apply inclusion_union_r2. basic_solver. }
    assert (ACTS_MON : E G ⊆₁ E G').
    { eapply BasicStep.basic_step_nupd_acts_mon; eauto. }

    assert (HB : (G'.(hb)⁼ w e) \/ (not (G'.(hb)⁼ w e))) by apply classic.
    destruct HB as [[WE_EQ | [ WE_HB | EW_HB]] | WE_NHB].
    { exfalso.
      eapply BasicStep.basic_step_acts_set_ne; eauto. 
      basic_solver. }
    { rewrite JF'. basic_solver. } 
    { unfold transp in EW_HB.
      exfalso. eapply coh; eauto.
      eexists. split; eauto.
      apply r_step. apply rf_in_eco.
      apply ES.jf_in_rf; eauto. } 
    exfalso.
    assert (HB_CLOS_PREFIX : dom_rel(hb G' ⨾ ⦗HB_prefix G' e w⦘) ⊆₁ HB_prefix G' e w).
    { unfold HB_prefix.
      rewrite dom_rel_eqv_dom_rel.
      rewrite <- seqA, (rewrite_trans_seq_cr_r (hb_trans G')).      
      basic_solver 10. }
    assert (HB_DOM : dom_rel (hb G') ⊆₁ E G).
    { eapply step_nupd_hb_dom; eauto. }
    assert (JF_CLOS_PREFIX : dom_rel(jf G' ⨾ ⦗HB_prefix G' e w⦘) ⊆₁ HB_prefix G' e w).
    { unfold HB_prefix.
      rewrite dom_rel_eqv_dom_rel.
      rewrite JF', IH.
      unfold AddJF.jf_delta.
      type_solver 9. }
    assert (PREF_EXEC : program_execution P G' (HB_prefix G' e w)).
    { red. splits; auto. constructor. 
      { unfold HB_prefix.
        arewrite (eq e ⊆₁ E G'); [basic_solver|].
        arewrite (eq w ⊆₁ E G'); [basic_solver|].
        rewrite hbE; auto.
        basic_solver. }
      { unfold HB_prefix.
        erewrite <- sb_in_hb.
        erewrite <- ES.sb_init; auto.
        rewrite BasicStep.basic_step_acts_ninit_set; eauto.
        basic_solver 10. }
      { rewrite sb_in_hb. apply HB_CLOS_PREFIX. }
      { rewrite sw_in_hb. apply HB_CLOS_PREFIX. }
      { unfold HB_prefix.
        rewrite codom_rel_eqv_dom_rel, <- tr_dom_eqv_codom.
        apply dom_rel_mori.
        rewrite !transp_seq, !transp_inv.
        rewrite crE at 1.
        rewrite seq_union_l, seq_union_r, seq_id_l.
        apply inclusion_union_l. 
        { rewrite BasicStep.basic_step_nupd_rmw; eauto.
          rewrite ES.rmwE; auto.
          rewrite ES.rmwD; eauto.
          assert (E_NOT_IN_G: ~ E G e).
          { eapply BasicStep.basic_step_acts_set_ne; eauto. }
          type_solver. }
        generalize (t_rmw_hb_in_hb WF_G' CONS).
        basic_solver 10. }
      { unfold HB_prefix.
        rewrite set_interC, <- dom_eqv1.
        rewrite dom_eqv_tr_codom, codom_rel_eqv_dom_rel.
        rewrite !transp_seq, transp_union, !transp_eqv_rel, transp_cr, !seqA.
        rewrite crE at 1.
        rewrite seq_union_l with (r2 := (hb G')⁻¹), seq_id_l.
        rewrite seq_union_r, codom_union. apply set_subset_union_l. split.
        { generalize (ES.jf_in_rf WF_G').
          type_solver 10. }
        apply codom_rel_mori.
        arewrite (G'.(hb) ≡ ⦗E G⦘ ⨾ G'.(hb)) at 1.
        { apply dom_rel_helper. auto. }
        rewrite transp_seq, seqA, transp_eqv_rel, seq_eqv.
        rewrite BasicStep.basic_step_r_eq_r; eauto.
        rewrite (ES.jf_complete WF_G). 
        rewrite <- seq_eqvK with (dom := codom_rel (jf G)).
        rewrite <- tr_dom_eqv_codom at 1.
        rewrite dom_in_seq_with_tr, transp_inv.
        rewrite IH at 1.
        rewrite ES.jf_in_rf; auto.
        rewrite HB_MON, seqA.
        rewrite <- codom_rel_helper; eauto.
        rewrite  <- seqA with (r1 := (hb G')⁻¹).
        rewrite (rewrite_trans (transitive_transp HB_TRANS)).

        rewrite (step_rf_mon BSTEP STEP_ WF_G).
        basic_solver 10. }
      { apply hb_prefix_cf_free; auto. }
      unfold vis; splits; constructor;
      rename x into v, H into vPREF.  
      { assert (dom_rel ((hb G')^? ⨾ (⦗eq e⦘ ∪ ⦗eq w⦘)) ⊆₁ (E G')); [|basic_solver].
        rewrite hbE; auto. basic_solver. }
      arewrite (cc G' ⨾ ⦗eq v⦘ ⊆ ∅₂); [|done].
      apply eq_predicate in vPREF.
      assert (AE' : HB_prefix G' e w ⊆₁ E G').
      { unfold HB_prefix.
        rewrite hbE; auto. basic_solver. }
      assert (CC_IN_HB : cc G ⊆ hb G).
      { unfold cc. rewrite inclusion_inter_l2.
        rewrite jfe_in_jf; auto.
        rewrite sb_in_hb, IH.
        generalize (hb_trans G). ins.
        relsf. }

      generalize (hb_prefix_cf_free WF_G' CONS WE_JF') as PREF_CF_FREE. ins.
      assert (DOM_CC'_V_IN_A : dom_rel (cc G' ⨾ ⦗eq v⦘) ⊆₁ HB_prefix G' e w).
      {
        assert (EE_DOM : dom_rel(jfe G' ⨾ (sb G' ∪ jf G')＊ ⨾ ⦗HB_prefix G' e w⦘)
                                ⊆₁ HB_prefix G' e w).
        { arewrite ((sb G' ∪ jf G')＊ ⨾ ⦗HB_prefix G' e w⦘
                                   ⊆ ⦗HB_prefix G' e w⦘ ⨾ (sb G' ∪ jf G')＊).
          { apply dom_r2l_rt.
            assert (DOM': dom_rel((sb G' ∪ jf G') ⨾ ⦗HB_prefix G' e w⦘)
                                 ⊆₁ HB_prefix G' e w).
            { rewrite sb_in_hb. relsf. }
            rewrite (dom_rel_helper DOM'). basic_solver. }
          rewrite jfe_in_jf; eauto.
          rewrite <-seqA, dom_seq. auto. }
        rewrite cc_alt, vPREF; eauto.
        rewrite <- seq_eqv_inter_rr, seqA. 
        rewrite (dom_rel_helper EE_DOM).
        basic_solver. }
      rewrite (dom_rel_helper DOM_CC'_V_IN_A).
      rewrite vPREF.
      unfold cc. rewrite inclusion_inter_l1.  
      auto. }
   
    assert (PREF_RC11 : Race.rc11_consistent_x G' (HB_prefix G' e w)).
    { unfold Race.rc11_consistent_x. admit. }
    
    specialize (RACE_FREE G' (HB_prefix G' e w) PREF_EXEC PREF_RC11).
    
    assert (RACE_W : Race.race G' (HB_prefix G' e w) w).
    { unfold Race.race. unfold dom_rel. exists e.
      unfolder. splits.
      1, 2: unfold HB_prefix; basic_solver 10.
      apply or_not_and. left. apply or_not_and. left. apply and_not_or. auto. }

    assert (RACE_E : Race.race G' (HB_prefix G' e w) e).
    { unfold Race.race. unfold dom_rel. exists w.
      unfolder. splits.
      1, 2: unfold HB_prefix; basic_solver 10. 
      apply or_not_and. left. apply or_not_and. left. apply and_not_or. split.
      { unfolder in WE_NHB. intuition. }
      intro HH. auto. apply ES.cf_sym in HH. auto. }
    specialize (RACE_FREE w RACE_W) as QW.
    specialize (RACE_FREE e RACE_E) as QE.
    destruct QE as [|wREL]; destruct QW as [eACQ|].
    1, 2, 4: type_solver.
    unfold Race.RLX_race_free in RACE_FREE.
    unfolder in WE_NHB.
    apply WE_NHB. right. left.
    apply ra_jf_in_hb; auto.
    apply proj1 in eACQ. apply proj1 in wREL.
    basic_solver. }
  admit. 

Admitted.

Lemma rf_in_jf (S : ES.t) (X : eventid -> Prop)
      (WF : ES.Wf S)
      (EXEC : Execution.t S X)
      (JF_IN_HB : S.(ES.jf) ⊆ S.(hb)):
  ⦗X⦘ ⨾ S.(ES.rf) ⨾ ⦗X⦘ ⊆ S.(ES.jf).
Proof.
  unfolder; intros x y HH. 
  destruct HH as [xX [xyRF yX]].
  unfold ES.rf in xyRF; unfolder in xyRF. 
  destruct xyRF as [[z [xzEW zyJF]] NCF].
  specialize (JF_IN_HB z y zyJF) as zyHB.
  assert (zX: X z).
  { apply (Execution.hb_prcl S X EXEC).
    unfolder. eauto. }
  eapply ES.ewc in xzEW as HH; auto.
  destruct HH; [basic_solver|].
  specialize (Execution.ex_ncf S X EXEC) as CF_FREE.
  destruct CF_FREE with (x := x) (y := z).
  basic_solver.
Qed.

Lemma po_rf_acyclic (S : ES.t) (X : eventid -> Prop)
      (WF : ES.Wf S)
      (CONS : es_consistent S (m := Weakestmo))
      (EXEC : Execution.t S X)
      (JF_IN_HB : S.(ES.jf) ⊆ S.(hb)):
  acyclic (⦗X⦘ ⨾ S.(ES.sb) ⨾ ⦗X⦘ ∪ ⦗X⦘ ⨾ S.(ES.rf) ⨾ ⦗X⦘).
Proof.
  rewrite sb_in_hb.
  rewrite (rf_in_jf WF EXEC JF_IN_HB), JF_IN_HB.
  specialize (hb_acyclic S Weakestmo CONS) as HB_ACYCLIC.
  rewrite <- restr_relE, inclusion_restr.
  relsf.
Qed.
  
End DRF.
