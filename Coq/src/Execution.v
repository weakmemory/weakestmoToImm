From hahn Require Import Hahn.
From imm Require Import Events AuxRel.
(* TODO : get rid of dependency on Step, move corresponding lemmas to Step.v *)
Require Import AuxDef.
Require Import AuxRel.
Require Import EventStructure.
Require Import Consistency.

Module Execution.

Section Execution.

Variable S : ES.t.

Notation "'E'" := S.(ES.acts_set).
Notation "'Einit'" := S.(ES.acts_init_set).
Notation "'Eninit'" := S.(ES.acts_ninit_set).

Notation "'lab'" := S.(ES.lab).

Notation "'sb'" := S.(ES.sb).
Notation "'rmw'" := S.(ES.rmw).
Notation "'ew'" := S.(ES.ew).
Notation "'jf'" := S.(ES.jf).
Notation "'rf'" := S.(ES.rf).
Notation "'fr'" := S.(ES.fr).
Notation "'co'" := S.(ES.co).
Notation "'cf'" := S.(ES.cf).

Notation "'rs'" := S.(rs).
Notation "'release'" := S.(release).
Notation "'sw'" := S.(sw).
Notation "'hb'" := S.(hb).


Notation "'jfe'" := S.(ES.jfe).
Notation "'rfe'" := S.(ES.rfe).
Notation "'coe'" := S.(ES.coe).
Notation "'jfi'" := S.(ES.jfi).
Notation "'rfi'" := S.(ES.rfi).
Notation "'coi'" := S.(ES.coi).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).

Notation "'same_tid'" := S.(ES.same_tid).
Notation "'same_lab'" := S.(ES.same_lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).

Notation "'Loc_' l" := (fun x => loc x = l) (at level 1).

Notation "'Pln'" := (fun a => is_true (is_only_pln S.(ES.lab) a)) (at level 10).
Notation "'Rlx'" := (fun a => is_true (is_rlx S.(ES.lab) a)) (at level 10).
Notation "'Rel'" := (fun a => is_true (is_rel S.(ES.lab) a)) (at level 10).
Notation "'Acq'" := (fun a => is_true (is_acq S.(ES.lab) a)) (at level 10).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel S.(ES.lab) a)) (at level 10).
Notation "'Sc'" := (fun a => is_true (is_sc S.(ES.lab) a)) (at level 10).

Record t (X : eventid -> Prop) :=
  mk { ex_inE : X ⊆₁ E ;
       init_in_ex : Einit ⊆₁ X ;

       ex_sb_prcl : dom_rel (sb ⨾ ⦗X⦘) ⊆₁ X ;
       ex_sw_prcl : dom_rel (sw ⨾ ⦗X⦘) ⊆₁ X ;
       
       ex_rmw_fwcl : codom_rel (⦗X⦘ ⨾ rmw) ⊆₁ X ;

       ex_rf_compl : X ∩₁ R ⊆₁ codom_rel (⦗X⦘ ⨾ rf) ;
       
       ex_ncf : ES.cf_free S X ; 

       ex_vis : X ⊆₁ vis S ;
     }.

Lemma co_total (WF : ES.Wf S) X (exec : t X) : 
  forall ol, is_total (X ∩₁ W ∩₁ Loc_ ol) co. 
Proof. 
  red. ins. 
  unfolder in IWa.
  unfolder in IWb.
  desc.
  edestruct ES.co_total; eauto.
  { unfolder; splits; eauto. 
    eapply ex_inE; eauto. }
  { unfolder; splits; eauto. 
    eapply ex_inE; eauto. }
  intros EW.
  apply ES.ewc in EW; auto.
  destruct EW as [EQ | CF]; auto.
  eapply ex_ncf; eauto.
  basic_solver.
Qed.

Lemma hb_prcl X (exec : t X) : 
  dom_rel (hb ⨾ ⦗X⦘) ⊆₁ X.
Proof. 
  rewrite seq_eqv_r.
  intros x [y [HB yX]].
  induction HB as [x y [SB | SW] | ]; auto.
  { apply ex_sb_prcl; auto. basic_solver 10. }
  apply ex_sw_prcl; auto. basic_solver 10. 
Qed.

Lemma ex_rff X
      (WF : ES.Wf S)
      (EXEC : t X) : 
  functional ((restr_rel X rf)⁻¹).
Proof. apply (ES.ncf_rff WF (ex_ncf X EXEC)). Qed.

Section ExecutionRels.

  Variable X : eventid -> Prop.
  Variable EXEC : t X.

  Definition ex_Einit := Einit.
  Definition ex_Eninit := Eninit ∩₁ X.

  Definition ex_rmw := restr_rel X rmw.
  Definition ex_sb := restr_rel X sb.
  Definition ex_jf := restr_rel X jf.
  Definition ex_co := restr_rel X co.
  Definition ex_ew := restr_rel X ew.

  Definition ex_same_tid := restr_rel X same_tid.
  Definition ex_cf := ⦗ex_Eninit⦘ ⨾ (ex_same_tid \ ex_sb⁼) ⨾ ⦗ex_Eninit⦘.
  Definition ex_rf := restr_rel X rf.
  Definition ex_fr := ex_rf⁻¹ ⨾ ex_co.
  Definition ex_rs := ⦗X ∩₁ W⦘ ⨾ (ex_sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (ex_rf ⨾ ex_rmw)＊.
  Definition ex_release := ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ ex_sb)^? ⨾ ex_rs.
  Definition ex_sw := ex_release ⨾ ex_rf ⨾ (ex_sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘.
  Definition ex_hb := (ex_sb ∪ ex_sw)⁺.

  Definition ex_rfe := ex_rf \ ex_sb.
  Definition ex_coe := ex_co \ ex_sb.

  Definition ex_rfi := ex_rf ∩ ex_sb.
  Definition ex_coi := ex_co ∩ ex_sb.

  Definition ex_eco := ex_rf ∪ ex_co ⨾ ex_rf^? ∪ ex_fr ⨾ ex_rf^?.

  Lemma ex_rf_restr_jf 
        (WF : ES.Wf S)
        (JF_PRCL : dom_rel (jf ⨾ ⦗X⦘) ⊆₁ X) :
    ex_rf ≡ restr_rel X jf.
  Proof.
    symmetry.
    unfold ex_rf.
    apply functional_codom_inclusion.
    { by rewrite ES.jf_in_rf. }
    { rewrite restr_relE at 1.
      rewrite (dom_r WF.(ES.rfD)), (dom_r WF.(ES.rfE)).
      rewrite !seqA.
      arewrite (⦗E⦘ ⨾ ⦗R⦘ ≡ ⦗E ∩₁ R⦘) by basic_solver.
      rewrite WF.(ES.jf_complete).
      rewrite eqv_codom_in_seq_tr, seqA.
      rewrite codom_seq, codom_seq, codom_seq.
      rewrite (dom_rel_helper JF_PRCL).
      by rewrite restr_relE. }
    by apply ex_rff.
  Qed.
   
  Lemma rf_in_ew_ex_rf  
        (WF : ES.Wf S) : 
    rf ⨾ ⦗X⦘ ⊆ ew ⨾ ex_rf.
  Proof.
    rewrite <- seq_eqvK at 1.
    rewrite (dom_r WF.(ES.rfD)) at 1. 
    rewrite !seqA. 
    arewrite (⦗R⦘ ⨾ ⦗X⦘ ≡ ⦗X ∩₁ R⦘) by basic_solver.
    rewrite (ex_rf_compl X EXEC) at 1.
    rewrite eqv_codom_in_seq_tr.
    rewrite transp_seq, !seqA, <- seqA.
    rewrite WF.(ES.rf_trf_in_ew).
    unfold ex_rf.
    basic_solver 5.
  Qed.

  
  Lemma ex_rs_alt_r
        (WF : ES.Wf S)
        (JF_PRCL : dom_rel (jf ⨾ ⦗X⦘) ⊆₁ X) :
    ex_rs ≡ rs ⨾ ⦗X⦘.
  Proof.
    unfold Consistency.rs, ex_rs.
    rewrite !seqA.
    assert (PRCL_JF_RMW : dom_rel (jf ⨾ rmw ⨾ ⦗X⦘) ⊆₁ X).
    { rewrite WF.(ES.rmw_in_sb).
      rewrite (dom_rel_helper (ex_sb_prcl X EXEC)).
      rewrite <- seqA, (dom_rel_helper JF_PRCL).
      basic_solver. }
    rewrite <- seqA in PRCL_JF_RMW.
    apply prcl_rt in PRCL_JF_RMW as PRCL_JF_RMW_RT.
    rewrite (dom_rel_helper PRCL_JF_RMW_RT).
    rewrite <- restr_relE.
    rewrite (restr_rt_prcl PRCL_JF_RMW).
    arewrite (restr_rel X (jf ⨾ rmw) ≡ ex_rf ⨾ ex_rmw).
    { rewrite restr_relE, seqA.
      erewrite dom_rel_helper with (r := rmw ⨾ ⦗X⦘).
      2: { rewrite WF.(ES.rmw_in_sb).
           apply (ex_sb_prcl X EXEC). }
      rewrite ex_rf_restr_jf; auto.
      unfold ex_rmw.
      basic_solver 10. }
    arewrite (⦗W⦘ ⨾ ⦗X⦘ ≡ ⦗X⦘ ⨾ ⦗W⦘) by basic_solver.
    arewrite ((sb ∩ same_loc)^? ⨾ ⦗X⦘ ≡ ⦗X⦘ ⨾ (ex_sb ∩ same_loc)^?).
    { assert (PRCL_SB_SL : dom_rel ((sb ∩ same_loc) ⨾ ⦗X⦘) ⊆₁ X).
      { rewrite inclusion_inter_l1.
        apply (ex_sb_prcl X EXEC). }
      erewrite dom_rel_helper with (r := (sb ∩ same_loc)^? ⨾ ⦗X⦘).
      2 : { by apply prcl_cr. }
      rewrite <- restr_relE, restr_cr_prcl_r; auto.
      unfold ex_sb. basic_solver 10. }
    specialize (ex_inE X EXEC).
    basic_solver 15.
  Qed.

  Lemma rs_prcl 
        (WF : ES.Wf S)
        (JF_PRCL : dom_rel (jf ⨾ ⦗X⦘) ⊆₁ X) :
    dom_rel (rs ⨾ ⦗X⦘) ⊆₁ X.
  Proof.
    rewrite <- ex_rs_alt_r; auto.
    unfold ex_rs.
    basic_solver.
  Qed.
  
  Lemma ex_rs_alt
        (WF : ES.Wf S)
        (JF_PRCL : dom_rel (jf ⨾ ⦗X⦘) ⊆₁ X) :
    ex_rs ≡ restr_rel X rs.
  Proof.
    rewrite restr_relE.
    rewrite <- ex_rs_alt_r; auto.
    unfold ex_rs.
    basic_solver 20.
  Qed.
    
  Lemma ex_release_alt_r 
        (WF : ES.Wf S)
        (JF_PRCL : dom_rel (jf ⨾ ⦗X⦘) ⊆₁ X) :
    ex_release ≡ release ⨾ ⦗X⦘.
  Proof.
    unfold ex_release.
    unfold Consistency.release.
    rewrite !seqA.
    erewrite dom_rel_helper with (r := rs ⨾ ⦗X⦘).
    2: { by apply rs_prcl. }
    rewrite ex_rs_alt, restr_relE; auto.
    arewrite ((⦗F⦘ ⨾ sb)^? ⨾ ⦗X⦘ ≡ (⦗F⦘ ⨾ ex_sb)^? ⨾ ⦗X⦘).
    { assert (PRCL : dom_rel (⦗F⦘ ⨾ sb ⨾ ⦗X⦘) ⊆₁ X).
      { specialize (ex_sb_prcl X EXEC). basic_solver. }
      rewrite <- seqA in PRCL.
      apply prcl_cr in PRCL as PRCL'.
      rewrite (dom_rel_helper PRCL'). 
      rewrite <- restr_relE, restr_cr_prcl_r; auto.
      unfold ex_sb.
      basic_solver 10. }
    done.
  Qed.

  Lemma release_prcl 
        (WF : ES.Wf S)
        (JF_PRCL : dom_rel (jf ⨾ ⦗X⦘) ⊆₁ X) :
    dom_rel (release ⨾ ⦗X⦘) ⊆₁ X.
  Proof.
    rewrite <- ex_release_alt_r; auto.
    unfold ex_release, ex_sb.
    rewrite ex_rs_alt; auto.
    basic_solver 10.
  Qed.

  Lemma ex_release_alt 
        (WF : ES.Wf S)
        (JF_PRCL : dom_rel (jf ⨾ ⦗X⦘) ⊆₁ X) :
    ex_release ≡ restr_rel X release.
  Proof.
    rewrite restr_relE.
    rewrite <- ex_release_alt_r; auto.
    unfold ex_release, ex_sb.
    rewrite ex_rs_alt; auto.
    basic_solver 20.
  Qed.

  Lemma ex_sw_alt_r
        (WF : ES.Wf S)
        (JF_PRCL : dom_rel (jf ⨾ ⦗X⦘) ⊆₁ X) : 
    ex_sw ≡ sw ⨾ ⦗X⦘.
  Proof.
    unfold ex_sw.
    unfold Consistency.sw.
    rewrite !seqA.
    arewrite (⦗Acq⦘ ⨾ ⦗X⦘ ≡ ⦗X⦘ ⨾ ⦗Acq⦘) by basic_solver.
    arewrite ((sb ⨾ ⦗F⦘)^? ⨾ ⦗X⦘ ≡ ⦗X⦘ ⨾ (ex_sb ⨾ ⦗F⦘)^?).
    { assert (PRCL : dom_rel (sb ⨾ ⦗F⦘ ⨾ ⦗X⦘) ⊆₁ X).
      { specialize (ex_sb_prcl X EXEC). basic_solver. }
      rewrite <- seqA in PRCL.
      apply prcl_cr in PRCL as PRCL'.
      rewrite (dom_rel_helper PRCL'). 
      rewrite <- restr_relE, restr_cr_prcl_r; auto.
      unfold ex_sb.
      basic_solver 10. }
    seq_rewrite (dom_rel_helper JF_PRCL).
    rewrite <- seq_eqvK with (dom := X) at 1.
    rewrite !seqA.
    seq_rewrite <- restr_relE.
    seq_rewrite ex_release_alt_r; auto.
    rewrite <- ex_rf_restr_jf; auto.
    basic_solver.
  Qed.

  Lemma sw_prcl
        (WF : ES.Wf S)
        (JF_PRCL : dom_rel (jf ⨾ ⦗X⦘) ⊆₁ X) : 
    dom_rel (sw ⨾ ⦗X⦘) ⊆₁ X.
  Proof.
    rewrite <- ex_sw_alt_r; auto.
    unfold ex_sw, ex_rf. 
    rewrite restr_relE.
    seq_rewrite (ex_release_alt_r); auto.
    rewrite dom_seq.
    by apply release_prcl.
  Qed.

  Lemma ex_sw_alt 
        (WF : ES.Wf S)
        (JF_PRCL : dom_rel (jf ⨾ ⦗X⦘) ⊆₁ X) :
    ex_sw ≡ restr_rel X sw.
  Proof.
    rewrite restr_relE.
    rewrite <- ex_sw_alt_r; auto.
    unfold ex_sw, ex_rf .
    rewrite restr_relE.
    rewrite <- seq_eqvK at 1 4.
    rewrite !seqA.
    seq_rewrite <- restr_relE.
    rewrite ex_release_alt; auto.
    basic_solver 20.
  Qed.
    
  Lemma ex_hb_alt 
        (WF : ES.Wf S)
        (JF_PRCL : dom_rel (jf ⨾ ⦗X⦘) ⊆₁ X) :
    ex_hb ≡ restr_rel X hb.
  Proof.
    unfold ex_hb, Consistency.hb, ex_sb.
    rewrite ex_sw_alt; auto.
    rewrite union_restr.
    split; [by apply restr_ct|].
    apply ct_ind_right with (P := fun r => restr_rel X r).
    { red. splits.
      { red. red. basic_solver. }
      basic_solver 10. }
    apply ct_step.
    intros r HH.
    erewrite <- seq_restr_prcl.
    { rewrite HH. apply ct_unit. } 
    arewrite (sb ∪ sw ⊆ hb).
    apply hb_prcl. done.
  Qed.
    
  Lemma ex_fr_alt
        (WF : ES.Wf S) : 
    ex_fr ≡ restr_rel X fr .
  Proof.
    unfold ex_fr, ES.fr, ex_co, ex_rf.
    split; [basic_solver |].
    rewrite restr_relE, seqA.
    rewrite <- seqA, <- transp_eqv_rel, <- transp_seq at 1.
    rewrite WF.(rf_in_ew_ex_rf).
    unfold ex_rf; rewrite restr_relE.
    rewrite !transp_seq, transp_eqv_rel, !seqA.
    rewrite (transp_sym_equiv WF.(ES.ew_sym)).
    specialize ES.ew_co_in_co.
    basic_solver 15.
  Qed.

  Lemma ex_co_rf_alt
        (WF : ES.Wf S) : 
    ex_co ⨾ ex_rf ≡ restr_rel X (co ⨾ rf).
  Proof.
    split; [unfold ex_co, ex_rf; basic_solver |].
    rewrite restr_relE, seqA.
    rewrite WF.(rf_in_ew_ex_rf) at 1.
    arewrite (co ⨾ ew ⊆ co) by apply ES.co_ew_in_co.
    unfold ex_co, ex_rf.
    basic_solver 10.
  Qed.

  Lemma ex_fr_rf_alt
        (WF : ES.Wf S) : 
    ex_fr ⨾ ex_rf ≡ restr_rel X (fr ⨾ rf).
  Proof.
    rewrite WF.(ex_fr_alt).
    unfold ex_rf.
    split; [basic_solver|].
    rewrite restr_relE, seqA.
    rewrite WF.(rf_in_ew_ex_rf) at 1.
    unfold ES.fr. rewrite seqA.
    arewrite (co ⨾ ew ⊆ co) by apply ES.co_ew_in_co.
    unfold ex_rf.
    basic_solver 10.
  Qed.
  
  Lemma ex_eco_alt 
        (WF : ES.Wf S) : 
    ex_eco ≡ restr_rel X (eco S Weakestmo).
  Proof.
    unfold ex_eco.
    unfold ex_rf.
    unfold ex_co.
    rewrite (eco_alt S WF).
    rewrite !restr_union.
    repeat apply union_more; [done | |].
    { rewrite !crE, !seq_union_r, !seq_id_r.
      rewrite restr_union.
      apply union_more; [done |].
      by apply ex_co_rf_alt. }
    rewrite !crE, !seq_union_r, !seq_id_r.
    rewrite restr_union.
    apply union_more; [ by apply ex_fr_alt
                      | by apply ex_fr_rf_alt].
  Qed.

End ExecutionRels.

End Execution.
End Execution.
