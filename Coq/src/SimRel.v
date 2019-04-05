Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CombRelations SimTraversal SimulationRel AuxRel.
Require Import AuxRel.
Require Import AuxDef.
Require Import ImmProperties.
Require Import EventStructure.
Require Import Consistency.
Require Import Execution.
Require Import EventToAction.
Require Import LblStep.
Require Import SimRelCont.
Require Import SimRelEventToAction.
Require Import SimRelJF.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRel.
  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable X : eventid -> Prop.

  Notation "'SE'" := S.(ES.acts_set).
  Notation "'SEinit'" := S.(ES.acts_init_set).
  Notation "'SEninit'" := S.(ES.acts_ninit_set).
  Notation "'Stid'" := (S.(ES.tid)).
  Notation "'Slab'" := (S.(ES.lab)).
  Notation "'Sloc'" := (loc S.(ES.lab)).
  Notation "'K'" := S.(ES.cont_set).

  Notation "'STid' t" := (fun x => Stid x = t) (at level 1).
  Notation "'SNTid' t" := (fun x => Stid x <> t) (at level 1).

  Notation "'SR'" := (fun a => is_true (is_r Slab a)).
  Notation "'SW'" := (fun a => is_true (is_w Slab a)).
  Notation "'SF'" := (fun a => is_true (is_f Slab a)).
  Notation "'SRel'" := (fun a => is_true (is_rel Slab a)).
  Notation "'SAcq'" := (fun a => is_true (is_acq Slab a)).

  Notation "'Ssb'" := (S.(ES.sb)).
  Notation "'Scf'" := (S.(ES.cf)).
  Notation "'Srmw'" := (S.(ES.rmw)).
  Notation "'Sjf'" := (S.(ES.jf)).
  Notation "'Sjfi'" := (S.(ES.jfi)).
  Notation "'Sjfe'" := (S.(ES.jfe)).
  Notation "'Srf'" := (S.(ES.rf)).
  Notation "'Srfi'" := (S.(ES.rfi)).
  Notation "'Srfe'" := (S.(ES.rfe)).
  Notation "'Sco'" := (S.(ES.co)).
  Notation "'Sew'" := (S.(ES.ew)).

  Notation "'Srs'" := (S.(Consistency.rs)).
  Notation "'Srelease'" := (S.(Consistency.release)).
  Notation "'Ssw'" := (S.(Consistency.sw)).
  Notation "'Shb'" := (S.(Consistency.hb)).

  Notation "'thread_syntax' tid"  := 
    (Language.syntax (thread_lts tid)) (at level 10, only parsing).  

  Notation "'thread_st' tid" := 
    (Language.state (thread_lts tid)) (at level 10, only parsing).

  Notation "'thread_init_st' tid" := 
    (Language.init (thread_lts tid)) (at level 10, only parsing).
  
  Notation "'thread_cont_st' tid" :=
    (fun st => existT _ (thread_lts tid) st) (at level 10, only parsing).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).

  Notation "'Gtid'" := (tid).
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gloc'" := (loc G.(lab)).
  
  Notation "'GTid' t" := (fun x => tid x = t) (at level 1).
  Notation "'GNTid' t" := (fun x => tid x <> t) (at level 1).

  Notation "'GR'" := (fun a => is_true (is_r Glab a)).
  Notation "'GW'" := (fun a => is_true (is_w Glab a)).
  Notation "'GF'" := (fun a => is_true (is_f Glab a)).

  Notation "'GRel'" := (fun a => is_true (is_rel Glab a)).
  Notation "'GAcq'" := (fun a => is_true (is_acq Glab a)).
  
  Notation "'Gsb'" := (G.(sb)).
  Notation "'Grmw'" := G.(rmw).
  Notation "'Grf'" := (G.(rf)).
  Notation "'Gco'" := (G.(co)).

  Notation "'Grs'" := (G.(imm_s_hb.rs)).
  Notation "'Grelease'" := (G.(imm_s_hb.release)).
  Notation "'Ghb'" := (G.(imm_s_hb.hb)).

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Notation "'Gvf'" := (furr G sc).

  Notation "'Ssim_jf'" := (sim_jf G sc TC S X).
  Notation "'Ssim_vf'" := (sim_vf G sc TC S X).
  Notation "'DR'" := (DR G TC S X).

  Notation "'e2a'" := (e2a S).

  Record simrel_graph := 
    { gprclos : forall thread m n (LT : m < n) (EE : GE (ThreadEvent thread n)),
        GE (ThreadEvent thread m);
      rmwclos : forall r w (RMW : Grmw r w), C r <-> C w;
      irelcov : GW ∩₁ GRel ∩₁ I ⊆₁ C;
    }.

  Record simrel_common :=
    { noinitprog : ~ IdentMap.In tid_init prog ;
      gprog : program_execution prog G ;
      
      gwf   : Execution.Wf G ;
      swf   : ES.Wf S ;
      
      gcons : imm_consistent G sc ;
      scons : @es_consistent S Weakestmo ;

      tccoh : tc_coherent G sc TC ;

      sr_graph : simrel_graph ;

      sr_exec : Execution.t S X ;
      
      sr_cont : simrel_cont prog S G TC ;

      sr_e2a : simrel_e2a S G ;
      
      ex_cov_iss : e2a □₁ X ≡₁ C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘) ;
      
      ex_cov_iss_lab : eq_dom (X ∩₁ e2a ⋄₁ (C ∪₁ I)) Slab (Glab ∘ e2a) ;

      rmw_cov : Grmw ⨾ ⦗ C ⦘ ⊆ e2a □ Srmw ⨾ ⦗ X ⦘ ;
      rf_cov  : Grf ⨾ ⦗ C ⦘ ⊆ e2a □ ⦗ X ⦘ ⨾ Srf ⨾ ⦗ X ⦘ ;
      iss_co_iss  : ⦗ I ⦘ ⨾ Gco ⨾ ⦗ I ⦘ ⊆ e2a □ ⦗ X ⦘ ⨾ Sco ⨾ ⦗ X ⦘ ;

      jfe_ex_iss : dom_rel Sjfe ⊆₁ dom_rel (Sew ⨾ ⦗ X ∩₁ e2a ⋄₁ I ⦘) ;
      ew_ex_iss  : dom_rel (Sew \ eq) ⊆₁ dom_rel (Sew ⨾ ⦗ X ∩₁ e2a ⋄₁ I ⦘) ;

      e2a_jfDR : e2a □ (Sjf ⨾ ⦗DR⦘) ⊆ Grf ;

      jf_in_sim_jf : Sjf ⊆ Ssim_jf ;

      (* rel_ew_ex_iss : dom_rel (Srelease ⨾ Sew ⨾ ⦗ X ∩₁ e2a ⋄₁ I ⦘) ⊆₁ X ; *)
    }.
  
  Section SimRelCommonProps. 
    
    Variable SRC : simrel_common.

    Lemma ex_Tid t : 
      e2a □₁ (X ∩₁ STid t) ≡₁ (e2a □₁ X) ∩₁ GTid t.
    Proof. 
      unfolder. split. 
      { ins; desf. 
        split; eauto.
        symmetry. apply e2a_tid. }
      ins; desf.
      eexists; splits; eauto.
      apply e2a_tid.
    Qed.

    Lemma ex_NTid t : 
      e2a □₁ (X ∩₁ SNTid t) ≡₁ (e2a □₁ X) ∩₁ GNTid t.
    Proof. 
      unfolder. split. 
      { intros x [y [[Xy NTIDy] EQx]].
        splits; eauto.
        intros TIDx. apply NTIDy.
        subst. apply e2a_tid. }
      intros x [[y [Xy EQx]] NTIDx].
      eexists; splits; eauto.
      intros TIDy. apply NTIDx.
      subst. symmetry. apply e2a_tid.
    Qed.

    Lemma ex_iss_inW : 
      X ∩₁ e2a ⋄₁ I ⊆₁ SW.
    Proof.
      unfolder.
      intros x [xX xI].
      unfold is_w.
      erewrite ex_cov_iss_lab; auto.
      { unfold compose.
        eapply issuedW; eauto.
        apply SRC. }
      basic_solver.
    Qed.

    Lemma rfe_ex_iss :
      dom_rel Srfe ⊆₁ dom_rel (Sew ⨾ ⦗X ∩₁ e2a ⋄₁ I⦘).
    Proof.
      assert (ES.Wf S) as WFS.
      { apply SRC. }
      unfold ES.rfe, ES.rf, ES.jfe.
      intros x [y [[[z [EW JF]] CC] NSB]].
      assert (~ Ssb z y) as AA.
      { intros SB. apply CC.
        apply ES.cf_sb_in_cf; auto.
        eexists. split; eauto.
        edestruct ES.ewc; eauto.
        apply ES.ewD in EW; auto.
        apply ES.jfD in JF; auto.
        red. ins. type_solver. }
      edestruct SRC.(jfe_ex_iss) as [v HH].
      { eexists. split; eauto. }
      destruct_seq_r HH as BB.
      eexists. apply seq_eqv_r. split; [|by eauto].
      generalize WFS.(ES.ew_trans) EW HH. basic_solver.
    Qed.
    
    Lemma e2a_ew_iss : 
      e2a □ (Sew \ eq) ⊆ ⦗ I ⦘. 
    Proof.
      intros x y HH.
      assert (x = y) as EQxy; subst.
      { eapply e2a_ew; [apply SRC|]. generalize HH. basic_solver 10. }
      split; auto.
      destruct HH as [a [b [EW [EQx EQy]]]]; subst.
      edestruct ew_ex_iss as [x HH]; eauto.
      { eexists; eauto. }
      destruct_seq_r HH as FI.
      red in FI. destruct FI as [y IY]; subst.
      unfolder in IY.
      arewrite (e2a a = e2a x); auto.
      eapply e2a_ew; [apply SRC|].
      eexists; eauto.
    Qed.

    Lemma e2a_jfrmw : e2a □ (Sjf ⨾ Srmw) ⊆ Grf ⨾ Grmw.
    Proof.
      assert (ES.Wf S) as WF.
      { apply SRC. }
      arewrite (Sjf ⨾ Srmw ⊆ Sjf ⨾ ⦗dom_rel (Srmw)⦘ ⨾ Srmw)
        by basic_solver 10.
      rewrite (dom_r WF.(ES.jfD)) at 1.
      rewrite !seqA.
      arewrite (⦗SR⦘ ⨾ ⦗dom_rel (Srmw)⦘ ⊆ ⦗DR⦘).
      { unfold SimRelJF.DR. basic_solver 10. }
      rewrite <- seqA.
      rewrite collect_rel_seqi.
      rewrite e2a_rmw, e2a_jfDR; try by apply SRC.
      done.
    Qed.

    Lemma e2a_rs : e2a □ Srs ⊆ Grs. 
    Proof. 
      assert (ES.Wf S) as WF by apply SRC.
      assert (simrel_e2a S G) as SRE2A by apply SRC.
      rewrite rs_alt; auto.
      rewrite !collect_rel_seqi.
      rewrite !set_collect_eqv.
      rewrite !e2a_W; eauto.
      repeat apply seq_mori; eauto with hahn.
      2: { rewrite collect_rel_crt.
           eauto using clos_refl_trans_mori, e2a_jfrmw. }
      rewrite ES.sbE; auto.
      rewrite wf_sbE.
      rewrite <- !restr_relE.
      rewrite <- restr_inter_absorb_r.
      rewrite <- restr_inter_absorb_r with (r':=same_loc Slab).
      rewrite collect_rel_cr.
      rewrite collect_rel_interi. 
      apply clos_refl_mori, inter_rel_mori. 
      2: by apply e2a_same_loc.
      rewrite !restr_relE, <- wf_sbE, <- ES.sbE; auto.
      eapply e2a_sb; eauto; apply SRC.
    Qed.

    Lemma e2a_release : e2a □ Srelease ⊆ Grelease.
    Proof. 
      rewrite release_alt; auto.
      rewrite !collect_rel_seqi, !collect_rel_cr, !collect_rel_seqi.
      rewrite !set_collect_eqv.
      arewrite (SE ∩₁ (SF ∪₁ SW) ⊆₁ SE) by basic_solver.
      rewrite e2a_Rel, e2a_rs, e2a_sb, e2a_F.
      { unfold imm_s_hb.release. basic_solver 10. }
      all: eauto; apply SRC.
    Qed.

    Lemma e2a_jfacq : e2a □ Sjf ⨾ (Ssb ⨾ ⦗SF⦘)^? ⨾ ⦗SAcq⦘ ⊆
                      Grf ⨾ (Gsb ⨾ ⦗GF⦘)^? ⨾ ⦗GAcq⦘.
    Proof.
      assert (ES.Wf S) as WF by apply SRC.
      assert (simrel_e2a S G) as SRE2A by apply SRC.
      inv SRE2A.
      arewrite (Ssb ⨾ ⦗SF⦘ ⊆ Ssb ⨾ ⦗SE∩₁SF⦘).
      { rewrite (dom_r WF.(ES.sbE)) at 1. basic_solver 10. }
      arewrite (Sjf ⨾ (Ssb ⨾ ⦗SE ∩₁ SF⦘)^? ⨾ ⦗SAcq⦘ ⊆
                Sjf ⨾ (Ssb ⨾ ⦗SE ∩₁ SF⦘)^? ⨾ ⦗SE∩₁SAcq⦘).
      { rewrite (dom_r WF.(ES.jfE)) at 1. basic_solver 10. }
      arewrite (Sjf ⨾ (Ssb ⨾ ⦗SE ∩₁ SF⦘)^? ⨾ ⦗SE ∩₁ SAcq⦘ ⊆
                Sjf ⨾ ⦗DR⦘ ⨾ (Ssb ⨾ ⦗SE ∩₁ SF⦘)^? ⨾ ⦗SE ∩₁ SAcq⦘).
      2: { rewrite <- !seqA.
           do 2 rewrite collect_rel_seqi.
           rewrite e2a_jfDR; auto.
           rewrite !collect_rel_cr, !collect_rel_seqi, !set_collect_eqv.
           rewrite e2a_sb; eauto; try apply SRC.
           rewrite e2a_F, e2a_Acq; eauto; try apply SRC.
           arewrite (GE ∩₁ GF ⊆₁ GF) by basic_solver.
           arewrite (GE ∩₁ GAcq ⊆₁ GAcq) by basic_solver. }
      rewrite crE. rewrite !seq_union_l, !seq_union_r, !seq_id_l.
      apply union_mori.
      { rewrite (dom_r WF.(ES.jfD)) at 1.
        rewrite !seqA.
        arewrite (⦗SR⦘ ⨾ ⦗SE ∩₁ SAcq⦘ ⊆ ⦗SR ∩₁ SE ∩₁ SAcq⦘ ⨾ ⦗SE ∩₁ SAcq⦘)
          by basic_solver.
        arewrite (SR ∩₁ SE ∩₁ SAcq ⊆₁ DR).
        2: done.
        unfold SimRelJF.DR.
        basic_solver 10. }
      rewrite (dom_r WF.(ES.jfD)) at 1.
      rewrite !seqA.
      arewrite (Ssb ⨾ ⦗SE ∩₁ SF⦘ ⊆ ⦗X ∩₁ e2a ⋄₁ C⦘ ⨾ Ssb ⨾ ⦗SE ∩₁ SF⦘).
      2: { arewrite (⦗SR⦘ ⨾ ⦗X ∩₁ e2a ⋄₁ C⦘ ⊆ ⦗DR⦘).
           2: done.
           unfold SimRelJF.DR. basic_solver 10. }
    Admitted.

    Lemma e2a_hb : e2a □ Shb ⊆ Ghb.
    Proof. 
      assert (e2a □₁ SE ⊆₁ GE) as EE by apply SRC.
      unfold hb, imm_s_hb.hb.
      rewrite collect_rel_ct.
      apply clos_trans_mori.
      rewrite collect_rel_union.
      apply union_mori.
      { eapply e2a_sb; eauto; apply SRC. }
      unfold Consistency.sw.
      rewrite collect_rel_seqi.
      rewrite e2a_release. by rewrite e2a_jfacq.
    Qed.

    Lemma e2a_jf : e2a □ Sjf ⊆ Gvf.
    Proof.
      assert (ES.Wf S) as WF by apply SRC.
      assert (simrel_e2a S G) as SRE2A by apply SRC.
      rewrite jf_in_sim_jf; auto.
      arewrite (Ssim_jf ⊆ Ssim_vf).
      unfold sim_vf.
      rewrite (dom_l WF.(ES.ewE)).
      rewrite (dom_l WF.(ES.ewD)). rewrite !seqA.
      arewrite (⦗SE⦘ ⨾ ⦗SW⦘ ⊆ ⦗SE∩₁SW⦘) by basic_solver.
      rewrite furr_alt; auto; try apply SRC.
      rewrite !collect_rel_seqi, !collect_rel_cr, !set_collect_eqv.
      rewrite e2a_jfDR; auto.
      rewrite e2a_hb. rewrite e2a_W; eauto.
      arewrite (e2a □ (e2a ⋄ sc) ⊆ sc) by basic_solver.
      arewrite (GE ∩₁ GW ⊆₁ GW) by basic_solver.
      rewrite e2a_ew; eauto.
      arewrite (⦗GW⦘ ⨾ eq ⊆ ⦗GW⦘) by basic_solver.
    Qed.

    Lemma ew_in_eq_ew_ex_iss_ew : 
      Sew ⊆ eq ∪ Sew ⨾ ⦗X ∩₁ e2a ⋄₁ I⦘ ⨾ Sew.
    Proof. 
      assert (ES.Wf S) as WFS.
      { apply SRC. }
      rewrite <- seqA.
      intros x y EWxy.
      destruct (classic (x = y)) as [EQ | nEQ].
      { basic_solver. }
      right. edestruct ew_ex_iss as [z HH]; auto.
      { basic_solver. }
      eexists; splits; eauto.
      eapply ES.ew_trans; eauto.
      apply ES.ew_sym; auto.
      generalize HH. basic_solver.
    Qed.

    Lemma cov_rmw_cov : 
      ⦗C⦘ ⨾ Grmw ⨾ ⦗C⦘ ⊆ e2a □ ⦗X⦘ ⨾ Srmw ⨾ ⦗X⦘.
    Proof. 
      assert (Wf G) as WFG.
      { apply SRC. }
      assert (ES.Wf S) as WFS.
      { apply SRC. }
      assert (tc_coherent G sc TC) as TCCOH.
      { apply SRC. }
      assert (Execution.t S X) as EXEC.
      { apply SRC. }
      erewrite <- dom_rel_helper with (r := Grmw ⨾ ⦗C⦘),
               <- dom_rel_helper with (r := Srmw ⨾ ⦗X⦘).                                      
      { by apply rmw_cov. }
      { rewrite ES.rmwi; auto.
        rewrite immediate_in.
        by apply Execution.ex_sb_prcl. }
      rewrite wf_rmwi; auto.
      rewrite immediate_in.
      eapply dom_sb_covered; eauto. 
    Qed.

    Lemma iss_rf_cov : 
      ⦗I⦘ ⨾ Grf ⨾ ⦗C⦘ ⊆ e2a □ ⦗X⦘ ⨾ Srf ⨾ ⦗X⦘.
    Proof. 
      assert (Wf G) as WFG.
      { apply SRC. }
      assert (ES.Wf S) as WFS.
      { apply SRC. }
      assert (tc_coherent G sc TC) as TCCOH.
      { apply SRC. }
      assert (Execution.t S X) as EXEC.
      { apply SRC. }
      erewrite <- dom_rel_helper with (r := Grf ⨾ ⦗C⦘).
      { by apply rf_cov. }
      eapply dom_rf_covered; eauto.
    Qed.

    Lemma sb_e2a_cov :
      dom_rel (Ssb ⨾ ⦗ e2a ⋄₁ C ⦘) ⊆₁ e2a ⋄₁ C.
    Proof.
      unfold set_map.
      rewrite seq_eqv_r.
      intros x [y [SB Cy]].
      eapply dom_sb_covered; [apply SRC|].
      unfolder; do 2 eexists; splits; eauto.
      eapply e2a_sb; try apply SRC.
      basic_solver 10.
    Qed.

    Lemma sb_ex_cov :
      dom_rel (Ssb ⨾ ⦗ X ∩₁ e2a ⋄₁ C ⦘) ⊆₁ X ∩₁ e2a ⋄₁ C.
    Proof.
      rewrite seq_eqv_r.
      intros x [y [SB [Xy Cy]]].
      split.
      { eapply Execution.ex_sb_prcl; [apply SRC|]. basic_solver 10. }
      eapply sb_e2a_cov. basic_solver 10.
    Qed.

    Lemma rel_ew_e2a_iss_cov :
      dom_rel (Srelease ⨾ Sew ⨾ ⦗ e2a ⋄₁ I ⦘) ⊆₁ e2a ⋄₁ C.
    Proof. 
      unfold set_map.
      rewrite seq_eqv_r.
      intros x [z [y [REL [EW Iz]]]].
      eapply dom_release_issued; try apply SRC.
      unfolder; do 2 eexists; splits; eauto.
      arewrite (e2a z = e2a y).
      { symmetry. eapply e2a_ew; [apply SRC|]. basic_solver 10. }
      eapply e2a_release; try apply SRC.
      basic_solver 10.
    Qed.

    Lemma rel_ew_ex_iss_cov :
      dom_rel (Srelease ⨾ Sew ⨾ ⦗ X ∩₁ e2a ⋄₁ I ⦘) ⊆₁ X ∩₁ e2a ⋄₁ C.
    Proof. 
      apply set_subset_inter_r. 
      split; [admit|].
      arewrite (X ∩₁ e2a ⋄₁ I ⊆₁ e2a ⋄₁ I).
      { basic_solver. }
      apply rel_ew_e2a_iss_cov.
    Admitted.

    Lemma rel_in_ex_cov_rel_sb : 
      Srelease ⊆ ⦗ X ∩₁ e2a ⋄₁ C ⦘ ⨾ Srelease ∪ Ssb^?. 
    Proof.
      assert (ES.Wf S) as WFS.
      { apply SRC. }
      arewrite (Srelease ⊆ ⦗X ∩₁ e2a ⋄₁ C ∪₁ set_compl (X ∩₁ e2a ⋄₁ C)⦘ ⨾ Srelease).
      { rewrite set_compl_union_id. by rewrite seq_id_l. }
      rewrite id_union, seq_union_l. 
      apply union_mori; [done|].
      unfold release at 1, rs. 
      rewrite <- !seqA.
      intros x y [z [HH JFRMW]].
      apply clos_rt_rtn1 in JFRMW.
      induction JFRMW as [|y w [u [JF RMW]]].
      { generalize WFS.(ES.sb_trans) HH. basic_solver 10. }
      apply ES.jfi_union_jfe in JF. destruct JF as [JF|JF].
      { apply WFS.(ES.rmwi) in RMW. red in JF. 
        generalize WFS.(ES.sb_trans) IHJFRMW JF RMW. basic_solver 10. }
      exfalso.
      assert (~ (X ∩₁ e2a ⋄₁ C) x) as CC.
      { generalize HH. basic_solver 10. }
      apply CC. eapply rel_ew_ex_iss_cov; eauto.
      assert (dom_rel (Sew ⨾ ⦗ X ∩₁ e2a ⋄₁ I ⦘) y) as [yy DD].
      { eapply jfe_ex_iss; auto. eexists. eauto. }
      eexists. eexists. split; eauto.
      unfold release, rs. apply clos_rtn1_rt in JFRMW.
      generalize HH JFRMW. basic_solver 40.
    Qed.

    Lemma sw_in_ex_cov_sw_sb : 
      Ssw ⊆ ⦗ X ∩₁ e2a ⋄₁ C ⦘ ⨾ Ssw ∪ Ssb. 
    Proof.
      assert (ES.Wf S) as WFS.
      { apply SRC. }
      arewrite (Ssw ⊆ ⦗X ∩₁ e2a ⋄₁ C ∪₁ set_compl (X ∩₁ e2a ⋄₁ C)⦘ ⨾ Ssw).
      { rewrite set_compl_union_id. by rewrite seq_id_l. }
      rewrite id_union, seq_union_l. 
      apply union_mori; [done|].
      unfold sw.
      arewrite (⦗set_compl (X ∩₁ e2a ⋄₁ C)⦘ ⨾ Srelease ⨾ Sjf ⊆ Ssb).
      2: { generalize WFS.(ES.sb_trans). basic_solver. }
      rewrite ES.jfi_union_jfe. 
      rewrite !seq_union_r. unionL.
      { rewrite <- seqA.
        erewrite eqv_l_set_compl_eqv_l.
        2 : apply rel_in_ex_cov_rel_sb.
        unfold ES.jfi.
        generalize WFS.(ES.sb_trans). basic_solver. }
      intros x y HH.
      destruct_seq_l HH as DX. 
      exfalso. apply DX.
      destruct HH as [z [REL RFE]].
      eapply rel_ew_ex_iss_cov; eauto.
      assert (dom_rel (Sew ⨾ ⦗X ∩₁ e2a ⋄₁ I⦘) z) as [zz DD].
      { apply jfe_ex_iss; auto. eexists. eauto. }
      eexists. eexists. eauto.
    Qed.

    Lemma hb_in_ex_cov_hb_sb :
      Shb ⊆ ⦗ X ∩₁ e2a ⋄₁ C ⦘ ⨾ Shb ∪ Ssb.
    Proof.
      assert (ES.Wf S) as WFS.
      { apply SRC. }
      arewrite (Shb ⊆ ⦗X ∩₁ e2a ⋄₁ C ∪₁ set_compl (X ∩₁ e2a ⋄₁ C)⦘ ⨾ Shb).
      { rewrite set_compl_union_id. by rewrite seq_id_l. }
      rewrite id_union, seq_union_l. 
      apply union_mori; [done|].
      intros x y HH. 
      destruct_seq_l HH as DX.
      red in HH. apply clos_trans_tn1 in HH.
      induction HH as [y [|HH]|y z [HH|HH]]; auto.
      { eapply eqv_l_set_compl_eqv_l.
        { apply sw_in_ex_cov_sw_sb. }
        basic_solver. }
      all: eapply ES.sb_trans; eauto.
      eapply eqv_l_set_compl_eqv_l.
      { apply sw_in_ex_cov_sw_sb. }
      apply seq_eqv_l.
      split; auto.
      red. intros CC. apply DX.
      eapply sb_ex_cov. 
      basic_solver 10.
    Qed.

  End SimRelCommonProps.

End SimRel.

Section SimRelLemmas.

  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable X : actid -> eventid.

  Notation "'SE'" := S.(ES.acts_set).
  Notation "'SEinit'" := S.(ES.acts_init_set).
  Notation "'SEninit'" := S.(ES.acts_ninit_set).
  Notation "'Stid'" := (S.(ES.tid)).
  Notation "'Slab'" := (S.(ES.lab)).
  Notation "'Sloc'" := (loc S.(ES.lab)).
  Notation "'K'" := S.(ES.cont_set).

  Notation "'STid' t" := (fun x => Stid x = t) (at level 1).

  Notation "'SR'" := (fun a => is_true (is_r Slab a)).
  Notation "'SW'" := (fun a => is_true (is_w Slab a)).
  Notation "'SF'" := (fun a => is_true (is_f Slab a)).
  Notation "'SRel'" := (fun a => is_true (is_rel Slab a)).

  Notation "'Ssb'" := (S.(ES.sb)).
  Notation "'Scf'" := (S.(ES.cf)).
  Notation "'Srmw'" := (S.(ES.rmw)).
  Notation "'Sjf'" := (S.(ES.jf)).
  Notation "'Sjfi'" := (S.(ES.jfi)).
  Notation "'Sjfe'" := (S.(ES.jfe)).
  Notation "'Srf'" := (S.(ES.rf)).
  Notation "'Srfi'" := (S.(ES.rfi)).
  Notation "'Srfe'" := (S.(ES.rfe)).
  Notation "'Sco'" := (S.(ES.co)).
  Notation "'Sew'" := (S.(ES.ew)).

  Notation "'Srs'" := (S.(Consistency.rs)).
  Notation "'Srelease'" := (S.(Consistency.release)).
  Notation "'Ssw'" := (S.(Consistency.sw)).
  Notation "'Shb'" := (S.(Consistency.hb)).

  Notation "'thread_syntax' tid"  := 
    (Language.syntax (thread_lts tid)) (at level 10, only parsing).  

  Notation "'thread_st' tid" := 
    (Language.state (thread_lts tid)) (at level 10, only parsing).

  Notation "'thread_init_st' tid" := 
    (Language.init (thread_lts tid)) (at level 10, only parsing).
  
  Notation "'thread_cont_st' tid" :=
    (fun st => existT _ (thread_lts tid) st) (at level 10, only parsing).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).

  Notation "'Gtid'" := (tid).
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gloc'" := (loc G.(lab)).
  
  Notation "'GTid' t" := (fun x => tid x = t) (at level 1).
  Notation "'GNTid' t" := (fun x => tid x <> t) (at level 1).

  Notation "'GR'" := (fun a => is_true (is_r Glab a)).
  Notation "'GW'" := (fun a => is_true (is_w Glab a)).
  Notation "'GF'" := (fun a => is_true (is_f Glab a)).

  Notation "'GRel'" := (fun a => is_true (is_rel Glab a)).
  
  Notation "'Gsb'" := (G.(sb)).
  Notation "'Grmw'" := G.(rmw).
  Notation "'Grf'" := (G.(rf)).
  Notation "'Gco'" := (G.(co)).

  Notation "'Grs'" := (G.(imm_s_hb.rs)).
  Notation "'Grelease'" := (G.(imm_s_hb.release)).
  Notation "'Ghb'" := (G.(imm_s_hb.hb)).

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Notation "'Gvf'" := (furr G sc).

  Lemma simrel_init 
        (nInitProg : ~ IdentMap.In tid_init prog)
        (PExec : program_execution prog G)
        (WF : Execution.Wf G)
        (CONS : imm_consistent G sc) : 
    let Sinit := ES.init prog in
    simrel_common prog Sinit G sc (init_trav G) (ES.acts_set Sinit).
  Proof. clear S TC X. admit. Admitted.

End SimRelLemmas.
