Require Import Program.Basics Omega.
From hahn Require Import Hahn.
From imm Require Import Events Execution
     Traversal TraversalConfig SimTraversal SimTraversalProperties
     Prog ProgToExecution ProgToExecutionProperties Receptiveness
     imm_common imm_s imm_s_hb SimulationRel
     CertExecution2
     SubExecution CombRelations.
Require Import AuxRel.
Require Import AuxDef.
Require Import EventStructure.
Require Import Consistency.
Require Import Execution.
Require Import BasicStep.
Require Import AddJF.
Require Import AddEW.
Require Import AddCO.
Require Import Step.
Require Import StepWf.
Require Import LblStep.
Require Import CertRf.
Require Import CertGraph.
Require Import EventToAction.
Require Import ImmProperties.
Require Import SimRelCont.
Require Import SimRelEventToAction.
Require Import SimRel.
Require Import SimRelCert.
Require Import SimRelCertBasicStep.
Require Import SimRelAddJF.
Require Import SimRelAddEW.
Require Import SimRelAddCO.
Require Import SimRelCertStep.
Require Import SimRelCertForwarding.
Require Import SimRelCertStepCoh.
Require Import ProgES.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelCertStepLemma.

  Variable prog : stable_prog_type.
  Variable G : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable TC' : trav_config.
  Variable X : eventid -> Prop.

  Notation "'SE' S" := S.(ES.acts_set) (at level 10).
  Notation "'SEinit' S" := S.(ES.acts_init_set) (at level 10).
  Notation "'SEninit' S" := S.(ES.acts_ninit_set) (at level 10).
  Notation "'Stid' S" := (S.(ES.tid)) (at level 10).
  Notation "'Slab' S" := S.(ES.lab) (at level 10).
  Notation "'Sloc' S" := (Events.loc S.(ES.lab)) (at level 10).

  Notation "'Ssb' S" := S.(ES.sb) (at level 10).
  Notation "'Srmw' S" := S.(ES.rmw) (at level 10).
  Notation "'Sew' S" := S.(ES.ew) (at level 10).
  Notation "'Sjf' S" := S.(ES.jf) (at level 10).
  Notation "'Srf' S" := S.(ES.rf) (at level 10).
  Notation "'Sco' S" := S.(ES.co) (at level 10).
  Notation "'Scf' S" := S.(ES.cf) (at level 10).
  Notation "'Sicf' S" := S.(ES.icf) (at level 10).

  Notation "'Sjfe' S" := S.(ES.jfe) (at level 10).
  Notation "'Srfe' S" := S.(ES.rfe) (at level 10).
  Notation "'Scoe' S" := S.(ES.coe) (at level 10).
  Notation "'Sjfi' S" := S.(ES.jfi) (at level 10).
  Notation "'Srfi' S" := S.(ES.rfi) (at level 10).
  Notation "'Scoi' S" := S.(ES.coi) (at level 10).

  Notation "'Scc' S" := S.(cc) (at level 10).
  Notation "'Ssw' S" := S.(sw) (at level 10).
  Notation "'Shb' S" := S.(hb) (at level 10).
  Notation "'Secf' S" := (S.(Consistency.ecf)) (at level 10).
  Notation "'Seco' S" := (Consistency.eco S Weakestmo) (at level 10).

  Notation "'SR' S" := (fun a => is_true (is_r S.(ES.lab) a)) (at level 10).
  Notation "'SW' S" := (fun a => is_true (is_w S.(ES.lab) a)) (at level 10).
  Notation "'SF' S" := (fun a => is_true (is_f S.(ES.lab) a)) (at level 10).

  Notation "'SPln' S" := (fun a => is_true (is_only_pln S.(ES.lab) a)) (at level 10).
  Notation "'SRlx' S" := (fun a => is_true (is_rlx S.(ES.lab) a)) (at level 10).
  Notation "'SRel' S" := (fun a => is_true (is_rel S.(ES.lab) a)) (at level 10).
  Notation "'SAcq' S" := (fun a => is_true (is_acq S.(ES.lab) a)) (at level 10).
  Notation "'SAcqrel' S" := (fun a => is_true (is_acqrel S.(ES.lab) a)) (at level 10).
  Notation "'SSc' S" := (fun a => is_true (is_sc S.(ES.lab) a)) (at level 10).

  Notation "'K' S" := (S.(ES.cont_set)) (at level 10).

  Notation "'Stid_' S" := (fun t x => Stid S x = t) (at level 1).
  Notation "'SNTid_' S" := (fun t x => Stid S x <> t) (at level 1).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).

  Notation "'Glab'" := (Execution.lab G).
  Notation "'Gloc'" := (Events.loc (lab G)).
  Notation "'Gtid'" := (Events.tid).

  Notation "'GTid' t" := (fun x => Gtid x = t) (at level 1).
  Notation "'GNTid' t" := (fun x => Gtid x <> t) (at level 1).

  Notation "'GR'" := (fun a => is_true (is_r Glab a)).
  Notation "'GW'" := (fun a => is_true (is_w Glab a)).
  Notation "'GF'" := (fun a => is_true (is_f Glab a)).

  Notation "'GRel'" := (fun a => is_true (is_rel Glab a)).
  Notation "'GAcq'" := (fun a => is_true (is_acq Glab a)).

  Notation "'Gsb'" := (Execution.sb G).
  Notation "'Grmw'" := (Execution.rmw G).
  Notation "'Grf'" := (Execution.rf G).
  Notation "'Gco'" := (Execution.co G).

  Notation "'Grs'" := (imm_s_hb.rs G).
  Notation "'Grelease'" := (imm_s_hb.release G).
  Notation "'Gsw'" := (imm_s_hb.sw G).
  Notation "'Ghb'" := (imm_s_hb.hb G).

  Notation "'Gfurr'" := (furr G sc).
  Notation "'Gvf' t" := (vf G sc TC' t) (at level 10, only parsing).

  Notation "'Geco'" := (Execution_eco.eco G).

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).
  Notation "'C''"  := (covered TC').
  Notation "'I''"  := (issued TC').
  
  Notation "'thread_syntax' t"  := 
    (Language.syntax (thread_lts t)) (at level 10, only parsing).  

  Notation "'thread_st' t" := 
    (Language.state (thread_lts t)) (at level 10, only parsing).

  Notation "'thread_init_st' t" := 
    (Language.init (thread_lts t)) (at level 10, only parsing).

  Notation "'thread_cont_st' t" :=
    (fun st => existT _ (thread_lts t) st) (at level 10, only parsing).

  Notation "'cont_lang'" :=
    (fun S k => thread_lts (ES.cont_thread S k)) (at level 10, only parsing).

  Notation "'kE' S" := (fun k => ES.cont_sb_dom S k) (at level 1, only parsing).
  Notation "'ktid' S" := (fun k => ES.cont_thread S k) (at level 1, only parsing).

  Notation "'certX' S" := (fun k => (X ∩₁ SNTid_ S (ktid S k)) ∪₁ (kE S k)) (at level 1, only parsing).

  Lemma simrel_cert_step_ex_ktid_cov k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'') 
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    X ∩₁ Stid_ S' (ktid S' k') ∩₁ e2a S' ⋄₁ C ⊆₁ kE S' k'. 
  Proof. 
    cdes CertSTEP.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    (* TODO: make a lemma `cont_sb_mon` *)
    erewrite basic_step_cont_sb_dom'; eauto.
    unionR left -> left.
    erewrite basic_step_cont_thread'; eauto.
    erewrite simrel_cert_basic_step_ex_tid; eauto.
    erewrite basic_step_e2a_set_map_inter_old
      with (S := S); eauto.
    { apply SRCC. }
    erewrite Execution.ex_inE 
      with (X := X); eauto.
    basic_solver. 
  Qed.
  
  Lemma simrel_cert_step_cov_in_ex k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'') 
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    e2a S' ⋄₁ C ∩₁ kE S' k' ⊆₁ X.
  Proof. 
    cdes CertSTEP.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S G TC X) as SRCONT.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    erewrite basic_step_cont_sb_dom'; eauto.
    rewrite set_unionA.
    rewrite set_inter_union_r.
    unionL.
    { rewrite set_interC.
      erewrite basic_step_e2a_set_map_inter_old
        with (S := S); eauto.
      { rewrite set_interC. apply SRCC. }
      eapply kE_inE; eauto. }
    rewrite set_inter_union_r. 
    unfolder. unionL.
    { intros x [Cx EQx]. subst x. exfalso. 
      erewrite basic_step_e2a_e in Cx; eauto.
      eapply thread_event_ge_ncov; eauto. }
    intros x [Cx EQx].
    destruct e' as [e'|]; [|done].
    subst x. exfalso. 
    erewrite basic_step_e2a_e' in Cx; eauto.
    eapply thread_event_ge_ncov.
    1,3: eauto.
    omega.
  Qed.

  Lemma simrel_cert_step_kE_lab k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    eq_dom (kE S' k' \₁ SEinit S') (Slab S') (Execution.lab (ProgToExecution.G st'') ∘ e2a S').
  Proof.
    cdes CertSTEP.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S G TC X) as SRCONT.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    erewrite basic_step_cont_sb_dom'; eauto.
    erewrite basic_step_acts_init_set; eauto.
    rewrite set_unionA.
    rewrite set_minus_union_l.
    eapply eq_dom_union. split.
    { unfolder. ins. desf. unfold Basics.compose.
      assert (SE S x) as EX.
      { eapply kE_inE; eauto. }
      erewrite basic_step_lab_eq_dom; eauto.
      erewrite basic_step_e2a_eq_dom with (S:=S); eauto.
      eapply kE_lab; eauto. by split. }
    unfolder. ins. desf.
    { eapply basic_step_e2a_lab_e with (S:=S); eauto; apply SRCC. }
    eapply basic_step_e2a_lab_e' with (S:=S); eauto; apply SRCC.
  Qed.

  Lemma simrel_cert_step_jf_in_cert_rf k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    e2a S' □ (Sjf S' ⨾ ⦗kE S' k'⦘) ⊆ cert_rf G sc TC' (ktid S' k').
  Proof. 
    cdes CertSTEP.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S G TC X) as SRCONT.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    erewrite basic_step_cont_sb_dom'; eauto.
    rewrite !id_union. rewrite !seq_union_r, !collect_rel_union.
    erewrite basic_step_cont_thread'; eauto.
    unionL.
    { erewrite <- jf_in_cert_rf; eauto.
      arewrite (⦗kE S k⦘ ⊆ ⦗SE S⦘ ⨾ ⦗kE S k⦘).
      { rewrite <- seq_eqvK at 1. by erewrite kE_inE at 1; eauto. }
      arewrite (Sjf S' ⨾ ⦗SE S⦘ ⊆ Sjf S).
      { eapply simrel_cert_step_jf_E; eauto. }
      eapply basic_step_e2a_collect_rel_eq_dom with (S' := S'); eauto.
      rewrite ES.jfE at 1; try apply SRCC. basic_solver. }
    { assert (Sjf S ⨾ ⦗eq e⦘ ⊆ ∅₂) as AA.
      { rewrite ES.jfE; try apply SRCC. unfold ES.acts_set.
        cdes BSTEP_. desf. unfolder. ins. omega. }
      red in CertSTEP_. desf; cdes CertSTEP_.
      1,3: rewrite JF'; rewrite AA; basic_solver.
      all: cdes AJF; rewrite JF';
        rewrite seq_union_l, collect_rel_union; unionL.
      1,3: rewrite AA; basic_solver.
      all: unfold jf_delta; unfolder; ins; desf. }
    arewrite (Sjf S' ⨾ ⦗eq_opt e'⦘ ⊆ ∅₂).
    2: basic_solver.
    assert (Sjf S ⨾ ⦗eq_opt e'⦘ ⊆ ∅₂) as AA.
    { cdes BSTEP_. step_solver. }
    cdes BSTEP_. desf.
    red in CertSTEP_. desf; cdes CertSTEP_.
    1,3: by rewrite JF'.
    all: cdes AJF; rewrite JF'; rewrite seq_union_l; unionL; auto.
    all: unfold jf_delta.
    { basic_solver. }
    desf. simpls. desf. unfolder. ins. desf. omega.
  Qed.

  Lemma simrel_cert_step_ex_cont_iss k k' e e' S S' 
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    X ∩₁ e2a S' ⋄₁ (acts_set st'.(ProgToExecution.G) ∩₁ I) ⊆₁ dom_rel (Sew S' ⨾ ⦗ kE S' k' ⦘).
  Proof. 
    cdes CertSTEP. cdes BSTEP_. 
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (tc_coherent G sc TC ) as TCCOH.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S G TC X) as SRCONT.
    { apply SRCC. }
    assert (cert_graph G sc TC TC' (ktid S k) st'').
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }

    edestruct ilbl_step_acts_set as [a [a' HH]].
    { eapply wf_cont_state; eauto. }
    { apply STEP. }
    destruct HH as [EQa [EQa' ACTS]].
    red in EQa, EQa', ACTS. 
    
    erewrite basic_step_e2a_set_map_inter_old; eauto.
    2 : apply EXEC.
    rewrite ACTS.
    rewrite basic_step_cont_sb_dom'; eauto.
    rewrite !set_inter_union_l, !set_map_union, !set_inter_union_r.
    rewrite !id_union, !seq_union_r, !dom_union.
    repeat apply set_union_Proper. 

    { rewrite ex_cont_iss; eauto.
      rewrite step_ew_mon; eauto.
      eapply simrel_cert_step_step_; eauto. }

    { intros x [Xx [EQx Ix]].
      assert (SW S' e) as Wx.
      { unfold is_w.
        erewrite basic_step_e2a_certlab_e; eauto.
        erewrite basic_step_e2a_e; eauto. 
        rewrite <- EQa, EQx. 
        erewrite cslab; eauto.
        { eapply issuedW; eauto. }
        red. do 4 left. right.
        eapply sim_trav_step_issued_le; eauto.
        eexists; apply SRCC. }
      unfold_cert_step_ CertSTEP_;
        try by (try cdes AJF; type_solver).
      eapply sim_add_ew_ex_issw; eauto.
      { basic_solver. }
      unfolder. 
      arewrite (e2a S' x = e2a S x).
      { eapply basic_step_e2a_eq_dom; eauto. 
        eapply Execution.ex_inE; eauto. }
      splits; auto.
      exists e; splits; eauto.
      erewrite basic_step_e2a_e; eauto.
      congruence. }

    intros x [Xx [EQx Ix]].
    unfold eq_opt in EQx.
    destruct a' as [a'|]; [|intuition].
    destruct lbl'; [|exfalso; congruence].
    destruct e' as [e'|].
    2 : by unfold opt_same_ctor in *.
    inversion EQa' as [EQa''].
    assert (SW S' e') as Wx.
    { unfold is_w.
      erewrite basic_step_e2a_certlab_e'; eauto.
      erewrite basic_step_e2a_e'; eauto. 
      rewrite Nat.add_1_l.
      rewrite <- EQa'', EQx. 
      erewrite cslab; eauto.
      { eapply issuedW; eauto. }
      red. do 4 left. right.
      eapply sim_trav_step_issued_le; eauto.
      eexists; apply SRCC. }
    unfold_cert_step_ CertSTEP_;
      try by (try cdes AJF; type_solver).
    eapply sim_add_ew_ex_issw; eauto.
    { basic_solver. }
    { basic_solver. }
    unfolder. 
    arewrite (e2a S' x = e2a S x).
    { eapply basic_step_e2a_eq_dom; eauto. 
      eapply Execution.ex_inE; eauto. }
    splits; auto.
    exists e'; splits; eauto.
    erewrite basic_step_e2a_e'; eauto.
    congruence.
  Qed.

  Lemma simrel_cert_step_kE_iss k k' e e' S S' 
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    kE S' k' ∩₁ e2a S' ⋄₁ I ⊆₁ dom_rel (Sew S' ⨾ ⦗ X ⦘).
  Proof. 
    cdes CertSTEP. cdes BSTEP_. 
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (tc_coherent G sc TC ) as TCCOH.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S G TC X) as SRCONT.
    { apply SRCC. }
    assert (cert_graph G sc TC TC' (ktid S k) st'').
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }

    erewrite basic_step_cont_sb_dom'; eauto.
    rewrite !set_inter_union_l.
    unionL.
    { erewrite basic_step_e2a_set_map_inter_old; eauto.
      2 : eapply ES.cont_sb_domE; eauto.
      rewrite kE_iss; eauto.
      rewrite step_ew_mon; eauto.
      eapply simrel_cert_step_step_; eauto. }
    { intros x [EQx Ix]. subst x.
      assert (SW S' e) as Wx.
      { unfold is_w.
        erewrite basic_step_e2a_certlab_e; eauto.
        erewrite cslab; eauto.
        { eapply issuedW; eauto. }
        red. do 4 left. right.
        eapply sim_trav_step_issued_le; eauto.
        eexists; apply SRCC. }
      unfold_cert_step_ CertSTEP_;
        try by (try cdes AJF; type_solver).
      eapply sim_add_ew_issw_ew_ex; eauto.
      all: basic_solver. }
    intros x [EQx Ix]. 
    unfold eq_opt in EQx.
    destruct e' as [e'|]; [|intuition].
    subst x.
    assert (SW S' e') as Wx.
    { unfold is_w.
      erewrite basic_step_e2a_certlab_e'; eauto.
      erewrite cslab; eauto.
      { eapply issuedW; eauto. }
      red. do 4 left. right.
      eapply sim_trav_step_issued_le; eauto.
      eexists; apply SRCC. }
    unfold_cert_step_ CertSTEP_;
      try by (try cdes AJF; type_solver).
    eapply sim_add_ew_issw_ew_ex; eauto.
    all: basic_solver.
  Qed.

  Lemma simrel_cert_step_e2a_co_kE_iss k k' e e' S S' 
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    e2a S' □ (Sco S' ⨾ ⦗kE S' k' ∩₁ e2a S' ⋄₁ I'⦘) ⊆ Gco.
  Proof. 
    cdes CertSTEP. cdes BSTEP_. 
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (tc_coherent G sc TC ) as TCCOH.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S G TC X) as SRCONT.
    { apply SRCC. }
    assert (cert_graph G sc TC TC' (ktid S k) st'') as CERTG.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }

    erewrite basic_step_cont_sb_dom'; eauto.
    rewrite !set_inter_union_l, !id_union, 
            !seq_union_r, !collect_rel_union.
    unionL.
    { unfold_cert_step_ CertSTEP_.
      3,4: eapply sim_add_co_e2a_co_kE_issw; eauto.
      3,4: basic_solver.
      all: rewrite CO'.
      all: rewrite basic_step_e2a_set_map_inter_old; eauto.
      2,4: eapply kE_inE; eauto.
      all: rewrite ES.coE; auto.
      all: arewrite 
        ((⦗SE S⦘ ⨾ Sco S ⨾ ⦗SE S⦘) ⨾ ⦗ES.cont_sb_dom S k ∩₁ e2a S ⋄₁ I'⦘ ≡
           restr_rel (SE S) (Sco S ⨾ ⦗ES.cont_sb_dom S k ∩₁ e2a S ⋄₁ I'⦘)).
      1,3: basic_solver 20. 
      all: rewrite collect_rel_restr_eq_dom.
      2,4: eapply basic_step_e2a_eq_dom; eauto.
      all: rewrite inclusion_restr; apply SRCC. }
    { assert (ES.Wf S') as WFS'.
      { eapply simrel_cert_step_wf; eauto. }
      unfold_cert_step_ CertSTEP_.
      3 : eapply sim_add_co_e2a_co_issw; eauto; basic_solver.
      1: arewrite (eq e ⊆₁ SF S') by basic_solver.
      2,3: arewrite (eq e ⊆₁ SR S') by (cdes AJF; basic_solver).
      all: rewrite ES.coD; auto; type_solver. }
    assert (ES.Wf S') as WFS'.
    { eapply simrel_cert_step_wf; eauto. }
    unfold_cert_step_ CertSTEP_.
    1-3: basic_solver.
    destruct e' as [e'|]; [|done].
    unfold eq_opt.
    eapply sim_add_co_e2a_co_issw; eauto; basic_solver.
  Qed.

  Lemma simrel_cert_step_rmw_cov_in_kE k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    Grmw ⨾ ⦗C' ∩₁ e2a S' □₁ kE S' k'⦘ ⊆ e2a S' □ Srmw S' ⨾ ⦗ kE S' k' ⦘.
  Proof. 
    cdes CertSTEP. cdes BSTEP_.
    assert (Wf G) as WFG by apply SRCC.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S G TC X) as SRCONT.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (simrel_e2a S' G sc) as SRE2A.
    { eapply simrel_cert_step_e2a; eauto. }

    erewrite basic_step_cont_sb_dom'; eauto.
    rewrite !set_collect_union.
    rewrite !set_inter_union_r.
    rewrite !id_union.
    rewrite !seq_union_r, !collect_rel_union.
    
    repeat apply union_mori.
    { erewrite basic_step_e2a_set_collect_eq_dom; eauto.
      2 : eapply kE_inE; eauto.
      (* TODO: make `rmw_mon` lemma *)
      assert (Srmw S ⊆ Srmw S') as AA.
      { rewrite RMW'. eauto with hahn. }
      rewrite <- AA.
      rewrite rmw_cov_in_kE; eauto.
      eapply basic_step_e2a_collect_rel_eq_dom with (S' := S'); eauto.
      rewrite WFS.(ES.rmwE) at 1. basic_solver. }
    
    { unfolder. 
      intros x y [RMW [Cy [y' [EQy' EQy]]]]. 
      subst y y'. exfalso. 
      erewrite basic_step_e2a_e with (S := S) in RMW; eauto.
      eapply simrel_cert_lbl_step_nrwm_eindex; eauto.
      { eexists. apply STEP. }
      basic_solver. } 
    
    rewrite RMW'; unfold rmw_delta.
    rewrite seq_union_l, collect_rel_union.
    unionR right.
    unfold eq_opt. unfolder. ins. desf.
    do 2 eexists. splits; eauto.
    eapply wf_rmw_invf; eauto.
    eapply e2a_rmw with (S := S'); eauto.
    red. do 2 eexists.
    splits; eauto.
    apply RMW'. right. red. 
    unfold eq_opt. basic_solver. 
  Qed.
  
  Lemma simrel_cert_lbl_step k S
        (st st' st'': thread_st (ktid S k))
        (NINIT : ktid S k <> tid_init)
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (LBL_STEP : lbl_step (ktid S k) st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    exists k' S',
      ⟪ kTID : ktid S' k' = ktid S k ⟫ /\
      ⟪ ESSTEP : (step Weakestmo)^? S S' ⟫ /\
      ⟪ SRCC' : simrel_cert prog S' G sc TC TC' X k' st' st'' ⟫.
  Proof.
    assert (Wf G) as WF by apply SRCC.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S G TC X) 
      as SRCONT.
    { apply SRCC. } 

    edestruct LBL_STEP as [lbl ILBL_STEP].
    edestruct ilbl_step_lbls as [l [l' EQlbl]]; eauto.
    { eapply wf_cont_state; eauto. }
    
    (* destruct (classic  *)
    (*   (exists k' st' e e', forwarding G sc TC' S l l' k k' e e' st st') *)
    (* ) as [[k' [st''' [e [e' FRWD]]]] | nFRWD]. *)
    (* { assert (st''' = st') as EQst. *)
    (*   { cdes FRWD. *)
    (*     eapply unique_ilbl_step; eauto. *)
    (*     by rewrite <- EQlbl. } *)
    (*   subst st'''. *)
    (*   assert (ktid S k = ktid S k') as kEQTID. *)
    (*   { by apply FRWD. } *)
    (*   exists k', S. splits; auto. *)
    (*   eapply simrel_cert_forwarding; eauto. } *)

    subst lbl.
    edestruct simrel_cert_step as [k' HH]; eauto. 
    desc. cdes CertSTEP.
    assert (ES.Wf S') as WFS'.
    { eapply simrel_cert_step_wf; eauto. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (simrel_e2a S' G sc) as SRE2A.
    { eapply simrel_cert_step_e2a; eauto. }
    assert (step_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (simrel prog S' G sc TC X) as SRC'.
    { red. splits.
      { eapply simrel_cert_step_simrel_; eauto. }
      eapply simrel_cert_step_consistent; eauto. }

    assert (~ Basic.IdentMap.In tid_init (stable_prog_to_prog prog)) as PTINN.
    { apply stable_prog_to_prog_no_init. apply SRCC. }
    assert (tc_coherent G sc TC ) as TCCOH.
    { apply SRCC. }
    assert (tc_coherent G sc TC') as TCCOH'.
    { eapply isim_trav_step_coherence; eauto. apply SRCC. }

    assert (ES.cont_thread S' k' = ES.cont_thread S k) as CTS.
    { cdes BSTEP_. desf. simpls.
      rewrite TID'. unfold upd_opt, opt_ext. desf.
      all: by rewrite upds. }

    assert (X ⊆₁ SE S) as XE.
    { eapply Execution.ex_inE. apply SRCC. }

    assert (X ⊆₁ X ∩₁ SE S) as XSE.
    { apply set_subset_inter_r. split; [done|].
      eapply Execution.ex_inE. apply SRCC. }

    assert (~ SE S (opt_ext e e')) as NSE.
    { cdes BSTEP_. desf. unfold opt_ext, ES.acts_set in *; simpls. 
      desf; omega. }

    (* assert (forall s (SES : s ⊆₁ SE S) s', *)
    (*            s ∩₁ e2a S' ⋄₁ s' ⊆₁ s ∩₁ e2a S ⋄₁ s') as SSE2A. *)
    (* { unfolder. ins. desf. splits; auto. *)
    (*   erewrite <- basic_step_e2a_eq_dom; eauto. } *)
    
    assert (e2a S' □₁ ES.cont_sb_dom S k ≡₁ 
            e2a S □₁ ES.cont_sb_dom S k) 
      as CONTDOMEQ.
    { eapply basic_step_e2a_set_collect_eq_dom; eauto.
      eapply kE_inE; eauto. }

    exists k', S'. splits.
    { eapply basic_step_cont_thread'; eauto. }
    { apply r_step. red.
      do 2 eexists; splits; eauto.
      eapply simrel_cert_step_consistent; eauto. }
    constructor; auto.
    (* tr_step : isim_trav_step G sc (ktid S k') TC TC' *)
    { erewrite basic_step_cont_thread'; eauto. apply SRCC. }
    (* cert : cert_graph G sc TC TC' (ktid S k') state'' *)
    { erewrite basic_step_cont_thread'; eauto. apply SRCC. }
    (* cstate : simrel_cstate *)
    { eapply simrel_cert_basic_step_cstate; eauto. } 
    (* ex_ktid_cov : X ∩₁ STid' ktid' ∩₁ e2a' ⋄₁ C ⊆₁ kE' *)
    { eapply simrel_cert_step_ex_ktid_cov; eauto. }
    (* cov_in_ex : e2a' ⋄₁ C ∩₁ kE' ⊆₁ X *)
    { eapply simrel_cert_step_cov_in_ex; eauto. }
    (* kE_lab : eq_dom (kE' \₁ SEinit') Slab' (certG.(lab) ∘ e2a') *)
    { eapply simrel_cert_step_kE_lab; eauto. } 
    (* jf_in_cert_rf : e2a' □ (Sjf ⨾ ⦗kE'⦘) ⊆ cert_rf G sc TC' ktid' *)
    { eapply simrel_cert_step_jf_in_cert_rf; eauto. }
    (* ex_cont_iss : X ∩₁ e2a' ⋄₁ (contE' ∩₁ I) ⊆₁ dom_rel (Sew' ⨾ ⦗ kE' ⦘) ; *)
    { eapply simrel_cert_step_ex_cont_iss; eauto. }
    (* kE_iss : kE' ∩₁ e2a' ⋄₁ I ⊆₁ dom_rel (Sew' ⨾ ⦗ X ⦘) ; *)
    { eapply simrel_cert_step_kE_iss; eauto. }
    (* e2a_co_kE_iss : e2a □ (Sco ⨾ ⦗kE' ∩₁ e2a ⋄₁ I'⦘) ⊆ Gco ;  *)
    { eapply simrel_cert_step_e2a_co_kE_iss; eauto. }
    (* rmw_cov_in_kE : Grmw ⨾ ⦗C' ∩₁ e2a' □₁ kE'⦘ ⊆ e2a' □ Srmw' ⨾ ⦗ kE' ⦘ *)
    { eapply simrel_cert_step_rmw_cov_in_kE; eauto. }

    assert (C ⊆₁ C') as CINC.
    { eapply sim_trav_step_covered_le.
      eexists. apply SRCC. }

    assert (Ssb S' ≡ Ssb S ∪ sb_delta S k e e') as SB'.
    { cdes BSTEP_. apply SB'. }

    assert (e2a S ⋄₁ C' ∩₁ ES.cont_sb_dom S k ⊆₁ e2a S' ⋄₁ C' ∩₁ ES.cont_sb_dom S' k')
      as CSBDIN.
    { erewrite basic_step_cont_sb_dom' with (S:=S) (S':=S'); eauto.
      unfolder. ins. desc. splits; auto.
      erewrite basic_step_e2a_eq_dom; eauto.
      eapply kE_inE; eauto. }

    assert (C' ∩₁ e2a S  □₁ ES.cont_sb_dom S  k  ⊆₁
            C' ∩₁ e2a S' □₁ ES.cont_sb_dom S' k') as CSBDINE.
    { erewrite basic_step_cont_sb_dom' with (S:=S) (S':=S'); eauto.
      rewrite <- CONTDOMEQ. basic_solver 10. }

    ins.
    destruct (classic (e2a S' ⋄₁ C' ∩₁ ES.cont_sb_dom S' k' ⊆₁
                       e2a S  ⋄₁ C' ∩₁ ES.cont_sb_dom S  k)) as [INC|NINC].
    { assert (e2a S' ⋄₁ C' ∩₁ ES.cont_sb_dom S' k' ≡₁
              e2a S  ⋄₁ C' ∩₁ ES.cont_sb_dom S  k) as CEQ by (by split).
      assert (C' ∩₁ e2a S' □₁ ES.cont_sb_dom S' k' ≡₁
              C' ∩₁ e2a S  □₁ ES.cont_sb_dom S  k ) as CEQE.
      { split; auto.
        unfolder. ins. desf. splits; eauto.
        specialize (INC y). unfolder in INC.
        destruct INC as [AA BB].
        { by split. }
        eexists. splits; eauto. symmetry.
        eapply basic_step_e2a_eq_dom; eauto. 
        eapply kE_inE; eauto. }
      edestruct contsimstate_kE as [kC]; try apply SRCC. desf.
      assert (ES.cont_thread S' kC = ES.cont_thread S kC) as KT.
      { erewrite basic_step_cont_thread; eauto. }
      exists kC. exists state. splits.
      { rewrite CTS. by rewrite KT. }
      { eapply basic_step_cont_set; eauto. left. by rewrite KT. }
      { rewrite CEQ. rewrite basic_step_cont_sb_dom_eq; eauto. }
      { intros AA. exfalso.
        eapply basic_step_acts_set_ne; eauto.
        eapply kE_inE; eauto.
        assert (ES.cont_sb_dom S' k' e) as BB.
        { eapply basic_step_cont_sb_dom'; eauto. basic_solver. }
        apply INC. split; auto. }
      eapply sim_state_set_eq; eauto.
      red. by rewrite KT. }
    assert (C' (e2a S' e) -> eq_opt e' ⊆₁ e2a S' ⋄₁ C') as EEC.
    { unfolder. ins. desf.
      eapply sim_trav_step_rmw_covered with (r:=e2a S' e); eauto.
      { red. eexists. apply SRCC. }
      { apply SRCC. }
      eapply e2a_rmw; eauto.
      do 2 eexists. splits; eauto.
      cdes BSTEP_. apply RMW'. unfold rmw_delta, eq_opt. basic_solver. }
    destruct (classic (C' (e2a S' e))) as [EE|NEE].
    2: { exfalso. apply NINC.
         rewrite basic_step_cont_sb_dom'; eauto.
         rewrite set_unionA.
         rewrite set_inter_union_r.
         unionL.
         { unfolder. ins. desf. splits; auto.
           erewrite <- basic_step_e2a_eq_dom with (S':=S'); eauto.
           eapply kE_inE; eauto. }
         unfolder. ins. desf.
         exfalso. apply NEE.
         unfolder. ins. desf.
         eapply sim_trav_step_rmw_covered with (w:=e2a S' x); eauto.
         { red. eexists. apply SRCC. }
         { apply SRCC. }
         eapply e2a_rmw; eauto.
         do 2 eexists. splits; eauto.
         cdes BSTEP_. apply RMW'. unfold rmw_delta, eq_opt. basic_solver. }
    assert (eq e ∪₁ eq_opt e' ⊆₁ e2a S' ⋄₁ C') as EECE.
    { unfolder. ins. desf. apply EEC; auto. by red. }
    assert (ES.cont_sb_dom S k ⊆₁ e2a S' ⋄₁ C') as CSBECE.
    { unfolder. ins.
      eapply dom_sb_covered; eauto.
      exists (e2a S' e). apply seq_eqv_r. split; auto.
      eapply e2a_sb; eauto; try apply SRCC.
      { apply SRE2A. }
      unfolder. do 2 eexists. splits; eauto. 
      apply SB'. right. unfold sb_delta.
      basic_solver. }
    assert (ES.cont_sb_dom S k ⊆₁ e2a S ⋄₁ C') as CSBEC.
    { arewrite (ES.cont_sb_dom S k ⊆₁ SE S ∩₁ ES.cont_sb_dom S k).
      { apply set_subset_inter_r. split; [|done].
        eapply kE_inE; eauto. }
      sin_rewrite CSBECE.
      unfolder. ins. desf. erewrite <- basic_step_e2a_eq_dom; eauto. }

    edestruct contsimstate_kE as [kC]; try apply SRCC. desf.
    assert (kC = k) by (by apply KINEQ); subst.
    assert (state = st); subst.
    { cdes BSTEP_.
      pose proof (ES.unique_K WFS _ _ CONT INK eq_refl) as HH.
      simpls. inv HH. }

    exists k'. eexists.
    splits; eauto.
    { eapply basic_step_cont_set; eauto. right.
      cdes BSTEP_. desf. simpls. by rewrite CTS. }
    { split; [|basic_solver].
      apply set_subset_inter_r. split; [|done].
      rewrite basic_step_cont_sb_dom'; eauto.
      rewrite set_unionA. apply set_subset_union_l. by split. }
    
    assert (ES.cont_sb_dom S' k' e) as SBDE.
    { eapply basic_step_cont_sb_dom'; eauto. basic_solver. }
    assert (eq_opt e' ⊆₁ ES.cont_sb_dom S' k') as SBDE'.
    { erewrite basic_step_cont_sb_dom'; eauto. basic_solver. }

    assert (C' ∩₁ e2a S' □₁ ES.cont_sb_dom S' k' ≡₁
            e2a S' □₁ ES.cont_sb_dom S' k') as CALT.
    { split; [basic_solver|].
      apply set_subset_inter_r. split; [|done].
      erewrite basic_step_cont_sb_dom'; eauto.
      rewrite set_unionA, set_collect_union.
      apply set_subset_union_l. split.
      2: { unfold eq_opt in *. unfolder. ins. desf; splits; eauto.
           apply EECE. basic_solver. }
      unfolder. ins. desf. splits; auto.
        by apply CSBECE. }
    assert (e2a S □₁ ES.cont_sb_dom S k ⊆₁ C') as ECSBC.
    { unfolder. ins. desf. by eapply CSBEC. }

    eapply sim_state_set_eq; eauto.
    eapply sim_state_set_eq with (s:=e2a S □₁ ES.cont_sb_dom S k) in SIMST.
    2: { split; [|basic_solver]. apply set_subset_inter_r. by split. }

    assert (SEninit S' e) as NENS.
    { by eapply basic_step_acts_ninit_set_e; eauto. }

    assert (stable_state st) as STBLST.
    { eapply contstable; eauto. }

    assert (wf_thread_state (ES.cont_thread S k) st) as WTS.
    { eapply wf_cont_state; eauto. }

    assert (wf_thread_state (ES.cont_thread S k) st') as WTS'.
    { eapply wf_thread_state_lbl_step; eauto. }

    assert (wf_thread_state (ES.cont_thread S k) st'') as WTS''.
    { eapply wf_thread_state_lbl_steps; eauto. }

    cdes SIMST.
    red. splits.
    2: { exists state'. red. splits.
         3: rewrite CTS.
         2,3: by apply SIMST1.
         cdes SIMST1.
         assert ((lbl_step (ES.cont_thread S k))＊ st state') as LBLSTEPS.
         { eapply steps_stable_lbl_steps. apply seq_eqv_lr. splits; auto.
           apply terminal_stable. by apply TERMINAL. }
         apply lbl_steps_in_steps.
         apply rtE in LBLSTEPS. destruct LBLSTEPS as [AA|LBLSTEPS].
         { exfalso. red in AA. desf.
           eapply no_lbl_step_from_terminal.
           apply seq_eqv_l. split; eauto. }
         apply ct_begin in LBLSTEPS.
         destruct LBLSTEPS as [st''' [STEP'' LBLSTEPS]].
         assert (st''' = st'); subst.
         2: by rewrite CTS.
         cdes STEP''.
         eapply unique_ilbl_step; eauto.
         assert 
           (lbls = opt_to_list (option_map (Slab S') e') ++ [(Slab S') e]);
         desf.

         assert (exists lbls0 lbls', lbls = opt_to_list lbls' ++ [lbls0]); desf.
         { clear -STEP''0.
           red in STEP''0.
           unfolder in STEP''0. desf.
           unfold opt_to_list.
           cdes STEP''0. cdes STEP. inv ISTEP0.
           1-4: by eexists; exists None; simpls.
           all: eexists; eexists (Some _); simpls. }

         assert (wf_thread_state (ES.cont_thread S k) st''') as WTS'''.
         { eapply wf_thread_state_lbl_step with (state0:=st); eauto. }

         assert (acts_set (ProgToExecution.G st''')
                          (ThreadEvent (ES.cont_thread S k) (eindex st))) as EIST'''.
         { eapply acts_clos; eauto. eapply lbl_step_eindex_lt; eauto. }

         assert ((ProgToExecution.step (ES.cont_thread S k))＊ st''' state') as STEPS'''.
         { by eapply lbl_steps_in_steps; eauto. }
         
         assert (lbls0 = Glab (ThreadEvent (ES.cont_thread S k) (eindex st))); subst.
         { arewrite (lbls0 =
                     Execution.lab st'''.(ProgToExecution.G)
                                   (ThreadEvent (ES.cont_thread S k) (eindex st))).
           { eapply ilbl_step_eindex_lbl; eauto. }
           erewrite <- steps_preserve_lab; simpls; eauto.
           eapply TEH. eapply steps_preserve_E; eauto. }
         
         assert (C' (ThreadEvent (ES.cont_thread S k) (eindex st))) as EIC'.
         { apply CALT. red. exists e.
           split; auto.
           eapply basic_step_e2a_e; eauto. }

         assert (acts_set (ProgToExecution.G st')
                          (ThreadEvent (ES.cont_thread S k) (eindex st))) as EIST'.
         { eapply acts_clos; eauto. eapply lbl_step_eindex_lt; eauto. }

         assert ((ProgToExecution.step (ES.cont_thread S k))＊ st' st'') as STEPS'.
         { by eapply lbl_steps_in_steps; eauto. }

         assert (acts_set (ProgToExecution.G st'')
                          (ThreadEvent (ES.cont_thread S k) (eindex st))) as EIST''.
         { eapply steps_preserve_E.
           2: by eauto.
           all: eauto. }

         arewrite (Slab S' e = Glab (ThreadEvent (ES.cont_thread S k) (eindex st))).
         { arewrite (Slab S' e =
                     Execution.lab st'.(ProgToExecution.G)
                                   (ThreadEvent (ES.cont_thread S k) (eindex st))).
           { eapply ilbl_step_eindex_lbl; eauto. }
           erewrite <- steps_preserve_lab; simpls; eauto.
           erewrite <- cslab with (G:=G) (state:=st'').
           3: by apply C_in_D; eauto.
           2: by apply SRCC.
           unfold certLab, restr_fun; desf. }
         
         assert (lbls' = option_map (Slab S') e'); desf.
         destruct (classic (Grmw (ThreadEvent (ES.cont_thread S k)
                                              (eindex st))
                                 (ThreadEvent (ES.cont_thread S k)
                                              (1 + eindex st)))) as [RMW|NRMW].
         2: { assert (~ Execution.rmw (ProgToExecution.G st')
                        (ThreadEvent (ES.cont_thread S k) (eindex st))
                        (ThreadEvent (ES.cont_thread S k) (1 + eindex st))) as NRMW'.
              { intros AA. apply NRMW.
                assert (Execution.rmw
                          (ProgToExecution.G st'')
                          (ThreadEvent (ES.cont_thread S k) (eindex st))
                          (ThreadEvent (ES.cont_thread S k) (1 + eindex st))) as BB.
                { eapply steps_preserve_rmw; eauto. }
                eapply dcertRMW in BB.
                2: by apply SRCC.
                unfolder in BB. desf. }

              assert (~ Execution.rmw (ProgToExecution.G st''')
                        (ThreadEvent (ES.cont_thread S k) (eindex st))
                        (ThreadEvent (ES.cont_thread S k) (1 + eindex st))) as NRMW'''.
              { intros AA. apply NRMW.
                assert (Execution.rmw
                          (ProgToExecution.G state')
                          (ThreadEvent (ES.cont_thread S k) (eindex st))
                          (ThreadEvent (ES.cont_thread S k) (1 + eindex st))) as BB.
                { eapply steps_preserve_rmw; eauto. }
                eapply tr_rmw in BB; eauto.
                unfolder in BB. desf. }
              
              assert (lbls' = None); subst.
              { eapply ilbl_step_nrmw_None with (st:=st); eauto. }

              symmetry.
              eapply ilbl_step_nrmw_None with (st:=st); eauto. }

         assert (Execution.rmw
                   (ProgToExecution.G st'')
                   (ThreadEvent (ES.cont_thread S k) (eindex st))
                   (ThreadEvent (ES.cont_thread S k) (1 + eindex st))) as RMW''.
         { eapply dcertRMW.
           { apply SRCC. }
           apply seq_eqv_l. splits; auto. }

         assert (acts_set (ProgToExecution.G st'')
                          (ThreadEvent (ES.cont_thread S k) (1 + eindex st))) as AEIST''.
         { eapply wft_rmwE in RMW''; eauto. by destruct_seq RMW'' as [AA BB]. }

         assert (Execution.rmw
                   (ProgToExecution.G st')
                   (ThreadEvent (ES.cont_thread S k) (eindex st))
                   (ThreadEvent (ES.cont_thread S k) (1 + eindex st))) as ARMW'.
         { eapply steps_dont_add_rmw; eauto.
           apply seq_eqv_l. split; auto. }

         assert (acts_set (ProgToExecution.G st')
                          (ThreadEvent (ES.cont_thread S k) (1 + eindex st))) as AEIST'.
         { eapply wft_rmwE in ARMW'; eauto. unfolder in ARMW'. desf. }

         assert (C' (ThreadEvent (ES.cont_thread S k) (1 + eindex st))) as EIC''.
         { eapply sim_trav_step_rmw_covered with (G:=G)
               (r:= ThreadEvent (ES.cont_thread S k) (eindex st)); eauto.
           { red. eexists. apply SRCC. }
           apply SRCC. }

         assert (Execution.rmw
                   (ProgToExecution.G state')
                   (ThreadEvent (ES.cont_thread S k) (eindex st))
                   (ThreadEvent (ES.cont_thread S k) (1 + eindex st))) as RMWST'.
         { eapply tr_rmw; eauto. apply seq_eqv_lr; auto. }

         assert (wf_thread_state (ES.cont_thread S k) state') as WTST'.
         { eapply wf_thread_state_lbl_steps; eauto. }

         assert (acts_set (ProgToExecution.G state')
                          (ThreadEvent (ES.cont_thread S k) (1 + eindex st))) as WEST'.
         { eapply wft_rmwE in RMWST'; eauto. unfolder in RMWST'. desf. }

         assert (Execution.rmw
                   (ProgToExecution.G st''')
                   (ThreadEvent (ES.cont_thread S k) (eindex st))
                   (ThreadEvent (ES.cont_thread S k) (1 + eindex st))) as RMW'''.
         { eapply steps_dont_add_rmw; eauto.
           apply seq_eqv_l. split; auto. }

         assert (acts_set (ProgToExecution.G st''')
                          (ThreadEvent (ES.cont_thread S k) (1 + eindex st))) as AEIST'''.
         { apply (dom_r WTS'''.(wft_rmwE)) in RMW'''.
           by destruct_seq_r RMW''' as AA. }
         
         destruct e' as [e'|].
         2: { eapply acts_rep in AEIST'; eauto. desf.
              apply ilbl_step_cases in ILBL_STEP; auto.
              desf; simpls; omega. }
         destruct lbls' as [lbls'|].
         2: { eapply acts_rep in AEIST'''; eauto. desf.
              apply ilbl_step_cases in STEP''0; auto.
              desf; simpls; omega. }
         simpls.
         assert (lbls' = Slab S' e').
         2: by subst.
         erewrite ilbl_step_eindex_lbl' with (st:=st) (st':=st''') (lbl':=lbls'); eauto.
         2: eby simpls.
         erewrite <- steps_preserve_lab with (state':=state'); eauto.
         erewrite tr_lab; eauto.

         arewrite (Slab S' e' =
                   Execution.lab (ProgToExecution.G st')
                                 (ThreadEvent (ES.cont_thread S k) (1 + eindex st))).
         { erewrite <- ilbl_step_eindex_lbl' with (st:=st); eauto.
           simpls. eauto. }
         erewrite <- steps_preserve_lab with (state':=st''); eauto.
         erewrite <- cslab; [|by apply SRCC|].
         { unfold certLab, restr_fun. desf. }
         eapply C_in_D. erewrite <- basic_step_e2a_e' with (e':=e'); eauto.
         apply EECE. basic_solver. }

    assert (ES.seqn S' e = eindex st) as SEQNE.
    { (* TODO: introduce a lemma *) admit. }
    assert (match e' with
            | None => True
            | Some e' => ES.seqn S' e' = 1 + eindex st
           end) as SEQNE'.
    { (* TODO: introduce a lemma *) admit. }

    assert (eindex st' =
            match e' with
            | None => 1 + eindex st
            | Some e' => 2 + eindex st
            end) as EINST.
    { apply ilbl_step_cases in ILBL_STEP; auto. desf. }
    rewrite EINST.
    
    rewrite CTS.
    split.
    { unfolder. intros [y [AA BB]].
      eapply basic_step_cont_sb_dom' with (S:=S) in AA; eauto.
      destruct AA as [[AA|AA]|AA].
      3: { red in AA. desf.
           erewrite basic_step_e2a_e' with (S0:=S) in BB; eauto.
           inv BB; desf; omega. }
      2: { subst; erewrite basic_step_e2a_e with (S:=S) in BB; eauto.
           inv BB; desf; omega. }
      etransitivity.
      { eapply PCOV. red. exists y. splits; auto. rewrite <- BB.
        symmetry. eapply basic_step_e2a_eq_dom; eauto.
        eapply ES.cont_sb_domE; eauto. }
      desf; omega. }
    intros AA.
    assert (index < eindex st \/ index = eindex st \/ index = 1 + eindex st) as [II|[II|II]].
    { desf; omega. }
    { apply PCOV in II. red in II. desc.
      exists y. split.
      { eapply basic_step_cont_sb_dom'; eauto. basic_solver. }
      rewrite <- II0.
      eapply basic_step_e2a_eq_dom; eauto.
      eapply ES.cont_sb_domE; eauto. }
    { exists e. splits; auto. rewrite II.
      eapply basic_step_e2a_e; eauto. }
    destruct e' as [e'|].
    2: omega.
    exists e'. splits.
    { apply SBDE'. by red. }
    rewrite II.
    eapply basic_step_e2a_e'; eauto.
  Admitted.

End SimRelCertStepLemma.
