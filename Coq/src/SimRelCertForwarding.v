Require Import Program.Basics Omega.
From hahn Require Import Hahn.
From imm Require Import Events Execution
     Traversal TraversalConfig SimTraversal SimTraversalProperties
     Prog ProgToExecution ProgToExecutionProperties Receptiveness
     imm_common imm_s imm_s_hb SimulationRel
     CertExecution2 CertExecutionMain
     SubExecution CombRelations AuxRel.
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
Require Import SimRelCertStep.
Require Import ProgES.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelCertForwarding.

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

  Definition forwarding S lbl lbl' k k' e e'
             (st st' : thread_st (ktid S k)) :=
    ⟪ LBL  : lbl  = Slab S e ⟫ /\
    ⟪ LBL' : lbl' = option_map (Slab S) e' ⟫ /\
    ⟪ Kk   : K S (k , existT _ _ st ) ⟫ /\
    ⟪ Kk'  : K S (k', existT _ _ st') ⟫ /\
    ⟪ ADJ  : ES.cont_adjacent S k k' e e'⟫ /\
    ⟪ STEP : ilbl_step (ktid S k) (opt_to_list lbl' ++ [lbl]) st st' ⟫ /\  
    ⟪ CertRF : e2a S □ Sjf S ⨾ ⦗eq e⦘ ⊆ cert_rf G sc TC' (ktid S k) ⟫.  

  Lemma forwarding_seqn_e S lbl lbl' k k' e e'
        (st st' st'': thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st') :
    ES.seqn S e = eindex st.
  Proof. 
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (simrel_cont (stable_prog_to_prog prog) S G TC X) 
      as SRCONT.
    { apply SRCC. }
    unfold forwarding in FRWD. desc.
    set (AA := ADJ).
    unfold ES.cont_adjacent in AA. desc.
    unfold ES.cont_sb_dom in kSBDOM.
    destruct k eqn:Heq.
    { erewrite continit; eauto.
      unfold ES.seqn.
      arewrite (dom_rel (Ssb S ∩ ES.same_tid S ⨾ ⦗eq e⦘) ≡₁ ∅).
      2 : by erewrite countNatP_empty.
      split; [|done].
      rewrite seq_eqv_r.
      intros x [y [[SB STID] EQy]].
      red. subst y.
      eapply ES.init_tid_K; eauto.
      exists (existT _ _ st), k.
      splits; [by subst k|]. 
      subst k. erewrite <- ES.cont_adjacent_tid_e; eauto.
      rewrite <- STID.
      assert (SEinit S x) as INITx.
      { apply kSBDOM. basic_solver 10. }
      red in INITx. unfolder in INITx. desf. }
    erewrite contseqn; eauto.
    erewrite ES.seqn_immsb; eauto.
    { red. 
      erewrite ES.cont_adjacent_tid_e 
        with (k := k) (e := e); eauto.
      2 : eby subst k.
      unfold ES.cont_thread. desf. }
    red. splits.
    { assert (dom_rel (Ssb S ⨾ ⦗eq e⦘) eid) as HH.
      { apply kSBDOM. basic_solver 10. }
      unfolder in HH. desf. } 
    intros x SB SB'.
    assert (dom_rel ((Ssb S)^? ⨾ ⦗eq eid⦘) x) as HH.
    { apply kSBDOM. basic_solver 10. }
    unfolder in HH. desf.
    { eapply ES.sb_irr; eauto. }
    eapply ES.sb_irr; eauto.
    eapply ES.sb_trans; eauto.
  Qed.
  
  Lemma forwarding_seqn_e' S lbl lbl' k k' e e'
        (st st' st'': thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (FRWD : forwarding S lbl lbl' k k' e (Some e') st st') :
    ES.seqn S e' = 1 + eindex st.
  Proof. 
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (simrel_cont (stable_prog_to_prog prog) S G TC X) 
      as SRCONT.
    { apply SRCC. }
    set (AA := FRWD).
    unfold forwarding in AA. desc.
    set (AA := ADJ).
    unfold ES.cont_adjacent in AA. desc.
    assert (immediate (ES.sb S) e e') as IMMSB.
    { apply ES.rmwi; auto.
      apply RMWe. basic_solver. }
    erewrite ES.seqn_immsb 
      with (x := e); eauto; try red; splits.
    { erewrite forwarding_seqn_e; eauto. }
    erewrite ES.cont_adjacent_tid_e; eauto. 
    erewrite ES.cont_adjacent_tid_e'
      with (k := k); eauto. 
  Qed.

  Lemma forwarding_e2a_e S lbl lbl' k k' e e'
        (st st' st'': thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st') :
    e2a S e = ThreadEvent (ES.cont_thread S k) (eindex st).
  Proof. 
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (ES.cont_adjacent S k k' e e') as ADJ.
    { apply FRWD. }
    rewrite e2a_ninit; auto.
    2 : eapply ES.cont_adjacent_ninit_e; eauto.
    erewrite ES.cont_adjacent_tid_e; eauto.
    erewrite forwarding_seqn_e; eauto.
  Qed.

  Lemma forwarding_e2a_e' S lbl lbl' k k' e e'
        (st st' st'': thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (FRWD : forwarding S lbl lbl' k k' e (Some e') st st') :
    e2a S e' = ThreadEvent (ES.cont_thread S k) (1 + eindex st).
  Proof. 
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (ES.cont_adjacent S k k' e (Some e')) as ADJ.
    { apply FRWD. }
    rewrite e2a_ninit; auto.
    2 : eapply ES.cont_adjacent_ninit_e'; eauto.
    erewrite ES.cont_adjacent_tid_e'; eauto.
    erewrite forwarding_seqn_e'; eauto.
  Qed.

  Lemma simrel_cert_forwarding_ex_ktid_cov lbl lbl' k k' e e' S 
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'') 
        (FRWD : forwarding S lbl lbl' k k' e e' st st')         
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    X ∩₁ Stid_ S (ktid S k') ∩₁ e2a S ⋄₁ C ⊆₁ kE S k'. 
  Proof. 
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    arewrite (ktid S k' = ktid S k).
    { symmetry. apply FRWD. }
    etransitivity; [apply SRCC|].
    eapply ES.cont_adjacent_sb_dom_mon; eauto.
    apply FRWD.
  Qed.

  Lemma simrel_cert_forwarding_cov_in_ex lbl lbl' k k' e e' S 
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'') 
        (FRWD : forwarding S lbl lbl' k k' e e' st st')         
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    e2a S ⋄₁ C ∩₁ kE S k' ⊆₁ X.
  Proof. 
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (ES.cont_adjacent S k k' e e') as ADJ.
    { apply FRWD. }
    rewrite ES.cont_adjacent_sb_dom 
      with (k' := k'); eauto.
    rewrite set_unionA.
    rewrite set_inter_union_r.
    unionL.
    { rewrite set_interC. 
      rewrite set_interC. 
      apply SRCC. }
    rewrite set_inter_union_r. 
    unfolder. unionL.
    { intros x [Cx EQx]. subst x. exfalso. 
      eapply e2a_ge_ncov; eauto.
      { apply FRWD. }
      { erewrite ES.cont_adjacent_tid_e; eauto. }
      erewrite forwarding_seqn_e; eauto. }
    intros x [Cx EQx].
    destruct e' as [e'|]; [|done].
    subst x. exfalso. 
    eapply e2a_ge_ncov; eauto.
    { eapply ES.cont_adjacent_ninit_e'; eauto. }
    { erewrite ES.cont_adjacent_tid_e'; eauto. }
    erewrite forwarding_seqn_e'; eauto. 
  Qed.

  Lemma simrel_cert_forwarding_kE_lab lbl lbl' k k' e e' S 
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'') 
        (FRWD : forwarding S lbl lbl' k k' e e' st st')         
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    eq_dom (kE S k' \₁ SEinit S) (Slab S) (Execution.lab (ProgToExecution.G st'') ∘ e2a S).
  Proof. 
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (simrel_cont (stable_prog_to_prog prog) S G TC X) 
      as SRCONT.
    { apply SRCC. } 
    assert (ES.cont_adjacent S k k' e e') as ADJ.
    { apply FRWD. }
    set (AA := FRWD).
    cdes AA.
    assert (ktid S k = ktid S k') as kEQTID.
    { by apply ADJ. }
    assert (wf_thread_state (ktid S k) st) as WFst.
    { eapply contwf; eauto. }
    assert (wf_thread_state (ktid S k) st') as WFst'.
    { rewrite kEQTID. eapply contwf; eauto. by rewrite <- kEQTID. }
    assert (Gtid (e2a S e) = ES.cont_thread S k) as GTIDe.
    { erewrite e2a_ninit; [|apply ADJ].
      unfold Events.tid.
      erewrite ES.cont_adjacent_tid_e; eauto. }
    rewrite ES.cont_adjacent_sb_dom 
      with (k' := k'); eauto.
    rewrite set_unionA.
    rewrite !set_minus_union_l.
    rewrite !eq_dom_union. splits.
    { apply SRCC. }
    { intros x [EQx _]. subst x.
      unfold compose.
      erewrite steps_preserve_lab; eauto.
      { rewrite <- LBL.
        erewrite forwarding_e2a_e; eauto.
        eapply ilbl_step_eindex_lbl; eauto. }
      { by rewrite GTIDe. }
      { apply lbl_steps_in_steps. 
          by rewrite GTIDe. }
      erewrite forwarding_e2a_e; eauto.
      eapply acts_clos; eauto.
      eapply ilbl_step_eindex_lt.
      apply STEP. }
    intros x [EQx _]. 
    unfold eq_opt in EQx. 
    destruct e' as [e'|]; [|done]. 
    assert (Gtid (e2a S e') = ES.cont_thread S k) as GTIDe'.
    { erewrite e2a_ninit.
      2 : eapply ES.cont_adjacent_ninit_e'; eauto.
      unfold Events.tid.
      erewrite ES.cont_adjacent_tid_e'; eauto. }
    subst x. unfold compose.
    erewrite steps_preserve_lab; eauto.
    { unfold option_map in LBL'.
      destruct lbl' as [lbl'|]; 
        inversion LBL' as [HLBL'].
      rewrite <- HLBL'.
      erewrite forwarding_e2a_e'; eauto.
      eapply ilbl_step_eindex_lbl'; eauto. }
    { by rewrite GTIDe'. }
    { apply lbl_steps_in_steps. 
        by rewrite GTIDe'. }
    erewrite forwarding_e2a_e'; eauto.
    eapply acts_clos; eauto.
    erewrite ilbl_step_eindex_shift
      with (st' := st'); eauto.
    unfold option_map in LBL'.
    destruct lbl' as [lbl'|].
    2 : inversion LBL'.
    unfold opt_to_list, app, length.
    omega. 
  Qed.

  Lemma simrel_cert_forwarding_jf_in_cert_rf lbl lbl' k k' e e' S 
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')         
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    e2a S □ (Sjf S ⨾ ⦗kE S k'⦘) ⊆ cert_rf G sc TC' (ktid S k').
  Proof.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (simrel_cont (stable_prog_to_prog prog) S G TC X) 
      as SRCONT.
    { apply SRCC. } 
    assert (ES.cont_adjacent S k k' e e') as ADJ.
    { apply FRWD. }
    arewrite (ktid S k' = ktid S k).
    { symmetry. apply ADJ. }
    erewrite ES.cont_adjacent_sb_dom; eauto.
    rewrite !id_union, !seq_union_r, !collect_rel_union.
    unionL; auto.
    { apply SRCC. }
    { apply FRWD. }
    unfold eq_opt.
    destruct e' as [e'|].
    2 : basic_solver.
    assert (ES.rmw S e e') as RMW.
    { eapply ES.cont_adjacent_rmw; eauto. }
    apply ES.rmwD in RMW; auto.
    rewrite ES.jfD; auto.
    generalize RMW. type_solver. 
  Qed.

  Lemma simrel_cert_forwarding_ex_cont_iss lbl lbl' k k' e e' S 
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')         
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    X ∩₁ e2a S ⋄₁ (acts_set st'.(ProgToExecution.G) ∩₁ I) ⊆₁ dom_rel (Sew S ⨾ ⦗ kE S k' ⦘).
  Proof. 
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC.
    { apply SRCC. }
    assert (simrel_cont (stable_prog_to_prog prog) S G TC X) 
      as SRCONT.
    { apply SRCC. }
    assert (ES.cont_adjacent S k k' e e') as ADJ.
    { apply FRWD. }
    erewrite ES.cont_adjacent_sb_dom; eauto.
    edestruct ilbl_step_acts_set as [a [a' HH]].
    { eapply wf_cont_state; eauto. }
    { eapply FRWD. }
    destruct HH as [EQa [EQa' ACTS]].
    red in EQa, EQa', ACTS. 
    rewrite ACTS.
    rewrite !set_inter_union_l, !set_map_union.
    rewrite !set_inter_union_r, !id_union, 
    !seq_union_r, !dom_union.
    apply set_union_Proper;
      [apply set_union_Proper|].
    { apply SRCC. }
    { intros x [Xx [EQx Ix]].
      assert (x = e) as EQe.
      { edestruct e2a_eq_in_cf
          with (x := x) (y := e) as [EQ | CF]; eauto.
        { eapply Execution.ex_inE; eauto. }
        { eapply ES.cont_adjacent_ninit_e; eauto. }
        { rewrite <- EQx.
          erewrite forwarding_e2a_e; eauto. }
        exfalso. 
        admit. }
      admit. }
    admit. 
  Admitted.

  Lemma simrel_cert_lbl_step_nrwm_eindex k S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (LBL_STEP : lbl_step (ktid S k) st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    ~ (codom_rel Grmw) (ThreadEvent (ktid S k) st.(eindex)).
  Proof. 
    assert (Wf G) as WFG by apply SRCC.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S G TC X) 
      as SRCONT.
    { apply SRCC. }
    
    intros [x RMW].
    assert (exists xindex,
               ⟪ ILT : xindex < eindex st ⟫ /\
               x = ThreadEvent (ES.cont_thread S k) xindex).
    { destruct x; simpls.
      { apply WFG.(rmw_from_non_init) in RMW.
        destruct_seq_l RMW as AA. desf. }
      apply WFG.(rmw_in_sb) in RMW.
      destruct_seq RMW as [AA BB].
      red in RMW. desf.
      eauto. }
    desf.

    assert (wf_thread_state (ktid S k) st) as WTS.
    { eapply wf_cont_state; eauto. }
    assert ((ProgToExecution.step (ktid S k))＊ st st') as STEPS.
    { destruct LBL_STEP.
      apply inclusion_t_rt. 
      eapply ilbl_step_in_steps; eauto. }
    assert (wf_thread_state (ktid S k) st') as WTS'.
    { eapply wf_thread_state_steps; eauto. }
    assert ((ProgToExecution.step (ES.cont_thread S k))＊ st' st'')
      as STEPS'.
    { apply lbl_steps_in_steps; eauto. }
    assert (wf_thread_state (ES.cont_thread S k) st'') as WTS''.
    { eapply wf_thread_state_steps; eauto. }

    eapply eindex_not_in_rmw 
      with (thread := ktid S k)
           (st := st) (st' := st'); eauto.
    { eapply ktid_ninit; eauto. }
    assert (eindex st < eindex st') as LTST.
    { edestruct LBL_STEP.
      eapply ilbl_step_eindex_lt; eauto. }
    assert (eindex st' <= eindex st'') as LTST'.
    { eapply eindex_steps_mon; eauto. }
    assert (acts_set (ProgToExecution.G st')
                     (ThreadEvent (ktid S k) xindex))
      as XINDST'.
    { red. apply acts_clos; auto. omega. }
    exists (ThreadEvent (ES.cont_thread S k) xindex).
    eapply steps_dont_add_rmw; eauto.
    apply seq_eqv_l. split; auto.
    eapply dcertRMW. 
    { apply SRCC. }
    apply seq_eqv_lr. splits; auto.
    all: apply acts_clos; auto.
    all: omega.
  Qed.

    Lemma simrel_cert_forwarding_rmw_cov_in_kE lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')         
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    Grmw ⨾ ⦗C' ∩₁ e2a S □₁ kE S k'⦘ ⊆ e2a S □ Srmw S ⨾ ⦗ kE S k' ⦘.
  Proof. 
    assert (Wf G) as WFG by apply SRCC.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC.
    { apply SRCC. }
    assert (simrel_cont (stable_prog_to_prog prog) S G TC X) 
      as SRCONT.
    { apply SRCC. }
    assert (simrel_e2a S G sc) as SRE2A.
    { apply SRCC. }
    assert (ES.cont_adjacent S k k' e e') as ADJ.
    { apply FRWD. }
    erewrite ES.cont_adjacent_sb_dom; eauto.
    rewrite !set_collect_union.
    rewrite !set_inter_union_r.
    rewrite !id_union.
    rewrite !seq_union_r, !collect_rel_union.
    repeat apply union_mori.
    { apply SRCC. }
    { rewrite !seq_eqv_r.
      intros x y [RMW [Cy [y' [EQy' E2Ae]]]].
      subst y y'. exfalso. 
      erewrite forwarding_e2a_e with (S := S) in RMW; eauto.
      eapply simrel_cert_lbl_step_nrwm_eindex; eauto.
      { eexists. apply FRWD. }
      basic_solver. }       
    unfold eq_opt.
    destruct e' as [e'|].
    2 : basic_solver. 
    rewrite !seq_eqv_r.
    intros x y [RMW [Cy [y' [EQy' E2Ae]]]].
    subst y y'. 
    exists e, e'. splits; auto.
    { eapply ES.cont_adjacent_rmw; eauto. }
    eapply wf_rmw_invf; eauto.
    eapply e2a_rmw with (S := S); eauto.
    red. do 2 eexists.
    splits; eauto.
    eapply ES.cont_adjacent_rmw; eauto. 
  Qed.

  Lemma simrel_cert_forwarding lbl lbl' k k' e e' S
        (st st' st'': thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')         
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    simrel_cert prog S G sc TC TC' X k' st' st''.
  Proof. 
    set (HH := FRWD).
    unfold forwarding in HH. desc.
    assert (ktid S k = ktid S k') as kEQTID.
    { by apply ADJ. }
    
    constructor; auto. 
    all: try (by try rewrite <- kEQTID; apply SRCC).
    (* cstate : simrel_cstate S k' st' st'' *)      
    { constructor. 
      { eapply cstate_stable, SRCC. }
      { red. exists st'. splits; eauto.
          by rewrite <- kEQTID. }
        by rewrite <- kEQTID. }
    (* ex_ktid_cov : X ∩₁ STid ktid' ∩₁ e2a ⋄₁ C ⊆₁ kE' *)
    { eapply simrel_cert_forwarding_ex_ktid_cov; eauto. }
    (* cov_in_ex : e2a ⋄₁ C ∩₁ kE' ⊆₁ X *)
    { eapply simrel_cert_forwarding_cov_in_ex; eauto. }
    (* kE_lab : eq_dom (kE' \₁ SEinit) Slab (certG.(lab) ∘ e2a) *)
    { eapply simrel_cert_forwarding_kE_lab; eauto. }
    (* jf_in_cert_rf : e2a □ (Sjf ⨾ ⦗kE'⦘) ⊆ cert_rf G sc TC' ktid' *)
    { eapply simrel_cert_forwarding_jf_in_cert_rf; eauto. }
    (* ex_cont_iss : X ∩₁ e2a ⋄₁ (contE' ∩₁ I) ⊆₁ dom_rel (Sew ⨾ ⦗ kE' ⦘) *)
    { eapply simrel_cert_forwarding_ex_cont_iss; eauto. }
    (* rmw_cov_in_kE : Grmw ⨾ ⦗C' ∩₁ e2a □₁ kE'⦘ ⊆ e2a □ Srmw ⨾ ⦗kE'⦘ *)
    { eapply simrel_cert_forwarding_rmw_cov_in_kE; eauto. }
    admit.
  Admitted.

  Lemma simrel_cert_nforwarding_icf_R lbl lbl' k k' e e' S S'
        (st st' st'': thread_st (ktid S k))
        (LBL  : lbl  = Slab S' e ) 
        (LBL' : lbl' = option_map (Slab S') e')
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (nFRWD : ~ exists k' e e', forwarding S lbl lbl' k k' e e' st st') :
    dom_rel (Sicf S') ⊆₁ SR S'.
  Proof.
    cdes CertSTEP. cdes BSTEP_.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (simrel_cont (stable_prog_to_prog prog) S G TC X) 
      as SRCONT.
    { apply SRCC. } 

    (* some technicalities *)
    assert (lbl0 = lbl) as EQl.
    { rewrite LBL, LAB'.
      rewrite updo_opt, upds; auto.
      unfold opt_ext in *.
      basic_solver. }
    assert (lbl'0 = lbl') as EQl'.
    { rewrite LBL', LAB'.
      unfold option_map, opt_same_ctor in *.
      destruct e' as [e'|].
      { destruct lbl'0; [|done].
        unfold upd_opt.
        by rewrite upds. }
      destruct lbl'0; done. }
    subst lbl0 lbl'0.

    erewrite basic_step_icf; eauto.
    rewrite dom_union. unionL.
    { arewrite (dom_rel (Sicf S) ⊆₁ SE S ∩₁ SR S).
      { apply set_subset_inter_r. split.
        { rewrite ES.icfE; auto. basic_solver. }
        eapply icf_R; apply SRCC. }
      (* TODO: introduce lemma *)
      intros x [Ex Rx].
      unfold is_r.
      erewrite basic_step_lab_eq_dom; eauto. }

    unfold icf_delta.
    destruct 
      (classic (is_r (Slab S') e))
      as [Re|nRe].
    { rewrite csE, dom_union. unionL.
      2 : basic_solver. 
      rewrite dom_cross.
      2 : { intros HH. eapply HH. edone. }
      intros x kICFx.
      assert ((Slab S □₁ ES.cont_icf_dom S k) (Slab S x)) 
        as HH.
      { basic_solver. }
      eapply basic_step_cont_icf_dom_same_lab_u2v 
        in HH; eauto.
      unfold is_r in *.
      arewrite (Slab S' x = Slab S x).
      { erewrite basic_step_lab_eq_dom; eauto.
        eapply ES.cont_icf_domE; eauto. }
      unfold same_label_u2v in HH.
      destruct (Slab S' e); try done.
      destruct (Slab S x); done. }
    
    intros x [y HH].
    exfalso. 
    apply nFRWD.
    edestruct cstate_cont
      as [s [EQs KK]]; [apply SRCC|].
    red in EQs, KK. subst s.
    assert (exists z, ES.cont_icf_dom S k z) 
      as [z kICFz].
    { generalize HH. basic_solver. }
    edestruct ES.cont_icf_dom_cont_adjacent 
      with (S := S) (k := k) (e := z)
      as [k''' [z' ADJ]]; eauto.
    exists k''', z, z'.
    edestruct simrel_cont_adjacent_inK'
      with (S := S) (k := k) (k' := k''')
      as [st''' KK''']; eauto.
    edestruct ES.K_adj 
      with (S := S) (k := k) (k' := k''') (st' := st''')
      as [ll [ll' [EQll [EQll' LSTEP]]]]; eauto.
    red in EQll, EQll', LSTEP.

    edestruct nR_ilbl_step 
      as [EQl [EQl' EQl'']].
    { apply STEP. }
    { apply LSTEP. }
    { unfold is_r, id in *. 
      by rewrite LBL. }
    red in EQl, EQl', EQl''.

    assert (st' = st''') as EQst.
    { eapply unique_nR_ilbl_step.
      { eapply STEP. }
      { eapply LSTEP. }
      unfold is_r, id in *. 
      by rewrite LBL. }
    subst st'''.

    constructor; splits; auto.
    1-2: congruence.
    arewrite (eq z ⊆₁ set_compl (is_r (Slab S))).
    2 : rewrite ES.jfD; auto; basic_solver.
    intros z'' EQz''. subst z''. 
    assert ((Slab S □₁ ES.cont_icf_dom S k) (Slab S z)) 
      as HA.
    { basic_solver. }
    eapply basic_step_cont_icf_dom_same_lab_u2v 
      in HA; eauto.
    intros Rz. apply nRe.
    unfold is_r in *.
    unfold same_label_u2v in HA.    
    destruct (Slab S z); try done.
    destruct (Slab S' e); done.
  Qed.

  (* TODO: move to more suitable place *)
  Lemma same_label_u2v_same_val lbl lbl'  
        (SAMEU2V : same_label_u2v lbl lbl')
        (SAMEVAL : val id lbl = val id lbl') : 
    lbl = lbl'.
  Proof. 
    unfold same_label_u2v, val, id in *.
    destruct lbl; destruct lbl'; desf.
  Qed.

  Lemma simrel_cert_nforwarding_icf_jf lbl lbl' k k' e e' S S'
        (st st' st'': thread_st (ktid S k))
        (LBL  : lbl  = Slab S' e ) 
        (LBL' : lbl' = option_map (Slab S') e')
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'')  
        (nFRWD : ~ exists k' e e', forwarding S lbl lbl' k k' e e' st st') :
    irreflexive (Sjf S' ⨾ Sicf S' ⨾ (Sjf S')⁻¹ ⨾ Sew S').
  Proof. 
    cdes CertSTEP. cdes BSTEP_.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (ES.Wf S') as WFS'.
    { eapply simrel_cert_step_wf; eauto. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (simrel_cont (stable_prog_to_prog prog) S G TC X) 
      as SRCONT.
    { apply SRCC. } 
    assert (simrel_e2a S G sc) as SRE2A.
    { apply SRCC. } 
    assert (step_ e e' S S') as STEP_.
    { eapply simrel_cert_step_step_; eauto. }


    (* some technicalities *)
    assert (lbl0 = lbl) as EQl.
    { rewrite LBL, LAB'.
      rewrite updo_opt, upds; auto.
      unfold opt_ext in *.
      basic_solver. }
    assert (lbl'0 = lbl') as EQl'.
    { rewrite LBL', LAB'.
      unfold option_map, opt_same_ctor in *.
      destruct e' as [e'|].
      { destruct lbl'0; [|done].
        unfold upd_opt.
          by rewrite upds. }
      destruct lbl'0; done. }
    subst lbl0 lbl'0.

    eapply step_icf_jf_irr; eauto. split. 
    { eapply icf_jf. apply SRCC. }

    rewrite !seq_eqv_r.
    intros x [[y [JF' EQy]] HH]. subst y.
    destruct HH as [z [y [EW [JF kICFy]]]].
    red.
    
    apply nFRWD.
    edestruct cstate_cont
      as [s [EQs KK]]; [apply SRCC|].
    red in EQs, KK. subst s.
    edestruct ES.cont_icf_dom_cont_adjacent 
      with (S := S) (k := k) (e := z)
      as [k''' [z' ADJ]]; eauto.
    edestruct simrel_cont_adjacent_inK'
      with (S := S) (k := k) (k' := k''')
      as [st''' KK''']; eauto.
    exists k''', z, z'.
    edestruct ES.K_adj 
      with (S := S) (k := k) (k' := k''') (st' := st''')
      as [ll [ll' [EQll [EQll' LSTEP]]]]; eauto.
    red in EQll, EQll', LSTEP.

    assert (lbl = ll) as EQLab.
    { eapply same_label_u2v_same_val.
      { eapply same_label_u2v_ilbl_step.
        { apply STEP. }
        apply LSTEP. }
      arewrite (val id lbl = val (Slab S') e).
      { basic_solver. }
      arewrite (val id ll = val (Slab S) z).
      { basic_solver. }
      arewrite (val (Slab S') e = val (Slab S') x).
      { erewrite <- ES.jfv; eauto. }
      arewrite (val (Slab S') x = val (Slab S) x).
      { unfold val. 
        erewrite basic_step_lab_eq_dom; eauto.
        apply ES.ewE in EW; auto.
        generalize EW. basic_solver. }
      erewrite ES.ewv. 
      2-3: eauto.
      erewrite ES.jfv; eauto. }

    assert (lbl' = ll') as EQLab'.
    { eapply same_label_fst_ilbl_step.
      { eapply STEP. }
      rewrite EQLab.
      eapply LSTEP. }

    assert (st' = st''') as EQst.
    { eapply unique_ilbl_step.
      { eapply STEP. }
      rewrite EQLab, EQLab'.
      apply LSTEP. }
    subst st'''.

    constructor; splits; auto.
    1-2: congruence.
    rewrite seq_eqv_r.
    intros a b [a' [b' [[JF'' EQb'] [EQa EQb]]]].
    subst a b b'.
    assert (a' = y) as EQa'.
    { eapply ES.jff with (S := S); eauto. }
    subst a'.
    arewrite (e2a S y = e2a S x).
    { erewrite e2a_ew; eauto. basic_solver 10. }
    arewrite (e2a S x = e2a S' x).
    { symmetry. eapply basic_step_e2a_eq_dom; eauto. 
      apply ES.ewE in EW; auto. 
      generalize EW. basic_solver. }
    arewrite (e2a S z = e2a S' e).
    { admit. }
    
    assert (is_r (Slab S') e) as Re.
    { apply ES.jfD in JF'; auto. 
      generalize JF'. basic_solver. }
    unfold_cert_step_ CertSTEP_.
    1,3: try cdes AEW; type_solver. 
    all: cdes AJF. 
    all: arewrite (x = w); auto. 
    all: apply JF'0 in JF'. 
    all: unfold jf_delta, singl_rel in JF'.
    all: destruct JF' as [JF'|JF'].
    2,4: basic_solver.
    all: exfalso; eapply basic_step_acts_set_ne; eauto.
    all: apply ES.jfE in JF'; auto.  
    all: generalize JF'; basic_solver.
  Admitted.

End SimRelCertForwarding.