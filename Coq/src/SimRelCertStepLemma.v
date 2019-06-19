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
Require Import SimRelAddJF.
Require Import SimRelAddEW.
Require Import SimRelAddCO.
Require Import SimRelCertStep.
Require Import ProgES.
Require Import SimRelCertStepCoh.

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
    erewrite basic_step_cont_sb_dom; eauto.
    unionR left -> left.
    erewrite basic_step_cont_thread_k; eauto.
    erewrite simrel_cert_basic_step_ex_tid; eauto.
    erewrite basic_step_e2a_set_map_inter_old
      with (S := S); eauto.
    { apply SRCC. }
    erewrite Execution.ex_inE 
      with (X := X); eauto.
    basic_solver. 
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
    erewrite basic_step_cont_sb_dom; eauto.
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
    erewrite basic_step_cont_sb_dom; eauto.
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
    erewrite basic_step_cont_sb_dom; eauto.
    rewrite !id_union. rewrite !seq_union_r, !collect_rel_union.
    erewrite basic_step_cont_thread_k; eauto.
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

    erewrite basic_step_cont_sb_dom; eauto.
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
      { eapply contwf; eauto. }
      assert ((ProgToExecution.step (ktid S k))＊ st st') as STEPS.
      { apply inclusion_t_rt. eapply ilbl_step_in_steps. apply STEP. }
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
      exists (ThreadEvent (ES.cont_thread S k) xindex).
      eapply steps_dont_add_rmw; eauto.
      
      assert (eindex st < eindex st') as LTST.
      { eapply ilbl_step_eindex_lt. apply STEP. }
      assert (eindex st' <= eindex st'') as LTST'.
      { eapply eindex_steps_mon; eauto. }

      assert (acts_set (ProgToExecution.G st')
                       (ThreadEvent (ktid S k) xindex))
        as XINDST'.
      { red. apply acts_clos; auto. omega. }
      apply seq_eqv_l. split; auto.

      eapply dcertRMW. 
      { apply SRCC. }
      apply seq_eqv_lr. splits; auto.
      all: apply acts_clos; auto.
      all: omega. }
    
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

  Lemma simrel_cert_forwarding lbl lbl' k k' e e' S
        (st st' st'': thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')         
        (ILBL_STEP : ilbl_step (ktid S k) (opt_to_list lbl' ++ [lbl]) st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    simrel_cert prog S G sc TC TC' X k' st' st''.
  Proof. 
    assert (Wf G) as WFG by apply SRCC.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (simrel_e2a S G sc) as SRE2A.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC.
    { apply SRCC. } 
    assert (simrel_cont (stable_prog_to_prog prog) S G TC X) 
      as SRCONT.
    { apply SRCC. } 

    set (HH := FRWD).
    unfold forwarding in HH. desc.
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
    { erewrite cont_adjacent_sb_dom; eauto.
      rewrite !set_collect_union.
      rewrite !set_inter_union_r.
      rewrite !id_union.
      rewrite !seq_union_r, !collect_rel_union.
      repeat apply union_mori.
      { apply SRCC. }
      { rewrite !seq_eqv_r.
        intros x y [RMW [Cy [y' [EQy' E2Ae]]]].
        subst y y'. exfalso. 
        erewrite forwarding_e2a_e in Cy, RMW; eauto.
        assert (exists xindex,
                   ⟪ ILT : xindex < eindex st ⟫ /\
                   x = ThreadEvent (ES.cont_thread S k) xindex).
        { destruct x; simpls.
          { apply WFG.(rmw_from_non_init) in RMW.
            destruct_seq_l RMW as AA. desf. }
          apply WFG.(rmw_in_sb) in RMW.
          destruct_seq RMW as [AA BB].
          red in RMW. desf. eauto. }
        desf.
        assert (eindex st < eindex st') as LTST.
        { eapply ilbl_step_eindex_lt. apply STEP. }
        assert (eindex st' <= eindex st'') as LTST'.
        { eapply eindex_steps_mon; eauto. 
          apply lbl_steps_in_steps; eauto. }
        eapply eindex_not_in_rmw
          with (thread := ktid S k) (st := st) (st' := st'); eauto.
        { eapply ktid_ninit; eauto. }
        { apply lbl_steps_in_steps; eauto.
          apply rt_step. red. eauto. }
        eexists. 
        eapply steps_dont_add_rmw; eauto.
        { apply lbl_steps_in_steps; eauto. }
        apply seq_eqv_l. split.
        { red. eapply acts_clos; [edone|].
          etransitivity.
          2 : eapply lbl_step_eindex_lt; red; eauto. 
          eapply ILT. }
        eapply dcertRMW; [eapply SRCC|]. 
        apply seq_eqv_lr; splits; auto.
        all: apply acts_clos; auto.
        all: try omega.
        all: eapply wf_cert_state; eauto. }
      unfold eq_opt.
      destruct e' as [e'|].
      2 : basic_solver. 
      rewrite !seq_eqv_r.
      intros x y [RMW [Cy [y' [EQy' E2Ae]]]].
      subst y y'. 
      exists e, e'. splits; auto.
      { eapply cont_adjacent_rmw; eauto. }
      eapply wf_rmw_invf; eauto.
      eapply e2a_rmw with (S := S); eauto.
      red. do 2 eexists.
      splits; eauto.
      eapply cont_adjacent_rmw; eauto. }
    admit.
  Admitted.
  
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
    edestruct lbl_step_lbls as [l [l' EQlbl]]; eauto.
    { eapply wf_cont_state; eauto. }
    
    assert (K S (k , existT _ _ st )) as Kk.
    { edestruct cstate_cont; [apply SRCC|]. desf. }

    destruct (classic 
      (exists k' e e' Kk', forwarding S l l' k k' e e' st st' Kk Kk')
    ) as [[k' [e [e' [Kk' FRWD]]]] | nFRWD].
    { exists k', S. splits; auto.

        

    edestruct simrel_cert_step as [k' HH]; eauto. desc.
    cdes CertSTEP.
    assert (Wf G) as WF by apply SRCC.
    assert (ES.Wf S) as WFS by apply SRCC.
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
    { eapply basic_step_cont_thread_k; eauto. }
    { apply r_step. red.
      do 2 eexists; splits; eauto.
      eapply simrel_cert_step_consistent; eauto. }
    constructor; auto.
    (* tr_step : isim_trav_step G sc (ktid S k') TC TC' *)
    { erewrite basic_step_cont_thread_k; eauto. apply SRCC. }
    (* cert : cert_graph G sc TC TC' (ktid S k') state'' *)
    { erewrite basic_step_cont_thread_k; eauto. apply SRCC. }
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
    { admit. }
    (* rmw_cov_in_kE : Grmw ⨾ ⦗C' ∩₁ e2a' □₁ kE'⦘ ⊆ e2a' □ Srmw' ⨾ ⦗ kE' ⦘ *)
    { eapply simrel_cert_step_rmw_cov_in_kE; eauto. }

    clear EQlbl.
    
    assert (C ⊆₁ C') as CINC.
    { eapply sim_trav_step_covered_le.
      eexists. apply SRCC. }

    assert (Ssb S' ≡ Ssb S ∪ sb_delta S k e e') as SB'.
    { cdes BSTEP_. apply SB'. }

    assert (e2a S ⋄₁ C' ∩₁ ES.cont_sb_dom S k ⊆₁ e2a S' ⋄₁ C' ∩₁ ES.cont_sb_dom S' k')
      as CSBDIN.
    { erewrite basic_step_cont_sb_dom with (S:=S) (S':=S'); eauto.
      unfolder. ins. desc. splits; auto.
      erewrite basic_step_e2a_eq_dom; eauto.
      eapply kE_inE; eauto. }

    assert (C' ∩₁ e2a S  □₁ ES.cont_sb_dom S  k  ⊆₁
            C' ∩₁ e2a S' □₁ ES.cont_sb_dom S' k') as CSBDINE.
    { erewrite basic_step_cont_sb_dom with (S:=S) (S':=S'); eauto.
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
        { eapply basic_step_cont_sb_dom; eauto. basic_solver. }
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
         rewrite basic_step_cont_sb_dom; eauto.
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
      { admit. }
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
      rewrite basic_step_cont_sb_dom; eauto.
      rewrite set_unionA. apply set_subset_union_l. by split. }
    
    assert (ES.cont_sb_dom S' k' e) as SBDE.
    { eapply basic_step_cont_sb_dom; eauto. basic_solver. }
    assert (eq_opt e' ⊆₁ ES.cont_sb_dom S' k') as SBDE'.
    { erewrite basic_step_cont_sb_dom; eauto. basic_solver. }

    assert (C' ∩₁ e2a S' □₁ ES.cont_sb_dom S' k' ≡₁
            e2a S' □₁ ES.cont_sb_dom S' k') as CALT.
    { split; [basic_solver|].
      apply set_subset_inter_r. split; [|done].
      erewrite basic_step_cont_sb_dom; eauto.
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
    { eapply contstable; eauto. apply SRCC. }

    assert (wf_thread_state (ES.cont_thread S k) st) as WTS.
    { eapply contwf; eauto. apply SRCC. }

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
         assert (lbl = lbls); desf.

         cdes BSTEP_.
         assert (lbl = opt_to_list lbl' ++ [lbl0]); subst.
         { eapply unique_lbl_ilbl_step; eauto. }
         
         assert (exists lbls0 lbls', lbls = opt_to_list lbls' ++ [lbls0]); desf.
         { clear -STEP''0.
           red in STEP''0.
           unfolder in STEP''0. desf.
           unfold opt_to_list.
           cdes STEP''0. cdes STEP. inv ISTEP0.
           1-4: by eexists; exists None; simpls.
           all: eexists; eexists (Some _); simpls. }

         assert (wf_thread_state (ES.cont_thread S k) st''') as WTS'''.
         { eapply wf_thread_state_lbl_step; eauto. }

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
         { admit. }

         assert (wf_thread_state (ES.cont_thread S k) st') as WTS'.
         { eapply wf_thread_state_lbl_step with (state0:=st); eauto. }

         assert (acts_set (ProgToExecution.G st')
                          (ThreadEvent (ES.cont_thread S k) (eindex st))) as EIST'.
         { eapply acts_clos; eauto. eapply lbl_step_eindex_lt; eauto. }

         assert ((ProgToExecution.step (ES.cont_thread S k))＊ st' st'') as STEPS'.
         { by eapply lbl_steps_in_steps; eauto. }

         assert (acts_set (ProgToExecution.G st'')
                          (ThreadEvent (ES.cont_thread S k) (eindex st))) as EIST''.
         { eapply steps_preserve_E; eauto. }

         assert (lbl0 = Glab (ThreadEvent (ES.cont_thread S k) (eindex st))); subst.
         { arewrite (lbl0 =
                     Execution.lab st'.(ProgToExecution.G)
                                   (ThreadEvent (ES.cont_thread S k) (eindex st))).
           { eapply ilbl_step_eindex_lbl; eauto. }
           erewrite <- steps_preserve_lab; simpls; eauto.
           erewrite <- cslab with (G:=G) (state:=st'').
           3: by apply C_in_D; eauto.
           2: by apply SRCC.
           unfold certLab, restr_fun; desf. }
         
         assert (lbl' = lbls'); desf.

         (* TODO: continue from here. *)
         admit. }

    (* cdes BSTEP_. *)
    (* assert (lbl = opt_to_list lbl' ++ [lbl0]); subst. *)
    (* { admit. } *)
    
    (* red. splits. *)
    (* { arewrite (eindex st' = *)
    (*             match e' with *)
    (*             | None => ES.seqn S' (ES.next_act S) *)
    (*             | Some e' => ES.seqn S' e' *)
    (*             end). *)
    (*   { erewrite ilbl_step_eindex_shift; eauto. *)
    (*     desf; simpls; desf. *)
    (*     all: admit. } *)
        
      (* ins. *)
      (* split. *)
      (* { unfolder. ins. desf. *)
      (*   match goal with *)
      (*   | H : ES.cont_sb_dom S' k' y |- _ => rename H into SBD *)
      (*   end. *)
      (*   eapply basic_step_cont_sb_dom in SBD; eauto. *)
      (*   unfolder in SBD. desf. *)
      (*   { erewrite ilbl_step_eindex_shift; eauto. *)
      (*     etransitivity. eapply SIMST. *)
      (*     2: destruct lbl; simpls; omega. *)
      (*     red. eexists. splits; eauto. *)
      (*     rewrite <- CTS. erewrite <- basic_step_e2a_eq_dom; eauto. *)
      (*     eapply kE_inE; eauto. } *)
      (*   { match goal with *)
      (*     | H : e2a S' y = _ |- _ => rename H into AA *)
      (*     end. *)
      (*     erewrite e2a_ninit in AA; eauto. *)
      (*     inv AA. *)

  Admitted.

End SimRelCertStepLemma.
