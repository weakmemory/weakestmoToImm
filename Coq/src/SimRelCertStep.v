Require Import Omega.
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
Require Import ProgES.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelCertStep.

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
  Notation "'Gloc'" := (Events.loc (Execution.lab G)).
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

  Definition cert_fence_step
             (e  : eventid)
             (e' : option eventid)
             (S S' : ES.t) : Prop :=
    ⟪ ENONE : e' = None ⟫ /\
    ⟪ FF  : SF S' e ⟫ /\
    ⟪ JF' : Sjf S' ≡ Sjf S ⟫ /\
    ⟪ EW' : Sew S' ≡ Sew S ⟫ /\
    ⟪ CO' : Sco S' ≡ Sco S ⟫.

  Definition cert_load_step
             (k : cont_label)
             (e : eventid)
             (e' : option eventid)
             (S S' : ES.t) : Prop :=
    exists w, 
      ⟪ ENONE : e' = None ⟫ /\
      ⟪ AJF : sim_add_jf G sc TC' X k w e S S' ⟫ /\
      ⟪ EW' : Sew S' ≡ Sew S ⟫ /\
      ⟪ CO' : Sco S' ≡ Sco S ⟫.

  Definition cert_store_step
             (k : cont_label)
             (e  : eventid)
             (e' : option eventid)
             (S S' : ES.t) : Prop :=
    ⟪ ENONE : e' = None ⟫ /\
    ⟪ JF' : Sjf S' ≡ Sjf S ⟫ /\ 
    ⟪ AEW : sim_add_ew TC X e S S' ⟫ /\
    ⟪ ACO : sim_add_co G TC X k e S S' ⟫.

  Definition cert_update_step
             (k : cont_label)
             (e  : eventid)
             (e' : option eventid)
             (S S' : ES.t) : Prop := 
    exists w w',
      ⟪ SLOC : same_loc S' e w' ⟫ /\
      ⟪ ESOME : e' = Some w' ⟫ /\ 
      ⟪ AJF : sim_add_jf G sc TC' X k w e S S' ⟫ /\ 
      ⟪ AEW : sim_add_ew TC X w' S S' ⟫ /\
      ⟪ ACO : sim_add_co G TC X k w' S S' ⟫.

  Definition cert_step_ 
             (k : cont_label)
             (e  : eventid)
             (e' : option eventid)
             (S S' : ES.t) : Prop := 
    cert_fence_step e e' S S' \/ 
    cert_load_step  k e e' S S' \/ 
    cert_store_step k e e' S S' \/ 
    cert_update_step k e e' S S'. 

  Definition cert_step 
             (thread : thread_id)
             (k k' : cont_label)
             (st st' : thread_st thread)
             (e  : eventid)
             (e' : option eventid)
             (S S' : ES.t) : Prop := 
    ⟪ CertSTEP_ : cert_step_ k e e' S S' ⟫ /\
    ⟪ BSTEP_ : basic_step_ (thread_lts thread) k k' st st' e e' S S' ⟫. 

  Ltac unfold_cert_step_ H := 
    unfold cert_step_, 
           cert_fence_step, 
           cert_load_step, 
           cert_store_step, 
           cert_update_step 
      in H; 
    destruct H as [HA | [HB | [HC | HD]]]; desc.

  Ltac unfold_cert_step H := 
    unfold cert_step in H; 
    destruct H as [H BSTEP_];
    red in BSTEP_;
    unfold_cert_step_ H.

  Lemma simrel_cert_basic_step k lbl lbl' lbls S jf_ ew_ co_
        (st st' st'' : thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'') 
        (ILBL_STEP : ilbl_step (ktid S k) lbls st st') 
        (LBLS_EQ : lbls = opt_to_list lbl' ++ [lbl]) :
    exists k' e e' S',
      ⟪ BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S' ⟫ /\
      ⟪ LBL  : lbl  = S'.(ES.lab) e ⟫ /\
      ⟪ LBL' : lbl' = option_map S'.(ES.lab) e' ⟫ /\
      ⟪ JF' : S'.(ES.jf) ≡ jf_ ⟫ /\
      ⟪ EW' : S'.(ES.ew) ≡ ew_ ⟫ /\
      ⟪ CO' : S'.(ES.co) ≡ co_ ⟫.
  Proof.
    assert (tc_coherent G sc TC') as TCCOH'. 
    { eapply isim_trav_step_coherence; apply SRCC. }
    assert ((K S) (k, existT Language.state (thread_lts (ktid S k)) st)) as KK.
    { edestruct cstate_cont; [apply SRCC|]. desf. }
    assert (wf_thread_state (ktid S k) st) as WFST.
    { by apply SRCC. }

    set (ILBL_STEP' := ILBL_STEP).
    eapply lbl_step_cases in ILBL_STEP'; auto. 
    subst lbls. desc.
    eapply opt_to_list_app_singl in LBLS. 
    desf.

    1-4 : 
      exists (CEvent S.(ES.next_act)); 
      exists S.(ES.next_act); exists None;
      eexists (ES.mk _ _ _ _ _ _ _ _ _);
      splits; simpl; eauto;
      [ econstructor; splits; simpl; eauto; 
        eexists; exists None; 
        splits; simpl; eauto; 
        eapply ILBL_STEP 
      | by rewrite upds ].

    exists (CEvent (1 + S.(ES.next_act))). 
    exists S.(ES.next_act). exists (Some (1 + S.(ES.next_act))).
    eexists (ES.mk _ _ _ _ _ _ _ _ _).
    econstructor; splits; simpl; eauto. 
    { econstructor; splits; simpl; eauto. 
      eexists; eexists. 
      splits; simpl; eauto; by simpl. }
    { rewrite updo; [|omega]. by rewrite upds. }
    by rewrite upds.
  Qed.

  Lemma simrel_cert_basic_step_cert_rf k lbl lbl' lbls S is_ex ord ll vv
        (st st' st'' : thread_st (ktid S k))
        (LBL_LD : lbl = Aload is_ex ord ll vv)
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'') 
        (ILBL_STEP : ilbl_step (ktid S k) lbls st st') 
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'')
        (LBLS_EQ : lbls = opt_to_list lbl' ++ [lbl]) :
    exists w,
      ⟪ CertEx : certX S k w ⟫ /\
      ⟪ CertRF : (cert_rf G sc TC' (ktid S k)) 
                   (e2a S w) (ThreadEvent (ktid S k) (st.(eindex))) ⟫.
  Proof.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert ((K S) (k, existT Language.state (thread_lts (ktid S k)) st)) as KK.
    { edestruct cstate_cont; [apply SRCC|]. desf. }
    assert (wf_thread_state (ktid S k) st) as WFST.
    { by apply SRCC. }
    assert (tc_coherent G sc TC') as TCCOH'.
    { eapply isim_trav_step_coherence; apply SRCC. }
    desc.
    edestruct cert_rf_complete as [w' RFwa];
      eauto; try apply SRCC.
    { assert
        (E0 G TC' (ktid S k) (ThreadEvent (ktid S k) st.(eindex)))
        as E0_eindex.
      { eapply ilbl_step_E0_eindex; eauto. apply SRCC. }
      split; eauto.
      eapply same_lab_u2v_dom_is_r.
      { apply same_lab_u2v_dom_comm.
        eapply cuplab_cert. apply SRCC. }
      split.
      { eapply dcertE; eauto; apply SRCC. }
      unfold is_r.
      erewrite steps_preserve_lab.
      { edestruct lbl_step_cases as [la [lb [LBLS HH]]]; eauto.
      subst lbls. apply opt_to_list_app_singl in LBLS.
      desc. subst la lb.
      destruct HH as [HA | HB].
      { destruct HA as [_ [_ [LAB _]]].
        rewrite LAB, upds. desf. }
      destruct HB as [_ [_ [LAB [LBLS' RMW]]]].
      rewrite LAB.
      rewrite updo_opt, upds; desf.
      red. ins. inv H. omega. }
      { eapply wf_thread_state_steps; eauto.
        eapply ilbl_steps_in_steps.
        econstructor; econstructor; eauto. }
      { by eapply ilbl_steps_in_steps. }
      edestruct lbl_step_cases as [la [lb [LBLS HH]]]; eauto.
      generalize HH. basic_solver. }
    assert (cert_dom G TC (ktid S k) st w') as CertDw'.
    { eapply cert_rf_cert_dom; try apply SRCC; auto.
      { red. ins. eapply ES.init_tid_K; eauto. }
      unfold dom_rel. eexists.
      apply seq_eqv_r; splits; eauto. }
    eapply cert_ex_certD in CertDw'; eauto.
    destruct CertDw' as [w [CertXw EQw']].
    exists w; splits; subst; auto.
  Qed.

  Lemma simrel_cert_fence_step k lbl S ord
        (st st' st'' : thread_st (ktid S k))
        (LBL_F : lbl = Afence ord)
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'') 
        (ILBL_STEP : ilbl_step (ktid S k) [lbl] st st') 
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    exists k' e e' S', 
      ⟪ BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S' ⟫ /\
      ⟪ CertFSTEP  : cert_fence_step e e' S S' ⟫.
  Proof. 
    desf.
    edestruct simrel_cert_basic_step as [k' [e [e' [S' HH]]]]; eauto.
    { erewrite opt_to_list_none. done. }    
    desf. cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor. eauto. }
    assert (SE S' e) as SEe.
    { eapply basic_step_acts_set; eauto. 
      basic_solver. }
    assert (SF S' e) as SFe.
    { unfold is_f. by rewrite <- LBL. }
    assert (e' = None) as e'None.
    { step_solver. }
    desf; do 5 eexists; splits; eauto.
    econstructor; splits; eauto.
  Qed.

  Lemma simrel_cert_load_step k lbl S is_ex ord ll vv
        (st st' st'' : thread_st (ktid S k))
        (LBL_LD : lbl = Aload is_ex ord ll vv)
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'') 
        (ILBL_STEP : ilbl_step (ktid S k) [lbl] st st') 
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    exists k' e e' S', 
      ⟪ BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S' ⟫ /\
      ⟪ CertLdSTEP  : cert_load_step k e e' S S' ⟫. 
  Proof. 
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    edestruct simrel_cert_basic_step_cert_rf
      as [w HA]; eauto 10.
    { erewrite opt_to_list_none. done. } 
    edestruct simrel_cert_basic_step as [k' [e [e' [S' HB]]]]; eauto.
    { erewrite opt_to_list_none. done. }    
    desf. cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor. eauto. }
    assert (SE S' e) as SEe.
    { eapply basic_step_acts_set; eauto. 
      basic_solver. }
    assert (SR S' e) as SRe.
    { unfold is_r. by rewrite <- LBL. }
    assert (e' = None) as e'None.
    { step_solver. }
    desf; do 5 eexists; splits; eauto.
    desc. exists w. 
    splits; eauto.
    econstructor; splits; eauto.
    erewrite basic_step_e2a_eq_dom; eauto. 
    2 : { eapply cert_ex_inE; eauto. } 
    erewrite basic_step_e2a_e
      with (S' := S'); eauto; try apply SRCC.
  Qed.

  Lemma simrel_cert_store_step k lbl S ord ll vv
        (st st' st'' : thread_st (ktid S k))
        (LBL_ST : lbl = Astore Xpln ord ll vv)
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'') 
        (ILBL_STEP : ilbl_step (ktid S k) [lbl] st st') 
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    exists k' e e' S', 
      ⟪ BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S' ⟫ /\
      ⟪ CertStSTEP  : cert_store_step k e e' S S' ⟫.
  Proof. 
    desf.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    edestruct simrel_cert_basic_step as [k' [e [e' [S' HH]]]]; eauto.
    { erewrite opt_to_list_none. done. }    
    desf. cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor. eauto. }
    assert (SE S' e) as SEe.
    { eapply basic_step_acts_set; eauto. 
      basic_solver. }
    assert (SW S' e) as SWe.
    { unfold is_w. by rewrite <- LBL. }
    assert (e' = None) as e'None.
    { step_solver. }
    desf; do 5 eexists; splits; eauto.
    econstructor; splits; eauto.
    all : econstructor; splits; eauto.   
    { unfold ew_delta, sim_ews. 
      erewrite basic_step_e2a_e with (e := ES.next_act S); 
        eauto; try apply SRCC. }
    unfold co_delta.
    unfold sim_ews, sim_ws.
    erewrite basic_step_e2a_e with (e := ES.next_act S); 
        eauto; try apply SRCC.
  Qed.

  Lemma simrel_cert_update_step k lbl lbl' lbls S is_ex ordr ordw ll vvr xmod vvw
        (st st' st'' : thread_st (ktid S k))
        (LBL_LD : lbl = Aload is_ex ordr ll vvr) 
        (LBL_ST : lbl' = Some (Astore xmod ordw ll vvw))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'') 
        (ILBL_STEP : ilbl_step (ktid S k) lbls st st') 
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'')
        (LBLS_EQ : lbls = opt_to_list lbl' ++ [lbl]) :
    exists k' e e' S', 
      ⟪ BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S' ⟫ /\
      ⟪ CertUpdSTEP  : cert_update_step k e e' S S' ⟫. 
  Proof. 
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    desc. 
    edestruct simrel_cert_basic_step_cert_rf
      as [w HA]; eauto 10.
    edestruct simrel_cert_basic_step as [k' [e [e' [S' HB]]]]; eauto.
    desf. cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor. eauto. }
    destruct e' as [e'|].
    2 : { unfold opt_same_ctor in *. desf. }
    assert (SE S' e) as SEe.
    { eapply basic_step_acts_set; eauto. 
      basic_solver. }
    assert (SR S' e) as SRe.
    { unfold is_r. by rewrite <- LBL. }
    assert (SE S' e') as SEe'.
    { eapply basic_step_acts_set; eauto. 
      basic_solver. }
    unfold option_map in LBL'. 
    inversion LBL' as [[LBL'']].
    assert (SW S' e') as SWe'.
    { unfold is_w. by rewrite <- LBL''. }
    unfold opt_ext in *. desc.
    desf; do 5 eexists; splits; eauto. 
    exists w. eexists.
    splits; eauto.
    { red. unfold Events.loc.
        by rewrite <- LBL, <- LBL''. }
    { econstructor; splits; eauto.
      erewrite basic_step_e2a_eq_dom; eauto. 
      2 : { eapply cert_ex_inE; eauto. } 
      erewrite basic_step_e2a_e
        with (S' := S'); eauto; try apply SRCC. }
    all : econstructor; splits; eauto.   
    { unfold ew_delta, sim_ews. 
      erewrite basic_step_e2a_e' with (e' := 1 + ES.next_act S); 
        eauto; try apply SRCC. }
    unfold co_delta.
    unfold sim_ews, sim_ws.
    erewrite basic_step_e2a_e' with (e' := 1+ ES.next_act S); 
      eauto; try apply SRCC.
  Qed.

  Lemma simrel_cert_step k lbls S
        (st st' st'' : thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'') 
        (ILBL_STEP : ilbl_step (ktid S k) lbls st st') 
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
    exists k' e e' S', ⟪ CertSTEP : cert_step k k' st st' e e' S S' ⟫. 
  Proof. 
    edestruct lbl_step_cases as [lbl [lbl' HH]]; eauto.
    { apply SRCC. edestruct cstate_cont; [apply SRCC|]. desf. }
    desf.
    1-4: rewrite opt_to_list_none in ILBL_STEP.
    1,2: edestruct simrel_cert_load_step; eauto.
    3: edestruct simrel_cert_store_step; eauto.
    4: edestruct simrel_cert_fence_step; eauto.
    5: edestruct simrel_cert_update_step; eauto.
    all: by desf; unfold cert_step, cert_step_; eauto 20.
  Qed.
  
  Lemma simrel_cert_step_step_ k k' e e' S S'
        (st st' st'' : thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'') 
        (CertSTEP : cert_step k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    step_ e e' S S'. 
  Proof. 
    unfold_cert_step CertSTEP.
    { left. econstructor; splits; auto. }
    { right; left. econstructor; splits; auto.
      eapply weaken_sim_add_jf; eauto. }
    { right; right; left. 
      econstructor. 
      eexists; splits; auto.
      { eapply weaken_sim_add_ew; eauto. basic_solver. }
      eapply weaken_sim_add_co; eauto. basic_solver. }
    right; right; right. 
    econstructor. 
    do 3 eexists; splits; eauto.
    { eapply weaken_sim_add_jf; eauto. }
    { eapply weaken_sim_add_ew; eauto. basic_solver. }
    eapply weaken_sim_add_co; eauto. basic_solver.
  Qed.

  Lemma simrel_cert_step_e2a_GE k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
    e2a S' □₁ SE S' ⊆₁ GE.
  Proof.
    cdes CertSTEP; cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ES.Wf S) as WF by apply SRCC.
    assert (tc_coherent G sc TC') as TCCOH'.
    { eapply sim_trav_step_coherence; eauto; try apply SRCC.
      red. eexists. apply SRCC. }
    rewrite basic_step_acts_set; eauto.  
    rewrite !set_collect_union. 
    rewrite !set_subset_union_l.
    splits. 
    { erewrite set_collect_eq_dom; [eapply SRCC|].
      eapply basic_step_e2a_eq_dom; eauto. } 
    { rewrite set_collect_eq.
      apply eq_predicate. 
      eapply basic_step_e2a_GE_e with (S:=S); eauto; try apply SRCC. }
    destruct e' as [e'|]; [|basic_solver]. 
    unfold eq_opt. 
    rewrite set_collect_eq.
    apply eq_predicate. 
    eapply basic_step_e2a_GE_e' with (S:=S); eauto; apply SRCC.
  Qed.
  
  Lemma simrel_cert_step_e2a_GEinit k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step k k' st st' e e' S S') :
    GEinit ⊆₁ e2a S' □₁ SEinit S'.
  Proof.
    cdes CertSTEP; cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ES.Wf S) as WF by apply SRCC.
    etransitivity. 
    { eapply e2a_GEinit. apply SRCC. }
    erewrite basic_step_acts_init_set with (S' := S'); eauto.
    eapply set_collect_eq_dom.
    unfold ES.acts_init_set.
    unfolder. ins. desf.
    eapply basic_step_e2a_eq_dom; eauto.
  Qed.

  Lemma simrel_cert_step_e2a_lab k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
    same_lab_u2v_dom (SE S') (Slab S')
                     (Basics.compose Glab (e2a S')).
  Proof.
    cdes CertSTEP; cdes BSTEP_.
    eapply basic_step_e2a_same_lab_u2v with (S:=S); eauto;
      apply SRCC.
  Qed.

  Lemma simrel_cert_step_wf k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
    ES.Wf S'.
  Proof.
    cdes CertSTEP; cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (step_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WF by apply SRCC.
    assert (Wf G) as WFG by apply SRCC.
    assert (simrel_e2a S G sc) as E2A by apply SRCC.
    assert (SE S' e) as SEe.
    { eapply basic_step_acts_set; eauto. 
      basic_solver. }

    eapply step_wf; eauto.
    ins. red.

    assert (exists ag, ⟪AIG : GEinit ag⟫ /\
                       ⟪LLG : Gloc ag = Some l⟫); desf.
    2: { set (BB:=AIG).
         eapply simrel_cert_step_e2a_GEinit in BB; eauto.
         red in BB. desf.
         exists y. splits; auto.
         rewrite <- LLG.
         arewrite (Gloc (e2a S' y) =
                   Events.loc (Basics.compose Glab (e2a S')) y).
         eapply same_lab_u2v_dom_loc.
         { eapply simrel_cert_step_e2a_lab; eauto. }
         apply BB. }
   exists (InitEvent l).
    splits; auto.
    2: { unfold Events.loc. rewrite wf_init_lab; auto. }
    split; auto.
    apply wf_init; auto.
    exists (e2a S' (ES.next_act S)).
    split.
    { eapply simrel_cert_step_e2a_GE; eauto.
      red. eexists. split; eauto. }
    rewrite <- LL. symmetry.
    arewrite (Gloc (e2a S' (ES.next_act S)) =
              Events.loc (Basics.compose Glab (e2a S')) (ES.next_act S)).
    eapply same_lab_u2v_dom_loc.
    { eapply simrel_cert_step_e2a_lab; eauto. }
    done.
  Qed.

  Lemma simrel_cert_step_jf_E k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'') 
        (CertSTEP : cert_step k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    Sjf S' ⨾ ⦗SE S⦘ ≡ Sjf S.
  Proof.
    cdes CertSTEP; cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor. eauto. }
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    red in CertSTEP_. desf; cdes CertSTEP_; desf.
    1,3: rewrite (dom_r WF.(ES.jfE)); rewrite JF'; basic_solver.
    all: eapply weaken_sim_add_jf in AJF; eauto.
    all: eapply add_jf_jfE; eauto.
  Qed.

  Lemma simrel_cert_step_e2a k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'') 
        (CertSTEP : cert_step k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
    simrel_e2a S' G sc. 
  Proof. 
    cdes CertSTEP; cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor. eauto. }
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (sim_trav_step G sc TC TC') as TCSTEP.
    { red. eexists. eapply tr_step; eauto. }
    assert (tc_coherent G sc TC') as TCCOH'.
    { eapply sim_trav_step_coherence; eauto. apply SRCC. }
    assert (ES.Wf S') as WF'.
    { eapply simrel_cert_step_wf; eauto. }
    assert (SE S' e) as SEE.
    { eapply basic_step_acts_set; eauto. basic_solver. }

    assert (e2a S' □₁ SE S' ⊆₁ GE) as E2AGE.
    { eapply simrel_cert_step_e2a_GE; eauto. }

    assert (same_lab_u2v_dom (SE S') (Slab S') (Basics.compose Glab (e2a S')))
      as E2ALAB.
    { eapply simrel_cert_step_e2a_lab; eauto. }

    constructor; auto.
    { eapply simrel_cert_step_e2a_GEinit; eauto. }
    (* e2a_rmw : e2a □ Srmw ⊆ Grmw *)
    { unfold_cert_step_ CertSTEP_.
      1-3 : 
        eapply simrel_cert_basic_step_e2a_eqr;
        try eapply basic_step_nupd_rmw; 
        try apply ES.rmwE; subst e'; eauto;
        apply SRCC.
      rewrite RMW'. 
      unfold rmw_delta.
      rewrite collect_rel_union. 
      unionL.
      { eapply simrel_cert_basic_step_e2a_eqr; eauto.
         { by apply ES.rmwE. }
         apply SRCC. }
      unfold eq_opt. subst e'.
      rewrite collect_rel_cross, !set_collect_eq.
      etransitivity; [|eapply inclusion_restr].
      rewrite restr_relE.
      erewrite <- dcertRMW; [|apply SRCC].
      etransitivity.
      2 : { eapply steps_preserve_rmw.
            eapply ilbl_steps_in_steps; eauto. }
      edestruct cstate_cont; [apply SRCC|]. desc.
      edestruct lbl_step_cases as [l [l' HH]].
      { eapply wf_cont_state; eauto. }
      { apply STEP. }
      destruct HH as [EE HH].
      apply opt_to_list_app_singl in EE.
      unfold opt_same_ctor in *. desf.
      rewrite GRMW.
      erewrite basic_step_e2a_e with (S:=S); eauto; try apply SRCC.
      erewrite basic_step_e2a_e' with (S0:=S); eauto; try apply SRCC.
      basic_solver. }
    (* e2a_ew  : e2a □ Sew  ⊆ eq *)
    { unfold_cert_step_ CertSTEP_.
      1,2 : 
        eapply simrel_cert_basic_step_e2a_eqr; eauto;
        try apply ES.ewE; apply SRCC.
      all : eapply sim_add_ew_e2a_ew_eq; eauto.
      all : try rewrite ESOME; basic_solver. }
    (* e2a_co  : e2a □ Sco  ⊆ Gco *)
    { unfold_cert_step_ CertSTEP_.
      1,2 : 
        eapply simrel_cert_basic_step_e2a_eqr; eauto;
        try apply ES.coE; apply SRCC.
      all : eapply sim_add_co_e2a_co; eauto.
      all : basic_solver. }
    { assert (e2a S' □ Sjf S ⊆ Gfurr) as AA.
      { eapply simrel_cert_basic_step_e2a_eqr; eauto.
        2: by apply SRCC.
        apply WF.(ES.jfE). }
      red in CertSTEP_. desf; cdes CertSTEP_.
      all: try cdes AJF.
      all: rewrite JF'; auto.
      all: rewrite collect_rel_union; unionL; auto.
      { unfolder. ins. desf.
        eapply cert_rf_in_furr.
        1,2: by apply SRCC.
        match goal with
        | H : jf_delta _ _ _ _ |- _ => inv H
        end.
        apply CertRF. }
      unfold jf_delta.
      unfolder. ins. desf.
      eapply cert_rf_in_furr; eauto.
      all: apply SRCC. }
    { assert (e2a S' □ Sjf S ⨾ Srmw S ⊆ Grf ⨾ Grmw) as AA.
      { eapply simrel_cert_basic_step_e2a_eqr; eauto.
        2: by apply SRCC.
        split; [|basic_solver].
        rewrite (dom_l WF.(ES.jfE)) at 1.
        rewrite (dom_r WF.(ES.rmwE)) at 1.
        basic_solver. }
      assert (forall w,
                 e2a S' □ jf_delta w (ES.next_act S) ⨾ Srmw S ⊆ Grf ⨾ Grmw)
        as BB.
      { unfold jf_delta. ins. rewrite (dom_l WF.(ES.rmwE)).
        unfold ES.acts_set. unfolder. ins. desf. omega. }
      rewrite RMW'. unfold rmw_delta, eq_opt.
      red in CertSTEP_. desf; cdes CertSTEP_.
      all: try cdes AJF.
      all: rewrite JF'; desf.
      all: rewrite seq_union_r, ?seq_union_l,
           !collect_rel_union; unionL; auto.
      1-4: basic_solver.
      { rewrite (dom_r WF.(ES.jfE)). unfold ES.acts_set.
        unfolder. ins. desf. omega. }
      assert (Grf (e2a S' w) (e2a S' (ES.next_act S))) as RF.
      { (* TODO: for Anton *)
        admit. }
      unfold jf_delta. unfolder. ins. desf.
      eexists. splits; eauto.
      (* TODO: for Evgenii *)
      admit. }

    assert (e2a S' □ ES.cont_sb_dom S k × eq e ⊆
            Gsb ;; <| eq (e2a S' e) |>) as HHSB.
    { (* TODO: for Evgenii *)
      admit. }
    assert (Sjf S' ⨾ ⦗SE S⦘ ⊆ Sjf S) as JFES.
    { eapply simrel_cert_step_jf_E; eauto. }

    rewrite SB'.
    rewrite seq_union_l, cr_union_l.
    rewrite !seq_union_l, !seq_union_r.
    rewrite collect_rel_union.
    unionL.
    2: { unfold sb_delta.
         rewrite !seq_union_l, !seq_union_r.
         arewrite ((ES.cont_sb_dom S k ∪₁ eq e) × eq_opt e' ⨾ ⦗SF S'⦘ ⊆ ∅₂).
         { unfold eq_opt.
           red in CertSTEP_. desf; cdes CertSTEP_; desf.
           1-3: basic_solver.
           arewrite ((fun b : eventid => w' = b) ⊆₁ SW S').
           2: type_solver.
           unfolder. ins. desf. unfold is_w.
           rewrite LAB'. rewrite upds.
           inv STEP. desc.
           match goal with
           | H : ineps_step _ _ _ _ |- _ => cdes H
           end.
           cdes STEP0. inv ISTEP0; inv LABELS. }
         relsf.
         arewrite (Sjf S' ⨾ ES.cont_sb_dom S k × eq e ⊆
                   Sjf S' ;; <|ES.cont_sb_dom S k|> ⨾
                   ES.cont_sb_dom S k × eq e) by basic_solver 10.
         arewrite (ES.cont_sb_dom S k ⊆₁ SE S ∩₁ ES.cont_sb_dom S k) at 1.
         { apply set_subset_inter_r. split; auto.
           eapply kE_inE; eauto. }
         rewrite id_inter, !seqA.
         sin_rewrite JFES.
         rewrite <- seqA. rewrite collect_rel_seqi.
         arewrite (e2a S' □ Sjf S ⨾ ⦗ES.cont_sb_dom S k⦘ ⊆
                   e2a S  □ Sjf S ⨾ ⦗ES.cont_sb_dom S k⦘).
         { rewrite WF.(ES.jfE) at 1.
           unfolder. ins. desf. do 2 eexists. splits; eauto.
           all: symmetry.
           all: eapply basic_step_e2a_eq_dom; eauto. }
         arewrite (ES.cont_sb_dom S k × eq e ⨾ ⦗SF S'⦘ ⨾ ⦗SAcq S'⦘ ⊆
                   ES.cont_sb_dom S k × eq e ⨾
                   ⦗SE S' ∩₁ SF S'⦘ ⨾ ⦗SE S' ∩₁ SAcq S'⦘).
         { generalize SEE. basic_solver 10. }
         rewrite jf_in_cert_rf; eauto.
         rewrite !collect_rel_seqi, !collect_rel_eqv.
         erewrite e2a_F; eauto.
         erewrite e2a_Acq; eauto.
         sin_rewrite HHSB.
         arewrite (eq (e2a S' e) ⊆₁ E0 G TC' (ES.cont_thread S k)).
         { unfolder. ins. desf. eapply basic_step_e2a_E0_e; eauto.
           all: apply SRCC. }
         arewrite (⦗GE ∩₁ GF⦘ ⨾ ⦗GE ∩₁ GAcq⦘ ⊆
                   ⦗GE ∩₁ GF⦘ ⨾ ⦗GE ∩₁ GAcq⦘ ⨾ ⦗GF ∩₁ GAcq⦘) by basic_solver.
         assert (Gsb ⨾ ⦗GF ∩₁ GAcq⦘ ⊆ (Gsb ⨾ ⦗GF⦘)^? ⨾ ⦗GAcq⦘) as BB
             by basic_solver 10.
         rewrite <- BB.
         hahn_frame.
         etransitivity.
         2: { apply cert_rf_sb_F_Acq_in_rf; eauto; try apply SRCC.
              eapply sim_trav_step_rel_covered; eauto.
              apply SRCC. }
         basic_solver 10. }

    rewrite crE, !seq_union_l, !seq_union_r, !seq_id_l.
    rewrite collect_rel_union.
    unionL.
    2: { rewrite WF.(ES.sbE), !seqA.
         sin_rewrite JFES.
         arewrite (⦗SE S⦘ ⨾ ⦗SF S'⦘ ⨾ ⦗SAcq S'⦘ ⊆
                   ⦗SE S⦘ ⨾ ⦗SE S ∩₁ SF S'⦘ ⨾ ⦗SE S ∩₁ SAcq S'⦘)
           by basic_solver.
         erewrite basic_step_f_in_f; eauto.
         erewrite basic_step_acq_in_acq; eauto.
         erewrite simrel_cert_basic_step_e2a_eqr; eauto.
         { reflexivity. }
         { rewrite WF.(ES.jfE). basic_solver 20. }
         etransitivity; [|by apply SRCC].
         basic_solver 20. }

    assert (e2a S' □ Sjf S ⨾ ⦗SAcq S'⦘ ⊆ Grf ⨾ (Gsb ⨾ ⦗GF⦘)^? ⨾ ⦗GAcq⦘) as AA.
    { rewrite WF.(ES.jfE), !seqA, <- id_inter.
      rewrite basic_step_acq_in_acq; eauto.
      erewrite simrel_cert_basic_step_e2a_eqr; eauto.
      { reflexivity. }
      { rewrite WF.(ES.jfE). basic_solver 20. }
      etransitivity; [|by apply SRCC].
      basic_solver 20. }

    assert (forall w (AJF : sim_add_jf G sc TC' X k w (ES.next_act S) S S'),
               e2a S' □ Sjf S' ⨾ ⦗SAcq S'⦘ ⊆ Grf ⨾ (Gsb ⨾ ⦗GF⦘)^? ⨾ ⦗GAcq⦘)
      as BB.
    { ins. cdes AJF. rewrite JF'.
      rewrite !seq_union_l, collect_rel_union. unionL; auto.
      unfold jf_delta.
      arewrite (singl_rel w (ES.next_act S) ⨾ ⦗SAcq S'⦘ ⊆
                singl_rel w (ES.next_act S) ⨾ ⦗SE S' ∩₁ SAcq S'⦘).
      { generalize SEE. basic_solver. }
      rewrite collect_rel_seqi, collect_rel_eqv.
      rewrite e2a_Acq; eauto.
      rewrite <- inclusion_id_cr, seq_id_l.
      unfolder. ins. desf. split; auto.
      eapply cert_rf_Acq_in_rf; eauto.
      1,2: by apply SRCC.
      apply seq_eqv_r. split; eauto. }
    
    red in CertSTEP_. desf; cdes CertSTEP_.
    all: try by rewrite JF'.
    all: eapply BB; eauto.
  Admitted.

  Lemma simrel_cert_step_rel_ew_ex_iss k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'') 
        (CertSTEP : cert_step k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
    dom_rel (release S' ⨾ Sew S' ⨾ ⦗X ∩₁ e2a S' ⋄₁ I⦘) ⊆₁ X.
  Proof.
    cdes CertSTEP.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (step_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S') as WFS'.
    { eapply simrel_cert_step_wf; eauto. }
    cdes BSTEP_.

    arewrite (X ∩₁ e2a S' ⋄₁ I ⊆₁ X ∩₁ e2a S ⋄₁ I).
    { arewrite (X ⊆₁ X ∩₁ SE S).
      { apply set_subset_inter_r; split; [done|].
        apply SRCC. }
      rewrite set_interA.
      arewrite (SE S ∩₁ e2a S' ⋄₁ I ⊆₁ SE S ∩₁ e2a S ⋄₁ I).
      2: basic_solver.
      apply set_subset_inter_r; split; [basic_solver|].
      unfolder. ins. desf.
      erewrite <- basic_step_e2a_eq_dom; eauto. }

    assert (release S' ⨾ ⦗SE S⦘ ⊆ release S ->
            dom_rel (release S' ⨾ Sew S ⨾ ⦗X ∩₁ e2a S ⋄₁ I⦘) ⊆₁ X) as BB.
    { intros AA.
      rewrite (dom_l WFS.(ES.ewE)), !seqA.
      sin_rewrite AA. apply SRCC. }

    assert (forall r, r × eq (ES.next_act S) ⨾ ⦗X ∩₁ e2a S ⋄₁ I⦘ ⊆ ∅₂) as CC.
    { ins.
      rewrite <- cross_inter_r.
      arewrite (eq (ES.next_act S) ∩₁ (X ∩₁ e2a S ⋄₁ I) ⊆₁ ∅).
      2: basic_solver.
      arewrite (X ⊆₁ SE S) by apply SRCC.
      unfold ES.acts_set.
      unfolder. ins. desf. omega. }

    red in CertSTEP_. desf; cdes CertSTEP_.

    1,2: desf; simpls; rewrite EW'.
    1,2: apply BB.
    { erewrite step_same_jf_releaseE; eauto; [basic_solver|].
      rewrite RMW'. unfold rmw_delta, eq_opt. basic_solver. }
    { erewrite add_jf_releaseE; eauto; [basic_solver|].
      eapply weaken_sim_add_jf; eauto. }

    { cdes AEW.
      arewrite (Sew S' ⊆ Sew S' ∩ Sew S').
      rewrite EW' at 2.
      rewrite inter_union_r.
      rewrite !seq_union_l, !seq_union_r.
      rewrite dom_union.
      unionL.
      { arewrite (Sew S' ∩ Sew S ⊆ Sew S).
        apply BB.
        erewrite step_same_jf_releaseE; eauto; [basic_solver|].
        rewrite RMW'. unfold rmw_delta, eq_opt. basic_solver. }
      unfold ew_delta.
      rewrite inter_union_r.
      rewrite !seq_union_l, !seq_union_r. rewrite dom_union. unionL.
      { arewrite (Sew S' ∩ eq (ES.next_act S) × eq (ES.next_act S) ⊆
                  eq (ES.next_act S) × eq (ES.next_act S)).
        erewrite CC. basic_solver. }
      unfold clos_sym.
      rewrite inter_union_r.
      rewrite !seq_union_l, !seq_union_r.
      rewrite dom_union. unionL.
      { arewrite
          (Sew S' ∩ sim_ews TC X (ES.next_act S) S S' × eq (ES.next_act S) ⊆
               sim_ews TC X (ES.next_act S) S S' × eq (ES.next_act S)).
        erewrite CC. basic_solver. }
      rewrite transp_cross.
      arewrite (release S' ⊆ release S' ∩ eq ∪ release S' \ eq).
      { unfolder. ins. destruct (classic (x = y)); basic_solver. }
      rewrite !seq_union_l.
      rewrite dom_union. unionL.
      { unfold sim_ews. rewrite releaseD; auto.
        unfolder. ins. desf.
        { type_solver. }
        exfalso.
        apply WFS.(ES.ewE) in wEWI.
        destruct_seq wEWI as [SEY SEY'].
        match goal with
        | [H : (Sew S') (ES.next_act S) y |- _ ] => rename H into AA
        end.
        apply WFS'.(ES.ewm) in AA.
        destruct AA as [|[AA QQ]]; subst.
        { red in SEY. omega. }
        unfold is_only_rlx in *.
        mode_solver. }
      (* TODO: continue from here *)

      (* unfold sim_ews. *)
      (* unfolder. ins. desf. *)
      (* assert ((e2a S' ⋄₁ I) (ES.next_act S) -> *)
      (*         dom_rel (release S' ⨾ ⦗eq (ES.next_act S)⦘) ⊆₁ X) *)
      (*   as DD. *)
      (* { intros AA. *)
      (*   unfold Consistency.release, Consistency.rs. *)
      (*   admit. } *)
      (* eapply DD. *)
      (* 2: { eexists. apply seq_eqv_r. split; eauto. } *)
      (* red. by rewrite <- wsE2Aeq. } *)
    admit.
  Admitted.

  Lemma simrel_cert_step_simrel_ k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'') 
        (CertSTEP : cert_step k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
    simrel_ prog S' G sc TC X.
  Proof. 
    cdes CertSTEP.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (step_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (Execution.t S X) as EXEC.
    { apply SRCC. }
    constructor; try apply SRCC.
    { eapply simrel_cert_step_wf; eauto. }
    { eapply step_preserves_execution; eauto; apply SRCC. }
    { eapply basic_step_simrel_cont; eauto; try apply SRCC. 
      eapply cstate_covered; eauto. }
    { eapply simrel_cert_step_e2a; eauto. }
    1-4 : admit.
    (* jfe_ex_iss : dom_rel Sjfe ⊆₁ dom_rel (Sew ⨾ ⦗ X ∩₁ e2a ⋄₁ I ⦘) *)
    { erewrite basic_step_e2a_set_map_inter_old; eauto.
      2 : apply Execution.ex_inE; auto.
      etransitivity. 
      { unfold_cert_step_ CertSTEP_.
        2,4 : eapply sim_add_jf_jfe_ex_iss; eauto.
        all : erewrite step_same_jf_jfe; 
          eauto; apply SRCC. }
      erewrite step_ew_mon; eauto. }
    (* ew_ex_iss : dom_rel (Sew \ eq) ⊆₁ dom_rel (Sew ⨾ ⦗ X ∩₁ e2a ⋄₁ I ⦘) *)
    { erewrite basic_step_e2a_set_map_inter_old; eauto.
      2 : apply Execution.ex_inE; auto.
      unfold_cert_step_ CertSTEP_.
      1,2 : rewrite EW'; apply SRCC.
      all : eapply sim_add_ew_ew_ex_iss; eauto.
      all : basic_solver. }
    (* rel_ew_ex_iss : dom_rel (Srelease ⨾ Sew ⨾ ⦗ X ∩₁ e2a ⋄₁ I  ⦘) ⊆₁ X *)
    eapply simrel_cert_step_rel_ew_ex_iss; eauto.
  Admitted.
        
End SimRelCertStep.

(* repeat tactics again *)

Ltac unfold_cert_step_ H := 
  unfold cert_step_, 
  cert_fence_step, 
  cert_load_step, 
  cert_store_step, 
  cert_update_step 
  in H; 
  destruct H as [HA | [HB | [HC | HD]]]; desc.

Ltac unfold_cert_step H := 
  unfold cert_step in H; 
  destruct H as [H BSTEP_];
  red in BSTEP_;
  unfold_cert_step_ H.
