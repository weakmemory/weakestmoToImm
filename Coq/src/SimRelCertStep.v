Require Import Omega.
Require Import Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality Classical_Prop.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution
     Traversal TraversalConfig SimTraversal SimTraversalProperties
     Prog ProgToExecution ProgToExecutionProperties Receptiveness
     imm_common imm_s imm_s_hb SimulationRel
     CertExecution2 CertExecutionMain
     SubExecution CombRelations AuxRel.
Require Import AuxRel AuxDef EventStructure BasicStep Step Consistency 
        LblStep CertRf CertGraph EventToAction ImmProperties
        SimRelCont SimRelEventToAction 
        SimRel SimRelCert SimRelCertBasicStep SimRelAddJF SimRelAddEW SimRelAddCO.  
Require Import StepWf.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelCertStep.

  Variable prog : Prog.t.
  Variable G : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable TC' : trav_config.
  Variable f : actid -> eventid.
  Variable h : actid -> eventid.

  Notation "'SE' S" := S.(ES.acts_set) (at level 10).
  Notation "'SEinit' S" := S.(ES.acts_init_set) (at level 10).
  Notation "'SEninit' S" := S.(ES.acts_ninit_set) (at level 10).
  Notation "'Stid' S" := (S.(ES.tid)) (at level 10).
  Notation "'Slab' S" := S.(ES.lab) (at level 10).
  Notation "'Sloc' S" := (loc S.(ES.lab)) (at level 10).

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

  Notation "'Stid_' t" := (fun x => Stid x = t) (at level 1).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gtid'" := (tid).
  Notation "'Grmw'" := G.(rmw).
  Notation "'Gaddr'" := G.(addr).
  Notation "'Gdata'" := G.(data).
  Notation "'Gctrl'" := G.(ctrl).
  Notation "'Grmw_dep'" := G.(rmw_dep).

  Notation "'Gtid_' t" := (fun x => tid x = t) (at level 1).
  Notation "'GNtid_' t" := (fun x => tid x <> t) (at level 1).

  Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
  Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

  Notation "'GR'" := (fun a => is_true (is_r Glab a)).
  Notation "'GW'" := (fun a => is_true (is_w Glab a)).
  Notation "'GR_ex'" := (fun a => R_ex Glab a).

  Notation "'Gsb'" := (G.(sb)).
  Notation "'Ghb'" := (G.(imm_s_hb.hb)).
  Notation "'Grf'" := (G.(rf)).
  Notation "'Gco'" := (G.(co)).
  Notation "'Gvf'" := (G.(furr)).
  Notation "'Gppo'" := (G.(ppo)).
  Notation "'Geco'" := (G.(Execution_eco.eco)).

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).
  Notation "'C''"  := (covered TC').
  Notation "'I''"  := (issued TC').

  Notation "'thread_syntax' tid"  := 
    (Language.syntax (thread_lts tid)) (at level 10, only parsing).  

  Notation "'thread_st' tid" := 
    (Language.state (thread_lts tid)) (at level 10, only parsing).

  Notation "'thread_init_st' tid" := 
    (Language.init (thread_lts tid)) (at level 10, only parsing).

  Notation "'thread_cont_st' tid" :=
    (fun st => existT _ (thread_lts tid) st) (at level 10, only parsing).

  Notation "'cont_lang'" :=
    (fun S k => thread_lts (ES.cont_thread S k)) (at level 10, only parsing).

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
             (thread : thread_id)
             (st : thread_st thread)
             (e : eventid)
             (e' : option eventid)
             (S S' : ES.t) : Prop :=
    exists w, 
      ⟪ ENONE : e' = None ⟫ /\
      ⟪ AJF : sim_add_jf G sc TC TC' h thread st w e S S' ⟫ /\
      ⟪ EW' : Sew S' ≡ Sew S ⟫ /\
      ⟪ CO' : Sco S' ≡ Sco S ⟫.

  Definition cert_store_step
             (k : cont_label)
             (e  : eventid)
             (e' : option eventid)
             (S S' : ES.t) : Prop :=
    ⟪ ENONE : e' = None ⟫ /\
    ⟪ JF' : Sjf S' ≡ Sjf S ⟫ /\ 
    ⟪ AEW : sim_add_ew TC f e S S' ⟫ /\
    ⟪ ACO : sim_add_co G TC f k e S S' ⟫.

  Definition cert_update_step
             (thread : thread_id)
             (k : cont_label)
             (st : thread_st thread)
             (e  : eventid)
             (e' : option eventid)
             (S S' : ES.t) : Prop := 
    exists w w',
      ⟪ ESOME : e' = Some w' ⟫ /\ 
      ⟪ AJF : sim_add_jf G sc TC TC' h thread st w e S S' ⟫ /\ 
      ⟪ AEW : sim_add_ew TC f w' S S' ⟫ /\
      ⟪ ACO : sim_add_co G TC f k w' S S' ⟫.

  Definition cert_step_ 
             (thread : thread_id)
             (k : cont_label)
             (st : thread_st thread)
             (e  : eventid)
             (e' : option eventid)
             (S S' : ES.t) : Prop := 
    cert_fence_step e e' S S' \/ 
    cert_load_step  st e e' S S' \/ 
    cert_store_step k e e' S S' \/ 
    cert_update_step k st e e' S S'. 

  Definition cert_step 
             (thread : thread_id)
             (k k' : cont_label)
             (st st' : thread_st thread)
             (e  : eventid)
             (e' : option eventid)
             (S S' : ES.t) : Prop := 
    ⟪ CertSTEP_ : cert_step_ k st e e' S S' ⟫ /\
    ⟪ BSTEP_ : ESBasicStep.t_ (thread_lts thread) k k' st st' e e' S S' ⟫. 

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

Section SimRelCertStepProps. 

  Lemma simrel_cert_start S thread
        (SRC : simrel_common prog S G sc TC f)
        (TR_STEP : isim_trav_step G sc thread TC TC') :
    exists k st st',
      ⟪ SRCC : simrel_cert prog S G sc TC TC' f f k st st' ⟫.
  Proof.
    edestruct simrel_cert_graph_start as [k [st' HH]]; eauto.
    desf.
    exists k.

    (* TODO: return the corresponding state in 'simrel_cert_graph_start'. *)
    eexists. 

    exists st'.
    constructor; auto.
    
    (* Ltac narrow_hdom q CsbqDOM := *)
    (*   arewrite (NTid_ (ES.cont_thread S q) ⊆₁ fun _ => True); *)
    (*   rewrite set_inter_full_r; *)
    (*   rewrite CsbqDOM; *)
    (*   rewrite set_unionC; *)
    (*   rewrite <- set_unionA; *)
    (*   rewrite set_unionK; *)
    (*   apply SRC. *)

    all: admit. 

    (* { by narrow_hdom q CsbqDOM. } *)
    (* { admit. } *)
    (* { by narrow_hdom q CsbqDOM. } *)
    (* { by narrow_hdom q CsbqDOM. } *)
    (* { admit. } *)
    (* { apply SRC.(ftid). }  *)
    (* { apply SRC.(flab). } *)
    (* { admit. } *)
    (* { by narrow_hdom q CsbqDOM. }  *)
    (* { admit. } *)
    (* { admit. } *)
    (* { admit. } *)
    (* rewrite CsbqDOM. *)
    (* unfold ES.cc. *)
    (* rewrite <- restr_relE. *)
    (* rewrite restr_inter. *)
    (* rewrite restr_rel_mori. *)
    (* { rewrite (restr_relE _ (Scf S)).  *)
    (*   rewrite SRC.(fimgNcf).  *)
    (*     by rewrite inter_false_l. }  *)
    (* all: basic_solver. *)
  Admitted.

  Lemma simrel_cert_basic_step k lbl lbl' lbls S jf ew co
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
        (ILBL_STEP : ilbl_step (ES.cont_thread S k) lbls st st') 
        (LBLS_EQ : lbls = opt_to_list lbl' ++ [lbl]) :
    exists k' e e' S',
      ⟪ BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S' ⟫ /\
      ⟪ LBL  : lbl  = S'.(ES.lab) e ⟫ /\
      ⟪ LBL' : lbl' = option_map S'.(ES.lab) e' ⟫ /\
      ⟪ JF' : S'.(ES.jf) ≡ jf ⟫ /\
      ⟪ EW' : S'.(ES.ew) ≡ ew ⟫ /\
      ⟪ CO' : S'.(ES.co) ≡ co ⟫.
  Proof.
    assert (tc_coherent G sc TC') as TCCOH'. 
    { eapply isim_trav_step_coherence; apply SRCC. }
    assert ((K S) (k, existT Language.state (thread_lts (ES.cont_thread S k)) st)) as KK.
    { edestruct cstate_q_cont; [apply SRCC|]. desf. }
    assert (wf_thread_state (ES.cont_thread S k) st) as WFST.
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

  Lemma simrel_cert_basic_step_cert_rf k lbl lbl' lbls S
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
        (ILBL_STEP : ilbl_step (ES.cont_thread S k) lbls st st') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'')
        (LBLS_EQ : lbls = opt_to_list lbl' ++ [lbl])
        (RR : exists is_ex ord loc val, ⟪ LBL_LD : lbl = Aload is_ex ord loc val ⟫) :
    exists w,
      ⟪CertDOMw : (cert_dom G TC (ES.cont_thread S k) st) w⟫ /\
      ⟪CertRF : cert_rf G sc TC' (ES.cont_thread S k) 
                        w (ThreadEvent (ES.cont_thread S k) (st.(eindex)))⟫.
  Proof.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert ((K S) (k, existT Language.state (thread_lts (ES.cont_thread S k)) st)) as KK.
    { edestruct cstate_q_cont; [apply SRCC|]. desf. }
    assert (wf_thread_state (ES.cont_thread S k) st) as WFST.
    { by apply SRCC. }
    assert (tc_coherent G sc TC') as TCCOH'.
    { eapply isim_trav_step_coherence; apply SRCC. }
    desc.
    edestruct cert_rf_complete as [w RFwa];
      eauto; try apply SRCC.
    { assert
        (E0 G TC' (ES.cont_thread S k) (ThreadEvent (ES.cont_thread S k) st.(eindex)))
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
    
    assert (cert_dom G TC (ES.cont_thread S k) st w) as HDOMw.
    { eapply cert_rf_cert_dom; try apply SRCC; auto.
      { red. ins. eapply ES.init_tid_K; eauto. }
      unfold dom_rel. eexists.
      apply seq_eqv_r; splits; eauto. }
    assert
      ((h □₁ (cert_dom G TC (ES.cont_thread S k) st)) (h w))
      as hHDOMhw.
    { unfolder; eexists; splits; eauto. }
    
    eexists; econstructor; splits; eauto.
  Qed.

  Lemma simrel_cert_fence_step k lbl S
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
        (ILBL_STEP : ilbl_step (ES.cont_thread S k) [lbl] st st') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'')
        (FF : exists ord, ⟪ LBL_LD : lbl = Afence ord ⟫) :
    exists k' e e' S', 
      ⟪ BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S' ⟫ /\
      ⟪ CertFSTEP  : cert_fence_step e e' S S' ⟫.
  Proof. 
    desf.
    edestruct simrel_cert_basic_step as [k' [e [e' [S' HH]]]]; eauto.
    { erewrite opt_to_list_none. done. }    
    desf. cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor. eauto. }
    assert (SE S' e) as SEe.
    { eapply ESBasicStep.basic_step_acts_set; eauto. 
      basic_solver. }
    assert (SF S' e) as SFe.
    { unfold is_f. by rewrite <- LBL. }
    assert (e' = None) as e'None.
    { ESBasicStep.step_solver. }
    desf; do 5 eexists; splits; eauto.
    econstructor; splits; eauto.
  Qed.

  Lemma simrel_cert_load_step k lbl S
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
        (ILBL_STEP : ilbl_step (ES.cont_thread S k) [lbl] st st') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'')
        (RR : exists is_ex ord loc val, ⟪ LBL_LD : lbl = Aload is_ex ord loc val ⟫) :
    exists k' e e' S', 
      ⟪ BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S' ⟫ /\
      ⟪ CertLdSTEP  : cert_load_step st e e' S S' ⟫. 
  Proof. 
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    edestruct simrel_cert_basic_step_cert_rf
      as [w HA]; eauto 10.
    { erewrite opt_to_list_none. done. } 
    edestruct simrel_cert_basic_step as [k' [e [e' [S' HB]]]]; eauto.
    { erewrite opt_to_list_none. done. }    
    desf. cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor. eauto. }
    assert (SE S' e) as SEe.
    { eapply ESBasicStep.basic_step_acts_set; eauto. 
      basic_solver. }
    assert (SR S' e) as SRe.
    { unfold is_r. by rewrite <- LBL. }
    assert (e' = None) as e'None.
    { ESBasicStep.step_solver. }
    desf; do 5 eexists; splits; eauto.
    desc. exists (h w). 
    splits; eauto.
    econstructor; splits; eauto.
    { basic_solver. }
    erewrite basic_step_e2a_eq_dom; eauto. 
    2 : { eapply a2e_img; [apply SRCC.(sr_a2e_h)|]. basic_solver. } 
    erewrite basic_step_e2a_e
      with (S' := S'); eauto; try apply SRCC.
    arewrite (e2a S (h w) = w); auto.
    eapply a2e_fix; [apply SRCC.(sr_a2e_h)|]. basic_solver. 
  Qed.

  Lemma simrel_cert_store_step k lbl S
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
        (ILBL_STEP : ilbl_step (ES.cont_thread S k) [lbl] st st') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'')
        (WW : exists ord loc val, ⟪ LBL_ST : lbl = Astore Xpln ord loc val ⟫) :
    exists k' e e' S', 
      ⟪ BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S' ⟫ /\
      ⟪ CertStSTEP  : cert_store_step k e e' S S' ⟫.
  Proof. 
    desf.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    edestruct simrel_cert_basic_step as [k' [e [e' [S' HH]]]]; eauto.
    { erewrite opt_to_list_none. done. }    
    desf. cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor. eauto. }
    assert (SE S' e) as SEe.
    { eapply ESBasicStep.basic_step_acts_set; eauto. 
      basic_solver. }
    assert (SW S' e) as SWe.
    { unfold is_w. by rewrite <- LBL. }
    assert (e' = None) as e'None.
    { ESBasicStep.step_solver. }
    desf; do 5 eexists; splits; eauto.
    econstructor; splits; eauto.
    all : econstructor; splits; eauto.   
    { unfold ESstep.ew_delta, sim_ews. 
      erewrite basic_step_e2a_e with (e := ES.next_act S); 
        eauto; try apply SRCC. }
    unfold ESstep.co_delta.
    (* erewrite ESstep.basic_step_co_ws_alt; eauto. *)
    (* 2 : basic_solver. *)
    (* rewrite <- LBL. *)
    unfold sim_ews, sim_ws.
    erewrite basic_step_e2a_e with (e := ES.next_act S); 
        eauto; try apply SRCC.
  Qed.

  Lemma simrel_cert_update_step k lbl lbl' lbls S
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
        (ILBL_STEP : ilbl_step (ES.cont_thread S k) lbls st st') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'')
        (LBLS_EQ : lbls = opt_to_list lbl' ++ [lbl])
        (RR : exists is_ex ord loc val, ⟪ LBL_LD : lbl = Aload is_ex ord loc val ⟫) 
        (WW : exists xmod ord loc val, ⟪ LBL_ST : lbl' = Some (Astore xmod ord loc val) ⟫) :
    exists k' e e' S', 
      ⟪ BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S' ⟫ /\
      ⟪ CertUpdSTEP  : cert_update_step k st e e' S S' ⟫. 
  Proof. 
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    desc. 
    edestruct simrel_cert_basic_step_cert_rf
      as [w HA]; eauto 10.
    edestruct simrel_cert_basic_step as [k' [e [e' [S' HB]]]]; eauto.
    desf. cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor. eauto. }
    destruct e' as [e'|].
    2 : { unfold opt_same_ctor in *. desf. }
    assert (SE S' e) as SEe.
    { eapply ESBasicStep.basic_step_acts_set; eauto. 
      basic_solver. }
    assert (SR S' e) as SRe.
    { unfold is_r. by rewrite <- LBL. }
    assert (SE S' e') as SEe'.
    { eapply ESBasicStep.basic_step_acts_set; eauto. 
      basic_solver. }
    unfold option_map in LBL'. 
    inversion LBL' as [[LBL'']].
    assert (SW S' e') as SWe'.
    { unfold is_w. by rewrite <- LBL''. }
    unfold opt_ext in *. desc.
    desf; do 5 eexists; splits; eauto. 
    exists (h w). eexists.
    splits; eauto.
    { econstructor; splits; eauto.
      { basic_solver. }
      erewrite basic_step_e2a_eq_dom; eauto. 
      2 : { eapply a2e_img; [apply SRCC.(sr_a2e_h)|]. basic_solver. } 
      erewrite basic_step_e2a_e
        with (S' := S'); eauto; try apply SRCC.
      arewrite (e2a S (h w) = w); auto.
      eapply a2e_fix; [apply SRCC.(sr_a2e_h)|]. basic_solver. }
    all : econstructor; splits; eauto.   
    { unfold ESstep.ew_delta, sim_ews. 
      erewrite basic_step_e2a_e' with (e' := 1 + ES.next_act S); 
        eauto; try apply SRCC. }
    unfold ESstep.co_delta.
    (* erewrite ESstep.basic_step_co_ws_alt; eauto. *)
    (* 2 : basic_solver. *)
    (* rewrite <- LBL''. *)
    unfold sim_ews, sim_ws.
    erewrite basic_step_e2a_e' with (e' := 1+ ES.next_act S); 
      eauto; try apply SRCC.
  Qed.

  Lemma simrel_cert_step k lbls S
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
        (ILBL_STEP : ilbl_step (ES.cont_thread S k) lbls st st') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    exists k' e e' S', ⟪ CertSTEP : cert_step k k' st st' e e' S S' ⟫. 
  Proof. 
    edestruct lbl_step_cases as [lbl [lbl' HH]]; eauto.
    { apply SRCC. edestruct cstate_q_cont; [apply SRCC|]. desf. }
    desf.
    1-4 : rewrite opt_to_list_none in ILBL_STEP.
    { edestruct simrel_cert_load_step 
        as [k' [e [e' [S' HH]]]]; eauto 10.
      desf. unfold cert_step, cert_step_. eauto 20. }
    { edestruct simrel_cert_load_step 
        as [k' [e [e' [S' HH]]]]; eauto 10.
      desf. unfold cert_step, cert_step_. eauto 20. }
    { edestruct simrel_cert_store_step 
        as [k' [e [e' [S' HH]]]]; eauto 10.
      desf. unfold cert_step, cert_step_. eauto 20. }
    { edestruct simrel_cert_fence_step 
        as [k' [e [e' [S' HH]]]]; eauto 10.
      desf. unfold cert_step, cert_step_. eauto 20. }
    edestruct simrel_cert_update_step 
      as [k' [e [e' [S' HH]]]]; eauto 10.
    desf. unfold cert_step, cert_step_. eauto 20.
  Qed.
  
  Lemma simrel_cert_step_step_ k k' e e' S S'
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
        (CertSTEP : cert_step k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :
    ESstep.t_ e e' S S'. 
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

  Lemma simrel_cert_step_e2a k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
        (CertSTEP : cert_step k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    simrel_e2a S' G sc.  
  Proof. 
    cdes CertSTEP; cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor. eauto. }
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (sim_trav_step G sc TC TC') as TCSTEP.
    { red. eexists. eapply tr_step; eauto. }
    assert (tc_coherent G sc TC') as TCCOH'.
    { eapply sim_trav_step_coherence; eauto. apply SRCC. }
    
    constructor.

    (* e2a_GE : e2a □₁ SE ⊆₁ GE *)
    { rewrite ESBasicStep.basic_step_acts_set; eauto.  
      rewrite !set_collect_union. 
      rewrite !set_subset_union_l.
      splits. 
      { erewrite set_collect_eq_dom; [eapply SRCC|].
        eapply basic_step_e2a_eq_dom; eauto. } 
      { rewrite set_collect_eq.
        apply eq_predicate. 
        eapply basic_step_e2a_GE_e; eauto; apply SRCC. }
      destruct e' as [e'|]; [|basic_solver]. 
      unfold eq_opt. 
      rewrite set_collect_eq.
      apply eq_predicate. 
      eapply basic_step_e2a_GE_e'; eauto; apply SRCC. }
    (* e2a_GEinit : GEinit ⊆₁ g □₁ SEinit *)
    { etransitivity. 
      { eapply e2a_GEinit. apply SRCC. }
      erewrite ESBasicStep.basic_step_acts_init_set with (S' := S'); eauto.  
      eapply set_collect_eq_dom.
      unfold ES.acts_init_set.
      unfolder. ins. desf.
      eapply basic_step_e2a_eq_dom; eauto. }
    (* e2a_lab : same_lab_u2v_dom SE Slab (Glab ∘ e2a) *)
    { eapply basic_step_e2a_same_lab_u2v; eauto; 
        try apply SRCC; apply BSTEP_. }
    (* e2a_rmw : e2a □ Srmw ⊆ Grmw *)
    { unfold_cert_step_ CertSTEP_.
      1-3 : 
        eapply simrel_cert_basic_step_e2a_eqr;
        try eapply ESBasicStep.basic_step_nupd_rmw; 
        try apply ES.rmwE; subst e'; eauto;
        apply SRCC.
      rewrite RMW'. 
      unfold ESBasicStep.rmw_delta.
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
      edestruct cstate_q_cont; [apply SRCC|]. desc.
      edestruct lbl_step_cases as [l [l' HH]].
      { eapply wf_cont_state; eauto. }
      { apply STEP. }
      destruct HH as [EE HH].
      apply opt_to_list_app_singl in EE.
      unfold opt_same_ctor in *. desf.
      rewrite GRMW.
      erewrite basic_step_e2a_e; eauto; try apply SRCC.
      erewrite basic_step_e2a_e'; eauto; try apply SRCC.
      basic_solver. }
    (* e2a_jf : e2a □ Sjf  ⊆ Gvf *)
    { unfold_cert_step_ CertSTEP_.
      1,3 : 
        eapply simrel_cert_basic_step_e2a_eqr; eauto;
        try apply ES.jfE; apply SRCC.
      all : eapply sim_add_jf_e2a_jf_vf; eauto. }
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
    (* e2a_rf_rmw : e2a □ (Srf ⨾ Srmw) ⊆ Grf ⨾ Grmw *)
    assert (Sjf S ⨾ Srmw S ≡ ⦗ SE S ⦘ ⨾ (Sjf S ⨾ Srmw S) ⨾ ⦗ SE S ⦘) 
      as jf_rmwE.
    { rewrite ES.jfE, ES.rmwE; auto. basic_solver 10. }
    unfold_cert_step_ CertSTEP_.
    { rewrite JF'. 
      rewrite ESBasicStep.basic_step_nupd_rmw.
      2 : { subst e'; eauto. }
      eapply simrel_cert_basic_step_e2a_eqr; eauto; apply SRCC. }
    { cdes AJF.
      rewrite JF'. 
      rewrite ESBasicStep.basic_step_nupd_rmw.
      2 : { subst e'; eauto. }
      rewrite seq_union_l.
      arewrite_false (ESstep.jf_delta w e ⨾ Srmw S).
      { ESBasicStep.step_solver. }
      relsf.
      eapply simrel_cert_basic_step_e2a_eqr; eauto; apply SRCC. }
    { rewrite JF'. 
      rewrite ESBasicStep.basic_step_nupd_rmw.
      2 : { subst e'; eauto. }
      eapply simrel_cert_basic_step_e2a_eqr; eauto; apply SRCC. }
    admit. 
  Admitted.

  Lemma simrel_cert_step_hb_delta_dom k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
        (CertSTEP : cert_step k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    dom_rel (ESstep.hb_delta S S' k e e') ⊆₁ 
            h □₁ cert_dom G TC (ES.cont_thread S k) st ∪₁ eq e. 
  Proof. 
    cdes CertSTEP; cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ESstep.t_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    unfold ESstep.hb_delta. relsf. split. 
    { rewrite <- seqA, dom_seq.
      eapply simrel_cert_basic_step_hb_sb_delta_dom; eauto. }
    unfold_cert_step_ CertSTEP_.
    all : rewrite <- seqA, dom_seq.
    2,4 : left; eapply sim_add_jf_hb_sw_delta_dom; eauto. 
    all : unfold ESstep.sw_delta.
    all : rewrite JF'; relsf; rewrite !seqA; splits.
    2,4 : ESBasicStep.step_solver.
    all : do 3 rewrite <- seqA; rewrite dom_seq, !seqA.
    all : left; eapply simrel_cert_basic_step_hb_rel_jf_sb_delta_dom; eauto.
  Qed.

  Lemma simrel_cert_step_hb_cf_irr k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')
        (CertSTEP : cert_step k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    irreflexive (Shb S' ⨾ Scf S').
  Proof.
    cdes CertSTEP; cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ESstep.t_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    erewrite ESstep.step_hb; eauto.
    erewrite ESBasicStep.basic_step_cf; eauto.
    relsf. rewrite !irreflexive_union. splits.

    { eapply ecf_irr_hb_cf_irr. apply SRCC. }

    { ESBasicStep.step_solver. } 

    { autounfold with ESStepDb.
      rewrite !csE, !transp_cross.
      relsf. rewrite !irreflexive_union. splits.
      2,4 : by ESBasicStep.step_solver.
      { intros x [y [HB [KCF EQe]]].
        subst x. apply hbE, seq_eqv_lr in HB; auto. desf.
        eapply ESBasicStep.basic_step_acts_set_ne; eauto. }
      unfold eq_opt. destruct e' as [e'|]; [|basic_solver].
      intros x [y [HB [KCF EQOPTe]]].
      subst x. apply hbE, seq_eqv_lr in HB; auto. desf.
      eapply ESBasicStep.basic_step_acts_set_ne'; eauto. }

    unfold ESBasicStep.cf_delta.
    rewrite !csE, !transp_cross. relsf.
    arewrite_false (ESstep.hb_delta S S' k e e' ⨾ ES.cont_cf_dom S k × eq e).
    { ESBasicStep.step_solver. }
    arewrite_false (ESstep.hb_delta S S' k e e' ⨾ ES.cont_cf_dom S k × eq_opt e'). 
    { ESBasicStep.step_solver. }
    relsf.

    erewrite dom_rel_helper with (r := ESstep.hb_delta S S' k e e').
    2 : { eapply simrel_cert_step_hb_delta_dom; eauto. }
    rewrite id_union. 
    relsf. rewrite !irreflexive_union. splits.
    all : try by ESBasicStep.step_solver.
    all : unfolder; ins; desc. 
    all : eapply cfk_hdom; eauto.
    all : basic_solver.
  Qed.

  Lemma simrel_cert_step_thb_cf_hb_irr k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')
        (CertSTEP : cert_step k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    irreflexive ((Shb S')⁻¹ ⨾ (Scf S') ⨾ (Shb S')).
  Proof.
    cdes CertSTEP; cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ESstep.t_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    erewrite ESstep.step_hb; eauto.
    erewrite ESBasicStep.basic_step_cf; eauto.
    unfold ESBasicStep.cf_delta.
    erewrite dom_rel_helper with (r := ESstep.hb_delta S S' k e e').
    2 : { eapply simrel_cert_step_hb_delta_dom; eauto. }
    rewrite !transp_union.
    relsf. rewrite !irreflexive_union. splits.

    { eapply ecf_irr_thb_cf_hb_irr. apply SRCC. }

    1-8 : ESBasicStep.step_solver.

    all : rewrite !id_union, !transp_seq, !transp_union, !transp_eqv_rel. 
    all : relsf; rewrite !seqA.

    { arewrite_false (Scf S ⨾ ⦗eq e⦘).
      { ESBasicStep.step_solver. }
      arewrite_false (⦗eq e⦘ ⨾ Scf S).
      { ESBasicStep.step_solver. }
      relsf. 
      unfolder. ins. desc. subst.
      eapply a2e_ncf.
      { apply SRCC.(sr_a2e_h). }
      unfolder. eauto 20. }

    { erewrite a2e_img with (a2e := h) at 1 2.
      2 : { apply SRCC.(sr_a2e_h). }
      arewrite_false 
        (⦗SE S⦘ ⨾ (ES.cont_cf_dom S k × eq e) ^⋈ ⨾ ⦗SE S⦘).
      { ESBasicStep.step_solver. }
      arewrite_false 
        (⦗eq e⦘ ⨾ (ES.cont_cf_dom S k × eq e) ^⋈ ⨾ ⦗eq e⦘).
      { ESBasicStep.step_solver. }
      relsf.

      rewrite !csE. relsf.
      arewrite_false (eq e × ES.cont_cf_dom S k ⨾ ⦗eq e⦘).
      { ESBasicStep.step_solver. }
      arewrite_false (⦗eq e⦘ ⨾ ES.cont_cf_dom S k × eq e).
      { ESBasicStep.step_solver. }
      relsf. rewrite !irreflexive_union. splits.
      all : unfolder; ins; desc; subst.
      all : eapply cfk_hdom; eauto.
      all : basic_solver. }

    erewrite a2e_img with (a2e := h).
    2 : { apply SRCC.(sr_a2e_h). }
    arewrite_false 
      (⦗SE S⦘ ⨾ (ES.cont_cf_dom S k × eq_opt e') ^⋈ ⨾ ⦗SE S⦘).
    { ESBasicStep.step_solver. }
    arewrite_false 
      (⦗SE S⦘ ⨾ (ES.cont_cf_dom S k × eq_opt e') ^⋈ ⨾ ⦗eq e⦘).
    { ESBasicStep.step_solver. }
    arewrite_false 
      (⦗eq e⦘ ⨾ (ES.cont_cf_dom S k × eq_opt e') ^⋈ ⨾ ⦗SE S⦘).
    { ESBasicStep.step_solver. }
    arewrite_false 
      (⦗eq e⦘ ⨾ (ES.cont_cf_dom S k × eq_opt e') ^⋈ ⨾ ⦗eq e⦘).
    { ESBasicStep.step_solver. }
    basic_solver.
  Qed.

  Lemma simrel_cert_step_jf_necf k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')
        (CertSTEP : cert_step k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    Sjf S' ∩ Secf S' ≡ ∅₂. 
  Proof. 
    cdes CertSTEP; cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ESstep.t_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    unfold_cert_step_ CertSTEP_.
    1,3 : 
      eapply ESstep.step_same_jf_jf_necf; 
      eauto; try apply SRCC;
      eapply ESBasicStep.basic_step_nupd_rmw;
      subst; eauto.
    { eapply sim_add_jf_jf_necf; eauto.
      subst. basic_solver. }
    eapply sim_add_jf_jf_necf; eauto.
    cdes AEW. type_solver.
  Qed.

  Lemma simrel_cert_step_jfe_vis k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')
        (CertSTEP : cert_step k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    dom_rel (Sjfe S') ⊆₁ (vis S'). 
  Proof. 
    cdes CertSTEP; cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ESstep.t_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WFS by apply SRCC.
    etransitivity. 
    2 : eapply ESstep.step_vis_mon; eauto.
    unfold_cert_step_ CertSTEP_.
    all : try (by eapply sim_add_jf_jfe_vis; eauto).
    all : rewrite ESstep.step_same_jf_jfe; eauto; apply SRCC.
  Qed.

  Lemma simrel_cert_step_fr_coh k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')
        (CertSTEP : cert_step k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    irreflexive (Shb S' ⨾ ES.fr S' ⨾ (Srf S')^?).
  Proof. 
    cdes CertSTEP; cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ESstep.t_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WF by apply SRCC.
    assert (ES.Wf S') as WFS.
    { eapply step_wf; eauto. }
    assert (simrel_e2a S' G sc) as SRE2A.
    { admit. }
    assert 
      (simrel_a2e S' (upd_a2e h e e' S') (cert_dom G TC (ES.cont_thread S' k') st')) 
      as SRA2E.
    { admit. }
    assert (Wf G) as WFG. 
    { apply SRCC. }
    assert (coherence G) as GCOH.
    { eapply gcons. apply SRCC. }
    assert (Scf S ⊆ Scf S') as SCFB.
    { admit. }

    unfold ES.fr.
    do 2 (rewrite <- !seqA; apply irreflexive_seqC).

    eapply collect_rel_irr with (f := e2a S').
    rewrite !collect_rel_seqi.
    erewrite e2a_hb; eauto; try apply SRCC.
    erewrite e2a_co; eauto.
    rewrite collect_rel_cr.
    (* TODO: introduce a corresponding lemma. *)
    arewrite (e2a S' □ (Srf S')⁻¹ ⊆ (e2a S' □ Srf S')⁻¹).
    { unfolder. basic_solver 10. }
    erewrite e2a_rf at 1; eauto.
    erewrite e2a_jf; eauto.
    rewrite (dom_r WFG.(wf_coD)). rewrite !seqA.
    arewrite (⦗GW⦘ ⨾ (Gvf sc)^? ⨾ Ghb ⊆ Gvf sc).
    { rewrite furr_alt.
      2: by apply SRCC.
      generalize (@imm_s_hb.hb_trans G). basic_solver 40. }

    (* red in CertSTEP_. desf. cdes CertSTEP_. *)

    (* { unfold ES.fr. rewrite !collect_rel_seqi. *)
    (*   rewrite e2a_co; eauto. *)
    (*   red in CertSTEP_. desf; cdes CertSTEP_. *)
    (*   { arewrite (Srf S' ⊆ Srf S). *)
    (*     { unfold ES.rf. by rewrite JF', EW', SCFB. } *)
    (*     arewrite (e2a S' □ Srf S ⊆ e2a S □ Srf S). *)
    (*     { admit. } *)



    (*   admit. } *)
    (* unfold ES.fr. rewrite !collect_rel_seqi. *)
    (* rewrite e2a_co; eauto. *)
    (* (* TODO: introduce a corresponding lemma. *) *)
    (* arewrite (e2a S' □ (Srf S')⁻¹ ⊆ (e2a S' □ Srf S')⁻¹). *)
    (* { unfolder. basic_solver 10. } *)
    (* admit. *)
  Admitted.

  Lemma simrel_cert_step_coh k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')
        (CertSTEP : cert_step k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    irreflexive (Shb S' ⨾ (Seco S')^?).
  Proof. 
    cdes CertSTEP; cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ESstep.t_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WF by apply SRCC.
    assert (ES.Wf S') as WFS.
    { eapply step_wf; eauto. }
    assert (simrel_e2a S' G sc) as SRE2A.
    { admit. }
    assert 
      (simrel_a2e S' (upd_a2e h e e' S') (cert_dom G TC (ES.cont_thread S' k') st')) 
      as SRA2E.
    { admit. }
    assert (Wf G) as WFG. 
    { apply SRCC. }
    assert (coherence G) as GCOH.
    { eapply gcons. apply SRCC. }
    
    rewrite crE. rewrite eco_alt; auto.
    rewrite crE at 1.
    rewrite !seq_union_r, !seq_id_r.
    rewrite <- !unionA.
    apply irreflexive_union. splits.
    2: by eapply simrel_cert_step_fr_coh; eauto.
    eapply collect_rel_irr with (f := e2a S').
    rewrite !collect_rel_union.
    rewrite !collect_rel_seqi.
    erewrite e2a_hb; eauto; try apply SRCC.
    erewrite e2a_co; eauto.
    rewrite !irreflexive_union. splits.
    { apply hb_irr; auto. }
    { erewrite e2a_rf, e2a_jf; eauto.
      intros x [y [HB VF]].
      unfold furr in VF. desc.  
      eapply urr_hb_irr; try apply SRCC.
      basic_solver. }
    { arewrite (Gco ⊆ Geco^?).
      2: by apply GCOH.
      rewrite Execution_eco.co_in_eco. basic_solver. }
    erewrite e2a_rf, e2a_jf; eauto.
    intros x [y [HB [z [CO VF]]]].
    unfold furr in VF. desc.  
    eapply eco_urr_irr; try apply SRCC.
    eexists. splits.
    { unfold Execution_eco.eco. basic_solver 10. }
    eapply urr_hb. basic_solver.
  Admitted.

  Lemma simrel_cert_step_consistent k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')
        (CertSTEP : cert_step k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    @es_consistent S' Weakestmo. 
  Proof. 
    cdes CertSTEP; cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    constructor.
    { eapply ecf_irr_alt. split.
      { eapply simrel_cert_step_hb_cf_irr; eauto. }
      eapply simrel_cert_step_thb_cf_hb_irr; eauto. }
    { eapply simrel_cert_step_jf_necf; eauto. }
    { eapply simrel_cert_step_jfe_vis; eauto. }
    { admit. }
    { admit. }
    admit. 
  Admitted.

  Lemma simrel_cert_lbl_step k S
        (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')
        (LBL_STEP : lbl_step (ES.cont_thread S k) st st')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :
    exists h' k' S',
      ⟪ ESSTEP : (ESstep.t Weakestmo)^? S S' ⟫ /\
      ⟪ SRCC' : simrel_cert prog S' G sc TC TC' f h' k' st' st''⟫.
  Proof.
    edestruct LBL_STEP as [lbl ILBL_STEP].
    edestruct simrel_cert_step as [k' HH]; eauto. desc.
    cdes CertSTEP.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ESstep.t_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    set (h' := upd_opt (upd h (e2a S' e) e) (option_map (e2a S') e') e'). 
    exists h', k', S'. splits.
    { apply r_step. red.
      do 2 eexists; splits; eauto.
      eapply simrel_cert_step_consistent; eauto. }
    constructor.
    { constructor; try apply SRCC.
      { admit. }
      { eapply simrel_cert_step_consistent; eauto. }
      { eapply basic_step_simrel_cont; eauto; apply SRCC. }
      { eapply simrel_cert_step_e2a; eauto. }
      { eapply basic_step_simrel_a2e_preserved; eauto; apply SRCC. }
      (* flab : eq_dom (C ∪₁ I) (Slab ∘ f) Glab *)
      { unfold eq_dom, compose. ins. 
        erewrite ESBasicStep.basic_step_lab_eq_dom; eauto.
        { by apply SRCC. }
        eapply a2e_img; [apply SRCC|].
        unfolder; eexists; split; eauto.
        destruct SX as [Cx | Ix]; [by left|].
        right. do 2 eexists. splits; eauto. }
      (* fvis : f □₁ fdom ⊆₁ vis S *)
      { etransitivity.
        { eapply fvis. apply SRCC. }
        eapply ESstep.step_vis_mon; eauto. }
      (* finitIncl : SEinit ⊆₁ f □₁ GEinit *)
      { erewrite ESBasicStep.basic_step_acts_init_set; eauto. apply SRCC. } 
      (* fD_rfc : (f □₁ fdom) ∩₁ SR ⊆₁ codom_rel (⦗ f □₁ fdom ⦘ ⨾ Srf) *)
      { admit. }
      (* jfe_fI : dom_rel Sjfe ⊆₁ dom_rel (Sew^? ⨾ ⦗ f □₁ I ⦘) *)
      { etransitivity. 
        { unfold_cert_step_ CertSTEP_.
          2,4 : eapply sim_add_jf_jfe_fI; eauto.
          all : erewrite ESstep.step_same_jf_jfe; 
                eauto; apply SRCC. }
        erewrite ESstep.step_ew_mon; eauto. }
      (* ew_fI  : dom_rel Sew  ⊆₁ dom_rel (Sew^? ⨾ ⦗ f □₁ I ⦘) *)
      { unfold_cert_step_ CertSTEP_.
        1,2 : rewrite EW'; apply SRCC.
        all : eapply sim_add_ew_ew_fI; eauto.
        all : basic_solver. }
      (* dom_rel (Srelease ⨾ Sew^? ⨾ ⦗ f □₁ I ⦘) ⊆₁ f □₁ C *)
      admit. }
    (* cert : cert_graph G sc TC TC' (ES.cont_thread S k') state'' *)
    { erewrite ESBasicStep.basic_step_cont_thread_k; eauto. apply SRCC. }
    (* cstate : simrel_cstate *)
    { eapply basic_step_simrel_cstate; eauto. } 
    (* tr_step : isim_trav_step G sc (ES.cont_thread S k') TC TC' *)
    { erewrite ESBasicStep.basic_step_cont_thread_k; eauto. apply SRCC. }
    { admit. }
    (* sr_a2e_h *)
    { eapply basic_step_simrel_a2e; eauto. }
    (* hlab : eq_dom (C ∪₁ I ∪₁ contE) (Slab ∘ h) certLab; *)
    { admit. }
    (* hfeq : eq_dom (C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘) ∩₁ GNTid qtid)) f h; *)
    { subst h'. 
      red. ins.
      erewrite ESBasicStep.basic_step_cont_thread_k in SX; eauto.
      rewrite updo_opt.
      { rewrite updo.
        { eapply hfeq; eauto. }
        red. ins. subst x.
        eapply basic_step_cert_dom_ne; 
          eauto; try apply SRCC.
        unfold cert_dom. by left. }
      { destruct e' as [e'|]; auto.
        unfold eq_opt, option_map.
        red. ins. subst x.
        eapply basic_step_cert_dom_ne'; 
          eauto; try apply SRCC.
        unfold cert_dom. by left. }
        by destruct e'. }
    (* hrel_iss_cov : dom_rel (Srelease ⨾ Sew^? ⨾ ⦗ h □₁ I ⦘) ⊆₁ h □₁ C *)
    admit. 
  Admitted.
        
      (* assert (g' □ Ssb S' ⊆ Gsb) as SSB. *)
      (* { admit. } *)
      (* assert (g □ Shb S ⊆ Ghb) as SHB. *)
      (* { (* We need a lemma stating that. *) *)
      (*   admit. } *)
      (* assert (g' □ Shb S ⊆ Ghb) as SHB'. *)
      (* { admit. } *)
      (* assert (ES.cont_sb_dom S k × eq e ⊆ S'.(ES.sb)) as SBDSB. *)
      (* { admit. } *)
      (* assert (g' □ S'.(hb) ⊆ Ghb) as BHB. *)
      (* { erewrite ESstep.load_step_hb; eauto. *)
      (*   rewrite collect_rel_union. *)
      (*   unionL; auto. *)
      (*   rewrite collect_rel_seqi. *)
      (*   etransitivity. *)
      (*   2: { apply rewrite_trans_seq_cr_l. *)
      (*        apply imm_s_hb.hb_trans. } *)
      (*   apply seq_mori. *)
      (*   { by rewrite collect_rel_cr, SHB'. } *)
      (*   rewrite collect_rel_union. *)
      (*   unionL. *)
      (*   { rewrite SBDSB. *)
      (*     etransitivity; eauto. *)
      (*     apply imm_s_hb.sb_in_hb. } *)
      (*   admit. } *)
      
End SimRelCertStepProps.

End SimRelCertStep.