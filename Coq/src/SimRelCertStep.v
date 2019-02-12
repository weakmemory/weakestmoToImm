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
        SimRelCont SimRelEventToAction SimRelSubExec
        SimRel SimRelCert SimRelCertBasicStep SimRelAddJF SimRelAddEW SimRelAddCO.  

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

  Definition cert_step_fence
             (e  : eventid)
             (e' : option eventid)
             (S S' : ES.t) : Prop :=
    ⟪ ENONE : e' = None ⟫ /\
    ⟪ FF  : SF S' e ⟫ /\
    ⟪ JF' : Sjf S' ≡ Sjf S ⟫ /\
    ⟪ EW' : Sew S' ≡ Sew S ⟫ /\
    ⟪ CO' : Sco S' ≡ Sco S ⟫.

  Definition cert_step_load
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

  Definition cert_step_store
             (thread : thread_id)
             (st : thread_st thread)
             (e  : eventid)
             (e' : option eventid)
             (S S' : ES.t) : Prop :=
    exists ws w,
      ⟪ ENONE : e' = None ⟫ /\
      ⟪ JF' : Sjf S' ≡ Sjf S ⟫ /\ 
      ⟪ AEW : sim_add_ew TC f ws e S S' ⟫ /\
      ⟪ ACO : sim_add_co G w e S S' ⟫.

  Definition cert_step_update
             (thread : thread_id)
             (st : thread_st thread)
             (e  : eventid)
             (e' : option eventid)
             (S S' : ES.t) : Prop := 
    exists rw ws ww w',
      ⟪ ESOME : e' = Some w' ⟫ /\ 
      ⟪ AJF : sim_add_jf G sc TC TC' h thread st rw e S S' ⟫ /\ 
      ⟪ AEW : sim_add_ew TC f ws w' S S' ⟫ /\
      ⟪ ACO : sim_add_co G ww w' S S' ⟫.

  Definition cert_step_ 
             (thread : thread_id)
             (st : thread_st thread)
             (e  : eventid)
             (e' : option eventid)
             (S S' : ES.t) : Prop := 
    cert_step_fence e e' S S' \/ 
    cert_step_load  st e e' S S' \/ 
    cert_step_store st e e' S S' \/ 
    cert_step_update st e e' S S'. 

  Definition cert_step 
             (e  : eventid)
             (e' : option eventid)
             (S S' : ES.t) : Prop := 
    exists k k' (st st' : thread_st (ES.cont_thread S k)),  
      ⟪ CertTT : cert_step_ st e e' S S' ⟫ /\
      ⟪ BSTEP : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S' ⟫. 

  Ltac unfold_cert_step H := 
    unfold cert_step, cert_step_, 
           cert_step_fence, cert_step_load, cert_step_store, cert_step_update 
      in H; destruct H as [HA | [HB | [HC | HD]]]; desc.

Section SimRelCertStepProps. 

  Lemma simrel_cert_start S thread
        (SRC : simrel_common prog S G sc TC f)
        (TR_STEP : isim_trav_step G sc thread TC TC') :
    exists k st st',
      ⟪ SRCC : simrel_cert prog S G sc TC f TC' f k st st' ⟫.
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

  Lemma simrel_cert_step_step_ k k' e e' S S'
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
        (CertSTEP_ : cert_step_ st e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :
    ESstep.t_ e e' S S'. 
  Proof. 
    unfold ESstep.t_.
    unfold_cert_step CertSTEP_.
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

  Lemma simrel_cert_step_e2a_eqr k k' e e' S S' r r' r''
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e e' S S') 
        (restrE : r ≡ ⦗ SE S ⦘ ⨾ r ⨾ ⦗ SE S ⦘)
        (rEQ : r' ≡ r) 
        (rIN : (e2a S) □ r ⊆ r'') : 
    (e2a S') □ r' ⊆ r''.
  Proof. 
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor. eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    rewrite rEQ, restrE, collect_rel_eq_dom.
    { rewrite <- restrE; eauto. }
    all: eapply basic_step_e2a_eq_dom; eauto. 
  Qed.

  Lemma simrel_cert_step_e2a k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
        (CertSTEP_ : cert_step_ st e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    simrel_e2a S' G sc.  
  Proof. 
    cdes BSTEP_.
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
    { unfold_cert_step CertSTEP_.
      1-3 : 
        eapply simrel_cert_step_e2a_eqr;
        try eapply ESBasicStep.basic_step_nupd_rmw; 
        try apply ES.rmwE; subst e'; eauto;
        apply SRCC.
      rewrite RMW'. 
      unfold ESBasicStep.rmw_delta.
      rewrite collect_rel_union. 
      unionL.
      { eapply simrel_cert_step_e2a_eqr; eauto.
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
    (* e2a_jf  : e2a □ Sjf  ⊆ Gvf *)
    { unfold_cert_step CertSTEP_.
      1,3 : 
        eapply simrel_cert_step_e2a_eqr; eauto;
        try apply ES.jfE; apply SRCC.
      all : admit. }
    (* e2a_ew  : e2a □ Sew  ⊆ ⦗I⦘ *)
    { unfold_cert_step CertSTEP_.
      1,2 : 
        eapply simrel_cert_step_e2a_eqr; eauto;
        try apply ES.ewE; apply SRCC.
      all : admit. }
    (* e2a_co  : e2a □ Sco  ⊆ Gco *)
    { unfold_cert_step CertSTEP_.
      1,2 : 
        eapply simrel_cert_step_e2a_eqr; eauto;
        try apply ES.coE; apply SRCC.
      all : admit. }
    (* e2a_rf_rmw : e2a □ (Srf ⨾ Srmw) ⊆ Grf ⨾ Grmw *)
    assert (Sjf S ⨾ Srmw S ≡ ⦗ SE S ⦘ ⨾ (Sjf S ⨾ Srmw S) ⨾ ⦗ SE S ⦘) 
      as jf_rmwE.
    { rewrite ES.jfE, ES.rmwE; auto. basic_solver 10. }
    unfold_cert_step CertSTEP_.
    { rewrite JF'. 
      rewrite ESBasicStep.basic_step_nupd_rmw.
      2 : { subst e'; eauto. }
      eapply simrel_cert_step_e2a_eqr; eauto; apply SRCC. }
    { cdes AJF.
      rewrite JF'. 
      rewrite ESBasicStep.basic_step_nupd_rmw.
      2 : { subst e'; eauto. }
      rewrite seq_union_l.
      arewrite_false (ESstep.jf_delta w e ⨾ Srmw S).
      { ESBasicStep.step_solver. }
      relsf.
      eapply simrel_cert_step_e2a_eqr; eauto; apply SRCC. }
    { rewrite JF'. 
      rewrite ESBasicStep.basic_step_nupd_rmw.
      2 : { subst e'; eauto. }
      eapply simrel_cert_step_e2a_eqr; eauto; apply SRCC. }
    admit. 
  Admitted.
    
    (* e2a_jf  : e2a □ Sjf  ⊆ Gvf *)
    (* { rewrite SSJF', collect_rel_union.  *)
    (*   unionL.  *)
    (*   { rewrite ES.jfE; auto.  *)
    (*     erewrite collect_rel_eq_dom. *)
    (*     { rewrite <- ES.jfE; auto.  *)
    (*       eapply SRCC. } *)
    (*     all: eapply basic_step_e2a_eq_dom; eauto. } *)
    (*   rewrite collect_rel_singl.  *)
    (*   unfolder; ins; desf. *)
    (*   eapply vf_in_furr; [by apply SRCC|].  *)
    (*   eapply cert_rf_in_vf, NEW_RF. } *)

  Lemma simrel_cert_step_hb_delta_dom k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
        (CertSTEP_ : cert_step_ st e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    dom_rel (ESstep.hb_delta S S' k e e') ⊆₁ 
            h □₁ cert_dom G TC (ES.cont_thread S k) st ∪₁ eq e. 
  Proof. 
    cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ESstep.t_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    repeat autounfold with ESStepDb.
    arewrite (
        ES.cont_sb_dom S k × eq e ∪ (ES.cont_sb_dom S k ∪₁ eq e) × eq_opt e' ≡
        ES.cont_sb_dom S k × (eq e ∪₁ eq_opt e') ∪ eq e × eq_opt e'
    ) by basic_solver.
    relsf. rewrite !seqA. splits.

    { rewrite <- seqA, dom_seq.
      rewrite cont_sb_dom_in_hhdom; eauto.
      intros x [y [z [[EQxy | HB] [certD _]]]].
      { basic_solver. }
      left. eapply h_hbD; eauto. basic_solver 10. }

    { rewrite crE. relsf. splits.
      { basic_solver. }
      etransitivity; [| apply set_subset_empty_l]. 
      ESBasicStep.step_solver. }

    { do 4 rewrite <- seqA.
      rewrite dom_seq, !seqA.
      rewrite <- seqA.
      intros x [y [z [HA HB]]].
      left. eapply h_hb_release_ewD; eauto.
      edestruct h_jfD as [a Ha]; eauto.
      { generalize HB. basic_solver 10. }
      eexists. apply seqA. 
      eexists; splits; eauto. }

    { etransitivity; [| apply set_subset_empty_l]. 
      ESBasicStep.step_solver. }

    unfold_cert_step CertSTEP_.
    all : try cdes AJF. 
    all : rewrite JF'.
    all : relsf; splits.
    all : try by (
      etransitivity; [| apply set_subset_empty_l]; 
      ESBasicStep.step_solver
    ).
    all : unfold ESstep.jf_delta.
    all : do 4 rewrite <- seqA.
    all : do 3 rewrite dom_seq.
    all : rewrite !seqA.
    all : intros x [y HH]. 
    all : left; eapply h_hb_release_ewD; eauto.
    all : generalize HH; basic_solver 20.
  Qed.

  Lemma simrel_cert_step_hb_cf_irr k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
        (CertSTEP_ : cert_step_ st e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    irreflexive (Shb S' ⨾ Scf S').
  Proof.
    cdes BSTEP_.
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
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
        (CertSTEP_ : cert_step_ st e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    irreflexive ((Shb S')⁻¹ ⨾ (Scf S') ⨾ (Shb S')).
  Proof.
    cdes BSTEP_.
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
      eapply exec_ncf.
      { apply SRCC.(sr_exec_h). }
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
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
        (CertSTEP_ : cert_step_ st e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    Sjf S' ∩ Secf S' ≡ ∅₂. 
  Proof. 
    cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ESstep.t_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    unfold_cert_step CertSTEP_.
    1,3 : 
      eapply ESstep.step_same_jf_jf_necf; 
      eauto; try apply SRCC;
      eapply ESBasicStep.basic_step_nupd_rmw;
      subst; eauto.
    { eapply simrel_step_add_jf_jf_necf; eauto.
      subst. basic_solver. }
    eapply simrel_step_add_jf_jf_necf; eauto.
    cdes AEW. type_solver.
  Qed.

  Lemma simrel_cert_step_jfe_vis k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
        (CertSTEP_ : cert_step_ st e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    dom_rel (Sjfe S') ⊆₁ (vis S'). 
  Proof. 
    cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ESstep.t_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WFS by apply SRCC.
    etransitivity. 
    2 : eapply ESstep.step_vis_mon; eauto.
    unfold_cert_step CertSTEP_.
    all : try (by eapply simrel_step_add_jf_jfe_vis; eauto).
    all : rewrite ESstep.step_same_jf_jfe; eauto; apply SRCC.
  Qed.

  Lemma simrel_cert_step_consistent k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
        (CertSTEP_ : cert_step_ st e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    @es_consistent S' Weakestmo. 
  Proof. 
    cdes BSTEP_.
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

  Lemma basic_step_hdom_cf_free TC' h k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e e' S S') : 
    ES.cf_free S' (h □₁ (cert_dom G TC (ES.cont_thread S k) st) ∪₁ eq e ∪₁ eq_opt e').
  Proof. 
    eapply ESBasicStep.basic_step_cf_free; 
      try apply SRCC; eauto. 
    eapply cfk_hdom; apply SRCC.
  Qed.

  Lemma basic_step_nupd_hdom_cf_free TC' h k k' e S' 
        (st st' st'': thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e None S S') : 
    ES.cf_free S' (h □₁ (cert_dom G TC (ES.cont_thread S k) st) ∪₁ eq e).
  Proof. 
    eapply ES.cf_free_eq.
    2 : eapply basic_step_hdom_cf_free; eauto. 
    unfold eq_opt. basic_solver 5.
  Qed.

  Lemma simrel_cert_basic_step k lbl lbl' lbls jf ew co
        (st st': (thread_lts (ES.cont_thread S k)).(Language.state))
        (WFTS : wf_thread_state (ES.cont_thread S k) st)
        (KK : K S (k, existT _ _ st))
        (ILBL_STEP : ilbl_step (ES.cont_thread S k) lbls st st') 
        (LBLS_EQ : lbls = opt_to_list lbl' ++ [lbl]) :
    exists k' e e' S',
      ⟪ ES_BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S' ⟫ /\
      ⟪ LBL  : lbl  = S'.(ES.lab) e ⟫ /\
      ⟪ LBL' : lbl' = option_map S'.(ES.lab) e' ⟫ /\
      ⟪ JF' : S'.(ES.jf) ≡ jf ⟫ /\
      ⟪ EW' : S'.(ES.ew) ≡ ew ⟫ /\
      ⟪ CO' : S'.(ES.co) ≡ co ⟫.
  Proof.
    set (ILBL_STEP' := ILBL_STEP).
    eapply lbl_step_cases in ILBL_STEP'; auto.  
    desf. 

    all : eapply opt_to_list_app_singl in LBLS; desf.

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

  Lemma simrel_cert_add_jf TC' h k lbl lbl' lbls ew co
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') 
        (ILBL_STEP : ilbl_step (ES.cont_thread S k) lbls st st') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'')
        (LBLS_EQ : lbls = opt_to_list lbl' ++ [lbl])
        (RR : exists is_ex ord loc val, ⟪ LBL_LD : lbl = Aload is_ex ord loc val ⟫) :
    exists k' e e' S', 
      ⟪ ES_BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S' ⟫ /\
      ⟪ LBL  : lbl  = S'.(ES.lab) e ⟫ /\
      ⟪ LBL' : lbl' = option_map S'.(ES.lab) e' ⟫ /\
      ⟪ CAJF : sim_add_jf S G sc TC TC' h k st e S' ⟫ /\
      ⟪ EW' : S'.(ES.ew) ≡ ew ⟫ /\
      ⟪ CO' : S'.(ES.co) ≡ co ⟫.
  Proof. 
    desf. 
    assert (tc_coherent G sc TC') as TCCOH'. 
    { eapply isim_trav_step_coherence; apply SRCC. }
    assert ((K S) (k, existT Language.state (thread_lts (ES.cont_thread S k)) st)) as KK.
    { edestruct cstate_q_cont; [apply SRCC|]. desf. }
    assert (wf_thread_state (ES.cont_thread S k) st) as WFST.
    { by apply SRCC. }
    edestruct cert_rf_complete as [w RFwa]; 
      eauto; try apply SRCC.
    { assert 
        (E0 G TC' (ES.cont_thread S k) (ThreadEvent (ES.cont_thread S k) st.(eindex)))
        as E0_eindex.
      { eapply ilbl_step_E0_eindex; eauto. 
        all : by eapply SRCC. }
      split; eauto.  
      eapply same_lab_u2v_dom_is_r.
      { apply same_lab_u2v_dom_comm.
        eapply cuplab_cert; apply SRCC. }
      split. 
      { eapply dcertE; eauto; apply SRCC. }
      unfold is_r.
      erewrite steps_preserve_lab.  
      { edestruct lbl_step_cases as [lbl [lbl'' HH]]; eauto.
        destruct HH as [LBLS [HA | HB]].
        all : apply opt_to_list_app_singl in LBLS.
        { destruct HA as [_ [_ [LAB _]]].
          rewrite LAB, upds. desf. }
        destruct HB as [_ [_ [LAB LBLS']]].
        rewrite LAB. unfold upd_opt. 
        destruct lbl'' eqn:Heq. 
        { rewrite updo, upds; desf.
          intros HH. inversion HH. omega. }
        exfalso. desf. }
      { eapply wf_thread_state_steps; eauto.
        eapply ilbl_steps_in_steps.
        econstructor; econstructor; eauto. }
      { by eapply ilbl_steps_in_steps. }
      edestruct lbl_step_cases as [lbl [lbl'' HH]]; eauto.
      destruct HH as [LBLS [HH | HH]].
      all : apply opt_to_list_app_singl in LBLS.
      all : destruct HH as [_ [ACTS _]].
      all : apply ACTS; basic_solver. }
    edestruct simrel_cert_basic_step as [k' [e [e' [S' BSTEP]]]]; eauto.
    desf; do 4 eexists; splits; eauto.
    econstructor; splits.  
    { unfold is_r. by rewrite <- LBL. }
    assert (cert_dom G TC (ES.cont_thread S k) st w) as HDOMw.
    { eapply cert_rf_cert_dom; try apply SRCC; auto. 
      { red. ins. eapply ES.init_tid_K; eauto. apply SRCC. }
      unfold dom_rel. eexists.
      apply seq_eqv_r; splits; eauto. }
    assert 
      ((h □₁ (cert_dom G TC (ES.cont_thread S k) st)) (h w)) 
      as hHDOMhw. 
    { unfolder; eexists; splits; eauto. }
    exists (h w); splits; auto. 
    2 : cdes ES_BSTEP_; desf; eauto. 
    arewrite (e2a S' (h w) = w).  
    { erewrite basic_step_e2a_eq_dom.
      { eapply a2e_fix; eauto. apply SRCC. }
      { apply SRCC. }
      { econstructor; eauto. }
      eapply a2e_img; eauto. apply SRCC. }
    erewrite basic_step_e2a_e; eauto. 
    all : apply SRCC.
  Qed.

  (* Lemma weaken_sim_add_jf TC' h k k' e e' S'  *)
  (*       (st st' st'' : thread_st (ES.cont_thread S k)) *)
  (*       (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')  *)
  (*       (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S')  *)
  (*       (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') *)
  (*       (SAJF : sim_add_jf S G sc TC TC' h k st e S') :  *)
  (*   ESstep.add_jf e S S'. *)
  (* Proof.  *)
  (*   cdes BSTEP_; cdes SAJF. *)
  (*   assert (ESBasicStep.t e e' S S') as BSTEP. *)
  (*   { econstructor. eauto. } *)
  (*   assert (SE S w) as SEw. *)
  (*   { eapply a2e_img; eauto. apply SRCC. } *)
  (*   assert (SE S' w) as SEw'. *)
  (*   { eapply ESBasicStep.basic_step_acts_set; eauto. basic_solver. } *)
  (*   assert (SE S' e) as SEe'. *)
  (*   { eapply ESBasicStep.basic_step_acts_set; eauto. basic_solver. } *)
  (*   assert (Gtid (e2a S' e) = ES.cont_thread S k) as GTIDe. *)
  (*   { rewrite <- e2a_tid. erewrite ESBasicStep.basic_step_tid_e; eauto. } *)
  (*   econstructor; auto.  *)
  (*   exists w; splits; auto.   *)
  (*   { assert (is_w (Glab ∘ (e2a S')) w) as WW. *)
  (*     { eapply cert_rfD, seq_eqv_lr in NEW_RF. *)
  (*       destruct NEW_RF as [HH _]. *)
  (*         by unfold is_w, compose in *. } *)
  (*     eapply same_lab_u2v_dom_is_w; eauto. *)
  (*     { eapply basic_step_e2a_same_lab_u2v; eauto; apply SRCC. } *)
  (*     red; split; auto. } *)
  (*   { assert (restr_rel (SE S') (same_loc (Slab S')) w e) as HH. *)
  (*     { eapply same_lab_u2v_dom_same_loc. *)
  (*       { eapply basic_step_e2a_same_lab_u2v; eauto; apply SRCC. } *)
  (*       apply restr_relE, seq_eqv_lr.  *)
  (*       splits; auto.  *)
  (*       eapply cert_rfl in NEW_RF. *)
  (*       by unfold same_loc, loc, compose in *. } *)
  (*     apply restr_relE, seq_eqv_lr in HH.  *)
  (*     basic_solver. } *)
  (*   assert (same_val (certLab G st'') (e2a S' w) (e2a S' e)) as SAME_VAL. *)
  (*   { eapply cert_rfv_clab; eauto. apply SRCC. } *)
  (*   unfold same_val, val in *. *)
  (*   erewrite basic_step_e2a_certlab_e with (e := e); eauto. *)
  (*   arewrite (Slab S' w = Slab S w). *)
  (*   { erewrite ESBasicStep.basic_step_lab_eq_dom; eauto. } *)
  (*   assert (e2a S w = e2a S' w) as E2Aw.  *)
  (*   { symmetry. eapply basic_step_e2a_eq_dom; eauto. apply SRCC. } *)
  (*   rewrite <- E2Aw in *. *)
  (*   eapply cert_rf_ntid_iss_sb in NEW_RF.  *)
  (*   2-10: apply SRCC. *)
  (*   unfolder in wHDOM. destruct wHDOM as [wa [CERTwa Hwa]]. *)
  (*   assert (g w = wa) as Gwwa. *)
  (*   { rewrite <- Hwa. *)
  (*     eapply a2e_fix; [apply SRCC|]. *)
  (*     unfolder. basic_solver. } *)
  (*   arewrite (Slab S w = certLab G st'' (e2a S w)); [|auto]. *)
  (*   rewrite <- Hwa at 1. *)
  (*   rewrite Gwwa. *)
  (*   arewrite ((Slab S) (h wa) = (Slab S ∘ h) wa). *)
  (*   destruct NEW_RF as [Iss | SB]. *)
  (*   { assert (I wa) as Iw. *)
  (*     { apply seq_eqv_l in Iss. unfolder in Iss. rewrite <- Gwwa. basic_solver. } *)
  (*     unfold certLab. *)
  (*     destruct  *)
  (*       (excluded_middle_informative (acts_set (ProgToExecution.G st'') wa))  *)
  (*       as [GCE | nGCE]. *)
  (*     { assert (GNtid_ (ES.cont_thread S k) wa) as HH. *)
  (*       { apply seq_eqv_l in Iss.  *)
  (*         destruct Iss as [[NTID _] _]. *)
  (*         rewrite <- Gwwa. apply NTID. } *)
  (*       exfalso. apply HH.  *)
  (*       eapply dcertE in GCE; [|apply SRCC]. *)
  (*       by destruct GCE. } *)
  (*     eapply hlabCI; eauto. *)
  (*     basic_solver. } *)
  (*   edestruct sb_tid_init as [STID | INITx]; eauto.  *)
  (*   { eapply hlab; eauto. right.  *)
  (*     destruct CERTwa as [[Cwa | Iwa] | ACTSst]; auto. *)
  (*     { eapply cstate_covered; [apply SRCC|]. *)
  (*       split; auto. *)
  (*       by rewrite <- Gwwa, STID, GTIDe. } *)
  (*     exfalso. destruct Iwa as [_ NTIDwa]. *)
  (*     apply NTIDwa. *)
  (*     rewrite <- Gwwa. *)
  (*     erewrite <- ESBasicStep.basic_step_tid_e; eauto. *)
  (*     by rewrite e2a_tid. } *)
  (*   assert (C wa) as Cwa. *)
  (*   { eapply init_covered; [apply SRCC|]. *)
  (*     rewrite <- Gwwa.  *)
  (*     split; auto.   *)
  (*     eapply e2a_GE; [apply SRCC|]. *)
  (*     unfolder. eauto. } *)
  (*   eapply hlab; eauto. basic_solver. *)
  (* Qed. *)
       
  (* Lemma simrel_cert_load_step_jfe_vis TC' h k k' e S' *)
  (*       (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state)) *)
  (*       (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') *)
  (*       (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e None S S')  *)
  (*       (SAJF : sim_add_jf S G sc TC TC' h k st e S') *)
  (*       (EW' : Sew S' ≡ Sew S) *)
  (*       (CO' : Sco S' ≡ Sco S) *)
  (*       (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :  *)
  (*   dom_rel (Sjfe S') ⊆₁ (vis S').  *)
  (* Proof.  *)
  (*   cdes BSTEP_; cdes SAJF. *)
  (*   assert (ESBasicStep.t e None S S') as BSTEP. *)
  (*   { econstructor; eauto. } *)
  (*   assert (ES.Wf S) as WFS by apply SRCC. *)
  (*   assert (ESstep.t_load e None S S') as LSTEP. *)
  (*   { econstructor; splits; auto.  *)
  (*     eapply weaken_sim_add_jf; eauto. } *)
  (*   cdes LSTEP. *)
  (*   assert (ES.Wf S') as WFS'. *)
  (*   { admit. } *)
  (*   destruct wHDOM as [wa [CERTwa Hwa]]. *)
  (*   assert (SE S w) as SEw. *)
  (*   { rewrite <- Hwa. *)
  (*     eapply a2e_img. *)
  (*     2 : unfolder; splits; eauto.  *)
  (*     apply SRCC. } *)
  (*   erewrite ESstep.load_step_jfe; eauto.  *)
  (*   rewrite dom_union.  *)
  (*   apply set_subset_union_l. split.  *)
  (*   { etransitivity.  *)
  (*     { eapply jfe_vis; apply SRCC. } *)
  (*     eapply ESstep.load_step_vis_mon; eauto. } *)
  (*   unfold ES.jfe. *)
  (*   rewrite <- seq_eqv_minus_lr, SSJF', seq_union_l.  *)
  (*   arewrite (Sjf S ⨾ ⦗eq e⦘ ≡ ∅₂).  *)
  (*   { split; [|basic_solver]. *)
  (*     rewrite WFS.(ES.jfE). *)
  (*     unfolder; splits; ins; desf; omega. } *)
  (*   arewrite (singl_rel w e ⨾ ⦗eq e⦘ ≡ singl_rel w e) by basic_solver.  *)
  (*   rewrite union_false_l. *)
  (*   unfolder. intros x [y [[EQx EQy] nSB]].  *)
  (*   subst x y.  *)
  (*   eapply cert_rf_ntid_iss_sb in NEW_RF. *)
  (*   2-6 : apply SRCC. *)
  (*   assert (e2a S' w = wa) as E2Aw. *)
  (*   { erewrite basic_step_e2a_eq_dom with (S := S); eauto.  *)
  (*     rewrite <- Hwa. *)
  (*     fold (compose g h wa). *)
  (*     eapply a2e_fix; eauto. apply SRCC. } *)
  (*   eapply ESstep.load_step_vis_mon; eauto. *)
  (*   destruct NEW_RF as [Iss | SB]. *)
  (*   { eapply fvis; [apply SRCC|]. *)
  (*     rewrite E2Aw in *.  *)
  (*     apply seq_eqv_l in Iss. *)
  (*     destruct Iss as [[NTIDwa Iwa] _]. *)
  (*     unfold set_collect.  *)
  (*     exists wa. split; [basic_solver 10|]. *)
  (*     erewrite hfeq; eauto.  *)
  (*     basic_solver 10. } *)
  (*   edestruct sb_tid_init as [STID | INITw]; eauto.  *)
  (*   { exfalso.  *)
  (*     do 2 erewrite <- e2a_tid in STID. *)
  (*     assert (Stid S' e <> tid_init) as TIDe. *)
  (*     { erewrite ESBasicStep.basic_step_tid_e; eauto.  *)
  (*       red. ins. eapply ES.init_tid_K.  *)
  (*       2: eauto. eauto. } *)
  (*     assert ((⦗SEninit S'⦘ ⨾ ES.same_tid S' ⨾ ⦗SEninit S'⦘) w e) as HH.  *)
  (*     { apply seq_eqv_lr.  *)
  (*       unfold ES.acts_ninit_set, ES.acts_init_set. *)
  (*       unfolder; splits; intuition.   *)
  (*       { eapply ESBasicStep.basic_step_acts_set; eauto. basic_solver. } *)
  (*       { congruence. } *)
  (*       unfold opt_ext in *. omega. } *)
  (*     apply ES.same_thread in HH; auto.   *)
  (*     destruct HH as [HA | HB]. *)
  (*     { apply seq_eqv_lr in HA. *)
  (*       destruct HA as [nINITw [CRS_SB nINITe]]. *)
  (*       apply crsE in CRS_SB. *)
  (*       destruct CRS_SB as [[AA | BB] | CC]. *)
  (*       { unfolder in AA. eapply ESBasicStep.basic_step_acts_set_ne; eauto. *)
  (*         desf; congruence. } *)
  (*       { intuition. } *)
  (*       unfold transp in CC.  *)
  (*       eapply ESBasicStep.basic_step_nupd_sb in CC; eauto.   *)
  (*       destruct CC as [DD | EE]. *)
  (*       { eapply ES.sbE in DD; eauto.   *)
  (*         apply seq_eqv_lr in DD. *)
  (*         eapply ESBasicStep.basic_step_acts_set_ne; eauto. *)
  (*         desf. } *)
  (*       destruct EE as [CONT_SB _]. *)
  (*       eapply ES.cont_sb_domE in CONT_SB; eauto.  *)
  (*       eapply ESBasicStep.basic_step_acts_set_ne; eauto. }  *)
  (*     eapply basic_step_hdom_cf_free; eauto.  *)
  (*     apply seq_eqv_lr. splits.  *)
  (*     { left; left. unfolder; eauto. } *)
  (*     { eapply HB. } *)
  (*     by left; right. } *)
  (*   exfalso.  *)
  (*   apply nSB. *)
  (*   eapply ESBasicStep.basic_step_nupd_sb; eauto.  *)
  (*   right; unfolder; splits; auto.  *)
  (*   eapply ES.cont_sb_dom_Einit; eauto. *)
  (*   eapply himgInit; eauto.  *)
  (*   rewrite <- Hwa in *.  *)
  (*   unfolder; eexists; splits; eauto.  *)
  (*   { unfold sb in SB. apply seq_eqv_lr in SB. desf. } *)
  (*   congruence. *)
  (* Admitted.   *)

  (* Lemma simrel_cert_load_step_hb_cf_irr TC' h k k' e S' *)
  (*       (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state)) *)
  (*       (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') *)
  (*       (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e None S S')  *)
  (*       (SAJF : sim_add_jf S G sc TC TC' h k st e S') *)
  (*       (EW' : Sew S' ≡ Sew S) *)
  (*       (CO' : Sco S' ≡ Sco S) *)
  (*       (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :  *)
  (*   irreflexive (Shb S' ⨾ Scf S'). *)
  (* Proof.  *)
  (*   cdes BSTEP_; cdes SAJF. *)
  (*   assert (ESBasicStep.t e None S S') as BSTEP. *)
  (*   { econstructor; eauto. } *)
  (*   assert (ES.Wf S) as WFS by apply SRCC. *)
  (*   (* assert (ES.Wf S') as WFS'. *) *)
  (*   (* { admit. } *) *)
  (*   assert (ESstep.t_load e None S S') as LSTEP. *)
  (*   { econstructor; splits; auto.  *)
  (*     eapply weaken_sim_add_jf; eauto. } *)

  (*   erewrite ESstep.load_step_hb; eauto. *)
  (*   rewrite SSJF'.  *)
  (*   erewrite ESBasicStep.basic_step_nupd_cf; eauto. *)
  (*   (* erewrite ESstep.load_step_jf; eauto. *) *)
  (*   (* rewrite SSJF'.  *) *)
  (*   (* rewrite inclusion_minus_rel. *) *)
  (*   rewrite crE, csE. relsf. *)
  (*   rewrite !seqA. *)
  (*   rewrite !irreflexive_union. *)
  (*   splits. *)

  (*   all : try by (eapply empty_irr; split; try done; ESBasicStep.step_solver). *)

  (*   { eapply ecf_irr_hb_cf_irr. apply SRCC. } *)

  (*   { intros x [y [HB [KCF EQe]]].  *)
  (*     subst x. apply hbE, seq_eqv_lr in HB; auto. desf. *)
  (*     eapply ESBasicStep.basic_step_acts_set_ne; eauto. } *)

  (*   { intros x [z [[KSB EQe] [_ KCF]]]. subst z.  *)
  (*     eapply ES.cont_cf_cont_sb in KCF; eauto. *)
  (*     destruct KCF as [_ NKSB]. by apply NKSB. } *)

  (*   { intros x HH. *)
  (*     destruct HH as [y [HB HH]]. *)
  (*     destruct HH as [z [[KSB EQe] HH]]. subst z. *)
  (*     destruct HH as [_ KCF]. *)
  (*     unfold ES.cont_sb_dom, ES.cont_cf_dom in KSB, KCF. *)
  (*     destruct k. *)

  (*     { eapply hb_ninit; [apply WFS|]. *)
  (*       apply seq_eqv_r. eauto. } *)
      
  (*     destruct KCF as [CF | SB]. *)

  (*     { destruct CF as [z HX].  *)
  (*       apply seq_eqv_r in HX. desf. *)
  (*       apply ES.cf_sym in HX. *)
  (*       eapply ecf_irr_hb_cf_irr. *)
  (*       { apply SRCC. } *)
  (*       eexists; splits; [|eauto]. *)
  (*       destruct KSB as [z' HY]. *)
  (*       apply seq_eqv_r in HY. desf. *)
  (*       apply crE in HY.  *)
  (*       unfolder in HY. desf. *)
  (*       eapply hb_trans; eauto.  *)
  (*       eapply sb_in_hb; eauto. } *)

  (*     eapply coh; [apply SRCC|]. *)
  (*     unfolder.  *)
  (*     exists x. split; [| by left]. *)
  (*     eapply hb_trans; eauto. *)
  (*     unfolder in KSB. unfolder in SB. desf. *)
  (*     { by eapply sb_in_hb. } *)
  (*     eapply hb_trans; eapply sb_in_hb; eauto. } *)

  (*   { intros x HH. *)
  (*     unfolder in HH.  *)
  (*     eapply cfk_hdom; eauto. *)
  (*     split; [|basic_solver]. *)
  (*     eapply h_rel_ewD; eauto.   *)
  (*     unfolder. basic_solver 10. } *)

  (*   intros x HH.  *)
  (*   unfolder in HH.  *)
  (*   eapply cfk_hdom; eauto. *)
  (*   split; [|basic_solver]. *)
  (*   eapply h_hbD; eauto. *)
  (*   destruct HH as [z [HB HH]]. *)
  (*   unfolder. do 2 eexists; splits; eauto. *)
  (*   eapply h_rel_ewD; eauto. *)
  (*   unfolder. basic_solver 10.  *)
  (* Qed. *)

  (* Lemma simrel_cert_load_step_hb_cf_thb_irr TC' h k k' e S' *)
  (*       (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state)) *)
  (*       (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') *)
  (*       (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e None S S')  *)
  (*       (SAJF : sim_add_jf S G sc TC TC' h k st e S') *)
  (*       (EW' : Sew S' ≡ Sew S) *)
  (*       (CO' : Sco S' ≡ Sco S) *)
  (*       (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :  *)
  (*   irreflexive ((Shb S')⁻¹ ⨾ (Scf S') ⨾ (Shb S')). *)
  (* Proof. *)
  (*   cdes BSTEP_; cdes SAJF. *)
  (*   assert (ESBasicStep.t e None S S') as BSTEP. *)
  (*   { econstructor; eauto. } *)
  (*   assert (ES.Wf S) as WFS by apply SRCC. *)
  (*   assert (ESstep.t_load e None S S') as LSTEP. *)
  (*   { econstructor; splits; auto.  *)
  (*     eapply weaken_sim_add_jf; eauto. } *)
  (*   (* assert  *) *)
  (*   (*   (restr_rel (h □₁ cert_dom G TC (ES.cont_thread S k) st) Secf ⊆ ∅₂)  *) *)
  (*   (*   as HDOM_nECF. *) *)
  (*   (* { eapply exec_necfD.  *) *)
  (*   (*   5 : apply SRCC.(sr_exec_h). *) *)
  (*   (*   all : try apply SRCC. *) *)
  (*   (*   unfold cert_dom. basic_solver. } *) *)

  (*   erewrite ESBasicStep.basic_step_nupd_cf; eauto. *)
  (*   rewrite csE. relsf. *)
  (*   arewrite  *)
  (*     ((Shb S')⁻¹ ⨾ ES.cont_cf_dom S k × eq e ⨾ Shb S' ≡ ∅₂).  *)
  (*   { split; [|done]. *)
  (*     erewrite dom_rel_helper_in with (r := (Shb S')). *)
  (*     2 : eapply ESstep.load_step_hb_dom; eauto. *)
  (*     unfolder; ins; splits; desf; omega. } *)
  (*   arewrite  *)
  (*     ((Shb S')⁻¹ ⨾ eq e × ES.cont_cf_dom S k ⨾ Shb S' ≡ ∅₂). *)
  (*   { split; [|done]. *)
  (*     erewrite dom_rel_helper_in with (r := (Shb S')). *)
  (*     2 : eapply ESstep.load_step_hb_dom; eauto. *)
  (*     rewrite transp_seq, transp_eqv_rel. *)
  (*     unfolder; ins; splits; desf; omega. } *)
  (*   rewrite !union_false_r. *)
    
  (*   erewrite ESstep.load_step_hb; eauto.  *)
  (*   rewrite transp_union. relsf. *)
  (*   (* rewrite ESstep.load_step_rf; eauto. *) *)
  (*   (* rewrite inclusion_minus_rel. *) *)
  (*   rewrite SSJF'. *)
  (*   rewrite transp_union. relsf. *)
  (*   (* rewrite seq_union_l with (r := ⦗eq e⦘). *) *)
  (*   arewrite_false (Sjf S ⨾ ⦗SAcq S'⦘ ⨾ ⦗eq e⦘);  *)
  (*     [ESBasicStep.step_solver|]. *)
  (*   (* rewrite union_false_l. *) *)
  (*   (* arewrite  *) *)
  (*   (*   ((Sjf S ∪ singl_rel w e ⨾ ⦗eq e⦘) ⨾ ⦗SAcq S'⦘ ⨾ ⦗eq e⦘ ≡ *) *)
  (*   (*              singl_rel w e ⨾ ⦗SAcq S'⦘). *) *)
  (*   (* { rewrite seq_union_l. *) *)
  (*   (*   arewrite_false (Srf S ⨾ ⦗SAcq S'⦘ ⨾ ⦗eq e⦘). *) *)
  (*   (*   { ESBasicStep.step_solver. } *) *)
  (*   (*   basic_solver 10. } *) *)
  (*   rewrite ?transp_union, ?transp_seq, ?transp_cross, *)
  (*           ?transp_eqv_rel, ?transp_singl_rel. *)
  (*   relsf. *)
  (*   rewrite !irreflexive_union. *)
  (*   splits. *)
    
  (*   { eapply ecf_irr_thb_cf_hb_irr. apply SRCC. } *)
  (*   all : try by ESBasicStep.step_solver. *)
  (*   all : try rewrite transp_cr with (r := Shb S). *)

  (*   { unfold seq, cross_rel.  *)
  (*     red. ins. desc. *)
  (*     eapply h_necfD; eauto.  *)
  (*     red; splits. *)
  (*     { unfold ecf. basic_solver 10. } *)
  (*     all : eapply cont_sb_dom_in_hhdom; eauto. } *)

  (*   { unfold seq, cross_rel.  *)
  (*     red. ins. desc. *)
  (*     eapply h_necfD; eauto.  *)
  (*     red. splits. *)
  (*     { unfold ecf. basic_solver 10. } *)
  (*     { eapply h_rel_ewD; eauto. *)
  (*       unfold singl_rel in *. desc. *)
  (*       basic_solver 10. } *)
  (*     eapply cont_sb_dom_in_hhdom; eauto. } *)

  (*   { unfold seq, cross_rel.  *)
  (*     red. ins. desc. *)
  (*     eapply h_necfD; eauto.  *)
  (*     red. splits. *)
  (*     { unfold ecf. basic_solver 10. } *)
  (*     { eapply cont_sb_dom_in_hhdom; eauto. } *)
  (*     eapply h_rel_ewD; eauto. *)
  (*     unfold singl_rel in *. desc. *)
  (*     basic_solver 10. } *)

  (*   unfold seq, cross_rel.  *)
  (*   red. ins. desc. *)
  (*   eapply h_necfD; eauto.   *)
  (*   red. splits. *)
  (*   { unfold ecf. basic_solver 10. } *)
  (*   { eapply h_rel_ewD; eauto. *)
  (*     unfold singl_rel in *. desc. *)
  (*     basic_solver 10. } *)
  (*   eapply h_rel_ewD; eauto. *)
  (*   unfold singl_rel in *. desc. *)
  (*   basic_solver 10. *)
  (* Qed. *)
  
  (* Lemma simrel_cert_load_step_jf_ncf TC' h k k' e S' *)
  (*       (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state)) *)
  (*       (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') *)
  (*       (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e None S S')  *)
  (*       (SAJF : sim_add_jf S G sc TC TC' h k st e S') *)
  (*       (EW' : Sew S' ≡ Sew S) *)
  (*       (CO' : Sco S' ≡ Sco S) *)
  (*       (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :  *)
  (*   Sjf S' ∩ Scf S' ≡ ∅₂. *)
  (* Proof.  *)
  (*   cdes BSTEP_; cdes SAJF. *)
  (*   assert (ESBasicStep.t e None S S') as BSTEP. *)
  (*   { econstructor; eauto. } *)
  (*   assert (ES.Wf S) as WFS by apply SRCC. *)
  (*   assert (ESstep.t_load e None S S') as LSTEP. *)
  (*   { econstructor; splits; auto.  *)
  (*     eapply weaken_sim_add_jf; eauto. } *)
  (*   cdes LSTEP. *)
  (*   split; [|basic_solver]. *)
  (*   rewrite SSJF'. *)
  (*   erewrite ESBasicStep.basic_step_nupd_cf; eauto.  *)
  (*   rewrite !inter_union_r, !inter_union_l.  *)
  (*   unionL. *)
  (*   { eapply jf_necf_jf_ncf; apply SRCC. } *)
  (*   { rewrite ES.cfE. *)
  (*     unfolder; splits; ins; desf; omega. } *)
  (*   { rewrite ES.jfE; auto.  *)
  (*     unfolder; splits; ins; desf; omega. } *)
  (*   rewrite csE, inter_union_r, transp_cross. *)
  (*   unionL.  *)
  (*   { unfolder. ins. desf. *)
  (*     eapply cfk_hdom; eauto.  *)
  (*     unfolder; eauto. } *)
  (*   rewrite ES.cont_cf_domEninit; eauto.  *)
  (*   unfold ES.acts_ninit_set. *)
  (*   unfolder; splits; ins; desf; omega.  *)
  (* Qed. *)

  (* Lemma simrel_cert_load_step_hb_jf_ncf TC' h k k' e S' *)
  (*       (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state)) *)
  (*       (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') *)
  (*       (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e None S S')  *)
  (*       (SAJF : sim_add_jf S G sc TC TC' h k st e S') *)
  (*       (EW' : Sew S' ≡ Sew S) *)
  (*       (CO' : Sco S' ≡ Sco S) *)
  (*       (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :  *)
  (*   (Shb S' ⨾ Sjf S') ∩ Scf S' ≡ ∅₂. *)
  (* Proof.  *)
  (*   cdes BSTEP_; cdes SAJF. *)
  (*   assert (ESBasicStep.t e None S S') as BSTEP. *)
  (*   { econstructor; eauto. } *)
  (*   assert (ES.Wf S) as WFS by apply SRCC. *)
  (*   assert (ESstep.t_load e None S S') as LSTEP. *)
  (*   { econstructor; splits; auto.  *)
  (*     eapply weaken_sim_add_jf; eauto. } *)
  (*   cdes LSTEP. *)
  (*   split; [|basic_solver]. *)
  (*   erewrite ESBasicStep.basic_step_nupd_cf; eauto.  *)
  (*   erewrite ESstep.load_step_hb; eauto.  *)
  (*   relsf. rewrite !seqA. *)
  (*   assert (Sjf S' ≡ ⦗SE S⦘ ⨾ Sjf S') as JFdomE. *)
  (*   { eapply dom_rel_helper.  *)
  (*     eapply ESstep.load_step_jf_dom; eauto. } *)
  (*   rewrite JFdomE. *)
  (*   arewrite (ES.cont_sb_dom S k × eq e ⨾ ⦗SE S⦘ ⨾ Sjf S' ≡ ∅₂). *)
  (*   { unfolder; splits; ins; desf; omega. } *)
  (*   arewrite (⦗eq e⦘ ⨾ ⦗SE S⦘ ⨾ Sjf S' ≡ ∅₂).  *)
  (*   { unfolder; splits; ins; desf; omega. } *)
  (*   relsf.  *)
  (*   rewrite csE, transp_cross. *)
  (*   rewrite <- JFdomE, SSJF'.  *)
  (*   rewrite seq_union_r, !inter_union_r, !inter_union_l. *)
    
  (*   unionL.  *)
  (*   { apply jf_necf_hb_jf_ncf; apply SRCC. } *)
  (*   { solve_by_EE ES.cfE. } *)
  (*   { solve_by_EE ES.jfE. } *)
  (*   2,3 : solve_by_EE hbE. *)

  (*   intros x y [[z [HB [EQz _]]] [KCF EQy]].  *)
  (*   subst y z. *)
  (*   assert (Scf S' x e) as CFE. *)
  (*   { eapply ESBasicStep.basic_step_nupd_cf; eauto.  *)
  (*     right. basic_solver. } *)
  (*   eapply basic_step_nupd_hdom_cf_free; eauto.  *)
  (*   apply seq_eqv_lr; splits; eauto; [|basic_solver].  *)
  (*   left. eapply h_hbD; try apply SRCC.  *)
  (*   basic_solver 10.  *)
  (* Qed. *)

  (* Lemma simrel_cert_load_step_hb_tjf_ncf TC' h k k' e S' *)
  (*       (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state)) *)
  (*       (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') *)
  (*       (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e None S S')  *)
  (*       (SAJF : sim_add_jf S G sc TC TC' h k st e S') *)
  (*       (EW' : Sew S' ≡ Sew S) *)
  (*       (CO' : Sco S' ≡ Sco S) *)
  (*       (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :  *)
  (*   (Shb S' ⨾ (Sjf S')⁻¹) ∩ Scf S' ≡ ∅₂. *)
  (* Proof.  *)
  (*   cdes BSTEP_; cdes SAJF. *)
  (*   assert (ESBasicStep.t e None S S') as BSTEP. *)
  (*   { econstructor; eauto. } *)
  (*   assert (ES.Wf S) as WFS by apply SRCC. *)
  (*   assert (ESstep.t_load e None S S') as LSTEP. *)
  (*   { econstructor; splits; auto.  *)
  (*     eapply weaken_sim_add_jf; eauto. } *)
  (*   assert *)
  (*     (restr_rel (h □₁ cert_dom G TC (ES.cont_thread S k) st) (Scf S) ⊆ ∅₂) *)
  (*     as HnCF. *)
  (*   { rewrite restr_relE. eapply exec_ncf. apply SRCC. } *)
  (*   cdes LSTEP. *)
  (*   split; [|basic_solver]. *)
  (*   rewrite SSJF'. *)
  (*   erewrite ESBasicStep.basic_step_nupd_cf; eauto.  *)
  (*   erewrite ESstep.load_step_hb; eauto.  *)
  (*   rewrite crE, csE, transp_union, transp_cross, transp_singl_rel.  *)
  (*   rewrite SSJF'.  *)
  (*   relsf.  *)
  (*   rewrite !inter_union_r, !inter_union_l.  *)

  (*   assert (singl_rel e w ⊆ eq e × SE S) as singlE. *)
  (*   { unfolder. ins. desf. splits; auto.  *)
  (*     eapply a2e_img in wHDOM; eauto. apply SRCC. } *)

  (*   unionL. *)
  (*   { apply jf_necf_hb_tjf_ncf; apply SRCC. } *)
  (*   all : try by (rewrite ?singlE; ESBasicStep.step_solver). *)
    
  (*   (* 1-4, 10-14, 21-24 : solve_by_EE ES.jfE. *) *)
  (*   (* 1,6, 11-12, 14, 16 : solve_by_EE hbE. *) *)
  (*   (* 5-8 : solve_by_EE singlE. *) *)
  (*   (* 5 : solve_by_EE ES.cont_sb_domE. *) *)
  (*   (* 5 : solve_by_EE releaseE.  *) *)

  (*   { erewrite cont_sb_dom_in_hhdom; eauto. *)
  (*     rewrite seq_cross_singl_l; auto.  *)
  (*     intros x y [[HDOMx EQy] CF]. subst y.  *)
  (*     eapply HnCF. red. splits; eauto. } *)

  (*   { rewrite seqA, seq_cross_singl_l; auto.  *)
  (*     rewrite h_hb_in_Chb_sb; eauto.  *)
  (*     rewrite !seq_union_l, inter_union_l. *)
  (*     unionL.  *)
  (*     { intros x y [HH CF]. *)
  (*       eapply HnCF; eauto.   *)
  (*       red. splits; [apply CF | |].   *)
  (*       { unfolder in HH. desf. *)
  (*         unfolder. unfold cert_dom.  *)
  (*         eexists. splits; eauto.  *)
  (*         by left; left. } *)
  (*       unfolder in HH; desf. } *)
  (*     intros x y [HH CF]. *)
  (*     eapply HnCF; eauto.   *)
  (*     red. splits; [apply CF | |].   *)
  (*     { destruct HH as [z [SB [CONTz EQw]]]. *)
  (*       subst y.  *)
  (*       assert ((Ssb S ⨾ ⦗ ES.cont_sb_dom S k ⦘) x z) as SBC. *)
  (*       { unfolder; eauto. } *)
  (*       eapply dom_rel_helper_in in SBC. *)
  (*       2 : eapply ES.cont_sb_prcl; eauto.  *)
  (*       eapply cont_sb_dom_in_hhdom; eauto.  *)
  (*       unfolder in SBC. desf. } *)
  (*     unfolder in HH; desf. } *)

  (*   (* all : *) *)
  (*   (*   (* erewrite ESstep.load_step_rf, SSJF'; eauto; *) *) *)
  (*   (*   rewrite !seq_union_l, !seq_union_r, !minus_union_l; *) *)
  (*   (*   relsf; rewrite !inter_union_l; unionL. *) *)

  (*   (* 1,4 : solve_by_EE ES.rfE. *) *)
  (*   (* 1,3 : solve_by_EE ES.jfE. *) *)

  (*   (* all : rewrite inclusion_minus_rel, !seqA. *) *)

  (*   { intros x y [HH CF]. *)
  (*     eapply HnCF; eauto.   *)
  (*     red. splits; [apply CF | |].   *)
  (*     { eapply h_rel_ewD; eauto. *)
  (*       unfolder. unfolder in HH. desc. *)
  (*       (* destruct HH as [z [REL HH]]. *) *)
  (*       (* destruct HH as [z' [rEW HH]]. *) *)
  (*       do 2 eexists; splits; eauto. } *)
  (*     unfolder in HH. desf. } *)

  (*   intros x y [HH CF]. *)
  (*   eapply HnCF; eauto.   *)
  (*   red. splits; [apply CF | |].   *)
  (*   { eapply h_hbD; eauto.  *)
  (*     unfolder. unfolder in HH. desc. *)
  (*     do 2 eexists; splits; eauto.  *)
  (*     eapply h_rel_ewD; eauto.       *)
  (*     unfolder.  *)
  (*     do 2 eexists; splits; eauto. } *)
  (*   unfolder in HH. desf.  *)
  (* Qed. *)

  (* Lemma simrel_cert_load_step_hb_jf_thb_ncf TC' h k k' e S' *)
  (*       (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state)) *)
  (*       (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') *)
  (*       (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e None S S')  *)
  (*       (SAJF : sim_add_jf S G sc TC TC' h k st e S') *)
  (*       (EW' : Sew S' ≡ Sew S) *)
  (*       (CO' : Sco S' ≡ Sco S) *)
  (*       (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :  *)
  (*   (Shb S' ⨾ Sjf S' ⨾ (Shb S')⁻¹) ∩ Scf S' ≡ ∅₂. *)
  (* Proof.  *)
  (*   cdes BSTEP_; cdes SAJF. *)
  (*   assert (ESBasicStep.t e None S S') as BSTEP. *)
  (*   { econstructor; eauto. } *)
  (*   assert (ES.Wf S) as WFS by apply SRCC. *)
  (*   assert (ESstep.t_load e None S S') as LSTEP. *)
  (*   { econstructor; splits; auto.  *)
  (*     eapply weaken_sim_add_jf; eauto. } *)
  (*   assert *)
  (*     (restr_rel (h □₁ cert_dom G TC (ES.cont_thread S k) st) (Scf S) ⊆ ∅₂) *)
  (*     as HnCF. *)
  (*   { rewrite restr_relE. eapply exec_ncf. apply SRCC. } *)

  (*   cdes LSTEP. *)
  (*   split; [|basic_solver]. *)
  (*   erewrite ESBasicStep.basic_step_nupd_cf; eauto.  *)
  (*   erewrite ESstep.load_step_hb; eauto. *)
  (*   rewrite SSJF'. *)
  (*   rewrite !seq_union_r, !seq_union_l, !seq_union_r. *)
  (*   rewrite !transp_union, !transp_seq, !transp_cross, transp_eqv_rel.  *)
  (*   relsf. rewrite !seqA. *)
    
  (*   rewrite !inter_union_r, !inter_union_l. *)

  (*   assert (singl_rel w e ⊆ SE S × eq e) as singlE. *)
  (*   { unfolder. ins. desf. splits; auto.  *)
  (*     eapply a2e_img in wHDOM; eauto. apply SRCC. } *)

  (*   unionL. *)
  (*   { eapply jf_necf_hb_jf_thb_ncf; eapply SRCC. } *)
  (*   all : try by (rewrite ?singlE; ESBasicStep.step_solver). *)

  (*   { intros x y [HH CF]. *)
  (*     eapply HnCF; eauto.   *)
  (*     red. splits; [apply CF | |].  *)
  (*     { eapply h_hbD; eauto.  *)
  (*       destruct HH as [z [HB [z' [[EQz EQz'] HH]]]]. *)
  (*       subst z z'. *)
  (*       unfolder; splits; eauto. }  *)
  (*     unfolder in HH. desf.  *)
  (*     { eapply cont_sb_dom_in_hhdom; eauto. } *)
  (*     eapply h_hbD; eauto.  *)
  (*     unfolder. do 2 eexists; splits; eauto.  *)
  (*     eapply cont_sb_dom_in_hhdom; eauto. } *)

  (*   intros x y [HH CF]. *)
  (*   eapply HnCF; eauto.   *)
  (*   red. splits; [apply CF | |].  *)
  (*   { eapply h_hbD; eauto.  *)
  (*     destruct HH as [z [HB [z' [[EQz EQz'] HH]]]]. *)
  (*     subst z z'.  *)
  (*     unfolder; splits; eauto. } *)
  (*   assert (((Shb S)^? ⨾ release S ⨾ (Sew S)^? ⨾ singl_rel w e) y e) as HBrREL.  *)
  (*   { unfold seq, eqv_rel, transp in HH. desf.  *)
  (*     unfold seq.  *)
  (*     eexists; splits; eauto. } *)
  (*   destruct HBrREL as [z [[EQ | HB] RELew]]. *)
  (*   { subst z.  *)
  (*     eapply h_rel_ewD; eauto.  *)
  (*     destruct RELew as [z [REL HX]]. *)
  (*     destruct HX as [z' [rEW [EQz' _]]]. *)
  (*     subst z'.  *)
  (*     do 2 eexists; splits; eauto.  *)
  (*     eexists; splits; eauto; desf. } *)
  (*   eapply h_hbD; eauto.  *)
  (*   unfolder. exists z, z. splits; auto. *)
  (*   eapply h_rel_ewD; eauto.  *)
  (*   destruct RELew as [z' [REL HX]]. *)
  (*   destruct HX as [z'' [rEW [EQz'' _]]]. *)
  (*   subst z''.  *)
  (*   do 2 eexists; splits; eauto.  *)
  (*   eexists; splits; eauto; desf.  *)
  (* Qed. *)

  Lemma simrel_cert_load_step_subexec_preserved TC' h k k' e S'
        (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e None S S') 
        (SAJF : sim_add_jf S G sc TC TC' h k st e S')
        (EW' : Sew S' ≡ Sew S)
        (CO' : Sco S' ≡ Sco S)
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    simrel_subexec S' TC f (C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘)).
  Proof. 
    cdes BSTEP_; cdes SAJF.
    assert (ESBasicStep.t e None S S') as BSTEP.
    { econstructor; eauto. }
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (ESstep.t_load e None S S') as LSTEP.
    { econstructor; splits; auto. 
      eapply weaken_sim_add_jf; eauto. }
    constructor. 
    (* exec_sb_prcl : dom_rel (Ssb ⨾ ⦗ f □₁ fdom ⦘) ⊆₁ f □₁ fdom; *)
    { rewrite <- set_interK 
          with (s := f □₁ (C ∪₁ dom_rel (Gsb^? ⨾ ⦗I⦘)))
          at 1.
      rewrite id_inter.
      rewrite a2e_img at 1; [|apply SRCC].
      rewrite <- seqA.
      rewrite ESBasicStep.basic_step_sbEr; eauto.
      apply SRCC. }
    (* exec_ncf : ES.cf_free S (f □₁ fdom) *)
    { red. 
      rewrite <- set_interK 
          with (s := f □₁ (C ∪₁ dom_rel (Gsb^? ⨾ ⦗I⦘))).
      rewrite id_inter.
      rewrite a2e_img at 2 3; [|apply SRCC].
      rewrite !seqA.
      rewrite <- seqA with (r1 := ⦗SE S⦘).
      rewrite <- seqA with (r2 := ⦗SE S⦘).
      rewrite seqA with (r1 := ⦗SE S⦘).
      rewrite <- restr_relE with (r := Scf S').
      erewrite ESBasicStep.basic_step_cf_restr; eauto. 
      apply SRCC. }
    (* exec_rfc : (h □₁ hdom) ∩₁ SR ⊆₁ codom_rel (⦗ h □₁ hdom ⦘ ⨾ Srf) *)    
    { rewrite ESstep.load_step_rf; eauto. 
      rewrite seq_union_r, codom_union.
      apply set_subset_union_r. left.
      erewrite <- set_inter_absorb_r
        with (s := f □₁ (C ∪₁ dom_rel (Gsb^? ⨾ ⦗I⦘)))
        at 1.
      2 : { apply a2e_img. apply SRCC. }
      rewrite set_interA.
      arewrite (SE S ∩₁ SR S' ≡₁ SE S ∩₁ SR S).
      { eapply ESBasicStep.type_step_eq_dom; eauto. }          
      rewrite <- set_interA.
      rewrite set_inter_absorb_r with (s' := SE S); auto.
      { apply SRCC. }
      apply a2e_img. apply SRCC. }
    (* exec_jfeI : dom_rel Sjfe ⊆₁ dom_rel (Sew^? ⨾ ⦗ f □₁ I ⦘) *)
    { (* proof is similar to `jfe_vis`, should be refactored *)
      rewrite EW'.
      erewrite ESstep.load_step_jfe; eauto. 
      rewrite dom_union. 
      apply set_subset_union_l. split. 
      { apply SRCC. }
      unfold ES.jfe.
      rewrite <- seq_eqv_minus_lr, SSJF', seq_union_l. 
      arewrite (Sjf S ⨾ ⦗eq e⦘ ≡ ∅₂). 
      { split; [|done]. ESBasicStep.step_solver. }
      arewrite (singl_rel w e ⨾ ⦗eq e⦘ ≡ singl_rel w e) by basic_solver. 
      rewrite union_false_l.
      eapply cert_rf_ntid_iss_sb in NEW_RF.
      2-6 : apply SRCC.
      destruct NEW_RF as [Iss | SB].
      2 : admit. 
      intros x [y [SINGL nSB]].
      unfolder in SINGL. desc. subst x y.
      apply seq_eqv_l in Iss. desc.
      unfolder. do 2 eexists. splits; eauto.
      eexists. split; [apply Iss|].
      erewrite hfeq; [| apply SRCC |].
      { arewrite (e2a S' w = e2a S w).
        { erewrite basic_step_e2a_eq_dom with (S := S); eauto. 
          eapply a2e_img; eauto. apply SRCC. }
        fold (compose h (e2a S) w).
        erewrite fixset_swap; eauto.
        apply SRCC. }
      right. red. split. 
      { unfolder. do 2 eexists. splits; eauto. apply Iss. }
      apply Iss. }
    (* exec_ewI : dom_rel Sew ⊆₁ dom_rel (Sew^? ⨾ ⦗ f □₁ I ⦘) *)
    { rewrite EW'. apply SRCC. }
    (* exec_rel_iss_cov : dom_rel (Srelease ⨾ Sew^? ⨾ ⦗ f □₁ I ⦘) ⊆₁ f □₁ C; *)
    erewrite ESstep.load_step_release; eauto. 
    rewrite EW'. apply SRCC. 
  Admitted.

  Lemma simrel_cert_load_step_updh_CIcontE TC' h k k' e S'
        (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e None S S') 
        (SAJF : sim_add_jf S G sc TC TC' h k st e S')
        (EW' : Sew S' ≡ Sew S)
        (CO' : Sco S' ≡ Sco S)
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    let h' := upd h (e2a S' e) e in
    eq_dom (C ∪₁ I ∪₁ acts_set st.(ProgToExecution.G)) (upd h (e2a S' e) e) h. 
  Proof. 
    cdes BSTEP_; cdes SAJF.
    assert (ESBasicStep.t e None S S') as BSTEP.
    { econstructor; eauto. }
    red. ins. 
    rewrite updo; auto. 
    red. ins.
    destruct SX as [[Cx | Ix] | contEx].
    { eapply basic_step_cert_dom_ne; 
        eauto; try apply SRCC.
      unfold cert_dom. basic_solver. }
    { eapply issuedW in Ix.
      2 : apply SRCC.
      edestruct e2a_R. 
      { eapply simrel_cert_load_step_simrel_e2a; eauto. }
      { unfold set_collect, set_inter.
        eexists; splits; eauto.
        eapply ESBasicStep.basic_step_acts_set; eauto.
        basic_solver. }
      type_solver. }
    eapply basic_step_cert_dom_ne; 
        eauto; try apply SRCC.
    unfold cert_dom. basic_solver.
  Qed.

  Lemma simrel_cert_load_step_subexec TC' h k k' e S'
        (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e None S S') 
        (SAJF : sim_add_jf S G sc TC TC' h k st e S')
        (EW' : Sew S' ≡ Sew S)
        (CO' : Sco S' ≡ Sco S)
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    let h' := upd h (e2a S' e) e in
    simrel_subexec S' TC h' (cert_dom G TC (ES.cont_thread S' k') st'). 
  Proof. 
    simpl.
    set (h' := upd h (e2a S' e) e). 
    cdes BSTEP_; cdes SAJF.
    assert (ESBasicStep.t e None S S') as BSTEP.
    { econstructor; eauto. }
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (ESstep.t_load e None S S') as LSTEP.
    { econstructor; splits; auto. 
      eapply weaken_sim_add_jf; eauto. }
    assert (h' □₁ (cert_dom G TC (ES.cont_thread S' k') st') ≡₁ 
              h □₁ (cert_dom G TC (ES.cont_thread S k) st) ∪₁ eq e) 
      as HDOMeq. 
    { erewrite basic_step_nupd_cert_dom; eauto; try apply SRCC. 
      subst h'. 
      rewrite set_collect_union, set_collect_eq.
      rewrite upds. 
      rewrite set_collect_updo; auto.
      eapply basic_step_cert_dom_ne; eauto; apply SRCC. }

    assert (h' □₁ C ≡₁ h □₁ C) as HCeq. 
    { apply set_collect_eq_dom.
      red. ins. 
      eapply simrel_cert_load_step_updh_CIcontE; eauto.
      basic_solver. }
      
    assert (h' □₁ I ≡₁ h □₁ I) as HIeq. 
    { apply set_collect_eq_dom. 
      red. ins. 
      eapply simrel_cert_load_step_updh_CIcontE; eauto.
      basic_solver. }

    simpl. constructor. 
    { rewrite HDOMeq. 
      apply set_subset_union_r. left.
      rewrite id_union, seq_union_r, dom_union.
      unionL.
      { rewrite <- set_interK 
          with (s := h □₁ cert_dom G TC (ES.cont_thread S k) st)
          at 1.
        rewrite id_inter.
        rewrite a2e_img at 1; [|apply SRCC].
        rewrite <- seqA.
        rewrite ESBasicStep.basic_step_sbEr; eauto.
        apply SRCC. }
      rewrite ESBasicStep.basic_step_nupd_sb; eauto.
      rewrite seq_union_l, dom_union.
      unionL. 
      { arewrite_false (Ssb S ⨾ ⦗eq e⦘).
        { ESBasicStep.step_solver. }
        basic_solver. }
      rewrite dom_seq, dom_cross.
      2 : red; basic_solver. 
      erewrite cont_sb_dom_in_hhdom; eauto. }
    (* exec_ncf : ES.cf_free S (h □₁ hdom) *)
    { eapply ES.cf_free_eq.
      { by rewrite HDOMeq. }
      eapply basic_step_nupd_hdom_cf_free; eauto. }
    (* exec_rfc : (h □₁ hdom) ∩₁ SR ⊆₁ codom_rel (⦗ h □₁ hdom ⦘ ⨾ Srf) *)
    { rewrite HDOMeq. 
      rewrite set_inter_union_l.
      rewrite id_union, seq_union_l, codom_union.
      arewrite_false (⦗eq e⦘ ⨾ Srf S'). 
      { erewrite dom_rel_helper with (r := Srf S').
        2 : eapply ESstep.load_step_rf_dom; eauto.  
        arewrite_false (⦗eq e⦘ ⨾ ⦗SE S⦘). 
        { ESBasicStep.step_solver. }
        basic_solver. }
      erewrite ESstep.load_step_rf; eauto.
      relsf. split.
      { arewrite (h □₁ cert_dom G TC (ES.cont_thread S k) st ∩₁ SR S' ≡₁ 
                  h □₁ cert_dom G TC (ES.cont_thread S k) st ∩₁ SR S). 
        { erewrite <- set_inter_absorb_r
            with (s := h □₁ cert_dom G TC (ES.cont_thread S k) st)
            at 1.
          2 : { apply a2e_img. apply SRCC. }
          rewrite set_interA.
          arewrite (SE S ∩₁ SR S' ≡₁ SE S ∩₁ SR S).
          { eapply ESBasicStep.type_step_eq_dom; eauto. }          
          rewrite <- set_interA.
          rewrite set_inter_absorb_r with (s' := SE S); auto.
          apply a2e_img. apply SRCC. }
        left. by apply SRCC. }
      intros x Hx. 
      unfolder in Hx. desc. subst x.
      right. red. eexists.
      apply seq_eqv_l; splits; eauto.
      red. splits. 
      { unfolder. eexists. splits; eauto.
        apply SSJF'. basic_solver. }
      red. ins. 
      eapply basic_step_nupd_hdom_cf_free; eauto.
      apply seq_eqv_lr. 
      splits; eauto; basic_solver. }
    { admit. }
    (* exec_ewI : dom_rel Sew  ⊆₁ dom_rel (Sew^? ⨾ ⦗ h □₁ I ⦘) *)
    { rewrite EW', HIeq. apply SRCC. }
    (* exec_rel_iss_cov : dom_rel (Srelease ⨾ Sew^? ⨾ ⦗ h □₁ I ⦘) ⊆₁ h □₁ C; *)
    rewrite EW', HCeq, HIeq.
    erewrite ESstep.load_step_release; eauto.
    apply SRCC. 
  Admitted.

  Lemma simrel_cert_lbl_step TC' h k
        (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (KK : K S (k, existT _ _ st))
        (LBL_STEP : lbl_step (ES.cont_thread S k) st st')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :
    exists  h' k' S',
      ⟪ ESSTEP : (ESstep.t Weakestmo)^? S S' ⟫ /\
      ⟪ SRCC' : simrel_cert prog S' G sc TC f TC' h' k' st' st''⟫.
  Proof.
    assert (Wf G) as WF by apply SRCC.
    assert (ES.Wf S) as WfS by apply SRCC.
    assert (wf_thread_state (ES.cont_thread S k) st) as WFST. 
    { by apply SRCC. }
    assert (tc_coherent G sc TC) as TCCOH by apply SRCC.
    assert (sim_trav_step G sc TC TC') as TCSTEP.
    { red. eexists. eapply tr_step; eauto. }
    assert (tc_coherent G sc TC') as TCCOH'.
    { eapply sim_trav_step_coherence; eauto. }
    assert (cert_graph G sc TC TC' (ES.cont_thread S k) st'') as CERTG by apply SRCC. 
    destruct LBL_STEP as [lbls ILBL_STEP].
    edestruct lbl_step_cases as [lbl [lbl' CASES]]; eauto. 
    desf.
    { edestruct simrel_cert_add_jf as [k' [e [e' [S' HH]]]]; eauto 10; desf.  
      assert (ESBasicStep.t e e' S S') as BSTEP. 
      { econstructor; eauto. }
      unfold option_map in LBL'.
      destruct e'; desf.
      assert (ESstep.t_load e None S S') as LSTEP.
      { red. splits; eauto. 
        eapply weaken_sim_add_jf; eauto. }
      
      cdes ES_BSTEP_; cdes LSTEP; cdes CAJF.

      set (g' := e2a S').
      assert (g' □ Ssb S' ⊆ Gsb) as SSB.
      { admit. }
      assert (g □ Shb S ⊆ Ghb) as SHB.
      { (* We need a lemma stating that. *)
        admit. }
      assert (g' □ Shb S ⊆ Ghb) as SHB'.
      { admit. }
      assert (ES.cont_sb_dom S k × eq e ⊆ S'.(ES.sb)) as SBDSB.
      { admit. }
      assert (g' □ S'.(hb) ⊆ Ghb) as BHB.
      { erewrite ESstep.load_step_hb; eauto.
        rewrite collect_rel_union.
        unionL; auto.
        rewrite collect_rel_seqi.
        etransitivity.
        2: { apply rewrite_trans_seq_cr_l.
             apply imm_s_hb.hb_trans. }
        apply seq_mori.
        { by rewrite collect_rel_cr, SHB'. }
        rewrite collect_rel_union.
        unionL.
        { rewrite SBDSB.
          etransitivity; eauto.
          apply imm_s_hb.sb_in_hb. }
        admit. }
      
      assert (@es_consistent S' Weakestmo) as ES_CONS'.
      { econstructor; simpl.
        { eapply ecf_irr_alt. split.
          { eapply simrel_cert_load_step_hb_cf_irr; eauto. }
          eapply simrel_cert_load_step_hb_cf_thb_irr; eauto. }
        { apply jf_necf_alt. splits.
          { eapply simrel_cert_load_step_jf_ncf; eauto. }
          { eapply simrel_cert_load_step_hb_jf_ncf; eauto.  } 
          { eapply simrel_cert_load_step_hb_tjf_ncf; eauto. }
          eapply simrel_cert_load_step_hb_jf_thb_ncf; eauto. }
        { eapply simrel_cert_load_step_jfe_vis; eauto. }
        all : admit. }

      set (h' := (upd h (e2a S' e) e)).

      exists h'. exists k'. exists S'.
      splits.
      { red. right. red. 
        exists e. exists None.
        splits; auto; red; eauto 20. }
      econstructor.
      { econstructor; try by apply SRCC. 
        { admit. }
        { apply ES_CONS'. }
        { eapply basic_step_simrel_cont; eauto; apply SRCC. }
        { eapply simrel_cert_load_step_simrel_e2a; eauto. }
        { eapply basic_step_simrel_a2e_preserved; eauto; apply SRCC. }
        { eapply simrel_cert_load_step_subexec_preserved; eauto. }
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
          eapply ESstep.load_step_vis_mon; eauto. }
        (* finitIncl : SEinit ⊆₁ f □₁ GEinit *)
        erewrite ESBasicStep.basic_step_acts_init_set; eauto. apply SRCC. }
      (* cert : cert_graph G sc TC TC' (ES.cont_thread S k') state'' *)
      { erewrite ESBasicStep.basic_step_cont_thread_k; eauto. }
      (* cstate : simrel_cstate *)
      { eapply basic_step_simrel_cstate; eauto. } 
      (* tr_step : isim_trav_step G sc (ES.cont_thread S k') TC TC' *)
      { erewrite ESBasicStep.basic_step_cont_thread_k; eauto. apply SRCC. }
      { admit. }
      (* sr_a2e_h *)
      { eapply basic_step_nupd_simrel_a2e_h; eauto. }
      (* sr_exec_h *)
      { eapply simrel_cert_load_step_subexec; eauto. }
      (* hlab : eq_dom (C ∪₁ I ∪₁ contE) (Slab ∘ h) certLab; *)
      { subst h'. 
        rewrite ACTS. rewrite <- set_unionA. 
        apply eq_dom_union. split.
        { red. ins. unfold compose. 
          erewrite simrel_cert_load_step_updh_CIcontE; eauto. 
          (* here we should consider `I x` case *)
          admit. 
          (* erewrite ESBasicStep.basic_step_lab_eq_dom; eauto. *)
          (* { by apply SRCC. } *)
          (* eapply a2e_img; [apply SRCC.(sr_a2e_h)|]. *)
          (* eexists; splits; eauto. *)
          (* unfold cert_dom.  *) }
        unfolder. unfold compose. ins.
        erewrite basic_step_e2a_e; 
          eauto; try apply SRCC.
        subst. rewrite upds.
        erewrite basic_step_e2a_certlab_e; 
          eauto; try apply SRCC.
        erewrite <- basic_step_e2a_e; 
          eauto; try apply SRCC. }
      (* hfeq : eq_dom (C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘) ∩₁ GNTid qtid)) f h; *)
      subst h'. 
      red. ins.
      erewrite ESBasicStep.basic_step_cont_thread_k in SX; eauto.
      rewrite updo.
      { eapply hfeq; eauto. }
      red. ins. subst x.
      eapply basic_step_cert_dom_ne; 
        eauto; try apply SRCC.
      unfold cert_dom. by left. }

    all : admit. 
  Admitted.

  Lemma simrel_cert_step TC' h q state''
        (state : (thread_lts (ES.cont_thread S q)).(Language.state))
        (SRCC : simrel_cert prog S G sc TC f TC' h q state state'')
        (KK : K S (q, existT _ _ state))
        (KNEQ : state <> state'') :
    exists (state' : (thread_lts (ES.cont_thread S q)).(Language.state)),
      lbl_step (ES.cont_thread S q) state state'.
  Proof.
    set (thread := (ES.cont_thread S q)).
    set (REACHABLE := KK).
    admit.
    (* eapply cstate_reachable in REACHABLE; [|by apply SRCC]. *)
    (* assert ((lbl_step thread)＊ state state'') as LSTEPS. *)
    (* { apply (steps_stable_lbl_steps thread).  *)
    (*   apply restr_relE. *)
    (*   unfold restr_rel. *)
    (*   splits; auto. *)
    (*   { apply (SRC.(scont)).(contstable) in KK. auto. }  *)
    (*   apply SRCC. }  *)
    (* apply rtE in LSTEPS. *)
    (* destruct LSTEPS as [Tr|TCSTEP]; [ red in Tr; desf | ]. *)
    (* apply t_step_rt in TCSTEP. *)
    (* destruct TCSTEP as [state' [STEP _]]. *)
    (* exists state'.  *)
    (* splits; auto.  *)
  Admitted.

  Lemma simrel_cert_cc_dom TC' h q state state'
        (SRCC : simrel_cert prog S G sc TC f TC' h q state state') :
    dom_rel (Scc S ⨾ ⦗ ES.cont_sb_dom S q ⦘) ⊆₁ f □₁ I. 
  Proof. 
    admit.
  Admitted.

End SimRelCertLemmas.

End SimRelCertStep.