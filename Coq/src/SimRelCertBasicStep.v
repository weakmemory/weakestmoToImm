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
Require Import AuxRel AuxDef EventStructure BasicStep Consistency 
        LblStep CertRf CertGraph EventToAction ImmProperties
        SimRelCont SimRelEventToAction SimRelSubExec SimRel SimRelCert. 

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelCertBasicStep.

  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G : execution.

  Variable TC : trav_config.
  Variable sc : relation actid.
  Variable f : actid -> eventid.

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
  Notation "'Secf'" := (S.(Consistency.ecf)).

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

  Lemma basic_step_simrel_a2e_h TC' h k k' e e' S' 
        (st st' st'': thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e e' S S') : 
    let h' := upd_opt (upd h (e2a S' e) e) (option_map (e2a S') e') e' in 
    simrel_a2e S' h' (cert_dom G TC (ES.cont_thread S' k') st'). 
  Proof. 
    cdes BSTEP_. 
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor. eauto. }

    set (h' := upd_opt (upd h (e2a S' e) e) (option_map (e2a S') e') e').

    assert 
      (~ eq_opt (option_map (e2a S') e') (e2a S' e))
      as NEQe'.
    { unfold eq_opt.
      destruct e' as [e'|]; simpl; red; ins.
      erewrite basic_step_e2a_e with (e := e) in H; eauto.
      2-5 : apply SRCC.
      erewrite basic_step_e2a_e' in H; eauto.
      2-5 : apply SRCC.
      inv H. omega. }

    assert 
      (set_disjoint (eq (e2a S' e)) (eq_opt (option_map (e2a S') e'))) 
      as DISJe'.
    { unfold eq_opt.
      destruct e'; simpl; red; ins.
      erewrite basic_step_e2a_e in IN; eauto.
      2-5 : apply SRCC.
      erewrite basic_step_e2a_e' in IN'; eauto.
      2-5 : apply SRCC.
      inv IN. omega. }

    assert 
      (opt_same_ctor (option_map (e2a S') e') e') 
      as CTORe'.
    { unfold opt_same_ctor, option_map. by destruct e'. }

    assert 
      (eq_dom (cert_dom G TC (ES.cont_thread S k) st) h' h)
      as EQhCERTD.
    { red. ins. subst h'. 
      rewrite updo_opt; auto.
      2 : 
        unfold eq_opt, option_map; 
        destruct e'; try done;
        red; ins; subst;
        eapply basic_step_cert_dom_ne';
        try apply SRCC; eauto. 
      rewrite updo; auto. 
      red. ins. subst. 
      eapply basic_step_cert_dom_ne;
        try apply SRCC; eauto. }

    simpl. 
    eapply simrel_a2e_set_equiv. 
    { eapply basic_step_cert_dom; eauto; apply SRCC. }
    subst h'. constructor.
    
    (* a2e_inj *)
    { rewrite set_unionA.
      eapply inj_dom_union.
      { red. ins.
        rewrite !EQhCERTD in EQ; auto.
        eapply a2e_inj; eauto. apply SRCC. }
      { eapply inj_dom_union.
        { apply inj_dom_eq. }
        { apply inj_dom_eq_opt. }
        unfold option_map, eq_opt, upd_opt.
        destruct e'; [|basic_solver].
        rewrite !set_collect_eq.
        rewrite updo, !upds; auto. 
        basic_solver. }
      erewrite set_collect_eq_dom; eauto.
      rewrite set_collect_union.
      rewrite set_collect_eq.
      rewrite updo_opt; auto.
      rewrite upds.
      red. ins. destruct IN' as [IN' | IN'].
      { eapply ESBasicStep.basic_step_acts_set_ne; eauto.
        subst. eapply a2e_img; eauto. apply SRCC. }
      unfold eq_opt, option_map, upd_opt in IN'.
      destruct e' as [e'|]. 
      2 : { unfolder in IN'. by desc. }
      apply set_collect_eq in IN'.
      rewrite upds in IN'.
      eapply ESBasicStep.basic_step_acts_set_ne'; eauto.
      subst. eapply a2e_img; eauto. apply SRCC. }
        
    (* a2e_img *)
    { rewrite !set_collect_union.
      rewrite !set_subset_union_l.
      splits.
      { erewrite set_collect_eq_dom; eauto.
        rewrite a2e_img; try apply SRCC.
        eapply ESBasicStep.basic_step_acts_set_mon; eauto. }
      { rewrite set_collect_updo_opt; auto. 
        rewrite set_collect_eq.
        rewrite upds; auto.  
        erewrite ESBasicStep.basic_step_acts_set; eauto. 
        basic_solver. }
      unfold upd_opt, option_map, eq_opt. 
      destruct e'; [|basic_solver]. 
      rewrite set_collect_eq.
      rewrite upds.
      erewrite ESBasicStep.basic_step_acts_set; eauto. 
      basic_solver. }

    (* a2e_fix *)
    rewrite !fixset_union. splits. 
    { eapply fixset_eq_dom.
      { unfold eq_dom, compose. 
        intros x DOM.
        rewrite EQhCERTD; auto.
        erewrite basic_step_e2a_eq_dom; eauto.
        { by fold (compose (e2a S) h x). }
        { apply SRCC. }
        apply SRCC.(sr_a2e_h).
        basic_solver. }
      apply SRCC. }
    { unfold eq_dom, compose. 
      intros x DOM. subst x. 
      rewrite updo_opt; auto. 
      by rewrite upds. }
    unfold eq_opt, option_map, upd_opt. 
    red. ins. destruct e'; [|by exfalso].
    unfold compose. subst x. by rewrite upds. 
  Qed.

  Lemma basic_step_nupd_simrel_a2e_h TC' h k k' e S' 
        (st st' st'': thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e None S S') : 
    let h' := upd h (e2a S' e) e in
    simrel_a2e S' h' (cert_dom G TC (ES.cont_thread S' k') st'). 
  Proof.
    edestruct basic_step_simrel_a2e_h; eauto.
    unfold upd_opt, option_map in *. 
    constructor; auto.
  Qed.

  Lemma basic_step_simrel_cstate TC' h k k' e e' S' 
        (st st' st'': thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e e' S S') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    simrel_cstate S' TC k' st' st''. 
  Proof. 
    cdes BSTEP_. 
    constructor.
    (* cstate_stable : stable_state (ES.cont_thread S' k') st''; *)
    { erewrite ESBasicStep.basic_step_cont_thread_k; eauto.
      eapply cstate_stable. apply SRCC. }
    (* cstate_q_cont : Kstate (k', st'); *)
    { red. exists st'. split; auto. 
      eapply ESBasicStep.basic_step_cont_set; eauto.
      erewrite ESBasicStep.basic_step_cont_thread_k with (S' := S'); eauto.
      subst. basic_solver. }
    (* cstate_reachable : (step (ES.cont_thread S' k'))＊ st' st'' *)
    { admit. }
    (* cstate_covered : C ∩₁ GTid (ES.cont_thread S' k') ⊆₁ contE' *)
    erewrite ESBasicStep.basic_step_cont_thread_k; eauto.
    etransitivity.
    { eapply cstate_covered. apply SRCC. }
    unfold set_subset. 
    eapply preserve_event.
    eapply ilbl_steps_in_steps.
    do 2 econstructor. apply STEP. 
  Admitted.

End SimRelCertBasicStep.
