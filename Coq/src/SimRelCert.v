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
Require Import AuxRel AuxDef EventStructure Construction Consistency 
        LblStep CertRf CertGraph EventToAction ImmProperties
        SimRelDef SimRelProps SimRelCont.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelLemmas.

Variable prog : Prog.t.
Variable S : ES.t.
Variable G  : execution.
Variable GPROG : program_execution prog G.

Notation "'g'" := (e2a S).

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

Section EventToActionLemmas.

  Variable PROG_NINIT : ~ (IdentMap.In tid_init prog).

  Lemma basic_step_e2a_eq_dom e e' S'
        (WF : ES.Wf S)
        (BSTEP : ESstep.t_basic e e' S S') :
    eq_dom (SE S) (e2a S') (e2a S).
  Proof.
    cdes BSTEP; cdes BSTEP_.
    red. intros x. ins.
    unfold e2a.
    assert (Stid S' x = tid_init <-> Stid S x = tid_init) as AA.
    { red; split; ins;
        [ erewrite <- ESstep.basic_step_tid_eq_dom
        | erewrite ESstep.basic_step_tid_eq_dom
        ]; eauto. }
    assert ((Sloc S') x = (Sloc S) x) as BB.
    { eapply ESstep.basic_step_loc_eq_dom; eauto. }
    unfold opt_ext; desf; try by (exfalso; intuition).
    assert ((Stid S') x = (Stid S) x) as CC.
    { eapply ESstep.basic_step_tid_eq_dom; eauto. }
    assert (ES.seqn S' x = ES.seqn S x) as DD.
    { eapply ESstep.basic_step_seqn_eq_dom; eauto. }
    congruence.
  Qed.

End EventToActionLemmas.

Section SimRelCertLemmas. 

  Variable TC : trav_config.
  Variable sc : relation actid.
  Variable f : actid -> eventid.

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Notation "'fdom'" := ( C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘))) (only parsing).

  Lemma simrel_cert_graph_start TC' thread 
        (SRC : simrel_common prog S G sc TC f)
        (TR_STEP : isim_trav_step G sc thread TC TC') : 
    exists k state',
      ⟪ CERTG : cert_graph G sc TC TC' thread state' ⟫ /\
      ⟪ kTID : ES.cont_thread S k = thread ⟫ /\
      ⟪ CST_STABLE : stable_state thread state' ⟫ /\
      ⟪ CST_REACHABLE : 
          forall (state : (thread_lts thread).(Language.state))
                 (KK : K S (k, existT _ _ state)),
            (step thread)＊ state state' ⟫. 
  Proof. 
    edestruct cont_tid_state as [state [k HH]]; eauto. 
    { eapply trstep_thread_prog; eauto; apply SRC. }
    desf. 
    edestruct cert_graph_start as [state' HH]; eauto; try by apply SRC.
    { eapply isim_trav_step_thread_ninit; eauto.
      all: apply SRC. }
    { (* TODO: it should be added to simrel_common *)
      admit. }
    { (* TODO: it shoud be added to simrel_common *)
      admit. }
    { (* should follow from CsbqDOM *)
      admit. }
    desf. 
    exists k, state'. 
    splits; auto.  
    ins. 
    eapply ES.unique_K in KK;
      [| by apply SRC | by apply QQ | auto].
    simpls. inv KK.
  Admitted. 

  Lemma simrel_cert_start TC' thread
        (SRC : simrel_common prog S G sc TC f)
        (TR_STEP : isim_trav_step G sc thread TC TC') :
    exists q state state',
      ⟪ SRCC : simrel_cert prog S G sc TC f TC' f q state state' ⟫.
  Proof.
    edestruct simrel_cert_graph_start as [q [state' HH]]; eauto.
    desf.
    exists q.

    (* TODO: return the corresponding state in 'simrel_cert_graph_start'. *)
    eexists. 

    exists state'.
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

  Lemma basic_step_e2a_E0_e TC' h k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
     E0 G TC' (ES.cont_thread S k) (e2a S' e).
  Proof. 
    cdes BSTEP_. simpl in BSTEP_.
    erewrite basic_step_e2a_e; eauto using BSTEP_. 
    2-3 : eapply SRCC.
    eapply ilbl_step_E0_eindex.
    all : try apply SRCC; eauto. 
    apply STEP.
  Qed.

  Lemma basic_step_e2a_E0_e' TC' h k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e (Some e') S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
     E0 G TC' (ES.cont_thread S k) (e2a S' e').
  Proof. 
    cdes BSTEP_. simpl in BSTEP_.
    erewrite basic_step_e2a_e'; eauto. 
    2-3 : eapply SRCC.
    eapply ilbl_step_E0_eindex'.
    all : try apply SRCC; eauto. 
    { apply STEP. }
    red. ins. by subst lbl'. 
  Qed.

  Lemma basic_step_e2a_GE_e TC' h k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
     GE (e2a S' e).
  Proof. 
    cdes BSTEP_. 
    eapply E0_in_E. 
    { eapply sim_trav_step_coherence; [econstructor|]; eapply SRCC. }
    eapply basic_step_e2a_E0_e; eauto.
  Qed.

  Lemma basic_step_e2a_GE_e' TC' h k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e (Some e') S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
     GE (e2a S' e').
  Proof. 
    cdes BSTEP_.
    eapply E0_in_E. 
    { eapply sim_trav_step_coherence; [econstructor|]; eapply SRCC. }
    eapply basic_step_e2a_E0_e'; eauto.
  Qed.

  Lemma basic_step_e2a_lab_e TC' h k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
     Slab S' e = lab (ProgToExecution.G st'') (e2a S' e).
  Proof. 
    cdes BSTEP_. simpl in BSTEP_.
    assert (Gtid (e2a S' e) = ES.cont_thread S k) as GTIDe.
    { rewrite <- e2a_tid. erewrite ESstep.basic_step_tid_e; eauto. }
    assert (wf_thread_state (ES.cont_thread S k) st') as WFTS. 
    { eapply wf_thread_state_steps.
      { eapply SRCC; eauto. }
      eapply ilbl_steps_in_steps.
      do 2 econstructor. eapply STEP. }
    arewrite ((Slab S') e = lbl).
    { rewrite LAB'. unfold upd_opt, opt_ext in *.
      destruct e'; desf. 
      { rewrite updo; [|omega].
          by rewrite upds. }
        by rewrite upds. }
    edestruct lbl_step_cases as [l [l' HH]]. 
    { eapply SRCC; eauto. }
    { eapply STEP. }
    destruct HH as [AA BB].
    apply opt_to_list_app_singl in AA.
    destruct AA as [LA LB].
    subst l l'.
    erewrite steps_preserve_lab.    
    { erewrite basic_step_e2a_e.
      2-5 : eauto; apply SRCC.
      destruct BB as [BB | BB].
      { destruct BB as [_ [ACTS [LAB _]]]. 
        rewrite LAB. by rewrite upds. }
      destruct BB as [_ [ACTS [LAB HH]]].
      desf. rewrite LAB.
      unfold upd_opt.
      rewrite updo. 
      { rewrite upds. basic_solver. }
      red. intros HH. inversion HH. omega. }
    { by rewrite GTIDe. }
    { apply ilbl_steps_in_steps. 
      by rewrite GTIDe. }    
    erewrite basic_step_e2a_e.
    2-5 : eauto; apply SRCC.
    desf; apply ACTS; basic_solver.    
  Qed.

  Lemma basic_step_e2a_lab_e' TC' h k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e (Some e') S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
     Slab S' e' = lab (ProgToExecution.G st'') (e2a S' e').
  Proof. 
    cdes BSTEP_. simpl in BSTEP_.
    assert (Gtid (e2a S' e') = ES.cont_thread S k) as GTIDe.
    { rewrite <- e2a_tid. erewrite ESstep.basic_step_tid_e'; eauto. }
    assert (wf_thread_state (ES.cont_thread S k) st') as WFTS. 
    { eapply wf_thread_state_steps.
      { eapply SRCC; eauto. }
      eapply ilbl_steps_in_steps.
      do 2 econstructor. eapply STEP. }
    destruct lbl' as [lbl' | ].
    2 : { by unfold opt_same_ctor in LABEL'. }
    arewrite ((Slab S') e' = lbl').
    { rewrite LAB'. unfold upd_opt, opt_ext in *.
      by rewrite upds. }
    edestruct lbl_step_cases as [l [l' HH]]. 
    { eapply SRCC; eauto. }
    { eapply STEP. }
    destruct HH as [AA BB].
    apply opt_to_list_app_singl in AA.
    destruct AA as [LA LB].
    subst l l'.
    destruct BB as [BB | BB]; [desf|].
    erewrite steps_preserve_lab.    
    { erewrite basic_step_e2a_e'.
        2-5 : eauto; apply SRCC.
        destruct BB as [_ [ACTS [LAB HH]]].
        desf. rewrite LAB.
        unfold upd_opt.
        by rewrite upds. }
    { by rewrite GTIDe. }
    { apply ilbl_steps_in_steps. 
      by rewrite GTIDe. }    
    erewrite basic_step_e2a_e'.
    2-5 : eauto; apply SRCC.
    desf; apply ACTS; basic_solver.    
  Qed.

  Lemma basic_step_e2a_certlab_e TC' h k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
     Slab S' e = certLab G st'' (e2a S' e).
  Proof. 
    unfold certLab.
    destruct 
      (excluded_middle_informative (acts_set (ProgToExecution.G st'') (e2a S' e))) as [GCE | nGCE].
    2 : { exfalso. apply nGCE. 
          eapply dcertE; [apply SRCC|].
          eapply basic_step_e2a_E0_e; eauto. }
    eapply basic_step_e2a_lab_e; eauto.
  Qed.

  Lemma basic_step_e2a_same_lab_u2v TC' h k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e e' S S') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :
    same_lab_u2v_dom (SE S') (Slab S') (Glab ∘ (e2a S')).
  Proof. 
    cdes BSTEP_. simpl in BSTEP_.
    assert (ESstep.t_basic e e' S S') as BSTEP.
    { econstructor; eauto. }
    unfold same_lab_u2v_dom.
    intros x SEx.
    eapply ESstep.basic_step_acts_set in SEx; eauto.
    destruct SEx as [[SEx | SEx] | SEx].
    { erewrite ESstep.basic_step_lab_eq_dom; eauto. 
      unfold compose. 
        by erewrite basic_step_e2a_eq_dom; eauto; apply SRCC. }
    { subst x.
      erewrite basic_step_e2a_lab_e; eauto.
      unfold compose. 
      eapply cuplab_cert; [|eapply dcertE].
      1-2 : apply SRCC.
      eapply basic_step_e2a_E0_e; eauto. }
    destruct e' as [e' | ].
    2 : { exfalso. by unfold eq_opt in SEx. }
    unfold eq_opt in SEx. subst x.
    erewrite basic_step_e2a_lab_e'; eauto.
    unfold compose. 
    eapply cuplab_cert; [|eapply dcertE].
    1-2 : apply SRCC.
    eapply basic_step_e2a_E0_e'; eauto.    
  Qed.

  Lemma basic_step_cert_dom TC' h k k' e e' S' 
        (st st' st'': thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e e' S S') : 
    cert_dom G TC (ES.cont_thread S' k') st' ≡₁ 
             cert_dom G TC (ES.cont_thread S k) st ∪₁ 
               eq (e2a S' e) ∪₁ eq_opt (option_map (e2a S') e').
  Proof. 
    cdes BSTEP_.   
    assert (ESstep.t_basic e e' S S') as BSTEP. 
    { econstructor. eauto. }
    assert (ES.Wf S) as WFS by apply SRCC.
    unfold cert_dom. 
    erewrite ESstep.basic_step_cont_thread_k; eauto. 
    rewrite !set_unionA.
    do 2 (eapply set_union_Propere; auto). 
    edestruct lbl_step_cases as [l [l' HH]].
    { eapply wf_cont_state. apply SRCC. }
    { apply STEP. }
    destruct HH as [LBLS HH].
    apply opt_to_list_app_singl in LBLS.
    destruct LBLS as [LA LB]. subst l l'. 
    destruct HH as [HA | HB].
    { destruct HA as [_ [ACTS [_ [LBL' _]]]].
      unfold eq_opt, option_map, opt_same_ctor in *.
      destruct e'; [desf|].
      etransitivity; [eapply ACTS|].
      apply set_union_Propere; auto. 
      erewrite basic_step_e2a_e; eauto. 
      2 : { apply SRCC. }
      basic_solver. }
    destruct HB as [_ [ACTS [_ LBLS]]].
    destruct LBLS as [ordr [ordw [loc [valr [valw [LA LB]]]]]].
    unfold eq_opt, option_map, opt_same_ctor in *.
    destruct e'; [|desf].
    etransitivity; [eapply ACTS|].
    rewrite set_unionA.
    apply set_union_Propere; auto. 
    erewrite basic_step_e2a_e; eauto. 
    2 : { apply SRCC. }
    erewrite basic_step_e2a_e'; eauto. 
    apply SRCC.
  Qed.

  (* Lemma basic_step_nupd_cert_dom TC' h k k' e S'  *)
  (*       (st st' st'': thread_st (ES.cont_thread S k)) *)
  (*       (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') *)
  (*       (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e None S S') :  *)
  (*   cert_dom G TC (ES.cont_thread S' k') st' ≡₁  *)
  (*            cert_dom G TC (ES.cont_thread S k) st ∪₁ eq (e2a S' e). *)
  (* Proof.  *)
  (*   erewrite basic_step_cert_dom. *)

  Lemma basic_step_hdom_cf_free TC' h k k' e e' S' 
        (st st' st'': thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e e' S S') : 
    ES.cf_free S' (h □₁ (cert_dom G TC (ES.cont_thread S k) st) ∪₁ eq e ∪₁ eq_opt e').
  Proof. 
    eapply ESstep.basic_step_cf_free; 
      try apply SRCC; eauto. 
    eapply cfk_hdom; apply SRCC.
  Qed.

  Lemma basic_step_nupd_hdom_cf_free TC' h k k' e S' 
        (st st' st'': thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e None S S') : 
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
      ⟪ ES_BSTEP_ : ESstep.t_basic_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S' ⟫ /\
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
      ⟪ ES_BSTEP_ : ESstep.t_basic_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S' ⟫ /\
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
    { edestruct cstate_q_cont; eauto. by desf. }
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
      { eapply ghfix; eauto. }
      { apply SRCC. }
      { econstructor; eauto. }
      eapply himg; eauto. }
    erewrite basic_step_e2a_e; eauto. 
    all : apply SRCC.
  Qed.

  Lemma weaken_sim_add_jf TC' h k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') 
        (BSTEP_ : ESstep.t_basic_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'')
        (SAJF : sim_add_jf S G sc TC TC' h k st e S') : 
    ESstep.add_jf e S S'.
  Proof. 
    cdes BSTEP_; cdes SAJF.
    assert (ESstep.t_basic e e' S S') as BSTEP.
    { econstructor. eauto. }
    assert (SE S w) as SEw.
    { eapply himg; eauto. }
    assert (SE S' w) as SEw'.
    { eapply ESstep.basic_step_acts_set; eauto. basic_solver. }
    assert (SE S' e) as SEe'.
    { eapply ESstep.basic_step_acts_set; eauto. basic_solver. }
    assert (Gtid (e2a S' e) = ES.cont_thread S k) as GTIDe.
    { rewrite <- e2a_tid. erewrite ESstep.basic_step_tid_e; eauto. }
    econstructor; auto. 
    exists w; splits; auto.  
    { assert (is_w (Glab ∘ (e2a S')) w) as WW.
      { eapply cert_rfD, seq_eqv_lr in NEW_RF.
        destruct NEW_RF as [HH _].
          by unfold is_w, compose in *. }
      eapply same_lab_u2v_dom_is_w; eauto.
      { eapply basic_step_e2a_same_lab_u2v; eauto. }
      red; split; auto. }
    { assert (restr_rel (SE S') (same_loc (Slab S')) w e) as HH.
      { eapply same_lab_u2v_dom_same_loc.
        { eapply basic_step_e2a_same_lab_u2v; eauto. }
        apply restr_relE, seq_eqv_lr. 
        splits; auto. 
        eapply cert_rfl in NEW_RF.
        by unfold same_loc, loc, compose in *. }
      apply restr_relE, seq_eqv_lr in HH. 
      basic_solver. }
    assert (same_val (certLab G st'') (e2a S' w) (e2a S' e)) as SAME_VAL.
    { eapply cert_rfv_clab; eauto. apply SRCC. }
    unfold same_val, val in *.
    erewrite basic_step_e2a_certlab_e with (e := e); eauto.
    arewrite (Slab S' w = Slab S w).
    { erewrite ESstep.basic_step_lab_eq_dom; eauto. }
    assert (e2a S w = e2a S' w) as E2Aw. 
    { symmetry. eapply basic_step_e2a_eq_dom; eauto. apply SRCC. }
    rewrite <- E2Aw in *.
    eapply cert_rf_ntid_iss_sb in NEW_RF. 
    2-6: apply SRCC.
    unfolder in wHDOM. destruct wHDOM as [wa [CERTwa Hwa]].
    assert (g w = wa) as Gwwa.
    { rewrite <- Hwa.
      eapply ghfix; [apply SRCC|].
      unfolder. basic_solver. }
    arewrite (Slab S w = certLab G st'' (e2a S w)); [|auto].
    rewrite <- Hwa at 1.
    rewrite Gwwa.
    arewrite ((Slab S) (h wa) = (Slab S ∘ h) wa).
    destruct NEW_RF as [Iss | SB].
    { assert (I wa) as Iw.
      { apply seq_eqv_l in Iss. unfolder in Iss. rewrite <- Gwwa. basic_solver. }
      unfold certLab.
      destruct 
        (excluded_middle_informative (acts_set (ProgToExecution.G st'') wa)) 
        as [GCE | nGCE].
      { assert (GNtid_ (ES.cont_thread S k) wa) as HH.
        { apply seq_eqv_l in Iss. 
          destruct Iss as [[NTID _] _].
          rewrite <- Gwwa. apply NTID. }
        exfalso. apply HH. 
        eapply dcertE in GCE; [|apply SRCC].
        by destruct GCE. }
      symmetry. eapply hlabCI; [apply SRCC|].
      basic_solver. }
    symmetry. 
    edestruct sb_tid_init as [STID | INITx]; eauto. 
    { eapply hlabTHRD; [apply SRCC|].
      destruct CERTwa as [[Cwa | Iwa] | ACTSst]; auto.
      { eapply cstate_covered; [apply SRCC|].
        split; auto.
        by rewrite <- Gwwa, STID, GTIDe. }
      exfalso. destruct Iwa as [_ NTIDwa].
      apply NTIDwa.
      rewrite <- Gwwa.
      erewrite <- ESstep.basic_step_tid_e; eauto.
      by rewrite e2a_tid. }
    assert (C wa) as Cwa.
    { eapply init_covered; [apply SRCC|].
      rewrite <- Gwwa. 
      split; auto.  
      eapply gE; [apply SRCC|].
      unfolder. eauto. }
    etransitivity. 
    { eapply cslab; [apply SRCC|].
      unfold D. repeat left.
      eapply sim_trav_step_covered_le; [|eauto].
      econstructor. apply SRCC. }
    etransitivity.
    { symmetry. eapply flab; [apply SRCC|]. basic_solver. }
    unfold compose. 
    arewrite (f wa = h wa); [|auto].
    eapply hfeq; [apply SRCC|].
    by repeat left. 
  Qed.

  (* Lemma simrel_cert_load_step_jfehI TC' h k k' e S' *)
  (*       (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state)) *)
  (*       (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') *)
  (*       (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e None S S')  *)
  (*       (SAJF : sim_add_jf S G sc TC TC' h k st e S') *)
  (*       (EW' : Sew S' ≡ Sew S) *)
  (*       (CO' : Sco S' ≡ Sco S) *)
  (*       (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :  *)
  (*   dom_rel (Sjfe S') ⊆₁ dom_rel ((Sew S)^? ⨾ ⦗ h □₁ I ⦘).  *)
  (* Proof. admit. Admitted. *)

  (* Lemma simrel_cert_load_step_rfehI TC' h k k' e S' *)
  (*       (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state)) *)
  (*       (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') *)
  (*       (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e None S S')  *)
  (*       (SAJF : sim_add_jf S G sc TC TC' h k st e S') *)
  (*       (EW' : Sew S' ≡ Sew S) *)
  (*       (CO' : Sco S' ≡ Sco S) *)
  (*       (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :  *)
  (*   dom_rel (Srfe S') ⊆₁ dom_rel ((Sew S)^? ⨾ ⦗ h □₁ I ⦘).  *)
  (* Proof. admit. Admitted. *)

  Lemma simrel_cert_load_step_jfe_vis TC' h k k' e S'
        (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e None S S') 
        (SAJF : sim_add_jf S G sc TC TC' h k st e S')
        (EW' : Sew S' ≡ Sew S)
        (CO' : Sco S' ≡ Sco S)
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    dom_rel (Sjfe S') ⊆₁ (vis S'). 
  Proof. 
    cdes BSTEP_; cdes SAJF.
    assert (ESstep.t_basic e None S S') as BSTEP.
    { econstructor; eauto. }
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (ESstep.t_load e None S S') as LSTEP.
    { econstructor; splits; auto. 
      eapply weaken_sim_add_jf; eauto. }
    cdes LSTEP.
    assert (ES.Wf S') as WFS'.
    { admit. }
    destruct wHDOM as [wa [CERTwa Hwa]].
    assert (SE S w) as SEw.
    { rewrite <- Hwa.
      eapply himg; eauto. 
      unfolder; splits; eauto. }
    erewrite ESstep.load_step_jfe; eauto. 
    rewrite dom_union. 
    apply set_subset_union_l. split. 
    { etransitivity. 
      { eapply jfe_vis; apply SRCC. }
      eapply ESstep.load_step_vis_mon; eauto. }
    unfold ES.jfe.
    rewrite <- seq_eqv_minus_lr, SSJF', seq_union_l. 
    arewrite (Sjf S ⨾ ⦗eq e⦘ ≡ ∅₂). 
    { split; [|basic_solver].
      rewrite WFS.(ES.jfE).
      unfolder; splits; ins; desf; omega. }
    arewrite (singl_rel w e ⨾ ⦗eq e⦘ ≡ singl_rel w e) by basic_solver. 
    rewrite union_false_l.
    unfolder. intros x [y [[EQx EQy] nSB]]. 
    subst x y. 
    eapply cert_rf_ntid_iss_sb in NEW_RF.
    2-6 : apply SRCC.
    assert (e2a S' w = wa) as E2Aw.
    { erewrite basic_step_e2a_eq_dom; eauto. 
      rewrite <- Hwa.
      fold (compose g h wa).
      eapply ghfix; eauto. }
    eapply ESstep.load_step_vis_mon; eauto.
    destruct NEW_RF as [Iss | SB].
    { eapply fvis; [apply SRCC|].
      rewrite E2Aw in *. 
      apply seq_eqv_l in Iss.
      destruct Iss as [[NTIDwa Iwa] _].
      unfold set_collect. 
      exists wa. split; [basic_solver 10|].
      erewrite hfeq; eauto. 
      basic_solver 10. }
    edestruct sb_tid_init as [STID | INITw]; eauto. 
    { exfalso. 
      do 2 erewrite <- e2a_tid in STID.
      assert (Stid S' e <> tid_init) as TIDe.
      { erewrite ESstep.basic_step_tid_e; eauto. 
        red. ins. eapply ES.init_tid_K. 
        2: eauto. eauto. }
      assert ((⦗SEninit S'⦘ ⨾ ES.same_tid S' ⨾ ⦗SEninit S'⦘) w e) as HH. 
      { apply seq_eqv_lr. 
        unfold ES.acts_ninit_set, ES.acts_init_set.
        unfolder; splits; intuition.  
        { eapply ESstep.basic_step_acts_set; eauto. basic_solver. }
        { congruence. }
        unfold opt_ext in *. omega. }
      apply ES.same_thread in HH; auto.  
      destruct HH as [HA | HB].
      { apply seq_eqv_lr in HA.
        destruct HA as [nINITw [CRS_SB nINITe]].
        apply crsE in CRS_SB.
        destruct CRS_SB as [[AA | BB] | CC].
        { unfolder in AA. eapply ESstep.basic_step_acts_set_NE; eauto.
          desf; congruence. }
        { intuition. }
        unfold transp in CC. 
        eapply ESstep.basic_step_nupd_sb in CC; eauto.  
        destruct CC as [DD | EE].
        { eapply ES.sbE in DD; eauto.  
          apply seq_eqv_lr in DD.
          eapply ESstep.basic_step_acts_set_NE; eauto.
          desf. }
        destruct EE as [CONT_SB _].
        eapply ES.cont_sb_domE in CONT_SB; eauto. 
        eapply ESstep.basic_step_acts_set_NE; eauto. } 
      eapply basic_step_hdom_cf_free; eauto. 
      apply seq_eqv_lr. splits. 
      { left; left. unfolder; eauto. }
      { eapply HB. }
      by left; right. }
    exfalso. 
    apply nSB.
    eapply ESstep.basic_step_nupd_sb; eauto. 
    right; unfolder; splits; auto. 
    eapply ES.cont_sb_dom_Einit; eauto.
    eapply himgInit; eauto. 
    rewrite <- Hwa in *. 
    unfolder; eexists; splits; eauto. 
    { unfold sb in SB. apply seq_eqv_lr in SB. desf. }
    congruence.
  Admitted.  

  Ltac solve_by_EE EE := 
    rewrite EE; eauto;
    unfolder; splits; ins; desf; omega.

  Lemma simrel_cert_load_step_jf_ncf TC' h k k' e S'
        (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e None S S') 
        (SAJF : sim_add_jf S G sc TC TC' h k st e S')
        (EW' : Sew S' ≡ Sew S)
        (CO' : Sco S' ≡ Sco S)
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    Sjf S' ∩ Scf S' ≡ ∅₂.
  Proof. 
    cdes BSTEP_; cdes SAJF.
    assert (ESstep.t_basic e None S S') as BSTEP.
    { econstructor; eauto. }
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (ESstep.t_load e None S S') as LSTEP.
    { econstructor; splits; auto. 
      eapply weaken_sim_add_jf; eauto. }
    cdes LSTEP.
    split; [|basic_solver].
    rewrite SSJF'.
    erewrite ESstep.basic_step_nupd_cf; eauto. 
    rewrite !inter_union_r, !inter_union_l. 
    unionL.
    { eapply jf_necf_jf_ncf; apply SRCC. }
    { rewrite ES.cfE.
      unfolder; splits; ins; desf; omega. }
    { rewrite ES.jfE; auto. 
      unfolder; splits; ins; desf; omega. }
    rewrite csE, inter_union_r, transp_cross.
    unionL. 
    { unfolder. ins. desf.
      eapply cfk_hdom; eauto. 
      unfolder; eauto. }
    rewrite ES.cont_cf_domEninit; eauto. 
    unfold ES.acts_ninit_set.
    unfolder; splits; ins; desf; omega. 
  Qed.

  Lemma simrel_cert_load_step_hb_jf_ncf TC' h k k' e S'
        (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e None S S') 
        (SAJF : sim_add_jf S G sc TC TC' h k st e S')
        (EW' : Sew S' ≡ Sew S)
        (CO' : Sco S' ≡ Sco S)
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    (Shb S' ⨾ Sjf S') ∩ Scf S' ≡ ∅₂.
  Proof. 
    cdes BSTEP_; cdes SAJF.
    assert (ESstep.t_basic e None S S') as BSTEP.
    { econstructor; eauto. }
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (ESstep.t_load e None S S') as LSTEP.
    { econstructor; splits; auto. 
      eapply weaken_sim_add_jf; eauto. }
    cdes LSTEP.
    split; [|basic_solver].
    erewrite ESstep.basic_step_nupd_cf; eauto. 
    erewrite ESstep.load_step_hb; eauto. 
    relsf. rewrite !seqA.
    assert (Sjf S' ≡ ⦗SE S⦘ ⨾ Sjf S') as JFdomE.
    { eapply dom_rel_helper. 
      eapply ESstep.load_step_jf_dom; eauto. }
    rewrite JFdomE.
    arewrite (ES.cont_sb_dom S k × eq e ⨾ ⦗SE S⦘ ⨾ Sjf S' ≡ ∅₂).
    { unfolder; splits; ins; desf; omega. }
    arewrite (⦗eq e⦘ ⨾ ⦗SE S⦘ ⨾ Sjf S' ≡ ∅₂). 
    { unfolder; splits; ins; desf; omega. }
    relsf. 
    rewrite csE, transp_cross.
    rewrite <- JFdomE, SSJF'. 
    rewrite seq_union_r, !inter_union_r, !inter_union_l.
    
    unionL. 
    { apply jf_necf_hb_jf_ncf; apply SRCC. }
    { solve_by_EE ES.cfE. }
    { solve_by_EE ES.jfE. }
    2,3 : solve_by_EE hbE.

    intros x y [[z [HB [EQz _]]] [KCF EQy]]. 
    subst y z.
    assert (Scf S' x e) as CFE.
    { eapply ESstep.basic_step_nupd_cf; eauto. 
      right. basic_solver. }
    eapply basic_step_nupd_hdom_cf_free; eauto. 
    apply seq_eqv_lr; splits; eauto; [|basic_solver]. 
    left. eapply hb_hhdom; eauto. 
    basic_solver 10. 
  Qed.

  Lemma simrel_cert_load_step_hb_tjf_ncf TC' h k k' e S'
        (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e None S S') 
        (SAJF : sim_add_jf S G sc TC TC' h k st e S')
        (EW' : Sew S' ≡ Sew S)
        (CO' : Sco S' ≡ Sco S)
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    (Shb S' ⨾ (Sjf S')⁻¹) ∩ Scf S' ≡ ∅₂.
  Proof. 
    cdes BSTEP_; cdes SAJF.
    assert (ESstep.t_basic e None S S') as BSTEP.
    { econstructor; eauto. }
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (ESstep.t_load e None S S') as LSTEP.
    { econstructor; splits; auto. 
      eapply weaken_sim_add_jf; eauto. }
    cdes LSTEP.
    split; [|basic_solver].
    rewrite SSJF'.
    erewrite ESstep.basic_step_nupd_cf; eauto. 
    erewrite ESstep.load_step_hb; eauto. 
    rewrite crE, csE, transp_union, transp_cross, transp_singl_rel. 
    relsf. 
    rewrite !inter_union_r, !inter_union_l. 

    assert (singl_rel e w ⊆ eq e × SE S) as singlE.
    { unfolder. ins. desf. splits; auto. 
      eapply himg in wHDOM; eauto. }

    unionL.
    { apply jf_necf_hb_tjf_ncf; apply SRCC. }
    
    1-4, 10-14, 21-24 : solve_by_EE ES.jfE.
    1,6, 11-12, 14, 16 : solve_by_EE hbE.
    5-8 : solve_by_EE singlE.
    5 : solve_by_EE ES.cont_sb_domE.
    5 : solve_by_EE releaseE. 

    { erewrite cont_sb_dom_in_hhdom; eauto.
      rewrite seq_cross_singl_l; auto. 
      intros x y [[HDOMx EQy] CF]. subst y. 
      eapply himgNcf; eauto. 
      apply seq_eqv_lr. splits; eauto. }

    { rewrite seqA, seq_cross_singl_l; auto. 
      rewrite hb_in_HChb_sb; eauto. 
      rewrite !seq_union_l, inter_union_l.
      unionL. 
      { intros x y [HH CF].
        eapply himgNcf; eauto.  
        apply seq_eqv_lr. splits; [|apply CF|].  
        { unfolder in HH. desf.
          unfolder. unfold cert_dom. 
          eexists. splits; eauto. 
          by left; left. }
        unfolder in HH; desf. }
      intros x y [HH CF].
      eapply himgNcf; eauto.  
      apply seq_eqv_lr. splits; [|apply CF|].  
      { destruct HH as [z [SB [CONTz EQw]]].
        subst y. 
        assert ((Ssb S ⨾ ⦗ ES.cont_sb_dom S k ⦘) x z) as SBC.
        { unfolder; eauto. }
        eapply ES.cont_sb_prcl in SBC; eauto. 
        eapply cont_sb_dom_in_hhdom; eauto. 
        unfolder in SBC. desf. }
      unfolder in HH; desf. }

    all : 
      erewrite ESstep.load_step_rf, SSJF'; eauto; 
      rewrite !seq_union_l, !seq_union_r, !minus_union_l; 
      relsf; rewrite !inter_union_l; unionL.

    1,4 : solve_by_EE ES.rfE.
    1,3 : solve_by_EE ES.jfE.

    all : rewrite inclusion_minus_rel, !seqA.

    { intros x y [HH CF].
      eapply himgNcf; eauto.  
      apply seq_eqv_lr. splits; [|apply CF|].  
      { eapply release_ew_hhdom; eauto.
        unfolder. unfolder in HH.
        destruct HH as [z [REL HH]].
        destruct HH as [z' [rEW HH]].
        do 2 eexists; splits; eauto. 
        eexists; splits; eauto; desf. }
      unfolder in HH. desf. }

    intros x y [HH CF].
    eapply himgNcf; eauto.  
    apply seq_eqv_lr. splits; [|apply CF|].  
    { eapply hb_hhdom; eauto. 
      destruct HH as [z [HB HH]].      
      unfolder. 
      do 2 eexists; splits; eauto. 
      eapply release_ew_hhdom; eauto.      
      unfolder. unfolder in HH. 
      destruct HH as [z' [REL HH]].
      destruct HH as [z'' [rEW HH]].
      do 2 eexists; splits; eauto. 
      eexists; splits; eauto; desf. }
    unfolder in HH. desf. 
  Qed.    

  Lemma simrel_cert_load_step_hb_jf_thb_ncf TC' h k k' e S'
        (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e None S S') 
        (SAJF : sim_add_jf S G sc TC TC' h k st e S')
        (EW' : Sew S' ≡ Sew S)
        (CO' : Sco S' ≡ Sco S)
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    (Shb S' ⨾ Sjf S' ⨾ (Shb S')⁻¹) ∩ Scf S' ≡ ∅₂.
  Proof. 
    cdes BSTEP_; cdes SAJF.
    assert (ESstep.t_basic e None S S') as BSTEP.
    { econstructor; eauto. }
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (ESstep.t_load e None S S') as LSTEP.
    { econstructor; splits; auto. 
      eapply weaken_sim_add_jf; eauto. }
    cdes LSTEP.
    split; [|basic_solver].
    rewrite SSJF'.
    erewrite ESstep.basic_step_nupd_cf; eauto. 
    erewrite ESstep.load_step_hb; eauto.
    rewrite !seq_union_r, !seq_union_l, !seq_union_r.
    rewrite !transp_union, !transp_seq, !transp_cross, transp_eqv_rel. 
    relsf. rewrite !seqA.
    
    rewrite !inter_union_r, !inter_union_l.

    assert (singl_rel w e ⊆ SE S × eq e) as singlE.
    { unfolder. ins. desf. splits; auto. 
      eapply himg in wHDOM; eauto. }

    unionL.
    { eapply jf_necf_hb_jf_thb_ncf; eapply SRCC. }

    1-2,6-8,12-14,19-20,24-26,30-32 : solve_by_EE ES.jfE.
    1,10-11,17 : solve_by_EE hbE.
    3-8,11-15 : solve_by_EE singlE.
    
    3 : { rewrite ES.cont_sb_domE; eauto. 
          solve_by_EE hbE. }
    3 : { rewrite releaseE; eauto. 
          solve_by_EE hbE. }

    { intros x y [HH CF].
      eapply himgNcf; eauto.  
      apply seq_eqv_lr. splits; [|apply CF|]. 
      { eapply hb_hhdom; eauto. 
        destruct HH as [z [HB [z' [[EQz EQz'] HH]]]].
        subst z z'.
        unfolder; splits; eauto. } 
      unfolder in HH. desf. 
      { eapply cont_sb_dom_in_hhdom; eauto. }
      eapply hb_hhdom; eauto. 
      unfolder. do 2 eexists; splits; eauto. 
      eapply cont_sb_dom_in_hhdom; eauto. }

    rewrite ESstep.load_step_rf; eauto.   
    rewrite transp_union. relsf.
    rewrite inter_union_l. 
    unionL.
    { solve_by_EE ES.rfE. }
    
    rewrite inclusion_minus_rel.
    rewrite SSJF'. 
    rewrite !transp_seq, transp_union, transp_singl_rel.
    relsf. rewrite inter_union_l. unionL. 
    { solve_by_EE ES.jfE. }

    intros x y [HH CF].
    eapply himgNcf; eauto.  
    apply seq_eqv_lr. splits; [|apply CF|]. 
    { eapply hb_hhdom; eauto. 
      destruct HH as [z [HB [z' [[EQz EQz'] HH]]]].
      subst z z'. 
      unfolder; splits; eauto. }
    assert (((Shb S)^? ⨾ release S ⨾ (Sew S)^? ⨾ singl_rel w e) y e) as HBrREL. 
    { unfold seq, eqv_rel, transp in HH. desf. 
      unfold seq. 
      eexists; splits; eauto. 
      eexists; splits; eauto. 
      eexists; splits; eauto. 
      unfold singl_rel in *. desf. }
    destruct HBrREL as [z [[EQ | HB] RELew]].
    { subst z. 
      eapply release_ew_hhdom; eauto. 
      destruct RELew as [z [REL HX]].
      destruct HX as [z' [rEW [EQz' _]]].
      subst z'. 
      do 2 eexists; splits; eauto. 
      eexists; splits; eauto; desf. }
    eapply hb_hhdom; eauto. 
    unfolder. exists z, z. splits; auto.
    eapply release_ew_hhdom; eauto. 
    destruct RELew as [z' [REL HX]].
    destruct HX as [z'' [rEW [EQz'' _]]].
    subst z''. 
    do 2 eexists; splits; eauto. 
    eexists; splits; eauto; desf. 
  Qed.
    
  Lemma simrel_cert_esstep_e2a_eqr TC' h k st st' e e' S' r r' r''
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st') 
        (ESSTEP : ESstep.t_basic e e' S S')
        (restrE : r ≡ ⦗ SE S ⦘ ⨾ r ⨾ ⦗ SE S ⦘)
        (rEQ : r' ≡ r) 
        (rIN : (e2a S) □ r ⊆ r'') : 
    (e2a S') □ r' ⊆ r''.
  Proof. 
    rewrite rEQ, restrE, collect_rel_eq_dom.
    { rewrite <- restrE; eauto. }
    all: eapply basic_step_e2a_eq_dom; eauto; apply SRCC.  
  Qed.

  Lemma simrel_cert_lbl_step TC' h k
        (st st' st'': (thread_lts (ES.cont_thread S k)).(Language.state))
        (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
        (KK : K S (k, existT _ _ st))
        (LBL_STEP : lbl_step (ES.cont_thread S k) st st')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :
    exists  h' k' S',
      ⟪ ESSTEP : (ESstep.t Weakestmo)^? S S' ⟫ /\
      ⟪ KK' : (ES.cont_set S') (k', existT _ _ st') ⟫ /\
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
      assert (ESstep.t_basic e e' S S') as BSTEP. 
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
        { admit. }
        { apply jf_necf_alt. splits.
          { eapply simrel_cert_load_step_jf_ncf; eauto. }
          { eapply simrel_cert_load_step_hb_jf_ncf; eauto.  } 
          { eapply simrel_cert_load_step_hb_tjf_ncf; eauto. }
          eapply simrel_cert_load_step_hb_jf_thb_ncf; eauto. }
        { eapply simrel_cert_load_step_jfe_vis; eauto. }
        all : admit. }

      exists (upd h (e2a S' e) e).
      exists k'. exists S'.
      splits.
      { red. right. red. 
        exists e. exists None.
        splits; auto; red; eauto 20. }
      { admit. }
      econstructor.
      { econstructor; try by apply SRCC. 
        { admit. }
        { apply ES_CONS'. }
        { eapply basic_step_simrel_cont; eauto; apply SRCC. }
        (* g' □₁ SE' ⊆₁ GE *)
        { rewrite ESstep.basic_step_nupd_acts_set; eauto.  
          rewrite set_collect_union. 
          apply set_subset_union_l. 
          split. 
          { erewrite set_collect_eq_dom; [eapply SRCC|].
            eapply basic_step_e2a_eq_dom; eauto. } 
          rewrite set_collect_eq.
          apply eq_predicate. 
          eapply basic_step_e2a_GE_e; eauto. }
        (* gEinit : GEinit ⊆₁ g □₁ SEinit *)
        { admit. }
        (* grmw : g □ Srmw ⊆ Grmw *)
        { eapply simrel_cert_esstep_e2a_eqr;
          [| | apply ES.rmwE | eapply ESstep.basic_step_nupd_rmw | apply SRCC];
          eauto. }
        (* gjf  : g □ Sjf  ⊆ Gvf *)
        { rewrite SSJF', collect_rel_union. 
          unionL. 
          { rewrite ES.jfE; auto. 
            erewrite collect_rel_eq_dom.
            { rewrite <- ES.jfE; auto. 
              eapply SRCC. }
            all: eapply basic_step_e2a_eq_dom; eauto. }
          rewrite collect_rel_singl. 
          unfolder; ins; desf.
          eapply vf_in_furr; [by apply SRCC|]. 
          eapply cert_rf_in_vf, NEW_RF. }
        (* gew  : g □ Sew  ⊆ ⦗I⦘ *)
        { eapply simrel_cert_esstep_e2a_eqr; 
          [| | apply ES.ewE | eapply EW' | apply SRCC];
          eauto. }
        (* gco  : g □ Sco  ⊆ Gco *)
        { eapply simrel_cert_esstep_e2a_eqr; 
          [| | apply ES.coE | eapply CO' | apply SRCC];
          eauto. } 
        all : admit. }
      1-15 : admit.
      (* himgNcf : ES.cf_free S (h □₁ hdom) *)
      { eapply ES.cf_free_eq.
        { symmetry. etransitivity.
          { eapply set_collect_more; [eauto|].
            etransitivity.
            { eapply basic_step_cert_dom; eauto. }
            unfold eq_opt, option_map. 
            rewrite set_union_empty_r. 
            eauto. } 
          rewrite set_collect_union.
          erewrite set_collect_updo.
          2 : admit. 
          rewrite set_collect_eq.
          by rewrite upds. }
        eapply basic_step_nupd_hdom_cf_free; eauto. }
      all : admit. }
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

End SimRelLemmas.