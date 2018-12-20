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
        SimRelDef SimRelProps.

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

Section SimRelContLemmas.

  Variable TC : trav_config.
  Variable f : actid -> eventid.

  Variable WF : ES.Wf S.
  
  Variable SRK : simrel_cont prog S G TC f.

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Lemma basic_step_simrel_cont k k' e e' S'
        (st st' : thread_st (ES.cont_thread S k))
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e e' S S') : 
    simrel_cont prog S' G TC f.
  Proof. 
    cdes BSTEP_.
    assert (ESstep.t_basic e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (Stid S' (opt_ext e e') = ES.cont_thread S k) as TIDee.
    { edestruct e'; simpl;
        [eapply ESstep.basic_step_tid_e' | eapply ESstep.basic_step_tid_e];
        eauto. }
    split.
    { intros kk lang st'' INK.  
      eapply ESstep.basic_step_cont_set in INK; eauto.
      unfold set_union in INK; desf.
      { erewrite ESstep.basic_step_cont_thread; eauto.
          by eapply SRK in INK. }
      unfold ES.cont_thread.
      rewrite TIDee.
      eapply SRK; eauto. }
    { intros kk st'' KK. 
      eapply ESstep.basic_step_cont_set in KK; eauto.
      unfold set_union in KK. 
      destruct KK as [KK | KK].
      { erewrite ESstep.basic_step_cont_thread; eauto.
        apply SRK.
        erewrite <- ESstep.basic_step_cont_thread; eauto. }
      assert (kk = CEvent (opt_ext e e')) as kkEQ.
      { by inversion KK. }
      rewrite <- kkEQ in *.
      assert (ES.cont_thread S' kk = (ES.cont_thread S k)) as Hkk.
      { subst kk. unfold ES.cont_thread at 1. apply TIDee. }
      rewrite Hkk in *. 
      inversion KK as [HH].
      apply inj_pair2 in HH. 
      rewrite <- HH.
      eapply wf_thread_state_steps.
      { eapply SRK; eauto. }
      eapply ilbl_steps_in_steps.
      do 2 econstructor. 
      eapply STEP. }
    { intros kk st'' KK. 
      eapply ESstep.basic_step_cont_set in KK; eauto.
      unfold set_union in KK. 
      destruct KK as [KK | KK].
      { erewrite ESstep.basic_step_cont_thread; eauto.
        apply SRK.
        erewrite <- ESstep.basic_step_cont_thread; eauto. }
      assert (kk = CEvent (opt_ext e e')) as kkEQ.
      { by inversion KK. }
      rewrite <- kkEQ in *.
      assert (ES.cont_thread S' kk = (ES.cont_thread S k)) as Hkk.
      { subst kk. unfold ES.cont_thread at 1. apply TIDee. }
      rewrite Hkk in *. 
      inversion KK as [HH].
      apply inj_pair2 in HH. 
      rewrite <- HH.
      simpls. 
      unfold ilbl_step in STEP.
      apply seqA in STEP.
      apply seq_eqv_r in STEP.
      desf. }
    { intros thread lprog INP.
      edestruct SRK.(contrun) as [st'' [Kinit ISTEP]]; eauto.    
      eexists; split; eauto.
      eapply ESstep.basic_step_cont_set; eauto.
      left. eauto. }
    { intros thread st'' KK. 
      eapply ESstep.basic_step_cont_set in KK; eauto.
      unfold set_union in KK. 
      destruct KK as [KK | KK].
      { by eapply SRK. }
      exfalso. inversion KK. }
    { intros x st'' KK. 
      eapply ESstep.basic_step_cont_set in KK; eauto.
      unfold set_union in KK. 
      destruct KK as [KK | KK].
      { assert (SE S x) as SEx.
        { eapply ES.K_inEninit; eauto. }
        erewrite ESstep.basic_step_seqn_eq_dom; eauto.
        eapply SRK. erewrite <- ESstep.basic_step_tid_eq_dom; eauto. }
      assert (x = opt_ext e e') as xEQ.
      { by inversion KK. }
      rewrite xEQ in *. 
      rewrite TIDee in KK. 
      inversion KK as [HST].
      apply inj_pair2 in HST. 
      rewrite <- HST.
      simpls.
      edestruct lbl_step_cases as [l [l' HH]]; eauto.
      { eapply contwf; eauto. }
      edestruct HH as [EE _].
      apply opt_to_list_app_singl in EE.
      destruct EE as [eqLBL eqLBL'].
      edestruct e'; simpl.
      { destruct HH as [_ [HH | HH]]. 
        { destruct HH as [_ [_ [_ [LBL _]]]].
          subst l'. rewrite LBL in LABEL'. exfalso. auto. } 
        destruct HH as [IDX _]. 
        erewrite IDX. simpl. 
        erewrite ESstep.basic_step_seqn_e'; eauto.
        2 : { (* TODO: refactor basic_step_seqn lemmas to get rid of this assumption *)
          admit. }             
        arewrite (eindex st = ES.seqn S' e); [|omega].
        edestruct k. 
        { erewrite continit; eauto.
          erewrite ESstep.basic_step_seqn_kinit; eauto. }
        erewrite contseqn; eauto.
        erewrite <- ESstep.basic_step_seqn_kevent; eauto.
        admit. }
      destruct HH as [_ [HH | HH]]. 
      { destruct HH as [IDX _]. 
        erewrite IDX. simpl. 
        edestruct k. 
        { erewrite continit; eauto.
          erewrite ESstep.basic_step_seqn_kinit; eauto. }
        erewrite contseqn; eauto.
        erewrite <- ESstep.basic_step_seqn_kevent; eauto.
        admit. }
      destruct HH as [_ [_ [_ HH]]].
      destruct HH as [ordr [ordw [loc [valr [vaw [_ LBL]]]]]].
      subst l'. rewrite LBL in LABEL'. exfalso. auto. }
    intros a st'' PC KK. 
    eapply ESstep.basic_step_cont_set in KK; eauto.
    unfold set_union in KK. 
    destruct KK as [KK | KK].
    { eapply contpc; eauto. }
    exfalso. 
    (* we need property like `pc < state.eindex` *)
    admit. 
  Admitted.  

  Lemma basic_step_e2a_e k k' e e' S' 
        (st st' : thread_st (ES.cont_thread S k))
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e e' S S') :
    e2a S' e = ThreadEvent (ES.cont_thread S k) (st.(eindex)).
  Proof. 
    cdes BSTEP_.
    assert (ESstep.t_basic e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (SE S' e) as SEe. 
    { eapply ESstep.basic_step_acts_set; eauto. basic_solver. }
    unfold e2a. 
    destruct (excluded_middle_informative ((Stid S') e = tid_init)) as [INIT | nINIT]. 
    { exfalso. eapply ESstep.basic_step_acts_ninit_set_e; eauto.
      unfold ES.acts_init_set. basic_solver. } 
    erewrite ESstep.basic_step_tid_e; eauto.  
    edestruct k; simpl.  
    { erewrite ESstep.basic_step_seqn_kinit; [erewrite continit| | |]; eauto. }
    erewrite ESstep.basic_step_seqn_kevent; eauto. 
    { erewrite contseqn; eauto. }
    (* TODO: refactor basic_step_seqn lemmas to get rid of this assumption *)
    admit. 
  Admitted.

  Lemma basic_step_e2a_e' k k' e e' S' 
        (st st' : thread_st (ES.cont_thread S k))
        (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e (Some e') S S') :
    e2a S' e' = ThreadEvent (ES.cont_thread S k) (1 + st.(eindex)).
  Proof. 
    cdes BSTEP_.
    assert (ESstep.t_basic e (Some e') S S') as BSTEP.
    { econstructor; eauto. }
    assert (SE S' e') as SEe'. 
    { eapply ESstep.basic_step_acts_set; eauto. basic_solver. }
    unfold e2a. 
    destruct (excluded_middle_informative ((Stid S') e' = tid_init)) as [INIT | nINIT]. 
    { exfalso. eapply ESstep.basic_step_acts_ninit_set_e'; eauto.
      unfold ES.acts_init_set. basic_solver. } 
    erewrite ESstep.basic_step_tid_e'; eauto.  
    erewrite ESstep.basic_step_seqn_e'; eauto.
    edestruct k; simpl.  
    { erewrite ESstep.basic_step_seqn_kinit; [erewrite continit| | |]; eauto. }
    erewrite ESstep.basic_step_seqn_kevent; eauto. 
    { erewrite contseqn; eauto. }
    (* TODO: refactor basic_step_seqn lemmas to get rid of this assumption *)
    all: admit. 
  Admitted. 

End SimRelContLemmas.

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
        2-4 : eauto; apply SRCC.
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
    2-4 : eauto; apply SRCC.
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
        2-4 : eauto; apply SRCC.
        destruct BB as [_ [ACTS [LAB HH]]].
        desf. rewrite LAB.
        unfold upd_opt.
        by rewrite upds. }
    { by rewrite GTIDe. }
    { apply ilbl_steps_in_steps. 
      by rewrite GTIDe. }    
    erewrite basic_step_e2a_e'.
    2-4 : eauto; apply SRCC.
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

    exists (CEvent S.(ES.next_act)). 
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
      admit. }
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
        { admit. }
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
      all : admit. }
    all : admit. 

      (*
        (* jf_vis *)
        { rewrite JF'. 
          apply inclusion_union_l.
          { etransitivity.
            { eapply scons. apply SRCC. }
            apply union_mori.
            { eapply ESstep.basic_step_sb_mon. eauto. }
            apply cross_mori. 
            { eapply ESstep.step_vis_mon; eauto. } 
            eapply ESstep.basic_step_acts_set_mon; eauto. }
          destruct (excluded_middle_informative (sb G w a)) as [waSB | waNSB].
          { apply inclusion_union_r; left. 
            admit. }
          (* apply (SRCC.(cert).(new_rf_iss_sb)) in RFwa. *)
          (* unfold union in RFwa; desf.  *)
          assert (I w) as Iw.
          { apply (SRCC.(cert).(new_rf_iss_sb)) in RFwa.
            unfolder in RFwa; desf. }
          apply inclusion_union_r; right. 
          unfolder; ins; splits; desf.
          2: cdes ES_BSTEP_; unfold opt_ext in EVENT'; omega.
          erewrite <- SRCC.(hfeq). 
          { eapply ESstep.step_vis_mon; eauto; apply SRCC. 
            unfolder.
            eexists; splits; eauto; right; repeat eexists; splits; eauto; desf. }
          right.
          unfolder; splits. 
          { right; repeat eexists; eauto. }
          unfold not; ins; apply waNSB. 
          destruct H as [y [SBqdom wEQ]].
          admit. }
        (* erewrite ESstep.e2a_step_eq_dom with (S:=S) in wEQ; eauto. *)
        (* [ | by apply SRC | admit | admit ]. *)
        (* eapply gsb; (* TODO: gsb should not depend on simrel *)  *)
        (*   [ by eauto | by eauto | admit | ].  *)
        (* unfolder; repeat eexists; splits; eauto.  *)
        (* unfold ES.cont_sb_dom in SBqdom; desf. *)
        (* { admit. } *)
        (* unfold set_inter in SBqdom. *)
        (* destruct SBqdom as [yTID ySBDOM]. *)
        (* unfold dom_rel in ySBDOM.  *)
        (* destruct ySBDOM as [y' yy'SBrefl]. *)
        (* admit. } *)
        
        (* hb_jf_not_cf *)
        { cdes ES_BSTEP_. 
          
          assert (eq (h w) ⊆₁ h □₁ cert_dom S G TC state q) as hwInHDOM. 
          { rewrite <- collect_eq.
            apply set_collect_mori; auto. 
            admit.
            (* arewrite (eq w ⊆₁ dom_rel new_rf). *)
            (* { autounfold with unfolderDb. *)
            (*   ins; desf; eexists; eauto. } *)
          (* eapply new_rf_dom; eauto. *) }

          unfold same_relation; splits; [|by basic_solver]. 
          erewrite ESstep.load_step_hb; eauto.
          rewrite JF'.
          rewrite ESstep.basic_step_nupd_cf; eauto.
          rewrite transp_union, transp_singl_rel, crE.
          relsf.
          rewrite !inter_union_l.
          rewrite !inter_union_r.
          repeat apply inclusion_union_l.

          all: try (
                   try rewrite ES.jfE;
                   try rewrite releaseE;
                   try rewrite hbE; 
                   try (rewrite ES.cont_sb_domE; eauto);
                   try (arewrite (singl_rel (ES.next_act S) (h w) ⊆ eq e × SE S)
                         by autounfold with unfolderDb; ins; desf);
                   try (arewrite (singl_rel (h w) (ES.next_act S) ⊆ SE S × eq e)
                         by autounfold with unfolderDb; ins; desf);
                     by ESstep.E_seq_e
                 ).

          { apply SRCC. }

          { rewrite seq_incl_cross.
            { rewrite <- restr_cross, restr_relE. 
              apply SRCC.(himgNcf). }
            { rewrite dom_cross; [|red; basic_solver]. 
              eapply sbk_in_hhdom; eauto. }
              by rewrite codom_singl_rel. } 

          { rewrite !seqA.
            rewrite hb_in_HChb_sb; eauto. 
            rewrite !seq_union_l. 
            rewrite inter_union_l.
            unionL.
            2: { rewrite <- !seqA.
                 rewrite sbk_in_hhdom; eauto.
                 rewrite seq_incl_cross.
                 { rewrite <- restr_cross, restr_relE. 
                   apply SRCC.(himgNcf). }
                 2: by rewrite codom_singl_rel.
                 admit. }
            rewrite seq_incl_cross.
            { rewrite <- restr_cross, restr_relE. 
              apply SRCC.(himgNcf). }
            { admit. }
            (* rewrite !set_collect_union. *)
            (* basic_solver 10. } *)
            rewrite !codom_seq.
              by rewrite codom_singl_rel. }
          
          { rewrite !seqA. 
            rewrite seq_incl_cross.
            { rewrite <- restr_cross, restr_relE.
              apply SRCC.(himgNcf). }
            { admit. 
            (* rewrite releaseC; eauto. 
            rewrite dom_seq.
            rewrite !set_collect_union.
            basic_solver 10. *) }
            rewrite !codom_seq.
            rewrite codom_singl_rel; auto. } 

          rewrite !seqA.
          rewrite hb_in_HChb_sb; eauto. 
          rewrite !seq_union_l. 
          rewrite inter_union_l.
          apply inclusion_union_l.  
          2: { rewrite <- !seqA.
               admit. 
          (* rewrite releaseC; eauto. 
          rewrite !seqA.
          rewrite <- seqA.
          rewrite seq_incl_cross.
          { rewrite <- restr_cross, restr_relE. 
              by rewrite SRCC.(himgNcf). }
          { admit. }
          rewrite !codom_seq.
            by rewrite codom_singl_rel. *) }
          rewrite seq_incl_cross.
          { rewrite <- restr_cross, restr_relE. 
            apply SRCC.(himgNcf). }
          { admit. }
          (* rewrite !set_collect_union. *)
          (* basic_solver 10. } *)
          rewrite !codom_seq.
          rewrite codom_singl_rel; auto. }
        
        { admit. }

        { cdes ES_BSTEP_.

          red; split; [|basic_solver].
          rewrite JF', ESstep.basic_step_cf; eauto. 
          rewrite !csE.
          rewrite !transp_cross.
          rewrite !inter_union_l.
          rewrite !inter_union_r. 
          unfold eq_opt.
          relsf.
          rewrite !unionA.
          repeat apply inclusion_union_l.

          all: try (
                   try rewrite ES.jfE;
                   try rewrite ES.cfE;
                     by ESstep.E_seq_e
                 ).

          { apply SRCC. }
          
          { unfolder. 
            intros x y [[EQx _] [CONTCFx _]].
            rewrite EQx in *. 
            eapply cfk_hdom; eauto. 
            unfold set_inter; split; eauto.
            unfold set_collect.
            eexists; split; eauto. }
          
          unfolder. 
          intros x y [[EQx _] [EQe _]].
          rewrite EQx in EQe.
          rewrite <- EQe in hwInSE.
          unfold "SE" in hwInSE.
          omega. }

        all: admit. }
      *)

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