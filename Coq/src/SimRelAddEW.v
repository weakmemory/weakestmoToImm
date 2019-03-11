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
        SimRel SimRelCert SimRelCertBasicStep. 

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelAddEW.
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
  Notation "'Sval' S" := (val S.(ES.lab)) (at level 10).

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

  Notation "'Stid_' S" := (fun t x => Stid S x = t) (at level 1).
  Notation "'SNTid_' S" := (fun t x => Stid S x <> t) (at level 1).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gtid'" := (tid).
  Notation "'Gval'" := (val (G.(lab))).
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
  
  Definition sim_ews (w' : eventid) (S S' : ES.t) := fun w => 
    ⟪ wsE2Aeq : e2a S w = e2a S' w' ⟫ /\
    ⟪ wEWI : dom_rel ((Sew S)^? ⨾ ⦗ f □₁ I ⦘) w ⟫.

  Definition sim_add_ew (w' : eventid) (S S' : ES.t) : Prop :=
    ⟪ wE' : SE S' w' ⟫ /\
    ⟪ wW' : SW S' w' ⟫ /\
    ⟪ EW' : Sew S' ≡ Sew S ∪ ESstep.ew_delta (sim_ews w' S S') w' ⟫. 

  Section SimRelAddEWProps. 

    Lemma sim_ewsE w' k S S' 
          (st st' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st') :
      sim_ews w' S S' ⊆₁ SE S.
    Proof. 
      unfold sim_ews. 
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      red. ins. desc.
      generalize wEWI. 
      generalize x.
      fold (set_subset (dom_rel ((Sew S)^? ⨾ ⦗f □₁ I⦘)) (SE S)).
      rewrite ES.ewE; auto.
      arewrite (f □₁ I ⊆₁ SE S).
      { etransitivity. 
        2 : { eapply a2e_img. apply SRCC.(sim_com). }         
        basic_solver 10. }
      basic_solver.
    Qed.

    Lemma sim_ewsW w' k S S' 
          (st st' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st') :
      sim_ews w' S S' ⊆₁ SW S.
    Proof. 
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      intros x Wx. 
      unfold sim_ews in Wx. desc.
      generalize wEWI.
      generalize x.
      fold (set_subset (dom_rel ((Sew S)^? ⨾ ⦗f □₁ I⦘)) (SW S)).
      rewrite ES.ewD; auto.
      arewrite (f □₁ I ⊆₁ SW S).
      { intros y [a [Ia EQa]]. subst y.
        unfold is_w. 
        fold (compose (Slab S) f a).
        erewrite flab; [| apply SRCC | basic_solver].
        fold (is_w Glab a).
        eapply issuedW; eauto.
        apply SRCC. }
      basic_solver.
    Qed.

    Lemma sim_ews_e2a_eq w' S S' :
      e2a S □₁ sim_ews w' S S' ⊆₁ eq (e2a S' w').
    Proof. unfold sim_ews. basic_solver. Qed.

    Lemma sim_ews_lab_e2a w' k S S' 
          (st st' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st') :
      (Glab ∘ e2a S) □₁ (sim_ews w' S S') ⊆₁ eq ((Glab ∘ (e2a S')) w').
    Proof. 
      unfold compose. 
      intros a [x [WSx LABx]]. subst a.
      arewrite (e2a S x = e2a S' w'); auto.
      generalize WSx. unfold sim_ews.
      basic_solver.
    Qed.

    Lemma sim_ews_loc w' k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'')
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      (Sloc S) □₁ sim_ews w' S S' ⊆₁ eq (Sloc S' w').
    Proof. 
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      intros l [x [WSx LOCx]].
      rewrite <- LOCx.
      arewrite ((Sloc S) x = (Sloc S') x).
      { symmetry. eapply ESBasicStep.basic_step_loc_eq_dom; eauto.
        eapply sim_ewsE; eauto. }
      assert 
        (restr_rel (SE S') (same_loc (Slab S')) w' x -> (Sloc S') w' = (Sloc S') x)
        as HH.
      { basic_solver. }
      apply HH.
      eapply same_lab_u2v_dom_same_loc.
      { eapply basic_step_e2a_same_lab_u2v; eauto; apply SRCC. }
      unfolder. splits.
      { red. unfold loc, compose. 
        erewrite sim_ews_e2a_eq; eauto.
        arewrite (e2a S' x = e2a S x).
        { eapply basic_step_e2a_eq_dom; eauto.
          eapply sim_ewsE; eauto. }
        basic_solver. }
      { eapply ESBasicStep.basic_step_acts_set; eauto.
        generalize wEE'. basic_solver. }
      eapply ESBasicStep.basic_step_acts_set; eauto.
      do 2 left. eapply sim_ewsE; eauto.
    Qed.

    Lemma sim_ews_val w' k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'')
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      (Sval S) □₁ sim_ews w' S S' ⊆₁ eq (Sval S' w').
    Proof. 
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      intros v [x [WSx VALx]].
      rewrite <- VALx.
      assert (SE S x) as SEx.
      { eapply sim_ewsE; eauto. }
      unfold sim_ews in WSx. desc.
      destruct wEWI as [y [z [rEW fI]]].
      destruct fI as [EQz [a [Ia EQa]]].
      subst y z.
      assert (e2a S' (f a) = a) as EQfaE2A.
      { erewrite basic_step_e2a_eq_dom; eauto.
        { eapply a2e_fix; [apply SRCC.(sim_com)|]. 
          basic_solver 10. }
        eapply a2e_img; [apply SRCC.(sim_com)|]. 
        basic_solver 10. }
      assert (e2a S' w' = a) as EQaE2A.
      { erewrite <- wsE2Aeq; eauto.
        arewrite (e2a S x = e2a S' x).
        { symmetry. erewrite basic_step_e2a_eq_dom; eauto. }
        destruct rEW as [EQ | EW].
        { congruence. }
        rewrite <- EQfaE2A. 
        eapply e2a_ew; [apply SRCC|].
        erewrite basic_step_e2a_eq_dom 
          with (S' := S'); eauto.
        erewrite basic_step_e2a_eq_dom 
          with (S' := S'); eauto.
        { basic_solver 6. }
        eapply ES.ewE, seq_eqv_lr in EW; auto. desf. }
      subst v.
      assert (Sval S x = Gval a) as EQaVAL.
      { unfold val.
        erewrite <- flab; [| apply SRCC| basic_solver].
        unfold compose.
        destruct rEW as [EQ | EW].
        { basic_solver. }
        eapply ES.ewv; auto. }
      rewrite EQaVAL.
      destruct wEE' as [E | E'].
      { subst w'. unfold val.
        erewrite basic_step_e2a_certlab_e; eauto. 
        2-3 : apply SRCC.
        rewrite EQaE2A.
        erewrite cslab; [auto | apply SRCC |].
        do 4 left. right. 
        eapply step_mon; eauto.
        econstructor.
        admit. }
      destruct e' as [e'|]; [|done].
      unfold eq_opt in E'. subst w'.
      unfold val.
      erewrite basic_step_e2a_certlab_e'; eauto. 
      2-3 : apply SRCC.
      rewrite EQaE2A.
      erewrite cslab; [ eauto | apply SRCC |].
      do 4 left. right. 
      eapply step_mon; eauto.
      econstructor.
      admit.       
    Admitted.

    Lemma sim_ews_cf w' k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      sim_ews w' S S' ⊆₁ Scf S' w'. 
    Proof. 
      cdes BSTEP_.
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (sim_ews w' S S' ⊆₁ ES.cont_cf_dom S k) as wsKCF.
      { intros x Hx.
        assert (SE S x) as Ex.
        { eapply sim_ewsE; eauto. }
        assert (e2a S x = e2a S' w') as EQE2A.
        { unfold sim_ews in Hx. desf. }
        erewrite e2a_ninit with (e := w') in EQE2A; auto.
        2 : { eapply ESBasicStep.basic_step_acts_ninit_set; eauto.
              generalize wEE'. basic_solver. }
        erewrite e2a_ninit with (e := x) in EQE2A; auto.
        2 : { red. unfolder. split; auto.
              intros SEix. erewrite e2a_init in EQE2A; auto. congruence. }
        inversion EQE2A as [[STID SSEQ]]. 
        (* erewrite ESBasicStep.basic_step_tid_eq_dom  *)
        (*   with (x := x) *)
        (*   in STID; eauto.  *)
        (* erewrite ESBasicStep.basic_step_seqn_eq_dom  *)
        (*   with (x := x) *)
        (*   in SSEQ; eauto. *)
        assert (Stid S x = ES.cont_thread S k) as TIDxKCF. 
        { destruct wEE' as [EQ | EQopt].
          { subst w'. rewrite STID.
            eapply ESBasicStep.basic_step_tid_e; eauto. }
          unfold eq_opt in EQopt. 
          destruct e' as [e'|]; [|done].
          subst w'. rewrite STID.
          eapply ESBasicStep.basic_step_tid_e'; eauto. }
        destruct k. 
        { unfold ES.cont_cf_dom; split; auto. }
        eapply ES.seqn_lt_cont_cf_dom; eauto.
        { eapply ES.K_inEninit; eauto. }
        rewrite SSEQ. 
        destruct wEE' as [EQ | EQopt].
        { subst w'. 
          erewrite ESBasicStep.basic_step_seqn_kevent
            with (e := e); eauto. }
        unfold eq_opt in EQopt. 
        destruct e' as [e'|]; [|done].
        subst w'. 
        erewrite ESBasicStep.basic_step_seqn_e'
            with (e' := e'); eauto.
        erewrite ESBasicStep.basic_step_seqn_kevent
            with (e := e); eauto. }
      intros x Hx.
      eapply ESBasicStep.basic_step_cf; eauto.
      autounfold with ESStepDb.
      generalize wEE'. basic_solver 10.
    Qed.
      
    Lemma weaken_sim_add_ew w' k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SAEW : sim_add_ew w' S S') 
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      ESstep.add_ew (sim_ews w' S S') w' S S'.
    Proof. 
      cdes BSTEP_; cdes SAEW.
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      
      constructor; splits; auto.
      (* ewsE : ews ⊆₁ E S *)
      { eapply sim_ewsE; eauto. }
      (* ewsW : ews ⊆₁ W S *)
      { eapply sim_ewsW; eauto. }
      (* ewsRLX : ews ⊆₁ Rlx S *)
      { admit. }
      (* ewsLOC : ews ⊆₁ same_loc S' w' *)
      { intros x WSx.
        unfold same_loc.
        arewrite (Sloc S' x = Sloc S x).
        { erewrite ESBasicStep.basic_step_loc_eq_dom; eauto.
          eapply sim_ewsE; eauto. }
        erewrite sim_ews_loc; eauto.
        basic_solver. }
      (* ewsVAL : ews ⊆₁ same_val S' w' *)
      { intros x WSx.
        unfold same_val.
        arewrite (Sval S' x = Sval S x).
        { erewrite ESBasicStep.basic_step_val_eq_dom; eauto.
          eapply sim_ewsE; eauto. }
        erewrite sim_ews_val; eauto.
        basic_solver. }
      (* ewsCF : ews ⊆₁ cf S' w' *)
      { eapply sim_ews_cf; eauto. }
      (* ewsEW : ews × ews \ eq ⊆ ew S *)
      { admit. }
      (* ewsEWprcl : dom_rel (ew S ⨾ ⦗ews⦘) ⊆₁ ews *)
      admit. 
    Admitted.

    Lemma sim_add_ew_e2a_ew_eq w' k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SAEW : sim_add_ew w' S S') 
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      e2a S' □ Sew S' ⊆ eq. 
    Proof. 
      cdes BSTEP_; cdes SAEW.
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      rewrite EW'.
      rewrite collect_rel_union.
      unionL.
      { eapply simrel_cert_basic_step_e2a_eqr; eauto; apply SRCC. }
      autounfold with ESStepDb.
      rewrite csE, transp_cross.
      rewrite collect_rel_union, 
              !collect_rel_cross,
              !set_collect_eq.
      erewrite set_collect_eq_dom.
      { rewrite !sim_ews_e2a_eq. basic_solver. }
      eapply eq_dom_mori; eauto.
      2 : eapply basic_step_e2a_eq_dom; eauto.
      eapply sim_ewsE; eauto. 
    Qed.

    Lemma sim_add_ew_ew_fI w' k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SAEW : sim_add_ew w' S S') 
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      dom_rel (Sew S') ⊆₁ dom_rel ((Sew S')^? ⨾ ⦗ f □₁ I ⦘). 
    Proof.
      cdes BSTEP_; cdes SAEW.
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      rewrite EW'. 
      rewrite !dom_union.
      unionL.
      { etransitivity; [apply SRCC|]. basic_solver 10. }
      autounfold with ESStepDb.
      rewrite csE, transp_cross.
      rewrite dom_union.
      unionL.
      { rewrite dom_cross; [|red; basic_solver].
        arewrite (sim_ews w' S S' ⊆₁ dom_rel ((Sew S)^? ⨾ ⦗f □₁ I⦘)).
        { unfold sim_ews. basic_solver 10. }
        basic_solver 10. }
      arewrite (
        dom_rel (eq w' × sim_ews w' S S') ⊆₁ 
        dom_rel (eq w' × sim_ews w' S S' ⨾ ⦗f □₁ I⦘)
      ).
      { unfold sim_ews. 
        intros x [y [EQx HH]]. subst x. desc.
        destruct wEWI as [z HH].
        apply seq_eqv_r in HH.
        destruct HH as [[EQ | EW] fI].
        { subst z. exists y. basic_solver 10. }
        exists z. unfolder. splits; auto.
        { rewrite <- wsE2Aeq. symmetry.
          eapply e2a_ew; [apply SRCC|].
          basic_solver 10. }
        basic_solver 10. }
      basic_solver 10.
    Qed.

  End SimRelAddEWProps. 

End SimRelAddEW.