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
Require Import BasicStep.
Require Import AddEW.
Require Import Step.
Require Import Consistency.
Require Import Execution.
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
Require Import ProgES.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelAddEW.
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
  Notation "'Smod' S" := (Events.mod S.(ES.lab)) (at level 10).
  Notation "'Sloc' S" := (Events.loc S.(ES.lab)) (at level 10).
  Notation "'Sval' S" := (Events.val S.(ES.lab)) (at level 10).

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

  Notation "'SPln' S"    := (fun a => is_true (is_only_pln S.(ES.lab) a)) (at level 10).
  Notation "'SORlx' S"   := (fun a => is_true (is_only_rlx S.(ES.lab) a)) (at level 10).
  Notation "'SRlx' S"    := (fun a => is_true (is_rlx S.(ES.lab) a)) (at level 10).
  Notation "'SRel' S"    := (fun a => is_true (is_rel S.(ES.lab) a)) (at level 10).
  Notation "'SAcq' S"    := (fun a => is_true (is_acq S.(ES.lab) a)) (at level 10).
  Notation "'SAcqrel' S" := (fun a => is_true (is_acqrel S.(ES.lab) a)) (at level 10).
  Notation "'SSc' S"     := (fun a => is_true (is_sc S.(ES.lab) a)) (at level 10).

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

  Notation "'kE' S" := (fun k => ES.cont_sb_dom S k) (at level 1, only parsing).
  Notation "'ktid' S" := (fun k => ES.cont_thread S k) (at level 1, only parsing).

  Notation "'certX' S" := (fun k => (X ∩₁ SNTid_ S (ktid S k)) ∪₁ (kE S k)) (at level 1, only parsing).
  
  Definition sim_ews (w' : eventid) (S S' : ES.t) := fun w => 
    ⟪ wsnREL : ~ SRel S w ⟫ /\               
    ⟪ wsE2Aeq : e2a S w = e2a S' w' ⟫ /\
    ⟪ wEWI : dom_rel (Sew S ⨾ ⦗ X ∩₁ e2a S ⋄₁ I ⦘) w ⟫.

  Definition sim_add_ew (w' : eventid) (S S' : ES.t) : Prop :=
    ⟪ wE' : SE S' w' ⟫ /\
    ⟪ wW' : SW S' w' ⟫ /\
    ⟪ EW' : Sew S' ≡ Sew S ∪ ew_delta (sim_ews w' S S') w' ⟫. 

  Section SimRelAddEWProps. 

    Lemma sim_ewsE w' k S S' 
          (st st' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st') :
      sim_ews w' S S' ⊆₁ SE S.
    Proof. 
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      unfold sim_ews. 
      red. ins. desc.
      red in wEWI. desc.
      apply seq_eqv_r in wEWI.
      destruct wEWI as [EW _].
      apply ES.ewE in EW; auto.
      generalize EW. basic_solver.
    Qed.

    Lemma sim_ewsW w' k S S' 
          (st st' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st') :
      sim_ews w' S S' ⊆₁ SW S.
    Proof. 
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      unfold sim_ews. 
      red. ins. desc.
      red in wEWI. desc.
      apply seq_eqv_r in wEWI.
      destruct wEWI as [EW _].
      apply ES.ewD in EW; auto.
      generalize EW. basic_solver.
    Qed.

    Lemma sim_ewsRLX w' k S S'
          (st st' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st') :
      sim_ews w' S S' ⊆₁ set_compl (SRel S).
    Proof. unfold sim_ews. basic_solver. Qed.

    Lemma sim_ews_e2a_eq w' S S' :
      e2a S □₁ sim_ews w' S S' ⊆₁ eq (e2a S' w').
    Proof. unfold sim_ews. basic_solver. Qed.

    Lemma sim_ews_lab_e2a w' k S S' 
          (st st' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st') :
      (Glab ∘ e2a S) □₁ (sim_ews w' S S') ⊆₁ eq ((Glab ∘ (e2a S')) w').
    Proof. 
      unfold compose. 
      intros a [x [WSx LABx]]. subst a.
      arewrite (e2a S x = e2a S' w'); auto.
      generalize WSx. unfold sim_ews.
      basic_solver.
    Qed.

    Lemma sim_ews_mod w' k k' e e' S S' 
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S') 
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'')
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      (Smod S) □₁ sim_ews w' S S' ⊆₁ eq (Smod S' w').
    Proof. 
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      intros l [x [WSx MODx]].
      rewrite <- MODx.
      arewrite ((Smod S) x = (Smod S') x).
      { symmetry. eapply basic_step_mod_eq_dom; eauto.
        eapply sim_ewsE; eauto. }
      assert 
        (restr_rel (SE S') (same_mod (Slab S')) w' x -> (Smod S') w' = (Smod S') x)
        as HH.
      { basic_solver. }
      apply HH.
      eapply same_lab_u2v_dom_same_mod.
      { eapply basic_step_e2a_same_lab_u2v; eauto; apply SRCC. }
      unfolder. splits.
      { red. unfold Events.mod, compose. 
        erewrite sim_ews_e2a_eq; eauto.
        arewrite (e2a S' x = e2a S x).
        { eapply basic_step_e2a_eq_dom; eauto.
          eapply sim_ewsE; eauto. }
        basic_solver. }
      { eapply basic_step_acts_set; eauto.
        generalize wEE'. basic_solver. }
      eapply basic_step_acts_set; eauto.
      do 2 left. eapply sim_ewsE; eauto.
    Qed.

    Lemma sim_ews_loc w' k k' e e' S S' 
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S') 
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'')
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      (Sloc S) □₁ sim_ews w' S S' ⊆₁ eq (Sloc S' w').
    Proof. 
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      intros l [x [WSx LOCx]].
      rewrite <- LOCx.
      arewrite ((Sloc S) x = (Sloc S') x).
      { symmetry. eapply basic_step_loc_eq_dom; eauto.
        eapply sim_ewsE; eauto. }
      assert 
        (restr_rel (SE S') (same_loc (Slab S')) w' x -> (Sloc S') w' = (Sloc S') x)
        as HH.
      { basic_solver. }
      apply HH.
      eapply same_lab_u2v_dom_same_loc.
      { eapply basic_step_e2a_same_lab_u2v; eauto; apply SRCC. }
      unfolder. splits.
      { red. unfold Events.loc, compose. 
        erewrite sim_ews_e2a_eq; eauto.
        arewrite (e2a S' x = e2a S x).
        { eapply basic_step_e2a_eq_dom; eauto.
          eapply sim_ewsE; eauto. }
        basic_solver. }
      { eapply basic_step_acts_set; eauto.
        generalize wEE'. basic_solver. }
      eapply basic_step_acts_set; eauto.
      do 2 left. eapply sim_ewsE; eauto.
    Qed.

    Lemma sim_ews_val w' k k' e e' S S' 
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S') 
          (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'')
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      (Sval S) □₁ sim_ews w' S S' ⊆₁ eq (Sval S' w').
    Proof. 
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      intros v [x [WSx VALx]].
      rewrite <- VALx.
      assert (SE S x) as SEx.
      { eapply sim_ewsE; eauto. }
      unfold sim_ews in WSx. desc.
      destruct wEWI as [y [z [EW HH]]].
      destruct HH as [EQz [Xz Iz]]. subst z.
      arewrite (Sval S' w' = Events.val (certLab G st'') (e2a S' w')).
      { destruct wEE' as [EQe | EQe'].
        { subst w'. unfold Events.val. 
          erewrite basic_step_e2a_certlab_e; 
            eauto; apply SRCC. }
        unfold eq_opt in *. 
        destruct e' as [e'|]; [|done].
        subst w'. unfold Events.val. 
        erewrite basic_step_e2a_certlab_e'; 
          eauto; apply SRCC. }
      rewrite <- wsE2Aeq.
      arewrite (e2a S x = e2a S y).
      { eapply e2a_ew; [apply SRCC|]. basic_solver 10. }
      arewrite (Sval S x = Sval S y).
      { apply ES.ewv; auto. }
      unfold Events.val. erewrite ex_cov_iss_cert_lab.
      { by unfold compose. }
      { apply SRCC. }
      basic_solver.
    Qed.

    Lemma sim_ews_cf w' k k' e e' S S' 
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S') 
          (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      sim_ews w' S S' ⊆₁ Scf S' w'. 
    Proof. 
      cdes BSTEP_.
      assert (basic_step e e' S S') as BSTEP.
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
        2 : { eapply basic_step_acts_ninit_set; eauto.
              generalize wEE'. basic_solver. }
        erewrite e2a_ninit with (e := x) in EQE2A; auto.
        2 : { red. unfolder. split; auto.
              intros SEix. erewrite e2a_init in EQE2A; auto. congruence. }
        inversion EQE2A as [[STID SSEQ]]. 
        assert (Stid S x = ES.cont_thread S k) as TIDxKCF. 
        { destruct wEE' as [EQ | EQopt].
          { subst w'. rewrite STID.
            eapply basic_step_tid_e; eauto. }
          unfold eq_opt in EQopt. 
          destruct e' as [e'|]; [|done].
          subst w'. rewrite STID.
          eapply basic_step_tid_e'; eauto. }
        destruct k. 
        { unfold ES.cont_cf_dom; split; auto. }
        eapply ES.seqn_lt_cont_cf_dom; eauto.
        { eapply ES.K_inEninit; eauto. }
        rewrite SSEQ. 
        destruct wEE' as [EQ | EQopt].
        { subst w'. 
          erewrite basic_step_seqn_kevent
            with (e := e); eauto. }
        unfold eq_opt in EQopt. 
        destruct e' as [e'|]; [|done].
        subst w'. 
        erewrite basic_step_seqn_e'
            with (e' := e'); eauto.
        erewrite basic_step_seqn_kevent
            with (e := e); eauto. }
      intros x Hx.
      eapply basic_step_cf; eauto.
      autounfold with ESStepDb.
      generalize wEE'. basic_solver 10.
    Qed.

    Lemma sim_ews_ew w' k k' e e' S S'
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S')
          (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'')
          (wEE' : (eq e ∪₁ eq_opt e') w') :
      sim_ews w' S S' × sim_ews w' S S' ⊆ Sew S.
    Proof. 
      cdes BSTEP_.
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (simrel_e2a S G sc) as SRE2A.
      { apply SRCC. }
      unfold sim_ews.
      intros x y [[_ [E2Ax DOMx]] [_ [E2Ay DOMy]]].
      red in E2Ax, DOMx, DOMy, E2Ay.
      unfolder in DOMx.
      unfolder in DOMy.
      destruct DOMx as [x' [z' [EWx [EQ [Xx' Ix']]]]]. subst z'.
      destruct DOMy as [y' [z' [EWy [EQ [Xy' Iy']]]]]. subst z'.
      assert (e2a S x' = e2a S y') as E2AEQ.
      { etransitivity.
        { symmetry. eapply e2a_ew; eauto. 
          basic_solver 10. }
        rewrite <- E2Ay.
        eapply e2a_ew; eauto. 
        basic_solver 10. }
      assert (x' = y') as EQ.
      { eapply e2a_inj.
        1,4-6: eauto.
        all: apply SRCC. }
      eapply ES.ew_trans; eauto.
      eapply ES.ew_sym; eauto. 
      congruence.
    Qed.

    Lemma sim_ews_ew_prcl w' k k' e e' S S'
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S')
          (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'')
          (wEE' : (eq e ∪₁ eq_opt e') w') :
      dom_rel (Sew S ⨾ ⦗sim_ews w' S S'⦘) ⊆₁ sim_ews w' S S'.
    Proof. 
      cdes BSTEP_.
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (simrel_e2a S G sc) as SRE2A.
      { apply SRCC. }
      rewrite seq_eqv_r.
      unfold sim_ews.
      unfolder. 
      intros x [y [EW [ORLXy [E2Ay HH]]]].
      red in ORLXy, E2Ay, HH.
      splits.
      { apply ES.ewm in EW; auto.
        generalize EW ORLXy. basic_solver. }
      { rewrite <- E2Ay.
        eapply e2a_ew; eauto.
        basic_solver 10. }
      destruct HH as [z [z' [EW' [EQ [Xz Iz]]]]]. subst z'. 
      exists z, z; splits; auto.
      eapply ES.ew_trans; eauto.
    Qed.

    Lemma weaken_sim_add_ew w' k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S') 
          (SAEW : sim_add_ew w' S S') 
          (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      add_ew (sim_ews w' S S') w' S S'.
    Proof. 
      cdes BSTEP_; cdes SAEW.
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      
      constructor; splits; auto.
      (* ewsE : ews ⊆₁ E S *)
      { eapply sim_ewsE; eauto. }
      (* ewsW : ews ⊆₁ W S *)
      { eapply sim_ewsW; eauto. }
      (* ewsRLX : ews ⊆₁ ORlx S *)
      { eapply sim_ewsRLX; eauto. }
      (* ewsMOD : ews ⊆₁ same_mod S' w' *)
      { intros x WSx.
        unfold AuxDef.same_mod.
        arewrite (Smod S' x = Smod S x).
        { erewrite basic_step_mod_eq_dom; eauto.
          eapply sim_ewsE; eauto. }
        erewrite sim_ews_mod; eauto.
        basic_solver. }
      (* ewsLOC : ews ⊆₁ same_loc S' w' *)
      { intros x WSx.
        unfold Events.same_loc.
        arewrite (Sloc S' x = Sloc S x).
        { erewrite basic_step_loc_eq_dom; eauto.
          eapply sim_ewsE; eauto. }
        erewrite sim_ews_loc; eauto.
        basic_solver. }
      (* ewsVAL : ews ⊆₁ same_val S' w' *)
      { intros x WSx.
        unfold AuxDef.same_val.
        arewrite (Sval S' x = Sval S x).
        { erewrite basic_step_val_eq_dom; eauto.
          eapply sim_ewsE; eauto. }
        erewrite sim_ews_val; eauto.
        basic_solver. }
      (* ewsCF : ews ⊆₁ cf S' w' *)
      { eapply sim_ews_cf; eauto. }
      (* ewsEW : ews × ews ⊆ ew S *)
      { eapply sim_ews_ew; eauto. }
      (* ewsEWprcl : dom_rel (ew S ⨾ ⦗ews⦘) ⊆₁ ews *)
      eapply sim_ews_ew_prcl; eauto.
    Qed.

    Lemma sim_add_ew_e2a_ew_eq w' k k' e e' S S' 
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S') 
          (SAEW : sim_add_ew w' S S') 
          (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      e2a S' □ Sew S' ⊆ eq. 
    Proof. 
      cdes BSTEP_; cdes SAEW.
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      rewrite EW'.
      rewrite collect_rel_union.
      unionL.
      { eapply simrel_cert_basic_step_e2a_eqr; eauto; apply SRCC. }
      autounfold with ESStepDb.
      rewrite csE, transp_cross.
      rewrite !collect_rel_union, 
              !collect_rel_cross,
              !set_collect_eq.
      erewrite set_collect_eq_dom.
      { rewrite !sim_ews_e2a_eq. basic_solver. }
      eapply eq_dom_mori; eauto.
      2 : eapply basic_step_e2a_eq_dom; eauto.
      eapply sim_ewsE; eauto. 
    Qed.

    Lemma sim_add_ew_ew_ex_iss w' k k' e e' S S' 
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S') 
          (SAEW : sim_add_ew w' S S') 
          (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      dom_rel (Sew S' \ eq) ⊆₁ dom_rel (Sew S' ⨾ ⦗ X ∩₁ e2a S ⋄₁ I ⦘). 
    Proof.
      cdes BSTEP_; cdes SAEW.
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      rewrite EW'. 
      rewrite minus_union_l, !dom_union.
      unionL.
      { etransitivity; [apply SRCC|]. 
        basic_solver 10. }
      autounfold with ESStepDb.
      rewrite csE, transp_cross.
      rewrite !minus_union_l, !dom_union.
      unionL.
      { basic_solver. }
      { rewrite dom_minus, dom_cross; [|red; basic_solver].
        arewrite (sim_ews w' S S' ⊆₁ dom_rel (Sew S ⨾ ⦗X ∩₁ e2a S ⋄₁ I⦘)).
        { unfold sim_ews. basic_solver 10. }
        basic_solver 10. }
      rewrite dom_minus.
      arewrite (
        dom_rel (eq w' × sim_ews w' S S') ⊆₁ 
        dom_rel (eq w' × sim_ews w' S S' ⨾ ⦗X ∩₁ e2a S ⋄₁ I⦘)
      ).
      { unfold sim_ews. 
        intros x [y [EQx HH]]. subst x. desc.
        destruct wEWI as [z HH].
        apply seq_eqv_r in HH.
        destruct HH as [EW [Xz Iz]].
        exists z, z; unfolder; splits; auto.
        { eapply ES.ewm in EW; auto.
          generalize EW wsnREL. basic_solver. }
        { rewrite <- wsE2Aeq. symmetry.
          eapply e2a_ew; [apply SRCC|].
          basic_solver 10. }
        do 2 eexists. splits.
        3-4: eauto.
        2 : done.
        apply ES.ew_refl; auto.
        assert ((SE S ∩₁ SW S) z) as EWz.
        { unfolder. split.
          { apply ES.ewE in EW; auto. 
            generalize EW. basic_solver. }
          apply ES.ewD in EW; auto. 
          generalize EW. basic_solver. }
        generalize EWz. basic_solver 10. }
      basic_solver 10.
    Qed.

    Lemma sim_add_ew_ex_issw_nrel w' k k' e e' S S' 
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S') 
          (SAEW : sim_add_ew w' S S') 
          (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      X ∩₁ e2a S' ⋄₁ (e2a S' □₁ eq w' ∩₁ I) ⊆₁ set_compl (SRel S).
    Proof. 
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (Execution.t S X) as EXEC.
      { apply SRCC. }
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (simrel_cont (stable_prog_to_prog prog) S G TC X) 
        as SRCONT.
      { apply SRCC. }
      assert (simrel_e2a S G sc) as SRE2A.
      { apply SRCC. }
      assert (simrel_ prog S G sc TC X) as SR_.
      { apply SRCC. }
      cdes BSTEP_.

      intros x [Xx [[x' [EQx' EQx]] Ix]] RELx.
      subst x'.
      assert (SE S x) as Ex.
      { eapply Execution.ex_inE; eauto. }
      assert (SEninit S x) as nINITx.
      { apply ES.acts_set_split in Ex.
        destruct Ex as [INITx | nINITx]; auto.
        edestruct ES.init_lab as [l LAB]; eauto.
        unfold init_write in LAB.
        unfold is_rel, mode_le, Events.mod in RELx.
        exfalso. by rewrite LAB in *. }
      assert (e2a S' x = e2a S x) as EQE2Ax.
      { eapply basic_step_e2a_eq_dom; eauto. }
      rewrite EQE2Ax in *.
      symmetry in EQx.
      erewrite e2a_ninit with (e := x) in EQx; auto.
      assert (Stid S x = ES.cont_thread S k) as TIDy.
      { unfolder in wEE'. desf.
        { erewrite basic_step_e2a_e in EQx; eauto.
            by inversion EQx. }
        erewrite basic_step_e2a_e' in EQx; eauto.
          by inversion EQx. }
      assert (kE S k x) as kSBx.
      { eapply ex_ktid_cov; eauto.
        unfolder; splits; auto. 
        eapply ex_w_rel_iss_in_cov; eauto.
        unfolder; splits; auto.
        eapply ex_iss_inW; eauto.
        basic_solver. }
      simpl in kSBx.
      assert (ES.seqn S x < eindex st) as SEQNle.
      { eapply e2a_kE_eindex; eauto.
        unfolder; eexists; splits; eauto.
        apply nINITx. }
      unfolder in wEE'. desf.
      { erewrite basic_step_e2a_e in EQx; eauto. 
        inversion EQx. omega. }
      erewrite basic_step_e2a_e' in EQx; eauto.
      inversion EQx. omega. 
    Qed.

    Lemma sim_add_ew_ex_issw w' k k' e e' S S' 
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S') 
          (SAEW : sim_add_ew w' S S') 
          (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      X ∩₁ e2a S' ⋄₁ (e2a S' □₁ eq w' ∩₁ I) ⊆₁ dom_rel (Sew S' ⨾ ⦗eq w'⦘).
    Proof. 
      cdes BSTEP_; cdes SAEW.
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (Execution.t S X) as EXEC.
      { apply SRCC. }
      rewrite EW'.
      unfold ew_delta.
      rewrite csE.
      rewrite !seq_union_l, !dom_union.
      apply set_subset_union_r; right.
      apply set_subset_union_r; right.
      apply set_subset_union_r; left.
      rewrite seq_eqv_r.
      intros x [Xx [[x' [EQx' EQE2Ax']] Ix]].
      exists w'; unfolder; splits; auto.
      unfold sim_ews.
      splits; auto.
      { eapply sim_add_ew_ex_issw_nrel; eauto. 
        basic_solver. }
      { erewrite <- basic_step_e2a_eq_dom; 
          eauto; try congruence. 
        eapply Execution.ex_inE; eauto. }
      eapply ES.ew_eqvW; auto.
      { rewrite <- set_interK with (s := X).
        rewrite set_interA.
        rewrite Execution.ex_inE 
          with (X := X) at 1; eauto.
        rewrite ex_iss_inW; auto.
        apply SRCC. }
      unfolder; splits; auto.
      erewrite <- basic_step_e2a_eq_dom; eauto. 
      eapply Execution.ex_inE; eauto. 
    Qed.

  End SimRelAddEWProps. 

End SimRelAddEW.