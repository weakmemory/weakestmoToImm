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
        SimRel SimRelCert. 

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

  Definition sim_add_ew ws (w' : eventid) (S S' : ES.t) : Prop :=
    ⟪ wE' : SE S' w' ⟫ /\
    ⟪ wW' : SW S' w' ⟫ /\
    ⟪ wsE2A : e2a S' □₁ ws ⊆₁ eq (e2a S' w') ⟫ /\
    ⟪ wsI : ws ⊆₁ dom_rel ((Sew S)^? ⨾ ⦗ f □₁ I ⦘) ⟫ /\
    ⟪ EW' : Sew S' ≡ Sew S ∪ ESstep.ew_delta ws w' ⟫. 

  Section SimRelAddEWProps. 

    Lemma sim_add_ew_wsE ws w' k S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') 
          (SAEW : sim_add_ew ws w' S S') :
      ws ⊆₁ SE S.
    Proof. 
      cdes SAEW.
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      etransitivity; [apply wsI|].
      rewrite crE. relsf. split.
      { etransitivity. 
        2 : { eapply a2e_img. apply SRCC.(sim_com). }
        basic_solver 10. }
      rewrite ES.ewE; auto. basic_solver.
    Qed.

    Lemma sim_add_ew_ws_lab_e2a ws w' k S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') 
          (SAEW : sim_add_ew ws w' S S') :
      (Glab ∘ e2a S') □₁ ws ⊆₁ eq ((Glab ∘ (e2a S')) w').
    Proof. 
      cdes SAEW.
      unfold compose. 
      intros a [x [WSx LABx]]. subst a.
      arewrite (e2a S' x = e2a S' w'); auto.
      erewrite wsE2A; eauto.
      basic_solver.
    Qed.

    Lemma sim_add_ew_ws_lab ws w' k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') 
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SAEW : sim_add_ew ws w' S S') 
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      (Slab S') □₁ ws ⊆₁ eq (Slab S' w').
    Proof. 
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      intros l [x [WSx EQx]].
      cdes SAEW.
      edestruct wsI as [y wsIy]; eauto.
      destruct wsIy as [z [EWr [EQyz [a [Ia EQa]]]]].
      subst y z.
      assert (e2a S' (f a) = a) as EQfaE2A.
      { erewrite basic_step_e2a_eq_dom; eauto.
        { eapply a2e_fix; [apply SRCC.(sim_com)|]. 
          basic_solver 10. }
        eapply a2e_img; [apply SRCC.(sim_com)|]. 
        basic_solver 10. }
      assert (e2a S' w' = a) as EQaE2A.
      { erewrite wsE2A; eauto.
        destruct EWr as [EQ | EW].
        { basic_solver. }
        unfolder; eexists; splits; eauto.
        eapply e2a_ew; [apply SRCC|].
        unfolder; do 2 eexists; splits; eauto.
        all : erewrite basic_step_e2a_eq_dom with (S' := S'); eauto.
        { eapply sim_add_ew_wsE; eauto. }
        eapply a2e_img; [apply SRCC.(sim_com)|]. 
        basic_solver 10. }
      subst l.
      assert (Slab S' x = Glab a) as EQaLAB.
      { erewrite ESBasicStep.basic_step_lab_eq_dom
          with (x := x); eauto.
        2 : { eapply sim_add_ew_wsE; eauto. } 
        erewrite <- flab; [| apply SRCC| basic_solver].
        unfold compose.
        destruct EWr as [EQ | EW].
        { basic_solver. }
        eapply ES.ewlab; auto. }
      rewrite EQaLAB.
      destruct wEE' as [E | E'].
      { subst w'.
        erewrite basic_step_e2a_certlab_e; eauto. 
        2-3 : apply SRCC.
        rewrite EQaE2A.
        eapply cslab; [apply SRCC|].
        do 4 left. right. 
        eapply step_mon; eauto.
        econstructor.
        admit. }
      destruct e' as [e'|]; [|done].
      unfold eq_opt in E'. subst w'.
      erewrite basic_step_e2a_certlab_e'; eauto. 
      2-3 : apply SRCC.
      rewrite EQaE2A.
      eapply cslab; [apply SRCC|].
      do 4 left. right. 
      eapply step_mon; eauto.
      econstructor.
      admit. 
    Admitted.
      
    Lemma weaken_sim_add_ew ws w' k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') 
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SAEW : sim_add_ew ws w' S S') 
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      ESstep.add_ew ws w' S S'.
    Proof. 
      cdes BSTEP_; cdes SAEW.
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      
      constructor; splits; auto.
      (* wsE : ws ⊆₁ E S *)
      { eapply sim_add_ew_wsE; eauto. }
      (* wsW : ws ⊆₁ W S *)
      { etransitivity; [apply wsI|]. 
        rewrite crE. relsf. split.
        { intros x [a [Ia EQa]]. subst x.
          unfold is_w. 
          fold (compose (Slab S) f a).
          erewrite flab; [| apply SRCC | basic_solver].
          fold (is_w Glab a).
          eapply issuedW; eauto.
          apply SRCC. }
        rewrite ES.ewD; auto. basic_solver. }
      (* LOCWS : ws ⊆₁ same_loc S' w' *)
      { intros x WSx.
        unfold same_loc, loc.
        erewrite sim_add_ew_ws_lab; eauto.
        basic_solver. }
      (* VALWS : ws ⊆₁ same_val S' w' *)
      { intros x WSx.
        unfold same_val, val.
        erewrite sim_add_ew_ws_lab; eauto.
        basic_solver. }
    Admitted.

  End SimRelAddEWProps. 

End SimRelAddEW.