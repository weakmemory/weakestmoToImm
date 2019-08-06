Require Import Program.Basics Omega.
From hahn Require Import Hahn.
From imm Require Import Events Execution
     Traversal TraversalConfig SimTraversal SimTraversalProperties
     Prog ProgToExecution ProgToExecutionProperties Receptiveness
     imm_common imm_s imm_s_hb SimulationRel
     CertExecution2 CertExecutionMain
     SubExecution CombRelations.
Require Import AuxRel.
Require Import AuxDef.
Require Import EventStructure.
Require Import Execution.
Require Import BasicStep.
Require Import AddEW.
Require Import AddCO.
Require Import Step.
Require Import Consistency.
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
Require Import SimRelAddEW. 
Require Import ProgES. 

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelAddCO.
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
  Notation "'SLoc_' S" := (fun l x => Sloc S x = l) (at level 1).

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

  Definition sim_ws (k : cont_label) (w' : eventid) (S S' : ES.t) := fun w => 
    ⟪ wE : SE S w ⟫ /\
    ⟪ wW : SW S w ⟫ /\  
    (* ⟪ wNCF : ~ ES.cont_cf_dom S k w ⟫ /\ *)
    (* ⟪ wkSB : dom_rel ((Sco S)^? ⨾ (Sew S)^? ⨾ ⦗set_compl (ES.cont_cf_dom S k)⦘) w ⟫ /\ *)
    ⟪ wE2Aco : Gco (e2a S w) (e2a S' w') ⟫.


  Definition sim_add_co (k : cont_label) (w' : eventid) (S S' : ES.t) : Prop :=
    ⟪ wE' : SE S' w' ⟫ /\
    ⟪ wW' : SW S' w' ⟫ /\  
    (* ⟪ wsE : ws ⊆₁ SE S ⟫ /\ *)
    (* ⟪ wsW : ws ⊆₁ SW S ⟫ /\ *)
    (* ⟪ wsNCF : ws ∩₁ Scf S' w' ⊆₁ ∅ ⟫ /\ *)
    (* ⟪ wsE : ws ⊆₁ fun w => Gco (e2a S' w) (e2a S' w') ⟫ /\   *)
    ⟪ CO' : Sco S' ≡ 
                Sco S ∪ co_delta (sim_ews TC X w' S S') (sim_ws k w' S S') w' S ⟫.

  Section SimRelAddCOProps. 

    Lemma sim_wsE k w' S S' :
      sim_ws k w' S S' ⊆₁ SE S.
    Proof. unfold sim_ws. basic_solver. Qed.

    Lemma sim_wsW k w' S S' :
      sim_ws k w' S S' ⊆₁ SW S.
    Proof. unfold sim_ws. basic_solver. Qed.

    Lemma sim_ws_e2a_co k w' S S' :
      e2a S □₁ sim_ws k w' S S' ⊆₁ fun w => Gco^? w (e2a S' w').
    Proof. 
      unfold sim_ws. unfolder.
      ins. desc. basic_solver.
    Qed.

    Lemma sim_ws_basic_step_loc_e2a w' k k' e e' S S'
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S') 
          (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') :
      sim_ws k w' S S' ⊆₁ Events.same_loc (Glab ∘ (e2a S')) w'.
    Proof. 
      cdes BSTEP_. 
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (Wf G) as WFG.
      { apply SRCC. }
      unfold sim_ws.
      intros w Wx. desc.
      assert 
        (Events.same_loc (Glab ∘ e2a S') w' w <-> Events.same_loc Glab (e2a S' w') (e2a S' w)) 
        as HH. 
      { basic_solver. }
      apply HH.
      apply same_loc_sym.
      edestruct loceq_same_loc as [E2A_CO E2A_SLOC].
      { apply loceq_co; eauto. }
      { apply wE2Aco. }
      erewrite basic_step_e2a_eq_dom; eauto.
    Qed.

    Lemma sim_ws_basic_step_loc w' k k' e e' S S'
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S') 
          (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') :
      sim_ws k w' S S' ⊆₁ same_loc (Slab S') w'.
    Proof.
      cdes BSTEP_. 
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (Wf G) as WFG.
      { apply SRCC. }
      intros w Wx. desc.
      assert ((restr_rel (SE S') (same_loc (Slab S'))) w' w) as SLOC.
      { eapply same_lab_u2v_dom_same_loc.
        { eapply basic_step_e2a_same_lab_u2v; eauto; apply SRCC. }
        red; splits; auto.
        { eapply sim_ws_basic_step_loc_e2a; eauto. }
        { eapply basic_step_acts_set; eauto.
          generalize wEE'. basic_solver. }
        eapply basic_step_acts_set_mon; eauto. 
        eapply sim_wsE; eauto. }
      red in SLOC. desf.
    Qed.

    Lemma sim_ws_basic_step_ws_Einit w' k k' e e' S S'
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S')
          (SACO : sim_add_co k w' S S')
          (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      SEinit S ∩₁ SLoc_ S (Sloc S' w') ⊆₁ sim_ws k w' S S'.
    Proof. 
      cdes BSTEP_; cdes SACO.
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (Wf G) as WFG.
      { apply SRCC. }
      intros x [Init LOCx].
      assert (SE S x) as SEx.
      { red in Init. unfolder in Init. desf. }
      assert (SE S' x) as SEx'.
      { eapply basic_step_acts_set; eauto. basic_solver. }
      econstructor; splits; auto.
      { eapply ES.acts_init_set_inW; auto. }
      eapply init_co_w; auto.
      { apply SRCC. }
      { eapply e2a_Einit. 
        apply stable_prog_to_prog_no_init.
        1-2 : apply SRCC. 
        { eapply e2a_GE. apply SRCC. } 
        basic_solver. }
      { intros InitW.
        assert (~ SEinit S' w') as nInitW.
        { unfolder in wEE'. desf.
          { eapply basic_step_acts_ninit_set_e; eauto. }
          eapply basic_step_acts_ninit_set_e'; eauto. }
        apply nInitW.
        red. split; auto. 
        etransitivity.
        { eapply e2a_tid. }
        unfold Events.tid. unfold is_init in InitW.
        destruct (e2a S' w'); desf. }
      { eapply basic_step_e2a_GE; 
          eauto; try apply SRCC.
        { eapply tccoh'; eauto. }
        basic_solver. }
      { unfold is_w. fold (compose Glab (e2a S') w'). 
        fold (is_w (Glab ∘ e2a S') w').
        eapply same_lab_u2v_dom_is_w.
        { apply same_lab_u2v_dom_comm.
          eapply basic_step_e2a_same_lab_u2v; 
            eauto; apply SRCC. }
        basic_solver. }
      assert 
        (restr_rel (SE S') (Events.same_loc (Glab ∘ (e2a S'))) x w') 
        as HH.
      { eapply same_lab_u2v_dom_same_loc.
        { apply same_lab_u2v_dom_comm.
          eapply basic_step_e2a_same_lab_u2v; 
            eauto; try apply SRCC. }
        unfolder; splits; eauto.
        red. arewrite (Sloc S' x = Sloc S x); auto.
        eapply basic_step_loc_eq_dom; eauto. }
      generalize HH. 
      unfold Events.same_loc, Events.loc, compose.
      arewrite (e2a S x = e2a S' x).
      { symmetry. eapply basic_step_e2a_eq_dom; eauto. }
      basic_solver. 
    Qed.

    Lemma sim_ws_basic_step_ws_ews w' k k' e e' S S'
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S') 
          (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') :
      sim_ws k w' S S' ∩₁ sim_ews TC X w' S S' ⊆₁ ∅.
    Proof. 
      cdes BSTEP_.
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (Wf G) as WFG.
      { apply SRCC. }
      unfold sim_ews, sim_ws.
      intros x [WSx EWSx]. 
      red. desf.
      rewrite wsE2Aeq in wE2Aco.
      eapply co_irr; eauto. 
    Qed.

    Lemma sim_ws_basic_step_co_ew_prcl w' k k' e e' S S'
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S')
          (wEE' : (eq e ∪₁ eq_opt e') w') :
      dom_rel ((Sco S)^? ⨾ (Sew S)^? ⨾ ⦗ sim_ws k w' S S' ⦘) ⊆₁ sim_ws k w' S S'.
    Proof. 
      cdes BSTEP_.
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (Wf G) as WFG.
      { apply SRCC. }
      assert (simrel_e2a S G sc) as SRE2A.
      { apply SRCC. }
      intros x [y [z [CO [z' [EW [EQz' SWS]]]]]].
      subst z'. 
      unfold sim_ws in *. desc.
      econstructor; splits.
      { unfolder in CO. unfolder in EW. desf.
        { apply ES.coE in CO; auto. generalize CO. basic_solver. }
        { apply ES.ewE in EW; auto. generalize EW. basic_solver. }
        apply ES.coE in CO; auto. generalize CO. basic_solver. }
      { unfolder in CO. unfolder in EW. desf.
        { apply ES.coD in CO; auto. generalize CO. basic_solver. }
        { apply ES.ewD in EW; auto. generalize EW. basic_solver. }
        apply ES.coD in CO; auto. generalize CO. basic_solver. }
      { unfolder in CO. unfolder in EW. desf.
        { edestruct e2a_co as [EQ | GCO].
          { apply SRCC. }
          { basic_solver 10. }
          { congruence. }
          eapply co_trans; eauto. }
        { arewrite (e2a S z = e2a S y); auto.
          eapply e2a_ew; [apply SRCC|].
          basic_solver 10. }
        assert (e2a S z = e2a S y) as EQyz.
        { eapply e2a_ew; eauto. basic_solver 10. }
        edestruct e2a_co as [EQ | GCO].
        { apply SRCC. }
        { basic_solver 10. }
        { congruence. }
        eapply co_trans; eauto. }
    Qed.

    Lemma sim_ws_basic_step_ews_co_prcl w' k k' e e' S S'
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S')
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      dom_rel (Sco S ⨾ ⦗sim_ews TC X w' S S'⦘) ⊆₁ sim_ws k w' S S'.
    Proof. 
      cdes BSTEP_.
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (Wf G) as WFG.
      { apply SRCC. }
      assert (simrel_e2a S G sc) as SRE2A.
      { apply SRCC. }
      assert (simrel_ prog S G sc TC X) as SR_.
      { apply SRCC. }
      intros x [y [z [CO [a SEWS]]]]. 
      unfold sim_ews in SEWS. desc. subst z.
      econstructor; splits; auto.
      { eapply ES.coE in CO; auto. generalize CO. basic_solver. }
      { eapply ES.coD in CO; auto. generalize CO. basic_solver. }
      rewrite <- wsE2Aeq.
      edestruct e2a_co as [EQ | GCO]. 
      { apply SRCC. }
      { basic_solver 10. }
      2 : congruence.
      destruct wEWI as [z HH].
      apply seq_eqv_r in HH. 
      destruct HH as [EW [Xz Iz]].
      exfalso. 
      eapply co_irr; eauto.
      eapply e2a_co_ew_iss; eauto. 
      exists x, z. splits.
      { basic_solver 10. }
      { apply EQ. }
      rewrite <- wsE2Aeq. symmetry. 
      eapply e2a_ew; eauto.
      basic_solver 10. 
    Qed.
    
    Lemma weaken_sim_add_co w' k k' e e' S S' 
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S') 
          (SACO : sim_add_co k w' S S') 
          (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      add_co (sim_ews TC X w' S S') (sim_ws k w' S S') w' S S'.
    Proof. 
      cdes BSTEP_; cdes SACO.
      constructor; splits;
        eauto using sim_wsE, sim_wsW, 
          sim_ws_basic_step_loc,
          sim_ws_basic_step_ws_Einit,
          sim_ws_basic_step_ws_ews,
          sim_ws_basic_step_co_ew_prcl,
          sim_ws_basic_step_ews_co_prcl.
    Qed.

    Lemma basic_step_e2a_sim_ws_eq w' k k' e e' S S' 
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S') :
      e2a S' □₁ (sim_ws k w' S S') ≡₁ e2a S □₁ (sim_ws k w' S S').
    Proof.   
      cdes BSTEP_.
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      eapply set_collect_eq_dom; eauto.
      red. ins. 
      eapply basic_step_e2a_eq_dom; eauto.
      eapply sim_wsE; eauto. 
    Qed.

    Lemma basic_step_e2a_codom_sim_ws_co_in_co w' k k' e e' S S' 
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S') 
          (SACO : sim_add_co k w' S S')
          (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      e2a S □₁ (codom_rel (
                    ⦗sim_ews TC X w' S S' ∪₁ sim_ws k w' S S'⦘ ⨾ Sco S) \₁ 
                          (sim_ews TC X w' S S' ∪₁ sim_ws k w' S S'))
          ⊆₁ fun w => Gco^? (e2a S' w') w.
    Proof. 
      cdes BSTEP_; cdes SACO.
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (Wf G) as WFG.
      { apply SRCC. }
      assert (simrel_e2a S G sc) as SRE2A.
      { apply SRCC. }
      intros a [x [[[y [z [[EQz SWS] COyx]]] nSWS] EQa]].
      subst a z.
      assert (SE S x) as SEx.
      { eapply ES.coE in COyx; auto.
        generalize COyx. basic_solver. }
      assert (SW S x) as SWx.
      { eapply ES.coD in COyx; auto.
        generalize COyx. basic_solver. }
      assert (SE S y) as SEy.
      { eapply ES.coE in COyx; auto.
        generalize COyx. basic_solver. }
      assert (SW S y) as SWy.
      { eapply ES.coD in COyx; auto.
        generalize COyx. basic_solver. }
      destruct
        (classic (e2a S' w' = e2a S x))
        as [EQ | nEQ].
      { by left. }
      right.
      edestruct wf_co_total as [CO | CO]; eauto.
      { unfold set_inter. splits.
        { eapply basic_step_e2a_GE;
            eauto; try apply SRCC.
          { eapply tccoh'; eauto. }
          basic_solver. }
        { unfold is_w. fold (compose Glab (e2a S') w').
          eapply same_lab_u2v_dom_is_w.
          { apply same_lab_u2v_dom_comm.
            eapply basic_step_e2a_same_lab_u2v;
              eauto; apply SRCC. }
          basic_solver. }
        eauto. }
      { unfolder; splits; auto.
        { eapply e2a_GE; [apply SRCC|]. basic_solver. }
        { unfold is_w. fold (compose Glab (e2a S) x).
          eapply same_lab_u2v_dom_is_w.
          { apply same_lab_u2v_dom_comm.
            eapply e2a_lab; apply SRCC. }
          basic_solver. }
        arewrite (Events.loc Glab (e2a S x) = Events.loc Glab (e2a S y)).
        { unfold Events.loc.
          fold (compose Glab (e2a S) x).
          fold (compose Glab (e2a S) y).
          fold (Events.loc (Glab ∘ e2a S) x).
          fold (Events.loc (Glab ∘ e2a S) y).
          erewrite same_lab_u2v_dom_loc with (lab1 := Glab ∘ e2a S).
          2 : eapply same_lab_u2v_dom_comm, e2a_lab; eauto.
          erewrite same_lab_u2v_dom_loc with (lab1 := Glab ∘ e2a S).
          2 : eapply same_lab_u2v_dom_comm, e2a_lab; eauto.
          { symmetry. apply ES.col; auto. }
          all: done. }
        arewrite (e2a S y = e2a S' y).
        { symmetry. eapply basic_step_e2a_eq_dom; eauto. }
        symmetry. destruct SWS as [EWSy | WSy].
        { unfold sim_ews in EWSy. desf.
          arewrite (e2a S' y = e2a S y); [|congruence].
          eapply basic_step_e2a_eq_dom; eauto. }
        eapply sim_ws_basic_step_loc_e2a; eauto. }
      exfalso. eapply nSWS.
      right; econstructor; splits; auto.
    Qed.

    Lemma sim_add_co_e2a_co w' k k' e e' S S' 
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S') 
          (SACO : sim_add_co k w' S S') 
          (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      e2a S' □ Sco S' ⊆ Gco^?.
    Proof.
      cdes BSTEP_; cdes SACO.
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      rewrite CO'.
      rewrite collect_rel_union.
      unionL.
      { eapply simrel_cert_basic_step_e2a_eqr; eauto; apply SRCC. }
      unfold co_delta.
      rewrite !collect_rel_union, 
              !collect_rel_cross,
              !set_collect_eq.
      erewrite basic_step_e2a_sim_ws_eq; eauto.
      erewrite set_collect_eq_dom
        with (s := codom_rel (⦗sim_ews TC X w' S S' ∪₁ sim_ws k w' S S'⦘ ⨾ Sco S) \₁
           (sim_ews TC X w' S S' ∪₁ sim_ws k w' S S')); eauto.      
      2 : { erewrite ES.coE; auto. intros x HH. 
            eapply basic_step_e2a_eq_dom; eauto.
            generalize HH. basic_solver. }
      rewrite sim_ws_e2a_co.
      erewrite basic_step_e2a_codom_sim_ws_co_in_co; eauto.
      basic_solver.
    Qed.

    Lemma sim_add_co_e2a_codom_ws_compl_ew w' k k' e e' S S'
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S')
          (SAEW : sim_add_ew TC X w' S S')
          (SACO : sim_add_co k w' S S')
          (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'')
          (wEE' : (eq e ∪₁ eq_opt e') w') :
    codom_rel (e2a S □
      ⦗ws_compl (sim_ews TC X w' S S') (sim_ws k w' S S') S⦘ ⨾ Sew S ⨾ ⦗X ∩₁ e2a S ⋄₁ I⦘
    ) ⊆₁ fun w => Gco (e2a S' w') w.
    Proof.
      cdes BSTEP_; cdes SAEW; cdes SACO.
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (Wf G) as WFG.
      { apply SRCC. }
      assert (simrel_cont (stable_prog_to_prog prog) S G TC X) 
        as SRCONT.
      { apply SRCC. }
      assert (simrel_e2a S G sc) as SRE2A.
      { apply SRCC. }
      assert (simrel_ prog S G sc TC X) as SR_.
      { apply SRCC. }
      assert (Execution.t S X) as EXEC.
      { apply SRCC. }
      rewrite seq_eqv_lr.
      intros y' [x' [x [y HH]]].
      destruct HH as [HH [EQx' EQy']].
      destruct HH as [WSC [EW [Xy Iy]]].
      unfold ws_compl in WSC.
      destruct WSC as [[z' [z'' [HH COz]]] nEWSWS].
      destruct HH as [EQz'' EWSWS].
      subst x' y' z''. desc.
      assert (SE S y) as Ey.
      { eapply Execution.ex_inE in Xy; eauto. }
      assert (Gco (e2a S z') (e2a S y)) as GCO.
      { eapply e2a_co_ew_iss; eauto. basic_solver 10. }
      destruct EWSWS as [EWS | WS].
      { unfold sim_ews in EWS. desc. congruence. }
      unfold sim_ws in WS. desc.
      destruct (classic (e2a S' w' = e2a S y)) 
        as [EQ | nEQ].
      { exfalso. apply nEWSWS. left.
        unfold sim_ews. splits.
        { apply ES.ewm in EW; auto.
          destruct EW as [EQx | [RLX _]];
            auto; subst x.
          eapply sim_add_ew_ex_issw_nrel; eauto.  
          unfolder; splits; try eexists; splits; eauto. 
          { symmetry. erewrite basic_step_e2a_eq_dom; eauto. }
          erewrite basic_step_e2a_eq_dom; eauto. }
        { rewrite EQ.
          eapply e2a_ew; eauto.
          basic_solver 10. }
        basic_solver 10. }
      edestruct wf_co_total
        with (a := e2a S' w') (b := e2a S y)
        as [GCO' | GCO']; eauto.
      { unfolder; splits; eauto.
        { eapply basic_step_e2a_GE;
            eauto; try apply SRCC.
          { eapply tccoh'; eauto. }
          basic_solver. }
        edestruct same_lab_u2v_dom_is_w as [HH _].
        { eapply basic_step_e2a_same_lab_u2v;
            eauto; apply SRCC. }
        apply HH; split; auto. }
      { unfolder; splits; auto.
        { eapply e2a_GE; eauto. basic_solver. }
        { edestruct same_lab_u2v_dom_is_w as [HH _].
          { eapply e2a_lab; eauto. }
          apply HH; split; auto.
          apply ES.ewD in EW; auto.
          generalize EW. basic_solver 10. }
        etransitivity.
        { erewrite <- loceq_co; eauto. }
        erewrite loceq_co; eauto. }
      exfalso. apply nEWSWS. right.
      unfold sim_ws.
      splits; auto.
      { apply ES.ewE in EW; auto. 
        generalize EW. basic_solver. }
      { apply ES.ewD in EW; auto. 
        generalize EW. basic_solver. }
      arewrite (e2a S x = e2a S y); auto.
      eapply e2a_ew; eauto. basic_solver 10. 
    Qed.

    Lemma sim_add_co_e2a_co_ew w' k k' e e' S S' 
          (st st' st'' : thread_st (ktid S k))
          (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
          (BSTEP_ : basic_step_ (thread_lts (ktid S k)) k k' st st' e e' S S') 
          (SAEW : sim_add_ew TC X w' S S') 
          (SACO : sim_add_co k w' S S') 
          (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') 
          (nRelIss : ~ (SRel S' ∩₁ e2a S' ⋄₁ I) w') : 
      e2a S' □ (Sco S' ⨾ Sew S' ⨾ ⦗X ∩₁ e2a S ⋄₁ I⦘) ⊆ Gco.
    Proof. 
      cdes BSTEP_; cdes SAEW; cdes SACO.
      assert (basic_step e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (Wf G) as WFG.
      { apply SRCC. }
      assert (simrel_e2a S G sc) as SRE2A.
      { apply SRCC. }
      assert (simrel_ prog S G sc TC X) as SR_.
      { apply SRCC. }
      assert (Execution.t S X) as EXEC.
      { apply SRCC. }
      rewrite EW', CO'.
      unfold co_delta, ew_delta.
      relsf. unionL.
      { erewrite basic_step_e2a_collect_rel_eq_dom; 
          eauto; [apply SRCC|].
        rewrite ES.ewE, ES.coE; auto.
        basic_solver 20. }
      { unfolder in wEE'; desf; step_solver. }
      { rewrite Execution.ex_inE 
          with (X := X) at 2; eauto.
        unfolder in wEE'; desf; step_solver. }
      { unfolder in wEE'; desf; step_solver. }
      { rewrite Execution.ex_inE 
          with (X := X) at 1; eauto.
        unfolder in wEE'; desf; step_solver. }
      { rewrite csE. relsf. unionL.
        { rewrite sim_ewsE; eauto.
          unfolder in wEE'; desf; step_solver. }
        rewrite seq_eqv_r.
        intros x' y' [x [y HH]].
        destruct HH as [[z HH] [EQx' EQy']].
        destruct HH as [[WS EQz] [[_ EWS] [Xy Iy]]].
        unfold sim_ws in WS.
        unfold sim_ews in EWS.
        subst x' y' z. desc.
        arewrite (e2a S' x = e2a S x). 
        { erewrite basic_step_e2a_eq_dom; eauto. }
        arewrite (e2a S' y = e2a S y). 
        { eapply Execution.ex_inE in Xy; eauto.
          erewrite basic_step_e2a_eq_dom; eauto. }
        congruence. }
      { unfolder. ins. desf.
        arewrite (e2a S' y' = e2a S y').
        { erewrite basic_step_e2a_eq_dom; eauto. 
          eapply Execution.ex_inE; eauto. }
        eapply sim_add_co_e2a_codom_ws_compl_ew; eauto.
        exists (e2a S z).
        basic_solver 10. }
      { erewrite add_co_ws_complE; auto.
        unfolder in wEE'; desf; step_solver. }
      erewrite add_co_ws_complE; auto.
      rewrite Execution.ex_inE 
          with (X := X) at 2; eauto.
      unfolder in wEE'; desf; step_solver.
    Qed.

  End SimRelAddCOProps. 

End SimRelAddCO.