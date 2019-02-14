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
        SimRel SimRelCert SimRelCertBasicStep. 

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelAddCO.
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

  Definition sim_ws (w' : eventid) (S S' : ES.t) := fun w => 
    ⟪ wE : SE S w ⟫ /\
    ⟪ wW : SW S w ⟫ /\  
    ⟪ wNCF : ~ (Scf S') w w' ⟫ /\
    ⟪ wE2A : Gco (e2a S' w) (e2a S' w') ⟫.

  Definition sim_add_co (w' : eventid) (S S' : ES.t) : Prop :=
    ⟪ wE' : SE S' w' ⟫ /\
    ⟪ wW' : SW S' w' ⟫ /\  
    (* ⟪ wsE : ws ⊆₁ SE S ⟫ /\ *)
    (* ⟪ wsW : ws ⊆₁ SW S ⟫ /\ *)
    (* ⟪ wsNCF : ws ∩₁ Scf S' w' ⊆₁ ∅ ⟫ /\ *)
    (* ⟪ wsE : ws ⊆₁ fun w => Gco (e2a S' w) (e2a S' w') ⟫ /\   *)
    ⟪ CO' : Sco S' ≡ Sco S ∪ ESstep.co_delta (sim_ws w' S S') w' S S' ⟫.

  Section SimRelAddCOProps. 

    Lemma sim_wsE w' S S' :
      sim_ws w' S S' ⊆₁ SE S.
    Proof. unfold sim_ws. basic_solver. Qed.

    Lemma sim_wsW w' S S' :
      sim_ws w' S S' ⊆₁ SW S.
    Proof. unfold sim_ws. basic_solver. Qed.

    Lemma sim_ws_nCF w' S S' (WFS : ES.Wf S) :
      sim_ws w' S S' ⊆₁ set_compl (Scf S' w').
    Proof. 
      unfold sim_ws. unfolder.
      red. intros. desc.
      by apply wNCF, ES.cf_sym. 
    Qed.

    Lemma sim_ws_same_loc_e2a w' S S' (WFS : ES.Wf S) (WFG : Wf G) :
      sim_ws w' S S' ⊆₁ same_loc (Glab ∘ (e2a S')) w'.
    Proof. 
      unfold sim_ws.
      intros w Wx. desc.
      assert 
        (same_loc (Glab ∘ e2a S') w' w <-> same_loc Glab (e2a S' w') (e2a S' w)) 
        as HH. 
      { basic_solver. }
      apply HH.
      apply same_loc_sym.
      edestruct loceq_same_loc as [E2A_CO E2A_SLOC].
      { apply loceq_co; eauto. }
      { apply wE2A. }
      done. 
    Qed.

    Lemma sim_ws_e2a_co w' S S' :
      e2a S' □₁ sim_ws w' S S' ⊆₁ fun w => Gco w (e2a S' w').
    Proof. 
      unfold sim_ws. unfolder.
      ins. desc. basic_solver.
    Qed.

    Lemma sim_ws_basic_step_loc_ws w' k k' e e' S S'
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') :
      sim_ws w' S S' ⊆₁ same_loc (Slab S') w'.
    Proof.
      cdes BSTEP_. 
      assert (ESBasicStep.t e e' S S') as BSTEP.
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
        { eapply sim_ws_same_loc_e2a; eauto. }
        { eapply ESBasicStep.basic_step_acts_set; eauto.
          generalize wEE'. basic_solver. }
        eapply ESBasicStep.basic_step_acts_set_mon; eauto. 
        eapply sim_wsE; eauto. }
      red in SLOC. desf.
    Qed.

    Lemma sim_ws_basic_step_co_ws w' k k' e e' S S'
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') :
      sim_ws w' S S' ⊆₁ ESstep.co_ws w' S S'.
    Proof. 
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      unfold ESstep.co_ws.
      rewrite set_minus_inter_set_compl.
      rewrite !set_subset_inter_r. 
      splits. 
      all : eauto using 
        sim_wsE, sim_wsW, sim_ws_nCF, sim_ws_basic_step_loc_ws. 
    Qed.
    
    Lemma weaken_sim_add_co w' k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') 
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SACO : sim_add_co w' S S') 
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      ESstep.add_co (sim_ws w' S S') w' S S'.
    Proof. 
      cdes BSTEP_; cdes SACO.
      constructor; splits; eauto using sim_ws_basic_step_co_ws.
    Qed.

    Lemma basic_step_e2a_co_ws_eq w' k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') 
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') :
      e2a S' □₁ (ESstep.co_ws w' S S') ≡₁ e2a S □₁ (ESstep.co_ws w' S S').
    Proof.   
      cdes BSTEP_.
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      unfold ESstep.co_ws.
      eapply set_collect_eq_dom; eauto.
      red. ins. 
      eapply basic_step_e2a_eq_dom; eauto.
      generalize SX. basic_solver.
    Qed.

    Lemma basic_step_e2a_sim_ws_eq w' k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') 
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') :
      e2a S' □₁ (sim_ws w' S S') ≡₁ e2a S □₁ (sim_ws w' S S').
    Proof.   
      cdes BSTEP_.
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      unfold ESstep.co_ws.
      eapply set_collect_eq_dom; eauto.
      red. ins. 
      eapply basic_step_e2a_eq_dom; eauto.
      eapply sim_wsE; eauto. 
    Qed.

    (* Lemma sim_add_co_e2a_co_ws_minus_co w' k k' e e' S S'  *)
    (*       (st st' st'' : thread_st (ES.cont_thread S k)) *)
    (*       (SRCC : simrel_cert prog S G sc TC f TC' h k st st'')  *)
    (*       (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S')  *)
    (*       (SACO : sim_add_co w' S S')  *)
    (*       (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'')  *)
    (*       (wEE' : (eq e ∪₁ eq_opt e') w') :  *)
    (*   e2a S' □₁ (ESstep.co_ws S S' w' \₁ (sim_ws w' S S')) ⊆₁  *)
    (*       fun w => (Gco)^? (e2a S' w') w.  *)
    (* Proof.  *)
    (*   cdes BSTEP_; cdes SACO. *)
    (*   assert (ESBasicStep.t e e' S S') as BSTEP. *)
    (*   { econstructor. eauto. } *)
    (*   assert (ES.Wf S) as WFS. *)
    (*   { apply SRCC. } *)
    (*   assert (Wf G) as WFG. *)
    (*   { apply SRCC. } *)
    (*   erewrite sim_add_co_e2a_co_ws; eauto. *)
    (*   intros a [w [[CO_WS nWS] EQa]]. subst a. *)
    (*   destruct  *)
    (*     (classic (e2a S' w' = e2a S w))  *)
    (*     as [EQ | nEQ]. *)
    (*   { basic_solver. } *)
    (*   apply r_step. *)
    (*   edestruct wf_co_total as [CO | CO]; eauto. *)
    (*   { unfold set_inter. splits. *)
    (*     { eapply basic_step_e2a_GE;  *)
    (*         eauto; try apply SRCC. *)
    (*       { admit. } *)
    (*       basic_solver. } *)
    (*     { unfold is_w. fold (compose Glab (e2a S') w').  *)
    (*       eapply same_lab_u2v_dom_is_w. *)
    (*       { apply same_lab_u2v_dom_comm. *)
    (*         eapply basic_step_e2a_same_lab_u2v;  *)
    (*           eauto; apply SRCC. } *)
    (*       basic_solver. } *)
    (*     eauto. } *)
    (*   { unfold ESstep.co_ws in CO_WS. *)
    (*     apply set_minus_inter_set_compl in CO_WS. *)
    (*     edestruct CO_WS as [[[wE wW] wLOC] wNCF]. *)
    (*     unfolder; splits; auto. *)
    (*     { eapply e2a_GE; [apply SRCC|]. basic_solver. } *)
    (*     { unfold is_w. fold (compose Glab (e2a S) w).  *)
    (*       eapply same_lab_u2v_dom_is_w. *)
    (*       { apply same_lab_u2v_dom_comm. *)
    (*         eapply e2a_lab; apply SRCC. } *)
    (*       basic_solver. } *)
    (*     arewrite (e2a S w = e2a S' w). *)
    (*     { symmetry. eapply basic_step_e2a_eq_dom; eauto. } *)
    (*     symmetry. admit. (* eapply sim_add_co_e2a_loc_co_ws; eauto. *) } *)
    (*   exfalso. eapply nWS. *)
    (*   unfold sim_ws. splits. *)
    (*   1-3 : admit.  *)
    (*   arewrite (e2a S' w = e2a S w). *)
    (*   { admit. } *)
    (*   done.  *)
    (* Admitted. *)

    Lemma sim_add_co_e2a_co w' k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC f TC' h k st st'') 
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SACO : sim_add_co w' S S') 
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') 
          (wEE' : (eq e ∪₁ eq_opt e') w') : 
      e2a S' □ Sco S' ⊆ Gco.
    Proof.
      cdes BSTEP_; cdes SACO.
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      rewrite CO'.
      rewrite collect_rel_union.
      unionL.
      { eapply simrel_cert_basic_step_e2a_eqr; eauto; apply SRCC. }
      unfold ESstep.co_delta.
      rewrite collect_rel_union, 
              collect_rel_cross,
              set_collect_eq.
      rewrite !crE. relsf.
      rewrite !cross_union_l, !cross_union_r, !seqA.
      unionL.
      { red. intros x y [Wx EQy]. subst y.
        eapply sim_ws_e2a_co; eauto. }
      { arewrite (e2a S' □₁ dom_rel (Sew S ⨾ ⦗sim_ws w' S S'⦘) ⊆₁ e2a S □₁ sim_ws w' S S').
        { rewrite seq_eqv_r. unfolder.
          intros a [x [[y [EW Wy]] EQx]]. subst a.
          eexists; splits; eauto.
          etransitivity.
          { eapply e2a_ew; [apply SRCC|].
            apply ES.ew_sym in EW; auto.
            do 2 eexists; splits; eauto. }
          symmetry. eapply basic_step_e2a_eq_dom; eauto.
          eapply ES.ewE in EW; auto. 
          generalize EW. basic_solver. }
        red. intros x y [Wx EQy]. subst y.
        eapply sim_ws_e2a_co; eauto. 
        eapply basic_step_e2a_sim_ws_eq; eauto. }
      { arewrite 
          (e2a S' □₁ dom_rel (Sco S ⨾ Sew S ⨾ ⦗ws⦘) ⊆₁ dom_rel (Gco ⨾ ⦗ e2a S □₁ ws ⦘)).
        { rewrite seq_eqv_r. unfolder.
          intros a [x [[y [z [CO [EW Wy]]]] EQx]]. subst a.
          eexists; splits; eauto.
          arewrite (e2a S' x = e2a S x).
          { eapply basic_step_e2a_eq_dom; eauto.
            eapply ES.coE in CO; auto. 
            generalize CO. basic_solver. }
          arewrite (e2a S y = e2a S z).
          { eapply e2a_ew; [apply SRCC|].
            apply ES.ew_sym in EW; auto.
            do 2 eexists; splits; eauto. }
          eapply e2a_co; [apply SRCC|].
          generalize CO. basic_solver 10. }
        unfolder. ins. desf.
        eapply co_trans; [apply SRCC | |]; eauto. 
        eapply wsE2A. basic_solver. }
      
      
        red. intros x y [[z Wx] EQy]. subst y.

eapply basic_step_e2a_eq_dom; eauto.
            eapply ES.coE in CO; auto. 
            generalize CO. basic_solver. }
          eapply co_trans; [apply SRCC| | ].
          { eapply e2a_co; [apply SRCC|].
            generalize CO. basic_solver 10. }
          
          etransitivity.
          { eapply e2a_ew; [apply SRCC|].
            apply ES.ew_sym in EW; auto.
            do 2 eexists; splits; eauto. }
          symmetry. eapply basic_step_e2a_eq_dom; eauto.
          eapply ES.ewE in EW; auto. 
          generalize EW. basic_solver. }
        red. intros x y [Wx EQy]. subst y.
        by eapply wsE2A.
          eapply E2Aws.
            
            eexists; splits; eauto.
            etransitivity. 
            { eapply e2a_ew; [apply SRCC|].
              unfolder.
          2 : { rewrite <- E2Aws. basic_solver 20.
          { 
        red. intros x y [Wx EQy]. subst y.
        
        eapply wsE2A.
        

        eapply E2Aws.
        
        eapply set_collect_eq_dom; eauto.
        red. symmetry.
        eapply basic_step_e2a_eq_dom; eauto. } 
      
        unfolder. ins. desf.
        eapply wsE2A. unfolder. basic_solver 10.
      unionL.
      { 
    

  End SimRelAddCOProps. 

End SimRelAddCO.