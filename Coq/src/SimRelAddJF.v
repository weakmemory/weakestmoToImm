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

Section SimRelAddJF.
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
  Notation "'Gvf'" := (furr G sc).
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

  Definition sim_add_jf thread st (w r' : eventid) (S S' : ES.t) : Prop :=
    ⟪ rE' : SE S' r' ⟫ /\
    ⟪ rR' : SR S' r' ⟫ /\
    ⟪ hCertDOM : (h □₁ (cert_dom G TC thread st)) w ⟫ /\
    ⟪ CertRF : (cert_rf G sc TC' thread) (e2a S' w) (e2a S' r') ⟫ /\
    ⟪ JF' : Sjf S' ≡ Sjf S ∪ ESstep.jf_delta w r' ⟫.

  Section SimRelAddJFProps. 

    Lemma sim_add_jf_jf_ncf w k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SAJF : sim_add_jf (ES.cont_thread S k) st w e S S')
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :
      Sjf S' ∩ Scf S' ≡ ∅₂.
    Proof. 
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WF.
      { apply SRCC. }
      cdes BSTEP_; cdes SAJF.
      split; [|done].
      rewrite JF'.
      erewrite ESBasicStep.basic_step_cf; eauto.
      rewrite !inter_union_l, !inter_union_r. 
      unionL.

      { apply ES.jf_ncf; apply SRCC. } 

      1-2 : by ESBasicStep.step_solver.

      autounfold with ESStepDb.
      rewrite !csE, !transp_cross.
      rewrite !inter_union_r. 
      unionL.

      2-4 : by ESBasicStep.step_solver.

      unfolder. ins. desf.
      eapply cfk_hdom; eauto.  
      basic_solver.
    Qed.

    Lemma weaken_sim_add_jf w k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SAJF : sim_add_jf (ES.cont_thread S k) st w e S S') 
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
      ESstep.add_jf w e S S'.
    Proof. 
      cdes BSTEP_; cdes SAJF.
      assert (ES.Wf S) as WFS by apply SRCC.
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WF.
      { apply SRCC. }
      assert (SE S w) as SEw.
      { eapply a2e_img; eauto. apply SRCC. }
      assert (SE S' w) as SEw'.
      { eapply ESBasicStep.basic_step_acts_set; eauto. basic_solver. }
      assert (SE S' e) as SEe'.
      { eapply ESBasicStep.basic_step_acts_set; eauto. basic_solver. }
      assert (Gtid (e2a S' e) = ES.cont_thread S k) as GTIDe.
      { rewrite <- e2a_tid. erewrite ESBasicStep.basic_step_tid_e; eauto. }
      econstructor; splits; auto.  
      { assert (is_w (Glab ∘ (e2a S)) w) as WW.
        { eapply cert_rfD, seq_eqv_lr in CertRF.
          destruct CertRF as [HH _].
          unfold is_w, compose in *. 
          erewrite <- basic_step_e2a_eq_dom; eauto. }
        eapply same_lab_u2v_dom_is_w; eauto.
        { eapply e2a_lab. apply SRCC. }
        red; split; auto. }
      { assert (restr_rel (SE S') (same_loc (Slab S')) w e) as HH.
        { eapply same_lab_u2v_dom_same_loc.
          { eapply basic_step_e2a_same_lab_u2v; eauto; apply SRCC. }
          apply restr_relE, seq_eqv_lr. 
          splits; auto. 
          eapply cert_rfl in CertRF.
            by unfold same_loc, loc, compose in *. }
        apply restr_relE, seq_eqv_lr in HH. 
        basic_solver. }
      { assert (same_val (certLab G st'') (e2a S' w) (e2a S' e)) as SAME_VAL.
        { eapply cert_rfv_clab; eauto. apply SRCC. }
        unfold same_val, val in *.
        erewrite basic_step_e2a_certlab_e with (e := e); eauto.
        arewrite (Slab S' w = Slab S w).
        { erewrite ESBasicStep.basic_step_lab_eq_dom; eauto. }
        assert (e2a S w = e2a S' w) as E2Aw. 
        { symmetry. eapply basic_step_e2a_eq_dom; eauto. }
        rewrite <- E2Aw in *.
        eapply cert_rf_ntid_iss_sb in CertRF. 
        2-10: apply SRCC.
        unfolder in hCertDOM. destruct hCertDOM as [wa [CERTwa Hwa]].
        assert (e2a S w = wa) as Gwwa.
        { rewrite <- Hwa.
          eapply a2e_fix; [apply SRCC|].
          unfolder. basic_solver. }
        arewrite (Slab S w = certLab G st'' (e2a S w)); [|auto].
        rewrite <- Hwa at 1.
        rewrite Gwwa.
        arewrite ((Slab S) (h wa) = (Slab S ∘ h) wa).
        destruct CertRF as [Iss | SB].
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
          eapply hlabCI; eauto.
          basic_solver. }
        edestruct sb_tid_init as [STID | INITx]; eauto. 
        { eapply hlab; eauto. right. 
          destruct CERTwa as [[Cwa | Iwa] | ACTSst]; auto.
          { eapply cstate_covered; [apply SRCC|].
            split; auto.
              by rewrite <- Gwwa, STID, GTIDe. }
          exfalso. destruct Iwa as [_ NTIDwa].
          apply NTIDwa.
          rewrite <- Gwwa.
          erewrite <- ESBasicStep.basic_step_tid_e; eauto.
            by rewrite e2a_tid. }
        assert (C wa) as Cwa.
        { eapply init_covered; [apply SRCC|].
          rewrite <- Gwwa. 
          split; auto.  
          eapply e2a_GE; [apply SRCC|].
          unfolder. eauto. }
        eapply hlab; eauto. basic_solver. }
      intros CF.
      eapply sim_add_jf_jf_ncf; eauto.
      split; eauto.
      apply JF'. 
      autounfold with ESStepDb.
      basic_solver.
    Qed.

    Lemma sim_add_jf_iss_sb w k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SAJF : sim_add_jf (ES.cont_thread S k) st w e S S')
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :
      (h □₁ (I ∩₁ (GNtid_ (ES.cont_thread S k))) ∪₁ ES.cont_sb_dom S k) w. 
    Proof. 
      assert (ESstep.add_jf w e S S') as AJF. 
      { eapply weaken_sim_add_jf; eauto. } 
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WF.
      { apply SRCC. }
      cdes BSTEP_; cdes SAJF; cdes AJF. 
      assert (e2a S' w = e2a S w) as e2aEQw.
      { eapply basic_step_e2a_eq_dom; eauto. }
      assert (h (e2a S w) = w) as he2aEQw.
      { fold (compose h (e2a S) w).
        eapply fixset_swap; eauto. 
        apply SRCC. }
      rewrite e2aEQw in *.
      eapply cert_rf_ntid_iss_sb in CertRF.
      2-6 : apply SRCC.
      destruct CertRF as [Iss | SB].
      { unfolder. left. 
        unfolder in Iss. 
        destruct Iss as [[NTID Iss] _].
        eexists; splits; eauto. }
      unfolder. right. 
      edestruct sb_tid_init as [STID | INITw]; eauto. 
      { assert ((SE S ∩₁ Stid_ S (ES.cont_thread S k)) w) as HH. 
        { split; auto.
          rewrite <- !e2a_tid in STID.
          rewrite STID.
          erewrite ESBasicStep.basic_step_tid_e; eauto. }
        eapply ES.cont_thread_sb_cf in HH; eauto. 
        destruct HH as [HA | HB].
        { generalize HA. basic_solver. }
        exfalso. eapply cfk_hdom; eauto.
        basic_solver. }
      eapply ES.cont_sb_dom_Einit; eauto.
      eapply himgInit; eauto.
      unfolder; eexists; splits; eauto.
      eapply wf_sbE, seq_eqv_lr in SB. 
      basic_solver.
    Qed.

    Lemma sim_add_jf_jf_delta_dom w k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SAJF : sim_add_jf (ES.cont_thread S k) st w e S S')
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :
      dom_rel (ESstep.jf_delta w e) ⊆₁ h □₁ (cert_dom G TC (ES.cont_thread S k) st).
    Proof. 
      autounfold with ESStepDb.
      edestruct sim_add_jf_iss_sb as [Iss | SB]; eauto. 
      { unfold cert_dom. generalize Iss. basic_solver 10. }
      eapply cont_sb_dom_in_hhdom in SB; eauto.
      basic_solver.
    Qed.

    Lemma sim_add_jf_jfe_delta_dom w k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SAJF : sim_add_jf (ES.cont_thread S k) st w e S S')
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :
      dom_rel (ESstep.jfe_delta S k w e) ⊆₁ h □₁ (I ∩₁ (GNtid_ (ES.cont_thread S k))).
    Proof. 
      autounfold with ESStepDb.
      edestruct sim_add_jf_iss_sb as [Iss | SB]; eauto. 
      { generalize Iss. basic_solver 10. }
      unfolder. ins. desc. subst.
      exfalso. auto. 
    Qed.

    (* Lemma sim_add_jf_jf_delta_ew w k k' e e' S S'  *)
    (*       (st st' st'' : thread_st (ES.cont_thread S k)) *)
    (*       (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')  *)
    (*       (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S')  *)
    (*       (SAJF : sim_add_jf (ES.cont_thread S k) st w e S S') *)
    (*       (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : *)
    (*   ESstep.jf_delta w e ⊆ Sew S ⨾ ESstep.jf_delta w e. *)
    (* Proof.  *)
    (*   assert (ES.Wf S) as WF. *)
    (*   { apply SRCC. } *)
    (*   eapply weaken_sim_add_jf in SAJF; eauto. *)
    (*   cdes SAJF. *)
    (*   autounfold with ESStepDb. *)
    (*   unfolder. ins. desf. *)
    (*   eexists; splits; eauto. *)
    (*   eapply ES.ew_refl; auto. *)
    (*   basic_solver. *)
    (* Qed. *)

    (* Lemma sim_add_jf_jfe_delta_ew w k k' e e' S S'  *)
    (*       (st st' st'' : thread_st (ES.cont_thread S k)) *)
    (*       (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')  *)
    (*       (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S')  *)
    (*       (SAJF : sim_add_jf (ES.cont_thread S k) st w e S S') *)
    (*       (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : *)
    (*   ESstep.jfe_delta S k w e ⊆ Sew S ⨾ ESstep.jfe_delta S k w e. *)
    (* Proof.  *)
    (*   assert (ES.Wf S) as WF. *)
    (*   { apply SRCC. } *)
    (*   eapply weaken_sim_add_jf in SAJF; eauto. *)
    (*   cdes SAJF. *)
    (*   autounfold with ESStepDb. *)
    (*   unfolder. ins. desf. *)
    (*   eexists; splits; eauto. *)
    (*   eapply ES.ew_refl; auto. *)
    (*   basic_solver. *)
    (* Qed. *)

    Lemma sim_add_jf_e2a_jf_vf w k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SAJF : sim_add_jf (ES.cont_thread S k) st w e S S')
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :
      e2a S' □ Sjf S' ⊆ Gvf.
    Proof. 
      assert (ESstep.add_jf w e S S') as AJF. 
      { eapply weaken_sim_add_jf; eauto. } 
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WF.
      { apply SRCC. }
      cdes BSTEP_; cdes SAJF; cdes AJF. 
      rewrite JF'.
      rewrite collect_rel_union.
      unionL.
      { eapply simrel_cert_basic_step_e2a_eqr; eauto; apply SRCC. }
      autounfold with ESStepDb.
      unfolder. ins. desf.
      eapply vf_in_furr; [by apply SRCC|].
      eapply cert_rf_in_vf; eauto. 
    Qed.

    Lemma sim_add_jf_hb_sw_delta_dom w k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
        (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
        (SAJF : sim_add_jf (ES.cont_thread S k) st w e S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
      dom_rel ((Shb S)^? ⨾ ESstep.sw_delta S S' k e e') ⊆₁ 
              h □₁ cert_dom G TC (ES.cont_thread S k) st.
    Proof. 
      cdes BSTEP_; cdes SAJF.
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor; eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      unfold ESstep.sw_delta. 
      relsf. rewrite !seqA. splits.
      { do 3 rewrite <- seqA. rewrite dom_seq, !seqA.
        eapply simrel_cert_basic_step_hb_rel_jf_sb_delta_dom; eauto. }
      rewrite JF'. relsf. splits.
      { etransitivity; [| apply set_subset_empty_l]. 
        ESBasicStep.step_solver. }
      do 3 rewrite <- seqA. rewrite dom_seq, !seqA.
      arewrite (ESstep.jf_delta w e ⊆ Sew S ⨾ ESstep.jf_delta w e).
      { apply ES.ew_domW; auto. 
        eapply weaken_sim_add_jf in SAJF; eauto.
        cdes SAJF. unfold ESstep.jf_delta. 
        unfolder. ins. desf. }
      etransitivity.
      2 : eapply hb_rel_ew_hD; eauto.
      unfold ESstep.jf_delta. 
      basic_solver 20.
    Qed.

    Lemma sim_add_jf_hb_delta_dom w k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
        (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
        (SAJF : sim_add_jf (ES.cont_thread S k) st w e S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
      dom_rel (ESstep.hb_delta S S' k e e') ⊆₁ 
              h □₁ cert_dom G TC (ES.cont_thread S k) st ∪₁ eq e. 
    Proof. 
      cdes BSTEP_; cdes SAJF.
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor; eauto. }
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      unfold ESstep.hb_delta.
      relsf. splits.
      { rewrite <- seqA, dom_seq.
        eapply simrel_cert_basic_step_hb_sb_delta_dom; eauto. }
      rewrite <- seqA, dom_seq.
      left; eapply sim_add_jf_hb_sw_delta_dom; eauto.
    Qed.

    (* Lemma sim_add_jf_jf_ncf w k k' e e' S S'  *)
    (*       (st st' st'' : thread_st (ES.cont_thread S k)) *)
    (*       (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')  *)
    (*       (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S')  *)
    (*       (SAJF : sim_add_jf (ES.cont_thread S k) st w e S S') *)
    (*       (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : *)
    (*   Sjf S' ∩ Scf S' ≡ ∅₂. *)
    (* Proof.  *)
    (*   assert (ESstep.add_jf w e S S') as AJF.  *)
    (*   { eapply weaken_sim_add_jf; eauto. }  *)
    (*   assert (ESBasicStep.t e e' S S') as BSTEP. *)
    (*   { econstructor. eauto. } *)
    (*   assert (ES.Wf S) as WF. *)
    (*   { apply SRCC. } *)
    (*   cdes BSTEP_; cdes SAJF; cdes AJF.  *)
    (*   split; [|done]. *)
    (*   rewrite JF'. *)
    (*   erewrite ESBasicStep.basic_step_cf; eauto. *)
    (*   rewrite !inter_union_l, !inter_union_r.  *)
    (*   unionL. *)

    (*   { apply ES.jf_ncf; apply SRCC. }  *)

    (*   1-2 : by ESBasicStep.step_solver. *)

    (*   autounfold with ESStepDb. *)
    (*   rewrite !csE, !transp_cross. *)
    (*   rewrite !inter_union_r.  *)
    (*   unionL. *)

    (*   2-4 : by ESBasicStep.step_solver. *)

    (*   unfolder. ins. desf. *)
    (*   eapply cfk_hdom; eauto.   *)
    (*   basic_solver. *)
    (* Qed. *)

    Lemma sim_add_jf_hb_jf_ncf w k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SAJF : sim_add_jf (ES.cont_thread S k) st w e S S')
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') 
          (nF' : eq_opt e' ∩₁ SF S' ⊆₁ ∅) :
      (Shb S' ⨾ Sjf S') ∩ Scf S' ≡ ∅₂.
    Proof. 
      assert (ESstep.add_jf w e S S') as AJF. 
      { eapply weaken_sim_add_jf; eauto. } 
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WF.
      { apply SRCC. }
      cdes BSTEP_; cdes SAJF; cdes AJF. 
      split; [|done].
      rewrite JF'.
      erewrite ESstep.step_add_jf_hb; eauto. 
      erewrite ESBasicStep.basic_step_cf; eauto.
      relsf. rewrite !inter_union_l, !inter_union_r. 
      unionL.

      { apply jf_necf_hb_jf_ncf; apply SRCC. }

      all : try by ESBasicStep.step_solver.

      autounfold with ESStepDb.
      rewrite !csE, !inter_union_r.
      unionL.

      { unfolder. ins. desf. 
        eapply cfk_hdom; eauto. 
        split; [|eauto]. 
        eapply hb_hD; eauto. 
        basic_solver 10. }

      all : by ESBasicStep.step_solver. 
    Qed.

    Lemma sim_add_jf_hb_tjf_ncf w k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SAJF : sim_add_jf (ES.cont_thread S k) st w e S S')
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') 
          (nF' : eq_opt e' ∩₁ SF S' ⊆₁ ∅) :
      (Shb S' ⨾ (Sjf S')⁻¹) ∩ Scf S' ≡ ∅₂.
    Proof. 
      assert (ESstep.add_jf w e S S') as AJF. 
      { eapply weaken_sim_add_jf; eauto. } 
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WF.
      { apply SRCC. }
      cdes BSTEP_; cdes SAJF; cdes AJF. 
      split; [|done].
      rewrite JF'.
      erewrite ESstep.step_add_jf_hb; eauto. 
      erewrite ESBasicStep.basic_step_cf; eauto.
      rewrite !transp_union.
      relsf. rewrite !inter_union_l, !inter_union_r. 
      unionL.

      { apply jf_necf_hb_tjf_ncf; apply SRCC. }

      all : try by ESBasicStep.step_solver.

      erewrite dom_rel_helper with (r := ESstep.hb_delta S S' k e e').
      2 : { eapply sim_add_jf_hb_delta_dom; eauto. }
      rewrite id_union. relsf.
      rewrite !inter_union_l.
      unionL.
      
      2 : by ESBasicStep.step_solver. 

      unfold ESstep.jf_delta.
      rewrite transp_singl_rel.
      intros x y [HH CF].
      destruct HH as [a [[b [certD HBd]] JFd]].
      eapply a2e_ncf.
      { apply SRCC.(sr_a2e_h). }
      apply seq_eqv_lr. 
      splits; [apply certD| apply CF |]. 
      unfold singl_rel in JFd. desf.
    Qed.

    Lemma sim_add_jf_hb_jf_thb_ncf w k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SAJF : sim_add_jf (ES.cont_thread S k) st w e S S')
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') 
          (nF' : eq_opt e' ∩₁ SF S' ⊆₁ ∅) :
      (Shb S' ⨾ Sjf S' ⨾ (Shb S')⁻¹) ∩ Scf S' ≡ ∅₂.
    Proof. 
      assert (ESstep.add_jf w e S S') as AJF. 
      { eapply weaken_sim_add_jf; eauto. } 
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WF.
      { apply SRCC. }
      cdes BSTEP_; cdes SAJF; cdes AJF. 
      split; [|done].
      rewrite JF'.
      erewrite ESstep.step_add_jf_hb; eauto. 
      rewrite transp_union. relsf.
      
      arewrite_false (ESstep.jf_delta w e ⨾ (Shb S)⁻¹).
      { ESBasicStep.step_solver. }
      arewrite_false (ESstep.hb_delta S S' k e e' ⨾ Sjf S).
      { ESBasicStep.step_solver. }
      arewrite_false (Sjf S ⨾ (ESstep.hb_delta S S' k e e')⁻¹).
      { ESBasicStep.step_solver. }
      arewrite_false (ESstep.hb_delta S S' k e e' ⨾ ESstep.jf_delta w e).
      { ESBasicStep.step_solver. }
      relsf.

      erewrite ESBasicStep.basic_step_cf; eauto.
      relsf. rewrite !inter_union_l, !inter_union_r. 
      unionL.

      2,4 : ESBasicStep.step_solver. 

      { apply jf_necf_hb_jf_thb_ncf; apply SRCC. }
      
      unfold ESstep.jf_delta.
      intros x y [HH CF].
      destruct HH as [a [HB [b [JFd HBd]]]].
      eapply a2e_ncf.
      { apply SRCC.(sr_a2e_h). }
      apply seq_eqv_lr. 
      splits; [|apply CF|].
      { eapply hb_hD; eauto.
        unfolder in JFd. desc. subst a b.
        basic_solver 10. }
      unfold transp in HBd.
      edestruct sim_add_jf_hb_delta_dom as [HX | HY]; eauto.
      { basic_solver. }
      exfalso. subst y.
      apply ES.cfE, seq_eqv_lr in CF.
      ESBasicStep.step_solver. 
    Qed.

    Lemma sim_add_jf_jf_necf w k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SAJF : sim_add_jf (ES.cont_thread S k) st w e S S')
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') 
          (nF' : eq_opt e' ∩₁ SF S' ⊆₁ ∅) :
      Sjf S' ∩ Secf S' ≡ ∅₂. 
    Proof. 
      apply jf_necf_alt; splits.
      { eapply sim_add_jf_jf_ncf; eauto. }
      { eapply sim_add_jf_hb_jf_ncf; eauto. } 
      { eapply sim_add_jf_hb_tjf_ncf; eauto. }
      eapply sim_add_jf_hb_jf_thb_ncf; eauto.
    Qed.
    
    Lemma sim_add_jf_jfe_vis w k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SAJF : sim_add_jf (ES.cont_thread S k) st w e S S') 
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
      dom_rel (Sjfe S') ⊆₁ vis S. 
    Proof. 
      assert (ESstep.add_jf w e S S') as AJF. 
      { eapply weaken_sim_add_jf; eauto. } 
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ES.Wf S) as WF.
      { apply SRCC. }
      cdes BSTEP_; cdes SAJF; cdes AJF. 
      erewrite ESstep.step_add_jf_jfe; eauto.
      rewrite dom_union. 
      apply set_subset_union_l. split. 
      { apply SRCC. }
      rewrite sim_add_jf_jfe_delta_dom; eauto.
      etransitivity; [|eapply hvis]; eauto.
      basic_solver 10.
    Qed.

    Lemma sim_add_jf_jfe_fI w k k' e e' S S' 
          (st st' st'' : thread_st (ES.cont_thread S k))
          (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
          (BSTEP_ : ESBasicStep.t_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
          (SAJF : sim_add_jf (ES.cont_thread S k) st w e S S') 
          (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
      dom_rel (Sjfe S') ⊆₁ dom_rel (Sew S ⨾ ⦗ f □₁ I ⦘). 
    Proof. 
      assert (ES.Wf S) as WF.
      { apply SRCC. }
      assert (ESBasicStep.t e e' S S') as BSTEP.
      { econstructor. eauto. }
      assert (ESstep.add_jf w e S S') as AJF. 
      { eapply weaken_sim_add_jf; eauto. } 
      cdes BSTEP_; cdes SAJF.
      erewrite ESstep.step_add_jf_jfe; eauto.
      rewrite dom_union. unionL. 
      { eapply jfe_fI. apply SRCC. }
      
      erewrite sim_add_jf_jfe_delta_dom; eauto.
      erewrite <- set_collect_eq_dom 
        with (g := h).
      2 : eapply eq_dom_mori; try eapply hfeq; eauto; red; basic_solver 10.
      etransitivity.
      2 : eapply ES.ew_eqvW; auto.
      { basic_solver. }
      eapply fI_EW; apply SRCC.
    Qed.

  End SimRelAddJFProps. 
  
End SimRelAddJF.
