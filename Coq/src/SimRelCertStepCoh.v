Require Import Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution
     Traversal TraversalConfig SimTraversal SimTraversalProperties
     Prog ProgToExecution ProgToExecutionProperties Receptiveness
     imm_common imm_s imm_s_hb SimulationRel
     CertExecution2 CertExecutionMain
     SubExecution CombRelations AuxRel.
Require Import AuxRel.
Require Import AuxDef.
Require Import EventStructure.
Require Import Consistency.
Require Import Execution.
Require Import BasicStep.
Require Import AddJF.
Require Import AddEW.
Require Import AddCO.
Require Import Step.
Require Import StepWf.
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
Require Import SimRelAddJF.
Require Import SimRelAddEW.
Require Import SimRelAddCO.
Require Import SimRelCertStep.
Require Import ProgES.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelCertStepCoh.

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
  Notation "'Sfr' S" := S.(ES.fr) (at level 10).
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
  Notation "'Seco' S" := (Consistency.eco S Weakestmo) (at level 10).

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
  Notation "'Gvf' t" := (vf G sc TC' t) (at level 10, only parsing).

  Notation "'Geco'" := (Execution_eco.eco G).

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

  Notation "'cont_lang'" :=
    (fun S k => thread_lts (ES.cont_thread S k)) (at level 10, only parsing).

  Notation "'kE' S" := (fun k => ES.cont_sb_dom S k) (at level 1, only parsing).
  Notation "'ktid' S" := (fun k => ES.cont_thread S k) (at level 1, only parsing).

  Notation "'certX' S" := (fun k => (X ∩₁ SNTid_ S (ktid S k)) ∪₁ (kE S k)) (at level 1, only parsing).

  Lemma simrel_cert_step_hb_delta_dom k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'') 
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
    dom_rel (hb_delta S S' k e e') ⊆₁ certX S k ∪₁ eq e.
  Proof. 
    cdes CertSTEP; cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (step_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    unfold hb_delta. relsf. split. 
    { rewrite <- seqA, dom_seq.
      eapply simrel_cert_basic_step_hb_sb_delta_dom; eauto. }
    unfold_cert_step_ CertSTEP_.
    all : rewrite <- seqA, dom_seq.
    2,4 : left; eapply sim_add_jf_hb_sw_delta_dom; eauto. 
    all : unfold sw_delta.
    all : rewrite JF'; relsf; rewrite !seqA; splits.
    2,4 : step_solver.
    all : do 3 rewrite <- seqA; rewrite dom_seq, !seqA.
    all : left; eapply simrel_cert_basic_step_hb_rel_jf_sb_delta_dom; eauto.
  Qed.

  Lemma simrel_cert_step_hb_cf_irr k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
    irreflexive (Shb S' ⨾ Scf S').
  Proof.
    cdes CertSTEP; cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (step_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    erewrite step_hb; eauto.
    erewrite basic_step_cf; eauto.
    relsf. rewrite !irreflexive_union. splits.

    { eapply ecf_irr_hb_cf_irr. apply SRCC. }

    { step_solver. } 

    { autounfold with ESStepDb.
      rewrite !csE, !transp_cross.
      relsf. rewrite !irreflexive_union. splits.
      2,4 : by step_solver.
      { intros x [y [HB [KCF EQe]]].
        subst x. apply hbE, seq_eqv_lr in HB; auto. desf.
        eapply basic_step_acts_set_ne; eauto. }
      unfold eq_opt. destruct e' as [e'|]; [|basic_solver].
      intros x [y [HB [KCF EQOPTe]]].
      subst x. apply hbE, seq_eqv_lr in HB; auto. desf.
      eapply basic_step_acts_set_ne'; eauto. }

    unfold cf_delta.
    rewrite !csE, !transp_cross. relsf.
    arewrite_false (hb_delta S S' k e e' ⨾ ES.cont_cf_dom S k × eq e).
    { step_solver. }
    arewrite_false (hb_delta S S' k e e' ⨾ ES.cont_cf_dom S k × eq_opt e'). 
    { step_solver. }
    relsf.

    erewrite dom_rel_helper with (r := hb_delta S S' k e e').
    2 : { eapply simrel_cert_step_hb_delta_dom; eauto. }
    rewrite id_union. 
    relsf. rewrite !irreflexive_union. splits.
    all : try by step_solver.
    all : unfolder; ins; desc. 
    all : eapply certX_ncf_cont; eauto.
    all : basic_solver.
  Qed.

  Lemma simrel_cert_step_thb_cf_hb_irr k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
    irreflexive ((Shb S')⁻¹ ⨾ (Scf S') ⨾ (Shb S')).
  Proof.
    cdes CertSTEP; cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (step_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    erewrite step_hb; eauto.
    erewrite basic_step_cf; eauto.
    unfold cf_delta.
    erewrite dom_rel_helper with (r := hb_delta S S' k e e').
    2 : { eapply simrel_cert_step_hb_delta_dom; eauto. }
    rewrite !transp_union.
    relsf. rewrite !irreflexive_union. splits.

    { eapply ecf_irr_thb_cf_hb_irr. apply SRCC. }

    1-8 : step_solver.

    all : rewrite !id_union with (s := certX S k) (s' := eq e).
    all : rewrite !transp_seq, !transp_union, !transp_eqv_rel. 
    all : relsf; rewrite !seqA.

    { arewrite_false (Scf S ⨾ ⦗eq e⦘).
      { step_solver. }
      arewrite_false (⦗eq e⦘ ⨾ Scf S).
      { step_solver. }
      relsf. 
      unfolder. ins. desc. subst.
      eapply cert_ex_ncf; eauto. 
      unfolder. eauto 20. }

    { erewrite cert_ex_inE at 1 2; eauto.
      arewrite_false 
        (⦗SE S⦘ ⨾ (ES.cont_cf_dom S k × eq e) ^⋈ ⨾ ⦗SE S⦘).
      { step_solver. }
      arewrite_false 
      (⦗eq e⦘ ⨾ (ES.cont_cf_dom S k × eq e) ^⋈ ⨾ ⦗eq e⦘).
      { step_solver. }
      relsf.

      rewrite !csE. relsf.
      arewrite_false (eq e × ES.cont_cf_dom S k ⨾ ⦗eq e⦘).
      { step_solver. }
      arewrite_false (⦗eq e⦘ ⨾ ES.cont_cf_dom S k × eq e).
      { step_solver. }
      relsf. rewrite !irreflexive_union. splits.
      all : unfolder; ins; desc; subst.
      all : eapply certX_ncf_cont; eauto.
      all : basic_solver. }

    erewrite cert_ex_inE; eauto.
    arewrite_false 
      (⦗SE S⦘ ⨾ (ES.cont_cf_dom S k × eq_opt e') ^⋈ ⨾ ⦗SE S⦘).
    { step_solver. }
    arewrite_false 
    (⦗SE S⦘ ⨾ (ES.cont_cf_dom S k × eq_opt e') ^⋈ ⨾ ⦗eq e⦘).
    { step_solver. }
    arewrite_false 
    (⦗eq e⦘ ⨾ (ES.cont_cf_dom S k × eq_opt e') ^⋈ ⨾ ⦗SE S⦘).
    { step_solver. }
    arewrite_false 
    (⦗eq e⦘ ⨾ (ES.cont_cf_dom S k × eq_opt e') ^⋈ ⨾ ⦗eq e⦘).
    { step_solver. }
    basic_solver.
  Qed.

  Lemma simrel_cert_step_jf_necf k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
    Sjf S' ∩ Secf S' ≡ ∅₂. 
  Proof. 
    cdes CertSTEP; cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (step_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    unfold_cert_step_ CertSTEP_.
    1,3 : 
      eapply step_same_jf_jf_necf; 
      eauto; try apply SRCC;
        eapply basic_step_nupd_rmw;
        subst; eauto.
    { eapply sim_add_jf_jf_necf; eauto.
      subst. basic_solver. }
    eapply sim_add_jf_jf_necf; eauto.
    cdes AEW. type_solver.
  Qed.

  Lemma simrel_cert_step_jfe_vis k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
    dom_rel (Sjfe S') ⊆₁ (vis S'). 
  Proof. 
    cdes CertSTEP; cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (step_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WFS by apply SRCC.
    etransitivity. 
    2 : eapply step_vis_mon; eauto.
    unfold_cert_step_ CertSTEP_.
    all : try (by eapply sim_add_jf_jfe_vis; eauto).
    all : rewrite step_same_jf_jfe; eauto; apply SRCC.
  Qed.

  Lemma simrel_cert_step_jf_delta_coh w k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (SAJF : sim_add_jf G sc TC' X k w e S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
    irreflexive (Sco S' ⨾ (Sjf S')^? ⨾ Shb S' ⨾ (jf_delta w e)⁻¹).
  Proof. 
    cdes CertSTEP; cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (step_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WF by apply SRCC.
    assert (ES.Wf S') as WFS.
    { eapply simrel_cert_step_wf; eauto. }
    assert (simrel_cont (stable_prog_to_prog prog) S' G TC) as SRCONT.
    { eapply basic_step_simrel_cont; try apply SRCC; eauto. 
      eapply cstate_covered; eauto. }
    assert (simrel_e2a S' G sc) as SRE2A.
    { eapply simrel_cert_step_e2a; eauto. }
    assert (simrel_ prog S' G sc TC X) as SR_.
    { eapply simrel_cert_step_simrel_; eauto. }
    assert (Wf G) as WFG. 
    { apply SRCC. }
    assert (coherence G) as GCOH.
    { eapply gcons. apply SRCC. }

    assert (e2a S' □ Ssb S' ⊆ Gsb) as SBN.
    { eapply e2a_sb; eauto; try apply SRCC.
      2: by eapply e2a_GE; eauto.
      apply stable_prog_to_prog_no_init; apply SRCC. }
    
    assert (e2a S' □ Shb S' ⊆ Ghb) as HBN.
    { eapply e2a_hb; eauto; try apply SRCC.
      all: apply SRE2A. }

    assert 
      (e2a S' □ jf_delta w e ⊆ cert_rf G sc TC' (ktid S k))
      as JFdN.
    { cdes SAJF. unfold jf_delta. basic_solver. }

    erewrite hb_in_ex_cov_hb_sb; eauto.
    (* erewrite basic_step_e2a_set_map_inter_old *)
    (*   with (S:= S); eauto. *)
    (* 2 : apply Execution.ex_inE; apply SRCC. *)
    relsf. rewrite irreflexive_union. split.

    { eapply collect_rel_irr with (f := e2a S').
      do 3 rewrite <- seqA.
      do 2 rewrite collect_rel_seqi.
      rewrite collect_rel_transp.
      rewrite !seqA.
      (* TODO: make a lemma *)
      arewrite (e2a S' □ Sco S' ⨾ (Sjf S')^? ⨾ ⦗X ∩₁ e2a S' ⋄₁ C⦘ ⊆ Gco ⨾ (Grf ⨾ ⦗C⦘)^?).    
      { eapply e2a_co_jf_cov; eauto. }
      erewrite sim_add_jf_jf_delta_in_cert_rf; eauto.
      rewrite HBN.
      rewrite (dom_r WFG.(wf_coD)), !seqA.
      arewrite (⦗GW⦘ ⨾ (Grf ⨾ ⦗C⦘)^? ⨾ Ghb ⊆ vf G sc TC' (ktid S' k')).
      2: unfold cert_rf; basic_solver 42.
      unfold vf.
      unionR left.
      arewrite (C ⊆₁ C').
      { eapply sim_trav_step_covered_le.
        eexists. apply SRCC. }
      rewrite wf_hbE at 1; auto.
      basic_solver 20. }

    rewrite ES.jfi_union_jfe.
    rewrite unionC, cr_union_r.
    relsf. rewrite irreflexive_union. split.

    { eapply collect_rel_irr with (f := e2a S').
      arewrite ((jf_delta w e)⁻¹ ≡ ⦗eq e⦘ ⨾ (jf_delta w e)⁻¹).
      { unfold jf_delta. basic_solver. }
      arewrite 
        (Ssb S' ⨾ ⦗eq e⦘ ≡ ⦗kE S k⦘ ⨾ Ssb S' ⨾ ⦗eq e⦘).
      { apply dom_rel_helper.
        erewrite basic_step_sbe; eauto.
        basic_solver. }
      do 2 rewrite <- seqA.
      rewrite collect_rel_seqi.
      rewrite !seqA.
      arewrite 
        (Sjfe S' ⨾ ⦗ES.cont_sb_dom S k⦘ ⊆ Sjfe S ⨾ ⦗ES.cont_sb_dom S k⦘).
      { rewrite <- seq_eqvK.
        rewrite kE_inE at 1; eauto.
        rewrite <- seqA.
        erewrite add_jf_jfeE; eauto.
        { basic_solver. }
        eapply weaken_sim_add_jf; eauto. }
      erewrite dom_rel_helper with (r := Sjfe S).
      2 : { eapply jfe_ex_iss. apply SRCC. }
      rewrite !seqA, <- seqA.
      rewrite collect_rel_seqi.
      arewrite 
        (e2a S' □ Sco S' ⨾ ⦗dom_rel (Sew S ⨾ ⦗X ∩₁ e2a S ⋄₁ I⦘)⦘ ⊆ Gco).
      { erewrite step_ew_mon; eauto.
        erewrite <- basic_step_e2a_set_map_inter_old
          with (S := S); eauto.
        2 : apply Execution.ex_inE; apply SRCC.
        rewrite seq_eqv_r.
        intros x' y' [x [y [[CO DD] [EQx' EQy']]]].
        destruct DD as [z HH].
        apply seq_eqv_r in HH. desf.
        arewrite (e2a S' y = e2a S' z).
        { eapply e2a_ew; eauto. basic_solver 10. }
        eapply e2a_co_ew_iss; eauto.
        basic_solver 30. }
      arewrite (Sjfe S ⊆ Sjf S).
      erewrite basic_step_e2a_collect_rel_eq_dom
        with (r := Sjf S ⨾ ⦗ES.cont_sb_dom S k⦘) (S := S); eauto.
      2 : { rewrite ES.jfE; auto. basic_solver. }
      erewrite jf_in_cert_rf; eauto.
      arewrite_id (⦗eq e⦘).
      rewrite seq_id_l.
      rewrite collect_rel_seqi.
      rewrite collect_rel_transp.
      rewrite SBN.
      erewrite sim_add_jf_jf_delta_in_cert_rf; eauto.
      rewrite cert_rf_in_vf. 
      sin_rewrite vf_sb_in_vf.
      erewrite <- basic_step_cont_thread_k; eauto.
      unfold cert_rf; basic_solver 10. }

    arewrite ((Sjfi S')^? ⨾ Ssb S' ⊆ Ssb S').
    { rewrite crE. relsf. 
      unionL; [done|].
      unfold ES.jfi. 
      rewrite inclusion_inter_l2.
      rewrite transitiveI.
      by apply ES.sb_trans. }
    
    unfold jf_delta, singl_rel, transp.
    intros x [y [CO [z [SB [EQx EQz]]]]]. 
    subst x z.
    eapply JFdN.
    { unfold jf_delta. exists w, e. basic_solver. }
    exists (e2a S' y). split.
    { eapply e2a_co_ncf; eauto.
      unfolder. do 2 eexists. 
      splits; eauto.
      intros CF.
      eapply sim_add_jf_ncf_we; eauto.
      eapply ES.cf_sb_in_cf; auto. 
      basic_solver. }
    eapply sb_in_vf.
    apply seq_eqv_l. split.
    { eapply e2a_W; eauto; try apply SRE2A.
      unfolder; eexists; splits; eauto.
      { apply ES.coE in CO; auto.
        generalize CO. basic_solver. }
      apply ES.coD in CO; auto.
      generalize CO. basic_solver. }
    eapply e2a_sb; eauto; try apply SR_.
    (* TODO: make a lemma *)
    { intros PROG_INIT. 
      eapply noinitprog; eauto. 
      unfold stable_prog_to_prog in PROG_INIT.
      eapply IdentMap.map_2; eauto. }
    basic_solver 10.
  Qed.

  Lemma simrel_cert_step_fr_coh k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
    irreflexive (Shb S' ⨾ ES.fr S' ⨾ (Srf S')^?).
  Proof. 
    cdes CertSTEP; cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (step_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WF by apply SRCC.
    assert (ES.Wf S') as WFS.
    { eapply simrel_cert_step_wf; eauto. }
    assert (simrel_cont (stable_prog_to_prog prog) S' G TC) as SRCONT.
    { eapply basic_step_simrel_cont; try apply SRCC; eauto. 
      eapply cstate_covered; eauto. }
    assert (simrel_e2a S' G sc) as SRE2A.
    { eapply simrel_cert_step_e2a; eauto. }
    assert (simrel_ prog S' G sc TC X) as SR_.
    { eapply simrel_cert_step_simrel_; eauto. }
    assert (Wf G) as WFG. 
    { apply SRCC. }
    assert (@es_consistent S Weakestmo) as SCONS.
    { apply SRCC. }
    assert (coherence G) as GCOH.
    { eapply gcons. apply SRCC. }

    rewrite ES.fr_alt; auto.
    rewrite !seqA.
    arewrite (Sco S' ⨾ (Srf S')^? ≡ Sco S' ⨾ (Sjf S')^?).
    { rewrite !crE. relsf.
      apply union_more; auto.
      apply ES.co_rf_alt; auto. }
    rewrite <- !seqA. apply irreflexive_seqC.
    rewrite <- !seqA. apply irreflexive_seqC.
    rewrite !seqA.

    assert (e2a S' □ Ssb S' ⊆ Gsb) as SBN.
    { eapply e2a_sb; eauto; try apply SRCC.
      2: by eapply e2a_GE; eauto.
      apply stable_prog_to_prog_no_init; apply SRCC. }
    
    assert (e2a S' □ Shb S' ⊆ Ghb) as HBN.
    { eapply e2a_hb; eauto; try apply SRCC.
      all: apply SRE2A. }

    assert 
    (irreflexive (Sco S' ⨾ (Sjf S')^? ⨾ Shb S' ⨾ (Sjf S)⁻¹)) 
      as IrrH.
    { arewrite (Shb S' ⨾ (Sjf S)⁻¹ ≡ Shb S ⨾ (Sjf S)⁻¹).
      { arewrite ((Sjf S)⁻¹ ≡ ⦗SE S⦘ ⨾ (Sjf S)⁻¹) at 1.
        { rewrite ES.jfE; auto. basic_solver. }
        rewrite <- seqA. erewrite step_hbE; eauto. }
      arewrite ((Sjf S')^? ⨾ Shb S ≡ (Sjf S)^? ⨾ Shb S).
      { rewrite !crE. relsf.
        apply union_more; auto.
        arewrite (Shb S ≡ ⦗SE S⦘ ⨾ Shb S) at 1.
        { rewrite hbE; auto. basic_solver. }
        (* TODO: lemma *)
        arewrite (Sjf S' ⨾ ⦗SE S⦘ ≡ Sjf S); auto.
        unfold_cert_step_ CertSTEP_.
        1,3: rewrite JF', ES.jfE; basic_solver.
        all : 
          eapply add_jf_jfE; eauto;
          eapply weaken_sim_add_jf; eauto. }
      unfold_cert_step_ CertSTEP_.
      all: try cdes ACO; rewrite CO'.
      1,2: apply co_jf_hb_tjf_irr; auto.
      all: unfold co_delta.
      all: rewrite add_co_ws_complE; auto.
      all: rewrite sim_wsE.
      all: relsf.
      all: rewrite !irreflexive_union; 
        splits; try done. 
      all: try step_solver. 
      all: apply co_jf_hb_tjf_irr; auto. }

    unfold_cert_step_ CertSTEP_.
    1,3: by rewrite JF' at 2. 
    all: cdes AJF; rewrite JF' at 2.
    all: rewrite transp_union; relsf.
    all: rewrite !irreflexive_union; 
      splits; try done.
    all: eapply simrel_cert_step_jf_delta_coh; eauto.
    
    all: arewrite ((jf_delta w e)⁻¹ ≡
                                 ⦗ eq e ⦘ ⨾ (jf_delta w e)⁻¹)
      by (unfold jf_delta; basic_solver).
    all: do 3 rewrite <- seqA.
    all: rewrite seqA with (r1 := Sco S' ⨾ (Sjf S')^?).
    all: rewrite seqA with (r1 := Sco S').
    all: eapply collect_rel_irr with (f := e2a S').
    all: rewrite collect_rel_seqi.
    all: arewrite (e2a S' □ (jf_delta w e)⁻¹ ⊆ 
                       (cert_rf G sc TC' (ktid S k))⁻¹)
      by (unfold jf_delta; basic_solver).
  Qed.

  Lemma simrel_cert_step_coh k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
    irreflexive (Shb S' ⨾ (Seco S')^?).
  Proof. 
    cdes CertSTEP; cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (step_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.Wf S) as WF by apply SRCC.
    assert (ES.Wf S') as WFS.
    { eapply simrel_cert_step_wf; eauto. }
    assert (simrel_e2a S' G sc) as SRE2A.
    { eapply simrel_cert_step_e2a; eauto. }
    assert (Wf G) as WFG. 
    { apply SRCC. }
    assert (coherence G) as GCOH.
    { eapply gcons. apply SRCC. }
    set (AA:=SRE2A).
    destruct AA.
    
    rewrite crE. rewrite eco_alt; auto.
    rewrite crE at 1.
    rewrite !seq_union_r, !seq_id_r.
    rewrite <- !unionA.
    apply irreflexive_union. splits.
    2: by eapply simrel_cert_step_fr_coh; eauto.
    eapply collect_rel_irr with (f := e2a S').
    rewrite !collect_rel_union.
    rewrite !collect_rel_seqi.
    erewrite e2a_hb; eauto; try apply SRCC.
    erewrite e2a_co; eauto.
    erewrite e2a_rf, e2a_jf; eauto.
    rewrite !crE. relsf.
    arewrite 
      (Ghb ∪ Ghb ⨾ Gfurr ∪ (Ghb ∪ Ghb ⨾ Gco) ∪ (Ghb ⨾ Gfurr ∪ Ghb ⨾ Gco ⨾ Gfurr) ≡
       Ghb ∪ Ghb ⨾ Gfurr ∪ Ghb ⨾ Gco ∪ Ghb ⨾ Gco ⨾ Gfurr).
    { basic_solver 10. }
    rewrite !irreflexive_union. splits.
    { apply hb_irr; eauto. }
    { intros x [y [HB VF]].
      unfold furr in VF. desc.
      eapply urr_hb_irr; try apply SRCC.
      basic_solver. }
    { arewrite (Gco ⊆ Geco^?).
      2: by apply GCOH.
      rewrite Execution_eco.co_in_eco. basic_solver. }
    intros x [y [HB [z [CO VF]]]].
    unfold furr in VF. desc.  
    eapply eco_urr_irr; try apply SRCC.
    eexists. splits.
    { unfold Execution_eco.eco. basic_solver 10. }
    eapply urr_hb. basic_solver.
  Qed.

  Lemma simrel_cert_step_consistent k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
    @es_consistent S' Weakestmo. 
  Proof. 
    cdes CertSTEP; cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    constructor.
    { eapply ecf_irr_alt. split.
      { eapply simrel_cert_step_hb_cf_irr; eauto. }
      eapply simrel_cert_step_thb_cf_hb_irr; eauto. }
    { eapply simrel_cert_step_jf_necf; eauto. }
    { eapply simrel_cert_step_jfe_vis; eauto. }
    { eapply simrel_cert_step_coh; eauto. }
    { admit. }
    admit. 
  Admitted.

  Lemma simrel_cert_lbl_step k S
        (st st' st'': (thread_lts (ktid S k)).(Language.state))
        (NINIT : ktid S k <> tid_init)
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (LBL_STEP : lbl_step (ktid S k) st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    exists k' S',
      ⟪ kTID : ktid S' k' = ktid S k ⟫ /\
      ⟪ ESSTEP : (step Weakestmo)^? S S' ⟫ /\
      ⟪ SRCC' : simrel_cert prog S' G sc TC TC' X k' st' st''⟫.
  Proof.
    edestruct LBL_STEP as [lbl ILBL_STEP].
    edestruct simrel_cert_step as [k' HH]; eauto. desc.
    cdes CertSTEP.
    assert (Wf G) as WF by apply SRCC.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (step_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (ES.cont_thread S' k' = ES.cont_thread S k) as CTS.
    { cdes BSTEP_. desf. simpls.
      rewrite TID'. unfold upd_opt, opt_ext. desf.
      all: by rewrite upds. }
    assert (X ⊆₁ X ∩₁ SE S) as XSE.
    { apply set_subset_inter_r. split; [done|].
      eapply Execution.ex_inE. apply SRCC. }
    assert (simrel prog S' G sc TC X) as SRC'.
    { red. splits.
      { eapply simrel_cert_step_simrel_; eauto. }
      eapply simrel_cert_step_consistent; eauto. }

    assert (forall s (SES : s ⊆₁ SE S) s',
               s ∩₁ e2a S' ⋄₁ s' ⊆₁ s ∩₁ e2a S ⋄₁ s') as SSE2A.
    { unfolder. ins. desf. splits; auto.
      erewrite <- basic_step_e2a_eq_dom; eauto. }
    exists k', S'. splits.
    { eapply basic_step_cont_thread_k; eauto. }
    { apply r_step. red.
      do 2 eexists; splits; eauto.
      eapply simrel_cert_step_consistent; eauto. }
    constructor; auto.
    (* tr_step : isim_trav_step G sc (ktid S k') TC TC' *)
    { erewrite basic_step_cont_thread_k; eauto. apply SRCC. }
    (* cert : cert_graph G sc TC TC' (ktid S k') state'' *)
    { erewrite basic_step_cont_thread_k; eauto. apply SRCC. }
    (* cstate : simrel_cstate *)
    { eapply simrel_cert_basic_step_cstate; eauto. } 
    { erewrite basic_step_cont_sb_dom; eauto.
      unionR left -> left.
      rewrite XSE, CTS.
      arewrite (X ∩₁ SE S ∩₁ (fun x => Stid S' x = ES.cont_thread S k) ⊆₁
                X ∩₁ SE S ∩₁ (fun x => Stid S  x = ES.cont_thread S k)).
      { unfolder. ins. desf. splits; auto.
        erewrite <- basic_step_tid_eq_dom; eauto. }
      rewrite SSE2A; [|basic_solver].
      arewrite (X ∩₁ SE S ⊆₁ X) by basic_solver.
      apply SRCC. }
    { erewrite basic_step_cont_sb_dom; eauto.
      rewrite set_unionA.
      rewrite set_inter_union_r.
      unionL.
      { unfolder. ins. desf. apply SRCC.(cov_in_ex).
        unfolder. splits; auto.
        erewrite <- basic_step_e2a_eq_dom; eauto.
        eapply kE_inE; eauto. }
      admit. }
    { erewrite basic_step_cont_sb_dom; eauto.
      erewrite basic_step_acts_init_set; eauto.
      rewrite set_unionA.
      rewrite set_minus_union_l.
      eapply eq_dom_union. split.
      { unfolder. ins. desf. unfold Basics.compose.
        assert (SE S x) as EX.
        { eapply kE_inE; eauto. }
        erewrite basic_step_lab_eq_dom; eauto.
        erewrite basic_step_e2a_eq_dom; eauto.
        eapply kE_lab; eauto. by split. }
      unfolder. ins. desf.
      { eapply basic_step_e2a_lab_e; eauto; apply SRCC. }
      eapply basic_step_e2a_lab_e'; eauto; apply SRCC. }
    { erewrite basic_step_cont_sb_dom; eauto.
      rewrite !id_union. rewrite !seq_union_r, !collect_rel_union.
      rewrite CTS.
      unionL.
      { erewrite <- jf_in_cert_rf; eauto.
        arewrite (⦗ES.cont_sb_dom S k⦘ ⊆ ⦗SE S⦘ ⨾ ⦗ES.cont_sb_dom S k⦘).
        { rewrite <- seq_eqvK at 1. by erewrite kE_inE at 1; eauto. }
        arewrite (Sjf S' ⨾ ⦗SE S⦘ ⊆ Sjf S).
        { eapply simrel_cert_step_jf_E; eauto. }
        (* TODO: introduce a lemma e2a S' □ restr_rel (SE S) r ⊆ e2a S □ r. *)
        rewrite ES.jfE at 1; try apply SRCC.
        unfolder. ins. desf. do 2 eexists. splits; eauto.
        all: symmetry.
        all: eapply basic_step_e2a_eq_dom; eauto. }
      { assert (Sjf S ⨾ ⦗eq e⦘ ⊆ ∅₂) as AA.
        { rewrite ES.jfE; try apply SRCC. unfold ES.acts_set.
          cdes BSTEP_. desf. unfolder. ins. omega. }
        red in CertSTEP_. desf; cdes CertSTEP_.
        1,3: rewrite JF'; rewrite AA; basic_solver.
        all: cdes AJF; rewrite JF';
          rewrite seq_union_l, collect_rel_union; unionL.
        1,3: rewrite AA; basic_solver.
        all: unfold jf_delta; unfolder; ins; desf. }
      arewrite (Sjf S' ⨾ ⦗eq_opt e'⦘ ⊆ ∅₂).
      2: basic_solver.
      assert (Sjf S ⨾ ⦗eq_opt e'⦘ ⊆ ∅₂) as AA.
      { cdes BSTEP_. rewrite ES.jfE; try apply SRCC.
        unfold ES.acts_set.
        unfolder. ins. desf. simpls. desf. omega. }
      cdes BSTEP_. desf.
      red in CertSTEP_. desf; cdes CertSTEP_.
      1,3: by rewrite JF'.
      all: cdes AJF; rewrite JF'; rewrite seq_union_l; unionL; auto.
      all: unfold jf_delta.
      { basic_solver. }
      desf. simpls. desf. unfolder. ins. desf. omega. }
    { admit. }
    erewrite basic_step_cont_sb_dom; eauto.
    rewrite !set_collect_union.
    rewrite !set_inter_union_r.
    rewrite !id_union.
    rewrite !seq_union_r, !collect_rel_union.
    
    cdes BSTEP_.
    repeat apply union_mori.
    { (* TODO: make a lemma *)
      arewrite (e2a S' □₁ ES.cont_sb_dom S k ⊆₁ e2a S □₁ ES.cont_sb_dom S k).
      { unfolder. ins. desf.
        eexists. splits; eauto.
        symmetry.
        eapply basic_step_e2a_eq_dom; eauto.
        eapply kE_inE; eauto. }
      rewrite rmw_cov_in_kE; eauto.
      assert (Srmw S ⊆ Srmw S') as AA.
      { rewrite RMW'. eauto with hahn. }
      rewrite <- AA.
      unfolder. ins. desf.
      do 2 eexists. splits; eauto.
      all: eapply basic_step_e2a_eq_dom; eauto.
      all: eapply kE_inE; eauto.
      match goal with
      | H : (Srmw S) _ _ |- _ => rename H into RMW
      end.
      match goal with
      | H : ES.cont_sb_dom S k _ |- _ => rename H into CY
      end.
      unfold ES.cont_sb_dom in *. desf.
      { exfalso.
        apply WFS.(ES.rmw_in_sb) in RMW.
        eapply WFS.(ES.sb_ninit).
        apply seq_eqv_r. eauto. }
      apply WFS.(ES.rmw_in_sb) in RMW.
      generalize WFS.(ES.sb_trans) RMW CY. basic_solver 10. }
    { unfolder. ins. desf.
      exfalso.
      match goal with
      | H : Grmw ?x _ |- _ => rename H into RMW
      end.
      erewrite basic_step_e2a_e in RMW; eauto.
      2: by apply SRCC.
      
      assert (exists xindex,
             << ILT : xindex < eindex st >> /\
             x = ThreadEvent (ES.cont_thread S k) xindex).
      { destruct x; simpls.
        { apply WF.(rmw_from_non_init) in RMW.
          destruct_seq_l RMW as AA. desf. }
        apply WF.(rmw_in_sb) in RMW.
        destruct_seq RMW as [AA BB].
        red in RMW. desf.
        eauto. }
      desf.

      assert (wf_thread_state (ES.cont_thread S k) st) as WTS.
      { eapply contwf; eauto. apply SRCC. }
      assert ((ProgToExecution.step (ES.cont_thread S k))＊ st st') as STEPS.
      { apply inclusion_t_rt. eapply ilbl_step_in_steps; eauto. }
      assert (wf_thread_state (ES.cont_thread S k) st') as WTS'.
      { eapply wf_thread_state_steps; eauto. }
      assert ((ProgToExecution.step (ES.cont_thread S k))＊ st' st'')
        as STEPS'.
      { apply lbl_steps_in_steps; eauto. }
      assert (wf_thread_state (ES.cont_thread S k) st'') as WTS''.
      { eapply wf_thread_state_steps; eauto. }

      eapply eindex_not_in_rmw with (thread:=ES.cont_thread S k)
                                    (st:=st) (st':=st'); eauto.
      exists (ThreadEvent (ES.cont_thread S k) xindex).
      eapply steps_dont_add_rmw; eauto.
      
      assert (eindex st < eindex st') as LTST.
      { eapply ilbl_step_eindex_lt; eauto. }
      assert (eindex st' <= eindex st'') as LTST'.
      { eapply eindex_steps_mon; eauto. }

      assert (acts_set (ProgToExecution.G st')
                       (ThreadEvent (ES.cont_thread S k) xindex))
        as XINDST'.
      { red. apply acts_clos; auto. omega. }
      apply seq_eqv_l. split; auto.

      eapply dcertRMW. 
      { apply SRCC. }
      apply seq_eqv_lr. splits; auto.
      all: apply acts_clos; auto.
      all: omega. }
    rewrite RMW'; unfold rmw_delta.
    rewrite seq_union_l, collect_rel_union.
    unionR right.
    unfold eq_opt. unfolder. ins. desf.
    do 2 eexists. splits; eauto.
    eapply wf_rmw_invf; eauto.
    eapply e2a_rmw with (S:=S'); eauto.
    { apply SRC'. }
    red.
    do 2 eexists.
    splits; eauto.
    apply RMW'. right. red. unfold eq_opt. basic_solver.
  Admitted.

End SimRelCertStepCoh.
