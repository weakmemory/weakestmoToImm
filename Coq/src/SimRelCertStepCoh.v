Require Import Omega.
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

  Lemma simrel_cert_step_fr_simpl_coh k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
    irreflexive (Sco S' ⨾ (Sjf S')^? ⨾ Shb S' ⨾ (Sjf S')⁻¹).
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

    assert (irreflexive (Sco S ⨾ (Sjf S)^? ⨾ Shb S ⨾ (Sjf S)⁻¹))
      as OLDCOH.
    { apply irreflexive_seqC. rewrite !seqA. 
      apply irreflexive_seqC. rewrite !seqA. 
      rewrite WF.(ES.jf_in_rf).
      arewrite ((Srf S)⁻¹ ⨾ Sco S ⊆ ES.fr S).
      arewrite (ES.fr S ⨾ (Srf S)^? ⊆ (Seco S)^?).
      2: by apply SRCC.
      rewrite fr_in_eco.
      arewrite (Srf S ⊆ Seco S).
      generalize (eco_trans S Weakestmo).
      basic_solver. }

    assert 
    (irreflexive (Sco S' ⨾ (Sjf S')^? ⨾ Shb S' ⨾ (Sjf S)⁻¹)) 
      as IrrH.
    { arewrite (Shb S' ⨾ (Sjf S)⁻¹ ≡ Shb S ⨾ (Sjf S)⁻¹).
      { rewrite ES.jfE; auto.
        rewrite !transp_seq, !transp_eqv_rel.
        rewrite <- seq_eqvK at 1. 
        rewrite !seqA, <- seqA.
        arewrite (Shb S' ⨾ ⦗SE S⦘ ≡ Shb S); auto.
        unfold_cert_step_ CertSTEP_.
        1,3: 
          eapply step_same_jf_hbE; eauto;
          rewrite RMW'; subst; 
            autounfold with ESStepDb;
            basic_solver.
        all: eapply add_jf_hbE; eauto. 
        1,3 : eapply weaken_sim_add_jf; eauto.
        { subst; autounfold with ESStepDb; basic_solver. }
        cdes ACO. type_solver. }
      arewrite ((Sjf S')^? ⨾ Shb S ≡ (Sjf S)^? ⨾ Shb S).
      { rewrite !crE. relsf.
        apply union_more; auto.
        rewrite hbE; auto.
        rewrite <- seq_eqvK at 1.
        rewrite !seqA. 
        arewrite (Sjf S' ⨾ ⦗SE S⦘ ≡ Sjf S); auto.
        unfold_cert_step_ CertSTEP_.
        1,3: rewrite JF', ES.jfE; basic_solver.
        all : 
          eapply add_jf_jfE; eauto;
          eapply weaken_sim_add_jf; eauto. }
      unfold_cert_step_ CertSTEP_.
      all: try cdes ACO; rewrite CO'.
      1,2: done.
      all: unfold co_delta.
      all: rewrite add_co_ws_complE; auto.
      all: rewrite sim_wsE.
      all: relsf.
      all: rewrite !irreflexive_union; splits. 
      2,3,5,6 : step_solver.
      all: done. }

    assert (e2a S' □ Ssb S' ⊆ Gsb) as SBN.
    { eapply e2a_sb; eauto; try apply SRCC.
      2: by eapply e2a_GE; eauto.
      apply stable_prog_to_prog_no_init; apply SRCC. }
    
    assert (e2a S' □ Shb S' ⊆ Ghb) as HBN.
    { eapply e2a_hb; eauto; try apply SRCC.
      all: apply SRE2A. }

    (* assert (e2a S' □ Sco S' ⨾ Sjf S' ⨾ Shb S' ⨾ ⦗eq e⦘ ⊆ *)
    (*             Gco ⨾ vf G sc TC' (ES.cont_thread S k)) as COVF_H. *)
    (* { admit. } *)
    (* { arewrite (Sjf S' ⨾ Shb S' ⨾ ⦗eq e⦘ ⊆ Sjf S ⨾ Shb S' ⨾ ⦗eq e⦘). *)
    (*   { admit. } *)
    (*   rewrite !collect_rel_seqi. *)
    (*   rewrite e2a_co; eauto. *)
    (*   rewrite HBN. *)
    (*   arewrite_id (e2a S' □ ⦗eq e⦘). *)
    (*   { basic_solver. } *)
    (*   rewrite seq_id_r. *)
    (*   hahn_frame. *)
    (*   arewrite (e2a S' □ Sjf S ⊆ e2a S □ Sjf S). *)
    (*   { (* TODO: generalize to a lemma *) *)
    (*     rewrite WF.(ES.jfE) at 1. *)
    (*     unfolder. ins. desf. do 2 eexists. *)
    (*     splits; eauto. *)
    (*     all: symmetry; eapply basic_step_e2a_eq_dom; eauto. } *)
    (*   arewrite (e2a S □ Sjf S ⊆ vf G sc TC' (ES.cont_thread S k)). *)
    (*   { (* TODO: It should follow from the simulation invariant. *) *)
    (*     admit. } *)
    (*   unfold vf at 1. rewrite !seqA. *)
    (*   arewrite (Ghb^? ⨾ ⦗GE⦘ ⨾ Ghb ⊆ Ghb^? ⨾ ⦗GE⦘). *)
    (*   2: done. *)
    (*   rewrite (dom_r WFG.(wf_hbE)) at 2. *)
    (*   generalize (@imm_s_hb.hb_trans G). *)
    (*   basic_solver 10. } *)

    (* assert  *)
    (*   (e2a S' □ Sco S' ⨾ (Sjf S')^? ⨾ Shb S' ⨾ ⦗ eq e ⦘ ⊆  *)
    (*        Gco ⨾ Gvf (ktid S k)) *)
    (*   as COVF. *)
    (* { rewrite crE. rewrite !seq_union_l, !seq_union_r, seq_id_l. *)
    (*   rewrite collect_rel_union. *)
    (*   unionL; auto. *)
    (*   rewrite !collect_rel_seqi. *)
    (*   rewrite e2a_co; eauto. *)
    (*   sin_rewrite HBN. *)
    (*   arewrite_id (e2a S' □ ⦗eq e⦘). *)
    (*   { basic_solver. } *)
    (*   rewrite seq_id_r. *)
    (*   rewrite (dom_r WFG.(wf_coD)) at 1. *)
    (*   rewrite (dom_r WFG.(wf_hbE)) at 1. *)
    (*   rewrite !seqA. *)
    (*   do 2 hahn_frame. *)
    (*   basic_solver 40. } *)

    (* TODO: introduce a lemma *)
    assert (Sjf S' ⨾ ⦗SE S⦘ ≡ Sjf S) as JFE.
    { red in WMO_STEP_. desf; cdes WMO_STEP_.
      1,3: rewrite JF', ES.jfE; auto; basic_solver.
      all: erewrite add_jf_jfE; eauto. }

    assert (irreflexive
              ((e2a S' □ Sco S' ⨾ (Sjf S')^? ⨾ Shb S' ⨾ ⦗eq e⦘)
                 ⨾ (cert_rf G sc TC' (ES.cont_thread S k))⁻¹)) as IRR.
    { arewrite (Shb S' ⊆ ⦗X ∩₁ e2a S ⋄₁ covered TC⦘ ⨾ Shb S' ∪ Ssb S').
      { erewrite <- basic_step_e2a_set_map_inter_old; eauto.
        2 : apply Execution.ex_inE; apply SRCC.
        eapply hb_in_ex_cov_hb_sb; eauto. }
      rewrite !seq_union_l, !seq_union_r, !seqA.
      arewrite ((Sjf S')^? ⨾ ⦗X ∩₁ e2a S ⋄₁ C⦘ ⊆
                        (Sjf S' ⨾ ⦗X ∩₁ e2a S ⋄₁ C⦘)^? ⨾ ⦗X ∩₁ e2a S ⋄₁ C⦘)
        by basic_solver 10.
      arewrite ((Sjf S')^? ⨾ Ssb S' ⨾ ⦗eq e⦘ ⊆ (Sjf S)^? ⨾ Ssb S' ⨾ ⦗eq e⦘).
      { rewrite !crE. relsf.
        apply union_mori; [done|].
        erewrite basic_step_sbe; eauto.
        erewrite dom_rel_helper 
          with (r := ES.cont_sb_dom S k × eq e) (d := SE S) at 1.
        { rewrite <- seqA. by rewrite JFE. }
        rewrite dom_cross.
        { eapply kE_inE; eauto. }
        intros [HA HB]. by eapply HA. }
      arewrite ((Sjf S)^? ⨾ Ssb S' ⨾ ⦗eq e⦘ ⊆
                       (Sjf S ⨾ ⦗kE S k⦘)^? ⨾ Ssb S' ⨾ ⦗eq e⦘).
      { erewrite basic_step_sbe; eauto. basic_solver 10. }

      rewrite !collect_rel_union.
      rewrite !collect_rel_seqi.
      rewrite !collect_rel_cr.
      arewrite (Sjf S' ⨾ ⦗X ∩₁ e2a S ⋄₁ C⦘ ⊆ 
                    Sjf S ⨾ ⦗X ∩₁ e2a S ⋄₁ C⦘).
      { rewrite <- seq_eqvK at 1.
        arewrite (X ∩₁ e2a S ⋄₁ C ⊆₁ SE S) at 1.
        { apply set_subset_inter_l. left.
          rewrite Execution.ex_inE; eauto.
          apply SRCC. }
          by rewrite <- seqA, JFE. }
      arewrite (e2a S' □ Sjf S ⨾ ⦗X ∩₁ e2a S ⋄₁ C⦘ ⊆
                    e2a S  □ Sjf S  ⨾ ⦗X ∩₁ e2a S ⋄₁ C⦘).
      { rewrite ES.jfE; auto.
        rewrite !seqA, seq_eqvC.
        arewrite (⦗SE S⦘ ⨾ Sjf S ⨾ ⦗X ∩₁ e2a S ⋄₁ C⦘ ⨾ ⦗SE S⦘ ≡ 
                         restr_rel (SE S) (Sjf S ⨾ ⦗X ∩₁ e2a S ⋄₁ C⦘)).
        { basic_solver. }
        apply collect_rel_restr_eq_dom.
        red. ins. symmetry. 
        eapply basic_step_e2a_eq_dom; eauto. }
      arewrite (e2a S □ Sjf S ⨾ ⦗X ∩₁ e2a S ⋄₁ C⦘ ⊆ Grf ⨾ ⦗C⦘).
      { rewrite <- seq_eqvK, <- seqA. rewrite collect_rel_seqi.
        arewrite (e2a S □ ⦗X ∩₁ e2a S ⋄₁ C⦘ ⊆ ⦗C⦘) by basic_solver. 
          by rewrite jf_cov_in_rf; [|apply SRCC]. }
      rewrite e2a_co; eauto.
      rewrite HBN, SBN.
      arewrite_id (e2a S' □ ⦗X ∩₁ e2a S ⋄₁ C⦘).
      { basic_solver. }
      rewrite seq_id_l.
      rewrite !seq_union_l.
      apply irreflexive_union; split.
      { arewrite_id (e2a S' □ ⦗eq e⦘).
        { basic_solver. }
        rewrite seq_id_l.
        rewrite (dom_r WFG.(wf_coD)), !seqA.
        unfold cert_rf.
        arewrite (⦗GW⦘ ⨾ (Grf ⨾ ⦗C⦘)^? ⨾ Ghb ⊆ vf G sc TC' (ES.cont_thread S k)).
        2: basic_solver 20.
        unfold vf.
        unionR left.
        arewrite (C ⊆₁ C').
        { eapply sim_trav_step_covered_le.
          eexists. apply SRCC. }
        rewrite wf_hbE at 1; auto.
        basic_solver 40. }
      arewrite (e2a S' □ Sjf S ⨾ ⦗ES.cont_sb_dom S k⦘ ⊆
                    e2a S  □ Sjf S ⨾ ⦗ES.cont_sb_dom S k⦘).
      { rewrite ES.jfE at 1; auto.
        unfolder. ins. desf. do 2 eexists. splits; eauto.
        all: symmetry; eapply basic_step_e2a_eq_dom; eauto. }
      rewrite jf_in_cert_rf; eauto.
      rewrite (dom_r WFG.(wf_coD)), !seqA.
      arewrite (⦗GW⦘ ⨾ (cert_rf G sc TC' (ES.cont_thread S k))^? ⨾ Gsb ⊆
                     vf G sc TC' (ES.cont_thread S k)).
      2: unfold cert_rf; basic_solver 10.
      rewrite cert_rf_in_vf.
      rewrite crE.
      rewrite !seq_union_l, !seq_union_r, seq_id_l.
      unionL.
      { unfold vf.
        unionR left.
        rewrite imm_s_hb.sb_in_hb.
        rewrite imm_s_hb.wf_hbE at 1; auto.
        basic_solver 20. }
      unfold vf at 1.
      rewrite !seq_union_l, !seq_union_r, !seqA.
      arewrite (Gsb^? ⨾ Gsb ⊆ Gsb^?).
      { generalize (@Execution.sb_trans G). basic_solver. }
      arewrite (Ghb^? ⨾ ⦗GE⦘ ⨾ Gsb ⊆ Ghb^? ⨾ ⦗GE⦘).
      { rewrite Execution.wf_sbE. rewrite imm_s_hb.sb_in_hb.
        generalize (@imm_s_hb.hb_trans G).
        basic_solver. }
      arewrite (⦗GW⦘ ⨾ Grf ⊆ Grf).
      arewrite (⦗GW⦘ ⨾ ⦗GW⦘ ⊆ ⦗GW⦘).
      done. }

    unfold_cert_step_ CertSTEP_.
    1,3: by rewrite JF' at 2. 
    all: cdes AJF; rewrite JF' at 2.
    all: rewrite transp_union; relsf.
    all: rewrite !irreflexive_union; splits. 
    1,3: done.

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
    
    (* The old proof which requires DR restrictions *)
    
    (* (* TODO: introduce a corresponding lemma. *) *)
    (* arewrite (Sjf S' ⊆ SimRelJF.sim_jf G sc TC' S' (certX S' k')). *)
    (* { (* eapply jf_in_sim_jf. *) *)
    (*   (* apply inclusion_minus_l. *) *)
    (*   (* unionR right. *) *)
    (*   (* Sew ⨾ sim_jf ⊆ sim_jf *) *)
    (*   admit. } *)

    (* arewrite (SimRelJF.sim_jf G sc TC' S' (certX S' k') ⊆ *)
    (*           SimRelJF.sim_vf G sc TC' S' (certX S' k')) at 1. *)
    (* arewrite (Sco S' ⨾ (SimRelJF.sim_vf G sc TC' S' (certX S' k'))^? ⨾ Shb S' ⊆ *)
    (*           Sco S' ⨾ SimRelJF.sim_vf G sc TC' S' (certX S' k')). *)
    (* 2: { unfold SimRelJF.sim_jf. basic_solver 10. } *)
    (* rewrite crE. rewrite !seq_union_l, !seq_union_r, seq_id_l. *)
    (* unionL. *)
    (* 2: { arewrite (SimRelJF.sim_vf G sc TC' S' (certX S' k') ⨾ Shb S' ⊆ *)
    (*                SimRelJF.sim_vf G sc TC' S' (certX S' k')). *)
    (*      2: done. *)
    (*      unfold SimRelJF.sim_vf. *)
    (*      rewrite !seqA. *)
    (*      arewrite ((Shb S')^? ⨾ Shb S' ⊆ (Shb S')^?). *)
    (*      2: done. *)
    (*      generalize (@hb_trans S'). basic_solver 20. } *)
    (* unfold SimRelJF.sim_vf. *)
    (* arewrite (Sco S' ⊆ Sco S' ⨾ Sew S'). *)
    (* 2: basic_solver 20. *)
    (* rewrite <- ES.ew_refl; auto. *)
    (* rewrite (dom_r WFS.(ES.coD)) at 1. *)
    (* rewrite (dom_r WFS.(ES.coE)) at 1. *)
    (* basic_solver. *)
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

    unfold ES.fr.
    rewrite <- !seqA. apply irreflexive_seqC.
    rewrite <- !seqA. apply irreflexive_seqC.
    
    arewrite (Srf S' ⊆ Sew S' ⨾ Sjf S').
    arewrite ((Sew S' ⨾ Sjf S')^? ⊆ (Sew S')^? ⨾ (Sjf S')^?)
      by basic_solver 10.
    rewrite transp_seq.
    arewrite (Sco S' ⨾ (Sew S')^? ⊆ Sco S').
    { generalize WFS.(ES.co_ew_in_co). basic_solver. }
    rewrite <- !seqA.
    rewrite irreflexive_seqC.
    rewrite !seqA.
    arewrite ((Sew S')⁻¹ ⊆ Sew S').
    { rewrite transp_sym_equiv; [done|]. apply WFS. }
    sin_rewrite WFS.(ES.ew_co_in_co).
    eapply simrel_cert_step_fr_simpl_coh; eauto.
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
    rewrite !irreflexive_union. splits.
    { apply hb_irr; eauto. }
    { admit. }
    (* { erewrite e2a_rf, e2a_jf; eauto. *)
    (*   intros x [y [HB VF]]. *)
    (*   unfold furr in VF. desc.   *)
    (*   eapply urr_hb_irr; try apply SRCC. *)
    (*   basic_solver. } *)
    { arewrite (Gco ⊆ Geco^?).
      2: by apply GCOH.
      rewrite Execution_eco.co_in_eco. basic_solver. }
    erewrite e2a_rf, e2a_jf; eauto.
    intros x [y [HB [z [CO VF]]]].
    unfold furr in VF. desc.  
    eapply eco_urr_irr; try apply SRCC.
    eexists. splits.
    { unfold Execution_eco.eco. basic_solver 10. }
    eapply urr_hb. basic_solver.
  Admitted.

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
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (step_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    exists k', S'. splits.
    { eapply basic_step_cont_thread_k; eauto. }
    { apply r_step. red.
      do 2 eexists; splits; eauto.
      eapply simrel_cert_step_consistent; eauto. }
    constructor.
    { red. splits.
      { eapply simrel_cert_step_simrel_; eauto. }
      eapply simrel_cert_step_consistent; eauto. }
    (* tr_step : isim_trav_step G sc (ktid S k') TC TC' *)
    { erewrite basic_step_cont_thread_k; eauto. apply SRCC. }
    (* cert : cert_graph G sc TC TC' (ktid S k') state'' *)
    { erewrite basic_step_cont_thread_k; eauto. apply SRCC. }
    (* cstate : simrel_cstate *)
    { eapply simrel_cert_basic_step_cstate; eauto. } 
    all : admit.
  Admitted.

End SimRelCertStepCoh.