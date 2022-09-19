Require Import Program.Basics Lia.
From PromisingLib Require Import Language.
From hahn Require Import Hahn.
From imm Require Import
     AuxDef
     Events Execution
     Traversal TraversalConfig SimTraversal SimTraversalProperties
     Prog ProgToExecution ProgToExecutionProperties Receptiveness
     imm_common imm_s imm_s_hb
     CertExecution2
     SubExecution CombRelations SimState.
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
Require Import SimRelCertForwarding.
Require Import SimRelCertStepCoh.
Require Import ProgES.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelCertStepLemma.

  Variable prog : stable_prog_type.
  Variable G : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable TC' : trav_config.
  Variable X : eventid -> Prop.
  Variable T : thread_id -> Prop.

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
  Notation "'Sicf' S" := S.(ES.icf) (at level 10).

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
  Notation "'klast' S" := (fun k => ES.cont_last S k) (at level 1, only parsing).

  Notation "'certX' S" := (fun k => (X ∩₁ SNTid_ S (ktid S k)) ∪₁ (kE S k)) (at level 1, only parsing).

  Lemma simrel_cert_step_ex_ktid_cov k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    X ∩₁ Stid_ S' (ktid S' k') ∩₁ e2a S' ⋄₁ C ⊆₁ kE S' k'.
  Proof.
    cdes CertSTEP.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    erewrite basic_step_cont_sb_dom'; eauto.
    unionR left -> left.
    erewrite basic_step_cont_thread'; eauto.
    erewrite simrel_cert_basic_step_ex_tid; eauto.
    erewrite basic_step_e2a_set_map_inter_old
      with (S := S); eauto.
    { apply SRCC. }
    erewrite Execution.ex_inE
      with (X := X); eauto.
    basic_solver.
  Qed.

  Lemma simrel_cert_step_cov_in_ex k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    e2a S' ⋄₁ C ∩₁ kE S' k' ⊆₁ X.
  Proof.
    cdes CertSTEP.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S) as SRCONT.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    erewrite basic_step_cont_sb_dom'; eauto.
    rewrite set_unionA.
    rewrite set_inter_union_r.
    unionL.
    { rewrite set_interC.
      erewrite basic_step_e2a_set_map_inter_old
        with (S := S); eauto.
      { rewrite set_interC. apply SRCC. }
      eapply kE_inE; eauto. }
    rewrite set_inter_union_r.
    unfolder. unionL.
    { intros x [Cx EQx]. subst x. exfalso.
      erewrite basic_step_e2a_e in Cx; eauto.
      eapply thread_event_ge_ncov; eauto. }
    intros x [Cx EQx].
    destruct e' as [e'|]; [|done].
    subst x. exfalso.
    erewrite basic_step_e2a_e' in Cx; eauto.
    eapply thread_event_ge_ncov.
    1,3: eauto.
    lia.
  Qed.

  Lemma simrel_cert_step_klast_sb_max k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    klast S' k' ⊆₁ max_elt (Ssb S').
  Proof.
    cdes CertSTEP. cdes BSTEP_.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S) as SRCONT.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    unfold ES.cont_last. subst k'.
    rewrite SB'.
    unfold sb_delta.
    rewrite <- cross_union_l.
    unfold opt_ext, eq_opt.
    destruct e' as [e'|].
    { intros x EQx. subst x.
      red. ins.
      destruct REL as [SB | [SB | SB]].
      { eapply basic_step_acts_set_ne'; eauto.
        apply ES.sbE in SB; auto.
        generalize SB. basic_solver. }
      { eapply basic_step_acts_set_ne'; eauto.
        eapply ES.cont_sb_domE; eauto.
        generalize SB. basic_solver. }
      destruct SB as [EQe _]. lia. }
    relsf.
    intros x EQx. subst x.
    red. ins.
    eapply basic_step_acts_set_ne; eauto.
    destruct REL as [SB | SB].
    { apply ES.sbE in SB; auto.
      generalize SB. basic_solver. }
    eapply ES.cont_sb_domE; eauto.
    generalize SB. basic_solver.
  Qed.

  Lemma simrel_cert_step_kE_sb_cov_iss k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    e2a S' □₁ codom_rel (⦗kE S' k'⦘ ⨾ Ssb S' ⨾ ⦗Stid_ S' (ktid S' k')⦘) ⊆₁ CsbI G TC'.
  Proof.
    cdes CertSTEP. cdes BSTEP_.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S) as SRCONT.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    rewrite SB'.
    erewrite basic_step_cont_sb_dom'; eauto.
    rewrite !id_union.
    rewrite !seq_union_l, !seq_union_r.
    rewrite !codom_union.
    arewrite
      (sb_delta S k e e' ⨾ ⦗Stid_ S' (ktid S' k')⦘ ⊆ sb_delta S k e e').
    rewrite !codom_seq
      with (r' := sb_delta S k e e').
    rewrite basic_step_sb_delta_codom; eauto.
    rewrite !set_collect_union.
    arewrite (e2a S' □₁ eq e ⊆₁ CsbI G TC').
    { rewrite set_collect_eq.
      intros x EQx. subst x.
      eapply basic_step_e2a_E0_e; eauto.
      apply SRCC. }
    arewrite (e2a S' □₁ eq_opt e' ⊆₁ CsbI G TC').
    { rewrite set_collect_eq_opt.
      unfold eq_opt, option_map.
      destruct e' as [e'|]; [|basic_solver].
      intros x EQx. subst x.
      eapply basic_step_e2a_E0_e'; eauto.
      apply SRCC. }
    relsf; splits; auto.
    2-3: step_solver.
    erewrite basic_step_e2a_set_collect_eq_dom;
      eauto.
    { assert
        (Ssb S ⨾ ⦗Stid_ S' (ktid S' k')⦘ ⊆ Ssb S ⨾ ⦗Stid_ S (ktid S k)⦘)
        as HH.
      { rewrite !seq_eqv_r.
        erewrite basic_step_cont_thread'; eauto.
        unfolder; ins; desf; splits; auto.
        erewrite <- basic_step_tid_eq_dom; eauto.
        apply ES.sbE in H; auto.
        generalize H. basic_solver. }
      rewrite HH.
      edestruct kcond; eauto; desc; auto.
      erewrite <- sim_trav_step_CsbI_mon;
        eauto; [|eexists]; apply SRCC. }
    rewrite ES.sbE; auto.
    basic_solver.
  Qed.

  Lemma simrel_cert_step_kE_lab k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    eq_dom (kE S' k' \₁ SEinit S') (Slab S') (Execution.lab (ProgToExecution.G st'') ∘ e2a S').
  Proof.
    cdes CertSTEP.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S) as SRCONT.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    erewrite basic_step_cont_sb_dom'; eauto.
    erewrite basic_step_acts_init_set; eauto.
    rewrite set_unionA.
    rewrite set_minus_union_l.
    eapply eq_dom_union. split.
    { unfolder. ins. desf. unfold Basics.compose.
      assert (SE S x) as EX.
      { eapply kE_inE; eauto. }
      erewrite basic_step_lab_eq_dom; eauto.
      erewrite basic_step_e2a_eq_dom with (S:=S); eauto.
      eapply kE_lab; eauto. by split. }
    unfolder. ins. desf.
    { eapply basic_step_e2a_lab_e with (S:=S); eauto; apply SRCC. }
    eapply basic_step_e2a_lab_e' with (S:=S); eauto; apply SRCC.
  Qed.

  Lemma simrel_cert_step_jf_in_cert_rf k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    e2a S' □ (Sjf S' ⨾ ⦗kE S' k'⦘) ⊆ cert_rf G sc TC'.
  Proof.
    cdes CertSTEP.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S) as SRCONT.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    erewrite basic_step_cont_sb_dom'; eauto.
    rewrite !id_union. rewrite !seq_union_r, !collect_rel_union.
    unionL.
    { erewrite <- jf_kE_in_cert_rf; eauto.
      arewrite (⦗kE S k⦘ ⊆ ⦗SE S⦘ ⨾ ⦗kE S k⦘).
      { rewrite <- seq_eqvK at 1. by erewrite kE_inE at 1; eauto. }
      arewrite (Sjf S' ⨾ ⦗SE S⦘ ⊆ Sjf S).
      { eapply simrel_cert_step_jf_E; eauto. }
      eapply basic_step_e2a_collect_rel_eq_dom with (S' := S'); eauto.
      rewrite ES.jfE at 1; try apply SRCC. basic_solver. }
    { assert (Sjf S ⨾ ⦗eq e⦘ ⊆ ∅₂) as AA.
      { rewrite ES.jfE; try apply SRCC. unfold ES.acts_set.
        cdes BSTEP_. desf. unfolder. ins. lia. }
      red in CertSTEP_. desf; cdes CertSTEP_.
      1,3: rewrite JF'; rewrite AA; basic_solver.
      all: cdes AJF; rewrite JF';
        rewrite seq_union_l, collect_rel_union; unionL.
      1,3: rewrite AA; basic_solver.
      all: unfold jf_delta; unfolder; ins; desf. }
    arewrite (Sjf S' ⨾ ⦗eq_opt e'⦘ ⊆ ∅₂).
    2: basic_solver.
    assert (Sjf S ⨾ ⦗eq_opt e'⦘ ⊆ ∅₂) as AA.
    { cdes BSTEP_. step_solver. }
    cdes BSTEP_. desf.
    red in CertSTEP_. desf; cdes CertSTEP_.
    1,3: by rewrite JF'.
    all: cdes AJF; rewrite JF'; rewrite seq_union_l; unionL; auto.
    all: unfold jf_delta.
    { basic_solver. }
    desf. simpls. desf. unfolder. ins. desf. lia.
  Qed.

  Lemma simrel_cert_step_icf_ex_ktid_in_co k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    e2a S' □ (Sjf S' ⨾ ⦗set_compl (kE S' k')⦘ ⨾ Sicf S' ⨾ ⦗X ∩₁ Stid_ S' (ktid S' k')⦘ ⨾ (Sjf S')⁻¹) ⊆ Gco.
  Proof.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S) as SRCONT.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { cdes CertSTEP. econstructor; eauto. }
    arewrite (Sjf S' ⨾ ⦗set_compl (ES.cont_sb_dom S' k')⦘ ⊆
              Sjf S  ⨾ ⦗set_compl (ES.cont_sb_dom S  k )⦘).
    { unfold_cert_step CertSTEP.
      1,3: arewrite (kE S k ⊆₁ kE S' k') at 1.
      1,3: erewrite basic_step_cont_sb_dom'
             with (S' := S'); eauto; basic_solver.
      1,2: rewrite JF'; basic_solver.
      all: cdes AJF; rewrite JF'.
      all: rewrite seq_union_l; unionL.
      1,3: arewrite (kE S k ⊆₁ kE S' k') at 1.
      1,3: erewrite basic_step_cont_sb_dom'
             with (S' := S'); eauto; basic_solver.
      1,2: done.
      all: erewrite basic_step_cont_sb_dom'; eauto.
      all: rewrite !set_compl_union.
      all: unfold jf_delta; basic_solver. }
    cdes CertSTEP. cdes BSTEP_.
    erewrite simrel_cert_basic_step_ex_tid; eauto.
    erewrite basic_step_cont_thread'; eauto.
    arewrite (Sjf S ⨾ ⦗set_compl (ES.cont_sb_dom S  k )⦘ ⨾ Sicf S' ⨾ ⦗X ∩₁ Stid_ S (ktid S k)⦘ ⊆
              Sjf S ⨾ ⦗set_compl (ES.cont_sb_dom S  k )⦘ ⨾ Sicf S  ⨾ ⦗X ∩₁ Stid_ S (ktid S k)⦘).
    { rewrite !seq_eqv_r, !seq_eqv_l.
      intros x y [z [JF [nkSBx [ICF [Xy TIDy]]]]].
      unfolder; eexists; splits; eauto.
      eapply basic_step_icf_restr
        with (S' := S'); eauto.
      red; splits; auto.
      { apply ES.jfE in JF; auto.
        generalize JF. basic_solver. }
      eapply Execution.ex_inE; eauto. }
    arewrite (⦗X ∩₁ Stid_ S (ktid S k)⦘ ⨾ (Sjf S')⁻¹ ⊆
              ⦗X ∩₁ Stid_ S (ktid S k)⦘ ⨾ (Sjf S )⁻¹).
    { rewrite !seq_eqv_l.
      intros x y [[Xx TIDx] JF]. red in JF.
      unfolder; splits; auto.
      eapply step_jfE; eauto.
      { eapply simrel_cert_step_step_; eauto. }
      apply seq_eqv_r; splits; auto.
      eapply Execution.ex_inE; eauto. }
    erewrite basic_step_e2a_collect_rel_eq_dom;
      eauto; [apply SRCC|].
    rewrite ES.jfE; auto.
    basic_solver 20.
  Qed.

  Lemma simrel_cert_step_ex_cont_iss k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    X ∩₁ e2a S' ⋄₁ (acts_set st'.(ProgToExecution.G) ∩₁ I) ⊆₁ dom_rel (Sew S' ⨾ ⦗ kE S' k' ⦘).
  Proof.
    cdes CertSTEP. cdes BSTEP_.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (tc_coherent G sc TC ) as TCCOH.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S) as SRCONT.
    { apply SRCC. }
    assert (cert_graph G sc TC' (ktid S k) st'').
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }

    edestruct ilbl_step_acts_set as [a [a' HH]].
    { eapply wf_cont_state; eauto. }
    { apply STEP. }
    destruct HH as [EQa [EQa' ACTS]].
    red in EQa, EQa', ACTS.

    erewrite basic_step_e2a_set_map_inter_old; eauto.
    2 : apply EXEC.
    rewrite ACTS.
    rewrite basic_step_cont_sb_dom'; eauto.
    rewrite !set_inter_union_l, !set_map_union, !set_inter_union_r.
    rewrite !id_union, !seq_union_r, !dom_union.
    repeat apply set_union_Proper.

    { rewrite ex_cont_iss; eauto.
      rewrite step_ew_mon; eauto.
      eapply simrel_cert_step_step_; eauto. }

    { intros x [Xx [EQx Ix]].
      assert (SW S' e) as Wx.
      { unfold is_w.
        erewrite basic_step_e2a_certlab_e; eauto.
        erewrite basic_step_e2a_e; eauto.
        rewrite <- EQa, EQx.
        erewrite cslab; eauto.
        { eapply issuedW; eauto. }
        red. do 3 left. right.
        eapply sim_trav_step_issued_le; eauto.
        eexists; apply SRCC. }
      unfold_cert_step_ CertSTEP_;
        try by (try cdes AJF; type_solver).
      eapply sim_add_ew_ex_issw; eauto.
      { basic_solver. }
      unfolder.
      arewrite (e2a S' x = e2a S x).
      { eapply basic_step_e2a_eq_dom; eauto.
        eapply Execution.ex_inE; eauto. }
      splits; auto.
      exists e; splits; eauto.
      erewrite basic_step_e2a_e; eauto.
      congruence. }

    intros x [Xx [EQx Ix]].
    unfold eq_opt in EQx.
    destruct a' as [a'|]; [|intuition].
    destruct lbl'; [|exfalso; congruence].
    destruct e' as [e'|].
    2 : by unfold opt_same_ctor in *.
    inversion EQa' as [EQa''].
    assert (SW S' e') as Wx.
    { unfold is_w.
      erewrite basic_step_e2a_certlab_e'; eauto.
      erewrite basic_step_e2a_e'; eauto.
      rewrite Nat.add_1_l.
      rewrite <- EQa'', EQx.
      erewrite cslab; eauto.
      { eapply issuedW; eauto. }
      red. do 3 left. right.
      eapply sim_trav_step_issued_le; eauto.
      eexists; apply SRCC. }
    unfold_cert_step_ CertSTEP_;
      try by (try cdes AJF; type_solver).
    eapply sim_add_ew_ex_issw; eauto.
    { basic_solver. }
    { basic_solver. }
    unfolder.
    arewrite (e2a S' x = e2a S x).
    { eapply basic_step_e2a_eq_dom; eauto.
      eapply Execution.ex_inE; eauto. }
    splits; auto.
    exists e'; splits; eauto.
    erewrite basic_step_e2a_e'; eauto.
    congruence.
  Qed.

  Lemma simrel_cert_step_kE_iss k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    kE S' k' ∩₁ e2a S' ⋄₁ I ⊆₁ dom_rel (Sew S' ⨾ ⦗ X ⦘).
  Proof.
    cdes CertSTEP. cdes BSTEP_.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (tc_coherent G sc TC ) as TCCOH.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S) as SRCONT.
    { apply SRCC. }
    assert (cert_graph G sc TC' (ktid S k) st'').
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }

    erewrite basic_step_cont_sb_dom'; eauto.
    rewrite !set_inter_union_l.
    unionL.
    { erewrite basic_step_e2a_set_map_inter_old; eauto.
      2 : eapply ES.cont_sb_domE; eauto.
      rewrite kE_iss; eauto.
      rewrite step_ew_mon; eauto.
      eapply simrel_cert_step_step_; eauto. }
    { intros x [EQx Ix]. subst x.
      assert (SW S' e) as Wx.
      { unfold is_w.
        erewrite basic_step_e2a_certlab_e; eauto.
        erewrite cslab; eauto.
        { eapply issuedW; eauto. }
        red. do 3 left. right.
        eapply sim_trav_step_issued_le; eauto.
        eexists; apply SRCC. }
      unfold_cert_step_ CertSTEP_;
        try by (try cdes AJF; type_solver).
      eapply sim_add_ew_issw_ew_ex; eauto.
      all: basic_solver. }
    intros x [EQx Ix].
    unfold eq_opt in EQx.
    destruct e' as [e'|]; [|intuition].
    subst x.
    assert (SW S' e') as Wx.
    { unfold is_w.
      erewrite basic_step_e2a_certlab_e'; eauto.
      erewrite cslab; eauto.
      { eapply issuedW; eauto. }
      red. do 3 left. right.
      eapply sim_trav_step_issued_le; eauto.
      eexists; apply SRCC. }
    unfold_cert_step_ CertSTEP_;
      try by (try cdes AJF; type_solver).
    eapply sim_add_ew_issw_ew_ex; eauto.
    all: basic_solver.
  Qed.

  Lemma simrel_cert_step_e2a_co_kE k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    e2a S' □ (Sco S' ⨾ ⦗kE S' k'⦘) ⊆ Gco.
  Proof.
    cdes CertSTEP. cdes BSTEP_.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (tc_coherent G sc TC ) as TCCOH.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S) as SRCONT.
    { apply SRCC. }
    assert (cert_graph G sc TC' (ktid S k) st'') as CERTG.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }

    erewrite basic_step_cont_sb_dom'; eauto.
    rewrite !id_union, !seq_union_r, !collect_rel_union.
    unionL.
    { unfold_cert_step_ CertSTEP_.
      3,4: eapply sim_add_co_e2a_co_kE; eauto.
      3,4: basic_solver.
      all: rewrite CO'.
      all: rewrite basic_step_e2a_collect_rel_eq_dom; eauto.
      1,3: eapply SRCC.
      all: rewrite ES.coE; auto.
      all: basic_solver. }
    { assert (ES.Wf S') as WFS'.
      { eapply simrel_cert_step_wf; eauto. }
      unfold_cert_step_ CertSTEP_.
      3 : eapply sim_add_co_e2a_co_w; eauto; basic_solver.
      1: arewrite (eq e ⊆₁ SF S') by basic_solver.
      2,3: arewrite (eq e ⊆₁ SR S') by (cdes AJF; basic_solver).
      all: rewrite ES.coD; auto; type_solver. }
    assert (ES.Wf S') as WFS'.
    { eapply simrel_cert_step_wf; eauto. }
    unfold_cert_step_ CertSTEP_.
    1-3: basic_solver.
    destruct e' as [e'|]; [|done].
    unfold eq_opt.
    eapply sim_add_co_e2a_co_w; eauto; basic_solver.
  Qed.

  Lemma simrel_cert_step_e2a_co_ex_ktid k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    e2a S' □ (Sco S' ⨾ ⦗X ∩₁ Stid_ S' (ktid S' k') \₁ e2a S' ⋄₁ (acts_set (ProgToExecution.G st'))⦘) ⊆ Gco.
  Proof.
    cdes CertSTEP. cdes BSTEP_.
    assert (Wf G) as WFG by apply SRCC.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S) as SRCONT.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }

    arewrite
      (X ∩₁ Stid_ S' (ktid S' k') \₁ e2a S' ⋄₁ acts_set (ProgToExecution.G st') ⊆₁
       X ∩₁ Stid_ S (ktid S k) \₁ e2a S ⋄₁ acts_set (ProgToExecution.G st')).
    { erewrite basic_step_cont_thread'; eauto.
      erewrite simrel_cert_basic_step_ex_tid; eauto.
      unfolder.
      intros x [[Xx TIDx] nACTSx].
      splits; auto.
      intros ACTSx. apply nACTSx.
      erewrite basic_step_e2a_eq_dom; eauto.
      eapply Execution.ex_inE; eauto. }

    rename BSTEP_ into BSTEP_'.
    unfold_cert_step CertSTEP.
    3,4: eapply sim_add_co_e2a_co_ex_ktid;
           eauto; basic_solver.
    all: rewrite CO'.
    all: erewrite <- ilbl_step_acts_set_mon;
           eauto; try apply STEP.
    2,4: eapply wf_cont_state; eauto.
    all: erewrite basic_step_e2a_collect_rel_eq_dom; eauto.
    1,3: apply SRCC.
    all: rewrite ES.coE; auto; basic_solver 10.
  Qed.

  Lemma simrel_cert_step_rmw_cov_in_kE k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    Grmw ⨾ ⦗C' ∩₁ e2a S' □₁ kE S' k'⦘ ⊆ e2a S' □ Srmw S' ⨾ ⦗ kE S' k' ⦘.
  Proof.
    cdes CertSTEP. cdes BSTEP_.
    assert (Wf G) as WFG by apply SRCC.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S) as SRCONT.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (simrel_e2a S' G sc) as SRE2A.
    { eapply simrel_cert_step_e2a; eauto. }

    erewrite basic_step_cont_sb_dom'; eauto.
    rewrite !set_collect_union.
    rewrite !set_inter_union_r.
    rewrite !id_union.
    rewrite !seq_union_r, !collect_rel_union.

    repeat apply union_mori.
    { erewrite basic_step_e2a_set_collect_eq_dom; eauto.
      2 : eapply kE_inE; eauto.
      assert (Srmw S ⊆ Srmw S') as AA.
      { rewrite RMW'. eauto with hahn. }
      rewrite <- AA.
      rewrite rmw_cov_in_kE; eauto.
      eapply basic_step_e2a_collect_rel_eq_dom with (S' := S'); eauto.
      rewrite WFS.(ES.rmwE) at 1. basic_solver. }

    { unfolder.
      intros x y [RMW [Cy [y' [EQy' EQy]]]].
      subst y y'. exfalso.
      erewrite basic_step_e2a_e with (S := S) in RMW; eauto.
      eapply simrel_cert_lbl_step_nrwm_eindex; eauto.
      { eexists. apply STEP. }
      basic_solver. }

    rewrite RMW'; unfold rmw_delta.
    rewrite seq_union_l, collect_rel_union.
    unionR right.
    unfold eq_opt. unfolder. ins. desf.
    do 2 eexists. splits; eauto.
    eapply wf_rmw_invf; eauto.
    eapply e2a_rmw with (S := S'); eauto.
    red. do 2 eexists.
    splits; eauto.
    apply RMW'. right. red.
    unfold eq_opt. basic_solver.
  Qed.

  Lemma simrel_cert_step_contsimstate_kE_covered k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'')
        (kE_COV : e2a S' ⋄₁ C' ∩₁ kE S' k' ⊆₁ e2a S ⋄₁ C' ∩₁ kE S k) :
    exists kC (state : thread_st (ES.cont_thread S' kC)),
            ⟪ THK   : ES.cont_thread S' kC = ktid S' k' ⟫ /\
            ⟪ INK   : K S' (kC, thread_cont_st (ES.cont_thread S' kC) state) ⟫ /\
            ⟪ INX   : ES.cont_sb_dom S' kC ≡₁ e2a S' ⋄₁ C' ∩₁ kE S' k' ⟫ /\
            ⟪ KINEQ : kE S' k' ⊆₁ e2a S' ⋄₁ C' -> kC = k' ⟫ /\
            ⟪ SIMST : @sim_state G sim_normal (C' ∩₁ e2a S' □₁ kE S' k') (ES.cont_thread S' kC) state ⟫.
  Proof.
    cdes CertSTEP.
    assert (Wf G) as WF by apply SRCC.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S)
      as SRCONT.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }

    assert (e2a S' ⋄₁ C' ∩₁ ES.cont_sb_dom S' k' ≡₁
            e2a S  ⋄₁ C' ∩₁ ES.cont_sb_dom S  k )
      as CEQE.
    { split; auto.
      erewrite basic_step_cont_sb_dom'
        with (S' := S'); eauto.
      rewrite set_interC.
      erewrite <- basic_step_e2a_set_map_inter_old; eauto.
      { basic_solver. }
      cdes BSTEP_. eapply ES.cont_sb_domE; eauto. }

    assert (C' ∩₁ e2a S' □₁ ES.cont_sb_dom S' k' ≡₁
            C' ∩₁ e2a S  □₁ ES.cont_sb_dom S  k )
      as CEQA.
    { symmetry.
      erewrite <- basic_step_e2a_set_collect_eq_dom; eauto.
      2 : { cdes BSTEP_. eapply ES.cont_sb_domE; eauto. }
      erewrite basic_step_cont_sb_dom'
        with (S' := S'); eauto.
      split; [basic_solver 10|].
      rewrite set_unionA, set_collect_union.
      rewrite set_inter_union_r.
      unionL; [basic_solver|].
      intros x [Cx E2Ax].
      split; auto.
      destruct E2Ax as [y [HH EQy]].
      exists y; split; auto.
      apply CEQE.
      split; [red; congruence|].
      eapply basic_step_cont_sb_dom'
        with (S' := S'); eauto.
      generalize HH. basic_solver. }

    edestruct contsimstate_kE as [kC]; try apply SRCC. desc.
    exists kC, state.
    erewrite basic_step_cont_thread; eauto.
    arewrite
      (ES.cont_thread S' k' = ES.cont_thread S k).
    { eapply basic_step_cont_thread'; eauto. }

    splits; auto.
    { eapply basic_step_cont_set; eauto. by left. }
    { rewrite CEQE. rewrite basic_step_cont_sb_dom_eq; eauto. }
    { intros AA. exfalso.
      eapply basic_step_acts_set_ne; eauto.
      eapply kE_inE; eauto.
      assert (ES.cont_sb_dom S' k' e) as BB.
      { eapply basic_step_cont_sb_dom'; eauto. basic_solver. }
      apply CEQE. split; auto. }

    red. splits; [|apply SIMST].
    intros idx. split; auto.
    { intros HH. eapply SIMST.
      apply CEQA. apply HH. }
    intros HH. apply CEQA.
    by apply SIMST.
  Qed.

  Lemma simrel_cert_step_contsimstate_kE_covering k k' e e' S S'
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'')
        (kE_nCOV : ~ (e2a S' ⋄₁ C' ∩₁ kE S' k' ⊆₁ e2a S ⋄₁ C' ∩₁ kE S k)) :
    exists kC (state : thread_st (ES.cont_thread S' kC)),
      ⟪ THK   : ES.cont_thread S' kC = ktid S' k' ⟫ /\
      ⟪ INK   : K S' (kC, thread_cont_st (ES.cont_thread S' kC) state) ⟫ /\
      ⟪ INX   : ES.cont_sb_dom S' kC ≡₁ e2a S' ⋄₁ C' ∩₁ kE S' k' ⟫ /\
      ⟪ KINEQ : kE S' k' ⊆₁ e2a S' ⋄₁ C' -> kC = k' ⟫ /\
      ⟪ SIMST : @sim_state G sim_normal (C' ∩₁ e2a S' □₁ kE S' k') (ES.cont_thread S' kC) state ⟫.
  Proof.
    cdes CertSTEP. cdes BSTEP_.
    assert (Wf G) as WF by apply SRCC.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S)
      as SRCONT.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (wf_thread_state (ktid S k) st) as WFT.
    { eapply wf_cont_state; eauto. }

    assert (C' (e2a S' e)) as Ce.
    { destruct (classic (C' (e2a S' e)))
        as [EE|NEE]; auto.
      exfalso. apply kE_nCOV.
      rewrite basic_step_cont_sb_dom'; eauto.
      rewrite set_unionA.
      rewrite set_inter_union_r.
      rewrite set_interC.
      erewrite basic_step_e2a_set_map_inter_old; eauto.
      2 : { eapply ES.cont_sb_domE; eauto. }
      unionL; [basic_solver|].
      intros x [Cx EQx].
      exfalso. apply NEE.
      destruct EQx as [HA|HB].
      { subst; done. }
      eapply sim_trav_step_rmw_covered
        with (r := e2a S' e); eauto.
      { eexists. apply SRCC. }
      { apply SRCC. }
      eapply e2a_rmw; eauto.
      { eapply simrel_cert_step_e2a; eauto. }
      do 2 eexists. splits; eauto.
      apply RMW'. unfold rmw_delta, eq_opt.
      basic_solver. }

    assert
      (eq_opt e' ⊆₁ e2a S' ⋄₁ C')
      as Ce'.
    { unfold eq_opt.
      intros x EQx.
      destruct e' as [e'|];
        try done; subst x.
      eapply sim_trav_step_rmw_covered
        with (r := e2a S' e); eauto.
      { eexists. apply SRCC. }
      { apply SRCC. }
      eapply e2a_rmw; eauto.
      { eapply simrel_cert_step_e2a; eauto. }
      do 2 eexists. splits; eauto.
      apply RMW'. unfold rmw_delta, eq_opt.
      basic_solver. }

    assert (kE S k ⊆₁ e2a S ⋄₁ C') as kE_COV.
    { intros x kSBx.
      eapply dom_sb_covered; eauto.
      { eapply sim_trav_step_coherence;
          [eexists|]; apply SRCC. }
      erewrite <- basic_step_e2a_eq_dom; eauto.
      2 : { cdes BSTEP_. eapply ES.cont_sb_domE; eauto. }
      exists (e2a S' e).
      apply seq_eqv_r.
      split; auto.
      eapply e2a_sb.
      { eapply simrel_cert_step_wf; eauto. }
      { eapply basic_step_e2a_GE; eauto;
          try apply SRCC.
        eapply sim_trav_step_coherence;
          [eexists|]; apply SRCC. }
      generalize SB'.
      unfold sb_delta.
      basic_solver 20. }

    exists k', st'.
    splits; auto.

    { cdes BSTEP_.
      eapply basic_step_cont_set; eauto.
      erewrite <- basic_step_cont_thread'; eauto.
      basic_solver. }

    { erewrite basic_step_cont_sb_dom'; eauto.
      split; [|basic_solver]. unionL.
      { intros x kSBx.
        split; [red|basic_solver].
        erewrite basic_step_e2a_eq_dom; eauto.
        { by apply kE_COV. }
        eapply ES.cont_sb_domE; eauto. }
      all: generalize kE_COV Ce Ce'.
      all: basic_solver 20. }

    edestruct contsimstate_kE as [kC];
      try apply SRCC. desc.
    assert (kC = k); [|subst kC].
    { by apply KINEQ. }
    assert (state = st); [|subst state].
    { cdes BSTEP_.
      pose proof (ES.unique_K WFS _ _ CONT INK eq_refl) as HH.
      simpls. inv HH. }
    cdes SIMST.
    red; splits.
    all: erewrite basic_step_cont_thread'; eauto.

    { assert (wf_thread_state (ktid S k) st') as WFT'.
      { eapply wf_thread_state_lbl_step; eauto.
        eexists; apply STEP. }

      assert (ES.Wf S') as WF'.
      { eapply simrel_cert_step_wf; eauto. }
      assert (simrel_cont (stable_prog_to_prog prog) S')
        as SRK.
      { eapply basic_step_simrel_cont
          with (S := S); eauto. }
      assert
        ((K S') (k', existT (Language.state (E:=list label))
                            (thread_lts (ES.cont_thread S' k')) st'))
        as Kk'.
      { eapply basic_step_cont_set; eauto.
        erewrite <- basic_step_cont_thread'; eauto.
        subst k'. basic_solver. }

      ins. split.
      { intros [Cx kSBx].
        eapply e2a_kE_eindex
          with (S := S') (k := k'); eauto.
        destruct kSBx as [x [kSBx E2Ax]].
        unfold e2a in E2Ax.
        destruct
          (excluded_middle_informative ((Stid S') x = tid_init))
          as [TIDx|nTIDx]; [congruence|].
        inversion E2Ax.
        exists x; unfolder; splits; auto.
        intros [_ TIDx]; congruence. }
      intros LEi.
      assert
        (acts_set st'.(ProgToExecution.G) (ThreadEvent (ES.cont_thread S k) index))
        as ACTS.
      { eapply acts_clos; eauto. }
      eapply e2a_kEninit
        with (S := S') (k := k') in ACTS; eauto.
      destruct ACTS as [x [[kSBx nINITx] E2Ax]].
      split; [|basic_solver].
      eapply basic_step_cont_sb_dom' in kSBx; eauto.
      rewrite <- E2Ax.
      destruct kSBx as [[HA | HB] | HC]; auto.
      { erewrite basic_step_e2a_eq_dom
          with (S := S); eauto.
        { by eapply kE_COV. }
        eapply ES.cont_sb_domE; eauto. }
      { by subst x. }
      by eapply Ce'. }

    cdes SIMST1.
    exists state'.
    red; splits; auto.

    assert ((lbl_step (ES.cont_thread S k))＊ st state') as LBLSTEPS.
    { eapply steps_stable_lbl_steps.
      apply seq_eqv_lr.
      splits; auto.
      { eapply contstable; eauto. }
      apply terminal_stable.
      by apply TERMINAL. }

    apply lbl_steps_in_steps.
    apply rtE in LBLSTEPS.
    destruct LBLSTEPS as [AA|LBLSTEPS].
    { cdes BSTEP_.
      exfalso. red in AA. desc.
      subst state'.
      eapply no_lbl_step_from_terminal.
      apply seq_eqv_l. split.
      { by eapply TERMINAL. }
      eexists. eapply STEP. }

    apply ct_begin in LBLSTEPS.
    destruct LBLSTEPS as [st''' [STEP'' LBLSTEPS]].
    assert (st''' = st'); try subst st'; auto.

    destruct STEP'' as [lbls ISTEP''].
    edestruct ilbl_step_lbls as [ll [ll' EQlbls]].
    { eapply WFT. }
    { apply ISTEP''. }
    subst lbls. symmetry.
    eapply unique_same_label_fst_ilbl_step.
    2,3: try eapply STEP; eauto.

    arewrite (lbl = Slab S' e).
    { rewrite LAB', updo_opt, upds; auto.
      unfold eq_opt, opt_ext in *.
      intros EQ. destruct e'; subst; lia. }

    erewrite basic_step_e2a_certlab_e
      with (S := S); eauto; [|apply SRCC].
    erewrite cslab; eauto;
      [| apply SRCC | by eapply C_in_D].
    erewrite basic_step_e2a_e; eauto.

    erewrite ilbl_step_eindex_lbl
      with (st := st); eauto.

    assert (wf_thread_state (ktid S k) st''') as WFT'''.
    { eapply wf_thread_state_lbl_step
        with (state0:=st); [|eexists]; eauto. }

    assert (acts_set (ProgToExecution.G st''')
                     (ThreadEvent (ktid S k) (eindex st))) as EIST'''.
    { eapply acts_clos; eauto.
      eapply lbl_step_eindex_lt; eexists; eauto. }

    assert (acts_set (ProgToExecution.G state')
                     (ThreadEvent (ktid S k) (eindex st))) as EIST''''.
    { eapply steps_preserve_E with (state0 := st'''); eauto.
      eapply lbl_steps_in_steps; eauto. }

    erewrite <- steps_preserve_lab
      with (state' := state'); eauto.
    { erewrite <- tr_lab; eauto. }
    unfold tid. eapply lbl_steps_in_steps; eauto.
  Qed.

  Lemma simrel_cert_lbl_step k S
        (st st' st'': thread_st (ktid S k))
        (NINIT : ktid S k <> tid_init)
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (LBL_STEP : lbl_step (ktid S k) st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    exists k' S',
      ⟪ kTID : ktid S' k' = ktid S k ⟫ /\
      ⟪ ESSTEP : (step Weakestmo)^? S S' ⟫ /\
      ⟪ SRCC' : simrel_cert prog S' G sc TC TC' X T k' st' st'' ⟫.
  Proof.
    assert (Wf G) as WF by apply SRCC.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S)
      as SRCONT.
    { apply SRCC. }

    edestruct LBL_STEP as [lbl ILBL_STEP].
    edestruct ilbl_step_lbls as [l [l' EQlbl]]; eauto.
    { eapply wf_cont_state; eauto. }

    destruct (classic
      (exists k' st' e e', forwarding G sc TC' S l l' k k' e e' st st')
    ) as [[k' [st''' [e [e' FRWD]]]] | nFRWD].
    { assert (st''' = st') as EQst.
      { cdes FRWD.
        eapply unique_ilbl_step; eauto.
        by rewrite <- EQlbl. }
      subst st'''.
      assert (ktid S k = ktid S k') as kEQTID.
      { by apply FRWD. }
      exists k', S. splits; auto.
      eapply simrel_cert_forwarding; eauto. }

    subst lbl.
    edestruct simrel_cert_step as [k' HH]; eauto.
    desc. cdes CertSTEP.
    assert (ES.Wf S') as WFS'.
    { eapply simrel_cert_step_wf; eauto. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (simrel_e2a S' G sc) as SRE2A.
    { eapply simrel_cert_step_e2a; eauto. }
    assert (step_ e e' S S') as WMO_STEP_.
    { eapply simrel_cert_step_step_; eauto. }
    assert (simrel_consistent prog S' G sc TC X (T \₁ eq (ktid S' k'))) as SRC'.
    { red. splits.
      { eapply simrel_cert_step_simrel; eauto. }
      eapply simrel_cert_step_consistent; eauto. }

    assert (~ Basic.IdentMap.In tid_init (stable_prog_to_prog prog)) as PTINN.
    { apply stable_prog_to_prog_no_init. apply SRCC. }
    assert (tc_coherent G sc TC ) as TCCOH.
    { apply SRCC. }
    assert (tc_coherent G sc TC') as TCCOH'.
    { eapply isim_trav_step_coherence; eauto. apply SRCC. }

    assert (e2a S' □₁ ES.cont_sb_dom S k ≡₁
            e2a S □₁ ES.cont_sb_dom S k)
      as CONTDOMEQ.
    { eapply basic_step_e2a_set_collect_eq_dom; eauto.
      eapply kE_inE; eauto. }

    exists k', S'. splits.
    { eapply basic_step_cont_thread'; eauto. }
    { apply r_step. red.
      do 2 eexists; splits; eauto.
      eapply simrel_cert_step_consistent; eauto. }
    constructor; auto.
    (* tr_step : isim_trav_step G sc (ktid S k') TC TC' *)
    { erewrite basic_step_cont_thread'; eauto. apply SRCC. }
    (* cert : cert_graph G sc TC TC' (ktid S k') state'' *)
    { erewrite basic_step_cont_thread'; eauto. apply SRCC. }
    (* cstate : simrel_cstate *)
    { eapply simrel_cert_basic_step_cstate; eauto. }
    (* ex_ktid_cov : X ∩₁ STid' ktid' ∩₁ e2a' ⋄₁ C ⊆₁ kE' *)
    { eapply simrel_cert_step_ex_ktid_cov; eauto. }
    (* cov_in_ex : e2a' ⋄₁ C ∩₁ kE' ⊆₁ X *)
    { eapply simrel_cert_step_cov_in_ex; eauto. }
    (* kcond : ... *)
    { right. splits.
      { eapply simrel_cert_step_klast_sb_max; eauto. }
      eapply simrel_cert_step_kE_sb_cov_iss; eauto. }
    (* kE_lab : eq_dom (kE' \₁ SEinit') Slab' (certG.(lab) ∘ e2a') *)
    { eapply simrel_cert_step_kE_lab; eauto. }
    (* jf_in_cert_rf : e2a' □ (Sjf ⨾ ⦗kE'⦘) ⊆ cert_rf G sc TC' ktid' *)
    { eapply simrel_cert_step_jf_in_cert_rf; eauto. }
    (* icf_ex_ktid_in_co : e2a' □ (Sjf' ⨾ ⦗set_compl kE'⦘ ⨾ Sicf' ⨾ ⦗X ∩₁ STid' ktid'⦘ ⨾ Sjf'⁻¹) ⊆ Gco *)
    { eapply simrel_cert_step_icf_ex_ktid_in_co; eauto. }
    (* icf_kE_in_co : e2a' □ (Sjf' ⨾ Sicf' ⨾ ⦗kE'⦘ ⨾ Sjf'⁻¹) ⊆ Gco *)
    { eapply simrel_cert_nforwarding_icf_kE_in_co; eauto. }
    (* ex_cont_iss : X ∩₁ e2a' ⋄₁ (contE' ∩₁ I) ⊆₁ dom_rel (Sew' ⨾ ⦗ kE' ⦘) ; *)
    { eapply simrel_cert_step_ex_cont_iss; eauto. }
    (* kE_iss : kE' ∩₁ e2a' ⋄₁ I ⊆₁ dom_rel (Sew' ⨾ ⦗ X ⦘) ; *)
    { eapply simrel_cert_step_kE_iss; eauto. }
    (* e2a_co_kE : e2a □ (Sco ⨾ ⦗kE'⦘) ⊆ Gco ;  *)
    { eapply simrel_cert_step_e2a_co_kE; eauto. }
    (* e2a_co_ex_ktid : e2a □ (Sco ⨾ ⦗X ∩₁ STid' ktid' \₁ e2a ⋄₁ contE⦘) ⊆ Gco ; *)
    { eapply simrel_cert_step_e2a_co_ex_ktid; eauto. }
    (* rmw_cov_in_kE : Grmw ⨾ ⦗C' ∩₁ e2a' □₁ kE'⦘ ⊆ e2a' □ Srmw' ⨾ ⦗ kE' ⦘ *)
    { eapply simrel_cert_step_rmw_cov_in_kE; eauto. }

    destruct
      (classic ((e2a S' ⋄₁ C' ∩₁ kE S' k' ⊆₁ e2a S ⋄₁ C' ∩₁ kE S k))).
    { eapply simrel_cert_step_contsimstate_kE_covered; eauto. }
    eapply simrel_cert_step_contsimstate_kE_covering; eauto.

  Qed.

End SimRelCertStepLemma.
