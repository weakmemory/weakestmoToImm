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
Require Import SimRelCertStepCoh.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelCertStepLemma.

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

  Notation "'ktid' S" := (fun k => ES.cont_thread S k) (at level 1, only parsing).

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
    assert (ES.Wf S') as WFS'.
    { eapply simrel_cert_step_wf; eauto. }
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
    assert (~ Basic.IdentMap.In tid_init (stable_prog_to_prog prog)) as PTINN.
    { apply stable_prog_to_prog_no_init. apply SRCC. }
    assert (simrel_e2a S' G sc) as SRE2A by apply SRC'.

    assert (~ SE S (opt_ext e e')) as NSE.
    { cdes BSTEP_. desf. unfold opt_ext, ES.acts_set in *; simpls. 
      desf; omega. }

    assert (forall s (SES : s ⊆₁ SE S) s',
               s ∩₁ e2a S' ⋄₁ s' ⊆₁ s ∩₁ e2a S ⋄₁ s') as SSE2A.
    { unfolder. ins. desf. splits; auto.
      erewrite <- basic_step_e2a_eq_dom; eauto. }
    
    (* TODO: make a lemma *)
    assert (e2a S' □₁ ES.cont_sb_dom S k ≡₁ e2a S □₁ ES.cont_sb_dom S k) as CONTDOMEQ.
    { unfolder. ins. desf. splits; ins; desf; eexists; splits; eauto.
      symmetry.
      all: eapply basic_step_e2a_eq_dom; eauto.
      all: eapply kE_inE; eauto. }

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
        erewrite basic_step_e2a_eq_dom with (S:=S); eauto.
        eapply kE_lab; eauto. by split. }
      unfolder. ins. desf.
      { eapply basic_step_e2a_lab_e with (S:=S); eauto; apply SRCC. }
      eapply basic_step_e2a_lab_e' with (S:=S); eauto; apply SRCC. }
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
        unfolder. ins. desf. }
      cdes BSTEP_. desf.
      red in CertSTEP_. desf; cdes CertSTEP_.
      1,3: by rewrite JF'.
      all: cdes AJF; rewrite JF'; rewrite seq_union_l; unionL; auto.
      all: unfold jf_delta.
      { basic_solver. }
      desf. simpls. desf. unfolder. ins. desf. omega. }
    { admit. }
    { erewrite basic_step_cont_sb_dom; eauto.
      rewrite !set_collect_union.
      rewrite !set_inter_union_r.
      rewrite !id_union.
      rewrite !seq_union_r, !collect_rel_union.
      
      cdes BSTEP_.
      repeat apply union_mori.
      { (* TODO: make a lemma *)
        rewrite CONTDOMEQ.
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
        erewrite basic_step_e2a_e with (S:=S) in RMW; eauto.
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
      red.
      do 2 eexists.
      splits; eauto.
      apply RMW'. right. red. unfold eq_opt. basic_solver. }
    
    assert (C ⊆₁ C') as CINC.
    { eapply sim_trav_step_covered_le.
      eexists. apply SRCC. }

    assert (Ssb S' ≡ Ssb S ∪ sb_delta S k e e') as SB'.
    { cdes BSTEP_. apply SB'. }

    ins.
    destruct PC as [[[CC [y [SY UU]]] TT] PP].

    assert (SEninit S' e0) as EE0'.
    { eapply ES.K_inEninit; eauto. }
    assert ((Stid S') e0 = (Stid S') y) as EYTT.
    { rewrite !e2a_tid. by rewrite UU. }

    assert ((K S') (k', existT Language.state (thread_lts (ES.cont_thread S k)) st')) as KK.
    { cdes BSTEP_. red. rewrite CONT'. constructor. done. }
      
    destruct XE as [[XE NT]|XE]; auto.
    { exfalso. 
      eapply ES.cont_sb_tid with (lang:=thread_lts (ES.cont_thread S k)) in SY; eauto.
      destruct SY as [SY|SY].
      2: { apply NT. by rewrite <- SY. }
      apply EE0'. split; [apply EE0'|].
      rewrite EYTT. apply SY. }

    assert (e0 = y); subst.
    { eapply e2a_cont_sb_dom_inj with (k:=k'); eauto; try apply SRCC.
      eapply e2a_GE; eauto. }

    eapply basic_step_cont_sb_dom in SY; eauto.
    apply set_unionA in SY.
    destruct SY as [SY|SY].
    { assert (C' ∩₁ e2a S' □₁ ES.cont_sb_dom S' k' ≡₁ C' ∩₁ e2a S □₁ ES.cont_sb_dom S k)
        as COLD.
      { split.
        2: { erewrite basic_step_cont_sb_dom with (S':=S'); eauto.
             rewrite <- CONTDOMEQ.
             basic_solver 10. }
        erewrite basic_step_cont_sb_dom with (S':=S'); eauto.
        rewrite set_unionA.
        rewrite set_collect_union.
        rewrite !set_inter_union_r.
        unionL.
        { by rewrite CONTDOMEQ. }
        etransitivity.
        2: by apply set_subset_empty_l.
        unfold eq_opt.
        unfolder. ins. desf.
        all: eapply PP; exists (e2a S' y0).
        all: apply seq_eqv_r; split; [|split]; auto.
        2,4: red; eexists; splits; [|by eauto];
          eapply basic_step_cont_sb_dom with (S':=S'); eauto; unfold eq_opt;
            basic_solver.
        all: eapply e2a_sb; try apply SRC'.
        1,3: apply stable_prog_to_prog_no_init; apply SRC'.
        all: red; do 2 eexists; splits; eauto.
        all: apply SB'; right; red; unfold eq_opt.
        all: basic_solver. }
      
      assert (SE S y) as EY.
      { eapply kE_inE; eauto. }
      assert (Stid S' y = Stid S y) as TTY.
      { eapply basic_step_tid_eq_dom; eauto. }
      rewrite TTY in *.
      assert (e2a S' y = e2a S y) as E2AY.
      { eapply basic_step_e2a_eq_dom; eauto. }
      rewrite E2AY in *.
      assert ((K S) (CEvent y, existT Language.state (thread_lts ((Stid S) y)) state))
        as YCONTOLD.
      { (* TODO: introduce a lemma *)
        admit. }
      assert (~ dom_rel (Gsb ⨾ ⦗C' ∩₁ e2a S □₁ ES.cont_sb_dom S k⦘) (e2a S y)) as YND.
      { intros [z AA]. destruct_seq_r AA as BB.
        apply COLD in BB.
        apply PP. basic_solver 10. }
      assert ((C' ∩₁ e2a S □₁ ES.cont_sb_dom S k ∩₁ GTid ((Stid S) y) \₁
                  dom_rel (Gsb ⨾ ⦗C' ∩₁ e2a S □₁ ES.cont_sb_dom S k⦘)) (e2a S y)) as YD.
      { split; auto. basic_solver. }
      red. splits.
      { ins. split; intros HH; [apply COLD in HH|apply COLD].
        all: eapply contpckE; eauto; basic_solver. }
      eapply contpckE; eauto.
      basic_solver. }
    assert (y = opt_ext e e'); subst.
    { unfold opt_ext, eq_opt in *. desf.
      2: { generalize SY. basic_solver. }
      destruct SY; desf.
      exfalso.
      apply ES.rmw_K with (S:=S'); auto.
      do 2 eexists. splits.
      { apply INK. }
      cdes BSTEP_. eexists. apply RMW'. unfold rmw_delta, eq_opt.
      basic_solver. }

    assert ((Stid S') (opt_ext e e') = ES.cont_thread S k) as ETT.
    { cdes BSTEP_. rewrite TID'. unfold upd_opt, opt_ext. desf.
      all: by rewrite upds. }

    assert (k' = CEvent (opt_ext e e')) by (by cdes BSTEP_); subst.
    assert (state = st'); subst.
    { rewrite ETT in INK.
      red in INK. cdes BSTEP_. rewrite CONT' in INK. inv INK.
      { match goal with
        | H: (_, _) = (_, _) |- _ => rename H into EQ
        end.
        apply pair_inj in EQ. inv EQ. }
      exfalso.
      match goal with
      | H: In _ (ES.cont S) |- _ => rename H into IN
      end.
      eapply WFS.(ES.K_inEninit) in IN.
      apply NSE. apply IN. }
    
    (* assert (@sim_state G sim_normal (C' ∩₁ e2a S □₁ ES.cont_sb_dom S k) *)
    (*                    (ES.cont_thread S k) st) as SST. *)
    (* { admit. } *)
    (* red. splits. *)
    (* 2: {  *)
  Admitted.

End SimRelCertStepLemma.