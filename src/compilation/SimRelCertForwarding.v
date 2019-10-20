Require Import Program.Basics Omega.
From hahn Require Import Hahn.
From PromisingLib Require Import Language.
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
Require Import SimRelAddJF.
Require Import SimRelCert.
Require Import SimRelCertBasicStep.
Require Import SimRelCertStep.
Require Import ProgES.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelCertForwarding.

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

  Definition forwarding S lbl lbl' k k' e e'
             (st st' : thread_st (ktid S k)) :=
    ⟪ LBL  : lbl  = Slab S e ⟫ /\
    ⟪ LBL' : lbl' = option_map (Slab S) e' ⟫ /\
    ⟪ Kk   : K S (k , existT _ _ st ) ⟫ /\
    ⟪ Kk'  : K S (k', existT _ _ st') ⟫ /\
    ⟪ ADJ  : ES.cont_adjacent S k k' e e'⟫ /\
    ⟪ STEP : ilbl_step (ktid S k) (opt_to_list lbl' ++ [lbl]) st st' ⟫ /\
    ⟪ CertRF : e2a S □ Sjf S ⨾ ⦗eq e⦘ ⊆ cert_rf G sc TC' ⟫.

  Lemma forwarding_seqn_e S lbl lbl' k k' e e'
        (st st' st'': thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st') :
    ES.seqn S e = eindex st.
  Proof.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (simrel_cont (stable_prog_to_prog prog) S)
      as SRCONT.
    { apply SRCC. }
    unfold forwarding in FRWD. desc.
    set (AA := ADJ).
    unfold ES.cont_adjacent in AA. desc.
    unfold ES.cont_sb_dom in kSBDOM.
    destruct k eqn:Heq.
    { erewrite continit; eauto.
      unfold ES.seqn.
      arewrite (dom_rel (Ssb S ∩ ES.same_tid S ⨾ ⦗eq e⦘) ≡₁ ∅).
      2 : by erewrite countNatP_empty.
      split; [|done].
      rewrite seq_eqv_r.
      intros x [y [[SB STID] EQy]].
      red. subst y.
      eapply ES.init_tid_K; eauto.
      exists (existT _ _ st), k.
      splits; [by subst k|].
      subst k. erewrite <- ES.cont_adjacent_tid_e; eauto.
      rewrite <- STID.
      assert (SEinit S x) as INITx.
      { apply kSBDOM. basic_solver 10. }
      red in INITx. unfolder in INITx. desf. }
    erewrite contseqn; eauto.
    erewrite ES.seqn_immsb; eauto.
    { red.
      erewrite ES.cont_adjacent_tid_e
        with (k := k) (e := e); eauto.
      2 : eby subst k.
      unfold ES.cont_thread. desf. }
    red. splits.
    { assert (dom_rel (Ssb S ⨾ ⦗eq e⦘) eid) as HH.
      { apply kSBDOM. basic_solver 10. }
      unfolder in HH. desf. }
    intros x SB SB'.
    assert (dom_rel ((Ssb S)^? ⨾ ⦗eq eid⦘) x) as HH.
    { apply kSBDOM. basic_solver 10. }
    unfolder in HH. desf.
    { eapply ES.sb_irr; eauto. }
    eapply ES.sb_irr; eauto.
    eapply ES.sb_trans; eauto.
  Qed.

  Lemma forwarding_seqn_e' S lbl lbl' k k' e e'
        (st st' st'': thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e (Some e') st st') :
    ES.seqn S e' = 1 + eindex st.
  Proof.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (simrel_cont (stable_prog_to_prog prog) S)
      as SRCONT.
    { apply SRCC. }
    set (AA := FRWD).
    unfold forwarding in AA. desc.
    set (AA := ADJ).
    unfold ES.cont_adjacent in AA. desc.
    assert (immediate (ES.sb S) e e') as IMMSB.
    { apply ES.rmwi; auto.
      apply RMWe. basic_solver. }
    erewrite ES.seqn_immsb
      with (x := e); eauto; try red; splits.
    { erewrite forwarding_seqn_e; eauto. }
    erewrite ES.cont_adjacent_tid_e; eauto.
    erewrite ES.cont_adjacent_tid_e'
      with (k := k); eauto.
  Qed.

  Lemma forwarding_e2a_e S lbl lbl' k k' e e'
        (st st' st'': thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st') :
    e2a S e = ThreadEvent (ES.cont_thread S k) (eindex st).
  Proof.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (ES.cont_adjacent S k k' e e') as ADJ.
    { apply FRWD. }
    rewrite e2a_ninit; auto.
    2 : eapply ES.cont_adjacent_ninit_e; eauto.
    erewrite ES.cont_adjacent_tid_e; eauto.
    erewrite forwarding_seqn_e; eauto.
  Qed.

  Lemma forwarding_e2a_e' S lbl lbl' k k' e e'
        (st st' st'': thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e (Some e') st st') :
    e2a S e' = ThreadEvent (ES.cont_thread S k) (1 + eindex st).
  Proof.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (ES.cont_adjacent S k k' e (Some e')) as ADJ.
    { apply FRWD. }
    rewrite e2a_ninit; auto.
    2 : eapply ES.cont_adjacent_ninit_e'; eauto.
    erewrite ES.cont_adjacent_tid_e'; eauto.
    erewrite forwarding_seqn_e'; eauto.
  Qed.

  Lemma forwarding_ex_kcond lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st') :
    ⟪ klast_ex : klast S k ⊆₁ X ⟫ /\
    ⟪ kE_sb_cov_iss : e2a S □₁ codom_rel (⦗kE S k⦘ ⨾ Ssb S ⨾ ⦗Stid_ S (ktid S k)⦘) ⊆₁ CsbI G TC ⟫.
  Proof.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    edestruct kcond; eauto; desc.
    edestruct ES.exists_cont_last
      with (k := k) as [x kLASTx]; eauto.
    exfalso.
    eapply klast_sb_max
      with (b := e); eauto.
    cdes FRWD.
    set (kSBIMM := ADJ).
    apply ES.cont_adjacent_cont_last_sb_imm
      in kSBIMM; auto.
    destruct kSBIMM as [y SB].
    destruct_seq_l SB as kLASTy.
    destruct SB as [SB _].
    unfold ES.cont_last in *.
    destruct k; [|congruence].
    apply ES.sb_init; auto.
    split; auto.
    cdes FRWD. eapply ES.cont_adjacent_ninit_e; eauto.
  Qed.

  Lemma forwarding_ex_e lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    X e.
  Proof.
    assert (Wf G) as WFG.
    { apply SRCC. }
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (@es_consistent S Weakestmo) as CONS.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC.
    { apply SRCC. }
    assert (simrel prog S G sc TC X (T \₁ eq (ktid S k))) as SR_.
    { apply SRCC. }
    assert (SEninit S e) as nINITe.
    { cdes FRWD. eapply ES.cont_adjacent_ninit_e; eauto. }
    assert (SE S e) as Ee.
    { apply nINITe. }
    assert (ES.cont_last S k ⊆₁ X) as klastX.
    { eapply forwarding_ex_kcond; eauto. }
     edestruct ES.exists_cont_last
      with (k := k) as [x kLASTx]; eauto.
    assert (X x) as Xx.
    { basic_solver. }
    assert (immediate (Ssb S) x e) as IMMSB.
    { cdes FRWD. eapply ES.cont_adjacent_con_last_sb_imm_alt; eauto. }
    assert (CsbI G TC (e2a S e)) as CsbIe.
    { eapply forwarding_ex_kcond; eauto.
      apply ES.cont_last_in_cont_sb
        in kLASTx; auto.
      eexists; splits; eauto.
      exists x.
      apply seq_eqv_lr; splits; auto.
      { apply IMMSB. }
      cdes FRWD.
      erewrite ES.cont_adjacent_tid_e; eauto. }

    eapply ex_cov_iss in CsbIe; eauto.
    destruct CsbIe as [y [Xy EQE2Ay]].
    assert (SE S y) as Ey.
    { eapply Execution.ex_inE; eauto. }
    set (EQE2Ay' := EQE2Ay).
    apply e2a_eq_in_cf in EQE2Ay'; auto.
    destruct EQE2Ay' as [EQ|CF]; [congruence|].
    set (EQE2Ay' := EQE2Ay).
    erewrite e2a_ninit
      with (e := e) in EQE2Ay'; auto.
    unfold e2a in EQE2Ay'.
    destruct
      (excluded_middle_informative ((Stid S) y = tid_init))
      as [TIDy|nTIDy]; [congruence|].
    inversion EQE2Ay' as [[EQTID EQSEQN]].
    clear EQE2Ay'.
    assert (Stid S y = ES.cont_thread S k) as TIDy.
    { cdes FRWD. erewrite <- ES.cont_adjacent_tid_e; eauto. }
    assert (SEninit S y) as nINITy.
    { split; auto.
      unfold ES.acts_init_set.
      intros [_ INITy]. congruence. }
    assert (Sicf S y e) as ICF.
    { red; split; auto.
      exists x; split; auto.
      apply immediate_transp with (r := Ssb S).
      unfold transp.
      eapply ES.seqn_eq_imm_sb; eauto.
      intros CF'.
      eapply Execution.ex_ncf; eauto.
      apply seq_eqv_lr.
      splits; [| apply CF' |]; eauto. }
    assert ((SE S ∩₁ SR S) y) as Ry.
    { split; auto.
      eapply icf_R; eauto.
      basic_solver. }
    assert ((SE S ∩₁ SR S) e) as Re.
    { split; auto.
      apply ES.icf_sym in ICF.
      eapply icf_R; eauto.
      basic_solver. }
    apply ES.jf_complete in Ry; auto.
    apply ES.jf_complete in Re; auto.
    destruct Ry as [w  JF ].
    destruct Re as [w' JF'].
    assert
      (cert_rf G sc TC (e2a S w) (e2a S y))
      as CertRF.
    { eapply jf_ex_in_cert_rf; eauto. basic_solver 10. }
    assert
      (cert_rf G sc TC' (e2a S w') (e2a S e))
      as CertRF'.
    { apply FRWD. basic_solver 10. }
    assert (Gco^? (e2a S w) (e2a S w')) as CO.
    { eapply sim_trav_step_cert_rf_co; eauto.
      1-3: try eexists; apply SRCC.
      unfolder; exists (e2a S y); splits; auto; congruence. }
    assert (Gco (e2a S w') (e2a S w)) as CO'.
    { eapply icf_ex_ktid_in_co; eauto.
      do 2 eexists; splits; eauto.
      exists e; splits; auto.
      apply seq_eqv_l; splits.
      { cdes FRWD. eapply ES.cont_adjacent_nsb_dom_e; eauto. }
      exists y; splits.
      { by apply ES.icf_sym. }
      apply seq_eqv_l; splits; [|done].
      basic_solver. }
    exfalso.
    destruct CO as [EQ|CO].
    all: eapply co_irr; eauto.
    { rewrite EQ in CO'. apply CO'. }
    eapply co_trans; eauto.
  Qed.

  Lemma forwarding_ex_e' lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e (Some e') st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    X e'.
  Proof.
    assert (Wf G) as WFG.
    { apply SRCC. }
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (@es_consistent S Weakestmo) as CONS.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC.
    { apply SRCC. }
    eapply Execution.ex_rmw_fwcl; eauto.
    exists e. apply seq_eqv_l. split.
    { eapply forwarding_ex_e; eauto. }
    cdes FRWD; eapply ES.cont_adjacent_rmw; eauto.
  Qed.

  Lemma simrel_cert_forwarding_ex_ktid_cov lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    X ∩₁ Stid_ S (ktid S k') ∩₁ e2a S ⋄₁ C ⊆₁ kE S k'.
  Proof.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    arewrite (ktid S k' = ktid S k).
    { symmetry. apply FRWD. }
    etransitivity; [apply SRCC|].
    eapply ES.cont_adjacent_sb_dom_mon; eauto.
    apply FRWD.
  Qed.

  Lemma simrel_cert_forwarding_cov_in_ex lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    e2a S ⋄₁ C ∩₁ kE S k' ⊆₁ X.
  Proof.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (ES.cont_adjacent S k k' e e') as ADJ.
    { apply FRWD. }
    rewrite ES.cont_adjacent_sb_dom
      with (k' := k'); eauto.
    rewrite set_unionA.
    rewrite set_inter_union_r.
    unionL.
    { rewrite set_interC.
      rewrite set_interC.
      apply SRCC. }
    rewrite set_inter_union_r.
    unfolder. unionL.
    { intros x [Cx EQx]. subst x. exfalso.
      eapply e2a_ge_ncov; eauto.
      { apply FRWD. }
      { erewrite ES.cont_adjacent_tid_e; eauto. }
      erewrite forwarding_seqn_e; eauto. }
    intros x [Cx EQx].
    destruct e' as [e'|]; [|done].
    subst x. exfalso.
    eapply e2a_ge_ncov; eauto.
    { eapply ES.cont_adjacent_ninit_e'; eauto. }
    { erewrite ES.cont_adjacent_tid_e'; eauto. }
    erewrite forwarding_seqn_e'; eauto.
  Qed.

  Lemma simrel_cert_forwarding_klast_ex lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    klast S k' ⊆₁ X.
  Proof.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    set (FRWD' := FRWD).
    cdes FRWD'. cdes ADJ.
    unfold ES.cont_last.
    subst k'.
    unfold opt_ext.
    destruct e' as [e'|].
    { unfolder. ins. desf.
      eapply forwarding_ex_e'; eauto. }
    unfolder. ins. desf.
    eapply forwarding_ex_e; eauto.
  Qed.

  Lemma simrel_cert_forwarding_kE_ex lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    kE S k' ⊆₁ X.
  Proof.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    erewrite ES.cont_sb_dom_alt; auto.
    erewrite simrel_cert_forwarding_klast_ex; eauto.
    apply prcl_cr. apply SRCC.
  Qed.

  Lemma simrel_cert_forwarding_kE_sb_cov_iss lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    e2a S □₁ codom_rel (⦗kE S k'⦘ ⨾ Ssb S ⨾ ⦗Stid_ S (ktid S k')⦘) ⊆₁ CsbI G TC.
  Proof.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    cdes FRWD.
    arewrite (ktid S k' = ktid S k).
    { by cdes ADJ. }
    edestruct forwarding_ex_kcond
      as [HA HB]; eauto.
    red in HA, HB.
    erewrite ES.cont_adjacent_sb_dom; eauto.
    rewrite set_unionA.
    rewrite id_union.
    relsf; split; try done.
    edestruct ES.exists_cont_last
      with (k := k) as [x kLASTx]; eauto.
    rewrite seq_eqv_lr.
    intros y' [y [HH EQy']].
    destruct HH as [z [EQz [SB TIDy]]].
    subst y'.
    apply HB.
    eexists; splits; eauto.
    exists x.
    apply seq_eqv_lr.
    splits; auto.
    { apply ES.cont_last_in_cont_sb; auto. }
    unfold eq_opt in *.
    destruct EQz as [EQz|EQz];
      [|destruct e' as [e'|]];
      try done; subst z.
    { eapply ES.sb_trans; eauto.
      eapply ES.cont_adjacent_con_last_sb_imm_alt; eauto. }
    eapply ES.sb_trans; eauto.
    eapply ES.sb_trans; eauto.
    { eapply ES.cont_adjacent_con_last_sb_imm_alt; eauto. }
    eapply ES.cont_adjacent_sb_imm; eauto.
    basic_solver.
  Qed.

  Lemma simrel_cert_forwarding_kE_lab lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    eq_dom (kE S k' \₁ SEinit S) (Slab S) (Execution.lab (ProgToExecution.G st'') ∘ e2a S).
  Proof.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (simrel_cont (stable_prog_to_prog prog) S)
      as SRCONT.
    { apply SRCC. }
    assert (ES.cont_adjacent S k k' e e') as ADJ.
    { apply FRWD. }
    set (AA := FRWD).
    cdes AA.
    assert (ktid S k = ktid S k') as kEQTID.
    { by apply ADJ. }
    assert (wf_thread_state (ktid S k) st) as WFst.
    { eapply contwf; eauto. }
    assert (wf_thread_state (ktid S k) st') as WFst'.
    { rewrite kEQTID. eapply contwf; eauto. by rewrite <- kEQTID. }
    assert (Gtid (e2a S e) = ES.cont_thread S k) as GTIDe.
    { erewrite e2a_ninit; [|apply ADJ].
      unfold Events.tid.
      erewrite ES.cont_adjacent_tid_e; eauto. }
    rewrite ES.cont_adjacent_sb_dom
      with (k' := k'); eauto.
    rewrite set_unionA.
    rewrite !set_minus_union_l.
    rewrite !eq_dom_union. splits.
    { apply SRCC. }
    { intros x [EQx _]. subst x.
      unfold compose.
      erewrite steps_preserve_lab; eauto.
      { rewrite <- LBL.
        erewrite forwarding_e2a_e; eauto.
        eapply ilbl_step_eindex_lbl; eauto. }
      { by rewrite GTIDe. }
      { apply lbl_steps_in_steps.
          by rewrite GTIDe. }
      erewrite forwarding_e2a_e; eauto.
      eapply acts_clos; eauto.
      eapply ilbl_step_eindex_lt.
      apply STEP. }
    intros x [EQx _].
    unfold eq_opt in EQx.
    destruct e' as [e'|]; [|done].
    assert (Gtid (e2a S e') = ES.cont_thread S k) as GTIDe'.
    { erewrite e2a_ninit.
      2 : eapply ES.cont_adjacent_ninit_e'; eauto.
      unfold Events.tid.
      erewrite ES.cont_adjacent_tid_e'; eauto. }
    subst x. unfold compose.
    erewrite steps_preserve_lab; eauto.
    { unfold option_map in LBL'.
      destruct lbl' as [lbl'|];
        inversion LBL' as [HLBL'].
      rewrite <- HLBL'.
      erewrite forwarding_e2a_e'; eauto.
      eapply ilbl_step_eindex_lbl'; eauto. }
    { by rewrite GTIDe'. }
    { apply lbl_steps_in_steps.
        by rewrite GTIDe'. }
    erewrite forwarding_e2a_e'; eauto.
    eapply acts_clos; eauto.
    erewrite ilbl_step_eindex_shift
      with (st' := st'); eauto.
    unfold option_map in LBL'.
    destruct lbl' as [lbl'|].
    2 : inversion LBL'.
    unfold opt_to_list, app, length.
    omega.
  Qed.

  Lemma simrel_cert_forwarding_jf_in_cert_rf lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    e2a S □ (Sjf S ⨾ ⦗kE S k'⦘) ⊆ cert_rf G sc TC'.
  Proof.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (simrel_cont (stable_prog_to_prog prog) S)
      as SRCONT.
    { apply SRCC. }
    assert (ES.cont_adjacent S k k' e e') as ADJ.
    { apply FRWD. }
    erewrite ES.cont_adjacent_sb_dom; eauto.
    rewrite !id_union, !seq_union_r, !collect_rel_union.
    unionL; auto.
    { apply SRCC. }
    { apply FRWD. }
    unfold eq_opt.
    destruct e' as [e'|].
    2 : basic_solver.
    assert (ES.rmw S e e') as RMW.
    { eapply ES.cont_adjacent_rmw; eauto. }
    apply ES.rmwD in RMW; auto.
    rewrite ES.jfD; auto.
    generalize RMW. type_solver.
  Qed.

  Lemma simrel_cert_forwarding_icf_ex_ktid_in_co lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
     e2a S □ (Sjf S ⨾ ⦗set_compl (kE S k')⦘ ⨾ Sicf S ⨾ ⦗X ∩₁ (Stid_ S (ktid S k'))⦘ ⨾ (Sjf S)⁻¹) ⊆ Gco.
  Proof.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (ES.cont_adjacent S k k' e e') as ADJ.
    { apply FRWD. }
    erewrite <- ES.cont_adjacent_sb_dom_mon; eauto.
    arewrite (ES.cont_thread S k' = ES.cont_thread S k).
    { by cdes ADJ. }
    apply SRCC.
  Qed.

  Lemma simrel_cert_forwarding_icf_kE_in_co lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    e2a S □ (Sjf S ⨾ Sicf S ⨾ ⦗kE S k'⦘ ⨾ (Sjf S)⁻¹) ⊆ Gco.
  Proof.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (ES.cont_adjacent S k k' e e') as ADJ.
    { apply FRWD. }
    intros x' y' [x [y [HH [EQx EQy]]]].
    destruct HH as [z  [JF HH]].
    destruct HH as [z' [ICF JF']].
    destruct_seq_l JF' as kSBz'.
    red in JF'. subst x' y'.
    eapply simrel_cert_forwarding_icf_ex_ktid_in_co; eauto.
    do 2 eexists; splits; eauto.
    exists z; splits; auto.
    apply seq_eqv_l; splits.
    (* dom (cf ; [cont_sb_dom S k]) ⊆ ~ cont_sb_dom S k  *)
    { cdes FRWD.
      eapply ES.cont_sb_dom_cf; eauto.
      destruct ICF as [CF _].
      basic_solver 10. }
    exists z'; splits; auto.
    apply seq_eqv_l; splits; [|done].
    red; split.
    { eapply simrel_cert_forwarding_kE_ex; eauto. }
    cdes FRWD; eapply ES.cont_sb_tid in kSBz'; eauto.
    destruct kSBz' as [INITz' | TIDz']; auto.
    apply ES.icfEninit in ICF; auto.
    exfalso.
    generalize ICF INITz'.
    unfold ES.acts_ninit_set.
    basic_solver 10.
  Qed.

  Lemma simrel_cert_forwarding_ex_cont_iss_e lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    X ∩₁ e2a S ⋄₁ (eq (e2a S e) ∩₁ I) ⊆₁ dom_rel (Sew S ⨾ ⦗eq e⦘).
  Proof.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (@es_consistent S Weakestmo) as SCONS.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC.
    { apply SRCC. }
    assert (X e) as Xe.
    { eapply forwarding_ex_e; eauto. }
    intros y [Xy [EQy Iy]].
    eapply ES.ew_eqvW with (ws := eq e); auto.
    { intros ee EQee. subst ee. split.
      { cdes FRWD; eapply ES.cont_adjacent_ninit_e; eauto. }
      eapply ex_iss_inW; [apply SRCC|].
      unfolder; splits; auto; congruence. }
    edestruct e2a_eq_in_cf
      with (x := y) (y := e) as [EQ | CF]; eauto.
    { eapply Execution.ex_inE; eauto. }
    { cdes FRWD; eapply ES.cont_adjacent_ninit_e; eauto. }
    exfalso. eapply Execution.ex_ncf; eauto.
    apply seq_eqv_lr; splits; eauto.
  Qed.

  Lemma simrel_cert_forwarding_ex_cont_iss_e' lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e (Some e') st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    X ∩₁ e2a S ⋄₁ (eq (e2a S e')∩₁ I) ⊆₁ dom_rel (Sew S ⨾ ⦗eq e'⦘).
  Proof.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (@es_consistent S Weakestmo) as SCONS.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC.
    { apply SRCC. }
    assert (X e') as Xe.
    { eapply forwarding_ex_e'; eauto. }
    intros y [Xy [EQy Iy]].
    eapply ES.ew_eqvW with (ws := eq e'); auto.
    { intros ee EQee. subst ee. split.
      { cdes FRWD; eapply ES.cont_adjacent_ninit_e'; eauto. }
      eapply ex_iss_inW; [apply SRCC|].
      unfolder; splits; auto; congruence. }
    edestruct e2a_eq_in_cf
      with (x := y) (y := e') as [EQ | CF]; eauto.
    { eapply Execution.ex_inE; eauto. }
    { cdes FRWD; eapply ES.cont_adjacent_ninit_e'; eauto. }
    exfalso. eapply Execution.ex_ncf; eauto.
    apply seq_eqv_lr; splits; eauto.
  Qed.

  Lemma simrel_cert_forwarding_ex_cont_iss lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    X ∩₁ e2a S ⋄₁ (acts_set st'.(ProgToExecution.G) ∩₁ I) ⊆₁ dom_rel (Sew S ⨾ ⦗ kE S k' ⦘).
  Proof.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (@es_consistent S Weakestmo) as SCONS.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC.
    { apply SRCC. }
    assert (simrel_cont (stable_prog_to_prog prog) S)
      as SRCONT.
    { apply SRCC. }
    cdes FRWD.
    erewrite ES.cont_adjacent_sb_dom; eauto.
    edestruct ilbl_step_acts_set as [a [a' HH]].
    { eapply wf_cont_state; eauto. }
    { eapply FRWD. }
    destruct HH as [EQa [EQa' ACTS]].
    red in EQa, EQa', ACTS.
    rewrite ACTS.
    rewrite !set_inter_union_l, !set_map_union.
    rewrite !set_inter_union_r, !id_union,
            !seq_union_r, !dom_union.
    apply set_union_Proper;
      [apply set_union_Proper|].
    { apply SRCC. }
    { arewrite (a = e2a S e).
      { erewrite forwarding_e2a_e; eauto. }
      eapply simrel_cert_forwarding_ex_cont_iss_e; eauto. }
    unfold eq_opt, option_map in *.
    destruct lbl' as [lbl'|];
      [|basic_solver].
    destruct e' as [e'|]; [|done].
    destruct a' as [a'|]; [|done].
    arewrite (a' = e2a S e').
    { erewrite forwarding_e2a_e'; eauto; congruence. }
    eapply simrel_cert_forwarding_ex_cont_iss_e'; eauto.
  Qed.

  Lemma simrel_cert_forwarding_kE_iss lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    kE S k' ∩₁ e2a S ⋄₁ I ⊆₁ dom_rel (Sew S ⨾ ⦗ X ⦘).
  Proof.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC.
    { apply SRCC. }
    assert (X ∩₁ SW S ⊆₁ X) as XW.
    { basic_solver. }
    rewrite <- XW.
    rewrite <- ES.ew_eqvW; auto.
    2 : erewrite Execution.ex_inE
          with (X := X); eauto.
    erewrite simrel_cert_forwarding_kE_ex; eauto.
    rewrite <- set_interK
      with (s := X) at 1.
    rewrite set_interA.
    erewrite ex_iss_inW; eauto.
    apply SRCC.
  Qed.

  Lemma simrel_cert_forwarding_e2a_co_kE lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    e2a S □ Sco S ⨾ ⦗ES.cont_sb_dom S k'⦘ ⊆ Gco.
  Proof.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC.
    { apply SRCC. }
    cdes FRWD.
    erewrite ES.cont_adjacent_sb_dom; eauto.
    rewrite set_unionA.
    rewrite id_union, seq_union_r, collect_rel_union.
    unionL; [apply SRCC|].
    arewrite
      (eq e ∪₁ eq_opt e' ⊆₁
          X ∩₁ (Stid_ S (ktid S k)) \₁ e2a S ⋄₁ (acts_set st.(ProgToExecution.G)));
      [|apply SRCC].
    unfolder; unfold eq_opt; ins; desf; splits.
    { eapply forwarding_ex_e; eauto. }
    { eapply ES.cont_adjacent_tid_e; eauto. }
    { intros HH.
      eapply acts_rep
        in HH; [|eapply wf_cont_state]; eauto.
      erewrite forwarding_e2a_e in HH; eauto.
      desc. inversion REP. omega. }
    { eapply forwarding_ex_e'; eauto. }
    { eapply ES.cont_adjacent_tid_e'; eauto. }
    intros HH.
    eapply acts_rep
      in HH; [|eapply wf_cont_state]; eauto.
    erewrite forwarding_e2a_e' in HH; eauto.
    desc. inversion REP. omega.
  Qed.

  Lemma simrel_cert_lbl_step_nrwm_eindex k S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (LBL_STEP : lbl_step (ktid S k) st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    ~ (codom_rel Grmw) (ThreadEvent (ktid S k) st.(eindex)).
  Proof.
    assert (Wf G) as WFG by apply SRCC.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S)
      as SRCONT.
    { apply SRCC. }

    intros [x RMW].
    assert (exists xindex,
               ⟪ ILT : xindex < eindex st ⟫ /\
               x = ThreadEvent (ES.cont_thread S k) xindex).
    { destruct x; simpls.
      { apply WFG.(rmw_from_non_init) in RMW.
        destruct_seq_l RMW as AA. desf. }
      apply WFG.(rmw_in_sb) in RMW.
      destruct_seq RMW as [AA BB].
      red in RMW. desf.
      eauto. }
    desf.

    assert (wf_thread_state (ktid S k) st) as WTS.
    { eapply wf_cont_state; eauto. }
    assert ((ProgToExecution.step (ktid S k))＊ st st') as STEPS.
    { destruct LBL_STEP.
      apply inclusion_t_rt.
      eapply ilbl_step_in_steps; eauto. }
    assert (wf_thread_state (ktid S k) st') as WTS'.
    { eapply wf_thread_state_steps; eauto. }
    assert ((ProgToExecution.step (ES.cont_thread S k))＊ st' st'')
      as STEPS'.
    { apply lbl_steps_in_steps; eauto. }
    assert (wf_thread_state (ES.cont_thread S k) st'') as WTS''.
    { eapply wf_thread_state_steps; eauto. }

    eapply eindex_not_in_rmw
      with (thread := ktid S k)
           (st := st) (st' := st'); eauto.
    { eapply ktid_ninit; eauto. }
    assert (eindex st < eindex st') as LTST.
    { edestruct LBL_STEP.
      eapply ilbl_step_eindex_lt; eauto. }
    assert (eindex st' <= eindex st'') as LTST'.
    { eapply eindex_steps_mon; eauto. }
    assert (acts_set (ProgToExecution.G st')
                     (ThreadEvent (ktid S k) xindex))
      as XINDST'.
    { red. apply acts_clos; auto. omega. }
    exists (ThreadEvent (ES.cont_thread S k) xindex).
    eapply steps_dont_add_rmw; eauto.
    apply seq_eqv_l. split; auto.
    eapply dcertRMW.
    { apply SRCC. }
    apply seq_eqv_l. splits; auto.
    all: apply acts_clos; auto.
    all: omega.
  Qed.

    Lemma simrel_cert_forwarding_rmw_cov_in_kE lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    Grmw ⨾ ⦗C' ∩₁ e2a S □₁ kE S k'⦘ ⊆ e2a S □ Srmw S ⨾ ⦗ kE S k' ⦘.
  Proof.
    assert (Wf G) as WFG by apply SRCC.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC.
    { apply SRCC. }
    assert (simrel_cont (stable_prog_to_prog prog) S)
      as SRCONT.
    { apply SRCC. }
    assert (simrel_e2a S G sc) as SRE2A.
    { apply SRCC. }
    assert (ES.cont_adjacent S k k' e e') as ADJ.
    { apply FRWD. }
    erewrite ES.cont_adjacent_sb_dom; eauto.
    rewrite !set_collect_union.
    rewrite !set_inter_union_r.
    rewrite !id_union.
    rewrite !seq_union_r, !collect_rel_union.
    repeat apply union_mori.
    { apply SRCC. }
    { rewrite !seq_eqv_r.
      intros x y [RMW [Cy [y' [EQy' E2Ae]]]].
      subst y y'. exfalso.
      erewrite forwarding_e2a_e with (S := S) in RMW; eauto.
      eapply simrel_cert_lbl_step_nrwm_eindex; eauto.
      { eexists. apply FRWD. }
      basic_solver. }
    unfold eq_opt.
    destruct e' as [e'|].
    2 : basic_solver.
    rewrite !seq_eqv_r.
    intros x y [RMW [Cy [y' [EQy' E2Ae]]]].
    subst y y'.
    exists e, e'. splits; auto.
    { eapply ES.cont_adjacent_rmw; eauto. }
    eapply wf_rmw_invf; eauto.
    eapply e2a_rmw with (S := S); eauto.
    red. do 2 eexists.
    splits; eauto.
    eapply ES.cont_adjacent_rmw; eauto.
  Qed.

  Lemma simrel_cert_forwarding_contsimstate_kE_covered lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'')
        (kE_COV : e2a S ⋄₁ C' ∩₁ kE S k' ⊆₁ e2a S ⋄₁ C' ∩₁ kE S k) :
    exists kC (state : thread_st (ES.cont_thread S kC)),
      ⟪ THK   : ES.cont_thread S kC = ktid S k' ⟫ /\
      ⟪ INK   : K S (kC, thread_cont_st (ES.cont_thread S kC) state) ⟫ /\
      ⟪ INX   : ES.cont_sb_dom S kC ≡₁ e2a S ⋄₁ C' ∩₁ kE S k' ⟫ /\
      ⟪ KINEQ : kE S k' ⊆₁ e2a S ⋄₁ C' -> kC = k' ⟫ /\
      ⟪ SIMST : @sim_state G sim_normal (C' ∩₁ e2a S □₁ kE S k') (ES.cont_thread S kC) state ⟫.
  Proof.
    assert (Wf G) as WF by apply SRCC.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S)
      as SRCONT.
    { apply SRCC. }

    assert (e2a S ⋄₁ C' ∩₁ ES.cont_sb_dom S k' ≡₁
            e2a S ⋄₁ C' ∩₁ ES.cont_sb_dom S k )
      as CEQE.
    { split; auto.
      cdes FRWD.
      erewrite ES.cont_adjacent_sb_dom
        with (k := k) (k' := k'); eauto.
      basic_solver. }

    assert (C' ∩₁ e2a S □₁ ES.cont_sb_dom S k' ≡₁
            C' ∩₁ e2a S □₁ ES.cont_sb_dom S k )
      as CEQA.
    { cdes FRWD.
      erewrite ES.cont_adjacent_sb_dom
        with (k := k) (k' := k'); eauto.
      split; [|basic_solver 10].
      rewrite set_unionA, set_collect_union.
      rewrite set_inter_union_r.
      unionL; [basic_solver|].
      intros x [Cx E2Ax].
      split; auto.
      destruct E2Ax as [y [HH EQy]].
      exists y; split; auto.
      apply CEQE.
      split; [red; congruence|].
      eapply ES.cont_adjacent_sb_dom
        with (k := k) (k' := k'); eauto.
      generalize HH. basic_solver. }

    edestruct contsimstate_kE as [kC]; try apply SRCC. desc.
    exists kC, state.
    arewrite
      (ES.cont_thread S k' = ES.cont_thread S k).
    { cdes FRWD. by cdes ADJ. }

    splits; auto.
    { by rewrite INX, <- CEQE. }
    { intros AA. exfalso.
      eapply ES.cont_adjacent_nsb_dom_e
        with (k := k); eauto.
      1-2: cdes FRWD; eauto.
      apply CEQE.
      assert (ES.cont_sb_dom S k' e) as kSBe.
      { cdes FRWD.
        eapply ES.cont_adjacent_sb_dom
          with (k := k) (k' := k'); eauto.
        basic_solver. }
      split; auto. }
    red. splits; [|apply SIMST].
    intros idx. split; auto.
    { intros HH. eapply SIMST.
      apply CEQA. apply HH. }
    intros HH. apply CEQA.
    by apply SIMST.
  Qed.

  Lemma simrel_cert_forwarding_contsimstate_kE_covering lbl lbl' k k' e e' S
        (st st' st'': (thread_st (ktid S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'')
        (kE_nCOV : ~ (e2a S ⋄₁ C' ∩₁ kE S k' ⊆₁ e2a S ⋄₁ C' ∩₁ kE S k)) :
    exists kC (state : thread_st (ES.cont_thread S kC)),
      ⟪ THK   : ES.cont_thread S kC = ktid S k' ⟫ /\
      ⟪ INK   : K S (kC, thread_cont_st (ES.cont_thread S kC) state) ⟫ /\
      ⟪ INX   : ES.cont_sb_dom S kC ≡₁ e2a S ⋄₁ C' ∩₁ kE S k' ⟫ /\
      ⟪ KINEQ : kE S k' ⊆₁ e2a S ⋄₁ C' -> kC = k' ⟫ /\
      ⟪ SIMST : @sim_state G sim_normal (C' ∩₁ e2a S □₁ kE S k') (ES.cont_thread S kC) state ⟫.
  Proof.
    cdes FRWD.
    assert (Wf G) as WF by apply SRCC.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (simrel_cont (stable_prog_to_prog prog) S)
      as SRCONT.
    { apply SRCC. }
    assert (wf_thread_state (ktid S k) st) as WFT.
    { eapply wf_cont_state; eauto. }

    assert (C' (e2a S e)) as Ce.
    { destruct (classic (C' (e2a S e)))
        as [EE|NEE]; auto.
      exfalso. apply kE_nCOV.
      cdes FRWD.
      rewrite ES.cont_adjacent_sb_dom; eauto.
      rewrite set_unionA.
      rewrite set_inter_union_r.
      rewrite set_interC.
      unionL; [basic_solver|].
      intros x [Cx EQx].
      exfalso. apply NEE.
      destruct EQx as [HA|HB].
      { subst; done. }
      eapply sim_trav_step_rmw_covered
        with (r := e2a S e); eauto.
      { eexists. apply SRCC. }
      { apply SRCC. }
      eapply e2a_rmw; eauto.
      { eapply SRCC. }
      do 2 eexists. splits; eauto.
      cdes ADJ. apply RMWe.
      basic_solver. }

    assert
      (eq_opt e' ⊆₁ e2a S ⋄₁ C')
      as Ce'.
    { unfold eq_opt.
      intros x EQx.
      destruct e' as [e'|];
        try done; subst x.
      eapply sim_trav_step_rmw_covered
        with (r := e2a S e); eauto.
      { eexists. apply SRCC. }
      { apply SRCC. }
      eapply e2a_rmw; eauto.
      { eapply SRCC. }
      do 2 eexists. splits; eauto.
      cdes ADJ. apply RMWe.
      basic_solver. }

    assert (kE S k ⊆₁ e2a S ⋄₁ C') as kE_COV.
    { intros x kSBx.
      eapply dom_sb_covered; eauto.
      { eapply sim_trav_step_coherence;
          [eexists|]; apply SRCC. }
      exists (e2a S e).
      apply seq_eqv_r.
      split; auto.
      eapply e2a_sb; eauto.
      { apply SRCC. }
      do 2 eexists; splits; eauto.
      eapply ES.cont_adjacent_sb_e; eauto.
      basic_solver. }

    exists k', st'.
    splits; auto.

    { cdes ADJ. by rewrite <- kEQTID. }

    { erewrite ES.cont_adjacent_sb_dom; eauto.
      split; [|basic_solver]. unionL.
      { intros x kSBx.
        split; [red|basic_solver].
        by eapply kE_COV. }
      all: generalize kE_COV Ce Ce'.
      all: basic_solver 20. }

    edestruct contsimstate_kE as [kC];
      try apply SRCC. desc.
    assert (kC = k); [|subst kC].
    { by apply KINEQ. }
    assert (state = st); [|subst state].
    { pose proof (ES.unique_K WFS _ _ Kk INK eq_refl) as HH.
      simpls. inv HH. }
    cdes SIMST.
    red; splits.
    all: cdes ADJ; rewrite <- kEQTID.

    { assert (wf_thread_state (ktid S k) st') as WFT'.
      { eapply wf_thread_state_lbl_step; eauto.
        eexists; apply STEP. }

      ins. split.
      { intros [Cx kSBx].
        eapply e2a_kE_eindex
          with (S := S) (k := k'); eauto.
        { by rewrite <- kEQTID. }
        destruct kSBx as [x [kSBx E2Ax]].
        unfold e2a in E2Ax.
        destruct
          (excluded_middle_informative ((Stid S) x = tid_init))
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
        with (S := S) (k := k') in ACTS; eauto.
      destruct ACTS as [x [[kSBx nINITx] E2Ax]].
      split; [|basic_solver].
      2 : { by rewrite <- kEQTID. }
      eapply ES.cont_adjacent_sb_dom in kSBx; eauto.
      rewrite <- E2Ax.
      destruct kSBx as [[HA | HB] | HC]; auto.
      { eapply kE_COV; eauto. }
      { by subst x. }
      by eapply Ce'. }

    cdes SIMST1.
    exists state'.
    red; splits; auto.

    (* TODO: make a lemma in `simrel_cert` *)
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
    { exfalso. red in AA. desc.
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

    rewrite LBL.
    erewrite simrel_cert_forwarding_kE_lab; eauto.
    2 : { split; [eapply ES.cont_adjacent_sb_dom; basic_solver|].
          eapply ES.cont_adjacent_ninit_e; eauto. }

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

    unfold compose.
    (* TODO: make a lemma *)
    arewrite
      (lab (ProgToExecution.G st'') (e2a S e) = certLab G st'' (e2a S e)).
    { unfold certLab.
      rewrite restr_fun_fst; auto.
      eapply steps_preserve_E.
      { eapply wf_thread_state_lbl_step.
        { apply WFT. }
        eexists; apply STEP. }
      { eapply lbl_steps_in_steps; eauto. }
      erewrite forwarding_e2a_e; eauto.
      edestruct ilbl_step_acts_set
        with (state0 := st) (state' := st'); eauto.
      desc. generalize ACTS. basic_solver. }

    erewrite cslab; eauto;
      [| apply SRCC | by eapply C_in_D].

    erewrite forwarding_e2a_e; eauto.

    erewrite ilbl_step_eindex_lbl
      with (st := st); eauto.

    erewrite <- steps_preserve_lab
      with (state' := state'); eauto.
    { erewrite <- tr_lab; eauto. }
    unfold tid. eapply lbl_steps_in_steps; eauto.
  Qed.

  Lemma simrel_cert_forwarding lbl lbl' k k' e e' S
        (st st' st'': thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (FRWD : forwarding S lbl lbl' k k' e e' st st')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    simrel_cert prog S G sc TC TC' X T k' st' st''.
  Proof.
    set (HH := FRWD).
    unfold forwarding in HH. desc.
    assert (ktid S k = ktid S k') as kEQTID.
    { by apply ADJ. }
    constructor; auto.
    all: try (by try rewrite <- kEQTID; apply SRCC).
    (* cstate : simrel_cstate S k' st' st'' *)
    { constructor.
      { eapply cstate_stable, SRCC. }
      { red. exists st'. splits; eauto.
          by rewrite <- kEQTID. }
        by rewrite <- kEQTID. }
    (* ex_ktid_cov : X ∩₁ STid ktid' ∩₁ e2a ⋄₁ C ⊆₁ kE' *)
    { eapply simrel_cert_forwarding_ex_ktid_cov; eauto. }
    (* cov_in_ex : e2a ⋄₁ C ∩₁ kE' ⊆₁ X *)
    { eapply simrel_cert_forwarding_cov_in_ex; eauto. }
    (* kcond : ... *)
    { left; splits.
      { eapply simrel_cert_forwarding_klast_ex; eauto. }
      eapply simrel_cert_forwarding_kE_sb_cov_iss; eauto. }
    (* kE_lab : eq_dom (kE' \₁ SEinit) Slab (certG.(lab) ∘ e2a) *)
    { eapply simrel_cert_forwarding_kE_lab; eauto. }
    (* jf_in_cert_rf : e2a □ (Sjf ⨾ ⦗kE'⦘) ⊆ cert_rf G sc TC' ktid' *)
    { eapply simrel_cert_forwarding_jf_in_cert_rf; eauto. }
    (* icf_ex_ktid_in_co : e2a □ (Sjf ⨾ ⦗set_compl kE'⦘ ⨾ Sicf ⨾ ⦗X ∩₁ STid ktid⦘ ⨾ Sjf⁻¹) ⊆ Gco *)
    { eapply simrel_cert_forwarding_icf_ex_ktid_in_co; eauto. }
    (* icf_kE_in_co : e2a □ (Sjf ⨾ Sicf ⨾ ⦗kE'⦘ ⨾ Sjf⁻¹) ⊆ Gco *)
    { eapply simrel_cert_forwarding_icf_kE_in_co; eauto. }
    (* ex_cont_iss : X ∩₁ e2a ⋄₁ (contE' ∩₁ I) ⊆₁ dom_rel (Sew ⨾ ⦗ kE' ⦘) *)
    { eapply simrel_cert_forwarding_ex_cont_iss; eauto. }
    (* kE_iss : kE' ∩₁ e2a ⋄₁ I ⊆₁ dom_rel (Sew ⨾ ⦗ X ⦘) *)
    { eapply simrel_cert_forwarding_kE_iss; eauto. }
    (* e2a_co_kE_iss : e2a □ (Sco ⨾ ⦗kE'⦘) ⊆ Gco *)
    { eapply simrel_cert_forwarding_e2a_co_kE; eauto. }
    (* e2a_co_ex_ktid : e2a □ (Sco ⨾ ⦗X \₁ e2a ⋄₁ contE'⦘) ⊆ Gco  *)
    { cdes ADJ. rewrite <- kEQTID.
      erewrite set_minus_mori; [|edone|red].
      { eapply e2a_co_ex_ktid; eauto. }
      erewrite ilbl_step_acts_set_mon; eauto.
      eapply wf_cont_state; eauto. }
    (* rmw_cov_in_kE : Grmw ⨾ ⦗C' ∩₁ e2a □₁ kE'⦘ ⊆ e2a □ Srmw ⨾ ⦗kE'⦘ *)
    { eapply simrel_cert_forwarding_rmw_cov_in_kE; eauto. }

    destruct
      (classic ((e2a S ⋄₁ C' ∩₁ kE S k' ⊆₁ e2a S ⋄₁ C' ∩₁ kE S k))).
    { eapply simrel_cert_forwarding_contsimstate_kE_covered; eauto. }
    eapply simrel_cert_forwarding_contsimstate_kE_covering; eauto.
  Qed.

  Lemma simrel_cert_cont_icf_dom_forwarding x k S
        (st st': thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st')
        (kICFx : ES.cont_icf_dom S k x)
        (JFx : e2a S □ Sjf S ⨾ ⦗eq x⦘ ⊆ cert_rf G sc TC') :
    exists x' ll ll' k'' st'',
      forwarding S ll ll' k k'' x x' st st''.
  Proof.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (simrel_cont (stable_prog_to_prog prog) S)
      as SRCONT.
    { apply SRCC. }

    edestruct cstate_cont
      as [s [EQs KK]]; [apply SRCC|].
    red in EQs, KK. subst s.
    edestruct ES.cont_icf_dom_cont_adjacent
      with (S := S) (k := k) (e := x)
      as [k''' [x' ADJ]]; eauto.
    edestruct simrel_cont_adjacent_inK'
      with (S := S) (k := k) (k' := k''')
      as [st''' KK''']; eauto.

    edestruct ES.K_adj
      with (S := S) (k := k) (k' := k''') (st' := st''')
      as [ll [ll' [EQll [EQll' LSTEP]]]]; eauto.
    red in EQll, EQll', LSTEP.
    exists x', ll, ll', k''', st'''.
    red; splits; auto.
  Qed.

  Lemma simrel_cert_cont_icf_dom_R lbl lbl' k k' e e' S S'
        (st st' st'': thread_st (ktid S k))
        (LBL  : lbl  = Slab S' e )
        (LBL' : lbl' = option_map (Slab S') e')
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (nFRWD : ~ exists k' st' e e', forwarding S lbl lbl' k k' e e' st st') :
    ES.cont_icf_dom S k ⊆₁ SR S.
  Proof.
    cdes CertSTEP. cdes BSTEP_.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (simrel_cont (stable_prog_to_prog prog) S)
      as SRCONT.
    { apply SRCC. }

    (* some technicalities *)
    assert (lbl0 = lbl) as EQl.
    { rewrite LBL, LAB'.
      rewrite updo_opt, upds; auto.
      unfold opt_ext in *.
      basic_solver. }
    assert (lbl'0 = lbl') as EQl'.
    { rewrite LBL', LAB'.
      unfold option_map, opt_same_ctor in *.
      destruct e' as [e'|].
      { destruct lbl'0; [|done].
        unfold upd_opt.
        by rewrite upds. }
      destruct lbl'0; done. }
    subst lbl0 lbl'0.

    intros x kICFx.

    destruct
      (classic (is_r (Slab S') e))
      as [Re|nRe].
    { assert ((Slab S □₁ ES.cont_icf_dom S k) (Slab S x))
        as HH.
      { basic_solver. }
      eapply basic_step_cont_icf_dom_same_lab_u2v
        in HH; eauto.
      unfold is_r in *.
      unfold same_label_u2v in HH.
      destruct (Slab S' e); try done.
      destruct (Slab S x); done. }

    assert (~ is_r (Slab S) x)
      as nRx.
    { intros Rx. apply nRe.
      assert ((Slab S □₁ ES.cont_icf_dom S k) (Slab S x))
        as HA.
      { basic_solver. }
      eapply basic_step_cont_icf_dom_same_lab_u2v
        in HA; eauto.
      unfold is_r in *.
      unfold same_label_u2v in HA.
      destruct (Slab S x); try done.
      destruct (Slab S' e); done. }

    exfalso.
    apply nFRWD.
    edestruct simrel_cert_cont_icf_dom_forwarding
      as [x' [ll [ll' [k''' [st''' FRWD]]]]]; eauto.
    { arewrite (eq x ⊆₁ set_compl (is_r (Slab S))).
      { basic_solver. }
      rewrite ES.jfD; auto; basic_solver. }

    exists k''', st''', x, x'.
    cdes FRWD.
    edestruct nR_ilbl_step
      with (la := lbl) as [EQll [lNone lNone']]; eauto.
    { apply STEP. }
    { intros Rlbl. apply nRe.
      rewrite LAB'.
      unfold is_r in *.
      unfold eq_opt, opt_ext in *.
      rewrite updo_opt, upds; auto.
      unfolder.
      destruct e' as [e'|];
        auto; omega. }
    red in EQll, lNone, lNone'.
    rewrite EQll.
    arewrite (lbl' = ll'); auto.
    congruence.
  Qed.

  Lemma simrel_cert_nforwarding_icf_R lbl lbl' k k' e e' S S'
        (st st' st'': thread_st (ktid S k))
        (LBL  : lbl  = Slab S' e )
        (LBL' : lbl' = option_map (Slab S') e')
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (nFRWD : ~ exists k' st' e e', forwarding S lbl lbl' k k' e e' st st') :
    dom_rel (Sicf S') ⊆₁ SR S'.
  Proof.
    cdes CertSTEP. cdes BSTEP_.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (simrel_cont (stable_prog_to_prog prog) S)
      as SRCONT.
    { apply SRCC. }

    erewrite basic_step_icf; eauto.
    rewrite dom_union. unionL.
    { arewrite (dom_rel (Sicf S) ⊆₁ SE S ∩₁ SR S).
      { apply set_subset_inter_r. split.
        { rewrite ES.icfE; auto. basic_solver. }
        eapply icf_R; apply SRCC. }
      (* TODO: introduce lemma *)
      intros x [Ex Rx].
      unfold is_r.
      erewrite basic_step_lab_eq_dom; eauto. }

    unfold icf_delta.
    rewrite csE, dom_union.
    unfold transp.
    rewrite set_subset_union_l; split.

    { rewrite dom_cross.
      2 : { intros HH; eapply HH; edone. }
      rewrite <- set_interK
        with (s := ES.cont_icf_dom S k).
      rewrite ES.cont_icf_domE at 1; auto.
      erewrite simrel_cert_cont_icf_dom_R; eauto.
      (* TODO: introduce lemma *)
      intros x [Ex Rx].
      unfold is_r.
      erewrite basic_step_lab_eq_dom; eauto. }

    intros x [y [kICFy EQx]]. subst x.
    destruct
      (classic (is_r (Slab S') e))
      as [Re|nRe]; auto.
    exfalso. apply nRe.
    assert ((Slab S □₁ ES.cont_icf_dom S k) (Slab S y))
      as HH.
    { basic_solver. }
    eapply basic_step_cont_icf_dom_same_lab_u2v
      in HH; eauto.
    eapply simrel_cert_cont_icf_dom_R
      in kICFy; eauto.
    unfold is_r in *.
    unfold same_label_u2v in HH.
    destruct (Slab S y); try done.
    destruct (Slab S' e); done.
  Qed.

  (* TODO: move to more suitable place *)
  Lemma same_label_u2v_same_val lbl lbl'
        (SAMEU2V : same_label_u2v lbl lbl')
        (SAMEVAL : val id lbl = val id lbl') :
    lbl = lbl'.
  Proof.
    unfold same_label_u2v, val, id in *.
    destruct lbl; destruct lbl'; desf.
  Qed.

  Lemma simrel_cert_nforwarding_icf_jf lbl lbl' k k' e e' S S'
        (st st' st'': thread_st (ktid S k))
        (LBL  : lbl  = Slab S' e )
        (LBL' : lbl' = option_map (Slab S') e')
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'')
        (nFRWD : ~ exists k' st' e e', forwarding S lbl lbl' k k' e e' st st') :
    irreflexive (Sjf S' ⨾ Sicf S' ⨾ (Sjf S')⁻¹ ⨾ Sew S').
  Proof.
    cdes CertSTEP. cdes BSTEP_.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (ES.Wf S') as WFS'.
    { eapply simrel_cert_step_wf; eauto. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (simrel_cont (stable_prog_to_prog prog) S)
      as SRCONT.
    { apply SRCC. }
    assert (simrel_e2a S G sc) as SRE2A.
    { apply SRCC. }
    assert (step_ e e' S S') as STEP_.
    { eapply simrel_cert_step_step_; eauto. }

    (* some technicalities *)
    assert (lbl0 = lbl) as EQl.
    { rewrite LBL, LAB'.
      rewrite updo_opt, upds; auto.
      unfold opt_ext in *.
      basic_solver. }
    assert (lbl'0 = lbl') as EQl'.
    { rewrite LBL', LAB'.
      unfold option_map, opt_same_ctor in *.
      destruct e' as [e'|].
      { destruct lbl'0; [|done].
        unfold upd_opt.
          by rewrite upds. }
      destruct lbl'0; done. }
    subst lbl0 lbl'0.

    eapply step_icf_jf_irr; eauto. split.
    { eapply icf_jf. apply SRCC. }

    rewrite !seq_eqv_r.
    intros x [[y [JF' EQy]] HH]. subst y.
    destruct HH as [z [y [EW [JF kICFy]]]].
    red.

    apply nFRWD.
    edestruct simrel_cert_cont_icf_dom_forwarding
      as [z' [ll [ll' [k''' [st''' FRWD]]]]]; eauto.
    { rewrite seq_eqv_r.
      intros a b [a' [b' [[JF'' EQb'] [EQa EQb]]]].
      subst a b b'.
      assert (a' = y) as EQa'.
      { eapply ES.jff with (S := S); eauto. }
      subst a'.
      arewrite (e2a S y = e2a S x).
      { erewrite e2a_ew; eauto. basic_solver 10. }
      arewrite (e2a S x = e2a S' x).
      { symmetry. eapply basic_step_e2a_eq_dom; eauto.
        apply ES.ewE in EW; auto.
        generalize EW. basic_solver. }
      arewrite (e2a S z = e2a S' e).
      { erewrite basic_step_e2a_cont_icf_dom
          with (S := S) (e := e); eauto.
        basic_solver. }

      assert (is_r (Slab S') e) as Re.
      { apply ES.jfD in JF'; auto.
        generalize JF'. basic_solver. }
      unfold_cert_step_ CertSTEP_.
      1,3: try cdes AEW; type_solver.
      all: cdes AJF.
      all: arewrite (x = w); auto.
      all: apply JF'0 in JF'.
      all: unfold jf_delta, singl_rel in JF'.
      all: destruct JF' as [JF'|JF'].
      2,4: basic_solver.
      all: exfalso; eapply basic_step_acts_set_ne; eauto.
      all: apply ES.jfE in JF'; auto.
      all: generalize JF'; basic_solver. }

    exists k''', st''', z, z'.
    cdes FRWD.
    assert (lbl = ll) as EQLab.
    { eapply same_label_u2v_same_val.
      { eapply same_label_u2v_ilbl_step.
        { apply STEP. }
        apply STEP0. }
      arewrite (val id lbl = val (Slab S') e).
      { basic_solver. }
      arewrite (val id ll = val (Slab S) z).
      { basic_solver. }
      arewrite (val (Slab S') e = val (Slab S') x).
      { erewrite <- ES.jfv; eauto. }
      arewrite (val (Slab S') x = val (Slab S) x).
      { unfold val.
        erewrite basic_step_lab_eq_dom; eauto.
        apply ES.ewE in EW; auto.
        generalize EW. basic_solver. }
      erewrite ES.ewv.
      2-3: eauto.
      erewrite ES.jfv; eauto. }

    assert (lbl' = ll') as EQLab'.
    { eapply same_label_fst_ilbl_step.
      { eapply STEP. }
      rewrite EQLab.
      eapply STEP0. }

    assert (st' = st''') as EQst.
    { eapply unique_ilbl_step.
      { eapply STEP. }
      rewrite EQLab, EQLab'.
      apply STEP0. }
    subst st'''.
    by rewrite EQLab, EQLab'.
  Qed.

  Lemma same_jf_icf_kE_in_co k k' e e' S S'
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (BSTEP_ : basic_step_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S')
        (JF' : Sjf S' ≡ Sjf S) :
    e2a S' □ (Sjf S' ⨾ Sicf S' ⨾ ⦗kE S' k'⦘ ⨾ (Sjf S')⁻¹) ⊆ Gco.
  Proof.
    assert (Wf G) as WFG.
    { apply SRCC. }
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (@es_consistent S Weakestmo) as CONS.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC.
    { apply SRCC. }
    assert (simrel_cont (stable_prog_to_prog prog) S)
      as SRCONT.
    { apply SRCC. }
    assert (simrel_e2a S G sc) as SRE2A.
    { apply SRCC. }
    assert (simrel prog S G sc TC X (T \₁ eq (ktid S k))) as SR_.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor. eauto. }

    rewrite JF'.
    arewrite (⦗kE S' k'⦘ ⨾ (Sjf S)⁻¹ ⊆ ⦗kE S k⦘ ⨾ (Sjf S)⁻¹).
    { erewrite basic_step_cont_sb_dom'; eauto.
      cdes BSTEP_. step_solver. }
    arewrite
      (Sjf S ⨾ Sicf S' ⨾ ⦗kE S k⦘ ⊆ Sjf S ⨾ Sicf S ⨾ ⦗kE S k⦘).
    { cdes BSTEP_.
      rewrite <- seq_eqvK
        with (dom := kE S k) at 1.
      erewrite ES.cont_sb_domE at 1; eauto.
      rewrite ES.jfE; auto.
      rewrite !seqA.
      arewrite (⦗SE S⦘ ⨾ Sicf S' ⨾ ⦗SE S⦘ ≡ Sicf S).
      { rewrite <- restr_relE.
        eapply basic_step_icf_restr; eauto. }
      rewrite ES.jfE; auto.
      basic_solver 10. }
    erewrite basic_step_e2a_collect_rel_eq_dom; eauto.
    { apply SRCC. }
    rewrite ES.jfE; auto.
    basic_solver 20.
  Qed.

  Lemma sim_add_jf_nforwarding_jf_icf_dom_w_in_co w lbl lbl' k k' e e' S S'
        (st st' st'' : thread_st (ES.cont_thread S k))
        (LBL  : lbl  = Slab S' e )
        (LBL' : lbl' = option_map (Slab S') e')
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (BSTEP_ : basic_step_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S')
        (SAJF : sim_add_jf G sc TC' X k w e S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'')
        (nFRWD : ~ exists k' st' e e', forwarding S lbl lbl' k k' e e' st st') :
    e2a S □ Sjf S ⨾ ES.cont_icf_dom S k × eq w ⊆ Gco.
  Proof.
    assert (Wf G) as WFG.
    { apply SRCC. }
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (@es_consistent S Weakestmo) as CONS.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC.
    { apply SRCC. }
    assert (simrel_cont (stable_prog_to_prog prog) S)
      as SRCONT.
    { apply SRCC. }
    assert (simrel_e2a S G sc) as SRE2A.
    { apply SRCC. }
    assert (simrel prog S G sc TC X (T \₁ eq (ktid S k))) as SR_.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor. eauto. }
    assert (add_jf w e S S') as AJF.
    { eapply weaken_sim_add_jf; eauto. }
    cdes SAJF. cdes BSTEP_.

    (* some technicalities *)
    assert (lbl0 = lbl) as EQl.
    { rewrite LBL, LAB'.
      rewrite updo_opt, upds; auto.
      unfold opt_ext in *.
      basic_solver. }
    assert (lbl'0 = lbl') as EQl'.
    { rewrite LBL', LAB'.
      unfold option_map, opt_same_ctor in *.
      destruct e' as [e'|].
      { destruct lbl'0; [|done].
        unfold upd_opt.
          by rewrite upds. }
      destruct lbl'0; done. }
    subst lbl0 lbl'0.

    intros x' y' [x [z [HH [EQx' EQy']]]].
    destruct HH as [y [JF [kICFy EQz]]].
    subst x' y' z.
    set (kICFy' := kICFy).
    unfold ES.cont_icf_dom in kICFy'.
    destruct kICFy' as [z HH].
    apply seq_eqv_lr in HH.
    destruct HH as [kLASTz [IMMSB TIDy]].
    edestruct kcond; eauto; desc.
    2 : { exfalso. eapply klast_sb_max; eauto. apply IMMSB. }
    assert (CsbI G TC (e2a S y)) as CsbIy.
    { eapply kE_sb_cov_iss.
      apply ES.cont_last_in_cont_sb in kLASTz; auto.
      generalize IMMSB. unfold immediate.
      basic_solver 10. }
    eapply ex_cov_iss in CsbIy; eauto.
    destruct CsbIy as [y' [Xy' E2Ay']].

    assert (SEninit S y) as ENINITy.
    { eapply ES.cont_icf_domEnint; eauto. }
    assert (SE S y) as Ey.
    { apply ENINITy. }
    assert (SR S y) as Ry.
    { apply ES.jfD in JF; auto.
      generalize JF. basic_solver. }

    assert (SE S y') as Ey'.
    { eapply Execution.ex_inE; eauto. }
    assert (SR S y') as Ry'.
    { eapply same_lab_u2v_dom_is_r.
      { eapply e2a_lab. apply SRCC. }
      split; auto.
      unfold is_r, compose.
      rewrite E2Ay'.
      fold (compose Glab (e2a S) y).
      fold (is_r (Glab ∘ e2a S) y).
      eapply same_lab_u2v_dom_is_r.
      { eapply same_lab_u2v_dom_comm.
        eapply e2a_lab. apply SRCC. }
      split; auto. }
    assert (SEninit S y') as ENINITy'.
    { split; auto.
      intros INITy'.
      apply ES.acts_init_set_inW in INITy'; auto.
      type_solver. }

    set (E2Ay'' := E2Ay').
    do 2 erewrite e2a_ninit in E2Ay''; auto.
    inversion E2Ay'' as [[EQTID EQSEQN]].
    clear E2Ay''.

    edestruct Execution.ex_rf_compl
      as [x' HH]; eauto.
    { basic_solver. }
    apply seq_eqv_l in HH.
    destruct HH as [Xx' RF].
    assert (cert_rf G sc TC (e2a S x') (e2a S y'))
      as CertRF'.
    { eapply rf_ex_in_cert_rf; eauto. basic_solver 10. }
    assert (e2a S' e = e2a S y') as EQE2Ae.
    { eapply basic_step_e2a_cont_icf_dom; eauto. basic_solver 10. }
    assert (e2a S w = e2a S' w) as EQE2Aw.
    { symmetry. erewrite basic_step_e2a_eq_dom; eauto. by cdes AJF. }
    assert (Gco^? (e2a S x') (e2a S w)) as CO.
    { eapply sim_trav_step_cert_rf_co; eauto.
      1-3: try eexists; apply SRCC.
      eexists; split; eauto; red; congruence. }

    set (HH := E2Ay').
    apply e2a_eq_in_cf in HH; auto.
    destruct HH as [EQ|CF].

    { subst y'.
      assert (Sew S x x') as EW.
      { eapply ES.rf_trf_in_ew; auto.
        unfolder; eexists; splits; eauto.
        apply ES.jf_in_rf; auto. }
      assert (e2a S x = e2a S x') as EQE2Ax'.
      { eapply e2a_ew; eauto. basic_solver 10. }
      rewrite EQE2Ax'.
      destruct CO as [EQ|CO]; auto.

      exfalso. apply nFRWD.
      edestruct simrel_cert_cont_icf_dom_forwarding
        as [y' [ll [ll' [k''' [st''' FRWD]]]]]; eauto.
      { intros a' b' [a [b [HH [EQa' EQb']]]].
        apply seq_eqv_r in HH.
        destruct HH as [JF'' EQb].
        subst a' b' b.
        rewrite <- EQE2Ae.
        arewrite (a = x); [|congruence].
        eapply ES.jff; eauto. }

      cdes FRWD.
      clear CertRF0.
      rename STEP0 into LSTEP.
      rename LBL0 into LL.
      rename LBL'0 into LL'.

      exists k''', st''', y, y'.
      assert (lbl = ll) as EQLab.
      { eapply same_label_u2v_same_val.
        { eapply same_label_u2v_ilbl_step; eauto.
          apply STEP. }
        arewrite (val id lbl = val (Slab S') e).
        { basic_solver. }
        arewrite (val id ll = val (Slab S) y).
        { basic_solver. }
        arewrite (val (Slab S') e = val (Slab S) w).
        { cdes AJF. rewrite <- VAL. unfold val.
          erewrite basic_step_lab_eq_dom; eauto. }
        arewrite (val (Slab S) y = val (Slab S) x').
        { symmetry. apply ES.rfv; auto. }
        unfold val.
        arewrite (Slab S x' = Slab S w); auto.
        apply ES.rfi_union_rfe in RF.
        destruct RF as [RFI | RFE].
        { assert (SE S x') as Ex'.
          { eapply Execution.ex_inE; eauto. }
          destruct RFI as [RF SB].
          apply e2a_eq_in_cf in EQ;
            try apply AJF; auto.
          destruct EQ as [EQ|CF]; auto.
          assert (SEninit S x') as nINITx'.
          { apply ES.cfEninit in CF; auto.
            generalize CF. basic_solver. }
          cdes AJF.
          exfalso. apply nCF.
          assert (dom_rel (Ssb S ⨾ ⦗ES.cont_icf_dom S k⦘) x')
            as SBkICFx'.
          { basic_solver 10. }
          eapply basic_step_sb_cont_icf_cont_sb_e
            in SBkICFx'; eauto.
          assert (ES.cont_cf_dom S k w)
            as kCFw.
          { eapply ES.cont_cf_cont_sb; eauto.
            unfolder; splits; auto.
            { arewrite (Stid S w = Stid S x').
              { symmetry. apply ES.cf_same_tid; auto. }
              arewrite (Stid S x' = Stid S y); auto.
              edestruct ES.Tid_sb_prcl
                as [INITx' | TIDx']; eauto.
              { basic_solver 10. }
              unfold ES.acts_ninit_set in nINITx'.
              exfalso. by apply nINITx'. }
            intros kSBw.
            eapply ES.cont_sb_cf_free
              with (k := k); eauto.
            apply seq_eqv_lr; splits.
            2,3: eauto.
            destruct SBkICFx' as [z' HH].
            eapply basic_step_sbe in HH; eauto.
            by destruct HH as [AA _]. }

          eapply basic_step_cf; eauto.
          unfold cf_delta.
          basic_solver 10. }

        assert (SEninit S x') as nINITx.
        { eapply rfe_dom_ninit; eauto. basic_solver. }
        assert (Stid S x' <> ktid S k) as nTIDx'.
        { eapply rfe_nsame_tid in RFE; eauto. }
        assert (I (e2a S x')) as Ix.
        { eapply rfe_iss; eauto. basic_solver. }
        arewrite (Slab S x' = Glab (e2a S x')).
        { eapply ex_cov_iss_lab; eauto. basic_solver. }
        arewrite (Slab S w = Glab (e2a S w)); [|congruence].
        eapply ex_cov_iss_lab; eauto.
        edestruct sim_add_jf_iss_sb_w
          as [HH | kSBw]; eauto.
        { generalize HH. basic_solver. }
        exfalso.
        eapply ES.cont_sb_tid in kSBw; eauto.
        destruct kSBw as [INITw | TIDw].
        { erewrite e2a_ninit, e2a_init
            in EQ; auto; congruence. }
        assert (SEninit S w) as nINITw.
        { split; [apply AJF|].
          intros [_ INITw].
          eapply ktid_ninit; eauto.
          congruence. }
        do 2 erewrite e2a_ninit in EQ; auto.
        congruence. }

      assert (lbl' = ll') as EQLab'.
      { eapply same_label_fst_ilbl_step.
        { eapply STEP. }
        rewrite EQLab.
        eapply LSTEP. }

      by rewrite EQLab, EQLab'. }

    apply ES.cf_sym in CF; auto.
    assert (Sicf S y y') as ICF.
    { split; auto.
      eexists; splits; eauto.
      { apply immediate_transp with (r := Ssb S); red; eauto. }
      eapply ES.seqn_eq_imm_sb; eauto.
      intros CF'. eapply Execution.ex_ncf; eauto.
      apply seq_eqv_lr; splits; [|apply CF'|]; eauto. }

    assert (Gco (e2a S x) (e2a S x')) as CO'.
    { destruct RF as [[x'' [EW JF'']] _].
      arewrite (e2a S x' = e2a S x'').
      { eapply e2a_ew; eauto. basic_solver 10. }
      eapply icf_ex_ktid_in_co; eauto.
      do 2 eexists; splits; eauto.
      exists y; splits; auto.
      apply seq_eqv_l. split.
      { intros kSBy.
        eapply ES.cont_sb_cont_icf_inter_false; eauto.
        basic_solver. }
      exists y'; splits; auto.
      apply seq_eqv_l. split; [|done].
      split; auto; congruence. }
    destruct CO as [EQ|CO]; [congruence|].
    eapply co_trans; eauto.

  Qed.

  Lemma sim_add_jf_nforwarding_icf_kE_in_co w lbl lbl' k k' e e' S S'
        (st st' st'' : thread_st (ES.cont_thread S k))
        (LBL  : lbl  = Slab S' e )
        (LBL' : lbl' = option_map (Slab S') e')
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (BSTEP_ : basic_step_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S')
        (SAJF : sim_add_jf G sc TC' X k w e S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'')
        (nFRWD : ~ exists k' st' e e', forwarding S lbl lbl' k k' e e' st st') :
    e2a S' □ (Sjf S' ⨾ Sicf S' ⨾ ⦗kE S' k'⦘ ⨾ (Sjf S')⁻¹) ⊆ Gco.
  Proof.
    assert (ES.Wf S) as WF.
    { apply SRCC. }
    assert (simrel prog S G sc TC X (T \₁ eq (ktid S k))) as SR_.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor. eauto. }
    assert (add_jf w e S S') as AJF.
    { eapply weaken_sim_add_jf; eauto. }
    cdes BSTEP_; cdes SAJF.
    erewrite basic_step_cont_sb_dom'; eauto.
    rewrite !id_union, !seq_union_l, !seq_union_r.
    arewrite_false (Sicf S' ⨾ ⦗eq_opt e'⦘).
    { cdes BSTEP_.
      rewrite basic_step_icf; eauto.
      unfold icf_delta.
      rewrite ES.cont_icf_domE; auto.
      rewrite ES.icfE; auto.
      step_solver. }
    relsf.
    rewrite basic_step_icf; eauto.
    rewrite !seq_union_l, !seq_union_r.
    rewrite !collect_rel_union.
    unionL.

    { arewrite (Sjf S' ⨾ Sicf S ⊆ Sjf S ⨾ Sicf S).
      { rewrite ES.icfE; auto.
        rewrite <- seqA with (r1 := Sjf S').
        rewrite add_jf_jfE; eauto.
        rewrite ES.jfE; auto.
        basic_solver 10. }
      arewrite (⦗kE S k⦘ ⨾ (Sjf S')⁻¹ ⊆ ⦗kE S k⦘ ⨾ (Sjf S)⁻¹).
      { rewrite !seq_eqv_l.
        unfold transp.
        intros x y [kSBx JF].
        splits; auto.
        eapply add_jf_jfE; eauto.
        apply seq_eqv_r.
        splits; auto.
        eapply ES.cont_sb_domE; eauto. }
      erewrite basic_step_e2a_collect_rel_eq_dom;
        eauto; [apply SRCC|].
      rewrite ES.jfE; auto.
      basic_solver 20. }

    { arewrite_false (icf_delta S k e ⨾ ⦗ES.cont_sb_dom S k⦘);
        [|basic_solver].
      unfold icf_delta.
      rewrite csE, transp_cross.
      rewrite seq_union_l.
      unionL.
      { step_solver. }
      rewrite <- cross_inter_r.
      rewrite set_interC.
      erewrite ES.cont_sb_cont_icf_inter_false; eauto.
      basic_solver. }

    { arewrite_false (Sicf S ⨾ ⦗eq e⦘).
      { rewrite ES.icfE; auto. step_solver. }
      basic_solver. }

    unfold icf_delta.
    rewrite csE, transp_cross.
    rewrite !seq_union_l, !seq_union_r.
    rewrite collect_rel_union.
    arewrite_false (eq e × ES.cont_icf_dom S k ⨾ ⦗eq e⦘).
    { rewrite ES.cont_icf_domE; auto. step_solver. }
    relsf.

    arewrite (⦗eq e⦘ ⨾ (Sjf S')⁻¹ ⊆ eq e × eq w).
    { rewrite JF'. step_solver. }
    rewrite seq_cross_eq.
    rewrite JF'.
    rewrite seq_union_l.
    arewrite_false (jf_delta w e ⨾ ES.cont_icf_dom S k × eq w).
    { unfold jf_delta.
      rewrite ES.cont_icf_domE; auto.
      step_solver. }
    rewrite union_false_r.
    erewrite basic_step_e2a_collect_rel_eq_dom; eauto.
    2 : { rewrite ES.jfE; auto.
          cdes AJF. basic_solver 10. }

    eapply sim_add_jf_nforwarding_jf_icf_dom_w_in_co; eauto.

  Qed.

  Lemma simrel_cert_nforwarding_icf_kE_in_co lbl lbl' k k' e e' S S'
        (st st' st'': thread_st (ktid S k))
        (LBL  : lbl  = Slab S' e )
        (LBL' : lbl' = option_map (Slab S') e')
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (CertSTEP : cert_step G sc TC TC' X k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'')
        (nFRWD : ~ exists k' st' e e', forwarding S lbl lbl' k k' e e' st st') :
    e2a S' □ (Sjf S' ⨾ Sicf S' ⨾ ⦗kE S' k'⦘ ⨾ (Sjf S')⁻¹) ⊆ Gco.
  Proof.
    unfold_cert_step CertSTEP.
    1,3: eapply same_jf_icf_kE_in_co; eauto.
    all: eapply sim_add_jf_nforwarding_icf_kE_in_co; eauto.
  Qed.

End SimRelCertForwarding.
