From hahn Require Import Hahn.
From PromisingLib Require Import Language.
From imm Require Import Events Execution
     Traversal TraversalConfig SimTraversal SimTraversalProperties
     Prog ProgToExecution ProgToExecutionProperties Receptiveness
     imm_common imm_s imm_s_hb
     CertExecution2
     SubExecution CombRelations.
Require Import AuxRel.
Require Import AuxDef.
Require Import EventStructure.
Require Import BasicStep.
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
Require Import ProgES.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelCertBasicStep.

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

  Notation "'STid' S" := (fun t x => Stid S x = t) (at level 1).
  Notation "'SNTid' S" := (fun t x => Stid S x <> t) (at level 1).

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

  Notation "'certX' S" := (fun k => (X ∩₁ SNTid S (ktid S k)) ∪₁ (kE S k)) (at level 1, only parsing).

  Lemma simrel_cert_basic_step_ex_tid t k k' e e' S S' 
        (st st' st'': thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S') : 
    X ∩₁ STid S' t ≡₁ X ∩₁ STid S t.
  Proof.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor. eauto. }
    split; unfolder; intros x [AA BB]; desf; splits; auto.
    1 : symmetry.
    all: eapply basic_step_tid_eq_dom; eauto.
    all: eapply Execution.ex_inE; eauto.
    all: apply SRCC.
  Qed.

  Lemma simrel_cert_basic_step_ex_ntid t k k' e e' S S' 
        (st st' st'': thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S') : 
    X ∩₁ SNTid S' t ≡₁ X ∩₁ SNTid S  t.
  Proof.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor. eauto. }
    split; unfolder; intros x [AA BB]; desf; splits; auto.
    all: intros CC.
    all: apply BB; rewrite <- CC.
    2: symmetry.
    all: eapply basic_step_tid_eq_dom; eauto.
    all: eapply Execution.ex_inE; eauto.
    all: apply SRCC.
  Qed.

  Lemma simrel_cert_basic_step_cert_ex k k' e e' S S' 
        (st st' st'': thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S') : 
    certX S' k' ≡₁ certX S k ∪₁ eq e ∪₁ eq_opt e'.  
  Proof. 
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor. eauto. }
    simpl. do 2 rewrite set_unionA.
    apply set_union_Propere.
    { erewrite basic_step_cont_thread'; eauto.
      eapply simrel_cert_basic_step_ex_ntid; eauto. }
    rewrite <- set_unionA.
    eapply basic_step_cont_sb_dom'; eauto.
  Qed.

  Lemma simrel_cert_basic_step_cstate k k' e e' S S'
        (st st' st'': thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    simrel_cstate S' k' st' st''. 
  Proof. 
    cdes BSTEP_. 
    constructor.
    (* cstate_stable : stable_state (ES.cont_thread S' k') st'' *)
    { eapply cstate_stable. apply SRCC. }
    (* cstate_q_cont : Kstate (k', st'); *)
    { red. exists st'. split; auto. 
      eapply basic_step_cont_set; eauto.
      erewrite basic_step_cont_thread' with (S' := S'); eauto.
      subst. basic_solver. }
    (* cstate_reachable : (step (ES.cont_thread S' k'))＊ st' st'' *)
    arewrite (ES.cont_thread S' k' = ES.cont_thread S k); [|done].
    desf. simpls. rewrite TID'.
    unfold opt_ext, upd_opt. desf; rewrite upds; auto.
  Qed.

  Lemma simrel_cert_basic_step_e2a_eqr k k' e e' S S' r r' r''
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S') 
        (restrE : r ≡ ⦗ SE S ⦘ ⨾ r ⨾ ⦗ SE S ⦘)
        (rEQ : r' ≡ r) 
        (rIN : (e2a S) □ r ⊆ r'') : 
    (e2a S') □ r' ⊆ r''.
  Proof. 
    assert (basic_step e e' S S') as BSTEP.
    { econstructor. eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    rewrite rEQ, restrE, <- restr_relE. 
    rewrite collect_rel_restr_eq_dom. 
    2 : eapply basic_step_e2a_eq_dom; eauto. 
    rewrite restr_relE, <- restrE; eauto. 
  Qed.

  Lemma simrel_cert_basic_step_hb_sb_delta_dom k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (BSTEP_ : basic_step_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    dom_rel ((Shb S)^? ⨾ (sb_delta S k e e')) ⊆₁ certX S k ∪₁ eq e. 
  Proof. 
    cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    repeat autounfold with ESStepDb.
    rewrite <- cross_union_l.
    relsf. splits.
    { intros x [y [z [[EQxy | HB] [certD _]]]].
      { basic_solver. }
      left. eapply cert_ex_hb_prcl; eauto. basic_solver 10. }
    rewrite crE, seq_union_l, seq_id_l, dom_union. 
    unionL. splits.
    { basic_solver. }
    etransitivity; [| apply set_subset_empty_l]. 
    step_solver. 
  Qed.

  Lemma simrel_cert_basic_step_hb_rel_jf_sb_delta_dom k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st'')
        (BSTEP_ : basic_step_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    dom_rel ((Shb S)^? ⨾ release S ⨾ Sjf S ⨾ sb_delta S k e e') ⊆₁ certX S k. 
  Proof. 
    cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    repeat autounfold with ESStepDb.
    rewrite <- cross_union_l.
    relsf. splits.
    { rewrite <- seqA.
      intros x [y [z [HA HB]]].
      eapply hb_rel_ew_cert_ex; eauto.
      edestruct jf_kE_in_ew_cert_ex as [a Ha]; eauto.
      { generalize HB. basic_solver 10. }
      eexists. apply seqA. 
      eexists; splits; eauto. }
    etransitivity; [| apply set_subset_empty_l]. 
    step_solver. 
  Qed.

End SimRelCertBasicStep.
