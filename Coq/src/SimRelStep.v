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
Require Import BasicStep.
Require Import Step.
Require Import StepWf.
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
Require Import SimRelCertStep.
Require Import SimRelCertStepCoh.
Require Import ProgES.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelStep.

  Variable prog : Prog.t.
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

  Lemma simrel_cert_graph_start thread S 
        (SRC : simrel prog S G sc TC X) 
        (TC_STEP : isim_trav_step G sc thread TC TC') : 
    exists k st st',
      ⟪ kTID : thread = ktid S k ⟫ /\
      ⟪ XkTIDCOV : kE S k ≡₁ X ∩₁ Stid_ S (ktid S k) ∩₁ e2a S ⋄₁ C ⟫ /\
      ⟪ kECOV : X ∩₁ Stid_ S thread ∩₁ e2a S ⋄₁ C ⊆₁ kE S k ⟫ /\
      ⟪ CERTG : cert_graph G sc TC TC' thread st' ⟫ /\
      ⟪ CERT_ST : simrel_cstate S k st st' ⟫.
  Proof. admit. Admitted.
  
  Lemma simrel_cert_start k S 
        (st st' : thread_st (ktid S k))
        (SRC : simrel prog S G sc TC X) 
        (TC_ISTEP : isim_trav_step G sc (ktid S k) TC TC') 
        (XkTIDCOV : kE S k ≡₁ X ∩₁ Stid_ S (ktid S k) ∩₁ e2a S ⋄₁ C)
        (CERTG : cert_graph G sc TC TC' (ktid S k) st')
        (CERT_ST : simrel_cstate S k st st') :
    simrel_cert prog S G sc TC TC' X k st st'.
  Proof. 
    constructor; auto.
    { apply XkTIDCOV. }
    { intros x [kEx nINITx].
      erewrite ex_cov_iss_lab; try apply SRC.
      2 : { apply XkTIDCOV in kEx. 
            generalize kEx. basic_solver. }
      unfold Basics.compose. 
      erewrite <- cslab; eauto.
      { unfold certLab.
        erewrite restr_fun_fst; auto.
        edestruct cstate_cont as [sta HH]; 
          eauto; desf.
        eapply steps_preserve_E; eauto.
        { eapply contwf; eauto. apply SRC. }
        { apply ilbl_steps_in_steps, CERT_ST. }
        eapply e2a_kE_ninit; auto; try apply SRC.
        basic_solver. }
      red. do 4 left.
      admit. }
    arewrite (kE S k ⊆₁ X ∩₁ e2a S ⋄₁ C) at 1.
    { etransitivity; [apply XkTIDCOV|]. basic_solver. } 
    arewrite (⦗X ∩₁ e2a S ⋄₁ C⦘ ≡ 
              ⦗X ∩₁ e2a S ⋄₁ C⦘ ⨾ ⦗e2a S ⋄₁ C⦘).
    { basic_solver. }
    rewrite <- seqA, collect_rel_seqi.
    rewrite jf_cov_in_rf; [|apply SRC].
    rewrite collect_rel_eqv.
    rewrite collect_map_in_set.
    admit. 
  Admitted.

  Lemma simrel_cert_end k S 
        (st : thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st) :
    simrel prog S G sc TC' (certX S k).
  Proof. 
    constructor; [|apply SRCC].
    constructor; try apply SRCC.
    { eapply tccoh'; eauto. }
    { constructor.
      { apply SRCC. }
      { eapply sim_trav_step_rmw_covered;
          try apply SRCC.
        eexists. apply SRCC. }
      eapply sim_trav_step_rel_covered;
        try apply SRCC.
      eexists. apply SRCC. }
    { admit. }
    { econstructor; try apply SRCC.
      admit. }
    { rewrite cert_ex_certD; eauto. 
      rewrite cert_dom_cov_sb_iss; eauto. }
    all: admit.
  Admitted.

  Lemma simrel_step_helper k S
        (st st''' : thread_st (ktid S k))
        (SRC : simrel prog S G sc TC X)
        (TC_ISTEP : isim_trav_step G sc (ktid S k) TC TC')
        (XkTIDCOV : kE S k ≡₁ X ∩₁ Stid_ S (ktid S k) ∩₁ e2a S ⋄₁ C)
        (CERTG : cert_graph G sc TC TC' (ktid S k) st''')
        (CERT_ST : simrel_cstate S k st st''') 
        (LBL_STEPS : (lbl_step (ktid S k))＊ st st''') :
    (fun st' => exists k' S',
      ⟪ kTID : ktid S' k' = ktid S k ⟫ /\
      ⟪ STEPS : (step Weakestmo)＊ S S' ⟫ /\
      ⟪ SRCC  : simrel_cert prog S' G sc TC TC' X k' st' st''' ⟫) st'''.
  Proof.
    eapply clos_refl_trans_ind_step_left.
    { exists k, S. splits; auto.
      { apply rt_refl. }
      eapply simrel_cert_start; eauto. }
    { eapply LBL_STEPS. }
    intros st' st'' HH. desc.
    intros LBL_STEP LBL_STEPS'.
    edestruct simrel_cert_lbl_step
      as [k'' [S'' HH]]; 
      eauto; desc.
    { rewrite kTID. apply LBL_STEP. }
    { rewrite kTID. apply LBL_STEPS'. }
    exists k'', S''. splits; auto.
    { congruence. }
    eapply rt_trans; eauto.
    destruct ESSTEP as [EQ | ESSTEP].
    { subst. by apply rt_refl. }
    by apply rt_step.
  Qed.
  
  Lemma simrel_step S 
        (SRC : simrel prog S G sc TC X) 
        (TRAV_STEP : sim_trav_step G sc TC TC') :
    exists X' S', 
      ⟪ STEPS : (step Weakestmo)＊ S S' ⟫ /\      
      ⟪ SRC' : simrel prog S' G sc TC' X' ⟫.
  Proof. 
    unfold sim_trav_step in TRAV_STEP. desc.
    edestruct simrel_cert_graph_start
      as [k [st [st' HH]]]; 
      eauto; desc. 
    edestruct simrel_step_helper
      as [k' [S' HH]]; 
      subst; eauto; desc.
    { by destruct CERT_ST. }
    exists (certX S' k'), S'.
    splits; auto.
    eapply simrel_cert_end; eauto.
  Qed.
  
End SimRelStep.