Require Import Program.Basics Lia.
From hahn Require Import Hahn.
From PromisingLib Require Import Basic Language.
From imm Require Import
     AuxDef
     Events Execution
     Traversal TraversalConfig SimTraversal SimTraversalProperties
     Prog ProgToExecution ProgToExecutionProperties Receptiveness
     imm_common imm_s imm_s_hb SimState
     CertExecution2
     SubExecution CombRelations.
Require Import AuxRel.
Require Import AuxDef.
Require Import EventStructure.
Require Import Execution.
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
Require Import SimRelCertStepLemma.
Require Import ProgES.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelStep.

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

  Notation "'certX' S" := (fun k => (X ∩₁ SNTid S (ktid S k)) ∪₁ (kE S k)) (at level 1, only parsing).

  (* Definition cont_pc S X k thread :=  *)
  (*   (⟪ KREP : k = CInit thread ⟫ /\ *)
  (*    ⟪ CEMP : C ∩₁ GTid thread ≡₁ ∅ ⟫)  *)
  (*   \/ *)
  (*   (exists e, *)
  (*       ⟪ KREP : k = CEvent e ⟫ /\ *)
  (*       ⟪ Xe   : X e ⟫ /\ *)
  (*       ⟪ EPC  : pc G TC thread (e2a S e) ⟫  *)
  (*   ). *)

  Lemma simrel_cert_cont_pc S thread
        (NINITT : thread <> tid_init)
        (SRC : simrel_consistent prog S G sc TC X T)
        (TC_STEP : isim_trav_step G sc thread TC TC') :
    exists k (state : Language.state (thread_lts thread)),
      ⟪ THK : thread = ES.cont_thread S k ⟫ /\
      ⟪ INK : K S (k, thread_cont_st thread state) ⟫ /\
      ⟪ EST : state.(ProgToExecution.G).(acts_set) ≡₁
                  C ∩₁ GTid thread ⟫ /\
      ⟪ INX : ES.cont_sb_dom S k ≡₁
              SEinit S ∪₁
              X ∩₁ STid S (ES.cont_thread S k) ∩₁ e2a S ⋄₁ C ⟫ /\
      ⟪ SIMST : @sim_state G sim_normal C (ES.cont_thread S k) state ⟫.
  Proof.
    cdes SRC.
    assert (ES.Wf S) as WFS by apply SRC.
    assert (Wf G) as WF by apply SRC.
    assert (simrel_graph G TC) as SG by apply SRC.
    assert (simrel_cont (stable_prog_to_prog prog) S) as SRCONT by apply SRC.
    assert (contsimstate prog S G TC X) as CSS by apply SRC.
    pose proof TC_STEP as HH.
    eapply trstep_thread_prog in HH; try apply SRC.
    apply Basic.IdentMap.Facts.in_find_iff in HH.
    destruct (Basic.IdentMap.find thread (stable_prog_to_prog prog))
      as [lprog|] eqn:AA; desf.

    edestruct CSS as [k BB]; eauto. desf.
    do 2 eexists. splits; eauto.

    assert (wf_thread_state (ES.cont_thread S k) state) as WT.
    { eapply contwf; eauto. }

    split; unfolder.
    { intros x BB. eapply acts_rep in BB; eauto. desf. simpls.
      splits; auto. by apply SIMST. }
    intros x [BB CC].
    destruct x; simpls; desf.
    { exfalso. apply NINITT. desf. }
    apply SIMST in BB. by apply acts_clos.
  Qed.

  Lemma simrel_cert_graph_start thread S
        (NINITT : thread <> tid_init)
        (SRC : simrel_consistent prog S G sc TC X T)
        (TC_STEP : isim_trav_step G sc thread TC TC') :
    exists k st st',
      ⟪ kTID : thread = ktid S k ⟫ /\
      ⟪ XkTIDCOV : kE S k ≡₁ X ∩₁ e2a S ⋄₁ C ∩₁ (SEinit S ∪₁ STid S (ktid S k)) ⟫ /\
      ⟪ CERTG : cert_graph G sc TC' thread st' ⟫ /\
      ⟪ CERT_ST : simrel_cstate S k st st' ⟫.
  Proof.
    cdes SRC.
    assert (ES.Wf S) as WFS by apply SRC.
    assert (Wf G) as WF by apply SRC.
    assert (Execution.t S X) as EXEC by apply SRC.
    assert (simrel_e2a S G sc) as SRE2A by apply SRC.
    assert (simrel_cont (stable_prog_to_prog prog) S) as SRCONT by apply SRC.

    pose proof TC_STEP as HH.
    eapply trstep_thread_prog in HH; try apply SRC.
    apply Basic.IdentMap.Facts.in_find_iff in HH.
    destruct (Basic.IdentMap.find thread (stable_prog_to_prog prog))
      as [lprog|] eqn:AA; desf.

    edestruct simrel_cert_cont_pc as [k CONTPC]; eauto. desf.
    assert (lprog = instrs state) as UU.
    { eapply kstate_instrs; eauto. }

    edestruct cert_graph_start with (state0:=state) as [state']; eauto.
    1,2,3: by apply SRC.
    { rewrite <- UU.
      unfold stable_prog_to_prog in *.
      rewrite Basic.IdentMap.Facts.map_o in AA.
      unfold option_map in *. clear UU. desf.
      destruct s. simpls. }
    { rewrite <- UU. eapply contreach; eauto.  }
    { rewrite EST. basic_solver. }
    all: try by apply SRC.
    desc.
    do 3 eexists.
    splits; eauto.
    2: { constructor; eauto.
         { red. eexists. splits; eauto. }
         apply steps_stable_lbl_steps.
         apply seq_eqv_l. split.
         { eapply contstable; try apply SRC; eauto. }
         apply seq_eqv_r. by split. }

    rewrite INX. split.
    2: basic_solver.
    unionL.
    2: basic_solver.
    arewrite (SEinit S ⊆₁ X ∩₁ SEinit S).
    { apply set_subset_inter_r. split; [|done].
      eapply Execution.init_in_ex. apply SRC. }
    arewrite (SEinit S ⊆₁ e2a S ⋄₁ C ∩₁ SEinit S).
    { apply set_subset_inter_r. split; [|done].
      eapply init_in_map_cov; eauto. }
    basic_solver.
  Qed.

  Lemma simrel_cert_start k S
        (st st' : thread_st (ktid S k))
        (Tktid : T (ktid S k))
        (SRC : simrel_consistent prog S G sc TC X T)
        (TC_ISTEP : isim_trav_step G sc (ktid S k) TC TC')
        (XkTIDCOV : kE S k ≡₁ X ∩₁ e2a S ⋄₁ C ∩₁ (SEinit S ∪₁ STid S (ktid S k)))
        (CERTG : cert_graph G sc TC' (ktid S k) st')
        (CERT_ST : simrel_cstate S k st st') :
    simrel_cert prog S G sc TC TC' X T k st st'.
  Proof.
    assert (ES.Wf S) as WF by apply SRC.
    assert (Execution.t S X) as EXEC by apply SRC.
    assert (tc_coherent G sc TC) as TCCOH by apply SRC.
    assert (tc_coherent G sc TC') as TCCOH'.
    { eapply sim_trav_step_coherence; try apply SRC.
      red. eauto. }
    assert (Wf G) as WFG by apply SRC.
    assert (simrel prog S G sc TC X T) as SR_.
    { apply SRC. }
    assert (contsimstate prog S G TC X) as CSS by apply SRC.

    pose proof TC_ISTEP as TT.
    eapply trstep_thread_prog in TT; try apply SRC.
    apply Basic.IdentMap.Facts.in_find_iff in TT.
    destruct (Basic.IdentMap.find (ES.cont_thread S k) (stable_prog_to_prog prog))
      as [lprog|] eqn:TTN; desf.

    constructor; auto.
    { red; splits; [constructor|]; try apply SRC.
      all: ins; eapply SRC; apply Tt. }
    (* ex_ktid_cov : X ∩₁ STid ktid ∩₁ e2a ⋄₁ C ⊆₁ kE *)
    { generalize XkTIDCOV. basic_solver 20. }
    (* cov_in_ex : e2a ⋄₁ C ∩₁ kE ⊆₁ X *)
    { rewrite XkTIDCOV. basic_solver. }
    (* kcond : ... *)
    { left. splits.
      { rewrite ES.cont_last_in_cont_sb; auto.
        rewrite XkTIDCOV. basic_solver. }
      arewrite (kE S k ⊆₁ X).
      { rewrite XkTIDCOV. basic_solver. }
      erewrite ex_sb_cov_iss; eauto. }
    (* kE_lab : eq_dom (kE \₁ SEinit) Slab (certG.(lab) ∘ e2a) *)
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
        { apply lbl_steps_in_steps, CERT_ST. }
        eapply e2a_kEninit; auto; try apply SRC.
        basic_solver. }
      red. do 4 left.
      simpl in XkTIDCOV.
      apply XkTIDCOV in kEx.
      destruct kEx as [[_ Cx] _].
      eapply sim_trav_step_covered_le in Cx.
      2 : eexists; eauto.
      basic_solver. }
    (* jf_in_cert_rf : e2a □ (Sjf ⨾ ⦗kE⦘) ⊆ cert_rf G sc TC' *)
    { rewrite XkTIDCOV.
      rewrite <- seq_eqvK.
      rewrite <- seqA, collect_rel_seqi.
      arewrite (X ∩₁ e2a S ⋄₁ C ∩₁ (SEinit S ∪₁ STid S (ES.cont_thread S k)) ⊆₁
                X ∩₁ e2a S ⋄₁ C) at 1 by basic_solver.
      rewrite jf_cov_in_rf; [|by apply SRC].
      rewrite collect_rel_eqv.
      arewrite (X ∩₁ e2a S ⋄₁ C ∩₁ (SEinit S ∪₁ STid S (ES.cont_thread S k)) ≡₁
                X ∩₁ (SEinit S ∪₁ STid S (ES.cont_thread S k)) ∩₁ e2a S ⋄₁ C).
      { basic_solver. }
      rewrite set_collect_inter.
      rewrite set_inter_union_r.
      rewrite set_collect_union.
      relsf. rewrite id_union.
      relsf. unionL.
      { erewrite Execution.ex_inE with (X := X); eauto.
        rewrite ES.acts_init_set_inW; auto.
        rewrite e2a_W; try apply SRC.
        rewrite wf_rfD; try apply SRC.
        type_solver. }
      rewrite collect_map_in_set.
      arewrite (X ∩₁ STid S (ES.cont_thread S k) ⊆₁
                STid S (ES.cont_thread S k)) by basic_solver.
      rewrite e2a_Tid.
      rewrite set_interC.
      rewrite id_inter.
      arewrite (C ⊆₁ C').
      { eapply sim_trav_step_covered_le.
        red. eauto. }
      rewrite <- seqA.
      erewrite rf_C_in_cert_rf;
        eauto; try apply SRC.
      basic_solver. }
    (* icf_ex_ktid_in_co :
     *   e2a □ (Sjf ⨾ ⦗set_compl kE⦘ ⨾ Sicf ⨾ ⦗X ∩₁ STid ktid⦘ ⨾ Sjf⁻¹) ⊆ Gco
     *)
    { arewrite
        (set_compl (kE S k) ⊆₁ fun _ => True).
      relsf.
      erewrite <- icf_ex_in_co
        with (t := ktid S k); eauto; done. }
    (* icf_kE_in_co : e2a □ (Sjf ⨾ Sicf ⨾ ⦗kE⦘ ⨾ Sjf⁻¹) ⊆ Gco *)
    { arewrite (kE S k ⊆₁ SEinit S ∪₁ X ∩₁ STid S (ktid S k)).
      { rewrite XkTIDCOV. basic_solver. }
      rewrite id_union. relsf. unionL.
      { seq_rewrite ES.icfEinit_r. basic_solver. }
      erewrite <- icf_ex_in_co
        with (t := ktid S k); eauto; done. }
    (* ex_cont_iss : X ∩₁ e2a ⋄₁ (contE ∩₁ I) ⊆₁ dom_rel (Sew ⨾ ⦗ kE ⦘) ; *)
    { arewrite (X ∩₁ e2a S ⋄₁ (acts_set (ProgToExecution.G st) ∩₁ I) ⊆₁
                  X ∩₁ SW S ∩₁ STid S (ktid S k) ∩₁ e2a S ⋄₁ C).
      { edestruct cstate_cont as [sta HH];
          eauto; desf.
        rewrite <- e2a_kEninit; try apply SRC; eauto.
        rewrite XkTIDCOV.
        unfolder. ins. desf. splits; auto; try congruence.
        { eapply ex_iss_inW; [apply SRC|]. basic_solver. }
        arewrite (Stid S x = Stid S y); auto.
        rewrite !e2a_tid. congruence. }
      rewrite XkTIDCOV.
      rewrite seq_eqv_r.
      unfolder. ins. desf.
      exists x; splits; auto.
      apply ES.ew_refl; [apply SRC|].
      unfolder; splits; auto.
      eapply Execution.ex_inE; eauto. }
    (* kE_iss : kE ∩₁ e2a ⋄₁ I ⊆₁ dom_rel (Sew ⨾ ⦗ X ⦘) ; *)
    { rewrite seq_eqv_r.
      intros x [kEx Ix].
      assert (X x) as Xx.
      { by apply XkTIDCOV. }
      exists x; splits; auto.
      apply ES.ew_refl; auto.
      red; splits; auto; split.
      { eapply Execution.ex_inE; eauto. }
      eapply ex_iss_inW.
      { apply SRC. }
      split; auto. }
    (* e2a_co_kE : e2a □ (Sco ⨾ ⦗kE⦘) ⊆ Gco *)
    { etransitivity;
        [|eapply e2a_co_ex_tid; eauto].
      rewrite XkTIDCOV.
      rewrite set_inter_union_r, id_union.
      rewrite seq_union_r, collect_rel_union.
      unionL; [|basic_solver 10].
      arewrite_false
        (Sco S ⨾ ⦗X ∩₁ e2a S ⋄₁ C ∩₁ SEinit S⦘).
      { rewrite <- ES.coEninit; auto.
        unfold ES.acts_ninit_set.
        basic_solver. }
      basic_solver. }
    (* e2a_co_ex_ktid : e2a □ (Sco ⨾ ⦗X ∩₁ STid ktid \₁ e2a ⋄₁ contE⦘) ⊆ Gco *)
    { erewrite <- e2a_co_ex_tid; eauto. basic_solver 10. }
    (* rmw_cov_in_kE : Grmw ⨾ ⦗C' ∩₁ e2a □₁ kE⦘ ⊆ e2a □ Srmw ⨾ ⦗ kE ⦘ ; *)
    { rewrite XkTIDCOV at 1.
      unfolder. ins. desf.
      { exfalso.
        match goal with
        | H : Grmw ?x ?y |- _ => rename H into RMW
        end.
        apply WFG.(rmw_in_sb) in RMW.
        apply no_sb_to_init in RMW.
        destruct_seq_r RMW as AA.
        match goal with
        | H : SEinit S ?z |- _ => rename H into IN
        end.
        apply e2a_init in IN. rewrite IN in *.
        desf. }
      edestruct rmw_cov_in_ex as [x' [y' [RMW']]]; try apply SRC.
      { apply seq_eqv_r. splits; eauto. }
      desf.
      destruct_seq_r RMW' as XY.
      exists x'. exists y'. splits; eauto.
      apply XkTIDCOV.
      match goal with
      | H : e2a S ?y' = e2a S ?y |- _ => rename H into EQ
      end.
      unfolder. splits; auto.
      { by rewrite EQ. }
      right. erewrite e2a_tid.
      rewrite EQ. by erewrite <- e2a_tid. }
    inv CERT_ST.
    cdes cstate_cont; desf.
    assert (C ⊆₁ C') as AA.
    { eapply sim_trav_step_covered_le. red; eauto. }

    assert (ES.cont_sb_dom S k ⊆₁ e2a S ⋄₁ C) as SBDC.
    { rewrite XkTIDCOV. basic_solver. }
    assert (ES.cont_sb_dom S k ⊆₁ e2a S ⋄₁ C') as SBDC'.
    { by rewrite <- AA. }

    edestruct CSS as [kC]; try apply SRC; eauto.
    desf.
    assert (kC = k); subst.
    { assert (ES.cont_sb_dom S kC ≡₁ ES.cont_sb_dom S k) as EQSBD.
      2: { eapply ES.same_sb_dom_same_k; eauto. }
      rewrite INX. rewrite XkTIDCOV.
      split; unfolder; ins; desf; splits; eauto.
      { eapply Execution.init_in_ex; eauto. }
      { eapply init_in_map_cov; eauto. }
      { rewrite THK. eauto. }
      right. splits; eauto. by rewrite <- THK. }

    exists k. exists st0. splits; eauto.
    { split; [|basic_solver].
      apply set_subset_inter_r. by split. }
    assert (st0 = state); subst.
    { pose proof (ES.unique_K WF _ _ KK INK eq_refl) as HH. simpls.
      inv HH. }

    apply sim_state_set_tid_eq with (s':=C); auto.
    split.
    { unfolder. ins. desf. split; auto. by apply SBDC. }
    rewrite XkTIDCOV.
    unfolder. ins. desf. splits; auto.
    assert ((e2a S □₁ X) x) as UU.
    { eapply ex_cov_iss.
      { apply SRC. }
      red. basic_solver. }
    red in UU. desf.
    eexists. splits; eauto.
    right. by rewrite e2a_tid.
  Qed.

  Lemma ew_ex_iss_cert_ex_iss k S
        (st : thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st) :
    dom_rel (Sew S ⨾ ⦗X ∩₁ e2a S ⋄₁ I⦘) ≡₁
    dom_rel (Sew S ⨾ ⦗certX S k ∩₁ e2a S ⋄₁ I⦘).
  Proof.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    erewrite <- ew_ex_cert_dom_iss_cert_ex_iss; eauto.
    split; [|basic_solver].
    rewrite <- ex_in_certD; eauto.
    unfolder; ins; desf.
    eexists; splits; eauto.
  Qed.

  Lemma cert_ex_rf_compl k S
        (st : thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st) :
    certX S k ∩₁ SR S ⊆₁ codom_rel (⦗certX S k⦘ ⨾ Srf S).
  Proof.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (es_consistent S) as CONS by apply SRCC.
    assert (simrel prog S G sc TC X (T \₁ eq (ktid S k))) as SR_ by apply SRCC.
    edestruct cstate_cont as [st_ [stEQ KK]];
      [apply SRCC|].
    red in stEQ, KK. subst st_.
    rewrite set_inter_union_l.
    rewrite set_subset_union_l. split.
    2 : eapply kE_rf_compl; eauto.
    intros x [[Xx nTIDx] Rx].
    edestruct Execution.ex_rf_compl
      as [y HH]; eauto.
    { basic_solver. }
    apply seq_eqv_l in HH.
    destruct HH as [Xy RF].
    eapply ES.set_split_Tid
      with (S := S) (t := ktid S k) in Xy.
    destruct Xy as [[Xy TIDy] | [Xy nTIDy]].
    2 : basic_solver 10.
    assert (SEninit S y) as nINITy.
    { red. split.
      { eapply Execution.ex_inE; eauto. }
      intros [_ INITy].
      eapply ktid_ninit; eauto.
      congruence. }
    assert (Srfe S y x) as RFE.
    { unfold ES.rfe. split; auto.
      intros SB.
      apply nTIDx.
      rewrite <- TIDy.
      symmetry.
      eapply ES.sb_tid; auto.
      basic_solver. }
    edestruct rfe_ex_iss
      as [z HH]; eauto.
    { eexists; eauto. }
    assert (dom_rel (Sew S ⨾ ⦗X ∩₁ e2a S ⋄₁ I⦘) y)
      as HH'.
    { basic_solver. }
    eapply ew_ex_iss_cert_ex_iss in HH'; eauto.
    destruct HH' as [z' HH']; eauto.
    apply seq_eqv_r in HH'.
    destruct HH' as [EW [CERTXz' Iz']].
    exists z'.
    apply seq_eqv_l.
    split; auto.
    apply ES.rfe_in_rf.
    eapply ew_rfe_in_rfe; eauto.
    eexists; splits; eauto.
    apply ES.ew_sym; auto.
  Qed.

  Lemma simrel_cert_vis k S
        (st : thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st) :
    certX S k ⊆₁ vis S.
  Proof.
    assert (ES.Wf S) as WFS by apply SRCC.
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (es_consistent S) as CONS by apply SRCC.
    assert (simrel prog S G sc TC X (T \₁ eq (ktid S k))) as SR_ by apply SRCC.
    edestruct cstate_cont as [st_ [stEQ KK]];
      [apply SRCC|].
    red in stEQ, KK. subst st_.
    simpl.
    intros x [[Xx nTIDx] | kSBx].
    { eapply ex_cov_ntid_vis; eauto. basic_solver. }
    red. splits.
    { eapply kE_inE; eauto. }
    rewrite seq_eqv_r.
    intros y z [CC EQz]. subst z.
    assert
      ((dom_rel (Sew S ⨾ ⦗certX S k ∩₁ e2a S ⋄₁ I⦘)) y)
      as EWCERTX.
    { eapply ew_ex_iss_cert_ex_iss; eauto.
      eapply jfe_ex_iss; eauto.
      apply dom_cc_jfe.
      basic_solver. }
    destruct EWCERTX as [z HH].
    apply seq_eqv_r in HH.
    destruct HH as [EW CERTXz].
    eexists; splits; eauto.
    destruct CERTXz as [[[Xz nTIDz] | kSBz] Iz].
    { eapply ES.cont_sb_tid in kSBx; eauto.
      destruct kSBx as [INITx | TIDx].
      { exfalso.
        apply cc_ninit in CC.
        destruct CC as [_ nINITx].
        by apply nINITx. }
      exfalso. apply nTIDz.
      etransitivity.
      { symmetry; apply ES.ew_tid; eauto. }
      etransitivity.
      { apply cc_tid; eauto. }
      done. }
    edestruct ES.cont_sb_dom_cross
      as [[INITz INITx] | HH]; eauto.
    { basic_solver. }
    exfalso.
    apply cc_ninit in CC.
    destruct CC as [_ nINITx].
    by apply nINITx.
  Qed.

  Lemma simrel_cert_end k S
        (st : thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X T k st st) :
    simrel_consistent prog S G sc TC' (certX S k) T.
  Proof.
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC.
    { apply SRCC. }
    assert (simrel prog S G sc TC X (T \₁ eq (ktid S k))) as SR_.
    { apply SRCC. }
    assert (simrel_e2a S G sc) as SRE2A.
    { apply SRCC. }
    assert (C ⊆₁ C') as ICC.
    { eapply sim_trav_step_covered_le. eexists. apply SRCC. }

    edestruct cstate_cont as [stx [EQ KK]];
      [apply SRCC|].
    red in EQ, KK. subst stx.
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
    (* sr_exec : Execution.t S certX *)
    { constructor.
      { eapply cert_ex_inE; eauto. }
      { eapply init_in_cert_ex; eauto. }
      { eapply cert_ex_sb_prcl; eauto. }
      { eapply cert_ex_sw_prcl; eauto. }
      { rewrite id_union, seq_union_l, codom_union.
        apply set_union_Proper.
        { apply set_subset_inter_r. split.
          { etransitivity.
            2: { apply Execution.ex_rmw_fwcl; eauto. }
            basic_solver. }
          rewrite WFS.(ES.rmwt).
          unfold ES.same_tid.
          unfolder. ins. desf. intros AA.
          match goal with
          | H : _ <> _ |- _ => apply H
          end.
          rewrite <- AA. desf. }
        eapply cont_sb_dom_rmw; eauto.
        apply SRCC. }
      { eapply cert_ex_rf_compl; eauto. }
      { eapply cert_ex_ncf; eauto. }
      eapply simrel_cert_vis; eauto. }
    { unfold contsimstate.
      ins.
      destruct (classic (thread = ES.cont_thread S k)) as [|TNEQ]; subst.
      { edestruct contsimstate_kE as [kC]; eauto; desf.
        exists kC. eexists. splits; eauto.
        { rewrite INX.
          split; unfolder; ins; desf; splits; auto.
          { match goal with
            | H : ES.cont_sb_dom S k x |- _ => pose proof H as AA
            end.
            eapply ES.cont_sb_tid in AA; eauto.
            unfolder in AA; desf; eauto.
            right. splits; auto. by rewrite THK. }
          { apply ICC. eapply init_in_map_cov; eauto. }
          { eapply SEinit_in_kE; eauto. }
          rewrite THK in *. desf. }
        eapply sim_state_set_tid_eq; [|by eauto].
        split; [|basic_solver].
        unfolder. ins. desf. splits; eauto.
        rewrite THK in *.
        assert (acts_set (ProgToExecution.G st) x) as BB.
        { eapply dcertE.
          { apply SRCC. }
          red. split; auto. by left. }
        eapply e2a_kEninit in BB; eauto; try apply SRCC.
        unfolder in BB. desf. eexists. splits; eauto. }
      assert (CSS : contsimstate prog S G TC X) by apply SRCC.
      edestruct CSS as [kC].
      { eauto. }
      desf.
      exists kC. eexists. splits; eauto.
      { rewrite !set_interA.
        arewrite ((STid S (ES.cont_thread S kC)) ∩₁ e2a S ⋄₁ C' ≡₁
                  (STid S (ES.cont_thread S kC)) ∩₁ e2a S ⋄₁ C).
        { split.
          2: by rewrite ICC.
          rewrite isim_trav_step_new_covered_tid; try apply SRCC.
          unfolder. ins. desf.
          exfalso.
          apply TNEQ.
          match goal with
          | H : Gtid (e2a S x) = ES.cont_thread S k |- _ => rewrite <- H
          end.
            by rewrite <- e2a_tid. }
        rewrite INX.
        split; unfolder; ins; desf; eauto 10.
        match goal with
        | H : ES.cont_sb_dom S k x |- _ => rename H into AA
        end.
        eapply ES.cont_sb_tid in AA; eauto.
        unfolder in AA; desf; eauto.
        exfalso.
        apply TNEQ. by rewrite <- AA. }
      eapply sim_state_set_tid_eq with (s':=C); auto.
      rewrite isim_trav_step_new_covered_tid; try apply SRCC.
      split; unfolder; ins; desf.
      2: by splits; eauto.
      exfalso. apply TNEQ.
      match goal with
      | H : Gtid x = ES.cont_thread S k |- _ => rewrite <- H
      end.
      done. }
    (* ex_cov_iss : e2a □₁ certX ≡₁ C' ∪₁ dom_rel (Gsb^? ⨾ ⦗ I' ⦘) *)
    { rewrite cert_ex_certD; eauto.
      rewrite cert_dom_cov_sb_iss; eauto.
      by unfold CsbI. }
    (* ex_sb_cov_iss :
     *   forall t (Tt : T t),
     *     e2a □₁ codom_rel (⦗certX⦘ ⨾ Ssb ⨾ ⦗STid ktid⦘) ⊆₁ CsbI G TC'
     *)
    { eapply cert_ex_sb_cov_iss; eauto. }
    (* ex_cov_iss_lab : eq_dom (certX ∩₁ e2a ⋄₁ (C' ∪₁ I')) Slab (Glab ∘ e2a) *)
    { eapply cert_ex_cov_iss_lab; apply SRCC. }
    (* rmw_cov_in_ex : Grmw ⨾ ⦗ C' ⦘ ⊆ e2a □ Srmw ⨾ ⦗ certX ⦘ *)
    { rewrite isim_trav_step_new_covered_tid; try apply SRCC.
      rewrite !id_union, !seq_union_r.
      rewrite collect_rel_union.
      apply union_mori.
      { rewrite !id_inter.
        rewrite <- seqA.
        rewrite rmw_cov_in_ex; eauto.
        unfolder. ins. desf.
        do 2 eexists. splits; eauto.
        eexists. splits; eauto. by rewrite e2a_tid. }
      etransitivity.
      2: by eapply rmw_cov_in_kE; eauto.
      erewrite e2a_kE;
        try apply SRCC; try apply KK.
      rewrite set_inter_union_r, id_union, seq_union_r.
      apply inclusion_union_r2_search.
      rewrite !seq_eqv_r.
      intros x y [RMW [Cy TIDy]].
      unfolder; splits; auto.
      assert (cert_dom G TC (ktid S k) st y)
        as CertDy.
      { eapply cert_dom_cov_sb_iss; eauto. by left. }
      eapply cert_dom_alt in CertDy.
      2 : eapply cstate_covered; apply SRCC.
      destruct CertDy as [[_ NTIDy] | BB]; auto.
      intuition. done. }
    (* jf_ex_in_cert_rf : e2a □ (Sjf ⨾ ⦗certX⦘) ⊆ cert_rf G sc TC' *)
    { eapply jf_cert_ex_in_cert_rf; eauto. }
    (* icf_ex_in_co :
     *   forall t (Tt : T t),
     *     e2a □ (Sjf ⨾ Sicf ⨾ ⦗certX ∩₁ STid t⦘ ⨾ Sjf⁻¹) ⊆ Gco
     *)
    { eapply icf_certX_in_co; eauto. }
    (*  e2a_co_ex_tid :
     *    forall t (Tt : T t),
     *      e2a □ (Sco ⨾ ⦗certX ∩₁ STid t⦘) ⊆ Gco *)
    { eapply e2a_co_cert_ex_tid; eauto. }
    (*  e2a_co_iss : e2a □ (Sco ⨾ ⦗certX ∩₁ e2a S ⋄₁ I'⦘) ⊆ Gco *)
    { eapply e2a_co_cert_ex_iss; eauto. }
    (* jfe_ex_iss : dom_rel Sjfe ⊆₁ dom_rel (Sew ⨾ ⦗ certX ∩₁ e2a ⋄₁ I ⦘) *)
    { etransitivity.
      { eapply jfe_ex_iss; eauto. }
      rewrite ew_ex_iss_cert_ex_iss; eauto.
      erewrite sim_trav_step_issued_le; eauto.
      eexists; apply SRCC. }
    (* ew_ex_iss : dom_rel (Sew \ eq) ⊆₁ dom_rel (Sew ⨾ ⦗ certX ∩₁ e2a ⋄₁ I ⦘) *)
    { etransitivity.
      { eapply ew_ex_iss; eauto. }
      rewrite ew_ex_iss_cert_ex_iss; eauto.
      erewrite sim_trav_step_issued_le; eauto.
      eexists; apply SRCC. }
    (* rel_ew_ex_iss : dom_rel (Srelease ⨾ Sew ⨾ ⦗ certX ∩₁ e2a ⋄₁ I  ⦘) ⊆₁ certX *)
    intros x HH.
    eapply rel_ew_cert_ex; eauto.
    generalize HH. basic_solver 10.
  Qed.

  Lemma simrel_step_helper k S
        (st st''' : thread_st (ktid S k))
        (Tktid : T (ktid S k))
        (SRC : simrel_consistent prog S G sc TC X T)
        (TC_ISTEP : isim_trav_step G sc (ktid S k) TC TC')
        (XkTIDCOV : kE S k ≡₁ X ∩₁ e2a S ⋄₁ C ∩₁ (SEinit S ∪₁ STid S (ktid S k)))
        (CERTG : cert_graph G sc TC' (ktid S k) st''')
        (CERT_ST : simrel_cstate S k st st''')
        (LBL_STEPS : (lbl_step (ktid S k))＊ st st''') :
    (fun st' => exists k' S',
      ⟪ kTID : ktid S' k' = ktid S k ⟫ /\
      ⟪ STEPS : (step Weakestmo)＊ S S' ⟫ /\
      ⟪ SRCC  : simrel_cert prog S' G sc TC TC' X T k' st' st''' ⟫) st'''.
  Proof.
    eapply clos_refl_trans_ind_step_left.
    { exists k, S. splits; auto.
      { apply rt_refl. }
      eapply simrel_cert_start; eauto. }
    { eapply LBL_STEPS. }
    intros st' st'' HH. desc.
    intros LBL_STEP LBL_STEPS'.
    edestruct simrel_cert_lbl_step with (k:=k')
      as [k'' [S'' HH]];
      eauto; desc.
    { rewrite kTID.
      eapply isim_trav_step_thread_ninit; eauto.
      4: apply stable_prog_to_prog_no_init.
      all: apply SRC. }
    { rewrite kTID. apply LBL_STEP. }
    { rewrite kTID. apply LBL_STEPS'. }
    exists k'', S''. splits; auto.
    { congruence. }
    eapply rt_trans; eauto.
    destruct ESSTEP as [EQ | ESSTEP].
    { subst. by apply rt_refl. }
    by apply rt_step.
  Qed.

  Lemma simrel_step t S
        (Tt : T t)
        (SRC : simrel_consistent prog S G sc TC X T)
        (ITRAV_STEP : isim_trav_step G sc t TC TC') :
    exists X' S',
      ⟪ STEPS : (step Weakestmo)＊ S S' ⟫ /\
      ⟪ SRC' : simrel_consistent prog S' G sc TC' X' T⟫.
  Proof.
    edestruct simrel_cert_graph_start
      as [k [st [st' HH]]];
      eauto; desc.
    { eapply isim_trav_step_thread_ninit; eauto.
      all: try apply SRC.
      apply stable_prog_to_prog_no_init.
      apply SRC. }
    edestruct simrel_step_helper
      as [k' [S' HH]];
      subst; eauto; desc.
    { by destruct CERT_ST. }
    exists (certX S' k'), S'.
    splits; auto.
    eapply simrel_cert_end; eauto.
  Qed.

End SimRelStep.
