Require Import Program.Basics.
From hahn Require Import Hahn.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CertExecution2 CertExecutionMain
     CombRelations SimTraversal SimTraversalProperties SimulationRel AuxRel.
Require Import AuxRel.
Require Import AuxDef.
Require Import EventStructure.
Require Import Consistency.
Require Import Execution.
Require Import EventToAction.
Require Import LblStep.
Require Import ImmProperties.
Require Import CertGraph.
Require Import CertRf.
Require Import SimRelCont.
Require Import SimRelEventToAction.
Require Import SimRel.
Require Import ProgES.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelCert.
  Variable prog : stable_prog_type.
  Variable S : ES.t.
  Variable G : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable TC': trav_config.
  Variable X : eventid -> Prop.
  Variable k : cont_label.

  (* A state in a continuation related to k in S. *)
  Variable st : ProgToExecution.state.

  (* A state, which is reachable from 'state' and which represents a graph certification. *)
  Variable st' : ProgToExecution.state.
  
  Notation "'SE'" := S.(ES.acts_set).
  Notation "'SEinit'" := S.(ES.acts_init_set).
  Notation "'SEninit'" := S.(ES.acts_ninit_set).
  Notation "'Stid'" := (S.(ES.tid)).
  Notation "'Slab'" := (S.(ES.lab)).
  Notation "'Sloc'" := (loc S.(ES.lab)).
  Notation "'K'" := S.(ES.cont_set).

  Notation "'STid' t" := (fun x => Stid x = t) (at level 1).
  Notation "'SNTid' t" := (fun x => Stid x <> t) (at level 1).

  Notation "'SR'" := (fun a => is_true (is_r Slab a)).
  Notation "'SW'" := (fun a => is_true (is_w Slab a)).
  Notation "'SF'" := (fun a => is_true (is_f Slab a)).
  Notation "'SRel'" := (fun a => is_true (is_rel Slab a)).
  Notation "'SAcq'" := (fun a => is_true (is_acq Slab a)).

  Notation "'Ssb'" := (S.(ES.sb)).
  Notation "'Scf'" := (S.(ES.cf)).
  Notation "'Srmw'" := (S.(ES.rmw)).
  Notation "'Sjf'" := (S.(ES.jf)).
  Notation "'Sjfi'" := (S.(ES.jfi)).
  Notation "'Sjfe'" := (S.(ES.jfe)).
  Notation "'Srf'" := (S.(ES.rf)).
  Notation "'Srfi'" := (S.(ES.rfi)).
  Notation "'Srfe'" := (S.(ES.rfe)).
  Notation "'Sco'" := (S.(ES.co)).
  Notation "'Sew'" := (S.(ES.ew)).

  Notation "'Srs'" := (S.(Consistency.rs)).
  Notation "'Srelease'" := (S.(Consistency.release)).
  Notation "'Ssw'" := (S.(Consistency.sw)).
  Notation "'Shb'" := (S.(Consistency.hb)).
  Notation "'Secf'" := (S.(Consistency.ecf)).

  Notation "'e2a'" := (e2a S).

  Notation "'thread_syntax' t"  := 
    (Language.syntax (thread_lts t)) (at level 10, only parsing).  

  Notation "'thread_st' t" := 
    (Language.state (thread_lts t)) (at level 10, only parsing).

  Notation "'thread_init_st' t" := 
    (Language.init (thread_lts t)) (at level 10, only parsing).

  Notation "'thread_cont_st' t" :=
    (fun st => existT _ (thread_lts t) st) (at level 10, only parsing).

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

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).
  Notation "'C''"  := (covered TC').
  Notation "'I''"  := (issued TC').

  Notation "'C''"  := (covered TC').
  Notation "'I''"  := (issued TC').

  Notation "'Gvf'" := (furr G sc).

  Notation "'kE'" := (ES.cont_sb_dom S k) (only parsing).
  Notation "'ktid'" := (ES.cont_thread S k) (only parsing).

  Notation "'E0'" := (E0 G TC' ktid).

  Notation "'contG'" := st.(ProgToExecution.G).
  Notation "'certG'" := st'.(ProgToExecution.G).

  Notation "'contE'" := contG.(acts_set).
  Notation "'certE'" := certG.(acts_set).

  Notation "'certLab'" := (certLab G st').

  Notation "'certX'" := ((X ∩₁ SNTid ktid) ∪₁ kE) (only parsing).

  Definition Kstate (ll : cont_label) (lstate : ProgToExecution.state) :=
    exists (st : (thread_lts (ES.cont_thread S ll)).(Language.state)),
      ⟪ SSTATE : lstate = st ⟫ /\
      ⟪ KK     : K (ll, existT _ _ st) ⟫.

  Record simrel_cstate := 
    { cstate_stable : stable_state st';
      cstate_cont : Kstate k st;
      cstate_reachable : (lbl_step ktid)＊ st st';
    }.
  
  Notation "'certC'" := (C' ∩₁ e2a □₁ kE).

  Record simrel_cert :=
    { sim : simrel prog S G sc TC X ;

      tr_step : isim_trav_step G sc ktid TC TC' ;

      cert : cert_graph G sc TC TC' ktid st' ;
      cstate : simrel_cstate ; 

      ex_ktid_cov : X ∩₁ STid ktid ∩₁ e2a ⋄₁ C ⊆₁ kE ;
      cov_in_ex   : e2a ⋄₁ C ∩₁ kE ⊆₁ X ;

      kE_lab : eq_dom (kE \₁ SEinit) Slab (certG.(lab) ∘ e2a) ;

      jf_in_cert_rf : e2a □ (Sjf ⨾ ⦗kE⦘) ⊆ cert_rf G sc TC' ktid ;

      ex_cont_iss : X ∩₁ e2a ⋄₁ (contE ∩₁ I) ⊆₁ dom_rel (Sew ⨾ ⦗ kE ⦘) ;
      
      rmw_cov_in_kE : Grmw ⨾ ⦗C' ∩₁ e2a □₁ kE⦘ ⊆ e2a □ Srmw ⨾ ⦗ kE ⦘ ;

      (* contpckE : forall e (XE : certX e) (state : thread_st (Stid e)) *)
      (*                 (PC : (certC ∩₁ GTid (Stid e) \₁ dom_rel (sb G ⨾ ⦗certC⦘)) (e2a e)) *)
      (*                 (INK : K (CEvent e, thread_cont_st (Stid e) state)), *)
      (*     @sim_state G sim_normal certC (Stid e) state; *)

      contsimstate_kE :
          exists kC (state : thread_st (ES.cont_thread S kC)),
            << THK   : ES.cont_thread S kC = ktid >> /\
            << INK   : K (kC, thread_cont_st (ES.cont_thread S kC) state) >> /\
            << INX   : ES.cont_sb_dom S kC ≡₁ e2a ⋄₁ C' ∩₁ kE >> /\
            << SIMST : @sim_state G sim_normal certC (ES.cont_thread S kC) state >>;
    }.

  Section SimRelCertProps. 
    
    Variable SRCC : simrel_cert.

    Lemma cov_in_cert_dom : 
      C ⊆₁ cert_dom G TC ktid st.
    Proof. unfold cert_dom. basic_solver. Qed.

    Lemma GEinit_in_cert_dom (TCCOH : tc_coherent G sc TC) : 
      GEinit ⊆₁ cert_dom G TC ktid st. 
    Proof. 
      etransitivity; [|apply cov_in_cert_dom].
      eapply init_covered; eauto. 
    Qed.

    Lemma cert_dom_sb_prcl :
      dom_rel (Gsb ⨾ ⦗ cert_dom G TC ktid st ⦘) ⊆₁ cert_dom G TC ktid st.
    Proof.
      assert (tc_coherent G sc TC) as TCCOH by apply SRCC.
      intros x [y SB].
      destruct_seq_r SB as YY.
      set (ESB := SB).
      destruct_seq ESB as [XE YE].
      destruct YY as [[YY|[YY NTID]]|YY].
      { apply cov_in_cert_dom. eapply dom_sb_covered; eauto.
        eexists. apply seq_eqv_r. eauto. }
      { set (CC := SB). apply sb_tid_init in CC. desf.
        { left. right. split. 2: by rewrite CC.
          generalize (@sb_trans G) SB YY. basic_solver 10. }
        apply cov_in_cert_dom. eapply init_covered; eauto.
        split; auto. }
      destruct (classic (is_init x)) as [NN|NINIT].
      { apply cov_in_cert_dom. eapply init_covered; eauto.
        split; auto. }
      right.
      edestruct cstate_cont as [lstate]; [apply SRCC|]. desf.
      assert (wf_thread_state (ES.cont_thread S k) lstate) as WFT.
      { eapply contwf; [by apply SRCC|]. apply KK. }
      eapply acts_rep in YY; eauto. 
      destruct YY as [yin [REP LE]]. 
      rewrite REP in *.
      destruct x; desf.
      red in ESB. desf. 
      apply acts_clos; auto.
      { by subst thread. }
      etransitivity; eauto.  
    Qed.

    Lemma ktid_ninit : 
      ktid <> tid_init. 
    Proof. 
      edestruct cstate_cont; [apply SRCC|]. 
      desc. subst x.
      intros kTID.
      edestruct ES.init_tid_K; [apply SRCC|].
      do 2 eexists. splits; eauto.
    Qed.

    Lemma cstate_covered : 
      C ∩₁ GTid ktid ⊆₁ contE. 
    Proof. 
      edestruct cstate_cont; [apply SRCC|]. 
      desc. subst x. 
      intros x [Cx TIDx].
      eapply e2a_kEninit; eauto; try apply SRCC.
      assert ((e2a □₁ X) x) as Xx.
      { eapply ex_cov_iss; [apply SRCC|]. basic_solver. }
      destruct Xx as [x' [Xx' EQx]]. subst x.
      unfolder; eexists; splits; eauto.
      { eapply ex_ktid_cov; auto.
        unfolder; splits; auto.
        by erewrite e2a_tid. }
      intros INITx.
      apply ktid_ninit.
      rewrite <- TIDx.
      erewrite <- e2a_tid.
      apply INITx.
    Qed.

    Lemma wf_cont_state : 
      wf_thread_state ktid st. 
    Proof. 
      edestruct cstate_cont. 
      { apply SRCC. }
      eapply contwf; eauto. 
      apply SRCC. desf.
    Qed.

    Lemma trav_step_cov_sb_iss_le : 
      C ∪₁ dom_rel (Gsb^? ⨾ ⦗I⦘) ⊆₁ C' ∪₁ dom_rel (Gsb^? ⨾ ⦗I'⦘).
    Proof. 
      erewrite sim_trav_step_covered_le,
               sim_trav_step_issued_le.
      2,3: eexists; apply SRCC.
      done.
    Qed.

    Lemma trav_step_cov_sb_iss_tid : 
      C' ∪₁ dom_rel (Gsb^? ⨾ ⦗I'⦘) ≡₁ 
         (C ∪₁ dom_rel (Gsb^? ⨾ ⦗I⦘)) ∩₁ GNTid ktid ∪₁ 
         (C' ∪₁ dom_rel (Gsb^? ⨾ ⦗I'⦘)) ∩₁ GTid ktid.
    Proof. 
      edestruct isim_trav_step_new_e_tid_alt as [HA HB].
      1-2 : apply SRCC.
      apply set_subset_union_l in HA.
      destruct HA as [HAC HAI].
      split.
      { rewrite crE at 1. relsf. splits. 
        { intros x Cx.
          apply HAC in Cx.
          generalize Cx. basic_solver 10. }
        { intros x Ix.
          apply HAI in Ix.
          generalize Ix. basic_solver 10. }
        rewrite seq_eqv_r.
        intros x [y [SB Iy]].
        edestruct tid_set_dec 
          with (thread := ktid)
          as [_ Htid].
        edestruct sb_tid_init as [EQtid | INITx]; eauto.
        { specialize (Htid y (Logic.I)).
          destruct Htid as [Htid | Htid].
          { do 2 right. split. 
            { exists y. basic_solver. }
            congruence. }
          apply HAI in Iy.
          destruct Iy as [[[Cy | Iy] _] | [_ TIDy]].
          { do 2 left. split. 
            { eapply dom_sb_covered.
              { apply SRCC. }
              basic_solver 10. }
            basic_solver. }
          { left. right. split.
            { basic_solver 10. }
            congruence. }
          exfalso. done. }
        do 2 left. split. 
        { eapply init_covered.
          { apply SRCC. }
          split; auto.
          apply wf_sbE in SB.
          generalize SB. basic_solver. }
        apply is_init_tid in INITx. 
        rewrite INITx.
        intros HH. by eapply ktid_ninit. }
      rewrite set_subset_union_l. splits.
      { erewrite sim_trav_step_covered_le,
                 sim_trav_step_issued_le.
        2,3 : eexists; apply SRCC.
        basic_solver 10. }
      basic_solver 5.
    Qed.

    Lemma cert_dom_cov_sb_iss : 
      cert_dom G TC ktid st' ≡₁ C' ∪₁ dom_rel (Gsb^? ⨾ ⦗I'⦘). 
    Proof. 
      rewrite cert_dom_alt.
      { rewrite dcertE; [|apply SRCC].
        unfold CertRf.E0.
        rewrite trav_step_cov_sb_iss_tid at 2.
        basic_solver 10. }
      etransitivity.
      { apply cstate_covered; eauto. }
      eapply steps_preserve_E. 
      { eapply wf_cont_state. }
      apply lbl_steps_in_steps.
      apply SRCC.
    Qed.

    Lemma tccoh' : 
      tc_coherent G sc TC'.
    Proof. eapply isim_trav_step_coherence; apply SRCC. Qed.

    Lemma kE_inE : 
      kE ⊆₁ SE. 
    Proof. 
      edestruct cstate_cont; [apply SRCC|]. 
      desc. subst x. 
      intros x kSBx.
      eapply ES.cont_sb_domE; eauto.
      apply SRCC.
    Qed.
    
    Lemma SEinit_in_kE : 
      SEinit ⊆₁ kE.
    Proof. 
      eapply ES.cont_sb_dom_Einit; [apply SRCC|].
      edestruct cstate_cont; [apply SRCC|].
      desf. apply KK.
    Qed.

    Lemma GEinit_in_e2a_kE : 
      GEinit ⊆₁ e2a □₁ kE. 
    Proof. 
      erewrite <- e2a_same_Einit.
      2-4: by eapply SRCC.
      apply set_collect_mori; auto. 
      by apply SEinit_in_kE.
      apply SRCC.
    Qed.

    Lemma cert_ex_inE : 
      certX ⊆₁ SE.
    Proof. 
      unionL.
      { rewrite Execution.ex_inE 
          with (X := X); [|apply SRCC].
        basic_solver. }
      edestruct cstate_cont; [apply SRCC|]. desc.
      eapply ES.cont_sb_domE; eauto.
      apply SRCC.
    Qed.

    Lemma init_in_cert_ex :
      SEinit ⊆₁ certX.
    Proof. 
      assert (ES.Wf S) as WFS by apply SRCC.
      assert (Execution.t S X) as EXEC by apply SRCC.
      edestruct cstate_cont as [st_ [stEQ KK]]; 
        [apply SRCC|].
      red in stEQ, KK. subst st_.
      rewrite ES.cont_sb_dom_Einit; eauto.
      basic_solver.
    Qed.

    Lemma ex_cov_in_certX :
      X ∩₁ e2a ⋄₁ C ⊆₁ certX. 
    Proof. 
      rewrite set_unionC.
      erewrite ES.set_split_Tid with 
          (S := S) (X := X) (t := ktid) at 1.
      rewrite set_inter_union_l.
      apply set_union_Proper. 
      { by apply ex_ktid_cov. }
      basic_solver.      
    Qed.

    Lemma cert_ex_certD : 
      e2a □₁ certX ≡₁ cert_dom G TC ktid st.
    Proof. 
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (Execution.t S X) as EXEC.
      { apply SRCC. }
      edestruct cstate_cont; [apply SRCC|]. 
      desc. subst x.
      rewrite cert_dom_alt.
      2 : apply cstate_covered; apply SRCC.
      rewrite set_collect_union.
      rewrite e2a_kE; eauto; try apply SRCC.
      rewrite <- set_unionA.
      erewrite set_union_absorb_r
        with (s := GEinit).
      { rewrite ex_NTid. 
        apply set_union_Propere; auto.
        apply set_inter_Propere; auto.
        eapply ex_cov_iss. apply SRCC. }
      rewrite <- e2a_same_Einit; try apply SRCC.
      apply set_collect_mori; auto.
      apply set_subset_inter_r. split.
      { by apply Execution.init_in_ex. }
      intros x [_ NTIDx] TIDx.
      eapply ktid_ninit. 
      congruence.
    Qed.

    Lemma ex_in_certD :
      e2a □₁ X ⊆₁ cert_dom G TC ktid st'.
    Proof. 
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (Execution.t S X) as EXEC.
      { apply SRCC. }
      assert (simrel_ prog S G sc TC X) as SR_.
      { apply SRCC. }
      rewrite ex_cov_iss; eauto.
      rewrite cert_dom_cov_sb_iss.
      apply trav_step_cov_sb_iss_le.
    Qed.

    Lemma ex_in_e2a_certD : 
      X ⊆₁ e2a ⋄₁ cert_dom G TC ktid st'. 
    Proof. 
      rewrite set_in_map_collect 
        with (s := X) (f := e2a).
      by rewrite ex_in_certD.
    Qed.

    Lemma ex_cov_iss_cert_lab : 
      eq_dom (X ∩₁ e2a ⋄₁ (C ∪₁ I)) Slab (certLab ∘ e2a).
    Proof. 
      intros x [Xx e2aCIx].
      erewrite ex_cov_iss_lab; 
        [ | apply SRCC | done].
      unfold compose.
      symmetry. eapply cslab.
      { apply SRCC. }
      unfold D. do 4 left. 
      eapply isim_trav_step_new_e_tid.
      1,2: apply SRCC.
      basic_solver.
    Qed.

    Lemma kE_cert_lab : 
      eq_dom kE Slab (certLab ∘ e2a).
    Proof.
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (Execution.t S X) as EXEC.
      { apply SRCC. }
      edestruct cstate_cont; [apply SRCC|]. 
      desc. subst x.
      intros x kSBx.
      unfold compose.
      assert (SE x) as SEx.
      { by apply kE_inE. }
      assert ((e2a □₁ kE) (e2a x)) as e2akEx.
      { basic_solver. }
      eapply e2a_kE in e2akEx;
        eauto; try apply SRCC.
      destruct e2akEx as [INITx | CONTEx].
      { assert (C (e2a x)) as Cx.
        { eapply init_covered; eauto. apply SRCC. }
        erewrite ex_cov_iss_lab; [| apply SRCC |].
        { erewrite cslab; [auto | apply SRCC |].
          unfold D. do 5 left. 
          eapply SimTraversalProperties.sim_trav_step_covered_le;
            eauto.
          econstructor. apply SRCC. }
        split; [|basic_solver].
        eapply Execution.init_in_ex; eauto.
        set (INITx' := INITx).
        eapply e2a_same_Einit in INITx'; try apply SRCC.
        unfolder in INITx'. 
        destruct INITx' as [y [INITy e2aEQ]].
        eapply e2a_map_Einit.
        split; eauto. }
      assert (certE (e2a x)) as CERTEx.
      { eapply steps_preserve_E; eauto.
        { apply wf_cont_state. }
        apply lbl_steps_in_steps.
        apply SRCC. }
      unfold CertGraph.certLab.
      erewrite restr_fun_fst; auto.
      apply kE_lab; auto. 
      split; auto.
      intros INITx.
      assert (GEinit (e2a x)) as GINITx.
      { eapply e2a_same_Einit.
        1-4: by apply SRCC.
        basic_solver. }
      edestruct acts_rep.
      { apply wf_cont_state. }
      { apply CONTEx. }
      unfolder in GINITx.
      unfold is_init in GINITx.
      desf. 
    Qed.
    
    Lemma cert_ex_cov_iss_lab : 
      eq_dom (certX ∩₁ e2a ⋄₁ (C' ∪₁ I')) Slab (Glab ∘ e2a).
    Proof. 
      rewrite set_inter_union_l.
      apply eq_dom_union. split. 
      { arewrite (X ∩₁ SNTid ktid ∩₁ e2a ⋄₁ (C' ∪₁ I') ⊆₁ 
                  X ∩₁ e2a ⋄₁ (C ∪₁ I)).
        { erewrite isim_trav_step_new_e_tid_alt.
          2,3: apply SRCC.
          rewrite set_map_union.
          rewrite set_inter_union_r.
          rewrite set_subset_union_l.
          splits.
          { basic_solver. }
          intros x [[_ nTIDx] [_ TIDx]]. 
          exfalso. apply nTIDx.
          by rewrite e2a_tid. }
        eapply ex_cov_iss_lab. apply SRCC. }
      intros x [KSBx e2aCIx].
      erewrite kE_cert_lab; auto.
      unfold compose.
      erewrite <- cslab 
        with (G := G); [auto | apply SRCC|].
      unfold D. do 4 left. basic_solver.
    Qed.

    Lemma cert_ex_cov_iss_cert_lab : 
      eq_dom (certX ∩₁ e2a ⋄₁ (C' ∪₁ I')) Slab (certLab ∘ e2a).
    Proof. 
      intros x [KSBx e2aCIx].
      erewrite cert_ex_cov_iss_lab.
      2 : basic_solver.
      unfold compose.
      erewrite <- cslab; 
        [eauto | apply SRCC |].
      unfold D. do 4 left. basic_solver.
    Qed.

    Lemma ex_ntid_sb_prcl : 
      dom_rel (Ssb ⨾ ⦗ X ∩₁ SNTid ktid ⦘) ⊆₁ SEinit ∪₁ X ∩₁ SNTid ktid.
    Proof. 
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      rewrite seq_eqv_r.
      intros x [y [SB [Xx NTIDy]]]. 
      edestruct ES.NTid_sb_prcl 
        as [INITx | NTIDx]; eauto.
      { basic_solver 10. }
      { by left. }
      right. split; auto.
      eapply Execution.ex_sb_prcl; [apply SRCC|].
      basic_solver 10.
    Qed.

    Lemma kE_sb_prcl : 
      dom_rel (Ssb ⨾ ⦗ kE ⦘) ⊆₁ kE.
    Proof. 
      edestruct cstate_cont; [apply SRCC|]. 
      eapply ES.cont_sb_prcl; [apply SRCC|].
      desc. apply KK.
    Qed.

    Lemma cert_ex_sb_prcl : 
      dom_rel (Ssb ⨾ ⦗ certX ⦘) ⊆₁ certX.
    Proof.
      rewrite id_union. 
      relsf. split.
      { rewrite ex_ntid_sb_prcl.
        rewrite init_in_cert_ex.
        basic_solver. }
      rewrite kE_sb_prcl. 
      basic_solver.
    Qed.

    Lemma certX_ncf_cont : 
      certX ∩₁ ES.cont_cf_dom S k ≡₁ ∅.
    Proof. 
      assert (ES.Wf S) as WFS by apply SRCC.
      edestruct cstate_cont as [st_ [stEQ KK]]; 
        [apply SRCC|].
      red; split; [|done].
      rewrite set_inter_union_l.
      apply set_subset_union_l; split. 
      { rewrite ES.cont_cf_Tid_; eauto. basic_solver. }
      eapply ES.cont_sb_cont_cf_inter_false; eauto. 
    Qed.

    Lemma cert_ex_ncf : 
      ES.cf_free S certX.
    Proof. 
      assert (ES.Wf S) as WFS by apply SRCC.
      assert (Execution.t S X) as EXEC by apply SRCC.
      edestruct cstate_cont as [st_ [stEQ KK]]; 
        [apply SRCC|].
      red in stEQ, KK. subst st_.
      red. rewrite <- restr_relE.
      intros x y [CF [CERTXx CERTXy]].
      destruct CERTXx as [[Xx NTIDx] | kSBx];
      destruct CERTXy as [[Xy NTIDy] | kSBy].
      { eapply Execution.ex_ncf; [apply SRCC|].
        apply restr_relE. red. eauto. }
      { eapply ES.cont_sb_tid in kSBy; eauto.
        destruct kSBy as [INITy | TIDy].
        { eapply Execution.ex_ncf; [apply SRCC|].
          apply restr_relE. red. splits; eauto.
          eapply Execution.init_in_ex; eauto. }
        apply NTIDx.
        erewrite ES.cf_same_tid; eauto. }
      { eapply ES.cont_sb_tid in kSBx; eauto.
        destruct kSBx as [INITx | TIDx].
        { eapply Execution.ex_ncf; [apply SRCC|].
          apply restr_relE. red. splits; eauto.
          eapply Execution.init_in_ex; eauto. }
        apply NTIDy.
        erewrite ES.cf_same_tid; eauto. 
        by apply ES.cf_sym. }
      eapply ES.cont_sb_cf_free; eauto.
      apply seq_eqv_lr. eauto.
    Qed.

    Lemma ex_iss_cert_ex :
      X ∩₁ e2a ⋄₁ (cert_dom G TC ktid st ∩₁ I) ⊆₁ 
        dom_rel (Sew ⨾ ⦗certX ∩₁ e2a ⋄₁ I⦘).
    Proof. 
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (Execution.t S X) as EXEC.
      { apply SRCC. }
      assert (simrel_ prog S G sc TC X) as SR_.
      { apply SRCC. }
      rewrite cert_dom_alt.
      2 : apply cstate_covered.
      rewrite !set_map_inter, 
              !set_map_union,
              !set_map_inter.
      rewrite !set_inter_union_l, 
              !set_inter_union_r,
              !set_subset_union_l.
      rewrite id_union. relsf.
      splits.
      { intros x [Xx [[_ nTIDx] Ix]].
        left. exists x.
        apply seq_eqv_r.
        unfold set_inter. 
        splits; auto.
        { apply ES.ew_refl; auto.
          unfolder; splits; auto.
          { eapply Execution.ex_inE; eauto. }
          eapply ex_iss_inW; eauto.
          red. auto. }
        intros TIDx. apply nTIDx. 
        by rewrite <- e2a_tid. }
      intros x [Xx [CONTx Ix]].
      edestruct ex_cont_iss
        as [z HH]; eauto.
      { unfolder; split; eauto. }
      apply seq_eqv_r in HH.
      destruct HH as [EW kSB].
      right. exists z.
      apply seq_eqv_r.
      unfold set_inter.
      splits; auto.
      red. erewrite e2a_ew; eauto.
      { apply SRCC. }
      do 2 eexists. splits.
      2,3: eauto.
      apply ES.ew_sym; auto.
    Qed.

    Lemma rel_ew_cert_ex : 
      dom_rel (Srelease ⨾ Sew ⨾ ⦗ certX ⦘) ⊆₁ certX.
    Proof.
      rewrite ew_in_ew_ex_iss_ew; [|apply SRCC].
      rewrite crE, !seq_union_l, !seq_union_r, 
              !dom_union, !seqA.
      relsf. split.
      { rewrite rel_in_ex_cov_rel_sb; [|apply SRCC].
        relsf. rewrite !seqA. splits.
        { rewrite dom_seq, dom_eqv.
          apply ex_cov_in_certX. }
        rewrite set_unionC.
        rewrite id_union, !seq_union_r, dom_union.
        rewrite crE, !seq_union_l, !dom_union.
        unionL.
        1,3 : basic_solver.
        { erewrite kE_sb_prcl. basic_solver. }
        erewrite ex_ntid_sb_prcl.
        apply set_union_Proper; auto.
        apply SEinit_in_kE. }
      do 2 rewrite <- seqA.
      rewrite dom_seq, !seqA.
      rewrite rel_ew_ex_iss_cov; [|apply SRCC].
      apply ex_cov_in_certX. 
    Qed.

    Lemma cert_ex_sw_prcl :
      dom_rel (Ssw ⨾ ⦗ certX ⦘) ⊆₁ certX. 
    Proof. 
      assert (ES.Wf S) as WFS.
      { apply SRCC. }
      assert (Execution.t S X) as EXEC.
      { apply SRCC. }
      assert (simrel_ prog S G sc TC X) as SR_.
      { apply SRCC. }
      rewrite sw_in_ex_cov_sw_sb; eauto.
      relsf. splits.
      2 : apply cert_ex_sb_prcl.
      rewrite seqA, dom_seq, dom_eqv.
      apply ex_cov_in_certX.
    Qed.

    Lemma cert_ex_hb_prcl :
      dom_rel (Shb ⨾ ⦗ certX ⦘) ⊆₁ certX.  
    Proof.
      unfold hb.
      rewrite seq_eqv_r.
      intros x [y [HB yX]].
      induction HB as [x y [SSB | SSW] | ]; auto.
      { apply cert_ex_sb_prcl; auto. basic_solver 10. }
      apply cert_ex_sw_prcl; auto. basic_solver 10. 
    Qed.

    Lemma hb_rel_ew_cert_ex :
      dom_rel (Shb^? ⨾ Srelease ⨾ Sew ⨾ ⦗ certX ⦘) ⊆₁ certX.  
    Proof. 
      rewrite crE with (r := Shb).
      relsf. split.
      { by apply rel_ew_cert_ex. }
      intros x [y [z [HB REL]]].
      eapply cert_ex_hb_prcl; auto.
      eexists. apply seq_eqv_r. split; eauto.
      apply rel_ew_cert_ex; auto. basic_solver.
    Qed.

    Lemma jf_kE_in_ew_cert_ex : 
      dom_rel (Sjf ⨾ ⦗ kE ⦘) ⊆₁ dom_rel (Sew ⨾ ⦗ certX ⦘).  
    Proof.
      assert (ES.Wf S) as WFS by apply SRCC.
      rewrite ES.jfi_union_jfe. relsf. splits.
      { arewrite (Sjfi ≡ ⦗ SE ∩₁ SW ⦘ ⨾ Sjfi).
        { rewrite ES.jfiE, ES.jfiD; auto. basic_solver. }
        rewrite dom_eqv1. 
        arewrite (Sjfi ⊆ Ssb).
        rewrite kE_sb_prcl.
        rewrite <- ES.ew_refl; auto.
        basic_solver 10. }
      rewrite !seq_eqv_r.
      intros x [y [JFE KSB]].
      edestruct jfe_ex_iss as [z HH]. 
      { apply SRCC. }
      { red. eauto. }
      apply seq_eqv_r in HH. 
      destruct HH as [EW [Xz Iz]].
      eexists. 
      splits; eauto.
      left. split; auto.
      eapply jfe_alt in JFE; auto.
      2 : apply SRCC.
      unfolder in JFE. 
      destruct JFE as [nINITx [JF nSTID]].
      intros TIDz. apply nSTID. red. 
      arewrite (Stid x = Stid z).
      { (* TODO : separate lemma *)
        apply ES.ewc in EW; auto.
        destruct EW as [EQ | CF]; auto.
        by apply ES.cf_same_tid. }
      edestruct cstate_cont; [apply SRCC|]. desc.
      eapply ES.cont_sb_tid in KSB; eauto.
      destruct KSB as [INITy | TIDy].
      { exfalso. eapply ES.jf_nEinit; eauto. basic_solver. }
      congruence.
    Qed.

    Lemma kE_rf_compl : 
      kE ∩₁ SR ⊆₁ codom_rel (⦗certX⦘ ⨾ Srf).
    Proof. 
      assert (ES.Wf S) as WFS by apply SRCC.
      assert (Execution.t S X) as EXEC by apply SRCC.
      edestruct cstate_cont as [st_ [stEQ KK]];
        [apply SRCC|].
      red in stEQ, KK. subst st_.
      intros x [kSBx Rx].
      edestruct ES.jf_complete
        as [y JF]; eauto.
      { split; eauto.
        eapply ES.cont_sb_domE; eauto. }
      edestruct jf_kE_in_ew_cert_ex
        as [z HH].
      { basic_solver 10. }
      apply seq_eqv_r in HH.
      destruct HH as [EW CERTXz].
      exists z. apply seq_eqv_l.
      splits; auto.
      unfold ES.rf.
      unfolder. splits.
      { eexists; splits; eauto.
        by apply ES.ew_sym. }
      intros CF.
      destruct CERTXz as [[Xz nTIDz] | kSBz].
      { eapply ES.cont_sb_tid in kSBx; eauto. 
        destruct kSBx as [INITx | TIDx].
        { eapply ES.ncfEinit_r. basic_solver. }
        apply nTIDz.
        apply ES.cf_same_tid in CF.
        congruence. }
      eapply ES.cont_sb_cf_free; eauto.
      basic_solver.
    Qed.

    Lemma cert_ex_necf :
      restr_rel certX Secf ⊆ ∅₂.
    Proof. 
      unfold restr_rel, ecf.
      intros a b [ECF [Hx Hy]].
      destruct ECF as [c [tHB [d [CF HB]]]].
      eapply cert_ex_ncf.
      apply restr_relE. unfold restr_rel.
      splits; eauto.
      { unfolder in tHB; desf.
        eapply cert_ex_hb_prcl; auto. basic_solver 10. }
      unfolder in HB; desf.
      eapply cert_ex_hb_prcl; auto. basic_solver 10.
    Qed.

    Lemma ex_cov_ntid_vis : 
      X ∩₁ e2a ⋄₁ C ∪₁ X ∩₁ SNTid ktid ⊆₁ vis S. 
    Proof. 
      rewrite <- set_inter_union_r.
      (* TODO : vis_mori *)
      intros x [Xx _].
      eapply Execution.ex_vis; eauto. 
      apply SRCC.
    Qed.

  End SimRelCertProps. 

End SimRelCert.
