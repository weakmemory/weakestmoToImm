Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CertExecution2 CertExecutionMain
     CombRelations SimTraversal SimulationRel AuxRel.
Require Import AuxRel AuxDef EventStructure Consistency Execution
        EventToAction LblStep 
        ImmProperties CertGraph CertRf 
        SimRelCont SimRelEventToAction SimRel  SimRelJF.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelCert.
  Variable prog : Prog.t.
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

  Notation "'thread_syntax' tid"  := 
    (Language.syntax (thread_lts tid)) (at level 10, only parsing).  

  Notation "'thread_st' tid" := 
    (Language.state (thread_lts tid)) (at level 10, only parsing).

  Notation "'thread_init_st' tid" := 
    (Language.init (thread_lts tid)) (at level 10, only parsing).
  
  Notation "'thread_cont_st' tid" :=
    (fun st => existT _ (thread_lts tid) st) (at level 10, only parsing).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).

  Notation "'Gtid'" := (tid).
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gloc'" := (loc G.(lab)).
  
  Notation "'GTid' t" := (fun x => tid x = t) (at level 1).
  Notation "'GNTid' t" := (fun x => tid x <> t) (at level 1).

  Notation "'GR'" := (fun a => is_true (is_r Glab a)).
  Notation "'GW'" := (fun a => is_true (is_w Glab a)).
  Notation "'GF'" := (fun a => is_true (is_f Glab a)).

  Notation "'GRel'" := (fun a => is_true (is_rel Glab a)).
  Notation "'GAcq'" := (fun a => is_true (is_acq Glab a)).
  
  Notation "'Gsb'" := (G.(sb)).
  Notation "'Grmw'" := G.(rmw).
  Notation "'Grf'" := (G.(rf)).
  Notation "'Gco'" := (G.(co)).

  Notation "'Grs'" := (G.(imm_s_hb.rs)).
  Notation "'Grelease'" := (G.(imm_s_hb.release)).
  Notation "'Ghb'" := (G.(imm_s_hb.hb)).

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

  Notation "'fdom'" := (C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘)) (only parsing).
  Notation "'hdom'" := (cert_dom G TC ktid st) (only parsing).

  Notation "'Ssim_jf'" := (sim_jf G sc TC' S h).
  Notation "'Ssim_vf'" := (sim_vf G sc TC' S h).
  Notation "'DR'" := (DR G TC' S h).

  Definition Kstate : cont_label * ProgToExecution.state -> Prop :=
    fun l =>
      match l with
      | (ll, lstate) =>
        exists (st : (thread_lts (ES.cont_thread S ll)).(Language.state)),
          ⟪ SSTATE : lstate = st ⟫ /\
          ⟪ KK     : K (ll, existT _ _ st) ⟫
      end.

  Record simrel_cstate := 
    { cstate_stable : stable_state ktid st';
      cstate_cont : Kstate (k, st);
      cstate_reachable : (lbl_step ktid)＊ st st';
      cstate_covered : C ∩₁ GTid ktid ⊆₁ contE; 
    }.

  Record simrel_cert :=
    { sim_com : simrel_common prog S G sc TC X;

      tr_step : isim_trav_step G sc ktid TC TC';

      cert : cert_graph G sc TC TC' ktid st';
      cstate : simrel_cstate; 

      ex_ktid_cov : X ∩₁ STid ktid ∩₁ e2a ⋄₁ C ⊆₁ kE ;

      kE_lab : eq_dom (kE \₁ SEinit) Slab (certG.(lab) ∘ e2a);

      rel_ew_cont_iss : dom_rel (Srelease ⨾ Sew ⨾ ⦗ kE ∩₁ e2a ⋄₁ I ⦘) ⊆₁ certX ;

      e2a_jfDR : e2a □ (Sjf ⨾ ⦗DR⦘) ⊆ Grf;

      jf_in_sim_jf : Sjf ⊆ Ssim_jf;

      (* imgcc : ⦗ f □₁ sbq_dom ⦘ ⨾ Scc ⨾ ⦗ h □₁ sbq_dom ⦘ ⊆ *)
      (*         ⦗ h □₁ GW ⦘ ⨾ Sew ⨾ Ssb⁼ ; *)
    }.

  Section SimRelCertProps. 
    
    Variable SRCC : simrel_cert.

    Lemma C_in_hdom : 
      C ⊆₁ hdom.
    Proof. unfold cert_dom. basic_solver. Qed.

    Lemma GEinit_in_hdom (TCCOH : tc_coherent G sc TC) : 
      GEinit ⊆₁ hdom. 
    Proof. 
      etransitivity; [|apply C_in_hdom].
      eapply init_covered; eauto. 
    Qed.

    Lemma hdom_sb_dom :
      dom_rel (Gsb ⨾ ⦗ hdom ⦘) ⊆₁ hdom.
    Proof.
      assert (tc_coherent G sc TC) as TCCOH by apply SRCC.
      intros x [y SB].
      destruct_seq_r SB as YY.
      set (ESB := SB).
      destruct_seq ESB as [XE YE].
      destruct YY as [[YY|[YY NTID]]|YY].
      { apply C_in_hdom. eapply dom_sb_covered; eauto.
        eexists. apply seq_eqv_r. eauto. }
      { set (CC := SB). apply sb_tid_init in CC. desf.
        { left. right. split. 2: by rewrite CC.
          generalize (@sb_trans G) SB YY. basic_solver 10. }
        apply C_in_hdom. eapply init_covered; eauto.
        split; auto. }
      destruct (classic (is_init x)) as [NN|NINIT].
      { apply C_in_hdom. eapply init_covered; eauto.
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

    Lemma hdom_sb_prefix :
      Gsb ⨾ ⦗ hdom ⦘ ≡ ⦗ hdom ⦘ ⨾ Gsb ⨾ ⦗ hdom ⦘.
    Proof.
      split.
      all: intros x y SB.
      2: { destruct_seq_l SB as AA. apply SB. }
      apply seq_eqv_l. split; auto.
      apply hdom_sb_dom; auto. red. eauto.
    Qed.

    Lemma tccoh' : 
      tc_coherent G sc TC'.
    Proof. eapply isim_trav_step_coherence; apply SRCC. Qed.

    Lemma ktid_ninit : 
      ktid <> tid_init. 
    Proof. 
      edestruct cstate_cont; [apply SRCC|]. 
      desc. subst x.
      intros kTID.
      edestruct ES.init_tid_K; [apply SRCC|].
      do 2 eexists. splits; eauto.
    Qed.

    Lemma kE_inE : 
      kE ⊆₁ SE. 
    Proof. 
      edestruct cstate_cont; [apply SRCC|]. 
      desc. subst x. 
      intros x kSBx.
      eapply ES.cont_sb_domE; eauto.
      apply SRCC.
    Qed.

    Lemma wf_cont_state : 
      wf_thread_state ktid st. 
    Proof. 
      edestruct cstate_cont. 
      { apply SRCC. }
      eapply contwf; eauto. 
      apply SRCC. desf.
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
      admit. 
    Admitted.

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
        eapply e2a_same_Einit in INITx; try apply SRCC.
        unfolder in INITx. 
        destruct INITx as [y [INITy e2aEQ]].
        (* TODO : proof x = y *)
        admit. }
      assert (certE (e2a x)) as CERTEx.
      { eapply steps_preserve_E; eauto.
        { apply wf_cont_state. }
        apply ilbl_steps_in_steps.
        apply SRCC. }
      assert (~ SEinit x) as nINITx.
      { intros INITx.
        assert (GEinit (e2a x)) as GINITx.
        { eapply e2a_same_Einit.
          1-3 : apply SRCC.
          basic_solver. }
        edestruct acts_rep.
        { apply wf_cont_state. }
        { apply CONTEx. }
        unfolder in GINITx.
        unfold is_init in GINITx.
        desf. }
      unfold CertGraph.certLab.
      destruct 
        (excluded_middle_informative (certE (e2a x)))
        as [CertEx | nCertEx].
      { apply kE_lab; auto. basic_solver. }
      exfalso. auto.
    Admitted.
    
    Lemma cert_ex_cov_iss_lab : 
      eq_dom (certX ∩₁ e2a ⋄₁ (C' ∪₁ I')) Slab (Glab ∘ e2a).
    Proof. 
      rewrite set_inter_union_l.
      apply eq_dom_union. split. 
      { arewrite (X ∩₁ SNTid ktid ∩₁ e2a ⋄₁ (C' ∪₁ I') ⊆₁ 
                  X ∩₁ e2a ⋄₁ (C ∪₁ I)).
        { admit. }
        eapply ex_cov_iss_lab. apply SRCC. }
      intros x [KSBx e2aCIx].
      erewrite kE_cert_lab; auto.
      unfold compose.
      erewrite <- cslab 
        with (G := G); [auto | apply SRCC|].
      unfold D. do 4 left. basic_solver.
    Admitted.

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
    Proof. admit. Admitted.

    Lemma rel_ew_cert_ex : 
      dom_rel (Srelease ⨾ Sew ⨾ ⦗ certX ⦘) ⊆₁ certX.
    Proof.
      rewrite ew_in_eq_ew_ex_iss_ew; [|apply SRCC].
      rewrite !seq_union_l, !seq_union_r, !dom_union, !seqA.
      unionL.
      { arewrite (Srelease ⨾ eq ≡ Srelease).
        { basic_solver. }
        rewrite rel_in_ex_cov_rel_sb; [|apply SRCC].
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

    Lemma cert_ex_hb_prcl :
      dom_rel (Shb ⨾ ⦗ certX ⦘) ⊆₁ certX.  
    Proof. admit. Admitted.
    (*   rewrite hb_in_ex_cov_hb_sb; [|apply SRCC]. *)
    (*   rewrite seq_union_l, dom_union. unionL. *)
    (*   2: eapply a2e_sb_prcl; eauto; apply SRCC. *)
    (*   rewrite hfC. unfold cert_dom. basic_solver 10. *)
    (* Qed. *)

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

    Lemma e2a_jfrmw : e2a □ (Sjf ⨾ Srmw) ⊆ Grf ⨾ Grmw.
    Proof.
      assert (ES.Wf S) as WF by apply SRCC.
      arewrite (Sjf ⨾ Srmw ⊆ Sjf ⨾ ⦗dom_rel (Srmw)⦘ ⨾ Srmw)
        by basic_solver 10.
      rewrite (dom_r WF.(ES.jfD)) at 1.
      rewrite !seqA.
      arewrite (⦗SR⦘ ⨾ ⦗dom_rel (Srmw)⦘ ⊆ ⦗DR⦘).
      { unfold SimRelJF.DR. basic_solver 10. }
      rewrite <- seqA.
      rewrite collect_rel_seqi.
      rewrite e2a_rmw, e2a_jfDR; try by apply SRCC.
      done.
    Qed.

    Lemma e2a_rs : e2a □ Srs ⊆ Grs. 
    Proof. 
      assert (ES.Wf S) as WF by apply SRCC.
      assert (simrel_e2a S G) as SRE2A by apply SRCC.
      rewrite rs_alt; auto.
      rewrite !collect_rel_seqi.
      rewrite !set_collect_eqv.
      rewrite !e2a_W; eauto.
      repeat apply seq_mori; eauto with hahn.
      2: { rewrite collect_rel_crt.
           eauto using clos_refl_trans_mori, e2a_jfrmw. }
      rewrite ES.sbE; auto.
      rewrite wf_sbE.
      rewrite <- !restr_relE.
      rewrite <- restr_inter_absorb_r.
      rewrite <- restr_inter_absorb_r with (r':=same_loc Slab).
      rewrite collect_rel_cr.
      rewrite collect_rel_interi. 
      apply clos_refl_mori, inter_rel_mori. 
      2: by apply e2a_same_loc.
      rewrite !restr_relE, <- wf_sbE, <- ES.sbE; auto.
      eapply e2a_sb; eauto; apply SRCC.
    Qed.

    Lemma e2a_release : e2a □ Srelease ⊆ Grelease.
    Proof. 
      rewrite release_alt; auto.
      rewrite !collect_rel_seqi, !collect_rel_cr, !collect_rel_seqi.
      rewrite !set_collect_eqv.
      arewrite (SE ∩₁ (SF ∪₁ SW) ⊆₁ SE) by basic_solver.
      rewrite e2a_Rel, e2a_rs, e2a_sb, e2a_F.
      { unfold imm_s_hb.release. basic_solver 10. }
      all: eauto; apply SRCC.
    Qed.

    Lemma e2a_jfacq : e2a □ Sjf ⨾ (Ssb ⨾ ⦗SF⦘)^? ⨾ ⦗SAcq⦘ ⊆
                      Grf ⨾ (Gsb ⨾ ⦗GF⦘)^? ⨾ ⦗GAcq⦘.
    Proof.
      assert (ES.Wf S) as WF by apply SRCC.
      assert (simrel_e2a S G) as SRE2A by apply SRCC.
      inv SRE2A.
      arewrite (Ssb ⨾ ⦗SF⦘ ⊆ Ssb ⨾ ⦗SE∩₁SF⦘).
      { rewrite (dom_r WF.(ES.sbE)) at 1. basic_solver 10. }
      arewrite (Sjf ⨾ (Ssb ⨾ ⦗SE ∩₁ SF⦘)^? ⨾ ⦗SAcq⦘ ⊆
                Sjf ⨾ (Ssb ⨾ ⦗SE ∩₁ SF⦘)^? ⨾ ⦗SE∩₁SAcq⦘).
      { rewrite (dom_r WF.(ES.jfE)) at 1. basic_solver 10. }
      arewrite (Sjf ⨾ (Ssb ⨾ ⦗SE ∩₁ SF⦘)^? ⨾ ⦗SE ∩₁ SAcq⦘ ⊆
                Sjf ⨾ ⦗DR⦘ ⨾ (Ssb ⨾ ⦗SE ∩₁ SF⦘)^? ⨾ ⦗SE ∩₁ SAcq⦘).
      2: { rewrite <- !seqA.
           do 2 rewrite collect_rel_seqi.
           rewrite e2a_jfDR; auto.
           rewrite !collect_rel_cr, !collect_rel_seqi, !set_collect_eqv.
           rewrite e2a_sb; eauto; try apply SRCC.
           rewrite e2a_F, e2a_Acq; eauto; try apply SRCC.
           arewrite (GE ∩₁ GF ⊆₁ GF) by basic_solver.
           arewrite (GE ∩₁ GAcq ⊆₁ GAcq) by basic_solver. }
      rewrite crE. rewrite !seq_union_l, !seq_union_r, !seq_id_l.
      apply union_mori.
      { rewrite (dom_r WF.(ES.jfD)) at 1.
        rewrite !seqA.
        arewrite (⦗SR⦘ ⨾ ⦗SE ∩₁ SAcq⦘ ⊆ ⦗SR ∩₁ SE ∩₁ SAcq⦘ ⨾ ⦗SE ∩₁ SAcq⦘)
          by basic_solver.
        arewrite (SR ∩₁ SE ∩₁ SAcq ⊆₁ DR).
        2: done.
        unfold SimRelJF.DR.
        basic_solver 10. }
      rewrite (dom_r WF.(ES.jfD)) at 1.
      rewrite !seqA.
      arewrite (Ssb ⨾ ⦗SE ∩₁ SF⦘ ⊆ ⦗h □₁ C'⦘ ⨾ Ssb ⨾ ⦗SE ∩₁ SF⦘).
      2: { arewrite (⦗SR⦘ ⨾ ⦗h □₁ C'⦘ ⊆ ⦗DR⦘).
           2: done.
           unfold SimRelJF.DR. basic_solver 10. }
    Admitted.

    Lemma e2a_hb : e2a □ Shb ⊆ Ghb.
    Proof. 
      assert (e2a □₁ SE ⊆₁ GE) as EE by apply SRCC.
      unfold hb, imm_s_hb.hb.
      rewrite collect_rel_ct.
      apply clos_trans_mori.
      rewrite collect_rel_union.
      apply union_mori.
      { eapply e2a_sb; eauto; apply SRCC. }
      unfold Consistency.sw.
      rewrite collect_rel_seqi.
      rewrite e2a_release. by rewrite e2a_jfacq.
    Qed.

    Lemma e2a_jf : e2a □ Sjf ⊆ Gvf.
    Proof.
      assert (ES.Wf S) as WF by apply SRCC.
      assert (simrel_e2a S G) as SRE2A by apply SRCC.
      rewrite jf_in_sim_jf; auto.
      arewrite (Ssim_jf ⊆ Ssim_vf).
      unfold sim_vf.
      rewrite (dom_l WF.(ES.ewE)).
      rewrite (dom_l WF.(ES.ewD)). rewrite !seqA.
      arewrite (⦗SE⦘ ⨾ ⦗SW⦘ ⊆ ⦗SE∩₁SW⦘) by basic_solver.
      rewrite furr_alt; auto; try apply SRCC.
      rewrite !collect_rel_seqi, !collect_rel_cr, !set_collect_eqv.
      rewrite e2a_jfDR; auto.
      rewrite e2a_hb. rewrite e2a_W; eauto.
      arewrite (e2a □ (e2a ⋄ sc) ⊆ sc) by basic_solver.
      arewrite (GE ∩₁ GW ⊆₁ GW) by basic_solver.
      rewrite e2a_ew; eauto.
      arewrite (⦗GW⦘ ⨾ eq ⊆ ⦗GW⦘) by basic_solver.
    Qed.

  End SimRelCertProps. 

End SimRelCert.