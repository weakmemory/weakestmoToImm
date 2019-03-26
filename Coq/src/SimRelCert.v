Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CertExecution2 CertExecutionMain
     CombRelations SimTraversal SimulationRel AuxRel.
Require Import AuxRel AuxDef EventStructure Consistency EventToAction LblStep 
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
  Variable f : actid -> eventid.
  Variable h : actid -> eventid.
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

  Notation "'Gvf'" := (furr G sc).

  Notation "'ktid'" := (ES.cont_thread S k) (only parsing).

  Notation "'E0'" := (E0 G TC' ktid).

  Notation "'new_rf'" := (cert_rf G sc TC' ktid).
  
  Notation "'contG'" := st.(ProgToExecution.G).
  Notation "'certG'" := st'.(ProgToExecution.G).

  Notation "'contE'" := contG.(acts_set).
  Notation "'certE'" := certG.(acts_set).

  Notation "'certLab'" := (certLab G st').

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
      cstate_q_cont : Kstate (k, st);
      cstate_reachable : (step ktid)＊ st st';
      cstate_covered : C ∩₁ GTid ktid ⊆₁ contE; 
    }.

  Record simrel_cert :=
    { sim_com : simrel_common prog S G sc TC f;

      cert : cert_graph G sc TC TC' ktid st';
      cstate : simrel_cstate; 

      tr_step : isim_trav_step G sc ktid TC TC';

      (* TODO : we need to simplify this property somehow *)
      hgfix : fixset (ES.cont_sb_dom S k) (h ∘ e2a);

      sr_a2e_h : simrel_a2e S h (cert_dom G TC ktid st);

      hlab : eq_dom (C ∪₁ I ∪₁ contE) (Slab ∘ h) certLab;
      hfeq : eq_dom (C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘) ∩₁ GNTid ktid)) f h; 

      hrel_iss_cov : dom_rel (Srelease ⨾ Sew ⨾ ⦗ h □₁ I ⦘) ⊆₁ h □₁ C;

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

    Lemma wf_cont_state : 
      wf_thread_state (ES.cont_thread S k) st. 
    Proof. 
      edestruct cstate_q_cont. 
      { apply SRCC. }
      eapply contwf; eauto. 
      apply SRCC. desf.
    Qed.

    Lemma htid : 
      eq_dom hdom (Stid ∘ h) Gtid.
    Proof. eapply a2e_tid. eapply SRCC. Qed.

    Lemma hfC : 
      f □₁ C ≡₁ h □₁ C. 
    Proof. 
      eapply set_collect_eq_dom.
      eapply eq_dom_mori; 
        try eapply hfeq; auto.
      red. basic_solver.
    Qed.

    Lemma himgInit :
      SEinit ≡₁ h □₁ GEinit.
    Proof.
      (* etransitivity. *)
      (* { apply fimgInit. apply SRCC. } *)
      (* eapply set_collect_eq_dom. *)
      admit.
    Admitted.
    
    Lemma SEinit_in_cont_sb_dom : 
      SEinit ⊆₁ ES.cont_sb_dom S k.
    Proof. 
      eapply ES.cont_sb_dom_Einit; [apply SRCC|].
      edestruct cstate_q_cont; [apply SRCC|].
      desf. apply KK.
    Qed.

    Lemma GEinit_in_e2a_cont_sb_dom : 
      GEinit ⊆₁ e2a □₁ ES.cont_sb_dom S k. 
    Proof. 
      erewrite <- e2a_same_Einit.
      2-4: by eapply SRCC.
      apply set_collect_mori; auto. 
        by apply SEinit_in_cont_sb_dom.
    Qed.

    Lemma cont_sb_dom_in_hhdom :
      ES.cont_sb_dom S k ⊆₁ h □₁ hdom.
    Proof.
      unfold cert_dom.
      arewrite (ES.cont_sb_dom S k ≡₁ h □₁ (e2a □₁ ES.cont_sb_dom S k)) at 1.
      { rewrite set_collect_compose.
        apply fixset_set_fixpoint.
        apply SRCC. }
      erewrite set_union_minus with (s := ES.cont_sb_dom S k) (s' := SEinit).
      2 : by apply SEinit_in_cont_sb_dom.
      rewrite !set_collect_union.
      apply set_subset_union_l. split.
      { arewrite (acts_set (ProgToExecution.G st) ≡₁ 
                  e2a □₁ (ES.cont_sb_dom S k \₁ SEinit)).
        2: by eauto with hahn.
        eapply contstateE; eauto.
        1-2: by apply SRCC.
        edestruct cstate_q_cont; [apply SRCC|]. desf. }
      rewrite <- !set_collect_union.
      apply set_collect_mori; auto. 
      rewrite e2a_same_Einit.
      2-4 : eapply SRCC. 
      eapply GEinit_in_hdom; apply SRCC.
    Qed.

    Lemma cfk_hdom : 
      h □₁ hdom ∩₁ ES.cont_cf_dom S k ≡₁ ∅.
    Proof. 
      assert (ES.Wf S) as WFS by apply SRCC.
      edestruct cstate_q_cont as [st_ [stEQ KK]]; 
        [apply SRCC|].
      red; split; [|basic_solver].
      rewrite cert_dom_alt; [|apply SRCC].
      rewrite !set_collect_union. 
      rewrite set_inter_union_l.
      apply set_subset_union_l; split. 
      { rewrite ES.cont_cf_Tid_; eauto.  
        intros x [HH TIDx]. red.
        destruct HH as [a [DOMa Ha]].
        edestruct DOMa as [CIa NTIDa].
        subst x. apply NTIDa.
        erewrite <- a2e_tid; 
          [eauto | | eapply DOMa]. 
        eapply fixset_mori; 
          [| eauto| eapply SRCC].
        rewrite cert_dom_alt; [|apply SRCC]. 
        red. basic_solver 10. }
      erewrite contstateE;
        [|apply SRCC | apply SRCC | rewrite stEQ; eapply KK].
      arewrite 
        (h □₁ (e2a □₁ (ES.cont_sb_dom S k \₁ SEinit)) ≡₁ 
           ES.cont_sb_dom S k \₁ SEinit).
      { rewrite set_collect_compose.
        symmetry. eapply fixset_set_fixpoint.
        eapply fixset_mori; eauto; 
          [| eapply hgfix; eapply SRCC].  
        red. basic_solver. }
      rewrite ES.cont_cf_cont_sb; eauto. 
      unfolder. ins. desf. 
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
      edestruct cstate_q_cont as [lstate]; [apply SRCC|]. desf.
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

    Lemma hsb : 
      h □ (Gsb ⨾ ⦗ hdom ⦘) ⊆ Ssb. 
    Proof.
      rewrite hdom_sb_prefix; auto.
      intros x y SB. red in SB. desf.
      destruct_seq SB as [AA BB].
      assert (~ is_init y') as YNINIT.
      { apply no_sb_to_init in SB. by destruct_seq_r SB as YY. }

      apply wf_sbE in SB. destruct_seq SB as [EX EY]. 

      assert (SE (h x')) as HEX.
      { eapply SRCC.(sr_a2e_h). eexists. split; [|by eauto]; eauto. }
      assert (SE (h y')) as HEY.
      { eapply SRCC.(sr_a2e_h). eexists. split; [|by eauto]; eauto. }

      assert (~ SEinit (h y')) as HYNINIT.
      { intros JJ. apply himgInit in JJ; auto.
        unfolder in JJ. desc. apply YNINIT.
        erewrite a2e_inj; eauto; try apply SRCC.
        unfold cert_dom. do 2 left. 
        eapply init_covered; try apply SRCC.
        basic_solver. }

      set (CC := SB). apply sb_tid_init in CC. desf.
      2: { apply ES.sb_init; [by apply SRCC|].
           split. 2: by split.
           apply himgInit; auto. eexists. split; eauto.
           split; auto. }
      assert (~ Scf (h x') (h y')) as NCF.
      { intros JJ.
        eapply a2e_ncf. 
        { apply SRCC.(sr_a2e_h). }
        apply seq_eqv_l. split; [|apply seq_eqv_r; split; eauto].
        all: by eexists; split; [|by eauto]. }
      edestruct ES.same_thread as [PP _]; [by apply SRCC|].
      specialize (PP (h x') (h y')).

      assert (~ is_init x') as XNINIT.
      { intros XX. apply YNINIT.
        eapply tid_initi; eauto; try by apply SRCC.
        split; auto.
        rewrite <- CC. destruct x'; desf. }
      assert (~ SEinit (h x')) as HXNINIT.
      { intros JJ. apply himgInit in JJ; auto.
        unfolder in JJ. desc. apply XNINIT.
        erewrite a2e_inj; try apply SRCC.(sr_a2e_h); eauto. 
        unfold cert_dom. do 2 left.
        eapply init_covered; try apply SRCC.
        basic_solver. }

      destruct PP as [PP|]; [| |done].
      { apply seq_eqv_l. split.
        2: apply seq_eqv_r; split.
        1,3: by split.
        do 2 (rewrite <- htid in CC; auto). }
      destruct_seq PP as [XX YY].
      red in PP. desf.
      { eapply SRCC.(sr_a2e_h) in PP; eauto. subst. by apply sb_irr in SB. }
      exfalso.
      eapply sb_irr. eapply sb_trans; eauto.
      eapply e2a_sb; eauto; try apply SRCC. 
      do 2 eexists. splits; eauto.
      1: fold (compose e2a h y').
      2: fold (compose e2a h x').
      all: eapply a2e_fix; [by apply SRCC|]; auto. 
    Qed.

    Lemma hlabCI : 
      eq_dom (C ∪₁ I) (Slab ∘ h) Glab.
    Proof. 
      red. ins. etransitivity.
      { eapply hlab; eauto. basic_solver. }
      eapply cslab; [apply SRCC|]. 
      do 4 left.
      (* it should be easy, but it seems there are no suitable lemmas *)
      admit. 
    Admitted.

    Lemma rel_ew_hD : 
      dom_rel (Srelease ⨾ Sew ⨾ ⦗ h □₁ hdom ⦘) ⊆₁ h □₁ hdom.  
    Proof.
      rewrite ew_in_eq_ew_fI_ew; [|apply SRCC].
      rewrite !seq_union_l, !seq_union_r, !dom_union, !seqA.
      unionL.
      { arewrite (Srelease ⨾ eq ≡ Srelease).
        { basic_solver. }
        rewrite frel_in_Crel_sb; [|apply SRCC].
        relsf. rewrite !seqA. splits.
        { rewrite dom_seq. rewrite hfC.
          unfold cert_dom. basic_solver 10. }
        rewrite crE. relsf. splits; auto.
        erewrite a2e_sb_prcl; eauto. apply SRCC. }
      do 2 rewrite <- seqA. 
      rewrite dom_seq, !seqA.
      etransitivity. 
      { eapply rel_fI_fC. apply SRCC. } 
      rewrite hfC. unfold cert_dom. basic_solver 10.
    Qed.

    Lemma hb_hD :
      dom_rel (Shb ⨾ ⦗ h □₁ hdom ⦘) ⊆₁ h □₁ hdom.  
    Proof.
      rewrite hb_in_fChb_sb; [|apply SRCC].
      rewrite seq_union_l, dom_union. unionL.
      2: eapply a2e_sb_prcl; eauto; apply SRCC.
      rewrite hfC. unfold cert_dom. basic_solver 10.
    Qed.

    Lemma hb_rel_ew_hD :
      dom_rel (Shb^? ⨾ Srelease ⨾ Sew ⨾ ⦗ h □₁ hdom ⦘) ⊆₁ h □₁ hdom.  
    Proof. 
      rewrite crE with (r := Shb).
      relsf. split.
      { by apply rel_ew_hD. }
      intros x [y [z [HB REL]]].
      eapply hb_hD; auto.
      eexists. apply seq_eqv_r. split; eauto.
      apply rel_ew_hD; auto. basic_solver.
    Qed.

    Lemma jf_hD : 
      dom_rel (Sjf ⨾ ⦗ ES.cont_sb_dom S k ⦘) ⊆₁ dom_rel (Sew ⨾ ⦗ h □₁ hdom ⦘).  
    Proof.
      assert (ES.Wf S) as WFS by apply SRCC.
      rewrite ES.jfi_union_jfe. relsf. splits.
      { arewrite (Sjfi ≡ ⦗ SE ∩₁ SW ⦘ ⨾ Sjfi).
        { rewrite ES.jfiE, ES.jfiD; auto. basic_solver. }
        rewrite dom_eqv1. 
        rewrite cont_sb_dom_in_hhdom.
        arewrite (Sjfi ⊆ Ssb).
        rewrite a2e_sb_prcl; [|apply SRCC].
        rewrite <- ES.ew_refl; auto.
        basic_solver 10. }
      rewrite seq_eqv_r with (r := Sjfe).
      intros x [y [JFE KSB]].
      edestruct jfe_fI as [z HH]. 
      { apply SRCC. }
      { red. eauto. }
      apply seq_eqv_r in HH. 
      destruct HH as [EW fI].
      eexists. apply seq_eqv_r.
      splits; eauto.
      unfold cert_dom.
      apply set_collect_union. left.
      apply set_collect_union. right.
      eapply set_collect_eq_dom.
      { eapply eq_dom_mori; [| eauto | |].
        3 : { intros a HH. symmetry. eapply hfeq; eauto. }
        all : eauto.
        red. basic_solver 10. }
      destruct fI as [a [fI EQa]].
      red; eexists; splits; eauto.
      red. splits.
      { basic_solver 10. }
      intros GTID.
      set (HH := JFE).
      eapply jfe_alt in HH. 
      2-3 : apply SRCC.
      apply seq_eqv_l in HH.
      destruct HH as [Enix [JF nSTID]].
      apply nSTID. red. 
      arewrite (Stid x = Stid z).
      { edestruct ES.ewc; eauto.
        by eapply ES.cf_same_tid. }
      arewrite (Stid z = Gtid a).
      { etransitivity; [eapply e2a_tid|].
        subst z. fold (compose e2a f a).
        erewrite a2e_fix; auto.
        { apply SRCC. }
        basic_solver 10. }
      arewrite (Stid y = ES.cont_thread S k); auto.
      eapply ES.cont_sb_tid in KSB; auto.
      2 : { edestruct cstate_q_cont; [apply SRCC|]. desf. apply KK. }
      destruct KSB as [Eiy | TIDy]; auto.
      exfalso. eapply ES.jf_nEinit; eauto.
      apply seq_eqv_r; eauto.
    Qed.

    Lemma necf_hD :
      restr_rel (h □₁ hdom) Secf ⊆ ∅₂.
    Proof. 
      unfold restr_rel, ecf.
      intros a b [ECF [Hx Hy]].
      destruct ECF as [c [tHB [d [CF HB]]]].
      eapply a2e_ncf; [apply SRCC.(sr_a2e_h)|].
      apply restr_relE. unfold restr_rel.
      splits; eauto.
      { unfolder in tHB; desf.
        eapply hb_hD; auto. basic_solver 10. }
      unfolder in HB; desf.
      eapply hb_hD; auto. basic_solver 10.
    Qed.

    Lemma hvis : 
      h □₁ (C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘) ∩₁ GNTid ktid)) ⊆₁ vis S. 
    Proof. 
      etransitivity. 
      { eapply set_collect_eq_dom. apply SRCC. }
      etransitivity; [| eapply fvis; apply SRCC]. 
      apply set_collect_mori; [done|].
      basic_solver 10.
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