Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CertExecution2 CertExecutionMain
     CombRelations SimTraversal SimulationRel AuxRel.
Require Import AuxRel AuxDef EventStructure Consistency EventToAction LblStep 
        ImmProperties CertGraph CertRf 
        SimRelCont SimRelEventToAction SimRel. 

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
  
  Notation "'Gsb'" := (G.(sb)).
  Notation "'Grmw'" := G.(rmw).
  Notation "'Grf'" := (G.(rf)).
  Notation "'Gco'" := (G.(co)).

  Notation "'Grs'" := (G.(imm_s_hb.rs)).
  Notation "'Grelease'" := (G.(imm_s_hb.release)).
  Notation "'Ghb'" := (G.(imm_s_hb.hb)).

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

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

      hgfix : fixset (ES.cont_sb_dom S k) (h ∘ (e2a S));

      sr_a2e_h : simrel_a2e S h (cert_dom G TC ktid st);

      hlab : eq_dom (C ∪₁ I ∪₁ contE) (Slab ∘ h) certLab;
      hfeq : eq_dom (C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘) ∩₁ GNTid ktid)) f h; 

      hrel_iss_cov : dom_rel (Srelease ⨾ Sew ⨾ ⦗ h □₁ I ⦘) ⊆₁ h □₁ C;

      (* imgcc : ⦗ f □₁ sbq_dom ⦘ ⨾ Scc ⨾ ⦗ h □₁ sbq_dom ⦘ ⊆ *)
      (*         ⦗ h □₁ GW ⦘ ⨾ Sew ⨾ Ssb⁼ ; *)
    }.

  (* Definition sim_add_jf (r : eventid) (S' : ES.t) : Prop := *)
  (*   ⟪ RR : is_r (ES.lab S') r ⟫ /\ *)
  (*   exists w, *)
  (*     ⟪ wHDOM : (h □₁ hdom) w  ⟫ /\ *)
  (*     ⟪ NEW_RF : new_rf (e2a S' w) (e2a S' r) ⟫ /\ *)
  (*     ⟪ SSJF' : S'.(ES.jf) ≡ S.(ES.jf) ∪ singl_rel w r ⟫. *)

  (* Definition sim_add_ew (w : eventid) (S S' : ES.t) : Prop := *)
  (*   ⟪ WW : is_w (ES.lab S') w ⟫ /\ *)
  (*   exists (ws : eventid -> Prop), *)
  (*     ⟪ gws : e2a S' □₁ ws ⊆₁ eq (e2a S' w) ⟫ /\ *)
  (*     ⟪ wsIN : ws ⊆₁ dom_rel (Sew^? ⨾ ⦗ f □₁ I ⦘) ⟫ /\ *)
  (*     ⟪ SSEW' : S'.(ES.ew) ≡ S.(ES.ew) ∪ (ws × eq w)^⋈ ⟫. *)

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
      GEinit ⊆₁ e2a S □₁ ES.cont_sb_dom S k. 
    Proof. 
      erewrite <- e2a_same_Einit.
      2-4 : eapply SRCC.
      apply set_collect_mori; auto. 
        by apply SEinit_in_cont_sb_dom.
    Qed.

    Lemma cont_sb_dom_in_hhdom :
      ES.cont_sb_dom S k ⊆₁ h □₁ hdom.
    Proof.
      unfold cert_dom.
      arewrite (ES.cont_sb_dom S k ≡₁ h □₁ (e2a S □₁ ES.cont_sb_dom S k)) at 1.
      { rewrite set_collect_compose.
        apply fixset_set_fixpoint.
        apply SRCC. }
      erewrite set_union_minus with (s := ES.cont_sb_dom S k) (s' := SEinit).
      2 : by apply SEinit_in_cont_sb_dom.
      rewrite !set_collect_union.
      apply set_subset_union_l. split.
      { arewrite (acts_set (ProgToExecution.G st) ≡₁ 
                           e2a S □₁ (ES.cont_sb_dom S k \₁ SEinit)).
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
        (h □₁ (e2a S □₁ (ES.cont_sb_dom S k \₁ SEinit)) ≡₁ 
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
      1 : fold (compose (e2a S) h y').
      2 : fold (compose (e2a S) h x').
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
        subst z. fold (compose (e2a S) f a).
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

  End SimRelCertProps. 

End SimRelCert.