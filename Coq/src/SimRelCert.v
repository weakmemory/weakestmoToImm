Require Import Omega.
Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution
     Traversal TraversalConfig SimTraversal SimTraversalProperties
     Prog ProgToExecution ProgToExecutionProperties Receptiveness
     imm_common imm_s imm_s_hb SimulationRel
     CertExecution2 CertExecutionMain
     SubExecution CombRelations AuxRel.
Require Import AuxRel AuxDef EventStructure Construction Consistency 
        SimRel LblStep CertRf CertGraph EventToAction ImmProperties.
Require Import Coq.Logic.FunctionalExtensionality Classical_Prop.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelCert.
  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G  : execution.
  Variable GPROG : program_execution prog G.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable TC': trav_config.
  
  Variable f : actid -> eventid.
  Variable h : actid -> eventid.
  Variable q : cont_label.
  Notation "'qtid'" := (ES.cont_thread S q) (only parsing).

  (* A state in a continuation related to q in S. *)
  Variable state : ProgToExecution.state.

  (* A state, which is reachable from 'state' and which represents a graph certification. *)
  Variable state' : ProgToExecution.state.

  Notation "'new_rf'" := (cert_rf G sc TC' qtid).
  
  Notation "'certG'" := state'.(ProgToExecution.G).

  Notation "'g'" := (e2a S).

  Notation "'SE'" := S.(ES.acts_set).
  Notation "'SEinit'" := S.(ES.acts_init_set).
  Notation "'Stid'" := (S.(ES.tid)).
  Notation "'Slab'" := (S.(ES.lab)).
  Notation "'Sloc'" := (loc S.(ES.lab)).
  Notation "'Srelease'" := (S.(Consistency.release)).
  Notation "'K'"  := S.(ES.cont_set).

  Notation "'Stid_' t" := (fun x => Stid x = t) (at level 1).

  Notation "'Ssb'" := (S.(ES.sb)).
  Notation "'Sjfe'" := (S.(ES.jfe)).
  Notation "'Srf'" := (S.(ES.rf)).
  Notation "'Srfe'" := (S.(ES.rfe)).
  Notation "'Sco'" := (S.(ES.co)).
  Notation "'Scf'" := (S.(ES.cf)).
  Notation "'Sew'" := (S.(ES.ew)).

  Notation "'Scc'" := (S.(cc)).
  Notation "'Ssw'" := (S.(sw)).
  Notation "'Shb'" := (S.(hb)).

  Notation "'SR'" := (fun a => is_true (is_r Slab a)).
  Notation "'SW'" := (fun a => is_true (is_w Slab a)).
  Notation "'SF'" := (fun a => is_true (is_f Slab a)).

  Notation "'SRel'" := (fun a => is_true (is_rel Slab a)).
  
  Notation "'GE'" := G.(acts_set).
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gtid'" := (tid).
  Notation "'Grmw'" := G.(rmw).
  Notation "'Gvf'" := (furr G sc).

  Notation "'GR'" := (fun a => is_true (is_r Glab a)).
  Notation "'GW'" := (fun a => is_true (is_w Glab a)).
  
  Notation "'Gsb'" := (G.(sb)).
  Notation "'Ghb'" := (G.(imm_s_hb.hb)).
  Notation "'Grf'" := (G.(rf)).
  Notation "'Grfe'" := (G.(rfe)).
  Notation "'Gco'" := (G.(co)).

  Notation "'certE'" := certG.(acts_set).
  Notation "'certRmw'" := (certG.(rmw)).

  Definition certLab (e : actid) : label :=
    if excluded_middle_informative (certE e)
    then certG.(lab) e
    else Glab e.
  
  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).
  Notation "'C''"  := (covered TC').
  Notation "'I''"  := (issued TC').

  Notation "'E0'" := (Tid_ qtid ∩₁ (C' ∪₁ dom_rel (Gsb^? ⨾ ⦗ I' ⦘))).

  Notation "'sbq_dom'" := (g □₁ ES.cont_sb_dom S q) (only parsing).
  Notation "'fdom'" := (C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘))) (only parsing).
  
  Definition cert_dom state q :=
    (C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘) ∩₁ NTid_ (ES.cont_thread S q)) ∪₁
      state.(ProgToExecution.G).(acts_set)).
  Notation "'hdom'" :=  (cert_dom state q) (only parsing).
  
  Definition Kstate : cont_label * ProgToExecution.state -> Prop :=
    fun l =>
      match l with
      | (ll, lstate) =>
        exists (st : (thread_lts (ES.cont_thread S ll)).(Language.state)),
          ⟪ SSTATE : lstate = st ⟫ /\
          ⟪ KK     : K (ll, existT _ _ st) ⟫
      end.
  
  Lemma Kstate_spec c (st : (thread_lts (ES.cont_thread S c)).(Language.state))
        (KK : K (c, existT _ _ st)) :
    exists (st' : ProgToExecution.state),
      ⟪ KST : Kstate (c, st') ⟫ /\
      ⟪ EQST : st = st' ⟫.
  Proof.
    exists st. splits; auto. red.
    eexists. splits; eauto.
  Qed.
  
  Record simrel_cert :=
    { sim : simrel_common prog S G sc TC f;

      cstate_stable : stable_state qtid state';
      state_q_cont  : Kstate (q, state);
      cstate_reachable : (step qtid)＊ state state';

      cert : cert_graph G sc TC TC' qtid state';

      tr_step : isim_trav_step G sc qtid TC TC';

      ghtrip : ⦗ hdom ⦘ ⨾ ↑ (g ∘ h) ⊆ eq;
      
      hgfix_sbk : fixset (ES.cont_sb_dom S q) (h ∘ g); 

      jfehI  : dom_rel Sjfe ⊆₁ dom_rel (Sew^? ⨾ ⦗ h □₁ I ⦘);

      hinj     : inj_dom_s hdom h;
      himg     : h □₁ hdom ⊆₁ SE;
      himgInit : SEinit ≡₁ h □₁ (GE ∩₁ is_init);
      hoth     : (h □₁ set_compl hdom) ∩₁ SE ≡₁ ∅;
      htid     : eq_dom hdom Gtid (Stid ∘ h);

      hlabCI : eq_dom (C ∪₁ I) Glab (Slab ∘ h);
      hlabTHRD : eq_dom sbq_dom certLab (Slab ∘ h);

      hco : h □ ⦗ hdom ⦘ ⨾ Gco ⨾ ⦗ hdom ⦘ ⊆ Sco;

      himgNcf : ES.cf_free S (h □₁ hdom);
      
      complete_fdom :
        (h □₁ hdom) ∩₁ SR ⊆₁ codom_rel (⦗ h □₁ hdom ⦘ ⨾ Srf);

      hfeq  : eq_dom (C ∪₁ fdom \₁ sbq_dom) f h; 

      imgcc : ⦗ f □₁ sbq_dom ⦘ ⨾ Scc ⨾ ⦗ h □₁ sbq_dom ⦘ ⊆
              ⦗ h □₁ GW ⦘ ⨾ Sew ⨾ Ssb⁼ ;

      release_issh_cov : dom_rel (Srelease ⨾ Sew^? ⨾ ⦗ h □₁ I ⦘) ⊆₁ h □₁ C;
    }.

  Definition sim_add_jf (r : eventid) (S' : ES.t) : Prop :=
    ⟪ RR : is_r (ES.lab S') r ⟫ /\
    exists w,
      ⟪ wHDOM : (h □₁ hdom) w  ⟫ /\
      ⟪ NEW_RF : new_rf (e2a S' w) (e2a S' r) ⟫ /\
      ⟪ SSJF' : S'.(ES.jf) ≡ S.(ES.jf) ∪ singl_rel w r ⟫.

  Definition sim_add_ew (w : eventid) (S S' : ES.t) : Prop :=
    ⟪ WW : is_w (ES.lab S') w ⟫ /\
    exists (ws : eventid -> Prop),
      ⟪ gws : e2a S' □₁ ws ⊆₁ eq (e2a S' w) ⟫ /\
      ⟪ wsIN : ws ⊆₁ dom_rel (Sew^? ⨾ ⦗ f □₁ I ⦘) ⟫ /\
      ⟪ SSEW' : S'.(ES.ew) ≡ S.(ES.ew) ∪ (ws × eq w)^⋈ ⟫.

  Lemma hgtrip (SRC : simrel_cert) : ⦗ h □₁ hdom ⦘ ⨾ ↑ (h ∘ g) ⊆ eq.
  Proof. 
    unfold seq, eqv_rel, set_collect, img_rel, inclusion, compose.
    intros x y [z [[zEQ [a [DOM xEQ]]] yEQ]].
    rewrite <- xEQ, yEQ, <- zEQ.
    arewrite (a = g x); auto.
    apply ghtrip; auto.
    apply seq_eqv_l; splits; auto.
    unfold img_rel, compose.
    congruence.
  Qed.

  Lemma C_in_hdom : C ⊆₁ hdom.
  Proof. unfold cert_dom. basic_solver. Qed.

  Lemma sbk_in_hhdom (SRC : simrel_cert) : ES.cont_sb_dom S q ⊆₁ h □₁ hdom.
  Proof.
    unfold cert_dom.
    rewrite set_collect_union.
    arewrite (ES.cont_sb_dom S q ≡₁ h □₁ (g □₁ ES.cont_sb_dom S q)) at 1.
    { rewrite set_collect_compose.
      apply fixset_set_fixpoint.
      apply SRC. }
    arewrite (acts_set (ProgToExecution.G state) ≡₁ g □₁ ES.cont_sb_dom S q).
    2: by eauto with hahn.
    eapply contstateE; eauto.
    { by apply SRC. }
    destruct state_q_cont; auto. desf.
    apply KK.
  Qed.

  Lemma cfk_hdom (SRC : simrel_cert) : ES.cont_cf_dom S q ∩₁ h □₁ hdom ≡₁ ∅.
  Proof. 
    red; split; [|basic_solver].
    unfold cert_dom.
    rewrite !set_collect_union. 
    rewrite !set_inter_union_r.
    apply set_subset_union_l; split. 
    { apply set_subset_union_l; split. 
      { admit. }
      admit. }
    admit. 
  Admitted.

  Lemma cont_sb_dom_dom (WF : ES.Wf S) :
    dom_rel (Ssb ⨾ ⦗ ES.cont_sb_dom S q ⦘) ⊆₁ ES.cont_sb_dom S q.
  Proof.
    intros x [y SB].
    destruct_seq_r SB as YY. red in YY. desf.
    { exfalso. eapply ES.sb_ninit; eauto.
      apply seq_eqv_r. eauto. }
    red. generalize WF.(ES.sb_trans) YY SB. basic_solver 10.
  Qed.

  Lemma hdom_sb_dom (SRC : simrel_cert) :
    dom_rel (Gsb ⨾ ⦗ hdom ⦘) ⊆₁ hdom.
  Proof.
    assert (tc_coherent G sc TC) as TCCOH by apply SRC.
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
    destruct state_q_cont as [lstate]; auto. desf.
    assert (wf_thread_state (ES.cont_thread S q) lstate) as WFT.
    { eapply contwf; [by apply SRC|]. apply KK. }
    eapply acts_rep in YY; eauto. destruct YY as [yin]. desf.
    rewrite REP in *.
    destruct x; desf.
    red in ESB. desf. rewrite ESB in *.
    apply acts_clos; auto.
    omega.
  Qed.

  Lemma hdom_sb_prefix (SRC : simrel_cert) :
    Gsb ⨾ ⦗ hdom ⦘ ≡ ⦗ hdom ⦘ ⨾ Gsb ⨾ ⦗ hdom ⦘.
  Proof.
    split.
    all: intros x y SB.
    2: { destruct_seq_l SB as AA. apply SB. }
    apply seq_eqv_l. split; auto.
    apply hdom_sb_dom; auto. red. eauto.
  Qed.

  Lemma hsb (SRC : simrel_cert) : h □ (Gsb ⨾ ⦗ hdom ⦘) ⊆ Ssb. 
  Proof.
    rewrite hdom_sb_prefix; auto.
    intros x y SB. red in SB. desf.
    destruct_seq SB as [AA BB].
    assert (~ is_init y') as YNINIT.
    { apply no_sb_to_init in SB. by destruct_seq_r SB as YY. }

    apply wf_sbE in SB. destruct_seq SB as [EX EY]. 

    assert (SE (h x')) as HEX.
    { apply himg; auto. eexists. split; [|by eauto]; eauto. }
    assert (SE (h y')) as HEY.
    { apply himg; auto. eexists. split; [|by eauto]; eauto. }

    assert (~ SEinit (h y')) as HYNINIT.
    { intros JJ. apply himgInit in JJ; auto.
      red in JJ. desf. apply hinj in JJ0; auto. subst.
      destruct JJ. desf. }

    set (CC := SB). apply sb_tid_init in CC. desf.
    2: { apply ES.sb_init; [by apply SRC|].
         split. 2: by split.
         apply himgInit; auto. eexists. split; eauto.
         split; auto. }
    assert (~ Scf (h x') (h y')) as NCF.
    { intros JJ.
      eapply SRC.(himgNcf).
      apply seq_eqv_l. split; [|apply seq_eqv_r; split; eauto].
      all: by eexists; split; [|by eauto]. }
    edestruct ES.same_thread as [PP _]; [by apply SRC|].
    specialize (PP (h x') (h y')).

    assert (~ is_init x') as XNINIT.
    { intros XX. apply YNINIT.
      eapply tid_initi; eauto; [by apply SRC|].
      split; auto.
      rewrite <- CC. destruct x'; desf. }
    assert (~ SEinit (h x')) as HXNINIT.
    { intros JJ. apply himgInit in JJ; auto.
      red in JJ. desf. apply hinj in JJ0; auto. subst.
      destruct JJ. desf. }
    destruct PP as [PP|]; [| |done].
    { apply seq_eqv_l. split.
      2: apply seq_eqv_r; split.
      1,3: by split.
      do 2 (rewrite htid in CC; auto). }
    destruct_seq PP as [XX YY].
    red in PP. desf.
    { apply hinj in PP; auto. subst. by apply sb_irr in SB. }
    exfalso.
    eapply sb_irr. eapply sb_trans; eauto.
    eapply e2a_sb; eauto; try apply SRC. 
    do 2 eexists. splits; eauto.
    all: symmetry; eapply ghtrip; [by apply SRC|].
    all: by apply seq_eqv_l; split; auto.
  Qed.

  Lemma rfeI (SRC : simrel_cert) :
    dom_rel Srfe ⊆₁ dom_rel (Sew^? ⨾ ⦗ h □₁ I ⦘).
  Proof.
    assert (ES.Wf S) as WF by apply SRC.
    unfold ES.rfe, ES.rf, ES.jfe.
    rewrite crE at 1.
    rewrite seq_union_l, !minus_union_l, dom_union, seq_id_l.
    unionL.
    { etransitivity; [|by apply SRC.(jfehI)].
      unfold ES.jfe. basic_solver. }
    intros x [y [[[z [EW JF]] CC] NSB]].
    assert (~ Ssb z y) as AA.
    { intros SB. apply CC.
      apply ES.cf_sb_in_cf; auto.
      eexists. split; eauto.
      apply ES.ewc; auto. }
    edestruct SRC.(jfehI) as [v HH].
    { eexists. split; eauto. }
    destruct_seq_r HH as BB.
    eexists.  apply seq_eqv_r. split; [|by eauto].
    generalize WF.(ES.ew_trans) EW HH. basic_solver.
  Qed.

  Lemma releaseNCsb (SRC : simrel_cert) : ⦗ set_compl (h □₁ C) ⦘ ⨾ Srelease ⊆ Ssb^?.
  Proof.
    assert (ES.Wf S) as WF by apply SRC.
    unfold release at 1, rs. rewrite <- !seqA.
    intros x y [z [HH RFRMW]].
    apply clos_rt_rtn1 in RFRMW.
    induction RFRMW as [|y w [u [RF RMW]]].
    { generalize WF.(ES.sb_trans) HH. basic_solver 10. }
    apply ES.rfi_union_rfe in RF. destruct RF as [RF|RF].
    { apply WF.(ES.rmwi) in RMW. red in RF. 
      generalize WF.(ES.sb_trans) IHRFRMW RF RMW. basic_solver 10. }
    exfalso.
    assert (~ (h □₁ C) x) as CC.
    { generalize HH. basic_solver 10. }
    apply CC. eapply release_issh_cov; auto.
    assert (dom_rel (Sew^? ⨾ ⦗ h □₁ I ⦘) y) as [yy DD].
    { apply rfeI; auto. eexists. eauto. }
    eexists. eexists. split; eauto.
    unfold release, rs. apply clos_rtn1_rt in RFRMW.
    generalize HH RFRMW. basic_solver 40.
  Qed.
  
  Lemma swNCsb (SRC : simrel_cert) : ⦗ set_compl (h □₁ C) ⦘ ⨾ Ssw ⊆ Ssb.
  Proof.
    assert (ES.Wf S) as WF by apply SRC.
    unfold sw.
    arewrite (⦗set_compl (h □₁ C)⦘ ⨾ Srelease ⨾ Srf ⊆ Ssb).
    2: { generalize WF.(ES.sb_trans). basic_solver. }
    rewrite ES.rfi_union_rfe. rewrite !seq_union_r. unionL.
    { sin_rewrite releaseNCsb; auto. unfold ES.rfi.
      generalize WF.(ES.sb_trans). basic_solver. }
    intros x y HH.
    destruct_seq_l HH as DX. exfalso. apply DX.
    destruct HH as [z [REL RFE]].
    eapply release_issh_cov; auto.
    assert (dom_rel (Sew^? ⨾ ⦗ h □₁ I ⦘) z) as [zz DD].
    { apply rfeI; auto. eexists. eauto. }
    eexists. eexists. eauto.
  Qed.

  Lemma sb_hdom_dom (SRC : simrel_cert) : dom_rel (Ssb ⨾ ⦗ h □₁ hdom ⦘) ⊆₁ h □₁ hdom.
  Proof. (* TODO: most likely, we need this in simrel_cert. *) Admitted.

  Lemma sb_hdom_in_hsb (SRC : simrel_cert) : Ssb ⨾ ⦗ h □₁ hdom ⦘ ⊆ h □ Gsb.
  Proof.
    assert (inj_dom_s hdom h) as HD by apply SRC.
    arewrite (Ssb ⨾ ⦗ h □₁ hdom ⦘ ⊆ ⦗ h □₁ hdom ⦘ ;; Ssb ⨾ ⦗ h □₁ hdom ⦘). 
    { intros x y HH. apply seq_eqv_l. split; auto.
      apply sb_hdom_dom; auto. eexists. eauto. }
    rewrite <- restr_relE.
    rewrite <- collect_rel_eqdom_eq. 2: by apply hgtrip.
    rewrite <- collect_rel_compose.
    apply collect_rel_mori; auto.
    rewrite inclusion_restr.
    eapply e2a_sb; apply SRC.
  Qed.
  
  Lemma sbHC_dom (SRC : simrel_cert) : dom_rel (Ssb ⨾ ⦗ h □₁ C ⦘) ⊆₁ h □₁ C.
  Proof.
    rewrite <- seq_eqvK.
    sin_rewrite C_in_hdom.
    sin_rewrite sb_hdom_in_hsb; auto.
    rewrite <- set_collect_eqv.
    rewrite <- collect_rel_seq_r.
    2: { sin_rewrite C_in_hdom. rewrite dom_eqv.
         apply SRC. }
    rewrite sb_covered; [|by apply SRC].
    basic_solver.
  Qed.

  Lemma sbNCNC (SRC : simrel_cert) :
    codom_rel (⦗ set_compl (h □₁ C) ⦘ ⨾ Ssb) ⊆₁ set_compl (h □₁ C).
  Proof.
    intros x [y HH]. destruct_seq_l HH as DX.
    intros DY. apply DX.
    apply sbHC_dom; auto. eexists. apply seq_eqv_r. eauto.
  Qed.

  Lemma hbNCsb (SRC : simrel_cert) : ⦗ set_compl (h □₁ C) ⦘ ⨾ Shb ⊆ Ssb. 
  Proof.
    assert (ES.Wf S) as WF by apply SRC.
    intros x y HH. destruct_seq_l HH as DX.
    red in HH. apply clos_trans_tn1 in HH.
    induction HH as [y [|HH]|y z [HH|HH]]; auto.
    { apply swNCsb; auto. by apply seq_eqv_l. }
    all: eapply ES.sb_trans; eauto.
    apply swNCsb; auto. apply seq_eqv_l. split; auto.
    apply sbNCNC; auto.
    eexists. apply seq_eqv_l. eauto.
  Qed.

  Lemma hb_in_HChb_sb (SRC : simrel_cert) : Shb ⊆ ⦗ h □₁ C ⦘ ⨾ Shb ∪ Ssb. 
  Proof.
    arewrite (Shb ⊆ ⦗h □₁ C ∪₁ set_compl (h □₁ C)⦘ ⨾ Shb).
    { rewrite set_compl_union_id. by rewrite seq_id_l. }
    rewrite id_union, seq_union_l. apply union_mori; [done|].
    apply hbNCsb; auto.
  Qed.

End SimRelCert.

Section SimRelLemmas.

Variable prog : Prog.t.
Variable S : ES.t.
Variable G  : execution.
Variable GPROG : program_execution prog G.

Notation "'g'" := (e2a S).

Notation "'SE' S" := S.(ES.acts_set) (at level 10).
Notation "'SEinit' S" := S.(ES.acts_init_set) (at level 10).
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

Notation "'SR' S" := (fun a => is_true (is_r S.(ES.lab) a)) (at level 10).
Notation "'SW' S" := (fun a => is_true (is_w S.(ES.lab) a)) (at level 10).
Notation "'SF' S" := (fun a => is_true (is_f S.(ES.lab) a)) (at level 10).

Notation "'SPln' S" := (fun a => is_true (is_only_pln S.(ES.lab) a)) (at level 10).
Notation "'SRlx' S" := (fun a => is_true (is_rlx S.(ES.lab) a)) (at level 10).
Notation "'SRel' S" := (fun a => is_true (is_rel S.(ES.lab) a)) (at level 10).
Notation "'SAcq' S" := (fun a => is_true (is_acq S.(ES.lab) a)) (at level 10).
Notation "'SAcqrel' S" := (fun a => is_true (is_acqrel S.(ES.lab) a)) (at level 10).
Notation "'SSc' S" := (fun a => is_true (is_sc S.(ES.lab) a)) (at level 10).

Notation "'Ssame_loc' S" := (same_loc S.(ES.lab)) (at level 10).
Notation "'Ssame_val' S" := (same_val S.(ES.lab)) (at level 10).
Notation "'K' S" := (S.(ES.cont_set)) (at level 10).

Notation "'Stid_' t" := (fun x => Stid x = t) (at level 1).

Notation "'GE'" := G.(acts_set).
Notation "'Glab'" := (G.(lab)).
Notation "'Gtid'" := (tid).
Notation "'Grmw'" := G.(rmw).
Notation "'Gaddr'" := G.(addr).
Notation "'Gdata'" := G.(data).
Notation "'Gctrl'" := G.(ctrl).
Notation "'Grmw_dep'" := G.(rmw_dep).

Notation "'Gtid_' t" := (fun x => tid x = t) (at level 1).
Notation "'GNtid_' t" := (fun x => tid x <> t) (at level 1).

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Notation "'GR'" := (fun a => is_true (is_r Glab a)).
Notation "'GW'" := (fun a => is_true (is_w Glab a)).
Notation "'GR_ex'" := (fun a => R_ex Glab a).

Notation "'Gsb'" := (G.(sb)).
Notation "'Ghb'" := (G.(imm_s_hb.hb)).
Notation "'Grf'" := (G.(rf)).
Notation "'Gco'" := (G.(co)).
Notation "'Gvf'" := (G.(furr)).
Notation "'Gppo'" := (G.(ppo)).

Notation "'thread_syntax' tid"  := 
  (Language.syntax (thread_lts tid)) (at level 10, only parsing).  

Notation "'thread_st' tid" := 
  (Language.state (thread_lts tid)) (at level 10, only parsing).

Notation "'thread_init_st' tid" := 
  (Language.init (thread_lts tid)) (at level 10, only parsing).

Notation "'thread_cont_st' tid" :=
  (fun st => existT _ (thread_lts tid) st) (at level 10, only parsing).

Notation "'sbq_dom' k" := (g □₁ ES.cont_sb_dom S k) (at level 1, only parsing).

Section EventToActionLemmas.

  Variable PROG_NINIT : ~ (IdentMap.In tid_init prog).

  Lemma basic_step_e2a_eq_dom e e' S'
        (WF : ES.Wf S)
        (BSTEP : ESstep.t_basic e e' S S') :
    eq_dom (SE S) (e2a S') (e2a S).
  Proof.
    cdes BSTEP; cdes BSTEP_.
    red. intros x. ins.
    unfold e2a.
    assert (Stid S' x = tid_init <-> Stid S x = tid_init) as AA.
    { red; split; ins;
        [ erewrite <- ESstep.basic_step_tid_eq_dom
        | erewrite ESstep.basic_step_tid_eq_dom
        ]; eauto. }
    assert ((Sloc S') x = (Sloc S) x) as BB.
    { eapply ESstep.basic_step_loc_eq_dom; eauto. }
    desf; try by (exfalso; intuition).
    assert ((Stid S') x = (Stid S) x) as CC.
    { eapply ESstep.basic_step_tid_eq_dom; eauto. }
    assert (ES.seqn S' x = ES.seqn S x) as DD.
    { eapply ESstep.basic_step_seqn_eq_dom; eauto. }
    congruence.
  Qed.

End EventToActionLemmas.

Section SimRelContLemmas.

  Variable TC : trav_config.
  Variable f : actid -> eventid.

  Variable WF : ES.Wf S.
  
  Variable SRK : simrel_cont prog S G TC f.

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Lemma basic_step_simrel_cont k k' e e' S'
        (st st' : thread_st (ES.cont_thread S k))
        (BSTEP_ : ESstep.t_basic_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') : 
    simrel_cont prog S' G TC f.
  Proof. 
    cdes BSTEP_.
    assert (ESstep.t_basic e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (Stid S' (opt_ext e e') = ES.cont_thread S k) as TIDee.
    { edestruct e'; simpl;
        [eapply ESstep.basic_step_tid_e' | eapply ESstep.basic_step_tid_e];
        eauto. }
    split.
    { intros kk lang st'' INK.  
      eapply ESstep.basic_step_cont_set in INK; eauto.
      unfold set_union in INK; desf.
      { erewrite ESstep.basic_step_cont_thread; eauto.
          by eapply SRK in INK. }
      unfold ES.cont_thread.
      rewrite TIDee.
      eapply SRK; eauto. }
    { intros kk st'' KK. 
      eapply ESstep.basic_step_cont_set in KK; eauto.
      unfold set_union in KK. 
      destruct KK as [KK | KK].
      { erewrite ESstep.basic_step_cont_thread; eauto.
        apply SRK.
        erewrite <- ESstep.basic_step_cont_thread; eauto. }
      assert (kk = CEvent (opt_ext e e')) as kkEQ.
      { by inversion KK. }
      rewrite <- kkEQ in *.
      assert (ES.cont_thread S' kk = (ES.cont_thread S k)) as Hkk.
      { subst kk. unfold ES.cont_thread at 1. apply TIDee. }
      rewrite Hkk in *. 
      inversion KK as [HH].
      apply inj_pair2 in HH. 
      rewrite <- HH.
      eapply wf_thread_state_steps.
      { eapply SRK; eauto. }
      eapply ilbl_steps_in_steps.
      do 2 econstructor. 
      eapply STEP. }
    { intros kk st'' KK. 
      eapply ESstep.basic_step_cont_set in KK; eauto.
      unfold set_union in KK. 
      destruct KK as [KK | KK].
      { erewrite ESstep.basic_step_cont_thread; eauto.
        apply SRK.
        erewrite <- ESstep.basic_step_cont_thread; eauto. }
      assert (kk = CEvent (opt_ext e e')) as kkEQ.
      { by inversion KK. }
      rewrite <- kkEQ in *.
      assert (ES.cont_thread S' kk = (ES.cont_thread S k)) as Hkk.
      { subst kk. unfold ES.cont_thread at 1. apply TIDee. }
      rewrite Hkk in *. 
      inversion KK as [HH].
      apply inj_pair2 in HH. 
      rewrite <- HH.
      simpls. 
      unfold ilbl_step in STEP.
      apply seqA in STEP.
      apply seq_eqv_r in STEP.
      desf. }
    { intros thread lprog INP.
      edestruct SRK.(contrun) as [st'' [Kinit ISTEP]]; eauto.    
      eexists; split; eauto.
      eapply ESstep.basic_step_cont_set; eauto.
      left. eauto. }
    { intros thread st'' KK. 
      eapply ESstep.basic_step_cont_set in KK; eauto.
      unfold set_union in KK. 
      destruct KK as [KK | KK].
      { by eapply SRK. }
      exfalso. inversion KK. }
    { intros x st'' KK. 
      eapply ESstep.basic_step_cont_set in KK; eauto.
      unfold set_union in KK. 
      destruct KK as [KK | KK].
      { assert (SE S x) as SEx.
        { eapply ES.K_inEninit; eauto. }
        erewrite ESstep.basic_step_seqn_eq_dom; eauto.
        eapply SRK. erewrite <- ESstep.basic_step_tid_eq_dom; eauto. }
      assert (x = opt_ext e e') as xEQ.
      { by inversion KK. }
      rewrite xEQ in *. 
      rewrite TIDee in KK. 
      inversion KK as [HST].
      apply inj_pair2 in HST. 
      rewrite <- HST.
      simpls.
      edestruct lbl_step_cases as [l [l' HH]]; eauto.
      { eapply contwf; eauto. }
      edestruct HH as [EE _].
      apply opt_to_list_app_singl in EE.
      destruct EE as [eqLBL eqLBL'].
      edestruct e'; simpl.
      { destruct HH as [_ [HH | HH]]. 
        { destruct HH as [_ [_ [_ [LBL _]]]].
          subst l'. rewrite LBL in LABEL'. exfalso. auto. } 
        destruct HH as [IDX _]. 
        erewrite IDX. simpl. 
        erewrite ESstep.basic_step_seqn_e'; eauto.
        2 : { (* TODO: refactor basic_step_seqn lemmas to get rid of this assumption *)
          admit. }             
        arewrite (eindex st = ES.seqn S' e); [|omega].
        edestruct k. 
        { erewrite continit; eauto.
          erewrite ESstep.basic_step_seqn_kinit; eauto. }
        erewrite contseqn; eauto.
        erewrite <- ESstep.basic_step_seqn_kevent; eauto.
        admit. }
      destruct HH as [_ [HH | HH]]. 
      { destruct HH as [IDX _]. 
        erewrite IDX. simpl. 
        edestruct k. 
        { erewrite continit; eauto.
          erewrite ESstep.basic_step_seqn_kinit; eauto. }
        erewrite contseqn; eauto.
        erewrite <- ESstep.basic_step_seqn_kevent; eauto.
        admit. }
      destruct HH as [_ [_ [_ HH]]].
      destruct HH as [ordr [ordw [loc [valr [vaw [_ LBL]]]]]].
      subst l'. rewrite LBL in LABEL'. exfalso. auto. }
    intros a st'' PC KK. 
    eapply ESstep.basic_step_cont_set in KK; eauto.
    unfold set_union in KK. 
    destruct KK as [KK | KK].
    { eapply contpc; eauto. }
    exfalso. 
    (* we need property like `pc < state.eindex` *)
    admit. 
  Admitted.  

  Lemma basic_step_e2a_e k k' e e' S' 
        (st st' : thread_st (ES.cont_thread S k))
        (BSTEP_ : ESstep.t_basic_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') :
    e2a S' e = ThreadEvent (ES.cont_thread S k) (st.(eindex)).
  Proof. 
    cdes BSTEP_.
    assert (ESstep.t_basic e e' S S') as BSTEP.
    { econstructor; eauto. }
    unfold e2a. 
    destruct (excluded_middle_informative ((SEinit S') e)) as [INIT | nINIT]. 
    { exfalso; eapply ESstep.basic_step_acts_ninit_set_e; eauto. } 
    erewrite ESstep.basic_step_tid_e; eauto.  
    edestruct k; simpl.  
    { erewrite ESstep.basic_step_seqn_kinit; [erewrite continit| | |]; eauto. 
      destruct (excluded_middle_informative (tid = tid_init)); auto.
      exfalso; eapply ES.init_tid_K; eauto. }
    erewrite ESstep.basic_step_seqn_kevent; eauto. 
    { erewrite contseqn; eauto. 
      destruct (excluded_middle_informative ((Stid S) eid = tid_init)); auto.
      exfalso; eapply ES.init_tid_K; eauto. }
    (* TODO: refactor basic_step_seqn lemmas to get rid of this assumption *)
    admit. 
  Admitted.

End SimRelContLemmas.

Section SimRelCertLemmas. 

  Variable TC : trav_config.
  Variable sc : relation actid.
  Variable f : actid -> eventid.

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Notation "'fdom'" := ( C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘))) (only parsing).

  Lemma simrel_cert_graph_start TC' thread 
        (SRC : simrel_common prog S G sc TC f)
        (TR_STEP : isim_trav_step G sc thread TC TC') : 
    exists k state',
      ⟪ CERTG : cert_graph G sc TC TC' thread state' ⟫ /\
      ⟪ kTID : ES.cont_thread S k = thread ⟫ /\
      ⟪ CST_STABLE : stable_state thread state' ⟫ /\
      ⟪ CST_REACHABLE : 
          forall (state : (thread_lts thread).(Language.state))
                 (KK : K S (k, existT _ _ state)),
            (step thread)＊ state state' ⟫. 
  Proof. 
    edestruct cont_tid_state as [state [k HH]]; eauto. 
    { eapply trstep_thread_prog; eauto; apply SRC. }
    desf. 
    edestruct cert_graph_start as [state' HH]; eauto; try by apply SRC.
    { (* should follow from TR_STEP ??? *)
      admit. }
    { (* should follow from CsbqDOM *)
      admit. }
    desf. 
    exists k, state'. 
    splits; auto.  
    ins. 
    eapply ES.unique_K in KK;
      [| by apply SRC | by apply QQ | auto].
    simpls. inv KK.
  Admitted. 

  Lemma simrel_cert_start TC' thread
        (SRC : simrel_common prog S G sc TC f)
        (TR_STEP : isim_trav_step G sc thread TC TC') :
    exists q state state',
      ⟪ SRCC : simrel_cert prog S G sc TC TC' f f q state state' ⟫.
  Proof.
    edestruct simrel_cert_graph_start as [q [state' HH]]; eauto.
    desf.
    exists q.

    (* TODO: return the corresponding state in 'simrel_cert_graph_start'. *)
    eexists. 

    exists state'.
    constructor; auto.
    
    (* Ltac narrow_hdom q CsbqDOM := *)
    (*   arewrite (NTid_ (ES.cont_thread S q) ⊆₁ fun _ => True); *)
    (*   rewrite set_inter_full_r; *)
    (*   rewrite CsbqDOM; *)
    (*   rewrite set_unionC; *)
    (*   rewrite <- set_unionA; *)
    (*   rewrite set_unionK; *)
    (*   apply SRC. *)

    all: admit. 

    (* { by narrow_hdom q CsbqDOM. } *)
    (* { admit. } *)
    (* { by narrow_hdom q CsbqDOM. } *)
    (* { by narrow_hdom q CsbqDOM. } *)
    (* { admit. } *)
    (* { apply SRC.(ftid). }  *)
    (* { apply SRC.(flab). } *)
    (* { admit. } *)
    (* { by narrow_hdom q CsbqDOM. }  *)
    (* { admit. } *)
    (* { admit. } *)
    (* { admit. } *)
    (* rewrite CsbqDOM. *)
    (* unfold ES.cc. *)
    (* rewrite <- restr_relE. *)
    (* rewrite restr_inter. *)
    (* rewrite restr_rel_mori. *)
    (* { rewrite (restr_relE _ (Scf S)).  *)
    (*   rewrite SRC.(fimgNcf).  *)
    (*     by rewrite inter_false_l. }  *)
    (* all: basic_solver. *)
  Admitted.

  Lemma basic_step_e2a_E0_e TC' h k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')
        (BSTEP_ : ESstep.t_basic_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
     E0 G TC' (ES.cont_thread S k) (e2a S' e).
  Proof. 
    cdes BSTEP_.
    eapply dcertE; [apply SRCC|].
    erewrite basic_step_e2a_e; eauto. 
    2-3 : eapply SRCC.
    eapply preserve_event.
    { eapply ilbl_steps_in_steps; eauto. }
    edestruct lbl_step_cases as [l [l' HH]].
    { eapply SRCC; eauto. }
    { apply STEP. }
    desf; apply ACTS; basic_solver.
  Qed.

  Lemma basic_step_e2a_GE_e TC' h k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')
        (BSTEP_ : ESstep.t_basic_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
     GE (e2a S' e).
  Proof. 
    cdes BSTEP_.
    eapply E0_in_E. 
    { eapply sim_trav_step_coherence; [econstructor|]; eapply SRCC. }
    eapply basic_step_e2a_E0_e; eauto.
  Qed.

  Lemma basic_step_e2a_lab TC' h k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'')
        (BSTEP_ : ESstep.t_basic_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :
    same_lab_u2v_dom (SE S') (Slab S') (Glab ∘ (e2a S')).
  Proof. 
    cdes BSTEP_.
    
    assert (ESstep.t_basic e e' S S') as BSTEP.
    { econstructor; eauto. }
    
    assert (wf_thread_state (ES.cont_thread S k) st') as WFTS. 
    { eapply wf_thread_state_steps.
      { eapply SRCC; eauto. }
      eapply ilbl_steps_in_steps.
      do 2 econstructor. eapply STEP. }
    
    assert (Gtid (e2a S' e) = ES.cont_thread S k) as GTIDe.
    { rewrite <- e2a_tid. erewrite ESstep.basic_step_tid_e; eauto. }

    unfold same_lab_u2v_dom.
    intros x SEx.
    eapply ESstep.basic_step_acts_set in SEx; eauto.
    destruct SEx as [[SEx | SEx] | SEx].
    { erewrite ESstep.basic_step_lab_eq_dom; eauto. 
      unfold compose. 
        by erewrite basic_step_e2a_eq_dom; eauto; apply SRCC. }
    { subst x.
      arewrite ((Slab S') e = lbl).
      { rewrite LAB'. unfold upd_opt, opt_ext in *.
        destruct e'; desf. 
        { rewrite updo; [|omega].
            by rewrite upds. }
          by rewrite upds. }
      unfold compose. 
      edestruct lbl_step_cases as [l [l' HH]]. 
      { eapply SRCC; eauto. }
      { eapply STEP. }
      destruct HH as [AA BB].
      apply opt_to_list_app_singl in AA.
      destruct AA as [LA LB].
      subst l l'.
      eapply same_label_u2v_trans.
      2 : { eapply cuplab_cert; [|eapply dcertE]. 
              1-2 : apply SRCC.
              eapply basic_step_e2a_E0_e; eauto. }
      erewrite steps_preserve_lab.
      { erewrite basic_step_e2a_e.
        2-4 : eauto; apply SRCC.
        destruct BB as [BB | BB].
        { destruct BB as [_ [ACTS [LAB _]]]. 
          rewrite LAB.
          rewrite upds. unfold same_label_u2v. desf. }
        destruct BB as [_ [ACTS [LAB HH]]].
        desf. rewrite LAB.
        unfold upd_opt.
        rewrite updo. 
        { rewrite upds. basic_solver. }
        red. intros HH. inversion HH. omega. }
      { by rewrite GTIDe. }
      { apply ilbl_steps_in_steps. 
        by rewrite GTIDe. }
      erewrite basic_step_e2a_e.
      2-4 : eauto; apply SRCC.
      desf; apply ACTS; basic_solver. }

    destruct e' as [e' | ].
    2 : { exfalso. by unfold eq_opt in SEx. }
    unfold eq_opt in SEx. subst x.
    destruct lbl' as [lbl' | ].
    2 : { exfalso. by unfold opt_same_ctor in LABEL'. }
    arewrite ((Slab S') e' = lbl').
    { rewrite LAB'. unfold upd_opt, opt_ext in *.
        by rewrite upds. }
    unfold compose. 
    edestruct lbl_step_cases as [l [l' HH]]. 
    { eapply SRCC; eauto. }
    { eapply STEP. }
    destruct HH as [AA BB].
    apply opt_to_list_app_singl in AA.
    destruct AA as [LA LB].
    subst l l'.
    eapply same_label_u2v_trans.
    2 : { eapply cuplab_cert; [|eapply dcertE]. 
          1-2 : apply SRCC.
          (* eapply basic_step_e2a_E0; eauto. *)
          admit. }
    (* erewrite steps_preserve_lab. *)
    admit. 
  Admitted.

  Lemma weaken_sim_add_jf TC' h k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') 
        (BSTEP_ : ESstep.t_basic_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'')
        (SAJF : sim_add_jf S G sc TC TC' h k st e S') : 
    ESstep.add_jf e S S'.
  Proof. 
    cdes SAJF.
    assert (ESstep.t_basic e e' S S') as BSTEP.
    { econstructor. eauto. }
    assert (SE S w) as SEw.
    { eapply himg; eauto. }
    assert (SE S' w) as SEw'.
    { eapply ESstep.basic_step_acts_set; eauto. basic_solver. }
    assert (SE S' e) as SEe'.
    { eapply ESstep.basic_step_acts_set; eauto. basic_solver. }
    econstructor; auto. 
    exists w; splits; auto.  
    { assert (is_w (Glab ∘ (e2a S')) w) as WW.
      { eapply cert_rfD, seq_eqv_lr in NEW_RF.
        destruct NEW_RF as [HH _].
          by unfold is_w, compose in *. }
      eapply same_lab_u2v_dom_is_w; eauto.
      { eapply basic_step_e2a_lab; eauto. }
      red; split; auto. }
    { assert (restr_rel (SE S') (Ssame_loc S') w e) as HH.
      { eapply same_lab_u2v_dom_same_loc.
        { eapply basic_step_e2a_lab; eauto. }
        apply restr_relE, seq_eqv_lr. 
        splits; auto. 
        eapply cert_rfl in NEW_RF.
        by unfold same_loc, loc, compose in *. }
      apply restr_relE, seq_eqv_lr in HH. 
      basic_solver. }
    admit. 
  Admitted.

  Lemma simrel_cert_basic_step k lbls jf ew co
        (st st': (thread_lts (ES.cont_thread S k)).(Language.state))
        (* (SRCC : simrel_cert prog S G sc TC TC' f h k st'' new_rf) *)
        (KK : K S (k, existT _ _ st))
        (ILBL_STEP : ilbl_step (ES.cont_thread S k) lbls st st') :
    exists k' e e' lbl lbl' S',
      ⟪ ES_BSTEP_ : ESstep.t_basic_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S' ⟫ /\
      ⟪ LBLS_EQ : lbls = opt_to_list lbl' ++ [lbl] ⟫ /\
      ⟪ LBL  : lbl  = S'.(ES.lab) e ⟫ /\
      ⟪ LBL' : lbl' = option_map S'.(ES.lab) e' ⟫ /\
      ⟪ TID  : ES.cont_thread S k  = S'.(ES.tid) e ⟫ /\
      ⟪ JF' : S'.(ES.jf) ≡ jf ⟫ /\
      ⟪ EW' : S'.(ES.ew) ≡ ew ⟫ /\
      ⟪ CO' : S'.(ES.co) ≡ co ⟫.
  Proof.
    set (ILBL_STEP_ALT := ILBL_STEP).
    eapply ilbl_step_alt in ILBL_STEP_ALT; desf. 
    cdes ISTEP. 
    edestruct ISTEP0; desf.

    1-4 :  
      exists (CEvent S.(ES.next_act)); 
               exists S.(ES.next_act); exists None;
               eexists; eexists None; eexists (ES.mk _ _ _ _ _ _ _ _ _);
               splits; simpl; eauto;
               [ econstructor; splits; simpl; eauto; 
                 eexists; exists None; 
                 splits; simpl; eauto
               | by rewrite upds 
               | by rewrite upds ].

             all : 
               exists (CEvent (1 + S.(ES.next_act))); 
               exists S.(ES.next_act); exists (Some (1 + S.(ES.next_act)));
               eexists; eexists (Some _); eexists (ES.mk _ _ _ _ _ _ _ _ _);
               splits; simpl; eauto;
               [ econstructor; splits; simpl; eauto; 
                 eexists; eexists (Some _); 
                 splits; simpl; eauto
               | rewrite updo; [by rewrite upds | omega]
               | by rewrite upds
               | rewrite updo; [by rewrite upds | omega] ].
  Qed.  

  Lemma simrel_cert_esstep_e2a_eqr TC' h k st st' e e' S' r r' r''
        (SRCC : simrel_cert prog S G sc TC TC' f h k st st') 
        (ESSTEP : ESstep.t_basic e e' S S')
        (restrE : r ≡ ⦗ SE S ⦘ ⨾ r ⨾ ⦗ SE S ⦘)
        (rEQ : r' ≡ r) 
        (rIN : (e2a S) □ r ⊆ r'') : 
    (e2a S') □ r' ⊆ r''.
  Proof. 
    rewrite rEQ, restrE, collect_rel_eq_dom.
    { rewrite <- restrE; eauto. }
    all: eapply basic_step_e2a_eq_dom; eauto; apply SRCC.  
  Qed.

  Lemma simrel_cert_lbl_step TC' h q
        (state state' state'': (thread_lts (ES.cont_thread S q)).(Language.state))
        (SRCC : simrel_cert prog S G sc TC TC' f h q state state'')
        (KK : K S (q, existT _ _ state))
        (LBL_STEP : lbl_step (ES.cont_thread S q) state state')
        (CST_REACHABLE : (step (ES.cont_thread S q))＊ state' state'') :
    exists  q' S' h',
      ⟪ ESSTEP : (ESstep.t Weakestmo)^? S S' ⟫ /\
      ⟪ KK' : (ES.cont_set S') (q', existT _ _ state') ⟫ /\
      ⟪ SRCC' : simrel_cert prog S' G sc TC TC' f h' q' state' state''⟫.
  Proof.
    assert (Wf G) as WF by apply SRCC.
    assert (ES.Wf S) as WfS by apply SRCC.
    assert (tc_coherent G sc TC) as TCCOH by apply SRCC.
    assert (sim_trav_step G sc TC TC') as TCSTEP.
    { red. eexists. eapply tr_step; eauto. }
    assert (tc_coherent G sc TC') as TCCOH'.
    { eapply sim_trav_step_coherence; eauto. }
    assert (cert_graph G sc TC TC' (ES.cont_thread S q) state'') as CERTG by apply SRCC. 

    destruct LBL_STEP as [lbls ILBL_STEP].
    edestruct lbl_step_cases; eauto; desf.
    { admit. }
    { set (thread := (ES.cont_thread S q)).
      set (a := ThreadEvent thread (eindex state)).

      assert (acts_set state''.(ProgToExecution.G) a) as aInCertE.
      { eapply preserve_event; eauto.  
        apply ACTS; basic_solver. }

      assert (GE a) as aInGE.
      { destruct CERTG. 
        eapply E0_in_E; [apply TCCOH'|].
          by eapply dcertE. }       

      assert (GR a) as aInGR.
      { edestruct CERTG.
        eapply same_lab_u2v_is_r.  
        { apply same_lab_u2v_comm. eapply cuplab; eauto. }
        unfold is_r, CertGraph.certLab.
        destruct 
          (excluded_middle_informative (acts_set (ProgToExecution.G state'') a))
          as [HinCertE | HninCertE].
        { erewrite steps_preserve_lab; eauto.  
          { by rewrite GLAB, upds. }
          { (* should follow from `simrel_cont S'` *)
            admit. }
          apply ACTS. basic_solver. }
        exfalso. by apply HninCertE. }

      edestruct cert_rf_complete as [w RFwa]; eauto.
      { unfold set_inter. splits.  
        2: by apply aInGR.
        admit. }

      assert (exists (pstate : ProgToExecution.state), pstate = state) as [pstate EQST].
      { eexists. eauto. }
      
      assert (cert_dom S G TC state q w) as wInHDOM.
      { eapply new_rf_ntid_iss_sb in RFwa; try eapply SRCC.  
        destruct RFwa as [RFwa|RFwa].
        { apply seq_eqv_l in RFwa. destruct RFwa as [[NTIDw IW] RFwa].
          left. right. split; auto.
          eexists. eexists. split; [|red]; eauto. }
        admit. }

      assert (SE S (h w)) as hwInSE.
      { apply SRCC.(himg). 
        unfold set_collect.
        eexists; split; eauto. }

      edestruct simrel_cert_basic_step as [q' [e [e' [lbl [lbl' [S' HH]]]]]]; eauto; desf.

      assert (ESstep.t_basic e e' S S') as ES_BSTEP.
      { econstructor. do 4 eexists. apply ES_BSTEP_. }

      set (g' := e2a S').
      assert (g' e = a) as g'eaEQ.
      { subst g' a thread. 
        unfold e2a. 
        destruct (excluded_middle_informative ((SEinit S') e)) as [INIT | nINIT]. 
        { exfalso; eapply ESstep.basic_step_acts_ninit_set_e; eauto. } 
        erewrite ESstep.basic_step_tid_e; eauto.  
        edestruct q; simpl.  
        { (* we need property like `K (Cinit, st) => st.eindex = 0` in SimRel *)
          erewrite ESstep.basic_step_seqn_kinit; eauto. 
          admit. }
        erewrite ESstep.basic_step_seqn_kevent; eauto. 
        { erewrite contseqn; eauto. 
          2: eapply SRCC. 
          destruct (excluded_middle_informative ((Stid S) eid = tid_init)); auto.
          exfalso; eapply ES.init_tid_K; eauto. }
        admit. }

      assert (e' = None) as e'NONE.
      { admit. }
      
      rewrite e'NONE in ES_BSTEP_. 
      rewrite e'NONE in ES_BSTEP.
      rewrite e'NONE in LBLS_EQ.
      simpl in LBLS_EQ.
      inversion LBLS_EQ as [eSLAB].
      symmetry in eSLAB.

      assert (ESstep.t_load e None S S') as ES_LSTEP.
      { unfold ESstep.t_load. splits; eauto.
        unfold ESstep.add_jf.
        splits.
        { simpl. unfold is_r. auto. by rewrite eSLAB. }
        exists (h w).
        splits; auto. 
        { simpl. unfold is_w. admit. }
        admit.
        admit.
        cdes ES_BSTEP_; rewrite EVENT; eauto. }

      assert (ESstep.t_ e None S S') as ES_STEP_.
      { unfold ESstep.t_. auto. }

      assert (g' □ Ssb S' ⊆ Gsb) as SSB.
      { admit. }

      assert (g □ Shb S ⊆ Ghb) as SHB.
      { (* We need a lemma stating that. *)
        admit. }
      assert (g' □ Shb S ⊆ Ghb) as SHB'.
      { admit. }

      assert (ES.cont_sb_dom S q × eq e ⊆ S'.(ES.sb)) as SBDSB.
      { admit. }
      
      assert (g' □ S'.(hb) ⊆ Ghb) as BHB.
      { erewrite ESstep.load_step_hb; eauto.
        rewrite collect_rel_union.
        unionL; auto.
        rewrite collect_rel_seqi.
        etransitivity.
        2: { apply rewrite_trans_seq_cr_l.
             apply imm_s_hb.hb_trans. }
        apply seq_mori.
        { by rewrite collect_rel_cr, SHB'. }
        rewrite collect_rel_union.
        unionL.
        { rewrite SBDSB.
          etransitivity; eauto.
          apply imm_s_hb.sb_in_hb. }
        admit. }
      
      assert (@es_consistent S' Weakestmo) as ES'CONS.
      { econstructor; simpl.
        
        (* jf_vis *)
        { rewrite JF'. 
          apply inclusion_union_l.
          { etransitivity.
            { eapply scons. apply SRCC. }
            apply union_mori.
            { eapply ESstep.basic_step_sb_mon. eauto. }
            apply cross_mori. 
            { eapply ESstep.step_vis_mon; eauto. } 
            eapply ESstep.basic_step_acts_set_mon; eauto. }
          destruct (excluded_middle_informative (sb G w a)) as [waSB | waNSB].
          { apply inclusion_union_r; left. 
            admit. }
          (* apply (SRCC.(cert).(new_rf_iss_sb)) in RFwa. *)
          (* unfold union in RFwa; desf.  *)
          assert (I w) as Iw.
          { apply (SRCC.(cert).(new_rf_iss_sb)) in RFwa.
            unfolder in RFwa; desf. }
          apply inclusion_union_r; right. 
          unfolder; ins; splits; desf.
          2: cdes ES_BSTEP_; unfold opt_ext in EVENT'; omega.
          erewrite <- SRCC.(hfeq). 
          { eapply ESstep.step_vis_mon; eauto; apply SRCC. 
            unfolder.
            eexists; splits; eauto; right; repeat eexists; splits; eauto; desf. }
          right.
          unfolder; splits. 
          { right; repeat eexists; eauto. }
          unfold not; ins; apply waNSB. 
          destruct H as [y [SBqdom wEQ]].
          admit. }
        (* erewrite ESstep.e2a_step_eq_dom with (S:=S) in wEQ; eauto. *)
        (* [ | by apply SRC | admit | admit ]. *)
        (* eapply gsb; (* TODO: gsb should not depend on simrel *)  *)
        (*   [ by eauto | by eauto | admit | ].  *)
        (* unfolder; repeat eexists; splits; eauto.  *)
        (* unfold ES.cont_sb_dom in SBqdom; desf. *)
        (* { admit. } *)
        (* unfold set_inter in SBqdom. *)
        (* destruct SBqdom as [yTID ySBDOM]. *)
        (* unfold dom_rel in ySBDOM.  *)
        (* destruct ySBDOM as [y' yy'SBrefl]. *)
        (* admit. } *)
        
        (* hb_jf_not_cf *)
        { cdes ES_BSTEP_. 
          
          assert (eq (h w) ⊆₁ h □₁ cert_dom S G TC state q) as hwInHDOM. 
          { rewrite <- collect_eq.
            apply set_collect_mori; auto. 
            admit.
            (* arewrite (eq w ⊆₁ dom_rel new_rf). *)
            (* { autounfold with unfolderDb. *)
            (*   ins; desf; eexists; eauto. } *)
          (* eapply new_rf_dom; eauto. *) }

          unfold same_relation; splits; [|by basic_solver]. 
          erewrite ESstep.load_step_hb; eauto.
          rewrite JF'.
          rewrite ESstep.basic_step_nupd_cf; eauto.
          rewrite transp_union, transp_singl_rel, crE.
          relsf.
          rewrite !inter_union_l.
          rewrite !inter_union_r.
          repeat apply inclusion_union_l.

          all: try (
                   try rewrite ES.jfE;
                   try rewrite releaseE;
                   try rewrite hbE; 
                   try (rewrite ES.cont_sb_domE; eauto);
                   try (arewrite (singl_rel (ES.next_act S) (h w) ⊆ eq e × SE S)
                         by autounfold with unfolderDb; ins; desf);
                   try (arewrite (singl_rel (h w) (ES.next_act S) ⊆ SE S × eq e)
                         by autounfold with unfolderDb; ins; desf);
                     by ESstep.E_seq_e
                 ).

          { apply SRCC. }

          { rewrite seq_incl_cross.
            { rewrite <- restr_cross, restr_relE. 
              apply SRCC.(himgNcf). }
            { rewrite dom_cross; [|red; basic_solver]. 
              eapply sbk_in_hhdom; eauto. }
              by rewrite codom_singl_rel. } 

          { rewrite !seqA.
            rewrite hb_in_HChb_sb; eauto. 
            rewrite !seq_union_l. 
            rewrite inter_union_l.
            unionL.
            2: { rewrite <- !seqA.
                 rewrite sbk_in_hhdom; eauto.
                 rewrite seq_incl_cross.
                 { rewrite <- restr_cross, restr_relE. 
                   apply SRCC.(himgNcf). }
                 2: by rewrite codom_singl_rel.
                 admit. }
            rewrite seq_incl_cross.
            { rewrite <- restr_cross, restr_relE. 
              apply SRCC.(himgNcf). }
            { admit. }
            (* rewrite !set_collect_union. *)
            (* basic_solver 10. } *)
            rewrite !codom_seq.
              by rewrite codom_singl_rel. }
          
          { rewrite !seqA. 
            rewrite seq_incl_cross.
            { rewrite <- restr_cross, restr_relE.
              apply SRCC.(himgNcf). }
            { admit. 
            (* rewrite releaseC; eauto. 
            rewrite dom_seq.
            rewrite !set_collect_union.
            basic_solver 10. *) }
            rewrite !codom_seq.
            rewrite codom_singl_rel; auto. } 

          rewrite !seqA.
          rewrite hb_in_HChb_sb; eauto. 
          rewrite !seq_union_l. 
          rewrite inter_union_l.
          apply inclusion_union_l.  
          2: { rewrite <- !seqA.
               admit. 
          (* rewrite releaseC; eauto. 
          rewrite !seqA.
          rewrite <- seqA.
          rewrite seq_incl_cross.
          { rewrite <- restr_cross, restr_relE. 
              by rewrite SRCC.(himgNcf). }
          { admit. }
          rewrite !codom_seq.
            by rewrite codom_singl_rel. *) }
          rewrite seq_incl_cross.
          { rewrite <- restr_cross, restr_relE. 
            apply SRCC.(himgNcf). }
          { admit. }
          (* rewrite !set_collect_union. *)
          (* basic_solver 10. } *)
          rewrite !codom_seq.
          rewrite codom_singl_rel; auto. }
        
        { admit. }

        { cdes ES_BSTEP_.

          red; split; [|basic_solver].
          rewrite JF', ESstep.basic_step_cf; eauto. 
          rewrite !csE.
          rewrite !transp_cross.
          rewrite !inter_union_l.
          rewrite !inter_union_r. 
          unfold eq_opt.
          relsf.
          rewrite !unionA.
          repeat apply inclusion_union_l.

          all: try (
                   try rewrite ES.jfE;
                   try rewrite ES.cfE;
                     by ESstep.E_seq_e
                 ).

          { apply SRCC. }
          
          { unfolder. 
            intros x y [[EQx _] [CONTCFx _]].
            rewrite EQx in *. 
            eapply cfk_hdom; eauto. 
            unfold set_inter; split; eauto.
            unfold set_collect.
            eexists; split; eauto. }
          
          unfolder. 
          intros x y [[EQx _] [EQe _]].
          rewrite EQx in EQe.
          rewrite <- EQe in hwInSE.
          unfold "SE" in hwInSE.
          omega. }

        all: admit. }

      exists q', S', (upd h a e).

      desf; splits. 
      { unfold "^?". right.
        unfold ESstep.t.  
        do 2 eexists. 
        splits; eauto. }
      
      { admit. }

      econstructor. 
      { econstructor; try by apply SRCC.  
        { admit. }
        { apply ES'CONS. }
        { admit. }
        (* g' □₁ SE' ⊆₁ GE *)
        { rewrite ESstep.basic_step_nupd_acts_set; eauto.  
          rewrite set_collect_union. 
          apply set_subset_union_l. 
          split. 
          { erewrite set_collect_eq_dom; [eapply SRCC|].
            eapply basic_step_e2a_eq_dom; eauto. } 
          rewrite set_collect_eq.
          apply eq_predicate. 
          unfold g' in g'eaEQ; rewrite g'eaEQ; auto. }
        (* grmw : g □ Srmw ⊆ Grmw *)
        { eapply simrel_cert_esstep_e2a_eqr;
          [| | apply ES.rmwE | eapply ESstep.basic_step_nupd_rmw | apply SRCC];
          eauto. }
        (* gjf  : g □ Sjf  ⊆ Gvf *)
        { rewrite JF', collect_rel_union. 
          unionL. 
          { rewrite ES.jfE; auto. 
            erewrite collect_rel_eq_dom.
            { rewrite <- ES.jfE; auto. 
              eapply SRCC. }
            all: eapply basic_step_e2a_eq_dom; eauto. }
          cdes ES_BSTEP_. 
          rewrite <- EVENT.
          rewrite collect_rel_singl. 
          arewrite (e2a S' (h w) = w).
          { erewrite basic_step_e2a_eq_dom; eauto.
            symmetry. eapply ghtrip; eauto.
            apply seq_eqv_l.
            split; auto.  
            basic_solver. }
          fold g'. rewrite g'eaEQ.
          unfolder. ins. desf.
          eapply vf_in_furr; [by apply SRCC|]. 
          eapply cert_rf_in_vf, RFwa. }
        (* gew  : g □ Sew  ⊆ ⦗I⦘ *)
        { eapply simrel_cert_esstep_e2a_eqr; 
          [| | apply ES.ewE | eapply EW' | apply SRCC];
          eauto. }
        (* gew  : g □ Sco  ⊆ Gco *)
        { eapply simrel_cert_esstep_e2a_eqr; 
          [| | apply ES.coE | eapply CO' | apply SRCC];
          eauto. }
        
        all: admit. }

      all: admit. 
  Admitted.

  Lemma simrel_cert_step TC' h q state''
        (state : (thread_lts (ES.cont_thread S q)).(Language.state))
        (SRCC : simrel_cert prog S G sc TC TC' f h q state state'')
        (KK : K S (q, existT _ _ state))
        (KNEQ : state <> state'') :
    exists (state' : (thread_lts (ES.cont_thread S q)).(Language.state)),
      lbl_step (ES.cont_thread S q) state state'.
  Proof.
    set (thread := (ES.cont_thread S q)).
    set (REACHABLE := KK).
    admit.
    (* eapply cstate_reachable in REACHABLE; [|by apply SRCC]. *)
    (* assert ((lbl_step thread)＊ state state'') as LSTEPS. *)
    (* { apply (steps_stable_lbl_steps thread).  *)
    (*   apply restr_relE. *)
    (*   unfold restr_rel. *)
    (*   splits; auto. *)
    (*   { apply (SRC.(scont)).(contstable) in KK. auto. }  *)
    (*   apply SRCC. }  *)
    (* apply rtE in LSTEPS. *)
    (* destruct LSTEPS as [Tr|TCSTEP]; [ red in Tr; desf | ]. *)
    (* apply t_step_rt in TCSTEP. *)
    (* destruct TCSTEP as [state' [STEP _]]. *)
    (* exists state'.  *)
    (* splits; auto.  *)
  Admitted.

  Lemma simrel_cert_cc_dom TC' h q state state'
        (SRCC : simrel_cert prog S G sc TC TC' f h q state state') :
    dom_rel (Scc S ⨾ ⦗ ES.cont_sb_dom S q ⦘) ⊆₁ f □₁ I. 
  Proof. 
    admit.
  Admitted.

End SimRelCertLemmas.

End SimRelLemmas.