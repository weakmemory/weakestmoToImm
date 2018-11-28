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
        SimRel LblStep CertRf CertGraph.
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

  Notation "'Shb'" := (S.(Consistency.hb)).
  Notation "'Ssb'" := (S.(ES.sb)).
  Notation "'Sjfe'" := (S.(ES.jfe)).
  Notation "'Srf'" := (S.(ES.rf)).
  Notation "'Srfe'" := (S.(ES.rfe)).
  Notation "'Sco'" := (S.(ES.co)).
  Notation "'Scf'" := (S.(ES.cf)).
  Notation "'Scc'" := (S.(ES.cc)).
  Notation "'Sew'" := (S.(ES.ew)).

  Notation "'SR'" := (fun a => is_true (is_r Slab a)).
  Notation "'SW'" := (fun a => is_true (is_w Slab a)).
  
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
          << SSTATE : lstate = st >> /\
          << KK     : K (ll, existT _ _ st) >>
      end.
  
  Lemma Kstate_spec c (st : (thread_lts (ES.cont_thread S c)).(Language.state))
        (KK : K (c, existT _ _ st)) :
    exists (st' : ProgToExecution.state),
      << KST : Kstate (c, st') >> /\
      << EQST : st = st' >>.
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

      jfehI  : dom_rel Sjfe ⊆₁ dom_rel (Sew^? ;; <| h □₁ I |>);

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

  Definition sim_add_jf (r : eventid) (S S' : ES.t) : Prop :=
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
    { (* TODO: add the constraint '~ IdentMap.In tid_init prog' to 'simrel'. *)
      admit. }
    { apply SRC. }
    destruct state_q_cont; auto. desf.
    apply KK.
  Admitted.

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
    dom_rel (Ssb ;; <| ES.cont_sb_dom S q |>) ⊆₁ ES.cont_sb_dom S q.
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
    { eapply contwf; [by apply SRC|]. subst. apply KK. }
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
      eapply tid_initi; [by apply SRC|].
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
    eapply gsb; [by apply SRC|].
    do 2 eexists. splits; eauto.
    all: symmetry; eapply ghtrip; [by apply SRC|].
    all: by apply seq_eqv_l; split; auto.
  Qed.

  Lemma rfeI (SRC : simrel_cert) :
    dom_rel Srfe ⊆₁ dom_rel (Sew^? ;; <| h □₁ I |>).
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
  
  (* Lemma hsw :  *)

  Lemma hbNCsb : ⦗ set_compl (h □₁ C) ⦘ ⨾ Shb ⊆ Ssb. 
  Proof. Admitted.

  Lemma hb_in_Chb_sb : Shb ⊆ ⦗ h □₁ C ⦘ ⨾ Shb ∪ Ssb. 
  Proof. Admitted.

End SimRelCert.

Section SimRelLemmas.

Variable prog : Prog.t.
Variable PROG_NINIT : ~ (IdentMap.In tid_init prog).
Variable S : ES.t.
Variable G  : execution.
Variable GPROG : program_execution prog G.
Variable sc : relation actid.
Variable TC : trav_config.

Variable f : actid -> eventid.

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
Notation "'Scc' S" := S.(ES.cc) (at level 10).

Notation "'Sjfe' S" := S.(ES.jfe) (at level 10).
Notation "'Srfe' S" := S.(ES.rfe) (at level 10).
Notation "'Scoe' S" := S.(ES.coe) (at level 10).
Notation "'Sjfi' S" := S.(ES.jfi) (at level 10).
Notation "'Srfi' S" := S.(ES.rfi) (at level 10).
Notation "'Scoi' S" := S.(ES.coi) (at level 10).

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

Notation "'C'"  := (covered TC).
Notation "'I'"  := (issued TC).

Notation "'sbq_dom' k" := (g □₁ ES.cont_sb_dom S k) (at level 1, only parsing).
Notation "'fdom'" := (C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘))) (only parsing).

Variable SRC : simrel_common prog S G sc TC f.

Hint Resolve SRC. 

(* cstate_stable : stable_state qtid state'; *)
(*       cstate_reachable :  *)
(*         forall (state : (thread_lts qtid).(Language.state)) *)
(*                (KK : K (q, existT _ _ state)), *)
(*           (step qtid)＊ state state'; *)
(*       certg : cert_graph G sc TC TC' qtid state'; *)

Lemma simrel_cert_graph_start TC' thread 
      (* (NINITT : thread <> tid_init) *)
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
  { eapply contwf; eauto. apply SRC. }
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
  
  Ltac narrow_hdom q CsbqDOM :=
    arewrite (NTid_ (ES.cont_thread S q) ⊆₁ fun _ => True);
    rewrite set_inter_full_r;
    rewrite CsbqDOM;
    rewrite set_unionC;
    rewrite <- set_unionA;
    rewrite set_unionK;
    apply SRC.

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

Lemma basic_step_e2a_eq_dom e e' S'
      (WF : ES.Wf S)
      (BSTEP : ESstep.t_basic e e' S S') :
  eq_dom (SE S) (e2a S') (e2a S).
Proof.
  cdes BSTEP; cdes BSTEP_.
  red. intros x. ins.
  unfold e2a.
  assert ((SEinit S') x <-> (SEinit S) x) as AA.
  { edestruct ESstep.basic_step_acts_init_set as [AA BB]; eauto. }
  assert ((Sloc S') x = (Sloc S) x) as BB.
  { eapply ESstep.basic_step_loc_eq_dom; eauto. }
  desf; try by intuition.
  assert ((Stid S') x = (Stid S) x) as CC.
  { eapply ESstep.basic_step_tid_eq_dom; eauto. }
  assert (ES.seqn S' x = ES.seqn S x) as DD.
  { eapply ESstep.basic_step_seqn_eq_dom; eauto. }
  congruence.
Qed.

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

Lemma simrel_cert_esstep_e2a_eqr e e' S' r r' r''
      (ESSTEP : ESstep.t_basic e e' S S')
      (restrE : r ≡ ⦗ SE S ⦘ ⨾ r ⨾ ⦗ SE S ⦘)
      (rEQ : r' ≡ r) 
      (rIN : (e2a S) □ r ⊆ r'') : 
  (e2a S') □ r' ⊆ r''.
Proof. 
  rewrite rEQ, restrE, collect_rel_eq_dom.
  { rewrite <- restrE; eauto. }
  all: eapply basic_step_e2a_eq_dom; eauto; apply SRC.  
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
  assert (Wf G) as WF by apply SRC.
  assert (ES.Wf S) as WfS by apply SRC.
  assert (tc_coherent G sc TC) as TCCOH by apply SRC.
  assert (sim_trav_step G sc TC TC') as TCSTEP.
  { red. eexists. eapply tr_step; eauto. }
  assert (tc_coherent G sc TC') as TCCOH'.
  { eapply sim_trav_step_coherence; eauto. }
  assert (cert_graph G sc TC TC' (ES.cont_thread S q) state'') as CERTG by apply SRCC. 

  destruct LBL_STEP as [lbls ILBL_STEP].
  edestruct lbl_step_cases; eauto; desf.  
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
      { erewrite contseqn; eauto. eapply SRC. }
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
          { apply SRC.(scons). }
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

        { apply SRC. }

        { rewrite seq_incl_cross.
          { rewrite <- restr_cross, restr_relE. 
            apply SRCC.(himgNcf). }
          { rewrite dom_cross; [|red; basic_solver]. 
            eapply sbk_in_hhdom; eauto. }
          by rewrite codom_singl_rel. } 

        { rewrite !seqA.
          rewrite hb_in_Chb_sb; eauto. 
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
        rewrite hb_in_Chb_sb; eauto. 
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

        { apply SRC. }
        
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
    { econstructor; try by apply SRC.  
      { admit. }
      { apply ES'CONS. }
      { admit. }
      { admit. }
      (* g' □₁ SE' ⊆₁ GE *)
      { rewrite ESstep.basic_step_nupd_acts_set; eauto.  
        rewrite set_collect_union. 
        apply set_subset_union_l. 
        split. 
        { erewrite set_collect_eq_dom; [eapply SRC|].
          eapply basic_step_e2a_eq_dom; eauto. } 
        rewrite set_collect_eq.
        apply eq_predicate. 
        unfold g' in g'eaEQ; rewrite g'eaEQ; auto. }
      (* grmw : g □ Srmw ⊆ Grmw *)
      { eapply simrel_cert_esstep_e2a_eqr; 
          [| apply ES.rmwE | eapply ESstep.basic_step_nupd_rmw | apply SRC];
          eauto. }
      (* gjf  : g □ Sjf  ⊆ Gvf *)
      { rewrite JF', collect_rel_union. 
        unionL. 
        { rewrite ES.jfE; auto. 
          erewrite collect_rel_eq_dom.
          { rewrite <- ES.jfE; auto. 
            eapply SRC. }
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
        eapply vf_in_furr; [by apply SRC|]. 
        eapply cert_rf_in_vf, RFwa. }
      (* gew  : g □ Sew  ⊆ ⦗I⦘ *)
      { eapply simrel_cert_esstep_e2a_eqr; 
          [| apply ES.ewE | eapply EW' | apply SRC];
          eauto. }
      (* gew  : g □ Sco  ⊆ Gco *)
      { eapply simrel_cert_esstep_e2a_eqr; 
          [| apply ES.coE | eapply CO' | apply SRC];
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

End SimRelLemmas.