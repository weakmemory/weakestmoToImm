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

  (* A state, which is reachable from a state in a continuation related to (h q) in S
     and which represents a graph certification. *)
  Variable state' : state.

  Notation "'new_rf'" := (cert_rf G sc TC' qtid).
  
  Notation "'certG'" := state'.(ProgToExecution.G).

  Notation "'g'" := (ES.event_to_act S).

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
  Notation "'Gco'" := (G.(co)).

  Notation "'certE'" := certG.(acts_set).
  Notation "'certTid'" := (tid).
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
  Notation "'hdom'" := (C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘) ∩₁ NTid_ qtid) ∪₁ sbq_dom)
                         (only parsing).

  Record simrel_cert :=
    { sim : simrel_common prog S G sc TC f;

      cstate_stable : stable_state qtid state';
      cstate_reachable : 
        forall (state : (thread_lts qtid).(Language.state))
               (KK : K (q, existT _ _ state)),
          (step qtid)＊ state state';

      cert : cert_graph G sc TC TC' qtid state';

      tr_step : isim_trav_step G sc qtid TC TC';

      ghtrip : ⦗ hdom ⦘ ⨾ ↑ (g ∘ h) ⊆ eq;
      
      hgfix_sbk : fixset (ES.cont_sb_dom S q) (h ∘ g); 

      jfehI  : dom_rel Sjfe ⊆₁ dom_rel (Sew^? ;; <| h □₁ I |>);

      hinj : inj_dom_s hdom h;
      himg : h □₁ hdom ⊆₁ SE;
      hoth : (h □₁ set_compl hdom) ∩₁ SE ≡₁ ∅;
      htid : Stid ∘ h = Gtid;

      hlabCI : eq_dom (C ∪₁ I) Glab (Slab ∘ h);
      hlabTHRD : eq_dom sbq_dom certLab (Slab ∘ h);

      hco : h □ ⦗ hdom ⦘ ⨾ Gco ⨾ ⦗ hdom ⦘ ⊆ Sco;

      himgNcf : ⦗ h □₁ hdom ⦘ ⨾ Scf ⨾ ⦗ h □₁ hdom ⦘ ≡ ∅₂;
      
      complete_fdom :
        (h □₁ hdom) ∩₁ SR ⊆₁ codom_rel (⦗ h □₁ hdom ⦘ ⨾ Srf);

      hfeq  : eq_dom (C ∪₁ fdom \₁ sbq_dom) f h; 

      imgcc : ⦗ f □₁ sbq_dom ⦘ ⨾ Scc ⨾ ⦗ h □₁ sbq_dom ⦘ ⊆
              ⦗ h □₁ GW ⦘ ⨾ Sew ⨾ Ssb⁼ ;

      release_issh_cov : dom_rel (Srelease ⨾ Sew^? ⨾ ⦗ h □₁ I ⦘) ⊆₁ h □₁ C;
    }.

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
  Proof. basic_solver. Qed.

  Lemma sbk_in_hhdom (SRC : simrel_cert) : ES.cont_sb_dom S q ⊆₁ h □₁ hdom.
  Proof. 
    rewrite set_collect_union.
    arewrite (ES.cont_sb_dom S q ≡₁ h □₁ (g □₁ ES.cont_sb_dom S q)) at 1.
    { rewrite set_collect_compose.
      apply fixset_set_fixpoint. 
      apply SRC. }
    apply set_subset_union_r2.
  Qed.

  Lemma cfk_hdom (SRC : simrel_cert) : ES.cont_cf_dom S q ∩₁ h □₁ hdom ≡₁ ∅.
  Proof. 
    red; split; [|basic_solver].
    rewrite !set_collect_union. 
    rewrite !set_inter_union_r.
    apply set_subset_union_l; split. 
    { apply set_subset_union_l; split. 
      { admit. }
      admit. }
    admit. 
  Admitted.

  Lemma hsb : h □ (⦗ hdom ⦘ ⨾ Gsb ⨾ ⦗ hdom ⦘) ⊆ Ssb. 
  Proof.
  Admitted.
  
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

Notation "'g'" := (ES.event_to_act S).

Notation "'SE' S" := S.(ES.acts_set) (at level 10).
Notation "'SEinit' S" := S.(ES.acts_init_set) (at level 10).
Notation "'Stid' S" := (S.(ES.tid)) (at level 10).
Notation "'Slab' S" := S.(ES.lab) (at level 10).
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
Notation "'hdom' k" := 
  (C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘) ∩₁ GNtid_ (ES.cont_thread S k)) ∪₁ (sbq_dom k))
    (at level 1, only parsing).

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
  exists q state',
    ⟪ SRCC : simrel_cert prog S G sc TC TC' f f q state' ⟫.
Proof.
  edestruct simrel_cert_graph_start as [q [state' HH]]; eauto.
  desf.
  exists q. exists state'.
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
    | rewrite updo; [by rewrite upds | by omega]
    | by rewrite upds
    | rewrite updo; [by rewrite upds | by omega] ].
Qed.  

Lemma simrel_cert_esstep_e2a_eqr e e' S' r r' r''
      (ESSTEP : ESstep.t_basic e e' S S')
      (restrE : r ≡ ⦗ SE S ⦘ ⨾ r ⨾ ⦗ SE S ⦘)
      (rEQ : r' ≡ r) 
      (rIN : (ES.event_to_act S) □ r ⊆ r'') : 
  (ES.event_to_act S') □ r' ⊆ r''.
Proof. 
  rewrite rEQ, restrE, collect_rel_eq_dom.
  { rewrite <- restrE; eauto. }
  all: eapply ESstep.e2a_step_eq_dom; eauto; apply SRC.  
Qed.

Lemma simrel_cert_lbl_step TC' h q
      (state state' state'': (thread_lts (ES.cont_thread S q)).(Language.state))
      (SRCC : simrel_cert prog S G sc TC TC' f h q state'')
      (KK : K S (q, existT _ _ state))
      (LBL_STEP : lbl_step (ES.cont_thread S q) state state')
      (CST_REACHABLE : (step (ES.cont_thread S q))＊ state' state'') :
  exists  q' S' h',
    ⟪ ESSTEP : (ESstep.t Weakestmo)^? S S' ⟫ /\
    ⟪ KK' : (ES.cont_set S') (q', existT _ _ state') ⟫ /\
    ⟪ SRCC' : simrel_cert prog S' G sc TC TC' f h' q' state''⟫.
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
    set (a   := ThreadEvent thread (eindex state)).

    assert (acts_set state''.(ProgToExecution.G) a) as aInCertE.
    { eapply preserve_event; eauto.  
      apply ACTS; basic_solver. }

    assert (GE a) as aInGE.
    { destruct CERTG. 
      eapply E0_in_E; [apply TCCOH'|].
      by eapply dcertE. }       

    assert (GR a) as aInGR.
    { edestruct CERTG.
      erewrite same_label_is_r.  
      2: { apply same_lab_up_to_value_comm. eapply cuplab; eauto. }
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

    assert (hdom q w) as wInHDOM.
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

    set (g' := ES.event_to_act S').
    assert (g' e = a) as g'eaEQ.
    { 

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
        
        assert (eq (h w) ⊆₁ h □₁ hdom q) as hwInHDOM. 
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
            by rewrite SRCC.(himgNcf). }
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
                   by rewrite SRCC.(himgNcf). }
               2: by rewrite codom_singl_rel.
               admit. }
          rewrite seq_incl_cross.
          { rewrite <- restr_cross, restr_relE. 
            by rewrite SRCC.(himgNcf). }
          { rewrite !set_collect_union.
            basic_solver 10. }
          rewrite !codom_seq.
            by rewrite codom_singl_rel. }
        
        { rewrite !seqA. 
          rewrite seq_incl_cross.
          { rewrite <- restr_cross, restr_relE.
            by rewrite SRCC.(himgNcf). }
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
            by rewrite SRCC.(himgNcf). }
        { rewrite !set_collect_union.
          basic_solver 10. }
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
          eapply ESstep.e2a_step_eq_dom; eauto. } 
        rewrite set_collect_eq.
        apply eq_predicate. 
        unfold g' in g'eaEQ; rewrite g'eaEQ; auto. }
      (* grmw : g □ Srmw ⊆ Grmw *)
      { eapply simrel_cert_esstep_e2a_eqr; 
          [| apply ES.rmwE | eapply ESstep.basic_step_nupd_rmw | apply SRC];
          eauto. }
      (* gjf  : g □ Sjf  ⊆ Gvf *)
      { admit. }
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
      (SRCC : simrel_cert prog S G sc TC TC' f h q state'')
      (KK : K S (q, existT _ _ state))
      (KNEQ : state <> state'') :
  exists (state' : (thread_lts (ES.cont_thread S q)).(Language.state)),
    lbl_step (ES.cont_thread S q) state state'.
Proof.
  set (thread := (ES.cont_thread S q)).
  set (REACHABLE := KK).
  eapply cstate_reachable in REACHABLE; [|by apply SRCC].
  assert ((lbl_step thread)＊ state state'') as LSTEPS.
  { apply (steps_stable_lbl_steps thread). 
    apply restr_relE.
    unfold restr_rel.
    splits; auto.
    { apply (SRC.(scont)).(contstable) in KK. auto. } 
    apply SRCC. } 
  apply rtE in LSTEPS.
  destruct LSTEPS as [Tr|TCSTEP]; [ red in Tr; desf | ].
  apply t_step_rt in TCSTEP.
  destruct TCSTEP as [state' [STEP _]].
  exists state'. 
  splits; auto. 
Qed.

Lemma simrel_cert_cc_dom TC' h q state'
  (SRCC : simrel_cert prog S G sc TC TC' f h q state') :
  dom_rel (Scc S ⨾ ⦗ ES.cont_sb_dom S q ⦘) ⊆₁ f □₁ I. 
Proof. 
  admit.
Admitted.

End SimRelLemmas.