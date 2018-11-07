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
Require Import AuxRel AuxDef EventStructure Construction Consistency SimRel LblStep CertRf.
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
  Notation "'K'"  := S.(ES.cont_set).

  Notation "'Stid_' t" := (fun x => Stid x = t) (at level 1).

  Notation "'Ssb'" := (S.(ES.sb)).
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

  Record sim_cert_graph :=
    { cslab : eq_dom ((Tid_ qtid) ∩₁ (C' ∪₁ I')) certLab Glab;
      cuplab_cert : forall e (EE : certE e),
          same_label_up_to_value (certG.(lab) e) (Glab e);
      cstate_stable : stable_state qtid state';
      cstate_reachable :
        forall (state : (thread_lts qtid).(Language.state))
               (KK : K (q, existT _ _ state)),
          (step qtid)＊ state state';
      
      dcertE : certE ≡₁ E0;
      dcertRMW : certRmw ≡ ⦗ certE ⦘ ⨾ Grmw ⨾ ⦗ certE ⦘;
      
      new_rfv : new_rf ⊆ same_val certLab;
      new_rfl : new_rf ⊆ same_loc certLab;
      new_rf_iss_sb : new_rf ⊆ ⦗ I ⦘ ⨾ new_rf ∪ Gsb;

      oval : eq_dom (D G TC' qtid) (val certLab) (val Glab);
    }.
  
  Section CertGraphProperties.
    Variable Wf_sc : wf_sc G sc.
    Variable SCG : sim_cert_graph.
    
    Lemma new_rf_w : new_rf ≡ ⦗ GW ⦘ ⨾ new_rf.
    Proof. rewrite cert_rfD. basic_solver. Qed.

    Lemma cuplab e :
        same_label_up_to_value (certLab e) (Glab e).
    Proof.
      unfold certLab. desf.
      { by apply SCG. }
      red. desf.
    Qed.
  End CertGraphProperties.

  Notation "'sbq_dom'" := (g □₁ ES.cont_sb_dom S q) (only parsing).
  Notation "'fdom'" := (C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘))) (only parsing).
  Notation "'hdom'" := (C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘) ∩₁ NTid_ qtid) ∪₁ sbq_dom)
                         (only parsing).
      
  Record simrel_cert :=
    { sim : simrel prog S G sc TC f;

      cert : sim_cert_graph;

      tr_step : isim_trav_step G sc qtid TC TC';

      ghtrip : ⦗ hdom ⦘ ⨾ ↑ (g ∘ h) ⊆ eq;
      
      hgfix_sbk : fixset (ES.cont_sb_dom S q) (h ∘ g); 

      hinj : inj_dom hdom h;
      himg : h □₁ hdom ⊆₁ SE;
      hoth : (h □₁ set_compl hdom) ∩₁ SE ≡₁ ∅;
      htid : Stid ∘ h = Gtid;

      hlabCI : eq_dom (C ∪₁ I) Glab (Slab ∘ h);
      hlabTHRD : eq_dom sbq_dom certLab (Slab ∘ h);

      hco : h □ ⦗ hdom ⦘ ⨾ Gco ⨾ ⦗ hdom ⦘ ⊆ Sco;

      himgNcf : ⦗ h □₁ hdom ⦘ ⨾ Scf ⨾ ⦗ h □₁ hdom ⦘ ≡ ∅₂;
      
      complete_fdom :
        (h □₁ hdom) ∩₁ SR ⊆₁ codom_rel (⦗ h □₁ hdom ⦘ ⨾ Srf);

      hfeq  : eq_dom (fdom \₁ (sbq_dom \₁ C)) f h; 

      imgcc : ⦗ f □₁ sbq_dom ⦘ ⨾ Scc ⨾ ⦗ h □₁ sbq_dom ⦘ ⊆
              ⦗ h □₁ GW ⦘ ⨾ Sew ⨾ Ssb⁼ ;
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
    repeat rewrite set_collect_union. 
    repeat rewrite set_inter_union_r.
    apply set_subset_union_l; split. 
    { apply set_subset_union_l; split. 
      { admit. }
      admit. }
    admit. 
  Admitted.

  Lemma hsb : h □ (⦗ hdom ⦘ ⨾ Gsb ⨾ ⦗ hdom ⦘) ⊆ Ssb. 
  Proof.
  Admitted.

  (* TODO: this statement is incorrect! *)
  Lemma new_rf_dom : dom_rel new_rf ⊆₁ hdom.
  Proof.
  Admitted.

  Lemma new_rf_ntid_iss_sb (SRC : simrel_cert) :
    new_rf ⊆ ⦗ NTid_ qtid ∩₁ I ⦘ ⨾ new_rf ∪ Gsb.
  Proof.
    etransitivity.
    { apply cert_rf_ntid_sb.
      1,2: by apply SRC.
      eapply sim_trav_step_rel_covered.
      eexists.
      all: apply SRC. }
    sin_rewrite new_rf_iss_sb.
    2: by apply SRC.
    basic_solver 10.
  Qed.

  Record forward_pair (e : actid) (e' : eventid) 
         (state : (thread_lts (ES.cont_thread S (CEvent e'))).(Language.state)) :=
    { fp_Kq      : K (CEvent e', existT _ _ state);
      fp_inCertE : certE e;
      fp_tidEq   : certTid e = Stid e';
      fp_labEq   : certLab e = Slab e';
      fp_sbEq    : upd h e e' □ (Gsb ⨾ ⦗ eq e ⦘) ≡ Ssb ⨾ ⦗ eq e' ⦘;
    }.

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

Variable SRC : simrel prog S G sc TC f.

Section Properties.

Variable q : cont_label.
Variable TC': trav_config.
Hypothesis TCCOH' : tc_coherent G sc TC'.

Notation "'E0'" := (Tid_ (ES.cont_thread S q) ∩₁
                         (covered TC' ∪₁ dom_rel (Gsb^? ⨾ ⦗ issued TC' ⦘))).
Notation "'D'" := (D G TC' (ES.cont_thread S q)).

Notation "'C''"  := (covered TC').
Notation "'I''"  := (issued TC').

Lemma dom_addrE_in_D : dom_rel (Gaddr ⨾ ⦗ E0 ⦘) ⊆₁ D.
Proof.
  assert (Wf G) as WF by apply SRC.
  rewrite set_inter_union_r.
  rewrite id_union; relsf; unionL; splits.
  { rewrite (addr_in_sb WF).
    generalize (dom_sb_covered TCCOH').
    unfold CertExecution2.D; basic_solver 21. }
  arewrite (Gtid_ (ES.cont_thread S q) ∩₁ dom_rel (Gsb^? ⨾ ⦗issued TC'⦘) ⊆₁
                  dom_rel (Gsb^? ⨾ ⦗issued TC'⦘)) by basic_solver.
  rewrite dom_rel_eqv_dom_rel.
  arewrite (⦗I'⦘ ⊆ ⦗GW⦘ ⨾ ⦗I'⦘).
  { generalize (issuedW TCCOH'); basic_solver. }
  rewrite (dom_l (wf_addrD WF)), !seqA.
  arewrite (⦗GR⦘ ⨾ Gaddr ⨾ Gsb^? ⨾ ⦗GW⦘ ⊆ Gppo).
  { unfold ppo; rewrite <- ct_step; basic_solver 12. }
  unfold CertExecution2.D; basic_solver 21.
Qed.

Lemma dom_ctrlE_in_D : dom_rel (Gctrl ⨾ ⦗ E0 ⦘) ⊆₁ D.
Proof.
  assert (Wf G) as WF by apply SRC.
  rewrite set_inter_union_r.
  rewrite id_union; relsf; unionL; splits.
  { rewrite (ctrl_in_sb WF).
    generalize (dom_sb_covered TCCOH').
    unfold CertExecution2.D; basic_solver 21. }
  arewrite (Gtid_ (ES.cont_thread S q) ∩₁ dom_rel (Gsb^? ⨾ ⦗issued TC'⦘) ⊆₁
                  dom_rel (Gsb^? ⨾ ⦗issued TC'⦘)) by basic_solver.
  rewrite dom_rel_eqv_dom_rel.
  arewrite (Gctrl ⨾ Gsb^? ⊆ Gctrl).
  { generalize (ctrl_sb WF); basic_solver 21. }
  arewrite (⦗I'⦘ ⊆ ⦗GW⦘ ⨾ ⦗I'⦘).
  { generalize (issuedW TCCOH'); basic_solver. }
  rewrite (wf_ctrlD WF), !seqA.
  arewrite (⦗GR⦘ ⨾ Gctrl ⨾ ⦗GW⦘ ⊆ Gppo).
  { unfold ppo; rewrite <- ct_step; basic_solver 12. }
  unfold CertExecution2.D; basic_solver 21.
Qed.

Lemma dom_rmw_depE_in_D : dom_rel (Grmw_dep ⨾ ⦗ E0 ⦘) ⊆₁ D.
Proof.
  assert (Wf G) as WF by apply SRC.
  rewrite set_inter_union_r.
  rewrite id_union; relsf; unionL; splits.
  { rewrite (rmw_dep_in_sb WF).
    generalize (dom_sb_covered TCCOH').
    unfold CertExecution2.D; basic_solver 21. }
  arewrite (Gtid_ (ES.cont_thread S q) ∩₁ dom_rel (Gsb^? ⨾ ⦗issued TC'⦘) ⊆₁
                  dom_rel (Gsb^? ⨾ ⦗issued TC'⦘)) by basic_solver.
  rewrite dom_rel_eqv_dom_rel.
  rewrite (wf_rmw_depD WF), !seqA.
  arewrite (⦗I'⦘ ⊆ ⦗GW⦘ ⨾ ⦗I'⦘).
  { generalize (issuedW TCCOH'); basic_solver. }
  arewrite (⦗GR⦘ ⨾ Grmw_dep ⨾ ⦗GR_ex⦘ ⨾ Gsb^? ⨾ ⦗GW⦘ ⊆ Gppo).
  2: unfold CertExecution2.D; basic_solver 21.
  unfold ppo; hahn_frame.
  case_refl _.
  { by rewrite <- ct_step; basic_solver 12. }
  rewrite ct_begin; rewrite <- inclusion_t_rt, <- ct_step; basic_solver 12.
Qed.

Lemma dom_rmwE_in_D : dom_rel (Grmw ⨾ ⦗ E0 ⦘) ⊆₁ D.
Proof.
  assert (Wf G) as WF by apply SRC.
  rewrite set_inter_union_r.
  rewrite id_union; relsf; unionL; splits.
  { rewrite (rmw_in_sb WF).
    generalize (dom_sb_covered TCCOH').
    unfold CertExecution2.D; basic_solver 21. }
  arewrite (Gtid_ (ES.cont_thread S q) ∩₁ dom_rel (Gsb^? ⨾ ⦗issued TC'⦘) ⊆₁
                  dom_rel (Gsb^? ⨾ ⦗issued TC'⦘)) by basic_solver.
  rewrite dom_rel_eqv_dom_rel.
  arewrite (⦗I'⦘ ⊆ ⦗GW⦘ ⨾ ⦗I'⦘).
  { generalize (issuedW TCCOH'); basic_solver. }
  generalize (rmw_in_ppo WF) (rmw_sb_W_in_ppo WF).
  unfold CertExecution2.D; basic_solver 21.
Qed.

Lemma dom_dataD_in_D : dom_rel (data G ⨾ ⦗D⦘) ⊆₁ D.
Proof.
  assert (Wf G) as WF by apply SRC.
  unfold CertExecution2.D.
  rewrite !id_union; relsf; unionL; splits.
  { rewrite (data_in_sb WF).
    generalize dom_sb_covered. basic_solver 21. }
  { rewrite (data_in_ppo WF).
    basic_solver 12. }
  { rewrite (data_in_sb WF).
    rewrite (dom_l (@wf_sbE G)) at 1.
    rewrite sb_tid_init' at 1; relsf; unionL; split.
    { unionR left -> left -> left -> right.
      unfold same_tid; unfolder; ins; desf; eauto 20. }
    arewrite (⦗GE⦘ ⨾ ⦗fun a : actid => is_init a⦘ ⊆ ⦗D⦘).
    generalize D_init; basic_solver.
    arewrite (dom_rel (⦗D⦘ ⨾ Gsb ⨾ ⦗GE ∩₁ NTid_ (ES.cont_thread S q)⦘) ⊆₁ D) by basic_solver.
    unfold CertExecution2.D; basic_solver 12. }
  { rewrite dom_rel_eqv_dom_rel.
    rewrite crE at 1; relsf; unionL; splits.
    { rewrite (dom_r (wf_dataD WF)), (dom_l (@wf_ppoD G)). type_solver. }
    rewrite (data_in_ppo WF).
    sin_rewrite ppo_rfi_ppo. basic_solver 21. }
  { rewrite (dom_r (wf_dataD WF)), (dom_r (wf_rfiD WF)). type_solver. }
  rewrite (dom_r (wf_dataD WF)), (dom_r (wf_rfeD WF)). type_solver.
Qed.

End Properties.

Lemma sim_cert_graph_start TC' thread
      (TR_STEP : isim_trav_step G sc thread TC TC') : 
  exists q state',
    ⟪ QTID : thread = ES.cont_thread S q  ⟫ /\
    ⟪ CsbqDOM : g □₁ ES.cont_sb_dom S q ⊆₁ covered TC ⟫ /\
    ⟪ SRCG : sim_cert_graph S G sc TC TC' q state' ⟫.
Proof.
  assert (Wf G) as WF by apply SRC.
  assert (imm_consistent G sc) as CON by apply SRC.
  assert (tc_coherent G sc TC) as TCCOH by apply SRC.
  assert (tc_coherent G sc TC') as TCCOH'.
  { eapply sim_trav_step_coherence.
    2: by apply SRC.
    red. eauto. }

  assert (forall r w, Grmw r w -> covered TC' r <-> covered TC' w) as RMWCOV.
  { eapply sim_trav_step_rmw_covered; eauto.
    { red. eauto. }
    apply SRC. }

  assert (IdentMap.In thread prog) as PROGI.
  { apply sim_trav_step_to_step in TR_STEP. desf.
    assert (GE e) as EE.
    { cdes TR_STEP. desf.
      { apply COV. }
      apply ISS. }
    set (BB := EE).
    apply GPROG in BB.
    desf. exfalso.
    destruct SRC.
    cdes TR_STEP. desf.
    { apply NEXT. by eapply init_covered; eauto. }
    apply NISS. by eapply init_issued; eauto. }

  edestruct cont_tid_state with (thread:=thread) as [state [q]]; eauto.
  desf.

  assert (ES.cont_thread S q <> tid_init) as NINITT.
  { admit. }
  
  assert (exists state', sim_cert_graph S G sc TC TC' q state')
    as [state' HH].
  2: { eexists. splits; eauto. }
  cdes SSTATE. cdes SSTATE1.
  set (E0 := Tid_ (ES.cont_thread S q) ∩₁
             (covered TC' ∪₁ dom_rel (Gsb^? ⨾ ⦗ issued TC' ⦘))).

  assert (E0 ⊆₁ acts_set (ProgToExecution.G state')) as EEI'.
  { unfold E0.
    rewrite tr_acts_set; eauto.
    rewrite set_interC.
    apply set_subset_inter; auto.
    rewrite coveredE; eauto.
    rewrite issuedE; eauto.
    rewrite wf_sbE.
    basic_solver. }
  
  assert (acts_set (ProgToExecution.G state) ⊆₁ E0) as EEI.
  { etransitivity.
    { eapply contstateE; eauto. apply SRC. }
    unfold E0.
    apply set_subset_inter_r. split.
    { unfold ES.cont_sb_dom.
      desf.
      { admit. (* unfolder. basic_solver. *) }
      admit.
      (* rewrite set_collect_inter. *)
      (* apply set_subset_inter_l. *)
      (* left. *)
      (* eapply gtid_; eauto. *) }
    unionR left.
    assert (covered TC ⊆₁ covered TC') as AA.
    { eapply sim_trav_step_covered_le.
      red. eauto. }
    etransitivity; eauto. }

  assert (E0 ⊆₁ acts_set G) as CTEE.
  { unfold E0.
    rewrite TCCOH'.(coveredE).
    rewrite TCCOH'.(issuedE).
    rewrite wf_sbE. basic_solver. }

  assert (wf_thread_state (ES.cont_thread S q) state) as GPC.
  { eapply contwf; eauto. apply SRC. }

  set (thread := ES.cont_thread S q).

  assert (wf_thread_state thread state') as GPC'.
  { eapply wf_thread_state_steps; eauto. }

  assert (CREP_weak :
            forall e (CTE : E0 e),
            exists index : nat,
              ⟪ EREP : e = ThreadEvent thread index ⟫).
  { ins. unfold E0 in CTE. destruct CTE as [AA BB].
    destruct e; simpls; rewrite <- AA in *; desf.
    eauto. }
  
  assert (exists ctindex,
             ⟪ CCLOS :forall index (LT : index < ctindex),
                 E0 (ThreadEvent thread index) ⟫ /\
             ⟪ CREP : forall e (CTE : E0 e),
                 exists index : nat,
                   ⟪ EREP : e = ThreadEvent thread index ⟫ /\
                   ⟪ ILT : index < ctindex ⟫ ⟫).
  { destruct (classic (exists e, E0 e)) as [|NCT].
    2: { exists 0. splits.
         { ins. inv LT. }
         ins. exfalso. apply NCT. eauto. }
    desc.
    assert (acyclic (Gsb ⨾ ⦗ E0 ⦘)) as AC.
    { arewrite (Gsb ⨾ ⦗E0⦘ ⊆ Gsb). apply sb_acyclic. }
    set (doml := filterP E0 G.(acts)).
    assert (forall c, (Gsb ⨾ ⦗E0⦘)＊ e c -> In c doml) as UU.
    { intros c SCC. apply rtE in SCC. destruct SCC as [SCC|SCC].
      { red in SCC. desf. apply in_filterP_iff. split; auto. by apply CTEE. }
      apply inclusion_ct_seq_eqv_r in SCC. apply seq_eqv_r in SCC.
      apply in_filterP_iff. split; auto; [apply CTEE|]; desf. }
    edestruct (last_exists doml AC UU) as [max [MM1 MM2]].
    assert (E0 max) as CTMAX.
    { apply rtE in MM1. destruct MM1 as [MM1|MM1].
      { red in MM1. desf. }
      apply inclusion_ct_seq_eqv_r in MM1. apply seq_eqv_r in MM1. desf. }
    assert (Tid_ thread max) as CTTID by apply CTMAX.
    destruct max as [l|mthread mindex].
    { simpls.
      unfold thread in *. rewrite <- CTTID in *. desf. }
    simpls. rewrite CTTID in *.
    assert (acts_set G (ThreadEvent thread mindex)) as EEM.
    { by apply CTEE. }
    exists (1 + mindex). splits.
    { ins. destruct CTMAX as [_ CTMAX].
      split; [by ins|].
     apply le_lt_or_eq in LT. destruct LT as [LT|LT].
      2: { inv LT. }
      assert ((ProgToExecution.G state').(acts_set) (ThreadEvent thread mindex)) as PP.
      { apply TEH.(tr_acts_set). by split. }
      assert (G.(acts_set) (ThreadEvent thread index)) as EEE.
      { apply TEH.(tr_acts_set). eapply acts_rep in PP; eauto. desc.
        eapply GPC'.(acts_clos). inv REP. omega. }
      assert (Gsb (ThreadEvent thread index) (ThreadEvent thread mindex)) as QQQ.
      { red.
        apply seq_eqv_l. split; auto.
        apply seq_eqv_r. split; auto.
        red. split; auto. omega. }
      destruct CTMAX as [AA|[z AA]]; [left|right].
      { apply TCCOH' in AA. apply AA. eexists.
        apply seq_eqv_r. split; eauto. }
      exists z. apply seq_eqv_r in AA. destruct AA as [AA1 AA2].
      apply seq_eqv_r. split; auto.
      apply rewrite_trans_seq_cr_cr.
      { apply sb_trans. }
      eexists; split; [|by eauto].
        by apply r_step. }
    ins. set (CTE' := CTE).
    apply CREP_weak in CTE'. desc.
    eexists. splits; eauto.
    destruct (le_gt_dec index mindex) as [LL|LL].
    { by apply le_lt_n_Sm. }
    exfalso.
    eapply MM2. apply seq_eqv_r. split; [|by apply CTE].
    red.
    apply seq_eqv_l. split; auto.
    apply seq_eqv_r. split; auto.
    red. rewrite EREP. by split. }
  desc.
  
  edestruct steps_middle_set with
      (thread:=ES.cont_thread S q)
      (state0:=state) (state':=state') as [state''].
  3: by apply EEI'.
  all: eauto.
  { ins.
    eapply rmw_in_thread_restricted_rmw in RMW; eauto.
    split; intros [TT XX]; split.
    1,3: by apply WF.(wf_rmwt) in RMW; rewrite <- TT; red in RMW; desf.
    all: destruct XX as [XX|XX]; [by left; eapply RMWCOV with (r:=r); eauto|right].
    all: destruct XX as [e XX].
    all: apply seq_eqv_r in XX; destruct XX as [SB II].
    all: exists e; apply seq_eqv_r; split; auto.
    2: { apply (wf_rmwi WF) in RMW.
         generalize SB RMW (@sb_trans G). basic_solver. }
    assert (GR r) as RR.
    { apply WF.(wf_rmwD) in RMW. destruct_seq RMW as [AAA BBB].
      type_solver. }
    apply (wf_rmwi WF) in RMW.
    destruct SB as [|SB]; subst.
    { eapply issuedW in II; eauto. type_solver. }
    destruct (classic (w = e)) as [|NEQ]; [by left|].
    assert (~ is_init r) as NINIT.
    { intros GG. eapply WF.(init_w) in GG.
      type_solver. }
    edestruct sb_semi_total_l with (y:=w) (z:=e); eauto.
    { apply RMW. }
    exfalso. eapply RMW; eauto. }
  desf.
  
  set (new_rf := cert_rf G sc TC' thread ⨾ ⦗ E0 \₁ D G TC' thread ⦘).
  set (new_rfi := ⦗ Tid_ thread ⦘ ⨾ new_rf ⨾ ⦗ Tid_ thread ⦘).
  set (new_rfe := ⦗ NTid_ thread ⦘ ⨾ new_rf ⨾ ⦗ Tid_ thread ⦘).

  assert (new_rff : functional new_rf⁻¹).
  { arewrite (new_rf ⊆ cert_rf G sc TC' thread).
    apply cert_rff; auto. }
  assert (new_rfif : functional new_rfi⁻¹).
  { arewrite (new_rfi ⊆ new_rf); auto.
    unfold new_rfi; basic_solver. }
  assert (new_rfef : functional new_rfe⁻¹).
  { arewrite (new_rfe ⊆ new_rf); auto.
    unfold new_rfe; basic_solver. }
  
  assert (new_rfi ⊆ Gsb) as NEWRFISB.
  { unfold new_rfi. unfolder. intros x y [TX [RFXY TY]].
    red in RFXY.
    apply seq_eqv_r in RFXY. destruct RFXY as [RFXY [EEY NDY]].
    apply cert_rfE in RFXY; auto. destruct_seq RFXY as [EX EY].
    apply cert_rfD in RFXY. destruct_seq RFXY as [WX RY].
    edestruct same_thread with (x:=x) (y:=y) as [[|SBXY]|SBXY]; eauto.
    { unfold thread in *. intros HH.
      destruct x; simpls.
      rewrite <- TX in *. desf. }
    { by rewrite TX. }
    { subst. exfalso. type_solver. }
    exfalso. eapply cert_rf_hb_sc_hb_irr; eauto.
    eexists. splits; eauto.
    eexists. splits.
    { eapply imm_s_hb.sb_in_hb; eauto. }
      by left. }

  set (new_rfe_ex := new_rfe ∪ ⦗ set_compl (codom_rel new_rfe) ⦘).

  assert (forall r, exists ! w, new_rfe_ex⁻¹ r w) as new_rfe_unique.
  { ins.
    destruct (classic ((codom_rel new_rfe) r)) as [X|X].
    { unfolder in X; desf.
      exists x; red; splits.
      unfold new_rfe_ex; basic_solver 12.
      unfold new_rfe_ex; unfolder; ins; desf.
      eapply new_rfef; basic_solver.
      exfalso; eauto. }
    exists r; red; splits.
    unfold new_rfe_ex; basic_solver 12.
    unfold new_rfe_ex; unfolder; ins; desf.
    unfolder in X; exfalso; eauto. }
 
  assert (exists new_value, forall x, (new_rfe_ex)⁻¹ x (new_value x)) as HH; desc.
  { apply (unique_choice (new_rfe_ex)⁻¹ (new_rfe_unique)). }

  set (get_val (v: option value) :=  match v with | Some v => v | _ => 0 end).

  set (new_val := fun r => get_val (val G.(lab) (new_value r))).

  assert (acts_set (ProgToExecution.G state) ⊆₁ C) as STATECOV.
  { intros x EE. apply GPC.(acts_rep) in EE. desc. subst. by apply PCOV. }

  assert (wf_thread_state (ES.cont_thread S q) state'') as GPC''.
  { eapply wf_thread_state_steps; [|by eauto]. done. }

  assert (doma (⦗Tid_ thread ⦘ ⨾ Gsb ⨾ ⦗E0⦘) E0) as PRSBE0.
  { red. intros x y SBXY.
    destruct_seq SBXY as [TX TY]. destruct TY as [TY EEY].
    split; auto.
    destruct EEY as [COVY|ISSY]; [left|right].
    { eapply dom_sb_covered; eauto.
      eexists. apply seq_eqv_r. eauto. }
    destruct ISSY as [z ISSY].
    apply seq_eqv_r in ISSY. destruct ISSY as [SBYZ ISSZ].
    exists z. apply seq_eqv_r. split; auto.
    generalize (@sb_trans G) SBXY SBYZ. basic_solver. }
  
  assert (new_rfi ≡ ⦗ E0 ⦘ ⨾ new_rfi ⨾ ⦗ E0 ⦘) as NEW_RFIE.
  { split; [|basic_solver].
    etransitivity.
    2: apply doma_helper.
    { unfold new_rfi, new_rf. basic_solver 10. }
    arewrite (new_rfi ⊆ ⦗Tid_ thread⦘ ⨾ Gsb). 2: done.
    generalize NEWRFISB. unfold new_rfi. basic_solver 6. }

  edestruct steps_old_restrict with (state0:=state'') (state':=state') as [ORMW]; eauto.
  desc. unnw.
  edestruct receptiveness_full with
      (tid:=ES.cont_thread S q)
      (s_init:=state) (s:=state'')
      (new_val:=new_val)
      (new_rfi:=new_rfi)
      (MOD:=E0 \₁ D G TC' thread) as [pre_cert_state]; eauto.
  { by rewrite CACTS. }
  { split; [|basic_solver].
    rewrite NEW_RFIE at 1.
    unfolder. intros x y [EEX [RFXY EEY]].
    set (AA := RFXY).
    unfold new_rfi in AA.
    destruct_seq AA as [TX TY].
    unfold new_rf in AA. apply seq_eqv_r in AA. destruct AA as [AA _].
    apply cert_rfD in AA. destruct_seq AA as [WX RY].
    splits; auto; unfold is_w, is_r.
    all: erewrite <- steps_preserve_lab with (state0:=state'') (state':=state'); eauto;
      [by erewrite tr_lab; eauto | | | by apply CACTS].
    3,4: by rewrite TY; eauto.
    all: by rewrite TX; eauto. }
  { rewrite NEWRFISB. unfold Execution.sb. basic_solver. }
  { unfold new_rfi, new_rf. basic_solver. }
  { rewrite <- CACTS. basic_solver. }
  { rewrite STATECOV.
    sin_rewrite sim_trav_step_covered_le.
    2: by red; eauto.
    rewrite <- C_in_D.
    basic_solver. }

  Ltac _ltt q thread E0 OC CC CACTS CCD := 
    rewrite OC; rewrite CC;
    rewrite CACTS;
    arewrite_id ⦗Gtid_ (ES.cont_thread S q)⦘; arewrite_id ⦗E0⦘ at 1;
    rewrite !seq_id_l;
    unfold E0, thread;
    rewrite CCD; auto;
    basic_solver.

  { _ltt q thread E0 OFAILDEP TEH.(tr_rmw_dep) CACTS dom_rmw_depE_in_D. }
  { _ltt q thread E0 OADDR TEH.(tr_addr) CACTS dom_addrE_in_D. }
  2: { _ltt q thread E0 OCTRL TEH.(tr_ctrl) CACTS dom_ctrlE_in_D. }

  { rewrite CACTS.
    unfolder; ins; desc.
    apply H2.
    destruct H as [TT [AA|AA]].
    { by apply C_in_D. }
    unfolder in AA. desf.
    { by apply I_in_D. }
    red. left. left. right.
    eexists. eexists. split.
    { by left. }
    apply seq_eqv_r. split; eauto.
    assert (R_ex Glab x) as UU.
    { admit. }
    red. apply seq_eqv_l. split.
    { by apply R_ex_in_R. }
    apply seq_eqv_r. split.
    2: by eapply issuedW; eauto.
    apply ct_step. left. right.
    apply seq_eqv_l. by split. }

  { rewrite ODATA, CACTS.
    arewrite_id ⦗E0⦘ at 1. rewrite seq_id_l.
    rewrite <- id_inter.
    arewrite (E0 ∩₁ set_compl (E0 \₁ D G TC' thread) ⊆₁ D G TC' thread).
    { unfolder. intros x [AA BB].
      destruct (classic (D G TC' thread x)); auto.
      exfalso. apply BB. desf. }
    rewrite TEH.(tr_data), !seqA. 
    arewrite_id ⦗Gtid_ (ES.cont_thread S q)⦘. rewrite !seq_id_l.
    unfold thread.
    generalize (dom_dataD_in_D q TCCOH'). basic_solver 10. }
  desf.

  assert (instrs pre_cert_state = instrs state) as INSTRSS.
  { eapply steps_same_instrs; eauto. }

  edestruct get_stable with (state0:=pre_cert_state) (thread:=thread)
    as [cert_state [CC _]].
  { (* TODO: add `stable_lprog thread (instrs state)` to SimRel. *)
    admit. }
  { eapply transitive_rt; [|by eauto].
    rewrite INSTRSS.
    (* TODO: add `(step thread)＊ (init (instrs state)) state` to SimRel. *)
    admit. }
  desc.
  
  assert (ProgToExecution.G cert_state = ProgToExecution.G pre_cert_state) as SCC.
  { eapply eps_steps_same_G; eauto. }

  assert (acts_set (ProgToExecution.G pre_cert_state) =
          acts_set (ProgToExecution.G state'')) as SS.
  { unfold acts_set. by rewrite RACTS. }

  exists cert_state.
  constructor; auto.
  all: try rewrite SCC.
  { red. ins. unfold certLab. rewrite SCC. desf.
    admit. }
  { ins.
    eapply same_label_up_to_value_trans; eauto.
    assert (Gtid e = (ES.cont_thread S q)) as BB.
    { red in EE. rewrite <- RACTS in EE. by apply CACTS. }
    assert (acts_set (ProgToExecution.G state'') e) as CC.
    { by red; rewrite RACTS. }

    assert (lab (ProgToExecution.G state'') e = Glab e) as AA. 
    2: { rewrite AA. red. desf. }
    erewrite <- steps_preserve_lab; try rewrite BB; eauto.
    eapply tr_lab; eauto.
    eapply steps_preserve_E; eauto. }
  { ins.
    eapply ES.unique_K in KK.
    3: by apply QQ.
    all: eauto.
    2: apply SRC.
    simpls. inv KK.
    eapply transitive_rt; eauto.
      by apply eps_steps_in_steps. }
  { unfold acts_set. by rewrite <- RACTS. }
  { rewrite <- RRMW, SS. rewrite ORMW, !CACTS.
    rewrite TEH.(tr_rmw), !seqA.
    rewrite seq_eqvC. seq_rewrite <- !id_inter.
    arewrite (E0 ∩₁ Gtid_ (ES.cont_thread S q) ≡₁ E0).
    2: done.
    rewrite set_interC. unfold E0. rewrite <- !set_interA. 
      by rewrite set_interK. }
  { admit. }
  { erewrite same_label_same_loc; eauto.
    all: admit. }
  { arewrite (cert_rf G sc TC' (ES.cont_thread S q) ⊆
              ⦗issued TC' ∪₁ set_compl (issued TC')⦘ ⨾
              cert_rf G sc TC' (ES.cont_thread S q)) at 1
      by rewrite set_compl_union_id, seq_id_l.
    rewrite id_union, seq_union_l.
    rewrite non_I_cert_rf; auto.
    { unionL; [|basic_solver].
      inv TR_STEP; simpls.

      3: assert (Gtid w = ES.cont_thread S q) as TX
          by (apply wf_rmwt in RMW; auto; rewrite <- RMW; auto).
      1,2: assert (Gtid w = ES.cont_thread S q) as TX by auto.

      3: assert (Gtid r = ES.cont_thread S q) as TR by auto.

      all: assert (~ is_init w) as NINITX
          by (intros AA; destruct w; simpls; desf;
              rewrite <- TX in *; desf).
      all: rewrite id_union, seq_union_l; unionL; [basic_solver|].
      all: unionR right.
      all: unfolder; intros x y [AA RF]; desf.
      
      3: rewrite TR in RF.
      1,2: rewrite TX in RF.
      all: assert (Gtid y = ES.cont_thread S q) as TY
          by (apply cert_rf_codomt in RF; generalize RF; basic_solver).

      all: apply cert_rfD in RF;       destruct_seq RF as [WX RY].
      all: apply cert_rfE in RF; auto; destruct_seq RF as [EX EY].
      all: assert (Gtid x = Gtid y) as TTT by (rewrite TY; auto).
      all: destruct (@same_thread G x y) as [[|SB]|SB]; desf; auto;
        [type_solver|].
      all: exfalso.
      all: eapply cert_rf_hb_sc_hb_irr; eauto.
      all: assert (Ghb y x) as HB by (apply imm_s_hb.sb_in_hb; auto).
      all: repeat (eexists; split; eauto). }
    eapply sim_trav_step_rel_covered.
    { red. eauto. }
    apply SRC. }
  admit.
Admitted.

Lemma simrel_cert_start TC' thread
      (TR_STEP : isim_trav_step G sc thread TC TC') : 
  exists q state',
    ⟪ SRCC : simrel_cert prog S G sc TC TC' f f q state' ⟫.
Proof.
  edestruct sim_cert_graph_start as [q [state' HH]]; eauto.
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

  { by narrow_hdom q CsbqDOM. }
  { admit. }
  { by narrow_hdom q CsbqDOM. }
  { by narrow_hdom q CsbqDOM. }
  { admit. }
  { apply SRC.(ftid). } 
  { apply SRC.(flab). }
  { admit. }
  { by narrow_hdom q CsbqDOM. } 
  { admit. }
  { admit. }
  { admit. }
  rewrite CsbqDOM.
  unfold ES.cc.
  rewrite <- restr_relE.
  rewrite restr_inter.
  rewrite restr_rel_mori.
  { rewrite (restr_relE _ (Scf S)). 
    rewrite SRC.(fimgNcf). 
      by rewrite inter_false_l. } 
  all: basic_solver.
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

Lemma simrel_cert_lbl_step TC' h q
      (state state' state'': (thread_lts (ES.cont_thread S q)).(Language.state))
      (SRCC : simrel_cert prog S G sc TC TC' f h q state'')
      (KK : K S (q, existT _ _ state))
      (LBL_STEP : lbl_step (ES.cont_thread S q) state state') :
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

  destruct LBL_STEP as [lbls ILBL_STEP].
  set (ILBL_STEP_ALT := ILBL_STEP).
  eapply ilbl_step_alt in ILBL_STEP_ALT; desf. 
  cdes ISTEP. 
  edestruct ISTEP0; desf.
  { set (thread := (ES.cont_thread S q)).
    set (a   := ThreadEvent thread (eindex state)).
    set (l   := (RegFile.eval_lexpr (regf state) lexpr)).

    assert (GE a) as aInGE.
    { admit. }

    assert (GR a) as aInGR.
    { admit. }

    assert (acts_set (ProgToExecution.G state'') a) as aInCertG.
    { admit. }

    edestruct cert_rf_complete as [w RFwa]; eauto.
    { unfold set_inter. splits.  
      2: by apply aInGR.
      admit. }

    assert (hdom q w) as wInHDOM.
    { eapply new_rf_ntid_iss_sb in RFwa; [|by apply SRCC].
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
    { admit. } 
    
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
          unfolder in *. 
          eexists; splits; eauto; right; repeat eexists; splits; eauto; desf. }
        unfolder; splits. 
        { right; repeat eexists; eauto. }
        unfold not; ins; apply waNSB. 
        destruct H as [[y [SBqdom wEQ]] NCw].
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
        repeat rewrite inter_union_l.
        repeat rewrite inter_union_r.
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

        { repeat rewrite seqA.
          rewrite seq_incl_cross.
          { rewrite <- restr_cross, restr_relE. 
            by rewrite SRCC.(himgNcf). }
          { rewrite dom_cross; [|red; basic_solver]. 
            eapply sbk_in_hhdom; eauto. }
          by rewrite codom_singl_rel. } 

        { repeat rewrite seqA.
          rewrite hbE; auto.
          rewrite set_union_minus with (s := SE S) (s' := f □₁ C) at 1.
          2 : 
            { etransitivity. 
              2 : eapply SRC.(fimg). 
              basic_solver. }
          rewrite id_union.  
          repeat rewrite seq_union_l. 
          rewrite inter_union_l.
          apply inclusion_union_l. 
          { repeat rewrite <- seqA.
            rewrite hbNCsb; eauto. 
            arewrite (Ssb S ⨾ ⦗SE S⦘ ≡ Ssb S). 
            { rewrite ES.sbE; auto; basic_solver. } 
            rewrite sbk_in_hhdom; eauto.
            rewrite <- seqA.
            rewrite seq_incl_cross.
            { rewrite <- restr_cross, restr_relE. 
              by rewrite SRCC.(himgNcf). }
            { admit. }
            by rewrite codom_singl_rel. }
          repeat rewrite seqA.
          rewrite seq_incl_cross.
          { rewrite <- restr_cross, restr_relE. 
            by rewrite SRCC.(himgNcf). }
          { arewrite (f □₁ C ≡₁ h □₁ C).
            { admit. }
            repeat rewrite set_collect_union.
            basic_solver 10. }
          repeat rewrite codom_seq.
          by rewrite codom_singl_rel. } 
        
        { repeat rewrite seqA. 
          rewrite seq_incl_cross.
          { rewrite <- restr_cross, restr_relE.
            by rewrite SRCC.(himgNcf). }
          { rewrite releaseC; eauto. 
            arewrite (f □₁ C ≡₁ h □₁ C).
            { admit. }
            rewrite dom_seq.
            repeat rewrite set_collect_union.
            basic_solver 10. }
          repeat rewrite codom_seq.
          rewrite codom_singl_rel; auto. } 

        repeat rewrite seqA.
        rewrite hbE; auto.
        rewrite set_union_minus with (s := SE S) (s' := f □₁ C) at 1.
        2: { etransitivity. 
             2: eapply SRC.(fimg). 
             basic_solver. }
        rewrite id_union.  
        repeat rewrite seq_union_l. 
        rewrite inter_union_l.
        apply inclusion_union_l.  
        { repeat rewrite <- seqA.
          rewrite hbNCsb; eauto. 
          arewrite (Ssb S ⨾ ⦗SE S⦘ ≡ Ssb S). 
          { rewrite ES.sbE; auto; basic_solver. } 
          rewrite releaseC; eauto. 
          repeat rewrite seqA.
          rewrite <- seqA.
          rewrite seq_incl_cross.
          { rewrite <- restr_cross, restr_relE. 
              by rewrite SRCC.(himgNcf). }
          { admit. }
          repeat rewrite codom_seq.
            by rewrite codom_singl_rel. }
        repeat rewrite seqA.
        rewrite seq_incl_cross.
        { rewrite <- restr_cross, restr_relE. 
            by rewrite SRCC.(himgNcf). }
        { arewrite (f □₁ C ≡₁ h □₁ C).
          { admit. }
          repeat rewrite set_collect_union.
          basic_solver 10. }
        repeat rewrite codom_seq.
        rewrite codom_singl_rel; auto. }
      
      { admit. }

      { cdes ES_BSTEP_.

        red; split; [|basic_solver].
        rewrite JF', ESstep.basic_step_cf; eauto. 
        repeat rewrite csE.
        repeat rewrite transp_cross.
        repeat rewrite inter_union_l.
        repeat rewrite inter_union_r. 
        unfold eq_opt.
        relsf.
        repeat rewrite unionA.
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