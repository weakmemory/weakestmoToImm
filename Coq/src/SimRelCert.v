Require Import Omega.
Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution
     Traversal TraversalConfig SimTraversal SimTraversalProperties
     Prog ProgToExecution ProgToExecutionProperties Receptiveness
     imm imm_hb SimulationRel
     CertExecution2
     SubExecution.
Require Import AuxRel AuxDef EventStructure Construction Consistency SimRel Vf LblStep CertRf.
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
  Variable new_rf : relation actid.
  
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
  Notation "'Gvf'" := G.(Gvf).

  Notation "'Gtid_' t" := (fun x => tid x = t) (at level 1).
  Notation "'GNtid_' t" := (fun x => tid x <> t) (at level 1).

  Notation "'GR'" := (fun a => is_true (is_r Glab a)).
  Notation "'GW'" := (fun a => is_true (is_w Glab a)).
  
  Notation "'Gsb'" := (G.(sb)).
  Notation "'Ghb'" := (G.(imm_hb.hb)).
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

  Notation "'cert_rf'"  := (cert_rf G TC' qtid).
  Notation "'E0'" := (Gtid_ qtid ∩₁ (C' ∪₁ dom_rel (Gsb^? ⨾ ⦗ I' ⦘))).

  Record sim_cert_graph :=
    { cslab : eq_dom ((Gtid_ qtid) ∩₁ (C' ∪₁ I')) certLab Glab;
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
      new_rf_in_vf  : new_rf ⊆ Gvf;
      new_rf_iss_sb : new_rf ⊆ ⦗ I ⦘ ⨾ new_rf ∪ Gsb;
      new_rf_complete : GR ∩₁ certE ⊆₁ codom_rel new_rf;
      new_rff : functional new_rf⁻¹;

      oval : eq_dom (D G TC' qtid) (val certLab) (val Glab);
    }.
  
  Section CertGraphProperties.
    Variable SCG : sim_cert_graph.
    
    Lemma new_rf_w : new_rf ≡ ⦗ GW ⦘ ⨾ new_rf.
    Proof.
      split; [|basic_solver].
      intros w r HH. apply seq_eqv_l. split; [|done].
      apply SCG.(new_rf_in_vf) in HH.
      apply Avf_dom in HH. apply seq_eqv_l in HH.
      desf.
    Qed.

    Lemma cuplab e :
        same_label_up_to_value (certLab e) (Glab e).
    Proof.
      unfold certLab. desf.
      { by apply SCG. }
      red. desf.
    Qed.
    
    Lemma new_rfl_g : new_rf ⊆ same_loc Glab.
    Proof.
      intros w r HH.
      apply SCG.(new_rfl) in HH.
      red. red in HH.
      assert (same_label_up_to_value (certLab w) (Glab w)) as AA
          by apply cuplab.
      assert (same_label_up_to_value (certLab r) (Glab r)) as BB
          by apply cuplab.
      red in AA. red in BB.
      unfold loc in *.
      destruct (certLab r); destruct (Glab r);
        destruct (certLab w); destruct (Glab w); desf.
    Qed.

    Lemma new_rf_dom_f : f □₁ (dom_rel (new_rf ⨾ ⦗ certE ⦘)) ⊆₁ SE.
    Proof. 
      admit.
    Admitted.

  End CertGraphProperties.

  Record sb_max i e :=
    (* TODO. It looks too strong. Shouldn't e' be in GE at very least?
       Doesn't inGi follow from sbMAX?
     *)
    { inGi  : Gtid_ i e;
      sbMAX : forall e', Gtid_ i e' -> Gsb^? e' e
    }.
  
  Notation "'sbq_dom'" := (g □₁ ES.cont_sb_dom S q) (only parsing).
  Notation "'fdom'" := (C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘))) (only parsing).
  Notation "'hdom'" := (C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘) ∩₁ GNtid_ qtid) ∪₁ sbq_dom)
                         (only parsing).
      
  Record simrel_cert :=
    { sim : simrel prog S G sc TC f;

      cert : sim_cert_graph;

      tr_step : isim_trav_step G sc qtid TC TC';

      hgtrip : ⦗ hdom ⦘ ⨾ ↑ (g ∘ h) ⊆ eq;

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

  Lemma hsb : h □ (⦗ hdom ⦘ ⨾ Gsb ⨾ ⦗ hdom ⦘) ⊆ Ssb. 
    Proof.
    Admitted.

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

Notation "'SE'" := S.(ES.acts_set).
Notation "'SEinit'" := S.(ES.acts_init_set).
Notation "'Stid'" := (S.(ES.tid)).
Notation "'Slab'" := (S.(ES.lab)).
Notation "'Sloc'" := (loc S.(ES.lab)).
Notation "'K'"  := S.(ES.cont_set).

Notation "'Stid_' t" := (fun x => Stid x = t) (at level 1).

Notation "'Ssb'" := (S.(ES.sb)).
Notation "'Sjf'" := (S.(ES.jf)).
Notation "'Srf'" := (S.(ES.rf)).
Notation "'Sco'" := (S.(ES.co)).
Notation "'Scf'" := (S.(ES.cf)).
Notation "'Scc'" := (S.(ES.cc)).
Notation "'Sew'" := (S.(ES.ew)).
Notation "'Srmw'" := (S.(ES.rmw)).

Notation "'SR'" := (fun a => is_true (is_r Slab a)).
Notation "'SW'" := (fun a => is_true (is_w Slab a)).

Notation "'GE'" := G.(acts_set).
Notation "'Glab'" := (G.(lab)).
Notation "'Gtid'" := (tid).
Notation "'Grmw'" := G.(rmw).

Notation "'Gtid_' t" := (fun x => tid x = t) (at level 1).
Notation "'GNtid_' t" := (fun x => tid x <> t) (at level 1).

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Notation "'GR'" := (fun a => is_true (is_r Glab a)).
Notation "'GW'" := (fun a => is_true (is_w Glab a)).

Notation "'Gsb'" := (G.(sb)).
Notation "'Ghb'" := (G.(imm_hb.hb)).
Notation "'Grf'" := (G.(rf)).
Notation "'Gco'" := (G.(co)).
Notation "'Gvf'" := (G.(Gvf)).

Notation "'C'"  := (covered TC).
Notation "'I'"  := (issued TC).

Variable SRC : simrel prog S G sc TC f.

Lemma sim_cert_graph_start TC' thread
      (TR_STEP : isim_trav_step G sc thread TC TC') : 
  exists q state' new_rf,
    ⟪ QTID : thread = ES.cont_thread S q  ⟫ /\
    ⟪ CsbqDOM : g □₁ ES.cont_sb_dom S q ⊆₁ covered TC ⟫ /\
    ⟪ SRCG : sim_cert_graph S G TC TC' q state' new_rf ⟫.
Proof.
  assert (tc_coherent G sc TC') as TCCOH'.
  { eapply sim_trav_step_coherence.
    2: by apply SRC.
    red. eauto. }
  
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
  assert (exists state' new_rf, sim_cert_graph S G TC TC' q state' new_rf)
    as [state' [new_rf HH]].
  2: { eexists. eexists. splits; eauto. }
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
      { autounfold with unfolderDb. basic_solver. }
      rewrite set_collect_inter.
      apply set_subset_inter_l.
      left.
      eapply gtid_; eauto. }
    unionR left.
    assert (covered TC ⊆₁ covered TC') as AA.
    { eapply sim_trav_step_covered_le.
      red. eauto. }
    etransitivity; eauto. }

  edestruct steps_middle_set with
      (thread:=ES.cont_thread S q)
      (state0:=state) (state':=state') as [state''].
  3: by apply EEI'.
  all: eauto.
  { admit. }
  { admit. }
  { admit. }
  { admit. }
  desf.
  
  set (thread := ES.cont_thread S q).
  set (new_rf := Gvf ∩ same_loc Glab ⨾ ⦗ (GE \₁ D G TC' thread) ∩₁ GR ⦘
                     \ Gco ⨾ Gvf).
  set (new_rfi := ⦗ Tid_ thread ⦘ ⨾ new_rf ⨾ ⦗ Tid_ thread ⦘).
  set (new_rfe := ⦗ NTid_ thread ⦘ ⨾ new_rf ⨾ ⦗ Tid_ thread ⦘).

  assert (new_rfef : functional new_rfe⁻¹).
  { admit. }
    (* arewrite  (new_rfe ⊆ new_rf G Gsc T thread). *)
    (* unfold new_rfe; basic_solver. *)
    (*   by apply wf_new_rff. } *)

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
  
  edestruct receptiveness_full with
      (tid:=ES.cont_thread S q)
      (s_init:=state) (s:=state'')
      (new_val:=new_val)
      (new_rfi:=new_rfi)
      (MOD:=E0 \₁ D G TC' thread) as [cert_state].
  1-14: admit.

  desf.
  exists cert_state. eexists.
  constructor.
  all: admit.
Admitted.

(* Lemma sbq_dom_incl_qtidTC' TC' q state' (SRCG: sim_cert_graph S G TC' q state') : *)
(*   sbq_dom S G q ⊆₁ (Gtid_ (ES.cont_thread S q)) ∩₁ (covered TC' ∪₁ issued TC'). *)
(* Proof.  *)

Lemma simrel_cert_start TC' thread
      (TR_STEP : isim_trav_step G sc thread TC TC') : 
  exists q state' new_rf,
    ⟪ SRCC : simrel_cert prog S G sc TC TC' f f q state' new_rf ⟫.
Proof.
  edestruct sim_cert_graph_start as [q [state' [new_rf HH]]]; eauto.
  desf.
  exists q. exists state'. exists new_rf.
  constructor; auto.

  Ltac narrow_hdom q CsbqDOM :=
    arewrite (NTid_ (ES.cont_thread S q) ⊆₁ fun _ => True);
    rewrite set_inter_full_r;
    rewrite CsbqDOM;
    rewrite set_unionC;
    rewrite <- set_unionA;
    rewrite set_unionK;
    apply SRC.

  1-3: by narrow_hdom q CsbqDOM.
  { admit. }
  { apply SRC.(ftid). } 
  { apply SRC.(flab). }
  { admit. }
  { by narrow_hdom q CsbqDOM. } 
  { admit. }
  { admit. }
  { admit. }
  { rewrite CsbqDOM. 
    unfold ES.cc.
    rewrite <- restr_relE.
    rewrite restr_inter.
    rewrite restr_rel_mori.
    { rewrite (restr_relE _ Scf). 
      rewrite SRC.(fimgNcf). 
      by rewrite inter_false_l. } 
    all: basic_solver. }
Admitted.

Lemma simrel_cert_basic_step TC' h q new_rf lbls jf ew co
      (state state' state'': (thread_lts (ES.cont_thread S q)).(Language.state))
      (SRCC : simrel_cert prog S G sc TC TC' f h q state'' new_rf)
      (KK : K (q, existT _ _ state))
      (ILBL_STEP : ilbl_step (ES.cont_thread S q) lbls state state') :
  exists e e' lbl lbl' S',
    ⟪ ES_BSTEP : (ESstep.t_basic e e') S S' ⟫ /\
    ⟪ LBLS_EQ : lbls = opt_to_list lbl' ++ [lbl] ⟫ /\
    ⟪ LBL  : lbl  = S'.(ES.lab) e ⟫ /\
    ⟪ LBL' : lbl' = option_map S'.(ES.lab) e' ⟫ /\
    ⟪ JF' : S'.(ES.jf) ≡ jf ⟫ /\
    ⟪ EW' : S'.(ES.ew) ≡ ew ⟫ /\
    ⟪ CO' : S'.(ES.co) ≡ co ⟫.
Proof.
  set (ILBL_STEP_ALT := ILBL_STEP).
  eapply ilbl_step_alt in ILBL_STEP_ALT; desf. 
  cdes ISTEP. 
  edestruct ISTEP0; desf.

  Ltac solve_nupd state state' :=
    exists S.(ES.next_act); exists None;
    eexists; eexists None; eexists (ES.mk _ _ _ _ _ _ _ _ _);
    splits; simpl; eauto;  
    [ econstructor; eauto; splits;
      [ exists 1; splits; simpl; eauto 
      | do 2 eexists; exists state, state' ; eexists; exists None; 
        splits; simpl; eauto ] 
    | by rewrite upds ].

  Ltac solve_upd state state' :=
    exists S.(ES.next_act); exists (Some (1 + S.(ES.next_act)));
    eexists; eexists (Some _); eexists (ES.mk _ _ _ _ _ _ _ _ _);
    splits; simpl; eauto; 
    [ econstructor; eauto; splits;
      [ exists 2; splits; simpl; eauto 
      | do 2 eexists; exists state, state' ; eexists; eexists (Some _); 
          splits; simpl; eauto ] 
      | rewrite updo; [by rewrite upds | by omega]
      | by rewrite upds ].
  
  1-4: by (solve_nupd state state').
  all: by (solve_upd state state').
Qed. 

Lemma simrel_cert_lbl_step TC' h q new_rf
      (state state' state'': (thread_lts (ES.cont_thread S q)).(Language.state))
      (SRCC : simrel_cert prog S G sc TC TC' f h q state'' new_rf)
      (KK : K (q, existT _ _ state))
      (LBL_STEP : lbl_step (ES.cont_thread S q) state state') :
  exists  q' S' h',
    ⟪ ESSTEP : (ESstep.t Weakestmo)^? S S' ⟫ /\
    ⟪ KK' : (ES.cont_set S') (q', existT _ _ state') ⟫ /\
    ⟪ SRCC' : simrel_cert prog S' G sc TC TC' f h' q' state'' new_rf ⟫.
Proof.
  destruct LBL_STEP as [lbls ILBL_STEP].
  set (ILBL_STEP_ALT := ILBL_STEP).
  eapply ilbl_step_alt in ILBL_STEP_ALT; desf. 
  cdes ISTEP. 
  edestruct ISTEP0; desf.
  { set (thread := (ES.cont_thread S q)).
    set (a   := ThreadEvent thread (eindex state)).
    set (q'  := CEvent S.(ES.next_act)).
    set (l   := (RegFile.eval_lexpr (regf state) lexpr)).

    assert (GE a) as aInGE.
    { admit. }

    assert (GR a) as aInGR.
    { admit. }

    assert (acts_set (ProgToExecution.G state'') a) as aInCertG.
    { admit. }

    edestruct new_rf_complete as [w RFwa].
    { by apply SRCC. }
    { unfold set_inter. splits.  
      { apply aInGR. }
      eapply preserve_event.
      { eapply cstate_reachable. 
        (* Here we probably have to show that simrel_cert holds for S' *)
        { admit. }
        (* Then this should follow trivially *)
        admit. }
      admit. }

    edestruct simrel_cert_basic_step as [e [e' [lbl [lbl' [S' HH]]]]]; eauto; desf.

    assert (ES.event_to_act S' e = a) as g'eaEQ.
    { admit. } 
    
    assert (e' = None) as e'NONE.
    { cdes ES_BSTEP. desf. }
    
    rewrite e'NONE in ES_BSTEP. 
    rewrite e'NONE in LBLS_EQ.
    simpl in LBLS_EQ.
    inversion LBLS_EQ as [eSLAB].
    symmetry in eSLAB.

    assert (ESstep.t_ S S') as ES_STEP_.
    { eapply ESstep.t_load; simpl; eauto.
      unfold ESstep.add_jf.
      splits.
      { simpl. unfold is_r. by rewrite eSLAB. }
      { exists (h w).
        splits.
        { eapply new_rf_dom_f; eauto; [by apply SRCC|].
          autounfold with unfolderDb.
          do 4 eexists. splits; eauto. }
        { simpl. unfold is_w. admit. }
        admit.
        admit.
        cdes ES_BSTEP; rewrite EVENT; eauto. } }

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
          { eapply ESstep.step_vis_mon. eauto. apply SRC. }
          eapply ESstep.basic_step_acts_set_mon; eauto. }
        destruct (excluded_middle_informative (sb G w a)) as [waSB | waNSB].
        { apply inclusion_union_r; left. 
          admit. }
        (* apply (SRCC.(cert).(new_rf_iss_sb)) in RFwa. *)
        (* unfold union in RFwa; desf.  *)
        { assert (I w) as Iw.
          { apply (SRCC.(cert).(new_rf_iss_sb)) in RFwa.
            autounfold with unfolderDb in RFwa; desf. }
          apply inclusion_union_r; right. 
          autounfold with unfolderDb; ins; splits; desf.
          { erewrite <- SRCC.(hfeq). 
            { eapply ESstep.step_vis_mon; eauto; apply SRCC. 
              autounfold with unfolderDb in *. 
              eexists; splits; eauto; right; repeat eexists; splits; eauto; desf. }
            autounfold with unfolderDb; splits. 
            { right; repeat eexists; eauto. }
            unfold not; ins; apply waNSB. 
            destruct H as [[y [SBqdom wEQ]] NCw].
            erewrite ESstep.step_event_to_act in wEQ; eauto; [ | by apply SRC | admit ].
            eapply gsb; (* TODO: gsb should not depend on simrel *) 
              [ by eauto | by eauto | admit | ]. 
            autounfold with unfolderDb; repeat eexists; splits; eauto. 
            unfold ES.cont_sb_dom in SBqdom; desf.
            unfold set_inter in SBqdom.
            destruct SBqdom as [yTID ySBDOM].
            unfold dom_rel in ySBDOM. 
            destruct ySBDOM as [y' yy'SBrefl].
            admit. }
          edestruct ES_BSTEP; desf; omega. } }
      all: admit. } 

    exists q', S', (upd h a e).

    desf; splits. 
    { unfold "^?". right.
      unfold ESstep.t.  
      splits; auto. }
                 
    { admit. }

    { econstructor. 
      all: admit. } }

  all: admit. 
Admitted.

Lemma simrel_cert_step TC' h q state'' new_rf
      (state : (thread_lts (ES.cont_thread S q)).(Language.state))
      (SRCC : simrel_cert prog S G sc TC TC' f h q state'' new_rf)
      (KK : K (q, existT _ _ state))
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

Lemma simrel_cert_cc_dom TC' h q state' new_rf
  (SRCC : simrel_cert prog S G sc TC TC' f h q state' new_rf) : 
  dom_rel (Scc ⨾ ⦗ ES.cont_sb_dom S q ⦘) ⊆₁ f □₁ I. 
Proof. 
  admit.
Admitted.

End SimRelLemmas.