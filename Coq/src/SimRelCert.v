Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution
     Traversal TraversalConfig SimTraversal SimTraversalProperties
     Prog ProgToExecution ProgToExecutionProperties Receptiveness
     imm_hb SimulationRel
     CertExecution2
     SubExecution.
Require Import AuxRel AuxDef EventStructure Construction Consistency SimRel Vf LblStep.
Require Import Coq.Logic.FunctionalExtensionality Classical_Prop.

Set Implicit Arguments.
Local Open Scope program_scope.

Definition cert_rf G TC thread :=
  G.(Gvf) ∩ same_loc G.(lab) ⨾ ⦗ (G.(acts_set) \₁ D G TC thread) ∩₁ is_r G.(lab) ⦘
                             \ G.(co) ⨾ G.(Gvf).
Definition cert_rfi G TC thread :=
  ⦗ fun x => tid x = thread ⦘ ⨾ cert_rf G TC thread ⨾ ⦗ fun x => tid x = thread ⦘.
Definition cert_rfe G TC thread :=
  ⦗ fun x => tid x <> thread ⦘ ⨾ cert_rf G TC thread ⨾ ⦗ fun x => tid x = thread ⦘.

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
  
  Notation "'certG'" := state'.(ProgToExecution.G).

  Notation "'g'" := (event_to_act S).

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

  Notation "'Gtid_' t" := (fun x => tid x = t) (at level 1).
  Notation "'GNtid_' t" := (fun x => tid x <> t) (at level 1).

  Notation "'GR'" := (fun a => is_true (is_r Glab a)).
  Notation "'GW'" := (fun a => is_true (is_w Glab a)).
  
  Notation "'Gsb'" := (G.(sb)).
  Notation "'Ghb'" := (G.(imm_hb.hb)).
  Notation "'Grf'" := (G.(rf)).
  Notation "'Gco'" := (G.(co)).

  Notation "'certE'" := certG.(acts_set).
  Notation "'certLab'" := (certG.(lab)).
  Notation "'certTid'" := (tid).
  Notation "'certRmw'" := (certG.(rmw)).
  
  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).
  Notation "'C''"  := (covered TC').
  Notation "'I''"  := (issued TC').

  Notation "'cert_rf'"  := (cert_rf  G TC' qtid).
  Notation "'cert_rfi'" := (cert_rfi G TC' qtid).
  Notation "'cert_rfe'" := (cert_rfe G TC' qtid).

  Record sim_cert_graph :=
    { cslab : eq_dom ((Gtid_ qtid) ∩₁ (C' ∪₁ I')) certLab Glab;
      cuplab : forall e (TIDE : Gtid_ qtid e)
                      (DOMI : dom_rel (Gsb ⨾ ⦗ I' ⦘) e),
          same_label_up_to_value (certLab e) (Glab e);
      cstate_stable : stable_state qtid state';
      cstate_reachable :
        forall (state : (thread_lts qtid).(Language.state))
               (KK : K (q, existT _ _ state)),
          (step qtid)＊ state state';
      
      dcertE : certE ≡₁ Gtid_ qtid ∩₁ dom_rel (Gsb^? ⨾ ⦗ C' ∪₁ I' ⦘);
      dcertRMW : certRmw ≡ ⦗ certE ⦘ ⨾ Grmw ⨾ ⦗ certE ⦘;
      
      rval : cert_rf ⊆ same_val certLab;
      oval : eq_dom (D G TC' qtid) (val certLab) (val Glab);
    }.

  Record sb_max i e :=
    (* TODO. It looks too strong. Shouldn't e' be in GE at very least?
       Doesn't inGi follow from sbMAX?
     *)
    { inGi  : Gtid_ i e;
      sbMAX : forall e', Gtid_ i e' -> Gsb^? e' e
    }.
  
  Notation "'sbq_dom'" := (g □₁ ES.cont_sb_dom S q) (only parsing).
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

      imgcc : ⦗ f □₁ sbq_dom ⦘ ⨾ Scc ⨾ ⦗ h □₁ sbq_dom ⦘ ⊆
              ⦗ h □₁ GW ⦘ ⨾ Sew ⨾ Ssb^= ;
    }.

  Record forward_pair (e : actid) (e' : eventid) 
         (state : (thread_lts (ES.cont_thread S (CEvent e'))).(Language.state)) :=
    { fp_Kq      : K (CEvent e', existT _ _ state);
      fp_inCertE : certE e;
      fp_tidEq   : certTid e = Stid e';
      fp_labEq   : certLab e = Slab e';
      fp_sbEq    : upd h e e' □ (Gsb ⨾ ⦗ eq e ⦘) ≡ Ssb ⨾ ⦗ eq e' ⦘;
      (* need to declare cert_rf ??? *)
      (* fp_imgrf   : upd h e e' □ (cert_rf ⨾ ⦗ eq e ⦘) ⊆ Srf; *)
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

Notation "'g'" := (event_to_act S).

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
  exists q state',
    ⟪ QTID : thread = ES.cont_thread S q  ⟫ /\
    ⟪ CsbqDOM : g □₁ ES.cont_sb_dom S q ⊆₁ covered TC ⟫ /\
    ⟪ SRCG : sim_cert_graph S G TC' q state' ⟫.
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
  assert (exists state', sim_cert_graph S G TC' q state') as [state' HH].
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
  exists cert_state.
  constructor.
  all: admit.
Admitted.

(* Lemma sbq_dom_incl_qtidTC' TC' q state' (SRCG: sim_cert_graph S G TC' q state') : *)
(*   sbq_dom S G q ⊆₁ (Gtid_ (ES.cont_thread S q)) ∩₁ (covered TC' ∪₁ issued TC'). *)
(* Proof.  *)
  

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

  1-3: by narrow_hdom q CsbqDOM.
  { admit. }
  { apply SRC.(ftid). } 
  { apply SRC.(flab). }
  { admit. }
  { by narrow_hdom q CsbqDOM. } 
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

Lemma simrel_cert_step TC' h q state'' 
      (state : (thread_lts (ES.cont_thread S q)).(Language.state))
      (SRCC : simrel_cert prog S G sc TC TC' f h q state'')
      (KK : K (q, existT _ _ state))
      (KNEQ : state <> state'') :
  exists (state' : (thread_lts (ES.cont_thread S q)).(Language.state)) q' S' h',
    ⟪ KSTEP : (lbl_step (ES.cont_thread S q)) state state' ⟫ /\
    ⟪ ESSTEP : (ESstep.t Weakestmo)^? S S' ⟫ /\
    ⟪ KK' : (ES.cont_set S') (q', existT _ _ state') ⟫ /\
    ⟪ SRCC' : simrel_cert prog S' G sc TC TC' f h' q' state'' ⟫.
Proof.
  set (thread := (ES.cont_thread S q)).
  set (REACHABLE := KK).
  eapply cstate_reachable in REACHABLE; [|by apply SRCC].
  assert ((lbl_step thread)^* state state'') as LSTEPS.
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
  edestruct STEP as [lbls ISTEP].
  edestruct ISTEP as [state_ [LBL_STEP [state__ H]]].
  destruct H as [EPS_STEPS H].
  unfold eqv_rel in H. destruct H as [H STABLE']. desf. 
  exists state'.
  edestruct LBL_STEP as [LB_NEQ [INSTRSEQ [instr [INSTR ISTEP_]]]].
  edestruct ISTEP_; try destruct (LB_NEQ LABELS).
  { set (e := ThreadEvent thread (eindex state)).
    set (e' := S.(ES.next_act)).
    set (q' := CEvent S.(ES.next_act)).
    set (lbl := Aload false ord l val).

    assert (Glab e = lbl) as eLab.
    { admit. } 
        
    exists q'. 
    destruct (excluded_middle_informative 
      (ES.cont_set S (q', existT _ (thread_lts thread) state'))
    ) as [EExists | ENExists ].
    { assert (SE e') as e'inSE. 
      { edestruct SRC. edestruct swf. 
        apply (K_inE e' (existT _ (thread_lts thread) state')). 
        apply EExists. }

      assert (Glab e = Slab e') as e'Lab.
      { admit. }

      admit. }
    
    eexists (ES.mk _ _ _ _ _ _ _ _ _).
    exists (upd h e e').
    splits; [by apply STEP | | |].
    { unfold "^?". right. 
      unfold ESstep.t.  
      splits. 
      { eapply ESstep.t_load. 
        { unfold ESstep.t_basic. 
          splits; eauto.
          { exists 1. splits; simpl; eauto. }
          do 2 eexists. 
          exists state, state', lbl, None.
          splits; simpl; eauto. 
          assert (lbls = [lbl]) as LBL_EQ. 
          { admit. }
          subst. 
          apply ISTEP. }
        { admit. } 
        admit.
        admit. } 
      admit. }
      admit. 
    admit. } 
  admit. 
  admit. 
  admit. 
  admit. 
  admit. 
Admitted.

Lemma simrel_cert_cc_dom TC' h q state'
  (SRCC : simrel_cert prog S G sc TC TC' f h q state') : 
  dom_rel (Scc ⨾ ⦗ ES.cont_sb_dom S q ⦘) ⊆₁ f □₁ I. 
Proof. 
  admit.
Admitted.

Lemma simrel_cert_end prog S G sc TC TC' f h (*certG*) i q
      (sbMAX: sb_max G i q)
      (SRcert: simrel_cert prog S G sc TC TC' f h q) : 
  exists f', 
    simrel prog S G sc TC' f'.
Proof.
Admitted.

End SimRelLemmas.