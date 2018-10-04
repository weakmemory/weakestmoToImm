Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution
     Traversal TraversalConfig SimTraversal SimTraversalProperties
     Prog ProgToExecution ProgToExecutionProperties Receptiveness
     imm_hb SimulationRel
     CertExecution2
     SubExecution.
Require Import AuxRel AuxDef EventStructure Construction Consistency SimRel Vf.
Require Import Coq.Logic.FunctionalExtensionality Classical_Prop.

Set Implicit Arguments.

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
  Notation "'certRmw'" := (certG.(rmw)).
  
  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).
  Notation "'C''"  := (covered TC').
  Notation "'I''"  := (issued TC').

  Record sim_cert_graph :=
    { cslab : eq_dom ((Gtid_ qtid) ∩₁ (C' ∪₁ I')) certLab Glab;
      cuplab : forall e (TIDE : Gtid_ qtid e)
                      (DOMI : dom_rel (Gsb ⨾ ⦗ I' ⦘) e),
          same_label_up_to_value (certLab e) (Glab e);
      cstate_reachable :
        forall (state : (thread_lts qtid).(Language.state))
               (KK : K (q, existT _ _ state)),
          (step qtid)^* state state';
      
      dcertE : certE ≡₁ Gtid_ qtid ∩₁ dom_rel (Gsb^? ⨾ ⦗ C' ∪₁ I' ⦘);
      dcertRMW : certRmw ≡ ⦗ certE ⦘ ⨾ Grmw ⨾ ⦗ certE ⦘;

      (* TODO. Reflect the following properties of the certification graph: *)
      (* ⟪ NEW_VAL1 : forall r w (RF: new_rfi w r), *)
      (*     val (s'.(G).(lab)) r = val (s'.(G).(lab)) w ⟫ /\ *)
      (* ⟪ NEW_VAL2 : forall r (RR : is_r s'.(G).(lab) r) (IN: MOD r) *)
      (*                     (NIN: ~ (codom_rel new_rfi) r), *)
      (*     val (s'.(G).(lab)) r = Some (new_val r) ⟫ /\ *)
      (* ⟪ OLD_VAL : forall a (NIN: ~ MOD a), *)
      (*     val (s'.(G).(lab)) a = val (s.(G).(lab)) a ⟫. *)
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

      hgtrip : ⦗ hdom ⦘ ⨾ ↑ (compose g h) ⊆ eq;

      hinj : inj_dom hdom h;
      himg : h □₁ hdom ⊆₁ SE;
      hoth : (h □₁ set_compl hdom) ∩₁ SE ≡₁ ∅;
      htid : compose Stid h = Gtid;

      hlabCI : eq_dom (C ∪₁ I) Glab (compose Slab h);
      hlabTHRD : eq_dom sbq_dom certLab (compose Slab h);

      hco : h □ ⦗ hdom ⦘ ⨾ Gco ⨾ ⦗ hdom ⦘ ⊆ Sco;

      himgNcf : ⦗ h □₁ hdom ⦘ ⨾ Scf ⨾ ⦗ h □₁ hdom ⦘ ≡ ∅₂;
      
      complete_fdom :
        (h □₁ hdom) ∩₁ SR ⊆₁ codom_rel (⦗ h □₁ hdom ⦘ ⨾ Srf);

      imgcc : ⦗ f □₁ sbq_dom ⦘ ⨾ Scc ⨾ ⦗ h □₁ sbq_dom ⦘ ⊆
              ⦗ h □₁ GW ⦘ ⨾ Sew ⨾ Ssb^= ;
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
      (* TODO: continue from here. *)
      admit. }
    unionR left.
    assert (covered TC ⊆₁ covered TC') as AA.
    { eapply sim_trav_step_covered_le.
      red. eauto. }
    etransitivity; [|by apply AA].
    admit. }

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
  set (new_rf:= Gvf ∩ same_loc Glab ;; <| (GE \₁ D G TC' thread) ∩₁ GR |>
                    \ Gco ;; Gvf).
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

Lemma simrel_cert_cc_dom TC' h q state'
  (SRCC: simrel_cert prog S G sc TC TC' f h q state') : 
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

Lemma simrel_cert_step prog S G sc TC TC' f h (*certG*) i q
      (NsbMAX : ~ sb_max G i q)
      (SRcert: simrel_cert prog S G sc TC TC' f h q) : 
  exists S' h' q',
    (ESstep.t Weakestmo)^? S S' /\
    simrel_cert prog S' G sc TC TC' f h' q'.
Proof.
Admitted.

End SimRelLemmas.