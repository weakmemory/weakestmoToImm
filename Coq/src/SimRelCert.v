Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_hb SimulationRel
     SubExecution.
Require Import AuxRel AuxDef EventStructure Construction Consistency SimRel.
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
  Variable q : ES.cont_label.
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
  
  Definition sbq_dom :=
    match q with
    | ES.CInit  _ => ∅
    | ES.CEvent e => Gtid_ qtid ∩₁ dom_rel (Gsb^? ⨾ ⦗ eq (g e) ⦘)
    end.
    
  Notation "'hdom'" := (C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘) ∩₁ GNtid_ qtid) ∪₁ sbq_dom) (only parsing).
      
  Record simrel_cert :=
    { sim : simrel prog S G sc TC f;

      cert : sim_cert_graph;

      tr_step :
        exists e,
          ⟪ TIDE : Gtid e = qtid ⟫ /\
          ⟪ TCSTEP : itrav_step G sc e TC TC' ⟫;

      hgtrip : ⦗ hdom ⦘ ⨾ ↑ (compose g h) ⊆ eq;

      hinj : inj_dom hdom h;
      himg : h □₁ hdom ⊆₁ SE;
      hoth : (h □₁ set_compl hdom) ∩₁ SE ≡₁ ∅;
      hlab : eq_dom hdom certLab (compose Slab h);
      htid : compose Stid h = Gtid;

      hco : h □ ⦗ hdom ⦘ ⨾ Gco ⨾ ⦗ hdom ⦘ ⊆ Sco;

      cimgNcf : ⦗ h □₁ hdom ⦘ ⨾ Scf ⨾ ⦗ h □₁ hdom ⦘ ≡ ∅₂;
      
      complete_fdom :
        (h □₁ hdom) ∩₁ SR ⊆₁ codom_rel (⦗ h □₁ hdom ⦘ ⨾ Srf);

      imgcc : ⦗ f □₁ sbq_dom ⦘ ⨾ Scc ⨾ ⦗ Stid_ qtid ⦘ ⊆
              ⦗ h □₁ GW ⦘ ⨾ Sew ⨾ Ssb^= ;
    }.
End SimRelCert.

Section SimRelLemmas.

Variable prog : Prog.t.
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

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Notation "'GR'" := (fun a => is_true (is_r Glab a)).
Notation "'GW'" := (fun a => is_true (is_w Glab a)).

Notation "'Gsb'" := (G.(sb)).
Notation "'Ghb'" := (G.(imm_hb.hb)).
Notation "'Grf'" := (G.(rf)).
Notation "'Gco'" := (G.(co)).

Notation "'C'"  := (covered TC).
Notation "'I'"  := (issued TC).

Variable SRC : simrel prog S G sc TC f.

Lemma sim_cert_graph_start TC' e
      (TR_STEP : itrav_step G sc e TC TC') : 
  exists q state',
    ⟪ QTID : ES.cont_thread S q = tid e ⟫ /\
    ⟪ CsbqDOM : sbq_dom S G q ⊆₁ covered TC ⟫ /\
    ⟪ SRCG : sim_cert_graph S G TC' q state' ⟫.
Proof.
  set (E0 := Tid_ (tid e) ∩₁ (covered TC' ∪₁ dom_rel (Gsb^? ;; <| issued TC' |>))).
  set (G0 := restrict G E0).
  (* assert (exists state'', *)
  (*            ⟪ STEPS'' : (step thread)＊ state state'' ⟫ /\ *)
  (*            ⟪ TEH''   : thread_restricted_execution G0 thread state''.(ProgToExecution.G) ⟫). *)



  (* destruct (classic (exists e'', (C ∩₁ Tid_ (tid e)) e'')) as [[e'' [CC' TIDE']]|NN]. *)
  (* 2: { exists (ES.CInit (tid e)). *)

Admitted.

Lemma simrel_cert_start TC' e
      (TR_STEP : itrav_step G sc e TC TC') : 
  exists q state',
    ⟪ SRCC : simrel_cert prog S G sc TC TC' f f q state' ⟫.
Proof.

  assert (forall A (s s': A -> Prop), s ∪₁ s' ≡₁ s' ∪₁ s) as set_union_comm.
  { basic_solver. } 
  assert (forall A (s s' s'': A -> Prop), s ∪₁ (s' ∪₁ s'') ≡₁ (s ∪₁ s') ∪₁ s'') as set_union_assoc.
  { basic_solver. } 

  edestruct sim_cert_graph_start as [q [state' HH]]; eauto.
  desf.
  exists q. exists state'.
  constructor; auto.
  { eexists; eauto. }
  (* TODO: get rid of repetition *)
  { arewrite (NTid_ (ES.cont_thread S q) ⊆₁ fun _ => True).
    rewrite set_inter_full_r.
    rewrite CsbqDOM.
    rewrite set_union_comm.
    rewrite set_union_assoc.
    rewrite set_unionK.
    apply SRC. }
  { arewrite (NTid_ (ES.cont_thread S q) ⊆₁ fun _ => True).
    rewrite set_inter_full_r.
    rewrite CsbqDOM.
    rewrite set_union_comm.
    rewrite set_union_assoc.
    rewrite set_unionK.
    apply SRC. } 
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