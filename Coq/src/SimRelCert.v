Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig SimTraversal
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

      cimgNcf : ⦗ h □₁ hdom ⦘ ⨾ Scf ⨾ ⦗ h □₁ hdom ⦘ ≡ ∅₂;
      
      complete_fdom :
        (h □₁ hdom) ∩₁ SR ⊆₁ codom_rel (⦗ h □₁ hdom ⦘ ⨾ Srf);

      imgcc : ⦗ f □₁ sbq_dom ⦘ ⨾ Scc ⨾ ⦗ Stid_ qtid ⦘ ⊆
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
  set (E0 := Tid_ thread ∩₁ (covered TC' ∪₁ dom_rel (Gsb^? ⨾ ⦗ issued TC' ⦘))).
  set (G0 := restrict G E0).
  edestruct cont_tid_state with (thread:=thread) as [state [q]]; eauto.
  { admit. }
  desf.
  (* assert (exists state'', *)
  (*            ⟪ STEPS'' : (step (tid e))＊ state state'' ⟫ /\ *)
  (*            ⟪ TEH''   : thread_restricted_execution *)
  (*                          G0 (tid e) state''.(ProgToExecution.G) ⟫). *)

  (* destruct (classic (exists e'', (C ∩₁ Tid_ (tid e)) e'')) as [[e'' [CC' TIDE']]|NN]. *)
  (* 2: { exists (CInit (tid e)). *)
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