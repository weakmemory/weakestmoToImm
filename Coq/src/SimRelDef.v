Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CombRelations SimTraversal SimulationRel AuxRel.
Require Import AuxRel AuxDef EventStructure Consistency EventToAction LblStep 
        CertGraph CertRf SimRelCont SimRelEventToAction SimRelSubExec. 

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelDef.
  Variable prog : Prog.t.

  Variable S : ES.t.

  Notation "'SE'" := S.(ES.acts_set).
  Notation "'SEinit'" := S.(ES.acts_init_set).
  Notation "'SEninit'" := S.(ES.acts_ninit_set).
  Notation "'Stid'" := (S.(ES.tid)).
  Notation "'Slab'" := (S.(ES.lab)).
  Notation "'Sloc'" := (loc S.(ES.lab)).
  Notation "'K'" := S.(ES.cont_set).

  Notation "'STid' t" := (fun x => Stid x = t) (at level 1).

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

  Notation "'g'" := (e2a S). 

  Notation "'thread_syntax' tid"  := 
    (Language.syntax (thread_lts tid)) (at level 10, only parsing).  

  Notation "'thread_st' tid" := 
    (Language.state (thread_lts tid)) (at level 10, only parsing).

  Notation "'thread_init_st' tid" := 
    (Language.init (thread_lts tid)) (at level 10, only parsing).
  
  Notation "'thread_cont_st' tid" :=
    (fun st => existT _ (thread_lts tid) st) (at level 10, only parsing).

  Variable G : execution.

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

  Variable sc : relation actid.

  Variable TC : trav_config.

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Notation "'Gvf'" := (furr G sc).

  Record simrel_graph := 
    { gprclos : forall thread m n (LT : m < n) (EE : GE (ThreadEvent thread n)),
        GE (ThreadEvent thread m);
      rmwclos : forall r w (RMW : Grmw r w), C r <-> C w;
      irelcov : GW ∩₁ GRel ∩₁ I ⊆₁ C;
    }.

  Variable f : actid -> eventid.

  Notation "'fdom'" := (C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘)) (only parsing).
  
  Record simrel_common :=
    { noinitprog : ~ IdentMap.In tid_init prog;
      gprog : program_execution prog G;
      
      gwf   : Execution.Wf G;
      swf   : ES.Wf S;
      
      gcons : imm_consistent G sc;
      scons : @es_consistent S Weakestmo;

      tccoh : tc_coherent G sc TC;
      
      sr_cont : simrel_cont prog S G TC;
      sr_graph : simrel_graph;

      sr_e2a : simrel_e2a S G sc;
      sr_a2e_f : simrel_a2e S f (C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘));
      
      sr_exec_f : simrel_subexec S TC f (C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘)); 

      flab : eq_dom (C ∪₁ I) (Slab ∘ f) Glab;
      fvis : f □₁ fdom ⊆₁ vis S;
      finitIncl : SEinit ⊆₁ f □₁ GEinit;      
    }.
  
  Record simrel :=
    { src : simrel_common;
      gE_trav : g □₁ SE ⊆₁ fdom;
      jfefI  : dom_rel Sjfe ⊆₁ dom_rel (Sew^? ⨾ ⦗ f □₁ I ⦘);

      release_issf_cov : dom_rel (Srelease ⨾ Sew^? ⨾ ⦗ f □₁ I ⦘) ⊆₁ f □₁ C;
    }.

  Variable TC': trav_config.

  Notation "'C''"  := (covered TC').
  Notation "'I''"  := (issued TC').

  Variable h : actid -> eventid.

  Variable q : cont_label.

  Notation "'qtid'" := (ES.cont_thread S q) (only parsing).

  (* A state in a continuation related to q in S. *)
  Variable state : ProgToExecution.state.

  (* A state, which is reachable from 'state' and which represents a graph certification. *)
  Variable state' : ProgToExecution.state.

  Notation "'E0'" := (E0 G TC' qtid).

  Notation "'new_rf'" := (cert_rf G sc TC' qtid).
  
  Notation "'contG'" := state.(ProgToExecution.G).
  Notation "'certG'" := state'.(ProgToExecution.G).

  Notation "'contE'" := contG.(acts_set).
  Notation "'certE'" := certG.(acts_set).

  Notation "'certLab'" := (certLab G state').

  (* Definition cert_dom thread state := *)
  (*   (C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘) ∩₁ GNTid thread) ∪₁ *)
  (*     state.(ProgToExecution.G).(acts_set)). *)
  
  Notation "'hdom'" := (cert_dom G TC (ES.cont_thread S q) state) (only parsing).

  Definition Kstate : cont_label * ProgToExecution.state -> Prop :=
    fun l =>
      match l with
      | (ll, lstate) =>
        exists (st : (thread_lts (ES.cont_thread S ll)).(Language.state)),
          ⟪ SSTATE : lstate = st ⟫ /\
          ⟪ KK     : K (ll, existT _ _ st) ⟫
      end.

  Record simrel_cstate := 
    { cstate_stable : stable_state qtid state';
      cstate_q_cont : Kstate (q, state);
      cstate_reachable : (step qtid)＊ state state';
      cstate_covered : C ∩₁ GTid qtid ⊆₁ contE; 
    }.

  Record simrel_cert :=
    { sim_com : simrel_common;

      cert : cert_graph G sc TC TC' qtid state';
      cstate : simrel_cstate; 

      tr_step : isim_trav_step G sc qtid TC TC';

      hgfix : fixset (ES.cont_sb_dom S q) (h ∘ g);

      sr_a2e_h : simrel_a2e S h (cert_dom G TC qtid state);

      sr_exec_h : simrel_subexec S TC h (cert_dom G TC qtid state); 

      hlab : eq_dom (C ∪₁ I ∪₁ contE) (Slab ∘ h) certLab;
      hfeq : eq_dom (C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘) ∩₁ GNTid qtid)) f h; 

      (* imgcc : ⦗ f □₁ sbq_dom ⦘ ⨾ Scc ⨾ ⦗ h □₁ sbq_dom ⦘ ⊆ *)
      (*         ⦗ h □₁ GW ⦘ ⨾ Sew ⨾ Ssb⁼ ; *)
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

End SimRelDef.