Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CombRelations SimTraversal SimulationRel AuxRel.
Require Import AuxRel AuxDef EventStructure Consistency EventToAction LblStep 
        CertGraph CertRf.

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

  Definition thread_lts (tid : thread_id) : Language.t :=
    @Language.mk
      (list Instr.t) state
      init
      is_terminal
      (ilbl_step tid).

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

  Variable TC : trav_config.

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Definition pc thread :=
    C ∩₁ GTid thread \₁ dom_rel (Gsb ⨾ ⦗ C ⦘).

  Variable sc : relation actid.

  Notation "'Gvf'" := (furr G sc).

  Record simrel_graph := 
    { gprclos : forall thread m n (LT : m < n) (EE : GE (ThreadEvent thread n)),
        GE (ThreadEvent thread m);
      rmwclos : forall r w (RMW : Grmw r w), C r <-> C w;
      irelcov : GW ∩₁ GRel ∩₁ I ⊆₁ C;
    }.

  Variable f : actid -> eventid.

  Notation "'fdom'" := (C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘)) (only parsing).
  
  Record simrel_cont :=
    { contlang : forall k lang (state : lang.(Language.state))
                        (INK : K (k, existT _ lang state)),
        lang = thread_lts (ES.cont_thread S k);

      contwf : forall k (state : thread_st (ES.cont_thread S k))
                      (INK : K (k, thread_cont_st (ES.cont_thread S k) state)),
          wf_thread_state (ES.cont_thread S k) state;

      contstable : forall k (state : thread_st (ES.cont_thread S k))
                          (INK : K (k, thread_cont_st (ES.cont_thread S k) state)), 
          stable_state (ES.cont_thread S k) state;

      contrun : forall thread (lprog : thread_syntax thread) 
                       (INPROG : IdentMap.find thread prog = Some lprog),
          exists (state : thread_st thread),
            ⟪ INK : K (CInit thread, thread_cont_st thread state) ⟫ /\
            ⟪ INITST : (istep thread [])＊ (thread_init_st thread lprog) state⟫;

      continit : forall thread (state : thread_st thread)
                        (INKi : K (CInit thread, thread_cont_st thread state)),
          state.(eindex) = 0;

      contseqn : forall e (state : thread_st (Stid e))
                        (INKe : K (CEvent e, thread_cont_st (Stid e) state)),
          state.(eindex) = 1 + ES.seqn S e;

      contpc : forall e (state : (thread_st (Gtid e)))
                      (PC : pc (Gtid e) e)
                      (INK : K (CEvent (f e), thread_cont_st (Gtid e) state)),
          @sim_state G sim_normal C (Gtid e) state;
    }.

  Record simrel_common :=
    { noinitprog : ~ IdentMap.In tid_init prog;
      gprog : program_execution prog G;
      
      gwf   : Execution.Wf G;
      swf   : ES.Wf S;
      
      gcons : imm_consistent G sc;
      scons : @es_consistent S Weakestmo;

      tccoh : tc_coherent G sc TC;
      
      sr_cont : simrel_cont;
      sr_graph : simrel_graph;

      gE : g □₁ SE ⊆₁ GE;
      gEinit : GEinit ⊆₁ g □₁ SEinit;

      grmw : g □ Srmw ⊆ Grmw;
      gjf  : g □ Sjf  ⊆ Gvf;
      gew  : g □ Sew  ⊆ ⦗I⦘;
      gco  : g □ Sco  ⊆ Gco;
      
      grfrmw : g □ (Srf ⨾ Srmw) ⊆ Grf ⨾ Grmw;

      fco : f □ ⦗ fdom ⦘ ⨾ Gco ⨾ ⦗ fdom ⦘ ⊆ Sco;

      fimgNcf : ES.cf_free S (f □₁ fdom);
      
      complete_fdom :
        (f □₁ fdom) ∩₁ SR ⊆₁ codom_rel (⦗ f □₁ fdom ⦘ ⨾ Srf);

      gffix : fixset fdom (g ∘ f);

      finj : inj_dom_s fdom f;  
      fimg : f □₁ fdom ⊆₁ SE;
      foth : (f □₁ set_compl fdom) ∩₁ SE ≡₁ ∅;
      flab : eq_dom (C ∪₁ I) (Slab ∘ f) Glab;

      glab : same_lab_u2v_dom SE Slab (Glab ∘ g);

      finitIncl : SEinit ⊆₁ f □₁ GEinit;

      vis  : f □₁ fdom ⊆₁ vis S;
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

  Definition cert_dom thread state :=
    (C ∪₁ (dom_rel (Gsb^? ⨾ ⦗ I ⦘) ∩₁ GNTid thread) ∪₁
      state.(ProgToExecution.G).(acts_set)).
  
  Notation "'hdom'" :=  (cert_dom (ES.cont_thread S q) state) (only parsing).

  Definition Kstate : cont_label * ProgToExecution.state -> Prop :=
    fun l =>
      match l with
      | (ll, lstate) =>
        exists (st : (thread_lts (ES.cont_thread S ll)).(Language.state)),
          ⟪ SSTATE : lstate = st ⟫ /\
          ⟪ KK     : K (ll, existT _ _ st) ⟫
      end.

  Record simrel_cert :=
    { sim_com : simrel_common;

      cstate_stable : stable_state qtid state';
      cstate_q_cont : Kstate (q, state);
      cstate_reachable : (step qtid)＊ state state';
      cstate_covered : C ∩₁ GTid qtid ⊆₁ contE;

      cert : cert_graph G sc TC TC' qtid state';

      tr_step : isim_trav_step G sc qtid TC TC';

      ghtrip : ⦗ hdom ⦘ ⨾ ↑ (g ∘ h) ⊆ eq;
      
      (* hgfix_sbk : fixset (ES.cont_sb_dom S q) (h ∘ g);  *)

      jfehI  : dom_rel Sjfe ⊆₁ dom_rel (Sew^? ⨾ ⦗ h □₁ I ⦘);

      hinj     : inj_dom_s hdom h;
      himg     : h □₁ hdom ⊆₁ SE;
      hoth     : (h □₁ set_compl hdom) ∩₁ SE ≡₁ ∅;

      hlabCI : eq_dom (C ∪₁ I) Glab (Slab ∘ h);
      hlabTHRD : eq_dom contE certLab (Slab ∘ h);

      hco : h □ ⦗ hdom ⦘ ⨾ Gco ⨾ ⦗ hdom ⦘ ⊆ Sco;

      himgNcf : ES.cf_free S (h □₁ hdom);
      
      complete_hdom :
        (h □₁ hdom) ∩₁ SR ⊆₁ codom_rel (⦗ h □₁ hdom ⦘ ⨾ Srf);

      hfeq  : eq_dom (C ∪₁ fdom \₁ contE) f h; 

      (* imgcc : ⦗ f □₁ sbq_dom ⦘ ⨾ Scc ⨾ ⦗ h □₁ sbq_dom ⦘ ⊆ *)
      (*         ⦗ h □₁ GW ⦘ ⨾ Sew ⨾ Ssb⁼ ; *)

      release_issh_cov : dom_rel (Srelease ⨾ Sew^? ⨾ ⦗ h □₁ I ⦘) ⊆₁ h □₁ C;
    }.

End SimRelDef.