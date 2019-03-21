Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CombRelations SimTraversal SimulationRel AuxRel.
Require Import AuxRel AuxDef ImmProperties 
        EventStructure Consistency Step EventToAction SimRelCont SimRel.

Set Implicit Arguments.
Local Open Scope program_scope.

Section Compilation.
  Variable prog : Prog.t.
  Variable G : execution.
  Variable sc : relation actid.

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

  Section Extraction.

    Variable S : ES.t.
    Variable TC : trav_config.
    Variable f : actid -> eventid.
  
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

    Notation "'C'"  := (covered TC).
    Notation "'I'"  := (issued TC).

    Definition extracted A := 
    ⟪ Restr : good_restriction S A ⟫ /\
    ⟪ GACTS : GE   ≡₁ e2a S □₁ A ⟫ /\
    ⟪ GSB   : Gsb  ≡  e2a S □ (Ssb ∩ A × A) ⟫ /\
    ⟪ GRMW  : Grmw ≡  e2a S □ (Srmw ∩ A × A) ⟫ /\
    ⟪ GRF   : Grf  ≡  e2a S □ (Srf ∩ A × A) ⟫ /\
    ⟪ GCO   : Gco  ≡  e2a S □ (Sco ∩ A × A) ⟫.

    Lemma simrel_extracted  
          (SRC : simrel_common prog S G sc TC f)
          (COVG : GE ⊆₁ C) :
      extracted (f □₁ GE).
    Proof. admit. Admitted.

  End Extraction.

  Lemma compilation_correctness 
        (nInitProg : ~ IdentMap.In tid_init prog)
        (PExec : program_execution prog G)
        (WF : Execution.Wf G)
        (CONS : imm_consistent G sc) :
    exists S A,
      ⟪STEPS : (ESstep.t Weakestmo)＊ (ES.init prog) S⟫ /\
      ⟪EXEC  : extracted S A⟫.

End Compilation.