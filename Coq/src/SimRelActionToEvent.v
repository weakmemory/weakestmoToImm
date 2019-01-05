Require Import Program.Basics Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CombRelations SimTraversal SimulationRel AuxRel.
Require Import AuxRel AuxDef EventStructure Consistency Construction 
        EventToAction LblStep SimRelCont.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelActionToEvent.
  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G : execution.
  
  Variable a2e : actid -> eventid.
  Variable a2eD : actid -> Prop.

  Notation "'SE'" := S.(ES.acts_set).
  Notation "'SEinit'" := S.(ES.acts_init_set).
  Notation "'SEninit'" := S.(ES.acts_ninit_set).

  Notation "'Stid'" := (S.(ES.tid)).
  Notation "'Slab'" := (S.(ES.lab)).
  Notation "'Sloc'" := (loc S.(ES.lab)).

  Notation "'K'" := S.(ES.cont_set).

  Notation "'STid' t" := (fun x => Stid x = t) (at level 1).

  Notation "'Ssb'" := (S.(ES.sb)).
  Notation "'Scf'" := (S.(ES.cf)).
  Notation "'Srmw'" := (S.(ES.rmw)).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).

  Notation "'Gtid'" := (tid).
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gloc'" := (loc G.(lab)).
  
  Notation "'GTid' t" := (fun x => tid x = t) (at level 1).
  Notation "'GNTid' t" := (fun x => tid x <> t) (at level 1).

  Notation "'Gsb'" := (G.(sb)).
  Notation "'Grmw'" := (G.(rmw)).

  Record simrel_a2e := 
    { a2e_inj : inj_dom_s a2eD a2e;
      a2e_img : a2e □₁ a2eD ⊆₁ SE;
      a2e_fix : fixset a2eD ((e2a S) ∘ a2e);
      (* Do we really need this ? *)
      (* a2e_oth : (a2e □₁ set_compl aD) ∩₁ SE ≡₁ ∅; *)
    }. 

  Section SimRelActionToEventProps.
    Variable SRA2E : simrel_a2e.

    

  End SimRelActionToEventProps.
      
End SimRelActionToEvent. 

Section SimRelActionToEventLemmas. 
  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G  : execution.
  Variable GPROG : program_execution prog G.
  Variable a2e : actid -> eventid.
  Variable a2eD : actid -> Prop.
  Variable WF : ES.Wf S.
  Variable SRA2E : simrel_a2e S a2e a2eD. 

  Notation "'SE' S" := S.(ES.acts_set) (at level 10).
  Notation "'SEinit' S" := S.(ES.acts_init_set) (at level 10).
  Notation "'SEninit' S" := S.(ES.acts_ninit_set) (at level 10).
  Notation "'Stid' S" := (S.(ES.tid)) (at level 10).
  Notation "'Slab' S" := S.(ES.lab) (at level 10).
  Notation "'Sloc' S" := (loc S.(ES.lab)) (at level 10).

  Notation "'K' S" := (S.(ES.cont_set)) (at level 10).

  Notation "'Stid_' t" := (fun x => Stid x = t) (at level 1).

  Notation "'Ssb' S" := S.(ES.sb) (at level 10).
  Notation "'Srmw' S" := S.(ES.rmw) (at level 10).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).

  Notation "'Glab'" := (G.(lab)).
  Notation "'Gtid'" := (tid).

  Notation "'Gtid_' t" := (fun x => tid x = t) (at level 1).
  Notation "'GNtid_' t" := (fun x => tid x <> t) (at level 1).

  Notation "'Gsb'" := (G.(sb)).
  Notation "'Grmw'" := G.(rmw).

  Notation "'thread_syntax' tid"  := 
    (Language.syntax (thread_lts tid)) (at level 10, only parsing).  

  Notation "'thread_st' tid" := 
    (Language.state (thread_lts tid)) (at level 10, only parsing).

  Notation "'thread_init_st' tid" := 
    (Language.init (thread_lts tid)) (at level 10, only parsing).

  Notation "'thread_cont_st' tid" :=
    (fun st => existT _ (thread_lts tid) st) (at level 10, only parsing).

  Notation "'cont_lang'" :=
    (fun S k => thread_lts (ES.cont_thread S k)) (at level 10, only parsing).

  Lemma simrel_a2e_set_equiv a2eD' (EQ : a2eD ≡₁ a2eD') : 
    simrel_a2e S a2e a2eD <-> simrel_a2e S a2e a2eD'.
  Proof. 
    clear prog GPROG G WF SRA2E.  
    split; [symmetry in EQ|].
    all: intros HH; inv HH; constructor;
      [ eapply inj_dom_s_more; eauto 
      | erewrite set_collect_more; eauto
      | eapply fixset_more; eauto ].
  Qed.

  (* Lemma basic_step_simrel_a2e k k' e e' S' *)
  (*       (st st' : thread_st (ES.cont_thread S k)) *)
  (*       (BSTEP_ : ESstep.t_basic_ (cont_lang S k) k k' st st' e e' S S') *)
  (*   let a2e' := upd_opt (upd a2e (e2a S' e) e) (option_map (e2a S') e') e' in *)
  (*   let A' := A ∪₁ eq (e2a S' e) ∪₁ eq_opt (option_map (e2a S') e') in *)
  (*   simrel_a2e S G a2e' A' Alab.  *)
      
End SimRelActionToEventLemmas. 