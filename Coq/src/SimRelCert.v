Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_hb SimulationRel.
Require Import AuxRel AuxDef EventStructure Construction Consistency SimRel.
Require Import Coq.Logic.FunctionalExtensionality Classical_Prop.

Set Implicit Arguments.

Section SimRelCert.
  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G  : execution.
  Variable certG : execution. 
  Variable GPROG : program_execution prog G.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable TC': trav_config.
  Variable f  : actid -> eventid.
  Variable q' : eventid.

  Notation "'g'" := (event_to_act).
  Notation "'q'" := (g S q').
  Notation "'qtid'" := (tid q).

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
  
  Notation "'GE'" := G.(acts_set).
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gtid'" := (tid).

  Notation "'Gtid_' t" := (fun x => tid x = t) (at level 1).

  Notation "'GR'" := (fun a => is_true (is_r Glab a)).
  Notation "'GW'" := (fun a => is_true (is_w Glab a)).
  
  Notation "'Gsb'" := (G.(sb)).
  Notation "'Ghb'" := (G.(imm_hb.hb)).
  Notation "'Grf'" := (G.(rf)).
  Notation "'Gco'" := (G.(co)).
  
  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).
  Notation "'C''"  := (covered TC').
  Notation "'I''"  := (issued TC').
    
  Definition tid_trav_step i :=
    exists e, Gtid e = i /\ itrav_step G sc e TC TC'.
      
  Record simrel_cert :=
    { sim : simrel prog S G sc TC f;

      (* TODO: state that certG is a certification graph *)
         
      tr_step : tid_trav_step (Gtid q);
      
      q_branch : f(q) = q' \/ Scf (f q) q';
      
      q_last : f(q) <> q' -> ⦗ eq q' ⦘ ⨾ Ssb = ∅₂; 

      imgcc : ⦗ f □₁ dom_rel (Gsb^? ⨾ ⦗ eq q ⦘) ⦘ ⨾ Scc ⨾ ⦗ Stid_ qtid ⦘ ⊆ 
              ⦗ f □₁ GW ⦘ ⨾ Sew ⨾ Ssb^= ;
    }.

End SimRelCert.


Lemma simrel_cert_start prog S G sc TC TC' f (*certG*) i 
      (SR : simrel prog S G sc TC f)
      (TR_STEP : tid_trav_step G sc TC TC' i) : 
  exists q', 
    pc S TC f i q' /\
    simrel_cert prog S G sc TC TC' f q'.
Proof.
  admit.
Admitted.

Lemma simrel_cert_end prog S G sc TC TC' f (*certG*) (i:thread_id) q'
      (* TODO: state that q' is sb-max wrt G.Ei *)
      (SRcert: simrel_cert prog S G sc TC TC' f q') : 
  exists f', 
    simrel prog S G sc TC' f'.
Proof.
  admit.
Admitted.

Lemma simrel_cert_step prog S G sc TC TC' f (*certG*) (i:thread_id) q' 
      (* TODO: state that q' is not sb-max wrt G.Ei *)
      (SRcert: simrel_cert prog S G sc TC TC' f q') : 
  exists S' qnext',
    (ESstep.t Weakestmo)^? S S' /\
    simrel_cert prog S' G sc TC TC' f qnext'.
Proof.
  admit.
Admitted.
    
    