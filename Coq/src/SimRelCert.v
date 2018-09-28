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
  
  Variable f : actid -> eventid.
  Variable h : actid -> eventid.
  Variable q : actid.

  Notation "'g'" := (event_to_act S).

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

  Notation "'SR'" := (fun a => is_true (is_r Slab a)).
  Notation "'SW'" := (fun a => is_true (is_w Slab a)).
  
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

  Notation "'certGE'" := G.(acts_set).
  Notation "'certGlab'" := (G.(lab)).
  
  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).
  Notation "'C''"  := (covered TC').
  Notation "'I''"  := (issued TC').

  Record cert_graph thread :=
    { same_lab : eq_dom ((Gtid_ thread) ∩₁ (C' ∪₁ I')) Glab certGlab; }.

  Record sb_max i e :=
    { inGi  : Gtid_ i e;
      sbMAX : forall e', Gtid_ i e' -> Gsb^? e' e
    }.
    
  Definition tid_trav_step thread :=
    exists e, Gtid e = thread /\ itrav_step G sc e TC TC'.

  Notation "'hdom'" := (Gtid_ qtid ∩₁ dom_rel (Gsb^? ⨾ ⦗ I' ⦘)) (only parsing).
      
  Record simrel_cert :=
    { sim : simrel prog S G sc TC f;

      cert : cert_graph qtid; 

      tr_step : tid_trav_step qtid;

      hgtrip : ⦗ hdom ⦘ ⨾ ↑ (compose g h) ⊆ eq;

      hinj : inj_dom hdom h;  
      himg : h □₁ hdom ⊆₁ SE;
      hoth : (h □₁ set_compl hdom) ∩₁ SE ≡₁ ∅;
      hlab : eq_dom hdom certGlab (compose Slab h);
      htid : eq_dom hdom Gtid (compose Stid h); 

      hco : h □ ⦗ hdom ⦘ ⨾ Gco ⨾ ⦗ hdom ⦘ ⊆ Sco;

      cimgNcf : ⦗ h □₁ hdom ⦘ ⨾ Scf ⨾ ⦗ h □₁ hdom ⦘ ≡ ∅₂;
      
      complete_fdom :
        (h □₁ hdom) ∩₁ SR ⊆₁ codom_rel (⦗ h □₁ hdom ⦘ ⨾ Srf);

      imgcc : ⦗ f □₁ dom_rel (Gsb^? ⨾ ⦗ eq q ⦘) ⦘ ⨾ Scc ⨾ ⦗ Stid_ qtid ⦘ ⊆ 
              ⦗ h □₁ GW ⦘ ⨾ Sew ⨾ Ssb^= ;
    }.

End SimRelCert.


Lemma simrel_cert_start prog S G sc TC TC' f (*certG*) i 
      (SR : simrel prog S G sc TC f)
      (TR_STEP : tid_trav_step G sc TC TC' i) : 
  exists q q', 
    pc S TC f i q' /\
    simrel_cert prog S G sc TC TC' f f q.
Proof.
  admit.
Admitted.

Lemma simrel_cert_end prog S G sc TC TC' f h (*certG*) i q
      (sbMAX: sb_max G i q)
      (SRcert: simrel_cert prog S G sc TC TC' f h q) : 
  exists f', 
    simrel prog S G sc TC' f'.
Proof.
  admit.
Admitted.

Lemma simrel_cert_step prog S G sc TC TC' f h (*certG*) i q
      (NsbMAX : ~ sb_max G i q)
      (SRcert: simrel_cert prog S G sc TC TC' f h q) : 
  exists S' h' q',
    (ESstep.t Weakestmo)^? S S' /\
    simrel_cert prog S' G sc TC TC' f h' q'.
Proof.
  admit.
Admitted.
    
    