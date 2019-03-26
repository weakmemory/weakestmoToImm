Require Import Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution
     Traversal TraversalConfig SimTraversal SimTraversalProperties
     imm_common imm_s imm_s_hb SimulationRel
     CertExecution2 CertExecutionMain
     SubExecution CombRelations AuxRel.
Require Import AuxRel AuxDef EventStructure Consistency EventToAction.
(* BasicStep Step Consistency *)
(*         LblStep CertRf CertGraph EventToAction ImmProperties *)
(*         SimRelCont SimRelEventToAction *)
(*         SimRel SimRelCert SimRelCertBasicStep SimRelAddJF SimRelAddEW SimRelAddCO. *)
(* Require Import StepWf. *)

Set Implicit Arguments.
Local Open Scope program_scope.

Section AuxJF.
  Variable G : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.
  
  Variable S : ES.t.

  Variable a2e : actid -> eventid.

  Variable WF : ES.Wf S.

  Notation "'SE'" := S.(ES.acts_set) (at level 10).
  Notation "'SEinit'" := S.(ES.acts_init_set) (at level 10).
  Notation "'SEninit'" := S.(ES.acts_ninit_set) (at level 10).
  Notation "'Stid'" := (S.(ES.tid)) (at level 10).
  Notation "'Slab'" := S.(ES.lab) (at level 10).
  Notation "'Sloc'" := (loc S.(ES.lab)) (at level 10).

  Notation "'Ssb'" := S.(ES.sb) (at level 10).
  Notation "'Srmw'" := S.(ES.rmw) (at level 10).
  Notation "'Sew'" := S.(ES.ew) (at level 10).
  Notation "'Sjf'" := S.(ES.jf) (at level 10).
  Notation "'Srf'" := S.(ES.rf) (at level 10).
  Notation "'Sco'" := S.(ES.co) (at level 10).
  Notation "'Scf'" := S.(ES.cf) (at level 10).

  Notation "'Sjfe'" := S.(ES.jfe) (at level 10).
  Notation "'Srfe'" := S.(ES.rfe) (at level 10).
  Notation "'Scoe'" := S.(ES.coe) (at level 10).
  Notation "'Sjfi'" := S.(ES.jfi) (at level 10).
  Notation "'Srfi'" := S.(ES.rfi) (at level 10).
  Notation "'Scoi'" := S.(ES.coi) (at level 10).

  Notation "'Scc'" := S.(cc) (at level 10).
  Notation "'Ssw'" := S.(sw) (at level 10).
  Notation "'Shb'" := S.(hb) (at level 10).
  Notation "'Secf'" := (S.(Consistency.ecf)) (at level 10).
  Notation "'Seco'" := (Consistency.eco S Weakestmo) (at level 10).

  Notation "'SR'" := (fun a => is_true (is_r S.(ES.lab) a)) (at level 10).
  Notation "'SW'" := (fun a => is_true (is_w S.(ES.lab) a)) (at level 10).
  Notation "'SF'" := (fun a => is_true (is_f S.(ES.lab) a)) (at level 10).

  Notation "'SPln'" := (fun a => is_true (is_only_pln S.(ES.lab) a)) (at level 10).
  Notation "'SRlx'" := (fun a => is_true (is_rlx S.(ES.lab) a)) (at level 10).
  Notation "'SRel'" := (fun a => is_true (is_rel S.(ES.lab) a)) (at level 10).
  Notation "'SAcq'" := (fun a => is_true (is_acq S.(ES.lab) a)) (at level 10).
  Notation "'SAcqrel'" := (fun a => is_true (is_acqrel S.(ES.lab) a)) (at level 10).
  Notation "'SSc'" := (fun a => is_true (is_sc S.(ES.lab) a)) (at level 10).

  Notation "'K'" := (S.(ES.cont_set)) (at level 10).

  Notation "'Stid_' t" := (fun x => Stid x = t) (at level 1).

  Notation "'e2a'" := (e2a S) (at level 1).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gtid'" := (tid).
  Notation "'Grmw'" := G.(rmw).
  Notation "'Gaddr'" := G.(addr).
  Notation "'Gdata'" := G.(data).
  Notation "'Gctrl'" := G.(ctrl).
  Notation "'Grmw_dep'" := G.(rmw_dep).

  Notation "'Gtid_' t" := (fun x => tid x = t) (at level 1).
  Notation "'GNtid_' t" := (fun x => tid x <> t) (at level 1).

  Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
  Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

  Notation "'GR'" := (fun a => is_true (is_r Glab a)).
  Notation "'GW'" := (fun a => is_true (is_w Glab a)).
  Notation "'GR_ex'" := (fun a => R_ex Glab a).

  Notation "'Gsb'" := (G.(sb)).
  Notation "'Ghb'" := (G.(imm_s_hb.hb)).
  Notation "'Grf'" := (G.(rf)).
  Notation "'Grfi'" := (G.(rfi)).
  Notation "'Gco'" := (G.(co)).
  Notation "'Gvf'" := (G.(furr)).
  Notation "'Gppo'" := (G.(ppo)).
  Notation "'Geco'" := (G.(Execution_eco.eco)).

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Definition dr_ppo := dom_rel (((e2a ⋄ Gppo) ∩ Ssb) ⨾ Sew ⨾ ⦗a2e □₁ I⦘).
  Definition dr_irfi := dom_rel (⦗a2e □₁ I⦘ ⨾ Sew ⨾ ((e2a ⋄ Grfi) ∩ Ssb)).
  Definition DR := SR ∩₁ (a2e □₁ C ∪₁ SE ∩₁ SAcq ∪₁
                          dom_rel (Srmw) ∪₁
                          dr_ppo ∪₁ dr_irfi).
  
  Definition sim_vf :=
    Sew ⨾ (Sjf ⨾ ⦗DR⦘)^? ⨾ Shb^? ⨾ (e2a ⋄ sc)^? ⨾ Shb^?.
  
  Definition sim_jf := sim_vf \ Sco ⨾ sim_vf.

  Lemma dr_ppoE : dr_ppo ⊆₁ SE.
  Proof.
    unfold dr_ppo.
    rewrite ES.sbE; auto.
    basic_solver.
  Qed.

  Lemma dr_irfiE : dr_irfi ⊆₁ SE.
  Proof.
    unfold dr_irfi.
    rewrite ES.ewE; auto.
    basic_solver 10.
  Qed.

  Lemma drE (A2ED : a2e □₁ C ⊆₁ SE) : DR ⊆₁ SE.
  Proof.
    unfold DR.
    apply set_subset_inter_l.
    right.
    rewrite A2ED.
    rewrite (dom_l WF.(ES.rmwE)); auto.
    unionL.
    1-3: basic_solver.
    { eapply dr_ppoE; eauto. }
    eapply dr_irfiE; eauto.
  Qed.

End AuxJF.
