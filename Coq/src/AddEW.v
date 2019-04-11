From hahn Require Import Hahn.
From imm Require Import Events AuxRel. 
Require Import AuxRel.
Require Import AuxDef.
Require Import EventStructure.
Require Import Consistency.
Require Import BasicStep.

Set Implicit Arguments.

Notation "'E' S" := S.(ES.acts_set) (at level 10).
Notation "'Einit' S"  := S.(ES.acts_init_set) (at level 10).
Notation "'Eninit' S" := S.(ES.acts_ninit_set) (at level 10).

Notation "'tid' S" := S.(ES.tid) (at level 10).
Notation "'lab' S" := S.(ES.lab) (at level 10).
Notation "'mod' S" := (Events.mod S.(ES.lab)) (at level 10).
Notation "'loc' S" := (Events.loc S.(ES.lab)) (at level 10).
Notation "'val' S" := (Events.val S.(ES.lab)) (at level 10).

Notation "'sb' S" := S.(ES.sb) (at level 10).
Notation "'rmw' S" := S.(ES.rmw) (at level 10).
Notation "'ew' S" := S.(ES.ew) (at level 10).
Notation "'jf' S" := S.(ES.jf) (at level 10).
Notation "'rf' S" := S.(ES.rf) (at level 10).
Notation "'co' S" := S.(ES.co) (at level 10).
Notation "'cf' S" := S.(ES.cf) (at level 10).

Notation "'jfe' S" := S.(ES.jfe) (at level 10).
Notation "'rfe' S" := S.(ES.rfe) (at level 10).
Notation "'coe' S" := S.(ES.coe) (at level 10).
Notation "'jfi' S" := S.(ES.jfi) (at level 10).
Notation "'rfi' S" := S.(ES.rfi) (at level 10).
Notation "'coi' S" := S.(ES.coi) (at level 10).

Notation "'R' S" := (fun a => is_true (is_r S.(ES.lab) a)) (at level 10).
Notation "'W' S" := (fun a => is_true (is_w S.(ES.lab) a)) (at level 10).
Notation "'F' S" := (fun a => is_true (is_f S.(ES.lab) a)) (at level 10).

Notation "'RW' S" := (R S ∪₁ W S) (at level 10).
Notation "'FR' S" := (F S ∪₁ R S) (at level 10).
Notation "'FW' S" := (F S ∪₁ W S) (at level 10).

Notation "'Pln' S" := (fun a => is_true (is_only_pln S.(ES.lab) a)) (at level 10).
Notation "'Rlx' S" := (fun a => is_true (is_rlx S.(ES.lab) a)) (at level 10).
Notation "'Rel' S" := (fun a => is_true (is_rel S.(ES.lab) a)) (at level 10).
Notation "'Acq' S" := (fun a => is_true (is_acq S.(ES.lab) a)) (at level 10).
Notation "'Acqrel' S" := (fun a => is_true (is_acqrel S.(ES.lab) a)) (at level 10).
Notation "'Sc' S" := (fun a => is_true (is_sc S.(ES.lab) a)) (at level 10).

(* Notation "'same_mod' S" := (same_mod S.(ES.lab)) (at level 10). *)
(* Notation "'same_loc' S" := (same_loc S.(ES.lab)) (at level 10). *)
(* Notation "'same_val' S" := (same_val S.(ES.lab)) (at level 10). *)

Notation "'K' S" := (S.(ES.cont_set)) (at level 10).

Notation "'Tid' S" := (fun t e => S.(ES.tid) e = t) (at level 1).
Notation "'Mod_' S" := (fun m x => mod S x = m) (at level 1).
Notation "'Loc_' S" := (fun l x => loc S x = l) (at level 1).
Notation "'Val_' S" := (fun v e => val S e = v) (at level 1).

Definition ew_delta ws w : relation eventid := 
  eq w × eq w ∪ (ws × eq w)^⋈.

Hint Unfold ew_delta : ESStepDb.

Definition add_ew ews w' S S' : Prop :=   
  ⟪ wE' : E S' w' ⟫ /\
  ⟪ wW' : W S' w' ⟫ /\
  ⟪ ewsE : ews ⊆₁ E S ⟫ /\
  ⟪ ewsW : ews ⊆₁ W S ⟫ /\
  ⟪ ewsRLX : ews ⊆₁ Rlx S ⟫ /\
  ⟪ ewsMOD : ews ⊆₁ same_mod S' w' ⟫ /\
  ⟪ ewsLOC : ews ⊆₁ same_loc S' w' ⟫ /\
  ⟪ ewsVAL : ews ⊆₁ same_val S' w' ⟫ /\
  ⟪ ewsCF : ews ⊆₁ cf S' w' ⟫ /\
  ⟪ ewsEW : ews × ews ⊆ ew S ⟫ /\
  ⟪ ewsEWprcl : dom_rel (ew S ⨾ ⦗ews⦘) ⊆₁ ews ⟫ /\
  ⟪ EW' : ew S' ≡ ew S ∪ ew_delta ews w' ⟫. 

(******************************************************************************)
(** ** ews lemmas *)
(******************************************************************************)

Lemma add_ew_ewsEWLoc ews w' e e' S S'
      (wf : ES.Wf S) 
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S') : 
  ews ⊆₁ (E S) ∩₁ (W S) ∩₁ (Loc_ S (loc S' w')).
Proof. 
  cdes AEW.
  intros x xEWS.
  unfolder; splits; auto.
  etransitivity.
  { symmetry. eapply basic_step_loc_eq_dom; eauto. }
  symmetry. by apply ewsLOC in xEWS.
Qed.

Lemma add_ew_ews_ew_fwcl ews w' S S'
      (wf : ES.Wf S) 
      (AEW : add_ew ews w' S S') : 
  codom_rel (⦗ews⦘ ⨾ ew S) ⊆₁ ews.
Proof.
  cdes AEW. 
  intros x [y [z [[EQz EWS] EW]]]. subst z.
  apply ES.ew_sym in EW; auto.
  apply ewsEWprcl.
  basic_solver 10.
Qed.

(******************************************************************************)
(** ** ew_delta lemmas *)
(******************************************************************************)

Lemma add_ew_ew_delta_dom ews w' e e' S S'
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S') 
      (wf : ES.Wf S) 
      (wEE' : (eq e ∪₁ eq_opt e') w') : 
  dom_rel (ew_delta ews w') ⊆₁ ews ∪₁ eq w'.
Proof. unfold ew_delta. basic_solver. Qed.

Lemma add_ew_ew_delta_codom ews w' e e' S S'
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S') 
      (wf : ES.Wf S) 
      (wEE' : (eq e ∪₁ eq_opt e') w') : 
  codom_rel (ew_delta ews w') ⊆₁ ews ∪₁ eq w'.
Proof. unfold ew_delta. basic_solver. Qed.

Lemma add_ew_ew_deltaEl ews w' e e' S S'
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S') 
      (wf : ES.Wf S) 
      (wEE' : (eq e ∪₁ eq_opt e') w') : 
  ew_delta ews w' ⨾ ⦗E S⦘ ≡ eq w' × ews. 
Proof. 
  cdes AEW; cdes BSTEP; cdes BSTEP_.
  unfold ew_delta. 
  rewrite csE, transp_cross.
  relsf.
  arewrite_false (eq w' × eq w' ⨾ ⦗E S⦘).
  { unfolder in wEE'; desf; step_solver. }
  arewrite_false (ews × eq w' ⨾ ⦗E S⦘).
  { unfolder in wEE'; desf; step_solver. }
  relsf. 
  generalize ewsE. basic_solver.
Qed.

Lemma add_ew_ew_deltaEr ews w' e e' S S'
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S') 
      (wf : ES.Wf S) 
      (wEE' : (eq e ∪₁ eq_opt e') w') : 
  ⦗E S⦘ ⨾ ew_delta ews w' ≡ ews × eq w'. 
Proof. 
  cdes AEW; cdes BSTEP; cdes BSTEP_.
  unfold ew_delta. 
  rewrite csE, transp_cross.
  relsf.
  arewrite_false (⦗E S⦘ ⨾ eq w' × eq w').
  { unfolder in wEE'; desf; step_solver. }
  arewrite_false (⦗E S⦘ ⨾ eq w' × ews).
  { unfolder in wEE'; desf; step_solver. }
  relsf. 
  generalize ewsE. basic_solver.
Qed.

