Require Import Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events AuxRel. 
Require Import AuxRel AuxDef EventStructure Consistency.

Set Implicit Arguments.

Export ListNotations.

Module ESBasicStep.

Notation "'E' S" := S.(ES.acts_set) (at level 10).
Notation "'Einit' S"  := S.(ES.acts_init_set) (at level 10).
Notation "'Eninit' S" := S.(ES.acts_ninit_set) (at level 10).

Notation "'tid' S" := S.(ES.tid) (at level 10).
Notation "'lab' S" := S.(ES.lab) (at level 10).
Notation "'loc' S" := (Events.loc S.(ES.lab)) (at level 10).
Notation "'mod' S" := (Events.mod S.(ES.lab)) (at level 10).

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

(* Definition same_tid (S : t) := fun x y => S.(tid) x = S.(tid) y. *)
Notation "'same_loc' S" := (same_loc S.(ES.lab)) (at level 10).
Notation "'same_val' S" := (same_val S.(ES.lab)) (at level 10).

Notation "'K' S" := (S.(ES.cont_set)) (at level 10).

Notation "'Tid' S" := (fun t e => S.(ES.tid) e = t) (at level 9).

Definition sb_delta S k e e' : relation eventid := 
  ES.cont_sb_dom S k × eq e ∪ (ES.cont_sb_dom S k ∪₁ eq e) × eq_opt e'.

Definition rmw_delta e e' : relation eventid := 
  eq e × eq_opt e'.

Hint Unfold sb_delta rmw_delta : ESStepDb.

Definition t_
           (lang : Language.t)
           (k k' : cont_label)
           (st st' : lang.(Language.state))
           (e  : eventid)
           (e' : option eventid)
           (S S' : ES.t) : Prop :=
  ⟪ EEQ    : 1 + e = opt_ext (1 + e) e' ⟫ /\
  ⟪ EVENT  : e = S.(ES.next_act) ⟫ /\
  ⟪ EVENT' : S'.(ES.next_act) = 1 + opt_ext e e' ⟫ /\
  exists lbl lbl',
    let lbls := opt_to_list lbl' ++ [lbl] in
    let thrd := ES.cont_thread S k in
    ⟪ KCE    : k' =  CEvent (opt_ext e e')⟫ /\
    ⟪ CONT   : K S (k, existT _ lang st) ⟫ /\
    ⟪ CONT'  : S'.(ES.cont) = (k', existT _ lang st') :: S.(ES.cont) ⟫ /\
    ⟪ STEP   : lang.(Language.step) lbls st st' ⟫ /\
    ⟪ LABEL' : opt_same_ctor e' lbl' ⟫ /\
    ⟪ LAB'   : S'.(ES.lab) = upd_opt (upd S.(ES.lab) e lbl ) e' lbl' ⟫ /\
    ⟪ TID'   : S'.(ES.tid) = upd_opt (upd S.(ES.tid) e thrd) e' (Some thrd) ⟫ /\
    ⟪ SB'    : S'.(ES.sb) ≡ S.(ES.sb) ∪ sb_delta S k e e' ⟫ /\
    ⟪ RMW'   : S'.(ES.rmw) ≡ S.(ES.rmw) ∪ rmw_delta e e' ⟫.

Definition t
           (e  : eventid)
           (e' : option eventid)
           (S S' : ES.t) : Prop :=
  exists lang k k' st st', 
    ⟪ BSTEP_ : t_ lang k k' st st' e e' S S' ⟫.

(* Definition add_jf (r : eventid) (S S' : ES.t) : Prop := *)
(*   ⟪ RR : R S' r ⟫ /\ *)
(*   exists w, *)
(*     ⟪ EW  : S.(ES.acts_set) w ⟫ /\ *)
(*     ⟪ WW  : W S' w ⟫ /\ *)
(*     ⟪ LOC : same_loc S' w r ⟫ /\ *)
(*     ⟪ VAL : same_val S' w r ⟫ /\ *)
(*     ⟪ JF' : S'.(ES.jf) ≡ S.(ES.jf) ∪ singl_rel w r ⟫. *)

(* Definition add_ew (w : eventid) (S S' : ES.t) : Prop := *)
(*   ⟪ WW : W S' w ⟫ /\ *)
(*   exists (ws : eventid -> Prop), *)
(*     ⟪ WWS   : ws ⊆₁ W S ⟫ /\ *)
(*     ⟪ LOCWS : ws ⊆₁ same_loc S w ⟫ /\ *)
(*     ⟪ VALWS : ws ⊆₁ same_val S w ⟫ /\ *)
(*     ⟪ CFWS  : ws ⊆₁ S.(ES.cf) w ⟫ /\ *)
(*     ⟪ REPR : *)
(*       S'.(ES.ew) ≡ S.(ES.ew) ∪ ws × eq w ∪ eq w × ws ⟫. *)

(* Definition add_co (w : eventid) (S S' : ES.t) : Prop := *)
(*   let A := S.(ES.acts_set) ∩₁ W S ∩₁ (same_loc S w) \₁ (S.(ES.cf)^? w) in *)
(*   ⟪ WW : W S' w ⟫ /\ *)
(*   exists (ws : eventid -> Prop), *)
(*     ⟪ WWS : ws ⊆₁ A ⟫ /\ *)
(*     ⟪ REPR : *)
(*       S'.(ES.co) ≡ S.(ES.co) ∪ S.(ES.ew) ∪ ws × eq w ∪ eq w × (A \₁ ws) ⟫. *)

(* Definition t_fence  *)
(*            (e  : eventid) *)
(*            (e' : option eventid)  *)
(*            (S S' : ES.t) : Prop :=  *)
(*   ⟪ ENONE : e' = None ⟫ /\ *)
(*   ⟪ FF  : F S' e ⟫ /\ *)
(*   ⟪ JF' : S'.(ES.jf) ≡ S.(ES.jf) ⟫ /\ *)
(*   ⟪ EW' : S'.(ES.ew) ≡ S.(ES.ew) ⟫ /\ *)
(*   ⟪ CO' : S'.(ES.co) ≡ S.(ES.co) ⟫. *)

(* Definition t_load  *)
(*            (e  : eventid) *)
(*            (e' : option eventid)  *)
(*            (S S' : ES.t) : Prop :=  *)
(*   ⟪ ENONE : e' = None ⟫ /\ *)
(*   ⟪ AJF : add_jf e S S' ⟫ /\ *)
(*   ⟪ EW' : S'.(ES.ew) ≡ S.(ES.ew) ⟫ /\ *)
(*   ⟪ CO' : S'.(ES.co) ≡ S.(ES.co) ⟫. *)

(* Definition t_store  *)
(*            (e  : eventid) *)
(*            (e' : option eventid)  *)
(*            (S S' : ES.t) : Prop :=  *)
(*   ⟪ ENONE : e' = None ⟫ /\ *)
(*   ⟪ JF' : S'.(ES.jf) ≡ S.(ES.jf) ⟫ /\ *)
(*   ⟪ AEW : add_ew e S S' ⟫ /\ *)
(*   ⟪ ACO : add_co e S S' ⟫. *)

(* Definition t_update  *)
(*            (e  : eventid) *)
(*            (e' : option eventid)  *)
(*            (S S' : ES.t) : Prop := exists w, *)
(*   ⟪ ESOME : e' = Some w ⟫ /\ *)
(*   ⟪ AJF : add_jf e S S' ⟫ /\ *)
(*   ⟪ AEW : add_ew w S S' ⟫ /\ *)
(*   ⟪ ACO : add_co w S S' ⟫. *)

(* Definition t_ e e' S S' :=  *)
(*   t_fence e e' S S' \/ t_load e e' S S' \/ t_store e e' S S' \/ t_update e e' S S'. *)

(* Definition t (m : model) (S S' : ES.t) : Prop := exists e e', *)
(*   ⟪ TT  : t_ e e' S S' ⟫ /\ *)
(*   ⟪ BSTEP : t_basic e e' S S' ⟫ /\ *)
(*   ⟪ CON : @es_consistent S' m ⟫. *)

(******************************************************************************)
(** ** Some useful tactics *)
(******************************************************************************)

(* Ltac unfold_t_ H :=  *)
(*   unfold t_, t_fence, t_load, t_store, t_update in H; desf.  *)

(* tries to solve goals like `sb ⨾ ⦗eq e⦘ ⊆ ∅₂`,
   where `e` is a new event added by step `S -> S'`,
   using the fact that `sb ≡ ⦗E⦘ ⨾ sb ⨾ ⦗E⦘` *)
Ltac step_solver := 
  autounfold with ESStepDb in *; 
  unfold eq_opt, opt_ext in *; 
  rewrite 1?ES.sbE, 1?ES.rmwE, 1?ES.cfE, 
    1?ES.cont_sb_domE, 1?ES.cont_cf_domE,
    1?ES.jfE, 1?ES.jfiE, 1?ES.jfeE,
    1?ES.rfE, 1?ES.coE, 1?ES.ewE, 
    1?rsE, 1?releaseE, 1?swE, 1?hbE;
  eauto; unfolder; ins; splits; desf; omega.

(******************************************************************************)
(** ** basic_step : `E` propeties *)
(******************************************************************************)

Lemma basic_step_next_act_lt e e' S S'
      (BSTEP : t e e' S S') :
  ES.next_act S < ES.next_act S'.
Proof.
  cdes BSTEP. cdes BSTEP_.
  unfold opt_ext in *. 
  rewrite EVENT'. 
  desf; omega.
Qed.

Lemma basic_step_acts_set 
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t e e' S S') :
  E S' ≡₁ E S ∪₁ eq e ∪₁ eq_opt e'.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold eq_opt, opt_ext in *.
  unfold ES.acts_set. 
  edestruct e'; unfolder; splits; ins; omega.
Qed.

Lemma basic_step_nupd_acts_set 
      (e  : eventid)
      (S S' : ES.t) 
      (BSTEP : t e None S S') :
  E S' ≡₁ E S ∪₁ eq e.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  apply basic_step_acts_set in BSTEP.
  unfold eq_opt in BSTEP.
  by rewrite set_union_empty_r in BSTEP.
Qed.

Lemma basic_step_nupd_acts_mon e e' S S'  
      (BSTEP : t e e' S S') :
  E S ⊆₁ E S'.
Proof. 
  rewrite basic_step_acts_set with (S' := S'); eauto. 
  basic_solver. 
Qed.

Lemma basic_step_acts_set_ne e e' S S'  
      (BSTEP : t e e' S S') :
  ~ E S e.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold not, ES.acts_set; ins; omega.
Qed.

Lemma basic_step_acts_set_ne' e e' S S'  
      (BSTEP : t e (Some e') S S') :
  ~ E S e'.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold not, ES.acts_set; ins; omega. 
Qed.

Lemma basic_step_acts_set_mon e e' S S' 
      (BSTEP : t e e' S S') :
  S.(ES.acts_set) ⊆₁ S'.(ES.acts_set).
Proof. 
  unfold ES.acts_set. unfolder. intros x. 
  generalize (basic_step_next_act_lt BSTEP).
  omega.
Qed.

Lemma basic_step_acts_ninit_set_e
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t e e' S S')
      (wfE: ES.Wf S) :
  ~ Einit S' e.
Proof.
  cdes BSTEP; cdes BSTEP_.
  unfold ES.acts_init_set.
  red. unfolder. intros [_ TIDe].
  apply wfE.(ES.init_tid_K).
  do 2 eexists; splits; [by apply CONT|].
  rewrite <- TIDe. 
  rewrite TID'. 
  edestruct e'; unfold upd_opt; desf.
  2: by rewrite upds. 
  rewrite updo.
  { by rewrite upds. }
  unfold opt_ext in EEQ. omega.
Qed.

Lemma basic_step_acts_ninit_set_e' e e' S S'
      (BSTEP : t e (Some e') S S')
      (wfE: ES.Wf S) :
  ~ Einit S' e'.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold ES.acts_init_set.
  red. unfolder. intros [_ TIDe].
  apply wfE.(ES.init_tid_K).
  do 2 eexists; splits; [by apply CONT|].
  rewrite <- TIDe. 
  rewrite TID'. 
  unfold upd_opt.
  by rewrite upds.
Qed.

(******************************************************************************)
(** ** basic_step : `tidlab_eq_dom` helper lemma *)
(******************************************************************************)

Lemma basic_step_tidlab_eq_dom  e e' S S'
      (BSTEP : t e e' S S') :
  ⟪ TIDEQ : eq_dom (E S) (tid S') (tid S) ⟫ /\
  ⟪ LABEQ : eq_dom (E S) (lab S') (lab S) ⟫.
Proof.
  cdes BSTEP. cdes BSTEP_.
  rewrite TID', LAB'. unnw. unfold eq_dom.
  splits; ins; desf.
  all: unfold upd_opt.
  all: assert (x <> ES.next_act S) as HH by (red in SX; omega).
  all: unfold opt_ext in *.
  all: desf; rewrite updo; auto; [|red in SX; omega].
  all: rewrite updo; auto.
Qed.

(******************************************************************************)
(** ** basic_step : `tid` propeties *)
(******************************************************************************)

Lemma basic_step_tid_eq_dom  e e' S S'
      (BSTEP : t e e' S S') :
  eq_dom (E S) (tid S') (tid S).
Proof. eapply basic_step_tidlab_eq_dom; eauto. Qed.

Lemma basic_step_same_tid_restr e e' S S'  
      (BSTEP : t e e' S S') :
  restr_rel S.(ES.acts_set) S'.(ES.same_tid) ≡ restr_rel S.(ES.acts_set) S.(ES.same_tid).
Proof. 
  unfolder. 
  unfold ES.same_tid.
  splits; ins; desf; splits; auto.
  erewrite <- basic_step_tid_eq_dom; eauto. 
  2: erewrite basic_step_tid_eq_dom; eauto; symmetry.
  all: rewrite H; eapply basic_step_tid_eq_dom; eauto. 
Qed.

Lemma basic_step_tid_e lang k k' st st' e e' S S' 
      (BSTEP_ : t_ lang k k' st st' e e' S S') :
  tid S' e = ES.cont_thread S k. 
Proof. 
  cdes BSTEP_.
  edestruct k, e';
    rewrite TID';
    unfold upd_opt, ES.cont_thread;
    unfold opt_ext in EEQ.
  1,3: rewrite updo; [by rewrite upds | omega].
  all: by rewrite upds.
Qed.

Lemma basic_step_tid_e' lang k k' st st' e e' S S'
      (BSTEP_ : t_ lang k k' st st' e (Some e') S S') :
  tid S' e' = ES.cont_thread S k. 
Proof. 
  cdes BSTEP_.
  edestruct k;
    rewrite TID';
    unfold upd_opt, ES.cont_thread;
    by rewrite upds.
Qed.

(******************************************************************************)
(** ** basic_step : `Einit/Eninit` propeties *)
(******************************************************************************)

Lemma basic_step_acts_init_set e e' S S' 
      (BSTEP : t e e' S S')
      (wfE: ES.Wf S) :
  Einit S' ≡₁ Einit S.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold ES.acts_init_set.
  rewrite basic_step_acts_set; eauto. 
  rewrite !set_inter_union_l.  
  arewrite (eq e ∩₁ (fun x : nat => (tid S') x = tid_init) ≡₁ ∅). 
  { apply set_disjointE; unfold set_disjoint; ins.
    eapply basic_step_acts_ninit_set_e; eauto.
    unfold ES.acts_init_set.  
    unfolder; splits; desf.
    destruct e'; rewrite EVENT'; unfold opt_ext in *; omega. }
  arewrite (eq_opt e' ∩₁ (fun x : nat => (tid S') x = tid_init) ≡₁ ∅). 
  { edestruct e'. 
    { apply set_disjointE; unfold set_disjoint; ins.
      eapply basic_step_acts_ninit_set_e'; eauto.
      unfold ES.acts_init_set.  
      unfolder; splits; desf; omega. }
    unfold eq_opt. apply set_inter_empty_l. }
  relsf.
  unfolder. unfold set_subset. splits; ins; splits; desf. 
  { erewrite <- basic_step_tid_eq_dom; eauto. }
  erewrite basic_step_tid_eq_dom; eauto.
Qed.

Lemma basic_step_acts_ninit_set e e' S S' 
      (BSTEP : t e e' S S')
      (wfE: ES.Wf S) :
  Eninit S' ≡₁ Eninit S ∪₁ eq e ∪₁ eq_opt e'.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold ES.acts_ninit_set.
  rewrite basic_step_acts_set, basic_step_acts_init_set; eauto.
  rewrite !set_minus_union_l.
  repeat apply set_union_Propere; auto. 
  { unfolder. unfold set_subset. splits; ins; splits; desf. 
    red. ins; desf; omega. }
  edestruct e'. 
  { unfolder. unfold set_subset. splits; ins; splits; desf. 
    red. ins; desf; omega. }
  unfold eq_opt; basic_solver. 
Qed.


(******************************************************************************)
(** ** basic_step : `lab` propeties *)
(******************************************************************************)

Lemma basic_step_lab_eq_dom  e e' S S'
      (BSTEP : t e e' S S') :
  eq_dom (E S) (lab S') (lab S).
Proof. eapply basic_step_tidlab_eq_dom; eauto. Qed.

Lemma basic_step_loc_eq_dom  e e' S S'
      (BSTEP : t e e' S S') :
  eq_dom (E S) (loc S') (loc S).
Proof.
  unfold Events.loc. red. ins.
  assert ((lab S') x = (lab S) x) as AA.
  2: by rewrite AA.
  eapply basic_step_lab_eq_dom; eauto.
Qed.

Lemma basic_step_same_loc_restr e e' S S' 
      (BSTEP : t e e' S S') :
  restr_rel S.(ES.acts_set) (same_loc S') ≡ restr_rel S.(ES.acts_set) (same_loc S).
Proof. 
  unfolder. 
  unfold ES.same_tid.
  splits; ins; desf; splits; auto; red.
  erewrite <- basic_step_loc_eq_dom; eauto.
  2: erewrite basic_step_loc_eq_dom; eauto; symmetry.
  all: rewrite H; eapply basic_step_loc_eq_dom; eauto. 
Qed.

Lemma basic_step_mod_eq_dom e e' S S' 
      (BSTEP : t e e' S S') :
  eq_dom S.(ES.acts_set) (mod S') (mod S).
Proof. 
  unfold eq_dom, Events.mod, ES.acts_set.
  ins; erewrite basic_step_lab_eq_dom; eauto. 
Qed.

(******************************************************************************)
(** ** basic_step : `sb` propeties *)
(******************************************************************************)

Lemma basic_step_nupd_sb lang k k' st st' e S S' 
      (BSTEP_ : t_ lang k k' st st' e None S S') :
  sb S' ≡ sb S ∪ ES.cont_sb_dom S k × eq e.  
Proof.                                       
  cdes BSTEP_.
  autounfold with ESStepDb in *.  
  rewrite cross_false_r in SB'. 
  rewrite union_false_r in SB'.
  apply SB'.
Qed.

Lemma basic_step_sb_delta_dom lang k k' st st' e e' S S'
      (BSTEP_ : t_ lang k k' st st' e e' S S') 
      (WF: ES.Wf S) :
  dom_rel (sb_delta S k e e') ⊆₁ E S ∪₁ eq e.
Proof. cdes BSTEP_. step_solver. Qed.

Lemma basic_step_sb_deltaE lang k k' st st' e e' S S'
      (BSTEP_ : t_ lang k k' st st' e e' S S') 
      (WF: ES.Wf S) :
  sb_delta S k e e' ⨾ ⦗E S⦘ ≡ ∅₂.
Proof. 
  cdes BSTEP_.
  split; [|done]. step_solver.
Qed.

Lemma basic_step_sbE e e' S S' 
      (BSTEP : t e e' S S') 
      (WF: ES.Wf S) :
  sb S' ⨾ ⦗E S⦘ ≡ sb S. 
Proof. 
  cdes BSTEP. cdes BSTEP_.
  rewrite SB'.
  rewrite !seq_union_l.
  rewrite basic_step_sb_deltaE; eauto.
  rewrite ES.sbE; auto. 
  basic_solver 10.
Qed.

Lemma basic_step_sb_mon e e' S S' 
      (BSTEP : t e e' S S') :
  sb S ⊆ sb S'.
Proof.
  cdes BSTEP; cdes BSTEP_.
  rewrite SB'; basic_solver. 
Qed.

Lemma basic_step_imm_sb_e a lang k k' st st' e e' S S'
      (WF : ES.Wf S)
      (kEVENT : k = CEvent a)
      (BSTEP_ : t_ lang k k' st st' e e' S S') :
  immediate (sb S') a e.
Proof. 
  cdes BSTEP_.
  assert (t e e' S S') as BSTEP. 
  { econstructor; eauto. }
  eapply immediate_more.
  { apply SB'. }
  autounfold with ESStepDb in *.  
  split. 
  { unfold ES.cont_sb_dom. basic_solver 10. }
  ins. unfold union in R2. desf.
  3 : unfolder in R2; step_solver. 
  { apply ES.sbE in R2; auto. 
    unfolder in R2. step_solver. }
  unfold cross_rel in R2. desc.
  assert (E S c) as Ec.
  { eapply ES.cont_sb_domE; eauto. }
  unfold ES.cont_sb_dom in *. 
  unfold union in R1. desf.
  { unfolder in R2. desf.
    { eapply ES.sb_irr; eauto. }
    eapply ES.sb_irr, ES.sb_trans; eauto. }
  { unfolder in R1. desc. subst.
    eapply basic_step_acts_set_ne; eauto. }
  unfolder in R1. desc. subst. 
  destruct e'; auto; subst.
  eapply basic_step_acts_set_ne'; eauto. 
Qed.

Lemma basic_step_imm_sb_e' lang k k' st st' e e' S S'
      (WF : ES.Wf S)
      (BSTEP_ : t_ lang k k' st st' e (Some e') S S') :
  immediate (sb S') e e'.
Proof. 
  cdes BSTEP_.
  assert (t e (Some e') S S') as BSTEP. 
  { econstructor; eauto. }
  eapply immediate_more.
  { apply SB'. }
  autounfold with ESStepDb in *.  
  split. 
  { unfold ES.cont_sb_dom. basic_solver 10. }
  ins. unfold union in R2. desf.
  { apply ES.sbE in R2; auto. 
    unfolder in R2. omega. } 
  { unfolder in R2. omega. }
  unfold eq_opt, opt_ext in *.
  unfold union in R1. desf.
  { apply ES.sbE in R1; auto. 
    unfolder in R1. omega. }
  { destruct R1 as [KSB _].
    eapply ES.cont_sb_domE in KSB; eauto. 
    unfolder in KSB. omega. } 
  unfold set_union, cross_rel in R1. desf.
  { eapply ES.cont_sb_domE in R1; eauto. 
    unfolder in R1. omega. }  
  unfold set_union, cross_rel in R2. desf.
  { eapply ES.cont_sb_domE in R2; eauto. 
    unfolder in R2. omega. }   
  omega.
Qed.

(******************************************************************************)
(** ** basic_step : `cf` propeties *)
(******************************************************************************)

Lemma basic_step_cf lang k k' st st' e e' S S' 
      (BSTEP_ : t_ lang k k' st st' e e' S S') 
      (wfE: ES.Wf S) :
  cf S' ≡ cf S ∪ (ES.cont_cf_dom S k × eq e)^⋈ ∪ (ES.cont_cf_dom S k × eq_opt e')^⋈.
Proof.
  assert (t e e' S S') as BSTEP.
  { unfold t. do 5 eexists. eauto. }
  cdes BSTEP_.
  autounfold with ESStepDb in *.  
  unfold "cf" at 1.
  rewrite <- restr_relE.
  rewrite basic_step_acts_ninit_set; eauto.
  rewrite !restr_set_union.
  rewrite id_union. 
  rewrite !seq_union_r.
  rewrite !seq_union_l.

  arewrite 
    (restr_rel (eq e) (ES.same_tid S' \ (sb S')⁼) ≡ ∅₂)
    by apply restr_irrefl_eq; basic_solver.
  arewrite 
    (restr_rel (eq_opt e') (ES.same_tid S' \ (sb S')⁼) ≡ ∅₂)
    by unfold eq_opt; desf; [apply restr_irrefl_eq|]; basic_solver.
  arewrite 
    (⦗eq e⦘ ⨾ (ES.same_tid S' \ (sb S')⁼) ⨾ ⦗eq_opt e'⦘ ≡ ∅₂)
    by rewrite SB'; basic_solver 42.
  arewrite 
    (⦗eq_opt e'⦘ ⨾ (ES.same_tid S' \ (sb S')⁼) ⨾ ⦗eq e⦘ ≡ ∅₂)
    by rewrite SB'; basic_solver 42.
  relsf.

  rewrite !unionA.
  apply union_more.

  { unfold ES.cf. 
    rewrite <- restr_relE. 
    rewrite !minus_inter_compl.
    rewrite !restr_inter.
    apply inter_rel_more.
    { eapply restr_set_subset.
      { eapply ES.acts_ninit_set_incl. } 
      erewrite <- basic_step_same_tid_restr; eauto. }
    rewrite SB'.
    rewrite cross_union_r.
    rewrite <- !unionA.
    rewrite !crs_union.
    rewrite !compl_union.
    rewrite !restr_inter.
    rewrite !restr_cross.
    rewrite <- !minus_inter_compl.
    arewrite (Eninit S × Eninit S \ (ES.cont_sb_dom S k × eq e)⁼ ≡ Eninit S × Eninit S \ ⦗⊤₁⦘).
    { unfold ES.acts_ninit_set, ES.acts_init_set.
      unfolder; unfold not.
      splits; ins; splits; desf; ins; splits; desf; auto; omega. }
    arewrite (Eninit S × Eninit S \ (ES.cont_sb_dom S k × eq_opt e')⁼ ≡ Eninit S × Eninit S \ ⦗⊤₁⦘).
    { unfold ES.acts_ninit_set, ES.acts_init_set.
      unfolder; unfold not.
      splits; ins; splits; desf; ins; splits; desf; auto; omega. }
    arewrite (Eninit S × Eninit S \ (eq e × eq_opt e')⁼ ≡ Eninit S × Eninit S \ ⦗⊤₁⦘).
    { unfold ES.acts_ninit_set, ES.acts_init_set.
      unfolder; unfold not.
      splits; ins; splits; desf; ins; splits; desf; auto; omega. } 
    rewrite !crsE.
    basic_solver 42. }

  rewrite <- unionA.

  arewrite 
    (⦗eq e⦘ ⨾ (ES.same_tid S' \ (sb S')⁼) ⨾ ⦗Eninit S⦘ ≡ 
            (⦗Eninit S⦘ ⨾ (ES.same_tid S' \ (sb S')⁼) ⨾ ⦗eq e⦘)⁻¹)
    by 
      rewrite seq_transp_sym; auto; 
      apply minus_sym; [ apply ES.same_tid_sym | apply crs_sym ].

  arewrite 
    (⦗eq_opt e'⦘ ⨾ (ES.same_tid S' \ (sb S')⁼) ⨾ ⦗Eninit S⦘ ≡ 
                 (⦗Eninit S⦘ ⨾ (ES.same_tid S' \ (sb S')⁼) ⨾ ⦗eq_opt e'⦘)⁻¹)
    by 
      rewrite seq_transp_sym; auto; 
      apply minus_sym; [ apply ES.same_tid_sym | apply crs_sym ].

    rewrite <- !csE.
    rewrite SB'. 
    rewrite cross_union_r.
    rewrite <- !unionA.
    rewrite !crs_union.
    rewrite !crs_cs.
    rewrite <- !unionA.
    arewrite 
      (⦗⊤₁⦘ ∪ (sb S) ^⋈ ∪ ⦗⊤₁⦘ ∪ (ES.cont_sb_dom S k × eq e) ^⋈ ∪ ⦗⊤₁⦘
       ∪ (ES.cont_sb_dom S k × eq_opt e') ^⋈ ∪ ⦗⊤₁⦘ ∪ (eq e × eq_opt e') ^⋈ ≡
      ⦗⊤₁⦘ ∪ (sb S) ^⋈ ∪ (ES.cont_sb_dom S k × eq e) ^⋈ 
       ∪ (ES.cont_sb_dom S k × eq_opt e') ^⋈ ∪ (eq e × eq_opt e') ^⋈)
      by basic_solver 42.
    apply union_more; apply clos_sym_more.

    { etransitivity.

      { rewrite !minus_union_r.
        rewrite !seq_eqv_inter_lr.

        arewrite 
          (⦗Eninit S⦘ ⨾ (ES.same_tid S' \ ⦗⊤₁⦘) ⨾ ⦗eq e⦘ ≡ 
           ⦗Eninit S⦘ ⨾ (ES.same_tid S') ⨾ ⦗eq e⦘).
        { unfold ES.acts_ninit_set.
          unfolder.
          splits; ins; splits; desf.
          intros [HH _].
          omega. }

        arewrite 
          (⦗Eninit S⦘ ⨾ (ES.same_tid S' \ (sb S)^⋈) ⨾ ⦗eq e⦘ ≡ 
           ⦗Eninit S⦘ ⨾ (ES.same_tid S') ⨾ ⦗eq e⦘).
        { erewrite minus_eqv_absorb_rr; auto.
          split; [|done]. step_solver. }

        arewrite 
          (⦗Eninit S⦘ ⨾ (ES.same_tid S' \ (ES.cont_sb_dom S k × eq_opt e') ^⋈) ⨾ ⦗eq e⦘ ≡
           ⦗Eninit S⦘ ⨾ (ES.same_tid S') ⨾ ⦗eq e⦘).           
        { erewrite minus_eqv_absorb_rr; auto.
          rewrite csE, transp_cross, seq_union_l.
          arewrite (ES.cont_sb_dom S k × eq_opt e' ⨾ ⦗eq e⦘ ≡ ∅₂).
          { split; try done; step_solver. }
          rewrite union_false_l.
          split; [|done]. step_solver. }

        arewrite 
          (⦗Eninit S⦘ ⨾ (ES.same_tid S' \ (eq e × eq_opt e')^⋈) ⨾ ⦗eq e⦘ ≡
           ⦗Eninit S⦘ ⨾ (ES.same_tid S') ⨾ ⦗eq e⦘).           
        { rewrite csE, transp_cross, minus_union_r, seq_eqv_inter_lr. 
          arewrite 
            (⦗Eninit S⦘ ⨾ (ES.same_tid S' \ eq e × eq_opt e') ⨾ ⦗eq e⦘ ≡ 
             ⦗Eninit S⦘ ⨾ (ES.same_tid S') ⨾ ⦗eq e⦘).
          { erewrite minus_eqv_absorb_rr; auto.
            split; try done; step_solver. }
          arewrite 
            (⦗Eninit S⦘ ⨾ (ES.same_tid S' \ eq_opt e' × eq e) ⨾ ⦗eq e⦘ ≡ 
             ⦗Eninit S⦘ ⨾ (ES.same_tid S') ⨾ ⦗eq e⦘).
          { rewrite <- seqA.
            erewrite minus_eqv_absorb_rl; [by rewrite seqA|]. 
            unfold ES.acts_ninit_set.
            split; try done; step_solver. }
          basic_solver. }

        rewrite interK, interA, interK, interC, <- interA, interK.
        erewrite inter_absorb_l; eauto. 
        rewrite <- AuxRel.seq_eqv_minus_lr, <- AuxRel.seq_eqv_minus_ll.
        basic_solver. }

      rewrite <- seq_eqv_minus_lr.
      rewrite csE, minus_union_r, transp_cross. 
      arewrite 
        (ES.same_tid S' ⨾ ⦗eq e⦘ \ eq e × ES.cont_sb_dom S k ≡ ES.same_tid S' ⨾ ⦗eq e⦘). 
      { red; split; [basic_solver|].
        unfolder; ins; desf; splits; auto.  
        red. intros [_ HH].
        eapply ES.cont_sb_domE in HH; eauto. 
        unfold ES.acts_set in HH; omega. }
      erewrite inter_absorb_r with (r' := ES.same_tid S' ⨾ ⦗eq e⦘); [|basic_solver]. 
      rewrite <- seq_eqv_minus_ll.
      arewrite 
        (⦗Eninit S⦘ ⨾ ES.same_tid S' ⨾ ⦗eq e⦘ ≡ (E S ∩₁ Tid S (ES.cont_thread S k)) × eq e).
      { unfolder; splits. 
        { intros x y [ENIx [STIDxy EQe]].
          assert (E S x) as Ex by apply ENIx.
          splits; auto. 
          erewrite <- basic_step_tid_eq_dom; eauto.
          unfold ES.same_tid in STIDxy.
          rewrite STIDxy, <- EQe.
          erewrite basic_step_tid_e; desf; eauto; by unfold ES.cont_thread. }
        intros x y [[Ex TIDx] EQe].
        assert (Eninit S x) as ENIx.
        { unfold ES.acts_ninit_set, ES.acts_init_set.
          unfold set_inter, set_minus.
          split; auto. 
          red; ins; desf. 
          eapply ES.init_tid_K; eauto. 
          do 2 eexists. 
          splits; eauto. 
          congruence. }
        splits; auto. 
        unfold ES.same_tid.
        erewrite basic_step_tid_eq_dom; eauto.
        rewrite TIDx, <- EQe.
        symmetry. 
        eapply basic_step_tid_e; eauto. }
      rewrite ES.cont_cf_cont_sb; eauto. 
      unfolder; splits; ins; splits; desf; auto.   
      red; ins; desf. } 

    destruct e'; [|unfold eq_opt; basic_solver].
    rename e0 into e'.
    rewrite eq_opt_someE.
    
    etransitivity.

      { rewrite !minus_union_r.
        rewrite !seq_eqv_inter_lr.

        arewrite 
          (⦗Eninit S⦘ ⨾ (ES.same_tid S' \ ⦗⊤₁⦘) ⨾ ⦗eq e'⦘ ≡ 
           ⦗Eninit S⦘ ⨾ (ES.same_tid S') ⨾ ⦗eq e'⦘).
        { unfold ES.acts_ninit_set.
          unfolder.
          splits; ins; splits; desf.
          intros [HH _]. omega. }

        arewrite 
          (⦗Eninit S⦘ ⨾ (ES.same_tid S' \ (sb S)^⋈) ⨾ ⦗eq e'⦘ ≡ 
           ⦗Eninit S⦘ ⨾ (ES.same_tid S') ⨾ ⦗eq e'⦘).
        { erewrite minus_eqv_absorb_rr; auto.
          split; [|done]. step_solver. }

        arewrite 
          (⦗Eninit S⦘ ⨾ (ES.same_tid S' \ (ES.cont_sb_dom S k × eq e) ^⋈) ⨾ ⦗eq e'⦘ ≡
           ⦗Eninit S⦘ ⨾ (ES.same_tid S') ⨾ ⦗eq e'⦘).           
        { erewrite minus_eqv_absorb_rr; auto.
          rewrite csE, transp_cross, seq_union_l.
          arewrite (ES.cont_sb_dom S k × eq e ⨾ ⦗eq e'⦘ ≡ ∅₂).
          { edestruct e'; unfold eq_opt; split; try done; step_solver. }
          rewrite union_false_l. 
          split; [|done]. step_solver. }

        arewrite 
          (⦗Eninit S⦘ ⨾ (ES.same_tid S' \ (eq e × eq e')^⋈) ⨾ ⦗eq e'⦘ ≡
           ⦗Eninit S⦘ ⨾ (ES.same_tid S') ⨾ ⦗eq e'⦘).           
        { rewrite csE, transp_cross, minus_union_r, seq_eqv_inter_lr. 
          arewrite 
            (⦗Eninit S⦘ ⨾ (ES.same_tid S' \ eq e' × eq e) ⨾ ⦗eq e'⦘ ≡ 
             ⦗Eninit S⦘ ⨾ (ES.same_tid S') ⨾ ⦗eq e'⦘).
          { erewrite minus_eqv_absorb_rr; auto.
            edestruct e'; unfold eq_opt; split; try done; step_solver. }
          arewrite 
            (⦗Eninit S⦘ ⨾ (ES.same_tid S' \ eq e × eq e') ⨾ ⦗eq e'⦘ ≡ 
             ⦗Eninit S⦘ ⨾ (ES.same_tid S') ⨾ ⦗eq e'⦘).
          { rewrite <- seqA.
            erewrite minus_eqv_absorb_rl; [by rewrite seqA|]. 
            unfold ES.acts_ninit_set.
            edestruct e'; unfold eq_opt; split; try done; step_solver. }
          basic_solver. }

        rewrite interK, interK, interC, <- interA, interK. 
        erewrite inter_absorb_l; eauto. 
        rewrite <- AuxRel.seq_eqv_minus_lr, <- AuxRel.seq_eqv_minus_ll.
        basic_solver. }

      rewrite <- seq_eqv_minus_lr.
      rewrite csE, minus_union_r, transp_cross. 
      arewrite 
        (ES.same_tid S' ⨾ ⦗eq e'⦘ \ eq e' × ES.cont_sb_dom S k ≡ ES.same_tid S' ⨾ ⦗eq e'⦘). 
      { red; split; [basic_solver|].
        unfolder; ins; desf; splits; auto.  
        red. intros [_ HH].
        eapply ES.cont_sb_domE in HH; eauto. 
        unfold ES.acts_set in HH; omega. }
      erewrite inter_absorb_r with (r' := ES.same_tid S' ⨾ ⦗eq e'⦘); [|basic_solver]. 
      rewrite <- seq_eqv_minus_ll.
      arewrite 
        (⦗Eninit S⦘ ⨾ ES.same_tid S' ⨾ ⦗eq e'⦘ ≡ (E S ∩₁ Tid S (ES.cont_thread S k)) × eq e').
      { unfolder; splits. 
        { intros x y [ENIx [STIDxy EQe]].
          assert (E S x) as Ex by apply ENIx.
          splits; auto. 
          erewrite <- basic_step_tid_eq_dom; eauto.
          unfold ES.same_tid in STIDxy.
          rewrite STIDxy, <- EQe.
          erewrite basic_step_tid_e'; desf; eauto; by unfold ES.cont_thread. }
        intros x y [[Ex TIDx] EQe].
        assert (Eninit S x) as ENIx.
        { unfold ES.acts_ninit_set, ES.acts_init_set.
          unfold set_inter, set_minus.
          split; auto. 
          red; ins; desf. 
          eapply ES.init_tid_K; eauto. 
          do 2 eexists. 
          splits; eauto. 
          congruence. }
        splits; auto. 
        unfold ES.same_tid.
        erewrite basic_step_tid_eq_dom; eauto.
        rewrite TIDx, <- EQe.
        symmetry. 
        eapply basic_step_tid_e'; eauto. }
      rewrite ES.cont_cf_cont_sb; eauto. 
      unfolder; splits; ins; splits; desf; auto.   
      red; ins; desf.  
Qed.

Lemma basic_step_nupd_cf lang k k' st st' e S S' 
      (BSTEP_ : t_ lang k k' st st' e None S S') 
      (wfE: ES.Wf S) :
  cf S' ≡ cf S ∪ (ES.cont_cf_dom S k × eq e)^⋈.
Proof. 
  erewrite basic_step_cf; eauto. 
  unfold eq_opt.
  basic_solver 42.
Qed.

Lemma basic_step_cf_restr e e' S S'
      (BSTEP : t e e' S S') 
      (wfE: ES.Wf S) : 
  restr_rel (E S) (cf S') ≡ cf S.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  erewrite basic_step_cf; eauto. 
  rewrite !restr_union.
  rewrite !restr_relE.
  arewrite (⦗E S⦘ ⨾ (ES.cont_cf_dom S k × eq e) ^⋈ ⨾ ⦗E S⦘ ≡ ∅₂)
    by (split; [|done]; step_solver).
  arewrite (⦗E S⦘ ⨾ (ES.cont_cf_dom S k × eq_opt e') ^⋈ ⨾ ⦗E S⦘ ≡ ∅₂)
    by destruct e'; [ split; [|done]; step_solver | basic_solver ].
  rewrite ES.cfE at 2; auto.
  by rewrite !union_false_r.
Qed.

Lemma basic_step_cf_mon e e' S S' 
      (BSTEP : t e e' S S') 
      (wfE: ES.Wf S) :
  cf S ⊆ cf S'.
Proof.
  cdes BSTEP; cdes BSTEP_.
  erewrite basic_step_cf with (S':=S'); eauto.  
  rewrite unionA.
  apply inclusion_union_r1.
Qed.  

Lemma basic_step_cf_free lang k k' st st' e e' S S' X 
      (BSTEP_ : t_ lang k k' st st' e e' S S') 
      (wfE: ES.Wf S)
      (XinE : X ⊆₁ E S)
      (CFF : ES.cf_free S X) 
      (nCFkX : X ∩₁ ES.cont_cf_dom S k ≡₁ ∅) :
  ES.cf_free S' (X ∪₁ eq e ∪₁ eq_opt e').  
Proof. 
  cdes BSTEP_.
  unfold ES.cf_free. 
  erewrite basic_step_cf; eauto. 
  rewrite !id_union, !csE.  
  relsf. unionL; auto.  

  Ltac helper := 
    unfold eq_opt, opt_ext in *;
    unfolder; splits; ins; desf; omega.

  all : try by helper.
  all : try by (rewrite ES.cfE; helper).
  all : try by (rewrite XinE; helper).
  all : try by (rewrite ES.cont_cf_domE; eauto; helper).

  1-2 : rewrite <- seqA, seq_eqv_cross_l, set_interK.
  3-4 : rewrite seq_eqv_cross_r, set_interK.

  all : unfolder; ins; desf.
  all : eapply nCFkX; unfolder; splits; eauto. 
Qed.

(******************************************************************************)
(** ** basic_step : `rmw` propeties *)
(******************************************************************************)

Lemma basic_step_nupd_rmw e S S' 
      (BSTEP : t e None S S') :
  rmw S' ≡ rmw S.  
Proof.                                       
  cdes BSTEP; cdes BSTEP_.
  unfold rmw_delta in *.
  unfold eq_opt in RMW'.
  rewrite cross_false_r in RMW'. 
  rewrite union_false_r in RMW'.
  apply RMW'.
Qed.

(******************************************************************************)
(** ** basic_step : continuation propeties *)
(******************************************************************************)

Lemma basic_step_cont_thread lang k st e e' S S' 
      (BSTEP_ : t e e' S S') 
      (WF : ES.Wf S)
      (KK : K S (k, existT _ lang st)) :
  ES.cont_thread S' k = ES.cont_thread S k. 
Proof. 
  unfold ES.cont_thread.
  destruct k; auto. 
  eapply basic_step_tid_eq_dom; eauto.
  eapply ES.K_inEninit; eauto.
Qed.

Lemma basic_step_cont_thread_k lang k k' st st' e e' S S'
      (BSTEP_ : t_ lang k k' st st' e e' S S') :
  ES.cont_thread S' k' = ES.cont_thread S k. 
Proof. 
  cdes BSTEP_. 
  subst k'. 
  unfold opt_ext in *.
  destruct e'. 
  { unfold ES.cont_thread at 1.
    erewrite basic_step_tid_e'; eauto. } 
  unfold ES.cont_thread at 1.
  erewrite basic_step_tid_e; eauto.
Qed.

Lemma basic_step_cont_set lang k k' st st' e e' S S' 
      (BSTEP_ : t_ lang k k' st st' e e' S S') :
  K S' ≡₁ K S ∪₁ eq (CEvent (opt_ext e e'), existT _ lang st').
Proof. 
  cdes BSTEP_.
  unfold ES.cont_set, set_union.
  rewrite CONT'. 
  split; intros kk KK;
    [apply in_cons_iff in KK|apply in_cons_iff];
    basic_solver.
Qed.  

Lemma basic_step_nupd_cont_set lang k k' st st' e S S' 
      (BSTEP_ : t_ lang k k' st st' e None S S') :
  K S' ≡₁ K S ∪₁ eq (CEvent e, existT _ lang st').
Proof. 
  cdes BSTEP_.
  erewrite basic_step_cont_set; eauto. 
  by unfold opt_ext.
Qed.  

(******************************************************************************)
(** ** `type_step_eq_dom` lemma *)
(******************************************************************************)

Lemma type_step_eq_dom  e e' S S'
      (BSTEP : t e e' S S') :
  ⟪ REQ : E S ∩₁ R S' ≡₁ E S ∩₁ R S ⟫ /\
  ⟪ WEQ : E S ∩₁ W S' ≡₁ E S ∩₁ W S ⟫ /\
  ⟪ FEQ : E S ∩₁ F S' ≡₁ E S ∩₁ F S ⟫.
Proof.
  cdes BSTEP. cdes BSTEP_.
  unfold is_r, is_w, is_f.
  generalize (basic_step_lab_eq_dom BSTEP). unfold eq_dom.
  intros HH.
  splits; split; unfolder; ins; desf.
  all: try by (rewrite HH in Heq0; [|by red]; destruct ((lab S) x); desf).
  all: try by (rewrite <- HH in Heq0; [|by red]; destruct ((lab S') x); desf).
Qed.

(******************************************************************************)
(** ** Well-formedness *)
(******************************************************************************)

(* Lemma step_wf e e' S S' *)
(*       (BSTEP : t e e' S S') *)
(*       (ISTEP: t_ e e' S S')  *)
(*       (wfE: ES.Wf S) : *)
(*   ES.Wf S'. *)
(* Proof. Admitted. *)

Lemma basic_step_sb_irr e e' S S'
      (BSTEP : t e e' S S')
      (WF : ES.Wf S) :
  irreflexive (sb S'). 
Proof. admit. Admitted.

Lemma basic_step_sb_trans e e' S S'
      (BSTEP : t e e' S S')
      (WF : ES.Wf S) :
  transitive (sb S'). 
Proof. admit. Admitted.

Lemma basic_step_sb_prcl e e' S S'
      (BSTEP : t e e' S S')
      (WF : ES.Wf S) : 
  prefix_clos (sb S' ∩ ES.same_tid S').
Proof. admit. Admitted.

(******************************************************************************)
(** ** seqn properties *)
(******************************************************************************)

Lemma basic_step_seqn_eq_dom e e' S S'
      (BSTEP : t e e' S S') 
      (WF : ES.Wf S) :
  eq_dom (E S) (ES.seqn S') (ES.seqn S). 
Proof. 
  cdes BSTEP; cdes BSTEP_.
  red. intros x. ins.
  unfold ES.seqn.
  rewrite <- lib.AuxRel.seq_eqv_inter_lr.
  arewrite (sb S' ⨾ ⦗eq x⦘ ≡ sb S ⨾ ⦗eq x⦘). 
  { red. split. 
    { rewrite <- seq_eqvK, <- seqA. 
      arewrite (eq x ⊆₁ E S).
      { basic_solver. }
      rewrite <- seqA, basic_step_sbE; eauto.
      basic_solver. }
    rewrite SB'. basic_solver. }
  rewrite lib.AuxRel.seq_eqv_inter_lr.
  rewrite ES.sbE at 1; auto.
  rewrite <- restr_relE, <- restr_inter_absorb_r. 
  rewrite basic_step_same_tid_restr; eauto.
  rewrite restr_inter_absorb_r, restr_relE. 
  rewrite <- ES.sbE; auto.
  erewrite countNatP_lt_eq. done.
  { eapply basic_step_next_act_lt; eauto. }
  intros y [z HH]. 
  apply seq_eqv_r in HH. 
  destruct HH as [[SB _] _].
  apply ES.sbE in SB; auto.
  apply seq_eqv_lr in SB. by desc.
Qed.  

Lemma basic_step_seqn_kinit thread lang k k' st st' e e' S S' 
      (kINIT : k = CInit thread)
      (BSTEP_ : t_ lang k k' st st' e e' S S') 
      (WF : ES.Wf S) :
  ES.seqn S' e = 0. 
Proof.   
  cdes BSTEP_.
  assert (t e e' S S') as BSTEP. 
  { econstructor; eauto. }
  autounfold with ESStepDb in *.  
  unfold ES.seqn.
  arewrite (sb S' ∩ ES.same_tid S' ⨾ ⦗eq e⦘ ≡ ∅₂); 
    [|by rewrite dom_empty; apply countNatP_empty].
  split; [|done]. 
  rewrite <- lib.AuxRel.seq_eqv_inter_lr.
  arewrite (sb S' ⨾ ⦗eq e⦘ ≡ ES.cont_sb_dom S k × eq e). 
  { rewrite SB'. 
    rewrite !seq_union_l.
    arewrite_false (sb S ⨾ ⦗eq e⦘).
    { step_solver. }
    arewrite_false ((ES.cont_sb_dom S k ∪₁ eq e) × eq_opt e' ⨾ ⦗eq e⦘).
    { step_solver. }
    basic_solver 10. }
  unfold ES.cont_sb_dom. subst. 
  unfold ES.same_tid.
  unfolder; ins; desc; subst.
  eapply ES.init_tid_K; eauto.
  do 2 eexists; splits; eauto.
  erewrite <- basic_step_tid_e; [|eauto].
  assert (tid S' x = tid S x) as Hx. 
  { eapply basic_step_tid_eq_dom; eauto. }
  congruence. 
Qed.

Lemma basic_step_seqn_kevent x lang k k' st st' e e' S S' 
      (kEVENT : k = CEvent x)
      (BSTEP_ : t_ lang k k' st st' e e' S S') 
      (WF : ES.Wf S) :
  ES.seqn S' e = 1 + ES.seqn S x. 
Proof.
  cdes BSTEP_.
  assert (t e e' S S') as BSTEP. 
  { econstructor; eauto. }
  assert (E S x) as Ex. 
  { eapply ES.K_inE; eauto; desf; eapply CONT. }
  assert (ES.cont_sb_dom S k x) as KSBx. 
  { unfold ES.cont_sb_dom. desf. 
    unfold dom_rel. eexists. basic_solver. }
  arewrite (ES.seqn S x = ES.seqn S' x).
  { symmetry; eapply basic_step_seqn_eq_dom; eauto. }

  (* The following proof is similar to proof of `seqn_immsb` lemma.
     We don't reuse this lemma here, because it assumes `Wf S'`
     (althoug it really uses only sb-related properties). 
     However, since here we are working with basic step, 
     we can only assume well-formdness of `sb`. 
   *)
  unfold ES.seqn.
  assert (immediate (sb S' ∩ ES.same_tid S') x e) as IMMSB_STID. 
  { apply immediate_inter. split. 
    { eapply basic_step_imm_sb_e; eauto. }
    red. erewrite basic_step_tid_e with (e := e); eauto.
    unfold ES.cont_thread; subst.
    eapply basic_step_tid_eq_dom; eauto. }
  erewrite trans_prcl_immediate_seqr_split with (y := e). 
  all: eauto using inter_trans, basic_step_sb_trans, ES.same_tid_trans, basic_step_sb_prcl. 
  rewrite dom_cross; [| red; basic_solver].
  rewrite countNatP_union.
  { eapply Nat.add_wd; auto. 
    eapply countNatP_eq. 
    eapply basic_step_acts_set_mon; eauto. }
  unfolder; ins; desf. 
  eapply basic_step_sb_irr; eauto.
Qed.

Lemma basic_step_seqn_e' e e' S S' 
      (BSTEP : t e (Some e') S S') 
      (WF : ES.Wf S) :
  ES.seqn S' e' = 1 + ES.seqn S' e. 
Proof.   
  cdes BSTEP; cdes BSTEP_.  
  unfold ES.seqn. 
  assert (immediate (sb S' ∩ ES.same_tid S') e e') as IMMSB_STID. 
  { apply immediate_inter. split. 
    { eapply basic_step_imm_sb_e'; eauto. }
    red. erewrite basic_step_tid_e, basic_step_tid_e'; eauto. }
  erewrite trans_prcl_immediate_seqr_split with (y := e'). 
  all: eauto using inter_trans, basic_step_sb_trans, ES.same_tid_trans, basic_step_sb_prcl. 
  rewrite dom_cross; [| red; basic_solver].
  rewrite countNatP_union.
  { eapply Nat.add_wd; auto. 
    eapply countNatP_eq.
    unfold opt_ext in *. omega. }
  unfolder; ins; desf. 
  eapply basic_step_sb_irr; eauto.
Qed.

End ESBasicStep.