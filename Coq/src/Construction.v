Require Import Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events. 
Require Import AuxRel AuxDef EventStructure Consistency.

Export ListNotations.

Module ESstep.

Notation "'E' S" := S.(ES.acts_set) (at level 10).
Notation "'E_init' S" := S.(ES.acts_init_set) (at level 10).
Notation "'lab' S" := S.(ES.lab) (at level 10).
Notation "'sb' S" := S.(ES.sb) (at level 10).
Notation "'rmw' S" := S.(ES.rmw) (at level 10).
Notation "'ew' S" := S.(ES.ew) (at level 10).
Notation "'jf' S" := S.(ES.jf) (at level 10).
Notation "'rf' S" := S.(ES.rf) (at level 10).
Notation "'co' S" := S.(ES.co) (at level 10).
Notation "'cf' S" := S.(ES.cf) (at level 10).
Notation "'cc' S" := S.(ES.cc) (at level 10).

Notation "'jfe' S" := S.(ES.jfe) (at level 10).
Notation "'rfe' S" := S.(ES.rfe) (at level 10).
Notation "'coe' S" := S.(ES.coe) (at level 10).
Notation "'jfi' S" := S.(ES.jfi) (at level 10).
Notation "'rfi' S" := S.(ES.rfi) (at level 10).
Notation "'coi' S" := S.(ES.coi) (at level 10).

Notation "'R' S" := (fun a => is_true (is_r S.(ES.lab) a)) (at level 10).
Notation "'W' S" := (fun a => is_true (is_w S.(ES.lab) a)) (at level 10).
Notation "'F' S" := (fun a => is_true (is_f S.(ES.lab) a)) (at level 10).

Notation "'Pln' S" := (fun a => is_true (is_only_pln S.(ES.lab) a)) (at level 10).
Notation "'Rlx' S" := (fun a => is_true (is_rlx S.(ES.lab) a)) (at level 10).
Notation "'Rel' S" := (fun a => is_true (is_rel S.(ES.lab) a)) (at level 10).
Notation "'Acq' S" := (fun a => is_true (is_acq S.(ES.lab) a)) (at level 10).
Notation "'Acqrel' S" := (fun a => is_true (is_acqrel S.(ES.lab) a)) (at level 10).
Notation "'Sc' S" := (fun a => is_true (is_sc S.(ES.lab) a)) (at level 10).

Notation "'same_loc' S" := (same_loc S.(ES.lab)) (at level 10).
Notation "'same_val' S" := (same_val S.(ES.lab)) (at level 10).
Notation "'K' S" := (S.(ES.cont_set)) (at level 10).

Definition t_basic_
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
    ⟪ CONT   : K S (k, existT _ lang st) ⟫ /\
    ⟪ CONT'  : S'.(ES.cont) = (CEvent (opt_ext e e'), existT _ lang st') :: S.(ES.cont) ⟫ /\
    ⟪ STEP   : lang.(Language.step) lbls st st' ⟫ /\
    ⟪ LABEL' : opt_same_ctor e' lbl' ⟫ /\
    ⟪ LAB'   : S'.(ES.lab) = upd_opt (upd S.(ES.lab) e lbl ) e' lbl' ⟫ /\
    ⟪ TID'   : S'.(ES.tid) = upd_opt (upd S.(ES.tid) e thrd) e' (Some thrd) ⟫ /\
    ⟪ SB'    : S'.(ES.sb) ≡ S.(ES.sb) ∪ ES.cont_sb_dom S k × eq e ∪ 
                                      (ES.cont_sb_dom S k ∪₁ eq e) × eq_opt e' ⟫ /\
    ⟪ RMW'   : S'.(ES.rmw) ≡ S.(ES.rmw) ∪ eq e × eq_opt e' ⟫.

Definition t_basic
           (e  : eventid)
           (e' : option eventid)
           (S S' : ES.t) : Prop :=
  exists lang k k' st st', 
    ⟪ BSTEP_ : t_basic_ lang k k' st st' e e' S S' ⟫.

Definition add_jf (r : eventid) (S S' : ES.t) : Prop :=
  ⟪ RR : R S' r ⟫ /\
  exists w,
    ⟪ EW  : S.(ES.acts_set) w ⟫ /\
    ⟪ WW  : W S' w ⟫ /\
    ⟪ LOC : same_loc S' w r ⟫ /\
    ⟪ VAL : same_val S' w r ⟫ /\
    ⟪ JF' : S'.(ES.jf) ≡ S.(ES.jf) ∪ singl_rel w r ⟫.

Definition add_ew (w : eventid) (S S' : ES.t) : Prop :=
  ⟪ WW : W S' w ⟫ /\
  exists (ws : eventid -> Prop),
    ⟪ WWS   : ws ⊆₁ W S ⟫ /\
    ⟪ LOCWS : ws ⊆₁ same_loc S w ⟫ /\
    ⟪ VALWS : ws ⊆₁ same_val S w ⟫ /\
    ⟪ CFWS  : ws ⊆₁ S.(ES.cf) w ⟫ /\
    ⟪ REPR :
      S'.(ES.ew) ≡ S.(ES.ew) ∪ ws × eq w ∪ eq w × ws ⟫.

Definition add_co (w : eventid) (S S' : ES.t) : Prop :=
  let A := S.(ES.acts_set) ∩₁ W S ∩₁ (same_loc S w) \₁ (S.(ES.cf)^? w) in
  ⟪ WW : W S' w ⟫ /\
  exists (ws : eventid -> Prop),
    ⟪ WWS : ws ⊆₁ A ⟫ /\
    ⟪ REPR :
      S'.(ES.co) ≡ S.(ES.co) ∪ S.(ES.ew) ∪ ws × eq w ∪ eq w × (A \₁ ws) ⟫.

Definition t_fence 
           (e  : eventid)
           (e' : option eventid) 
           (S S' : ES.t) : Prop := 
  ⟪ ENONE : e' = None ⟫ /\
  ⟪ BSTEP : t_basic e None S S' ⟫ /\
  ⟪ FF  : F S' e ⟫ /\
  ⟪ JF' : S'.(ES.jf) ≡ S.(ES.jf) ⟫ /\
  ⟪ EW' : S'.(ES.ew) ≡ S.(ES.ew) ⟫ /\
  ⟪ CO' : S'.(ES.co) ≡ S.(ES.co) ⟫.

Definition t_load 
           (e  : eventid)
           (e' : option eventid) 
           (S S' : ES.t) : Prop := 
  ⟪ ENONE : e' = None ⟫ /\
  ⟪ BSTEP : t_basic e None S S' ⟫ /\
  ⟪ AJF : add_jf e S S' ⟫ /\
  ⟪ EW' : S'.(ES.ew) ≡ S.(ES.ew) ⟫ /\
  ⟪ CO' : S'.(ES.co) ≡ S.(ES.co) ⟫.

Definition t_store 
           (e  : eventid)
           (e' : option eventid) 
           (S S' : ES.t) : Prop := 
  ⟪ ENONE : e' = None ⟫ /\
  ⟪ BSTEP : t_basic e None S S' ⟫ /\
  ⟪ JF' : S'.(ES.jf) ≡ S.(ES.jf) ⟫ /\
  ⟪ AEW : add_ew e S S' ⟫ /\
  ⟪ ACO : add_co e S S' ⟫.

Definition t_update 
           (e  : eventid)
           (e' : option eventid) 
           (S S' : ES.t) : Prop := exists w,
  ⟪ ESOME : e' = Some w ⟫ /\
  ⟪ BSTEP : t_basic e e' S S' ⟫ /\
  ⟪ AJF : add_jf e S S' ⟫ /\
  ⟪ AEW : add_ew w S S' ⟫ /\
  ⟪ ACO : add_co w S S' ⟫.

Definition t_incons e e' S S' := 
  t_fence e e' S S' \/ t_load e e' S S' \/ t_store e e' S S' \/ t_update e e' S S'.

Ltac unfold_t_incons H := 
  unfold t_incons, t_fence, t_load, t_store, t_update in H; desf. 

Definition t (m : model) (S S' : ES.t) : Prop := exists e e',
  ⟪ TT  : t_incons e e' S S' ⟫ /\
  ⟪ CON : @es_consistent S' m ⟫.

(******************************************************************************)
(** ** Basic step properites *)
(******************************************************************************)

Ltac lift_basic_step H L := 
  unfold_t_incons H; eapply L; eauto.

Lemma basic_step_acts_set 
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e e' S S') :
  S'.(ES.acts_set) ≡₁ S.(ES.acts_set) ∪₁ eq e ∪₁ eq_opt e'.
Proof. 
  cdes BSTEP.
  cdes BSTEP_.
  edestruct e'; 
    unfold opt_ext in *; desf; 
    unfold ES.acts_set; 
    autounfold with unfolderDb;
    splits; unfold set_subset; intros; by omega.
Qed.

Lemma step_acts_set 
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (ISTEP : t_incons e e' S S') :
  S'.(ES.acts_set) ≡₁ S.(ES.acts_set) ∪₁ eq e ∪₁ eq_opt e'.
Proof. lift_basic_step ISTEP basic_step_acts_set. Qed.

Lemma basic_step_nupd_acts_set 
      (e  : eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e None S S') :
  S'.(ES.acts_set) ≡₁ S.(ES.acts_set) ∪₁ eq e.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  apply basic_step_acts_set in BSTEP.
  unfold eq_opt in BSTEP.
  by rewrite set_union_empty_r in BSTEP.
Qed.

Lemma step_nupd_acts_set 
      (e  : eventid)
      (S S' : ES.t) 
      (ISTEP : t_incons e None S S') :
  S'.(ES.acts_set) ≡₁ S.(ES.acts_set) ∪₁ eq e.
Proof. lift_basic_step ISTEP basic_step_nupd_acts_set. Qed.

Lemma basic_step_acts_set_NE  
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e e' S S') :
  ~ S.(ES.acts_set) e.
Proof. 
  unfold not, ES.acts_set; ins.
  cdes BSTEP; cdes BSTEP_; omega.
Qed.

Lemma step_acts_set_NE  
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (ISTEP : t_incons e e' S S') :
  ~ S.(ES.acts_set) e.
Proof. lift_basic_step ISTEP basic_step_acts_set_NE. Qed.

Lemma basic_step_acts_set_mon
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e e' S S') :
  S.(ES.acts_set) ⊆₁ S'.(ES.acts_set).
Proof. 
  edestruct basic_step_acts_set as [INCL_L INCL_R]; eauto. 
  do 2 (apply set_subset_union_l in INCL_R; desf). 
Qed.

Lemma step_acts_set_mon
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (ISTEP : t_incons e e' S S') :
  S.(ES.acts_set) ⊆₁ S'.(ES.acts_set).
Proof. lift_basic_step ISTEP basic_step_acts_set_mon. Qed.

Lemma basic_step_tid_eq_dom
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e e' S S') :
  eq_dom S.(ES.acts_set) S.(ES.tid) S'.(ES.tid).
Proof. 
  unfold eq_dom. ins. 
  unfold ES.acts_set in SX.
  cdes BSTEP; cdes BSTEP_.
  rewrite TID'.
  unfold opt_ext in *.
  destruct e';
    desf; unfold upd_opt; rewrite updo; try rewrite updo; desf; omega.
Qed.

Lemma step_tid_eq_dom
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (ISTEP : t_incons e e' S S') :
  eq_dom S.(ES.acts_set) S.(ES.tid) S'.(ES.tid).
Proof. lift_basic_step ISTEP basic_step_tid_eq_dom. Qed.

Lemma basic_step_same_tid
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e e' S S') :
  restr_rel S.(ES.acts_set) S.(ES.same_tid) ≡ restr_rel S.(ES.acts_set) S'.(ES.same_tid).
Proof. 
  autounfold with unfolderDb. 
  unfold ES.same_tid.
  splits; ins; desf; splits; auto;
    [erewrite <- basic_step_tid_eq_dom | erewrite basic_step_tid_eq_dom];
    eauto;
    rewrite H;
    [|symmetry];
    eapply basic_step_tid_eq_dom; eauto. 
Qed.

Lemma step_same_tid
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (ISTEP : t_incons e e' S S') :
  restr_rel S.(ES.acts_set) S.(ES.same_tid) ≡ restr_rel S.(ES.acts_set) S'.(ES.same_tid).
Proof. lift_basic_step ISTEP basic_step_same_tid. Qed.

Lemma basic_step_lab_eq_dom
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e e' S S') :
  eq_dom S.(ES.acts_set) S.(ES.lab) S'.(ES.lab).
Proof. 
  unfold eq_dom. ins. 
  unfold ES.acts_set in SX.
  cdes BSTEP; cdes BSTEP_.
  rewrite LAB'.
  unfold opt_ext in *.
  destruct e', lbl'; 
    desf; unfold upd_opt; rewrite updo; try rewrite updo; desf; omega.
Qed.

Lemma step_lab_eq_dom
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (ISTEP : t_incons e e' S S') :
  eq_dom S.(ES.acts_set) S.(ES.lab) S'.(ES.lab).
Proof. lift_basic_step ISTEP basic_step_lab_eq_dom. Qed.

Lemma basic_step_loc_eq_dom
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e e' S S') :
  eq_dom S.(ES.acts_set) (loc S.(ES.lab)) (loc S'.(ES.lab)).
Proof. 
  unfold eq_dom, loc, ES.acts_set.
  ins; erewrite basic_step_lab_eq_dom; eauto. 
Qed.

Lemma step_loc_eq_dom
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (ISTEP : t_incons e e' S S') :
  eq_dom S.(ES.acts_set) (loc S.(ES.lab)) (loc S'.(ES.lab)).
Proof. lift_basic_step ISTEP basic_step_loc_eq_dom. Qed.

Lemma basic_step_same_loc 
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e e' S S') :
  restr_rel S.(ES.acts_set) (same_loc S) ≡ restr_rel S.(ES.acts_set) (same_loc S').
Proof. 
  autounfold with unfolderDb. 
  unfold imm.basic.Events.same_loc.
  splits; ins; desf; splits; auto;
    [erewrite <- basic_step_loc_eq_dom | erewrite basic_step_loc_eq_dom];
    eauto;
    rewrite H;
    [|symmetry];
    eapply basic_step_loc_eq_dom; eauto. 
Qed.

Lemma step_same_loc 
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (ISTEP : t_incons e e' S S') :
  restr_rel S.(ES.acts_set) (same_loc S) ≡ restr_rel S.(ES.acts_set) (same_loc S').
Proof. lift_basic_step ISTEP basic_step_same_loc. Qed.

Lemma basic_step_nupd_sb lang k k' st st' e S S' 
      (BSTEP_ : t_basic_ lang k k' st st' e None S S') :
  S'.(ES.sb) ≡ S.(ES.sb) ∪ ES.cont_sb_dom S k × eq e.  
Proof.                                       
  cdes BSTEP_.
  unfold eq_opt in SB'.
  rewrite cross_false_r in SB'. 
  rewrite union_false_r in SB'.
  apply SB'.
Qed.

Lemma basic_step_sb_mon
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e e' S S') :
  S.(ES.sb) ⊆ S'.(ES.sb).
Proof.
  cdes BSTEP; cdes BSTEP_.
  desf; rewrite SB'; basic_solver. 
Qed.

Lemma step_sb_mon
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (ISTEP : t_incons e e' S S') :
  S.(ES.sb) ⊆ S'.(ES.sb).
Proof. lift_basic_step ISTEP basic_step_sb_mon. Qed.

Lemma basic_step_cf_mon 
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e e' S S') :
  S.(ES.cf) ⊆ S'.(ES.cf).
Proof.
  edestruct basic_step_same_tid as [STIDL STIDR]; [by apply BSTEP|].
  unfold ES.cf.
  cdes BSTEP. 
  cdes BSTEP_.
  rewrite SB'. 
  rewrite (basic_step_acts_set e e' S S'); [| apply BSTEP].
  unfold eq_opt. 
  repeat rewrite <- restr_relE.
  repeat rewrite restr_inter.
  rewrite STIDL. 
  autounfold with unfolderDb.
  ins; desf; splits; auto; 
    unfold not; ins; desf; auto; omega. 
Qed.

Lemma step_cf_mon 
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (ISTEP : t_incons e e' S S') :
  S.(ES.cf) ⊆ S'.(ES.cf).
Proof. lift_basic_step ISTEP basic_step_cf_mon. Qed.

Lemma basic_step_nupd_rmw e S S' 
      (BSTEP : t_basic e None S S') :
  rmw S' ≡ rmw S.  
Proof.                                       
  cdes BSTEP; cdes BSTEP_.
  unfold eq_opt in RMW'.
  rewrite cross_false_r in RMW'. 
  rewrite union_false_r in RMW'.
  apply RMW'.
Qed.

Lemma step_nupd_rmw e S S'
      (ISTEP : t_incons e None S S') :
  rmw S' ≡ rmw S.  
Proof. lift_basic_step ISTEP basic_step_nupd_rmw. Qed.

(******************************************************************************)
(** ** Inconsistent step properites *)
(******************************************************************************)

Lemma step_jf_mon e e' S S' (STEP_: t_incons e e' S S') :
  S.(ES.jf) ⊆ S'.(ES.jf).
Proof. 
  unfold_t_incons STEP_;
    try (by rewrite JF'; apply inclusion_refl2); 
    cdes AJF; rewrite JF'; basic_solver.  
Qed.

Lemma step_ew_mon e e' S S' (STEP_: t_incons e e' S S') :
  S.(ES.ew) ⊆ S'.(ES.ew).
Proof. 
  unfold_t_incons STEP_; try (by rewrite EW');
    cdes AEW; rewrite REPR; basic_solver. 
Qed.

Lemma step_jfe_mon e e' S S' (STEP_: t_incons e e' S S') (wfE: ES.Wf S) :
  S.(ES.jfe) ⊆ S'.(ES.jfe).
Proof. 
  unfold ES.jfe.
  unfold_t_incons STEP_; 
    cdes BSTEP;
    cdes BSTEP_;
    rewrite SB';
    try (cdes AJF);
    rewrite JF';
    rewrite wfE.(ES.jfE).
  1,3:
    autounfold with unfolderDb;
    ins; desf; splits;
    try (by eexists; splits; eauto);
    unfold not; ins; desf; omega.
  all:
    autounfold with unfolderDb;
    ins; desf; splits;
    try (by left; eexists; splits; eauto);
    unfold not; ins; desf; omega.
Qed.

Lemma step_cc_mon e e' S S' (STEP_: t_incons e e' S S') (wfE: ES.Wf S) :
  S.(ES.cc) ⊆ S'.(ES.cc).
Proof.
  unfold ES.cc. 
  eauto 20 using
        inclusion_union_mon, inclusion_inter_mon, inclusion_seq_mon, clos_refl_trans_mon,
        step_sb_mon, step_cf_mon, step_jf_mon, step_jfe_mon,
        clos_refl_mori, clos_refl_trans_mori.
Qed.
      
Lemma step_vis_mon e e' S S' (STEP_: t_incons e e' S S') (wfE: ES.Wf S) :
  vis S ⊆₁ vis S'.
Proof.
  unfold vis. 
  eauto 10 using 
        inclusion_seq_mon, codom_rel_mori, inclusion_inter_mon, 
        step_sb_mon, step_cc_mon, step_ew_mon,
        eq_class_mori.
Qed.

Lemma step_event_to_act e e' S S' (STEP_: t_incons e e' S S') (wfE: ES.Wf S) : 
  eq_dom (ES.acts_set S) (ES.event_to_act S) (ES.event_to_act S').
Admitted. 

(******************************************************************************)
(** ** Well-formdness *)
(******************************************************************************)

Lemma step_wf e e' S S'
      (ISTEP: t_incons e e' S S') 
      (wfE: ES.Wf S) :
  ES.Wf S'.
Proof. Admitted.

(******************************************************************************)
(** ** Load step properites *)
(******************************************************************************)

Lemma load_step_w e e' S S'
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ W S' ≡₁ E S ∩₁ W S.
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  unfold upd_opt in LAB'.

  admit.
Admitted.
(*   unfold is_w. *)
(*   rewrite LAB'. *)
  
(*   unfold upd, set_equiv, set_subset; split; ins. *)
(*   { destruct (excluded_middle_informative (x = e)) as [Heq |]; [|apply H]. *)
(*     (* Here we need a property like `forall x, ~ S.E x -> lab x = trash` *) *)
(*     admit. } *)
(*   destruct (excluded_middle_informative (x = e)) as [Heq |]; [|apply H]. *)
(*   (* Same here *) *)
(*   admit. *)
(* Admitted. *)

Lemma load_step_rf_rmw e e' S S'
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) : 
  rf S' ⨾ rmw S' ≡ rf S ⨾ rmw S.
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite basic_step_nupd_rmw; eauto.
  unfold "rf". 
  rewrite JF', EW'.
  rewrite seq_union_r.
  rewrite minus_union_l.
  rewrite seq_union_l.
  arewrite (((ew S)^? ⨾ singl_rel w e \ cf S') ⨾ rmw S ≡ ∅₂). 
  { rewrite crE. 
    rewrite seq_union_l. 
    rewrite minus_union_l.
    rewrite seq_union_l. 
    rewrite seq_id_l.
    unfold same_relation; splits; [|basic_solver].
    apply inclusion_union_l.
    (* Need some lemma like: `r ; r' ⊆ r'' -> (r \ a) ; r' ⊆ r''` *)
    { admit. }
    admit. 
Admitted.
    
Lemma load_step_rs e e' S S' 
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  rs S' ⨾ ⦗ E S' ⦘ ≡ rs S ⨾ ⦗ E S ⦘.
Proof.
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite rsEE; [| eapply step_wf; eauto; right; left; eauto ].
  rewrite (rsEE S); auto.
  unfold rs.
  do 2 rewrite 
     crE, seq_union_l, seq_union_r, seq_id_l, seq_union_l, seq_union_r.
  do 4 rewrite <- seqA. 
  do 2 rewrite seq_eqvK.
  repeat rewrite seqA.
  do 2 rewrite <- (seqA ⦗E S'⦘ ⦗W S'⦘).
  rewrite <- imm.lib.AuxRel.id_inter.
  rewrite load_step_w; eauto.
  rewrite imm.lib.AuxRel.id_inter.
  rewrite load_step_rf_rmw; eauto. 
  repeat rewrite seqA.
  rewrite (basic_step_nupd_acts_set e S S'); eauto. 
  rewrite id_union.
  repeat rewrite seq_union_r.
  arewrite ((rf S ⨾ rmw S)＊ ⨾ ⦗eq e⦘ ≡ ∅₂).
  { admit. }
  repeat rewrite seq_false_r.
  repeat rewrite union_false_r.
  apply union_more; eauto. 
  rewrite basic_step_nupd_sb; eauto.
  rewrite inter_union_l.
  rewrite seq_union_l.
  repeat rewrite seq_union_r.
  arewrite 
    (ES.cont_sb_dom S k × eq e ∩ same_loc S' ⨾ ⦗W S'⦘ ⨾ (rf S ⨾ rmw S)＊ ⨾ ⦗E S⦘ ≡ ∅₂).
  { admit. }
  repeat rewrite seq_false_r.
  repeat rewrite union_false_r.
  rewrite <- (seqA (sb S ∩ same_loc S')).
  arewrite (sb S ∩ same_loc S' ⨾ ⦗W S'⦘ ≡ sb S ∩ same_loc S ⨾ ⦗W S⦘); auto. 
  rewrite wfE.(ES.sbE).
  rewrite <- restr_relE.
  rewrite <- restr_inter_absorb_r.
  erewrite <- basic_step_same_loc; eauto. 
  rewrite <- restr_inter.
  rewrite <- restr_inter_absorb_r.
  rewrite <- restr_inter.
  rewrite restr_relE.
  repeat rewrite seqA.
  arewrite (⦗E S⦘ ⨾ ⦗W S'⦘ ≡ ⦗E S⦘ ⨾ ⦗W S⦘); auto.
  repeat rewrite <- imm.lib.AuxRel.id_inter.
  unfold is_w.
  autounfold with unfolderDb; splits; ins;
    [ erewrite (basic_step_lab_eq_dom _ _ _ _ BSTEP)
    | erewrite <- (basic_step_lab_eq_dom _ _ _ _ BSTEP) ]; 
    desf; auto.
Admitted.


Lemma step_fence_rf e e' S S' 
      (STEP_: t_incons e e' S S') 
      (wfE: ES.Wf S) 
      (EF : F S' e) :
  rf S' ≡ rf S.
Proof.
Admitted.

Lemma step_read_sw e e' S S' 
      (STEP_: t_incons e e' S S') 
      (wfE: ES.Wf S) 
      (eR : R S' e): 
  sw S' ≡ sw S ∪ release S ⨾ rf S' ⨾ ⦗ Acq S' ⦘ ⨾ ⦗ eq e ⦘.
Proof.
Admitted.

Lemma step_sw e e' S S' (STEP_: t_incons e e' S S') (wfE: ES.Wf S) : 
  sw S' ≡ sw S ∪ 
     release S ⨾ rf S' ⨾ ⦗ Acq S' ⦘ ⨾ ⦗ eq e ⦘ ∪ 
     release S ⨾ rf S  ⨾ sb S' ⨾ ⦗ F S' ⦘ ⨾ ⦗ Acq S' ⦘ ⨾ ⦗ eq e ⦘. 
Proof.
  unfold sw.
  edestruct STEP_.
  { rewrite step_fence_rf; eauto. 
    unfold ES.rf. 
    (* rewrite JF'. *)
    (* rewrite EW'. *)
    all: admit.
  }
Admitted.

End ESstep.