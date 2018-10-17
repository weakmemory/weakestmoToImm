Require Import Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events ProgToExecution Execution.
Require Import AuxRel AuxDef EventStructure Consistency.

Export ListNotations.

Module ESstep.

Notation "'R' S" := (fun a => is_true (is_r S.(ES.lab) a)) (at level 10).
Notation "'W' S" := (fun a => is_true (is_w S.(ES.lab) a)) (at level 10).
Notation "'F' S" := (fun a => is_true (is_f S.(ES.lab) a)) (at level 10).
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

Inductive t_incons 
          (e  : eventid)
          (e' : option eventid) 
          (S S' : ES.t) : Prop :=
| t_fence       (BS  : t_basic e e' S S')
                (EN  : e' = None)
                (FF  : F S' e)
                (JF' : S'.(ES.jf) ≡ S.(ES.jf))
                (EW' : S'.(ES.ew) ≡ S.(ES.ew))
                (CO' : S'.(ES.co) ≡ S.(ES.co))
| t_load        (BS  : t_basic e e' S S')
                (EN  : e' = None)
                (AJF : add_jf e S S')
                (EW' : S'.(ES.ew) ≡ S.(ES.ew))
                (CO' : S'.(ES.co) ≡ S.(ES.co))
| t_store       (BS  : t_basic e e' S S')
                (EN  : e' = None)
                (JF' : S'.(ES.jf) ≡ S.(ES.jf))
                (AEW : add_ew e S S')
                (ACO : add_co e S S')
| t_update w    (BS  : t_basic e e' S S')
                (ES  : e' = Some w)
                (AJF : add_jf e  S S')
                (AEW : add_ew w S S')
                (ACO : add_co w S S').

Definition t (m : model) (S S' : ES.t) : Prop := exists e e',
  ⟪ TT  : t_incons e e' S S' ⟫ /\
  ⟪ CON : @es_consistent S' m ⟫.

Lemma basic_step_acts_set 
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BASIC_STEP : t_basic e e' S S') :
  S'.(ES.acts_set) ≡₁ S.(ES.acts_set) ∪₁ eq e ∪₁ eq_opt e'.
Proof. 
  cdes BASIC_STEP.
  cdes BSTEP_.
  edestruct e'; 
    unfold opt_ext in *; desf; 
    unfold ES.acts_set; 
    autounfold with unfolderDb;
    splits; unfold set_subset; intros; by omega.
Qed.

Lemma basic_step_acts_set_mon
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BASIC_STEP : t_basic e e' S S') :
  S.(ES.acts_set) ⊆₁ S'.(ES.acts_set).
Proof. 
  edestruct basic_step_acts_set as [INCL_L INCL_R]; eauto. 
  do 2 (apply set_subset_union_l in INCL_R; desf). 
Qed.

Lemma basic_step_tid_eq_dom
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e e' S S') :
  eq_dom S.(ES.acts_set) S.(ES.tid) S'.(ES.tid).
Proof. 
  unfold eq_dom. ins. 
  unfold ES.acts_set in SX.
  cdes BSTEP. 
  cdes BSTEP_.
  rewrite TID'.
  unfold opt_ext in *.
  destruct e';
    desf; unfold upd_opt; rewrite updo; try rewrite updo; desf; omega.
Qed.

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

Lemma basic_step_sb_mon
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e e' S S') :
  S.(ES.sb) ⊆ S'.(ES.sb).
Proof.
  cdes BSTEP.
  cdes BSTEP_.
  desf; rewrite SB'; basic_solver. 
Qed.

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

Lemma step_jf_mon e e' S S' (STEP_: t_incons e e' S S') :
  S.(ES.jf) ⊆ S'.(ES.jf).
Proof. 
  destruct STEP_; try (by rewrite JF'; apply inclusion_refl2); 
    cdes AJF; rewrite JF'; basic_solver.  
Qed.

Lemma step_ew_mon e e' S S' (STEP_: t_incons e e' S S') :
  S.(ES.ew) ⊆ S'.(ES.ew).
Proof. 
  destruct STEP_; try (by rewrite EW');
    cdes AEW; rewrite REPR; basic_solver. 
Qed.

Lemma step_jfe_mon e e' S S' (STEP_: t_incons e e' S S') (wfE: ES.Wf S) :
  S.(ES.jfe) ⊆ S'.(ES.jfe).
Proof. 
  unfold ES.jfe.
  edestruct STEP_; 
    cdes BS;
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
  apply inclusion_inter_mon.
  { edestruct STEP_; eapply basic_step_cf_mon; apply BS. } 
  apply inclusion_seq_mon.
  { eapply step_jfe_mon; eauto. }
  apply inclusion_seq_mon.
  { unfold inclusion. ins. eapply clos_refl_trans_mon.
    { apply H. }
    apply inclusion_union_mon.
    { edestruct STEP_; eapply basic_step_sb_mon; apply BS. }
    eapply step_jf_mon; eauto. } 
  apply inclusion_seq_mon. 
  { eapply step_jfe_mon; eauto. }
  apply clos_refl_mori. 
  edestruct STEP_; eapply basic_step_sb_mon; apply BS. 
Qed.
      
Lemma step_vis_mon e e' S S' (STEP_: t_incons e e' S S') (wfE: ES.Wf S) :
  vis S ⊆₁ vis S'.
Proof.
  assert (ES.sb S ⊆ ES.sb S') as HH.
  { edestruct STEP_; eapply basic_step_sb_mon; apply BS. }
  unfold vis. 
  eauto 10 using 
        inclusion_seq_mon, codom_rel_mori, inclusion_inter_mon, 
        step_cc_mon, step_ew_mon,  eq_class_mori.
Qed.

Lemma step_event_to_act e e' S S' (STEP_: t_incons e e' S S') (wfE: ES.Wf S) : 
  eq_dom (ES.acts_set S) (ES.event_to_act S) (ES.event_to_act S').
Proof.
Admitted. 

End ESstep.