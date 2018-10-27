Require Import Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events. 
Require Import AuxRel AuxDef EventStructure Consistency.

Export ListNotations.

Module ESstep.

Notation "'E' S" := S.(ES.acts_set) (at level 10).
Notation "'E_init' S" := S.(ES.acts_init_set) (at level 10).

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

Notation "'RW' S" := (R S ∪₁ W S) (at level 10).
Notation "'FR' S" := (F S ∪₁ R S) (at level 10).
Notation "'FW' S" := (F S ∪₁ W S) (at level 10).

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

Definition t (m : model) (S S' : ES.t) : Prop := exists e e',
  ⟪ TT  : t_incons e e' S S' ⟫ /\
  ⟪ CON : @es_consistent S' m ⟫.


(******************************************************************************)
(** ** Some useful tactics *)
(******************************************************************************)

Ltac unfold_t_incons H := 
  unfold t_incons, t_fence, t_load, t_store, t_update in H; desf. 

(* Proves that `r ⨾ ⦗E⦘ ⨾ ⦗eq e⦘ ⨾ r'` or `r ⨾ ⦗eq e⦘ ⨾ ⦗E⦘ ⨾ r'` are empty. *)
Ltac E_seq_e := 
  apply seq_codom_dom_inter, set_disjointE;
  autounfold with unfolderDb; ins; splits; desf; omega.

(******************************************************************************)
(** ** Basic step properites *)
(******************************************************************************)

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

Lemma basic_step_acts_set_NE e e' S S'  
      (BSTEP : t_basic e e' S S') :
  ~ S.(ES.acts_set) e.
Proof. 
  unfold not, ES.acts_set; ins.
  cdes BSTEP; cdes BSTEP_; omega.
Qed.

Lemma basic_step_acts_set_mon e e' S S' 
      (BSTEP : t_basic e e' S S') :
  S.(ES.acts_set) ⊆₁ S'.(ES.acts_set).
Proof. 
  edestruct basic_step_acts_set as [INCL_L INCL_R]; eauto. 
  do 2 (apply set_subset_union_l in INCL_R; desf). 
Qed.

Lemma basic_step_tid_eq_dom e e' S S' 
      (BSTEP : t_basic e e' S S') :
  eq_dom S.(ES.acts_set) (tid S) (tid S').
Proof. 
  unfold eq_dom. ins. 
  unfold ES.acts_set in SX.
  cdes BSTEP; cdes BSTEP_.
  rewrite TID'.
  unfold opt_ext in *.
  destruct e';
    desf; unfold upd_opt; rewrite updo; try rewrite updo; desf; omega.
Qed.

Lemma basic_step_same_tid e e' S S'  
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

Lemma basic_step_lab_eq_dom e e' S S' 
      (BSTEP : t_basic e e' S S') :
  eq_dom S.(ES.acts_set) (lab S) (lab S').
Proof. 
  unfold eq_dom. ins. 
  unfold ES.acts_set in SX.
  cdes BSTEP; cdes BSTEP_.
  rewrite LAB'.
  unfold opt_ext in *.
  destruct e', lbl'; 
    desf; unfold upd_opt; rewrite updo; try rewrite updo; desf; omega.
Qed.

Lemma basic_step_loc_eq_dom e e' S S' 
      (BSTEP : t_basic e e' S S') :
  eq_dom S.(ES.acts_set) (loc S) (loc S').
Proof. 
  unfold eq_dom, Events.loc, ES.acts_set.
  ins; erewrite basic_step_lab_eq_dom; eauto. 
Qed.

Lemma basic_step_same_loc e e' S S' 
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

Lemma basic_step_mod_eq_dom e e' S S' 
      (BSTEP : t_basic e e' S S') :
  eq_dom S.(ES.acts_set) (mod S) (mod S').
Proof. 
  unfold eq_dom, Events.mod, ES.acts_set.
  ins; erewrite basic_step_lab_eq_dom; eauto. 
Qed.

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

Lemma basic_step_sb_mon e e' S S' 
      (BSTEP : t_basic e e' S S') :
  S.(ES.sb) ⊆ S'.(ES.sb).
Proof.
  cdes BSTEP; cdes BSTEP_.
  desf; rewrite SB'; basic_solver. 
Qed.

Lemma basic_step_cf lang k k' st st' e e' S S' 
      (BSTEP_ : t_basic_ lang k k' st st' e e' S S') :
  cf S' ≡ cf S ∪ 
                ES.cont_cf_dom S k × eq e ∪ eq e × ES.cont_cf_dom S k ∪
                ES.cont_cf_dom S k × eq_opt e' ∪ eq_opt e' × ES.cont_cf_dom S k.
Proof.
  cdes BSTEP_.
  unfold "cf" at 1.
  admit.
  
  (* arewrite  *)
  (*   ((sb S')^? ∪ (sb S')⁻¹ ≡  *)
  (*           (sb S)^? ∪ (sb S)⁻¹ ∪  *)
  (*           ES.cont_sb_dom S k × eq e ∪ eq e × ES.cont_sb_dom S k ∪  *)
  (*           ES.cont_sb_dom S k × eq_opt e' ∪ eq_opt e' × ES.cont_sb_dom S k ∪ *)
  (*           eq e × eq_opt e' ∪ eq_opt e' × eq e). *)
  (* { rewrite SB'.  *)
  (*   repeat rewrite cr_union_l. *)
  (*   repeat rewrite transp_union.  *)
  (*   repeat rewrite transp_cross.  *)
  (*   rewrite cross_union_l, cross_union_r. *)
  (*   basic_solver 10. } *)

  (* repeat rewrite (unionA ((sb S)^? ∪ (sb S)⁻¹)). *)
  (* rewrite compl_union. *)
  (* rewrite <- interA. *)
  (* (* rewrite <- (interK (ES.same_tid S')). *) *)
  (* (* rewrite interA. *) *)
  (* (* rewrite (interAC (ES.same_tid S') (compl_rel ((sb S)^? ∪ (sb S)⁻¹))). *) *)
  (* (* rewrite <- interA. *) *)
  (* (* rewrite seq_inter_l. *) *)
  
  (* rewrite basic_step_acts_set.  *)
  (* 2: { unfold t_basic.  do 5 eexists; eapply BSTEP_. } *)
  (* repeat rewrite id_union. *)
  (* repeat rewrite seq_union_r. *)
  (* repeat rewrite seq_union_l. *)

  (* repeat rewrite (unionA ((sb S)^? ∪ (sb S)⁻¹)). *)
  (* rewrite compl_union. *)
  (* rewrite <- (interK (ES.same_tid S')). *)
  (* rewrite interA. *)
  (* rewrite (interAC (ES.same_tid S') (compl_rel ((sb S)^? ∪ (sb S)⁻¹))). *)
  (* rewrite <- interA. *)
  (* rewrite seq_inter_l. *)
Admitted.


Lemma basic_step_cf_mon e e' S S' 
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

(******************************************************************************)
(** ** Monotonocity step lemmas *)
(******************************************************************************)

Lemma step_sb_mon e e' S S' 
      (ISTEP : t_incons e e' S S') :
  S.(ES.sb) ⊆ S'.(ES.sb).
Proof. eapply basic_step_sb_mon; unfold_t_incons ISTEP; eauto. Qed.

Lemma step_cf_mon e e' S S' 
      (ISTEP : t_incons e e' S S') :
  S.(ES.cf) ⊆ S'.(ES.cf).
Proof. eapply basic_step_cf_mon; unfold_t_incons ISTEP; eauto. Qed.

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
        clos_refl_sym_mori.
Qed.

Lemma step_event_to_act e e' S S' (STEP_: t_incons e e' S S') (wfE: ES.Wf S) :
  eq_dom (E S) (ES.event_to_act S) (ES.event_to_act S').
Admitted.

(******************************************************************************)
(** ** Well-formedness *)
(******************************************************************************)

Lemma step_wf e e' S S'
      (ISTEP: t_incons e e' S S') 
      (wfE: ES.Wf S) :
  ES.Wf S'.
Proof. Admitted.

(******************************************************************************)
(** ** Load step properties *)
(******************************************************************************)

Lemma load_step_r e e' S S'
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ R S' ≡₁ (E S ∩₁ R S) ∪₁ eq e.
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  unfold upd_opt in LAB'.
  rewrite basic_step_nupd_acts_set; eauto.
  rewrite set_inter_union_l.
  arewrite (E S ∩₁ R S' ≡₁ E S ∩₁ R S ).
  { unfold is_r.
    rewrite LAB'.
    autounfold with unfolderDb; unfold set_subset; splits;
      intros x [xE HH]; [rewrite updo in HH | rewrite updo];
      splits; auto; omega. }
  arewrite (eq e ∩₁ R S' ≡₁ eq e); [|auto]. 
  autounfold with unfolderDb; unfold set_subset; splits; [|basic_solver]; ins; desf. 
Qed.  

Lemma load_step_w e e' S S'
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ W S' ≡₁ E S ∩₁ W S.
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  unfold upd_opt in LAB'.
  rewrite basic_step_nupd_acts_set; eauto.
  rewrite set_inter_union_l.
  arewrite (E S ∩₁ W S' ≡₁ E S ∩₁ W S ).
  { unfold is_w.
    rewrite LAB'.
    autounfold with unfolderDb; unfold set_subset; splits;
      intros x [xE HH]; [rewrite updo in HH | rewrite updo];
      splits; auto; omega. }
  arewrite (eq e ∩₁ W S' ≡₁ ∅); [|by rewrite set_union_empty_r]. 
  autounfold with unfolderDb; unfold set_subset; splits; [|basic_solver].
  intros x [eEQ HH]; desf.
  unfold is_w in HH.
  unfold is_r in RR.
  by rewrite LAB', upds in RR, HH; desf.
Qed.  

Lemma load_step_f e e' S S'
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ F S' ≡₁ E S ∩₁ F S.
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  unfold upd_opt in LAB'.
  rewrite basic_step_nupd_acts_set; eauto.
  rewrite set_inter_union_l.
  arewrite (E S ∩₁ F S' ≡₁ E S ∩₁ F S).
  { unfold is_f.
    rewrite LAB'.
    autounfold with unfolderDb; unfold set_subset; splits;
      intros x [xE HH]; [rewrite updo in HH | rewrite updo];
      splits; auto; omega. }
  arewrite (eq e ∩₁ F S' ≡₁ ∅); [|by rewrite set_union_empty_r]. 
  autounfold with unfolderDb; unfold set_subset; splits; [|basic_solver].
  intros x [eEQ HH]; desf.
  unfold is_f in HH.
  unfold is_r in RR.
  by rewrite LAB', upds in RR, HH; desf.
Qed.  

Lemma load_step_rel e e' S S'
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ FW S' ∩₁ Rel S' ≡₁ E S ∩₁ FW S ∩₁ Rel S.
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite set_inter_union_r, load_step_w, load_step_f; eauto.
  rewrite <- set_inter_union_r.
  rewrite (set_interC (E S)).
  rewrite set_interA.
  arewrite (E S ∩₁ Rel S' ≡₁ E S ∩₁ Rel S); [|basic_solver].
  unfold is_rel, mode_le. 
  autounfold with unfolderDb; unfold set_subset; splits;
    intros x [xE HH];
    [ erewrite <- basic_step_mod_eq_dom in HH
    | erewrite basic_step_mod_eq_dom in HH ];
    eauto. 
Qed.

Lemma load_step_acq e e' S S'
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ FR S' ∩₁ Acq S' ≡₁ (E S ∩₁ FR S ∩₁ Acq S) ∪₁ (eq e ∩₁ Acq S').
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite set_inter_union_r, load_step_r, load_step_f; eauto.
  rewrite <- set_unionA.
  rewrite <- set_inter_union_r.
  rewrite set_inter_union_l.
  arewrite (E S ∩₁ FR S ∩₁ Acq S' ≡₁ E S ∩₁ FR S ∩₁ Acq S); auto.
  unfold is_acq, mode_le. 
  autounfold with unfolderDb; unfold set_subset; splits;
    intros x [[xE xFR] HH];
    [ erewrite <- basic_step_mod_eq_dom in HH
    | erewrite basic_step_mod_eq_dom in HH ];
    eauto.
Qed.  

Lemma load_step_rf e e' S S'
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) : 
  rf S' ≡ rf S ∪ (ew S)^? ⨾ jf S' ⨾ ⦗eq e⦘ \ cf S'.
Proof.
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  unfold "rf" at 1.
  rewrite EW', JF'.
  autorewrite with hahn hahn_full.
  rewrite minus_union_l.
  arewrite ((ew S)^? ⨾ jf S \ cf S' ≡ rf S).
  { unfold "rf".
    admit. }
  arewrite ((ew S)^? ⨾ jf S ⨾ ⦗eq e⦘ ≡ ∅₂).
  { rewrite ES.jfE; auto.
    repeat rewrite seqA.
    by E_seq_e. }
  arewrite (singl_rel w e ⨾ ⦗eq e⦘ ≡ singl_rel w e); 
    basic_solver 10.
Admitted.

Lemma load_step_rf_rmw e e' S S'
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) : 
  rf S' ⨾ rmw S' ≡ rf S ⨾ rmw S.
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite basic_step_nupd_rmw; eauto.
  unfold "rf". 
  rewrite JF', EW'.
  rewrite seq_union_r, minus_union_l, seq_union_l.
  arewrite (((ew S)^? ⨾ singl_rel w e \ cf S') ⨾ rmw S ≡ ∅₂). 
  { rewrite crE. 
    rewrite seq_union_l. 
    rewrite minus_union_l.
    rewrite seq_union_l. 
    rewrite seq_id_l.
    unfold same_relation; splits; [|basic_solver].
    rewrite ES.rmwE; auto.
    apply inclusion_union_l;
      autounfold with unfolderDb; ins; splits; desf; omega. }
  rewrite union_false_r.
  admit.
Admitted.
    
Lemma load_step_rs e e' S S' 
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  rs S' ≡ rs S.
Proof.
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  assert (ES.Wf S') as wfE'.
  { eapply step_wf; unfold t_incons; eauto. }
  repeat rewrite rs_alt; auto.
  rewrite basic_step_nupd_sb, load_step_w, load_step_rf_rmw; eauto.
  do 2 rewrite crE.
  relsf.
  apply union_more; auto.
  do 2 rewrite <- seqA.
  rewrite (seqA ⦗E S ∩₁ W S⦘).
  rewrite <- restr_relE.
  rewrite restr_inter.
  rewrite restr_union.
  arewrite (restr_rel (E S ∩₁ W S) (ES.cont_sb_dom S k × eq e) ≡ ∅₂).
  { rewrite restr_relE.
    rewrite seq_eqv_cross.
    arewrite (E S ∩₁ W S ∩₁ eq e ≡₁ ∅); [|by rewrite cross_false_r].
    autounfold with unfolderDb; unfold set_subset; splits; ins; desf; omega. }
  arewrite (restr_rel (E S ∩₁ W S) (same_loc S') ≡ restr_rel (E S ∩₁ W S) (same_loc S)).
  { do 2 rewrite <- restr_restr.
    apply restr_rel_more; auto.
    rewrite <- basic_step_same_loc; eauto. }
  basic_solver 21.
Qed.

Lemma load_step_release e e' S S' 
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  release S' ≡ release S. 
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.  
  assert (ES.Wf S') as wfE'.
  { eapply step_wf; unfold t_incons; eauto. }
  repeat rewrite release_alt; auto.
  rewrite basic_step_nupd_sb, load_step_rel, load_step_f, load_step_rs; eauto.
  do 2 rewrite crE.
  relsf.
  apply union_more; auto.
  repeat rewrite seqA.
  arewrite (ES.cont_sb_dom S k × eq e ⨾ rs S ≡ ∅₂); [|basic_solver 10].
  rewrite rsE; auto.
  arewrite (ES.cont_sb_dom S k × eq e ⨾ ⦗E S⦘ ≡ ∅₂); [ by E_seq_e | basic_solver ].
Qed.

Lemma load_step_sw e e' S S' 
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  sw S' ≡ sw S ∪ release S ⨾ rf S' ⨾ ⦗eq e⦘ ⨾ ⦗Acq S'⦘. 
Proof.
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.  
  assert (ES.Wf S') as wfE'.
  { eapply step_wf; unfold t_incons; eauto. }
  repeat rewrite sw_alt; auto.
  rewrite 
    load_step_release, load_step_rf, load_step_f, load_step_acq,
    basic_step_nupd_sb;
    eauto.
  rewrite id_union.
  repeat rewrite crE.
  relsf.
  repeat rewrite unionA.
  apply union_more; auto.
  apply union_more; auto.
  arewrite (ES.cont_sb_dom S k × eq e ⨾ ⦗E S ∩₁ F S⦘ ≡ ∅₂) by E_seq_e.
  arewrite (⦗E S ∩₁ F S⦘ ⨾ ⦗eq e ∩₁ Acq S'⦘ ≡ ∅₂) by E_seq_e.
  rewrite <- (seqA ((jf S' ⨾ ⦗eq e⦘ ∪ ew S ⨾ jf S' ⨾ ⦗eq e⦘) \ cf S')).
  arewrite 
    (((jf S' ⨾ ⦗eq e⦘ ∪ ew S ⨾ jf S' ⨾ ⦗eq e⦘) \ cf S') ⨾ sb S ≡ ∅₂) 
    by rewrite ES.sbE; auto; E_seq_e.
  relsf.
  rewrite id_union, seq_union_r.
  arewrite 
    (((jf S' ⨾ ⦗eq e⦘ ∪ ew S ⨾ jf S' ⨾ ⦗eq e⦘) \ cf S') ⨾ ⦗E S ∩₁ F S ∩₁ Acq S⦘ ≡ ∅₂) 
    by E_seq_e.
  arewrite 
    (((jf S' ⨾ ⦗eq e⦘ ∪ ew S ⨾ jf S' ⨾ ⦗eq e⦘) \ cf S') ⨾ ⦗E S ∩₁ R S ∩₁ Acq S⦘ ≡ ∅₂) 
    by E_seq_e.
  basic_solver 42.
Qed.

Lemma load_step_hb lang k k' st st' e e' S S' 
      (BSTEP_ : t_basic_ lang k k' st st' e e' S S') 
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  hb S' ≡ hb S ∪ 
     (hb S)^? ⨾ (ES.cont_sb_dom S k × eq e ∪ release S ⨾ rf S' ⨾ ⦗eq e⦘ ⨾ ⦗Acq S'⦘). 
Proof.
  cdes LSTEP; cdes AJF; cdes BSTEP_; desf.
  unfold hb at 1.
  rewrite basic_step_nupd_sb, load_step_sw; eauto.
  rewrite unionA.
  rewrite (unionAC (ES.cont_sb_dom S k × eq (ES.next_act S))).
  rewrite <- (unionA (sb S)).
  rewrite unionC.
  erewrite clos_trans_union_ext.
  { rewrite <- cr_of_ct.
    fold (hb S).
    basic_solver. }
  { unfold same_relation; splits; [|basic_solver].
    rewrite ES.cont_sb_domE, releaseE; eauto; by E_seq_e. }
  { unfold same_relation; splits; [|basic_solver].
    rewrite ES.cont_sb_domE, ES.sbE, swE; eauto; by E_seq_e. }
Qed.
    
End ESstep.