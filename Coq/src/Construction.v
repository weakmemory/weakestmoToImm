Require Import Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events AuxRel. 
Require Import AuxRel AuxDef EventStructure Consistency.

Set Implicit Arguments.

Export ListNotations.

Module ESstep.

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

Notation "'same_loc' S" := (same_loc S.(ES.lab)) (at level 10).
Notation "'same_val' S" := (same_val S.(ES.lab)) (at level 10).

Notation "'K' S" := (S.(ES.cont_set)) (at level 10).

Notation "'Tid' S" := (fun t e => S.(ES.tid) e = t) (at level 9).

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
    ⟪ KCE    : k' =  CEvent (opt_ext e e')⟫ /\
    ⟪ CONT   : K S (k, existT _ lang st) ⟫ /\
    ⟪ CONT'  : S'.(ES.cont) = (k', existT _ lang st') :: S.(ES.cont) ⟫ /\
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
  ⟪ FF  : F S' e ⟫ /\
  ⟪ JF' : S'.(ES.jf) ≡ S.(ES.jf) ⟫ /\
  ⟪ EW' : S'.(ES.ew) ≡ S.(ES.ew) ⟫ /\
  ⟪ CO' : S'.(ES.co) ≡ S.(ES.co) ⟫.

Definition t_load 
           (e  : eventid)
           (e' : option eventid) 
           (S S' : ES.t) : Prop := 
  ⟪ ENONE : e' = None ⟫ /\
  ⟪ AJF : add_jf e S S' ⟫ /\
  ⟪ EW' : S'.(ES.ew) ≡ S.(ES.ew) ⟫ /\
  ⟪ CO' : S'.(ES.co) ≡ S.(ES.co) ⟫.

Definition t_store 
           (e  : eventid)
           (e' : option eventid) 
           (S S' : ES.t) : Prop := 
  ⟪ ENONE : e' = None ⟫ /\
  ⟪ JF' : S'.(ES.jf) ≡ S.(ES.jf) ⟫ /\
  ⟪ AEW : add_ew e S S' ⟫ /\
  ⟪ ACO : add_co e S S' ⟫.

Definition t_update 
           (e  : eventid)
           (e' : option eventid) 
           (S S' : ES.t) : Prop := exists w,
  ⟪ ESOME : e' = Some w ⟫ /\
  ⟪ AJF : add_jf e S S' ⟫ /\
  ⟪ AEW : add_ew w S S' ⟫ /\
  ⟪ ACO : add_co w S S' ⟫.

Definition t_ e e' S S' := 
  t_fence e e' S S' \/ t_load e e' S S' \/ t_store e e' S S' \/ t_update e e' S S'.

Definition t (m : model) (S S' : ES.t) : Prop := exists e e',
  ⟪ TT  : t_ e e' S S' ⟫ /\
  ⟪ BSTEP : t_basic e e' S S' ⟫ /\
  ⟪ CON : @es_consistent S' m ⟫.

(******************************************************************************)
(** ** Some useful tactics *)
(******************************************************************************)

Ltac unfold_t_ H := 
  unfold t_, t_fence, t_load, t_store, t_update in H; desf. 

(* tries to solve goals like `sb ⨾ ⦗eq e⦘ ⊆ ∅₂`,
   where `e` is a new event added by step `S -> S'`,
   using the fact that `sb ≡ ⦗E⦘ ⨾ sb ⨾ ⦗E⦘` *)
Ltac step_solver := 
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
      (BSTEP : t_basic e e' S S') :
  ES.next_act S < ES.next_act S'.
Proof.
  cdes BSTEP. cdes BSTEP_.
  unfold opt_ext in *. desf.
  all: rewrite EVENT'; omega.
Qed.

Lemma basic_step_acts_set 
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e e' S S') :
  E S' ≡₁ E S ∪₁ eq e ∪₁ eq_opt e'.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  edestruct e'; 
    unfold opt_ext in *; desf; 
    unfold ES.acts_set; 
    unfolder;
    splits; unfold set_subset; intros; omega.
Qed.

Lemma basic_step_nupd_acts_set 
      (e  : eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e None S S') :
  E S' ≡₁ E S ∪₁ eq e.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  apply basic_step_acts_set in BSTEP.
  unfold eq_opt in BSTEP.
  by rewrite set_union_empty_r in BSTEP.
Qed.

Lemma basic_step_nupd_acts_mon e e' S S'  
      (BSTEP : t_basic e e' S S') :
  E S ⊆₁ E S'.
Proof. 
  rewrite basic_step_acts_set with (S' := S'); eauto. 
  basic_solver. 
Qed.

Lemma basic_step_acts_set_NE e e' S S'  
      (BSTEP : t_basic e e' S S') :
  ~ E S e.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold not, ES.acts_set; ins; omega.
Qed.

Lemma basic_step_acts_set_NE' e e' S S'  
      (BSTEP : t_basic e (Some e') S S') :
  ~ E S e'.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold not, ES.acts_set; ins; omega. 
Qed.

Lemma basic_step_acts_set_mon e e' S S' 
      (BSTEP : t_basic e e' S S') :
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
      (BSTEP : t_basic e e' S S')
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
      (BSTEP : t_basic e (Some e') S S')
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
      (BSTEP : t_basic e e' S S') :
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
      (BSTEP : t_basic e e' S S') :
  eq_dom (E S) (tid S') (tid S).
Proof. eapply basic_step_tidlab_eq_dom; eauto. Qed.

Lemma basic_step_same_tid_restr e e' S S'  
      (BSTEP : t_basic e e' S S') :
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
      (BSTEP_ : t_basic_ lang k k' st st' e e' S S') :
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
      (BSTEP_ : t_basic_ lang k k' st st' e (Some e') S S') :
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
      (BSTEP : t_basic e e' S S')
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
      (BSTEP : t_basic e e' S S')
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
      (BSTEP : t_basic e e' S S') :
  eq_dom (E S) (lab S') (lab S).
Proof. eapply basic_step_tidlab_eq_dom; eauto. Qed.

Lemma basic_step_loc_eq_dom  e e' S S'
      (BSTEP : t_basic e e' S S') :
  eq_dom (E S) (loc S') (loc S).
Proof.
  unfold Events.loc. red. ins.
  assert ((lab S') x = (lab S) x) as AA.
  2: by rewrite AA.
  eapply basic_step_lab_eq_dom; eauto.
Qed.

Lemma basic_step_same_loc_restr e e' S S' 
      (BSTEP : t_basic e e' S S') :
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
      (BSTEP : t_basic e e' S S') :
  eq_dom S.(ES.acts_set) (mod S') (mod S).
Proof. 
  unfold eq_dom, Events.mod, ES.acts_set.
  ins; erewrite basic_step_lab_eq_dom; eauto. 
Qed.

(******************************************************************************)
(** ** basic_step : `sb` propeties *)
(******************************************************************************)

Lemma basic_step_nupd_sb lang k k' st st' e S S' 
      (BSTEP_ : t_basic_ lang k k' st st' e None S S') :
  sb S' ≡ sb S ∪ ES.cont_sb_dom S k × eq e.  
Proof.                                       
  cdes BSTEP_.
  unfold eq_opt in SB'.
  rewrite cross_false_r in SB'. 
  rewrite union_false_r in SB'.
  apply SB'.
Qed.

Lemma basic_step_sb_restr e e' S S' 
      (BSTEP : t_basic e e' S S') 
      (WF: ES.Wf S) :
  restr_rel (E S) (sb S') ≡ sb S.  
Proof. 
  cdes BSTEP; cdes BSTEP_.
  rewrite SB', cross_union_r, !restr_union. 
  arewrite (restr_rel (E S) (ES.cont_sb_dom S k × eq e) ≡ ∅₂).
  { rewrite restr_relE. split; [|done]. step_solver. }
  arewrite (restr_rel (E S) (ES.cont_sb_dom S k × eq_opt e') ≡ ∅₂).
  { unfold eq_opt. 
    destruct e'; [|basic_solver].
    split; [|done]. step_solver. }
  arewrite (restr_rel (E S) (eq e × eq_opt e') ≡ ∅₂).
  { split; [|done]. step_solver. }
  rewrite ES.sbE at 2; auto. 
  basic_solver 10. 
Qed.

Lemma basic_step_sb_mon e e' S S' 
      (BSTEP : t_basic e e' S S') :
  sb S ⊆ sb S'.
Proof.
  cdes BSTEP; cdes BSTEP_.
  desf; rewrite SB'; basic_solver. 
Qed.

(******************************************************************************)
(** ** basic_step : `cf` propeties *)
(******************************************************************************)

Lemma basic_step_cf lang k k' st st' e e' S S' 
      (BSTEP_ : t_basic_ lang k k' st st' e e' S S') 
      (wfE: ES.Wf S) :
  cf S' ≡ cf S ∪ (ES.cont_cf_dom S k × eq e)^⋈ ∪ (ES.cont_cf_dom S k × eq_opt e')^⋈.
Proof.
  assert (t_basic e e' S S') as BSTEP.
  { unfold t_basic. do 5 eexists. eauto. }
  cdes BSTEP_.
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
      unfolder; splits; ins; splits; desf; unfold not;
        ins; splits; desf; auto; omega. }
    arewrite (Eninit S × Eninit S \ (ES.cont_sb_dom S k × eq_opt e')⁼ ≡ Eninit S × Eninit S \ ⦗⊤₁⦘).
    { unfold ES.acts_ninit_set, ES.acts_init_set.
      unfolder; splits; ins; splits; desf; unfold not;
        ins; splits; desf; auto; omega. }
    arewrite (Eninit S × Eninit S \ (eq e × eq_opt e')⁼ ≡ Eninit S × Eninit S \ ⦗⊤₁⦘).
    { unfold ES.acts_ninit_set, ES.acts_init_set.
      unfolder; splits; ins; splits; desf; unfold not;
        ins; splits; desf; auto; omega. }
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
          { edestruct e'; unfold eq_opt; split; try done; step_solver. }
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
            edestruct e'; unfold eq_opt; split; try done; step_solver. }
          arewrite 
            (⦗Eninit S⦘ ⨾ (ES.same_tid S' \ eq_opt e' × eq e) ⨾ ⦗eq e⦘ ≡ 
             ⦗Eninit S⦘ ⨾ (ES.same_tid S') ⨾ ⦗eq e⦘).
          { rewrite <- seqA.
            erewrite minus_eqv_absorb_rl; [by rewrite seqA|]. 
            unfold ES.acts_ninit_set.
            edestruct e'; unfold eq_opt; split; try done; step_solver. }
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
      (BSTEP_ : t_basic_ lang k k' st st' e None S S') 
      (wfE: ES.Wf S) :
  cf S' ≡ cf S ∪ (ES.cont_cf_dom S k × eq e)^⋈.
Proof. 
  erewrite basic_step_cf; eauto. 
  unfold eq_opt.
  basic_solver 42.
Qed.

Lemma basic_step_cf_restr e e' S S'
      (BSTEP : t_basic e e' S S') 
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
      (BSTEP : t_basic e e' S S') 
      (wfE: ES.Wf S) :
  S.(ES.cf) ⊆ S'.(ES.cf).
Proof.
  cdes BSTEP; cdes BSTEP_.
  erewrite basic_step_cf with (S':=S'); eauto.  
  rewrite unionA.
  apply inclusion_union_r1.
Qed.  

Lemma basic_step_cf_free lang k k' st st' e e' S S' X 
      (BSTEP_ : t_basic_ lang k k' st st' e e' S S') 
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
(** ** basic_step : continuation propeties *)
(******************************************************************************)

Lemma basic_step_cont_thread lang k st e e' S S' 
      (BSTEP_ : t_basic e e' S S') 
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
      (BSTEP_ : t_basic_ lang k k' st st' e e' S S') :
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
      (BSTEP_ : t_basic_ lang k k' st st' e e' S S') :
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
      (BSTEP_ : t_basic_ lang k k' st st' e None S S') :
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
      (BSTEP : t_basic e e' S S') :
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

Lemma step_wf e e' S S'
      (BSTEP : t_basic e e' S S')
      (ISTEP: t_ e e' S S') 
      (wfE: ES.Wf S) :
  ES.Wf S'.
Proof. Admitted.

(******************************************************************************)
(** ** seqn properties *)
(******************************************************************************)

Lemma basic_step_seqn_eq_dom e e' S S'
      (BSTEP : t_basic e e' S S') 
      (WF : ES.Wf S) :
  eq_dom (E S) (ES.seqn S') (ES.seqn S). 
Proof. 
  cdes BSTEP; cdes BSTEP_.
  red. intros x. ins.
  unfold ES.seqn.
  arewrite ((tid S') x = (tid S) x).
  { eapply basic_step_tid_eq_dom; eauto. }
  arewrite (sb S' ⨾ ⦗eq x⦘ ≡ sb S ⨾ ⦗eq x⦘).
  { rewrite SB'. relsf.
    rewrite !seq_eqv_cross_r.
    arewrite (eq x ∩₁ eq e ≡₁ ∅).
    { split; [|basic_solver].
      unfolder. ins. desf.
      red in SX. omega. }
    arewrite (eq x ∩₁ eq_opt e' ≡₁ ∅).
    { split; [|basic_solver].
      unfolder. ins. desf.
      unfold opt_ext in EEQ. desf.
      red in SX. omega. }
    basic_solver. }
  rewrite (dom_l WF.(ES.sbE)). rewrite !seqA.
  seq_rewrite <- !id_inter.
  arewrite ((Tid S' (tid S x)) ∩₁ E S ≡₁ (Tid S  (tid S x)) ∩₁ E S).
  { split.
    all: unfolder; ins; desf.
    all: splits; auto.
    all: rewrite <- H.
    symmetry.
    all: eapply basic_step_tid_eq_dom; eauto. }
  erewrite countNatP_lt_eq. done.
  { eapply basic_step_next_act_lt; eauto. }
  ins. apply dom_eqv1 in EE. apply EE. 
Qed.

Lemma basic_step_seqn_kinit thread lang k k' st st' e e' S S' 
      (kINIT : k = CInit thread)
      (BSTEP_ : t_basic_ lang k k' st st' e e' S S') 
      (WF : ES.Wf S) :
  ES.seqn S' e = 0. 
Proof.   
  cdes BSTEP_.
  unfold ES.seqn.
  arewrite (⦗Tid S' ((tid S') e)⦘ ⨾ sb S' ⨾ ⦗eq e⦘ ≡ ∅₂); 
    [|by rewrite dom_empty; apply countNatP_empty].
  split; [|basic_solver]. 
  rewrite SB', cross_union_r. relsf. 
  repeat apply inclusion_union_l.
  { step_solver. }
  2-3: destruct e'; by step_solver.
  rewrite seq_eqv_lr. 
  unfold ES.cont_sb_dom. 
  desf; red.
  intros x y [eqTID [CROSS EQy]]; desf.
  eapply ES.init_tid_K; eauto. 
  do 2 eexists; splits; eauto.  
  unfold ES.cont_thread.
  arewrite (thread = (tid S') (ES.next_act S)) .
  { etransitivity; [|erewrite basic_step_tid_e; eauto].  
    by unfold ES.cont_thread. }
  assert (Einit S' x) as INITx. 
  { eapply basic_step_acts_init_set; eauto.  
    { econstructor; eauto. }
    unfold cross_rel in CROSS; desf. } 
  arewrite (tid_init = (tid S') x); auto. 
  unfold ES.acts_init_set, set_inter in INITx; desf. 
Qed.

Lemma basic_step_seqn_kevent x lang k k' st st' e e' S S' 
      (kEVENT : k = CEvent x)
      (BSTEP_ : t_basic_ lang k k' st st' e e' S S') 
      (STEP_ : t_ e e' S S') 
      (WF : ES.Wf S) :
  ES.seqn S' e = 1 + ES.seqn S x. 
Proof.
  cdes BSTEP_.
  assert (t_basic e e' S S') as BSTEP. 
  { econstructor; eauto. }
  assert (ES.Wf S') as WF'.
  { eapply step_wf; eauto. }
  assert (E S x) as Ex. 
  { eapply ES.K_inE; eauto; desf; eapply CONT. }
  assert (ES.cont_sb_dom S k x) as KSBx. 
  { unfold ES.cont_sb_dom. desf. 
    unfold dom_rel. eexists. basic_solver. }
  arewrite (ES.seqn S x = ES.seqn S' x).
  { symmetry; eapply basic_step_seqn_eq_dom; eauto. }
  eapply ES.seqn_immsb; auto. 
  { unfold ES.same_tid.
    erewrite basic_step_tid_e with (e := e); eauto.  
    erewrite basic_step_tid_eq_dom; eauto.  
    unfold ES.cont_thread. desf. }
  eapply immediateE. 
  unfold minus_rel. 
  split. 
  { apply SB'. basic_solver. }
  red. intros [z [SBxz SBe]].
  assert (ES.cont_sb_dom S k z) as KSBz.
  { apply SB' in SBe.
    unfold union in SBe.
    destruct SBe as [[SB | kSB] | kSBe'].
    { exfalso. 
      eapply basic_step_acts_set_NE; eauto.  
      apply ES.sbE in SB; auto. 
      apply seq_eqv_lr in SB; desf. }
    { unfold cross_rel in kSB. 
      destruct kSB as [kSBz _].
      eapply kSBz. }
    unfold cross_rel in kSBe'.
    destruct kSBe' as [_ EQe].
    destruct e'; step_solver. } 
  eapply ES.cont_sb_nfrwd; 
    [ by apply WF | by eapply kEVENT | eauto | | by apply KSBz ].
  assert (E S z) as Ez. 
  { eapply ES.cont_sb_domE; eauto. }
  unfold codom_rel.
  eexists. apply seq_eqv_l. 
  split; eauto.
  eapply (basic_step_sb_restr BSTEP); auto. 
  by unfold restr_rel. 
Qed.  

Lemma basic_step_seqn_e' e e' S S' 
      (BSTEP : t_basic e (Some e') S S') 
      (STEP_ : t_ e (Some e') S S') 
      (WF : ES.Wf S) :
  ES.seqn S' e' = 1 + ES.seqn S' e. 
Proof.   
  cdes BSTEP; cdes BSTEP_.  
  assert (ES.Wf S') as WF'.
  { eapply step_wf; eauto. }
  assert (immediate (sb S') e e') as IMMSB. 
  { apply immediateE.
    unfold minus_rel, seq. 
    split. 
    { apply SB'. basic_solver. }
    red. intros [x [SBz SBz']].
    assert (x = e') as EQx. 
    { apply SB' in SBz.
      unfold union in SBz.
      destruct SBz as [[SB | SBK] | HH].
      { exfalso. 
        eapply ES.sbE in SB; auto.  
        apply seq_eqv_lr in SB.
        eapply basic_step_acts_set_NE; eauto.
        desf. }
      { exfalso. 
        eapply basic_step_acts_set_NE; eauto.
        unfold cross_rel in SBK.
        destruct SBK as [SBk _].
        eapply ES.cont_sb_domE; eauto. }
      unfold cross_rel, eq_opt in HH; desf. }
    eapply ES.sb_irr; [apply WF'|].
    subst x; eauto. } 
  eapply ES.seqn_immsb; eauto.  
  unfold ES.same_tid.
  erewrite basic_step_tid_e; [erewrite basic_step_tid_e'|]; eauto. 
Qed.

(******************************************************************************)
(** ** Load step properties *)
(******************************************************************************)

Lemma load_step_E e e' S S'
      (BSTEP : t_basic e e' S S')
      (LSTEP: t_load e e' S S') :
  E S' ≡₁ E S ∪₁ eq e.
Proof. 
  assert (e' = None) by inv LSTEP. subst.
    by apply basic_step_nupd_acts_set.
Qed.

Lemma load_step_R e e' S S'
      (LSTEP: t_load e e' S S') :
  R S' e.
Proof. apply LSTEP. Qed.

Lemma load_step_r e e' S S'
      (BSTEP : t_basic e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ R S' ≡₁ (E S ∩₁ R S) ∪₁ eq e.
Proof. 
  erewrite load_step_E; eauto.
  rewrite set_inter_union_l.
  arewrite (eq e ∩₁ R S' ≡₁ eq e).
  { generalize (load_step_R LSTEP).
    basic_solver. }
  arewrite (E S ∩₁ R S' ≡₁ E S ∩₁ R S). 2: done.
  eapply type_step_eq_dom; eauto.
Qed.  

Lemma load_step_w e e' S S'
      (BSTEP : t_basic e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ W S' ≡₁ E S ∩₁ W S.
Proof. 
  assert (R S' e) as AA.
  { eapply load_step_R; eauto. }
  erewrite load_step_E; eauto.
  rewrite set_inter_union_l.
  arewrite (E S ∩₁ W S' ≡₁ E S ∩₁ W S).
  { eapply type_step_eq_dom; eauto. }
  arewrite (eq e ∩₁ W S' ≡₁ ∅).
  { split; [|basic_solver].
    unfolder. ins. desf.
    type_solver. }
  basic_solver.
Qed.  

Lemma load_step_f e e' S S'
      (BSTEP : t_basic e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ F S' ≡₁ E S ∩₁ F S.
Proof. 
  assert (R S' e) as AA.
  { eapply load_step_R; eauto. }
  erewrite load_step_E; eauto.
  rewrite set_inter_union_l.
  arewrite (E S ∩₁ F S' ≡₁ E S ∩₁ F S).
  { eapply type_step_eq_dom; eauto. }
  arewrite (eq e ∩₁ F S' ≡₁ ∅).
  { split; [|basic_solver].
    unfolder. ins. desf.
    type_solver. }
  basic_solver.
Qed.

Lemma load_step_rel e e' S S'
      (BSTEP : t_basic e e' S S')
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
  unfolder. splits; intros x [xE HH].
  { erewrite basic_step_mod_eq_dom in HH; eauto. }
  erewrite <- basic_step_mod_eq_dom in HH; eauto. 
Qed.

Lemma load_step_acq e e' S S'
      (BSTEP : t_basic e e' S S')
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
  unfolder; splits; intros x [[xE xFR] HH].
  { erewrite basic_step_mod_eq_dom in HH; eauto. }
  erewrite <- basic_step_mod_eq_dom in HH; eauto.
Qed.  

Lemma load_step_jf_dom e e' S S'
      (BSTEP : t_basic e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) : 
  dom_rel (jf S') ⊆₁ E S.
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite JF', dom_union. 
  apply set_subset_union_l.
  rewrite wfE.(ES.jfE).
  basic_solver.
Qed.

Lemma load_step_jfe_dom e e' S S'
      (BSTEP : t_basic e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) : 
  dom_rel (jfe S') ⊆₁ E S.
Proof. 
  unfold ES.jfe.
  unfolder; ins; desf.
  eapply load_step_jf_dom; eauto. 
  basic_solver.
Qed.  

Lemma load_step_jfe e e' S S'
      (BSTEP : t_basic e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) : 
  jfe S' ≡ jfe S ∪ jfe S' ⨾ ⦗eq e⦘.
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  unfold ES.jfe.
  erewrite basic_step_nupd_sb. 
  2 : { desf; eauto. }
  rewrite <- EVENT.
  rewrite JF'.
  rewrite minus_union_l at 1.
  apply union_more.
  { rewrite ES.sbE, ES.jfE; auto. 
    rewrite minus_union_r. 
    erewrite minus_disjoint with (r' := ES.cont_sb_dom S k × eq e). 
    2 : { unfolder; splits; ins; desf; omega. }
    basic_solver. }
  rewrite <- seq_eqv_minus_lr, seq_union_l. 
  arewrite (jf S ⨾ ⦗eq e⦘ ≡ ∅₂). 
  { rewrite wfE.(ES.jfE).
    unfolder; splits; ins; desf; omega. }
  basic_solver 10.
Qed.

Lemma load_step_sb_jf  lang k k' st st' e e' S S'
      (BSTEP_ : t_basic_ lang k k' st st' e e' S S') 
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  (sb S' ∪ jf S')＊ ≡ (sb S ∪ jf S)＊ ⨾ (ES.cont_sb_dom S k × eq e ∪ jf S' ⨾ ⦗eq e⦘)^?. 
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP_.
  assert (t_basic e e' S S') as BSTEP.
  { econstructor. eauto. }
  erewrite basic_step_nupd_sb. 
  2 : { desf; eauto. }
  rewrite <- EVENT.
  rewrite JF'.
  arewrite 
    ( sb S ∪ ES.cont_sb_dom S k × eq e ∪ (jf S ∪ singl_rel w e) ≡
     (ES.cont_sb_dom S k × eq e ∪ singl_rel w e) ∪ (sb S ∪ jf S))
    by basic_solver. 
  erewrite clos_refl_trans_union_ext with (r' := sb S ∪ jf S).
  { arewrite 
      ((jf S ∪ singl_rel w e) ⨾ ⦗eq e⦘ ≡ singl_rel w e).
    { rewrite seq_union_l. 
      arewrite (jf S ⨾ ⦗eq e⦘ ≡ ∅₂). 
      { rewrite wfE.(ES.jfE).
        unfolder; splits; ins; desf; omega. }
      basic_solver. }
    basic_solver. }
  all : split; [|basic_solver].
  all : erewrite ES.cont_sb_domE; eauto. 
  all : arewrite (singl_rel w e ⊆ E S × eq e); [basic_solver|].
  all : relsf.
  2 : rewrite wfE.(ES.sbE); rewrite wfE.(ES.jfE).
  all : unfolder; splits; ins; desf; omega.
Qed.

Lemma load_step_rf e e' S S'
      (BSTEP : t_basic e e' S S')
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
    rewrite !seqA.
    split; [|done]. step_solver. }
  arewrite (singl_rel w e ⨾ ⦗eq e⦘ ≡ singl_rel w e); 
    basic_solver 10.
Admitted.

Lemma load_step_rf_rmw e e' S S'
      (BSTEP : t_basic e e' S S')
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
      unfolder; ins; splits; desf; omega. }
  rewrite union_false_r.
  admit.
Admitted.

Lemma load_step_cc lang k k' st st' e e' S S'
      (BSTEP_ : t_basic_ lang k k' st st' e e' S S') 
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  cc S' ≡ cc S ∪ 
     ES.cont_cf_dom S k × eq e ∩ 
     (jfe S ⨾ (sb S ∪ jf S)＊ ⨾ (jfe S ⨾ ES.cont_sb_dom S k × eq e ∪ jfe S')). 
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP_.
  assert (t_basic e e' S S') as BSTEP.
  { econstructor. eauto. }
  unfold cc. 
  erewrite load_step_sb_jf; eauto. 
  erewrite basic_step_nupd_sb with (S' := S'). 
  2 : { desf; eauto. }
  erewrite basic_step_nupd_cf; eauto. 
  2 : { desf; eauto. }
  rewrite <- EVENT.
  rewrite <- seqA with (r2 := jfe S').
  arewrite
    (((sb S ∪ jf S)＊ ⨾ (ES.cont_sb_dom S k × eq e ∪ jf S' ⨾ ⦗eq e⦘)^?) ⨾ jfe S' ≡
     (sb S ∪ jf S)＊ ⨾ jfe S'). 
  { rewrite seqA, crE, !seq_union_l, !seq_union_r, seq_id_l.
    arewrite (ES.cont_sb_dom S k × eq e ⨾ jfe S' ≡ ∅₂). 
    { apply seq_codom_dom_inter.
      split; [|basic_solver].
      erewrite load_step_jfe_dom; eauto. 
      unfolder; splits; ins; desf; omega. }
    arewrite (⦗eq e⦘ ⨾ jfe S' ≡ ∅₂).
    { apply seq_codom_dom_inter.
      split; [|basic_solver].
      erewrite load_step_jfe_dom; eauto. 
      unfolder; splits; ins; desf; omega. }
    basic_solver 10. }
  arewrite (jfe S' ⨾ (sb S ∪ jf S)＊ ⨾ jfe S' ≡ jfe S ⨾ (sb S ∪ jf S)＊ ⨾ jfe S').
  { rewrite <- cr_of_ct, crE, seq_union_l, seq_union_r, seq_id_l.
    arewrite (jfe S' ⨾ jfe S' ≡ ∅₂).
    { erewrite load_step_jfe; eauto. 
      relsf. split; [|basic_solver].
      repeat apply inclusion_union_l.
      { rewrite wfE.(ES.jfeD).
        type_solver. }
      { rewrite wfE.(ES.jfeE).
        unfolder; splits; ins; desf; omega. }
      { unfold ES.jfe. 
        rewrite JF', <- seq_eqv_minus_lr. 
        rewrite wfE.(ES.jfE), wfE.(ES.jfD).
        assert (is_w (lab S) w) as WW'. 
        { eapply type_step_eq_dom with (S' := S'); eauto. done. }
        unfolder; splits; ins; desf; [omega | type_solver]. } 
      rewrite seqA. 
      rewrite <- seqA with (r2 := jfe S').
      arewrite (⦗eq e⦘ ⨾ jfe S' ⊆ ∅₂); [|basic_solver].
      apply seq_codom_dom_inter.
      split; [|basic_solver].
      erewrite load_step_jfe_dom; eauto. 
      unfolder; splits; ins; desf; omega. }
    rewrite union_false_l.
    rewrite seq_union_r. 
    arewrite (jfe S ⨾ jfe S' ≡ ∅₂).
    { erewrite load_step_jfe with (S' := S'); eauto. 
      relsf. split; [|basic_solver].
      repeat apply inclusion_union_l.
      { rewrite wfE.(ES.jfeD).
        type_solver. }
      unfold ES.jfe. 
      rewrite JF', <- seq_eqv_minus_lr. 
      rewrite wfE.(ES.jfE), wfE.(ES.jfD).
      assert (is_w (lab S) w) as WW'. 
      { eapply type_step_eq_dom with (S' := S'); eauto. done. }
      unfolder; splits; ins; desf; [omega | type_solver]. }  
    rewrite union_false_l, <- !seqA. 
    apply seq_more; auto. 
    erewrite load_step_jfe with (S' := S'); eauto. 
    rewrite seq_union_l. 
    arewrite ((jfe S' ⨾ ⦗eq e⦘) ⨾ tc (sb S ∪ jf S) ≡ ∅₂). 
    { split; [|basic_solver].
      rewrite wfE.(ES.sbE), wfE.(ES.jfE), <- !restr_relE, <- restr_union.
      rewrite restr_ct.
      unfolder; splits; ins; desf; omega. }
    basic_solver. }
  rewrite crE, !seq_union_r, seq_id_r.
  rewrite inter_union_l. 
  apply union_more.
  { rewrite !inter_union_r. 
    arewrite 
      (cf S ∩ (jfe S ⨾ (sb S ∪ jf S)＊ ⨾ jfe S' ⨾ ES.cont_sb_dom S k × eq e) ≡ ∅₂). 
    { split; [|basic_solver].
      rewrite ES.cfE.
      unfolder; splits; ins; desf; omega. }
     arewrite (jfe S' ⨾ sb S ≡ jfe S ⨾ sb S).
    { erewrite load_step_jfe with (S' := S'); eauto. 
      rewrite seq_union_l, seqA.
      arewrite (jfe S' ⨾ ⦗eq e⦘ ⨾ sb S ≡ ∅₂). 
      { split; [|basic_solver].
        rewrite wfE.(ES.sbE).
        unfolder; splits; ins; desf; omega. }
      basic_solver. }
    arewrite (cf S ∩ (jfe S ⨾ (sb S ∪ jf S)＊ ⨾ jfe S') ≡ 
              cf S ∩ (jfe S ⨾ (sb S ∪ jf S)＊ ⨾ jfe S )). 
    { erewrite load_step_jfe with (S' := S'); eauto. 
      rewrite !seq_union_r, inter_union_r. 
      arewrite (cf S ∩ (jfe S ⨾ (sb S ∪ jf S)＊ ⨾ jfe S' ⨾ ⦗eq e⦘) ≡ ∅₂).  
      { split; [|basic_solver].
        rewrite ES.cfE.
        unfolder; splits; ins; desf; omega. }
      basic_solver 42. }
    basic_solver 42. }
  rewrite csE, transp_cross, inter_union_l.
  arewrite (
      eq e × ES.cont_cf_dom S k
         ∩ (jfe S ⨾ (sb S ∪ jf S)＊ ⨾ jfe S'
                ∪ (jfe S ⨾ (sb S ∪ jf S)＊ ⨾ jfe S' ⨾ sb S
                ∪ jfe S ⨾ (sb S ∪ jf S)＊ ⨾ jfe S' ⨾ ES.cont_sb_dom S k × eq e)) 
    ≡ ∅₂).
  { rewrite wfE.(ES.jfeE).
    split; [|basic_solver].
    intros x y [[EQx _] HH].   
    assert (E S x) as Ex.  
    { unfolder in HH. desf. }
    eapply basic_step_acts_set_NE; eauto. desf. }
  rewrite union_false_r, !inter_union_r.
  arewrite (ES.cont_cf_dom S k × eq e ∩ (jfe S ⨾ (sb S ∪ jf S)＊ ⨾ jfe S' ⨾ sb S) ≡ ∅₂). 
  { split; [|basic_solver].
    rewrite wfE.(ES.sbE). 
    unfolder; splits; ins; desf; omega. }
  arewrite (jfe S' ⨾ ES.cont_sb_dom S k × eq e ≡ jfe S ⨾ ES.cont_sb_dom S k × eq e). 
  { erewrite load_step_jfe with (S' := S'); eauto. 
    rewrite seq_union_l. 
    arewrite ((jfe S' ⨾ ⦗eq e⦘) ⨾ ES.cont_sb_dom S k × eq e ≡ ∅₂).
    { split; [|basic_solver].
      erewrite ES.cont_sb_domE; eauto. 
      unfolder; splits; ins; desf; omega. }
    basic_solver 10. }
  basic_solver 16.
Qed.    

Lemma load_step_cc_seqE e e' S S' 
      (BSTEP : t_basic e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) : 
  cc S' ⨾ ⦗E S⦘ ≡ cc S.
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite load_step_cc; eauto. 
  rewrite seq_union_l. 
  rewrite <- lib.AuxRel.seq_eqv_inter_lr.
  arewrite (ES.cont_cf_dom S k × eq e ⨾ ⦗E S⦘ ≡ ∅₂). 
  { split; [|basic_solver].
    unfolder; splits; ins; desf; omega. }
  rewrite ccE. basic_solver 10.
Qed.

Lemma load_step_vis_mon e e' S S'
      (BSTEP : t_basic e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) : 
  vis S ⊆₁ vis S'. 
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  unfold vis. 
  intros x VIS.
  splits; desf.
  { eapply basic_step_acts_set_mon; eauto. }
  arewrite (eq x ⊆₁ E S ∩₁ eq x) by basic_solver.
  unfold set_inter. rewrite <- seq_eqv.
  rewrite <- seqA.
  erewrite load_step_cc_seqE; eauto. 
  rewrite EW'.
  etransitivity; eauto.  
  apply seq_mori; [done|]. 
  apply clos_refl_sym_mori. 
  eapply basic_step_sb_mon; eauto.  
Qed.
  
Lemma load_step_rs e e' S S' 
      (BSTEP : t_basic e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  rs S' ≡ rs S.
Proof.
  assert (e' = None) by inv LSTEP. subst.
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  assert (ES.Wf S') as wfE'.
  { eapply step_wf; unfold t_; eauto. }
  rewrite !rs_alt; auto.
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
    unfolder; unfold set_subset; splits; ins; desf; omega. }
  arewrite (restr_rel (E S ∩₁ W S) (same_loc S') ≡ restr_rel (E S ∩₁ W S) (same_loc S)).
  2: basic_solver 21.
  do 2 rewrite <- restr_restr.
  apply restr_rel_more; auto.
  rewrite <- basic_step_same_loc_restr; eauto.
Qed.

Lemma load_step_release e e' S S' 
      (BSTEP : t_basic e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  release S' ≡ release S. 
Proof. 
  assert (e' = None) by inv LSTEP. subst.
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.  
  assert (ES.Wf S') as wfE'.
  { eapply step_wf; unfold t_; eauto. }
  rewrite !release_alt; auto.
  rewrite basic_step_nupd_sb, load_step_rel, load_step_f, load_step_rs; eauto.
  do 2 rewrite crE.
  relsf.
  apply union_more; auto.
  rewrite !seqA.
  arewrite (ES.cont_sb_dom S k × eq e ⨾ rs S ≡ ∅₂); 
    [|basic_solver 10].
  rewrite rsE; auto.
  arewrite (ES.cont_sb_dom S k × eq e ⨾ ⦗E S⦘ ≡ ∅₂); 
    [ split; [|done]; step_solver | basic_solver ].
Qed.

Lemma load_step_sw e e' S S' 
      (BSTEP : t_basic e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  sw S' ≡ sw S ∪ release S ⨾ rf S' ⨾ ⦗Acq S'⦘ ⨾ ⦗eq e⦘. 
Proof.
  assert (e' = None) by inv LSTEP. subst.
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.  
  assert (ES.Wf S') as wfE'.
  { eapply step_wf; unfold t_; eauto. }
  rewrite !sw_alt; auto.
  rewrite 
    load_step_release, load_step_rf, load_step_f, load_step_acq,
    basic_step_nupd_sb;
    eauto.
  rewrite id_union.
  rewrite !crE.
  relsf.
  rewrite !unionA.
  apply union_more; auto.
  apply union_more; auto.
  arewrite (ES.cont_sb_dom S k × eq e ⨾ ⦗E S ∩₁ F S⦘ ≡ ∅₂) 
    by split; [|done]; step_solver.
  arewrite (⦗E S ∩₁ F S⦘ ⨾ ⦗eq e ∩₁ Acq S'⦘ ≡ ∅₂) 
    by split; [|done]; step_solver.
  rewrite <- (seqA ((jf S' ⨾ ⦗eq e⦘ ∪ ew S ⨾ jf S' ⨾ ⦗eq e⦘) \ cf S')).
  arewrite 
    (((jf S' ⨾ ⦗eq e⦘ ∪ ew S ⨾ jf S' ⨾ ⦗eq e⦘) \ cf S') ⨾ sb S ≡ ∅₂) 
    by split; [|done]; step_solver.
  relsf.
  rewrite id_union, seq_union_r.
  arewrite 
    (((jf S' ⨾ ⦗eq e⦘ ∪ ew S ⨾ jf S' ⨾ ⦗eq e⦘) \ cf S') ⨾ ⦗E S ∩₁ F S ∩₁ Acq S⦘ ≡ ∅₂) 
    by split; [|done]; step_solver.
  arewrite 
    (((jf S' ⨾ ⦗eq e⦘ ∪ ew S ⨾ jf S' ⨾ ⦗eq e⦘) \ cf S') ⨾ ⦗E S ∩₁ R S ∩₁ Acq S⦘ ≡ ∅₂) 
    by split; [|done]; step_solver.
  basic_solver 42.
Qed.

Lemma load_step_hb lang k k' st st' e e' S S' 
      (BSTEP_ : t_basic_ lang k k' st st' e e' S S') 
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  hb S' ≡ hb S ∪ 
     (hb S)^? ⨾ (ES.cont_sb_dom S k × eq e ∪ release S ⨾ rf S' ⨾ ⦗Acq S'⦘ ⨾ ⦗eq e⦘). 
Proof.
  assert (e' = None) by inv LSTEP. subst.
  assert (t_basic e None S S') as BSTEP.
  { econstructor. eauto. }
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
  all : split; [|done].
  all : rewrite load_step_rf; eauto.
  all : rewrite basic_step_cf; eauto.
  all : rewrite JF'.
  all : relsf; unionL.
  all : by step_solver.
Qed.

Lemma load_step_hb_dom e e' S S'
      (BSTEP : t_basic e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) : 
  dom_rel (hb S') ⊆₁ E S.
Proof. 
  cdes BSTEP. cdes BSTEP_. cdes LSTEP. cdes AJF.
  rewrite load_step_hb; eauto.
  rewrite releaseE, hbE; auto.
  rewrite ES.cont_sb_domE; eauto.
  basic_solver.
Qed.  

Lemma load_step_hb_seq_E e e' S S' 
      (BSTEP : t_basic e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  hb S' ⨾ ⦗E S⦘ ≡ hb S.
Proof. 
  cdes BSTEP. cdes BSTEP_. cdes LSTEP. cdes AJF.
  rewrite load_step_hb; eauto.
  rewrite seq_union_l, !seqA.
  arewrite (
      (ES.cont_sb_dom S k × eq e ∪ release S ⨾ rf S' ⨾ ⦗Acq S'⦘ ⨾ ⦗eq e⦘) ⨾ ⦗E S⦘ ≡ ∅₂
  ). 
 { split; [|done]. 
   rewrite load_step_rf; eauto.
   rewrite basic_step_cf; eauto.
   rewrite JF'.
   step_solver. }
  rewrite hbE; auto.
  basic_solver 20.
Qed.

End ESstep.