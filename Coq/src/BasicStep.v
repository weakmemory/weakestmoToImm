Require Import Omega.
From PromisingLib Require Import Language.
From hahn Require Import Hahn.
From imm Require Import Events. 
Require Import AuxRel.
Require Import AuxDef.
Require Import EventStructure.
Require Import Consistency.

Set Implicit Arguments.

Section BasicStep.

Notation "'E' S" := S.(ES.acts_set) (at level 10).
Notation "'Einit' S"  := S.(ES.acts_init_set) (at level 10).
Notation "'Eninit' S" := S.(ES.acts_ninit_set) (at level 10).

Notation "'tid' S" := S.(ES.tid) (at level 10).
Notation "'lab' S" := S.(ES.lab) (at level 10).
Notation "'loc' S" := (Events.loc S.(ES.lab)) (at level 10).
Notation "'val' S" := (Events.val S.(ES.lab)) (at level 10).
Notation "'mod' S" := (Events.mod S.(ES.lab)) (at level 10).

Notation "'sb' S" := S.(ES.sb) (at level 10).
Notation "'rmw' S" := S.(ES.rmw) (at level 10).
Notation "'ew' S" := S.(ES.ew) (at level 10).
Notation "'jf' S" := S.(ES.jf) (at level 10).
Notation "'rf' S" := S.(ES.rf) (at level 10).
Notation "'co' S" := S.(ES.co) (at level 10).
Notation "'cf' S" := S.(ES.cf) (at level 10).
Notation "'icf' S" := S.(ES.icf) (at level 10).

Notation "'jfe' S" := S.(ES.jfe) (at level 10).
Notation "'rfe' S" := S.(ES.rfe) (at level 10).
Notation "'coe' S" := S.(ES.coe) (at level 10).
Notation "'jfi' S" := S.(ES.jfi) (at level 10).
Notation "'rfi' S" := S.(ES.rfi) (at level 10).
Notation "'coi' S" := S.(ES.coi) (at level 10).

Notation "'R' S" := (fun a => is_true (is_r S.(ES.lab) a)) (at level 10).
Notation "'R_ex' S" := (fun a => is_true (R_ex S.(ES.lab) a)) (at level 10).
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
Notation "'same_lab' S" := (ES.same_lab S) (at level 10).
Notation "'same_mod' S" := (same_mod S.(ES.lab)) (at level 10).
Notation "'same_loc' S" := (same_loc S.(ES.lab)) (at level 10).
Notation "'same_val' S" := (same_val S.(ES.lab)) (at level 10).

Notation "'K' S" := (S.(ES.cont_set)) (at level 10).

Notation "'Tid_' S" := (fun t e => S.(ES.tid) e = t) (at level 1).
Notation "'Mod_' S" := (fun m x => mod S x = m) (at level 1).
Notation "'Loc_' S" := (fun l x => loc S x = l) (at level 1).
Notation "'Val_' S" := (fun v e => val S e = v) (at level 1).

Definition sb_delta S k e e' : relation eventid := 
  ES.cont_sb_dom S k × eq e ∪ ES.cont_sb_dom S k × eq_opt e' ∪ eq e × eq_opt e'.

Definition imm_sb_delta S k e e' : relation eventid := 
  ES.cont_last S k × eq e ∪ eq e × eq_opt e'. 

Definition rmw_delta e e' : relation eventid := 
  eq e × eq_opt e'.

Definition cf_delta S k e e' : relation eventid := 
  (ES.cont_cf_dom S k × eq e)^⋈ ∪ (ES.cont_cf_dom S k × eq_opt e')^⋈.

Definition icf_delta S k e : relation eventid := 
  (ES.cont_icf_dom S k × eq e)^⋈.

Hint Unfold sb_delta imm_sb_delta rmw_delta cf_delta icf_delta : ESStepDb.

Definition basic_step_
           (lang : Language.t (list label))
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

Definition basic_step
           (e  : eventid)
           (e' : option eventid)
           (S S' : ES.t) : Prop :=
  exists lang k k' st st', 
    ⟪ BSTEP_ : basic_step_ lang k k' st st' e e' S S' ⟫.

(******************************************************************************)
(** ** Some useful tactics *)
(******************************************************************************)

(* tries to solve goals like `sb ⨾ ⦗eq e⦘ ⊆ ∅₂`,
   where `e` is a new event added by step `S -> S'`,
   using the fact that `sb ≡ ⦗E⦘ ⨾ sb ⨾ ⦗E⦘` *)
Ltac step_solver := 
  repeat autounfold with ESStepDb in *; 
  unfold eq_opt, opt_ext in *; 
  rewrite 1?ES.sbE, 1?ES.rmwE, 1?ES.cfE, 
    1?ES.cont_sb_domE, 1?ES.cont_cf_domE,
    1?ES.jfE, 1?ES.jfiE, 1?ES.jfeE,
    1?ES.rfE, 1?ES.coE, 1?ES.ewE, 
    1?rsE, 1?releaseE, 1?swE, 1?hbE;
  unfold ES.acts_ninit_set, ES.acts_init_set, ES.acts_set in *;
  eauto; unfolder; ins; splits; desf; omega.

(******************************************************************************)
(** ** basic_step : `E` properties *)
(******************************************************************************)

Lemma basic_step_next_act_lt e e' S S'
      (BSTEP : basic_step e e' S S') :
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
      (BSTEP : basic_step e e' S S') :
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
      (BSTEP : basic_step e None S S') :
  E S' ≡₁ E S ∪₁ eq e.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  apply basic_step_acts_set in BSTEP.
  unfold eq_opt in BSTEP.
  by rewrite set_union_empty_r in BSTEP.
Qed.

Lemma basic_step_nupd_acts_mon e e' S S'  
      (BSTEP : basic_step e e' S S') :
  E S ⊆₁ E S'.
Proof. 
  rewrite basic_step_acts_set with (S' := S'); eauto. 
  basic_solver. 
Qed.

Lemma basic_step_acts_set_ne e e' S S'  
      (BSTEP : basic_step e e' S S') :
  ~ E S e.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold not, ES.acts_set; ins; omega.
Qed.

Lemma basic_step_acts_set_ne' e e' S S'  
      (BSTEP : basic_step e (Some e') S S') :
  ~ E S e'.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold not, ES.acts_set; ins; omega. 
Qed.

Lemma basic_step_acts_set_mon e e' S S' 
      (BSTEP : basic_step e e' S S') :
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
      (BSTEP : basic_step e e' S S')
      (wfE: ES.Wf S) :
  Eninit S' e.
Proof.
  cdes BSTEP; cdes BSTEP_.
  split.
  { desf. red. rewrite EVENT'. unfold opt_ext in *. desf. omega. }
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
      (BSTEP : basic_step e (Some e') S S')
      (wfE: ES.Wf S) :
  Eninit S' e'.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  split.
  { desf. red. rewrite EVENT'. unfold opt_ext in *. desf. }
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
      (BSTEP : basic_step e e' S S') :
  ⟪ TIDEQ : eq_dom (E S) (tid S') (tid S) ⟫ /\
  ⟪ LABEQ : eq_dom (E S) (lab S') (lab S) ⟫.
Proof.
  cdes BSTEP. cdes BSTEP_.
  rewrite TID', LAB'. unnw. unfold eq_dom.
  splits; ins; desf.
  all: unfold upd_opt.
  all: assert (x <> ES.next_act S) as HH by (red in DX; omega).
  all: unfold opt_ext in *.
  all: desf; rewrite updo; auto; [|red in DX; omega].
  all: rewrite updo; auto.
Qed.

(******************************************************************************)
(** ** basic_step : `tid` properties *)
(******************************************************************************)

Lemma basic_step_tid_eq_dom  e e' S S'
      (BSTEP : basic_step e e' S S') :
  eq_dom (E S) (tid S') (tid S).
Proof. eapply basic_step_tidlab_eq_dom; eauto. Qed.

Lemma basic_step_same_tid_restr e e' S S'  
      (BSTEP : basic_step e e' S S') :
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
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') :
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
      (BSTEP_ : basic_step_ lang k k' st st' e (Some e') S S') :
  tid S' e' = ES.cont_thread S k. 
Proof. 
  cdes BSTEP_.
  edestruct k;
    rewrite TID';
    unfold upd_opt, ES.cont_thread;
    by rewrite upds.
Qed.

(******************************************************************************)
(** ** basic_step : `Einit/Eninit` properties *)
(******************************************************************************)

Lemma basic_step_acts_init_set e e' S S' 
      (BSTEP : basic_step e e' S S')
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
    unfold ES.acts_init_set, ES.acts_set.
    unfolder; splits; desf.
    destruct e'; rewrite EVENT'; unfold opt_ext in *; omega. }
  arewrite (eq_opt e' ∩₁ (fun x : nat => (tid S') x = tid_init) ≡₁ ∅). 
  { edestruct e'. 
    { apply set_disjointE; unfold set_disjoint; ins.
      eapply basic_step_acts_ninit_set_e'; eauto.
      unfold ES.acts_init_set, ES.acts_set.  
      unfolder; splits; desf; omega. }
    unfold eq_opt. apply set_inter_empty_l. }
  relsf.
  unfolder. unfold set_subset. splits; ins; splits; desf. 
  { erewrite <- basic_step_tid_eq_dom; eauto. }
  erewrite basic_step_tid_eq_dom; eauto.
Qed.

Lemma basic_step_acts_ninit_set e e' S S' 
      (BSTEP : basic_step e e' S S')
      (wfE: ES.Wf S) :
  Eninit S' ≡₁ Eninit S ∪₁ eq e ∪₁ eq_opt e'.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold ES.acts_ninit_set.
  rewrite basic_step_acts_set, basic_step_acts_init_set; eauto.
  rewrite !set_minus_union_l.
  repeat apply set_union_Propere; auto. 
  { unfold ES.acts_init_set, ES.acts_set.
    unfolder; splits; ins; splits; desf. 
    red; ins; desf; omega. }
  edestruct e'. 
  { unfold ES.acts_init_set, ES.acts_set.
    unfolder. splits; ins; splits; desf. 
    red. ins; desf; omega. }
  unfold eq_opt; basic_solver. 
Qed.

(******************************************************************************)
(** ** basic_step : `lab` properties *)
(******************************************************************************)

Lemma basic_step_lab_eq_dom  e e' S S'
      (BSTEP : basic_step e e' S S') :
  eq_dom (E S) (lab S') (lab S).
Proof. eapply basic_step_tidlab_eq_dom; eauto. Qed.

Lemma basic_step_loc_eq_dom  e e' S S'
      (BSTEP : basic_step e e' S S') :
  eq_dom (E S) (loc S') (loc S).
Proof.
  unfold Events.loc. red. ins.
  arewrite ((lab S') x = (lab S) x); auto. 
  eapply basic_step_lab_eq_dom; eauto.
Qed.

Lemma basic_step_val_eq_dom  e e' S S'
      (BSTEP : basic_step e e' S S') :
  eq_dom (E S) (val S') (val S).
Proof.
  unfold Events.val. red. ins.
  arewrite ((lab S') x = (lab S) x); auto. 
  eapply basic_step_lab_eq_dom; eauto.
Qed.

Lemma basic_step_mod_eq_dom e e' S S' 
      (BSTEP : basic_step e e' S S') :
  eq_dom S.(ES.acts_set) (mod S') (mod S).
Proof. 
  unfold eq_dom, Events.mod, ES.acts_set.
  ins; erewrite basic_step_lab_eq_dom; eauto. 
Qed.

Lemma basic_step_same_mod_restr e e' S S' 
      (BSTEP : basic_step e e' S S') :
  restr_rel (E S) (same_mod S') ≡ restr_rel (E S) (same_mod S).
Proof. 
  unfolder. 
  unfold ES.same_tid.
  splits; ins; desf; splits; auto; red.
  erewrite <- basic_step_mod_eq_dom; eauto.
  2: erewrite basic_step_mod_eq_dom; eauto; symmetry.
  all: rewrite H; eapply basic_step_mod_eq_dom; eauto. 
Qed.

Lemma basic_step_same_loc_restr e e' S S' 
      (BSTEP : basic_step e e' S S') :
  restr_rel (E S) (same_loc S') ≡ restr_rel (E S) (same_loc S).
Proof. 
  unfolder. 
  unfold ES.same_tid.
  splits; ins; desf; splits; auto; red.
  erewrite <- basic_step_loc_eq_dom; eauto.
  2: erewrite basic_step_loc_eq_dom; eauto; symmetry.
  all: rewrite H; eapply basic_step_loc_eq_dom; eauto. 
Qed.

Lemma basic_step_same_val_restr e e' S S' 
      (BSTEP : basic_step e e' S S') :
  restr_rel (E S) (same_val S') ≡ restr_rel (E S) (same_val S).
Proof. 
  unfolder. 
  unfold ES.same_tid.
  splits; ins; desf; splits; auto; red.
  erewrite <- basic_step_val_eq_dom; eauto.
  2: erewrite basic_step_val_eq_dom; eauto; symmetry.
  all: rewrite H; eapply basic_step_val_eq_dom; eauto. 
Qed.

(*******************************************************)
(* Lemmas about equality of types and modes of events  *)
(* after a basic step.                                 *)
(*******************************************************)

Hint Unfold eq_dom Events.loc Events.val Events.mod Events.xmod 
     is_r is_w is_f is_acq is_rel is_rlx is_acqrel Events.R_ex
     is_only_pln is_sc is_ra is_xacq
     same_lab_u2v_dom same_label_u2v :
  same_lab_unfoldDb.

Ltac basic_step_same_lab S S' :=
  repeat autounfold with same_lab_unfoldDb;
  intros x [EX REL];
  assert (ES.lab S' x = ES.lab S x) as HH;
  [eapply basic_step_lab_eq_dom; eauto |
    try (by rewrite HH in REL);
    try (by rewrite <- HH in REL)].

Lemma basic_step_mod_in_mod e e' S S'
      (BSTEP : basic_step e e' S S') :
  forall m, E S ∩₁ Mod_ S' m ⊆₁ Mod_ S m.
Proof. ins. basic_step_same_lab S S'. Qed.

Lemma basic_step_loc_in_loc e e' S S'
      (BSTEP : basic_step e e' S S') :
  forall l, E S ∩₁ Loc_ S' l ⊆₁ Loc_ S l.
Proof. ins. basic_step_same_lab S S'. Qed.

Lemma basic_step_val_in_val e e' S S'
      (BSTEP : basic_step e e' S S') :
  forall v, E S ∩₁ Val_ S' v ⊆₁ Val_ S v.
Proof. ins. basic_step_same_lab S S'. Qed.

Lemma basic_step_rel_in_rel e e' S S'
      (BSTEP : basic_step e e' S S') :
  E S ∩₁ Rel S' ⊆₁ Rel S.
Proof. basic_step_same_lab S S'. Qed.

Lemma basic_step_acq_in_acq e e' S S'
      (BSTEP : basic_step e e' S S') :
  E S ∩₁ Acq S' ⊆₁ Acq S.
Proof. basic_step_same_lab S S'. Qed.

Lemma basic_step_sc_in_sc e e' S S'
      (BSTEP : basic_step e e' S S') :
  E S ∩₁ Sc S' ⊆₁ Sc S.
Proof. basic_step_same_lab S S'. Qed.

Lemma basic_step_r_in_r e e' S S'
      (BSTEP : basic_step e e' S S') :
  E S ∩₁ R S' ⊆₁ R S.
Proof. basic_step_same_lab S S'. Qed.

Lemma basic_step_w_in_w e e' S S'
      (BSTEP : basic_step e e' S S') :
  E S ∩₁ W S' ⊆₁ W S.
Proof. basic_step_same_lab S S'. Qed.

Lemma basic_step_f_in_f e e' S S'
      (BSTEP : basic_step e e' S S') :
  E S ∩₁ F S' ⊆₁ F S.
Proof. basic_step_same_lab S S'. Qed.

Lemma basic_step_rel_eq_rel e e' S S'
      (BSTEP : basic_step e e' S S') :
  E S ∩₁ Rel S' ≡₁ E S ∩₁ Rel S.
Proof. split; basic_step_same_lab S S'. Qed.

Lemma basic_step_acq_eq_acq e e' S S'
      (BSTEP : basic_step e e' S S') :
  E S ∩₁ Acq S' ≡₁ E S ∩₁ Acq S.
Proof. split; basic_step_same_lab S S'. Qed.

Lemma basic_step_sc_eq_sc e e' S S'
      (BSTEP : basic_step e e' S S') :
  E S ∩₁ Sc S' ≡₁ E S ∩₁ Sc S.
Proof. split; basic_step_same_lab S S'. Qed.

Lemma basic_step_r_eq_r e e' S S'
      (BSTEP : basic_step e e' S S') :
  E S ∩₁ R S' ≡₁ E S ∩₁ R S.
Proof. split; basic_step_same_lab S S'. Qed.

Lemma basic_step_r_ex_eq_r_ex e e' S S'
      (BSTEP : basic_step e e' S S') :
  E S ∩₁ R_ex S' ≡₁ E S ∩₁ R_ex S.
Proof. split; basic_step_same_lab S S'. Qed.

Lemma basic_step_w_eq_w e e' S S'
      (BSTEP : basic_step e e' S S') :
  E S ∩₁ W S' ≡₁ E S ∩₁ W S.
Proof. split; basic_step_same_lab S S'. Qed.

Lemma basic_step_f_eq_f e e' S S'
      (BSTEP : basic_step e e' S S') :
  E S ∩₁ F S' ≡₁ E S ∩₁ F S.
Proof. split; basic_step_same_lab S S'. Qed.

Lemma basic_step_fr_eq_fr e e' S S'
      (BSTEP : basic_step e e' S S') :
  E S ∩₁ FR S' ≡₁ E S ∩₁ FR S.
Proof. 
  rewrite !set_inter_union_r.
  erewrite basic_step_f_eq_f; eauto. 
  erewrite basic_step_r_eq_r; eauto. 
Qed.

Lemma basic_step_fw_eq_fw e e' S S'
      (BSTEP : basic_step e e' S S') :
  E S ∩₁ FW S' ≡₁ E S ∩₁ FW S.
Proof. 
  rewrite !set_inter_union_r.
  erewrite basic_step_f_eq_f; eauto. 
  erewrite basic_step_w_eq_w; eauto. 
Qed.

Lemma basic_step_fracq_eq_fracq e e' S S'
      (BSTEP : basic_step e e' S S') :
  E S ∩₁ FR S' ∩₁ Acq S' ≡₁ E S ∩₁ FR S ∩₁ Acq S.
Proof. 
  erewrite basic_step_fr_eq_fr; eauto. 
  arewrite (E S ∩₁ FR S ∩₁ Acq S' ≡₁ E S ∩₁ Acq S' ∩₁ FR S).
  { basic_solver. }
  erewrite basic_step_acq_eq_acq; eauto. 
  basic_solver.
Qed.

Lemma basic_step_fwrel_eq_fwrel e e' S S'
      (BSTEP : basic_step e e' S S') :
  E S ∩₁ FW S' ∩₁ Rel S' ≡₁ E S ∩₁ FW S ∩₁ Rel S.
Proof. 
  erewrite basic_step_fw_eq_fw; eauto. 
  arewrite (E S ∩₁ FW S ∩₁ Rel S' ≡₁ E S ∩₁ Rel S' ∩₁ FW S).
  { basic_solver. }
  erewrite basic_step_rel_eq_rel; eauto. 
  basic_solver.
Qed.

Hint Rewrite
     basic_step_rel_in_rel
     basic_step_acq_in_acq
     basic_step_sc_in_sc
     basic_step_r_in_r
     basic_step_w_in_w
     basic_step_f_in_f
     basic_step_rel_eq_rel
     basic_step_acq_eq_acq
     basic_step_sc_eq_sc
     basic_step_r_eq_r
     basic_step_w_eq_w
     basic_step_f_eq_f
     basic_step_fr_eq_fr
     basic_step_fw_eq_fw
     basic_step_fracq_eq_fracq
     basic_step_fwrel_eq_fwrel
  : same_lab_solveDb.

(******************************************************************************)
(** ** basic_step : `sb` propreties *)
(******************************************************************************)

Lemma basic_step_sb_delta_dom lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (WF: ES.Wf S) :
  dom_rel (sb_delta S k e e') ⊆₁ E S ∪₁ eq e.
Proof. cdes BSTEP_. step_solver. Qed.

Lemma basic_step_sb_delta_codom lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (WF: ES.Wf S) :
  codom_rel (sb_delta S k e e') ⊆₁ eq e ∪₁ eq_opt e'.
Proof. cdes BSTEP_. step_solver. Qed.

Lemma basic_step_sb_deltaE lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (WF: ES.Wf S) :
  sb_delta S k e e' ⨾ ⦗E S⦘ ≡ ∅₂.
Proof. 
  cdes BSTEP_.
  split; [|done]. step_solver.
Qed.

Lemma basic_step_sb_delta_seq_sb_delta lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (WF: ES.Wf S) :
  sb_delta S k e e' ⨾ sb_delta S k e e' ≡ ES.cont_sb_dom S k × eq_opt e'.
Proof. 
  cdes BSTEP_.
  unfold sb_delta.
  rewrite <- cross_union_l.
  rewrite !seq_union_l, !seq_union_r.
  arewrite_false (
    ES.cont_sb_dom S k × (eq e ∪₁ eq_opt e') ⨾ 
    ES.cont_sb_dom S k × (eq e ∪₁ eq_opt e')
  ).
  { step_solver. }
  arewrite_false (
    eq e × eq_opt e' ⨾ ES.cont_sb_dom S k × (eq e ∪₁ eq_opt e')
  ).
  { step_solver. }
  arewrite_false (
    eq e × eq_opt e' ⨾ eq e × eq_opt e'
  ).
  { step_solver. }
  relsf.
  rewrite cross_union_l, seq_union_l.
  arewrite_false (
    ES.cont_sb_dom S k × eq_opt e' ⨾ eq e × eq_opt e'
  ).
  { step_solver. }
  basic_solver 10.
Qed.

Lemma basic_step_sb_seq_sb_delta lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (WF: ES.Wf S) :
  sb S ⨾ sb_delta S k e e' ≡ 
     sb S ⨾ ES.cont_sb_dom S k × eq e ∪ sb S ⨾ ES.cont_sb_dom S k × eq_opt e'.
Proof. 
  cdes BSTEP_.
  unfold sb_delta.
  rewrite !seq_union_r.
  arewrite_false (sb S ⨾ eq e × eq_opt e').
  { step_solver. }
  basic_solver 10.
Qed.

Lemma basic_step_nupd_sb lang k k' st st' e S S' 
      (BSTEP_ : basic_step_ lang k k' st st' e None S S') :
  sb S' ≡ sb S ∪ ES.cont_sb_dom S k × eq e.  
Proof.                                       
  cdes BSTEP_.
  autounfold with ESStepDb in *.  
  rewrite !cross_false_r in SB'. 
  rewrite !union_false_r in SB'.
  apply SB'.
Qed.

Lemma basic_step_sbE e e' S S' 
      (BSTEP : basic_step e e' S S') 
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

Lemma basic_step_sb_nTid t lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (WF: ES.Wf S) 
      (nEQ : t <> ES.cont_thread S k) :
  sb S' ⨾ ⦗Tid_ S' t⦘ ≡ sb S ⨾ ⦗Tid_ S t⦘. 
Proof. 
  assert (basic_step e e' S S') 
    as BSTEP.
  { do 5 eexists. red. eauto. }
  cdes BSTEP_.
  rewrite SB'.
  rewrite !seq_union_l.

  arewrite
    (sb S ⨾ ⦗Tid_ S' t⦘ ≡ sb S ⨾ ⦗Tid_ S t⦘).
  { rewrite !seq_eqv_r.
    split; intros x y [SB TIDy]; 
      splits; auto.
    { erewrite <- basic_step_tid_eq_dom; eauto.
      apply ES.sbE in SB; auto.
      generalize SB. basic_solver. }
    erewrite basic_step_tid_eq_dom; eauto.
    apply ES.sbE in SB; auto.
    generalize SB. basic_solver. }

  arewrite_false 
    (sb_delta S k e e' ⨾ ⦗Tid_ S' t⦘).
  { unfold sb_delta.
    rewrite unionA.
    rewrite <- cross_union_r.
    rewrite seq_eqv_r.
    intros x y [[[_ EQy] | [_ EQy]] TIDy].
    { apply nEQ.
      subst t y. 
      erewrite basic_step_tid_e; eauto. }
    apply nEQ.
    unfold eq_opt in EQy.
    destruct e' as [e'|]; try done.
    subst t y. 
    erewrite basic_step_tid_e'; eauto. }

  basic_solver.
Qed.

Lemma basic_step_sbe lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (WF : ES.Wf S) :
  sb S' ⨾ ⦗eq e⦘ ≡ ES.cont_sb_dom S k × eq e. 
Proof. 
  cdes BSTEP_.
  rewrite SB'.
  unfold sb_delta.
  rewrite !seq_union_l.
  rewrite <- !cross_inter_r.
  rewrite set_interK.
  arewrite_false (sb S ⨾ ⦗eq e⦘).
  { step_solver. }
  arewrite (eq_opt e' ∩₁ eq e ≡₁ ∅).
  { split; [|done]. step_solver. }
  relsf.
Qed.

Lemma basic_step_sbe' lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (WF : ES.Wf S) :
  sb S' ⨾ ⦗eq_opt e'⦘ ≡ ES.cont_sb_dom S k × eq_opt e' ∪ eq e × eq_opt e'. 
Proof. 
  cdes BSTEP_.
  rewrite SB'.
  unfold sb_delta.
  rewrite !seq_union_l.
  rewrite <- !cross_inter_r.
  rewrite set_interK.
  arewrite_false (sb S ⨾ ⦗eq_opt e'⦘).
  { step_solver. }
  arewrite (eq e ∩₁ eq_opt e' ≡₁ ∅).
  { split; [|done]. step_solver. }
  relsf. 
Qed.

Lemma basic_step_sb_mon e e' S S' 
      (BSTEP : basic_step e e' S S') :
  sb S ⊆ sb S'.
Proof.
  cdes BSTEP; cdes BSTEP_.
  rewrite SB'; basic_solver. 
Qed.

Lemma basic_step_imm_sb lang k k' st st' e e' S S' 
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (WF : ES.Wf S) :
  immediate (sb S') ≡ immediate (sb S) ∪ imm_sb_delta S k e e'.
Proof. 
  cdes BSTEP_.
  rewrite SB'.
  rewrite !immediateE. 
  rewrite !minus_union_l.
  rewrite !seq_union_l, !seq_union_r.
  rewrite !minus_union_r. 
  
  rewrite !minus_disjoint
    with (r  := sb S) 
         (r' := sb S ⨾ sb_delta S k e e').
  2 : { split; [|done]. step_solver. }

  rewrite !minus_disjoint
    with (r  := sb S) 
         (r' := sb_delta S k e e' ⨾ sb_delta S k e e').
  2 : { split; [|done]. step_solver. }

  rewrite !minus_disjoint
    with (r  := sb_delta S k e e') 
         (r' := sb S ⨾ sb S).
  2 : { split; [|done]. step_solver. }

  
  arewrite_false (sb_delta S k e e' ⨾ sb S).
  { step_solver. }

  apply union_more.
  { basic_solver 10. }
  rewrite basic_step_sb_delta_seq_sb_delta; eauto.
  erewrite basic_step_sb_seq_sb_delta; eauto.
  rewrite minus_union_r.
  rewrite minus_false_r.
  rewrite !interA.
  rewrite !inter_absorb_l
    with (r' := sb_delta S k e e').
  2,3 : basic_solver.
  rewrite <- !minus_union_r.
  unfold sb_delta.
  rewrite !minus_union_l.
  rewrite !minus_union_r.
  
  rewrite !minus_disjoint
    with (r  := ES.cont_sb_dom S k × eq e) 
         (r' := sb S ⨾ ES.cont_sb_dom S k × eq_opt e').
  2 : { split; [|done]. step_solver. }
  rewrite !minus_disjoint
    with (r  := ES.cont_sb_dom S k × eq e) 
         (r' := ES.cont_sb_dom S k × eq_opt e').
  2 : { split; [|done]. step_solver. }
  rewrite !minus_disjoint
    with (r  := eq e × eq_opt e') 
         (r' := sb S ⨾ ES.cont_sb_dom S k × eq e).
  2 : { split; [|done]. step_solver. }
  rewrite !minus_disjoint
    with (r  := eq e × eq_opt e') 
         (r' := sb S ⨾ ES.cont_sb_dom S k × eq_opt e').
  2 : { split; [|done]. step_solver. }
  rewrite !minus_disjoint
    with (r  := eq e × eq_opt e') 
         (r' := ES.cont_sb_dom S k × eq_opt e').
  2 : { split; [|done]. step_solver. }
    
  arewrite_false (
    ES.cont_sb_dom S k × eq_opt e' \ ES.cont_sb_dom S k × eq_opt e'
  ).
  { basic_solver. }
  relsf.
  rewrite !inter_absorb_r.
  2 : basic_solver.

  unfold imm_sb_delta.
  apply union_more; auto.
  rewrite ES.cont_last_alt; auto.
  rewrite seq_eqv_r.
  split.
  { intros x y [[kSB EQy] nSB].
    unfolder; splits; auto.
    intros SB. apply nSB.
    basic_solver. }
  intros x y [[kSB nSB] EQy].
  unfolder; splits; auto.
  intros SB. apply nSB.
  basic_solver.
Qed.

Lemma basic_step_imm_sb_e a lang k k' st st' e e' S S'
      (WF : ES.Wf S)
      (kEVENT : k = CEvent a)
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') :
  immediate (sb S') a e.
Proof. 
  cdes BSTEP_.
  assert (basic_step e e' S S') as BSTEP. 
  { econstructor; eauto. }
  eapply basic_step_imm_sb; eauto.
  unfold imm_sb_delta, ES.cont_sb_dom.
  subst k.
  right. left.
  split; auto; split.
Qed.

Lemma basic_step_imm_sb_e' lang k k' st st' e e' S S'
      (WF : ES.Wf S)
      (BSTEP_ : basic_step_ lang k k' st st' e (Some e') S S') :
  immediate (sb S') e e'.
Proof. 
  cdes BSTEP_.
  assert (basic_step e (Some e') S S') as BSTEP. 
  { econstructor; eauto. }
  eapply basic_step_imm_sb; eauto.
  unfold imm_sb_delta.
  basic_solver.
Qed.

(******************************************************************************)
(** ** basic_step : `cf` properties *)
(******************************************************************************)

Lemma basic_step_cf lang k k' st st' e e' S S' 
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (wfE: ES.Wf S) :
  cf S' ≡ cf S ∪ cf_delta S k e e'.
Proof.
  assert (basic_step e e' S S') as BSTEP.
  { unfold basic_step. do 5 eexists. eauto. }
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
    rewrite <- !unionA.
    rewrite !crs_union.
    rewrite !compl_union.
    rewrite !restr_inter.
    rewrite !restr_cross.
    rewrite !interC with (r2 := Eninit S × Eninit S).
    rewrite <- !minus_inter_compl.
    arewrite (Eninit S × Eninit S \ (ES.cont_sb_dom S k × eq e)⁼ ≡ Eninit S × Eninit S \ ⦗⊤₁⦘).
    { unfold ES.acts_ninit_set, ES.acts_init_set, ES.acts_set.
      unfolder; unfold not. 
      splits; ins; splits; desf; ins; splits; desf; auto; omega. }
    arewrite (Eninit S × Eninit S \ (ES.cont_sb_dom S k × eq_opt e')⁼ ≡ Eninit S × Eninit S \ ⦗⊤₁⦘).
    { unfold ES.acts_ninit_set, ES.acts_init_set, ES.acts_set.
      unfolder; unfold not.
      splits; ins; splits; desf; ins; splits; desf; auto; omega. }
    arewrite (Eninit S × Eninit S \ (eq e × eq_opt e')⁼ ≡ Eninit S × Eninit S \ ⦗⊤₁⦘).
    { unfold ES.acts_ninit_set, ES.acts_init_set, ES.acts_set.
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
        rewrite !seq_eqv_inter.

        arewrite 
          (⦗Eninit S⦘ ⨾ (ES.same_tid S' \ ⦗⊤₁⦘) ⨾ ⦗eq e⦘ ≡ 
           ⦗Eninit S⦘ ⨾ (ES.same_tid S') ⨾ ⦗eq e⦘).
        { unfold ES.acts_ninit_set, ES.acts_init_set, ES.acts_set.
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
        { rewrite csE, transp_cross, minus_union_r, seq_eqv_inter. 
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
        rewrite <- seq_eqv_minus_lr, <- seq_eqv_minus_ll.
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
        (⦗Eninit S⦘ ⨾ ES.same_tid S' ⨾ ⦗eq e⦘ ≡ (E S ∩₁ Tid_ S (ES.cont_thread S k)) × eq e).
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
        rewrite !seq_eqv_inter.

        arewrite 
          (⦗Eninit S⦘ ⨾ (ES.same_tid S' \ ⦗⊤₁⦘) ⨾ ⦗eq e'⦘ ≡ 
           ⦗Eninit S⦘ ⨾ (ES.same_tid S') ⨾ ⦗eq e'⦘).
        { unfold ES.acts_ninit_set, ES.acts_init_set, ES.acts_set.
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
        { rewrite csE, transp_cross, minus_union_r, seq_eqv_inter. 
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
        rewrite <- seq_eqv_minus_lr, <- seq_eqv_minus_ll.
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
        (⦗Eninit S⦘ ⨾ ES.same_tid S' ⨾ ⦗eq e'⦘ ≡ (E S ∩₁ Tid_ S (ES.cont_thread S k)) × eq e').
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
      (BSTEP_ : basic_step_ lang k k' st st' e None S S') 
      (wfE: ES.Wf S) :
  cf S' ≡ cf S ∪ (ES.cont_cf_dom S k × eq e)^⋈.
Proof.
  erewrite basic_step_cf; eauto. 
  unfold cf_delta, eq_opt.
  basic_solver 42.
Qed.

Lemma basic_step_cf_restr e e' S S'
      (BSTEP : basic_step e e' S S') 
      (wfE: ES.Wf S) : 
  restr_rel (E S) (cf S') ≡ cf S.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  erewrite basic_step_cf; eauto. 
  unfold cf_delta.
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
      (BSTEP : basic_step e e' S S') 
      (wfE: ES.Wf S) :
  cf S ⊆ cf S'.
Proof.
  cdes BSTEP; cdes BSTEP_.
  erewrite basic_step_cf with (S':=S'); eauto.  
  apply inclusion_union_r1.
Qed.  

Lemma basic_step_cf_free lang k k' st st' e e' S S' X 
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (wfE: ES.Wf S)
      (XinE : X ⊆₁ E S)
      (CFF : ES.cf_free S X) 
      (nCFkX : X ∩₁ ES.cont_cf_dom S k ≡₁ ∅) :
  ES.cf_free S' (X ∪₁ eq e ∪₁ eq_opt e').  
Proof. 
  cdes BSTEP_.
  unfold ES.cf_free. 
  erewrite basic_step_cf; eauto. 
  unfold cf_delta.
  rewrite !id_union, !csE.  
  relsf. unionL; auto.  
  all : try by (rewrite ?XinE; step_solver).
  all : unfolder; ins; desf.
  all : eapply nCFkX; unfolder; splits; eauto. 
Qed.

(******************************************************************************)
(** ** basic_step : `icf` properties *)
(******************************************************************************)

Lemma basic_step_icf lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S')
      (wfE: ES.Wf S) :
  icf S' ≡ icf S ∪ icf_delta S k e.
Proof.
  assert (basic_step e e' S S') as BSTEP.
  { unfold basic_step. do 5 eexists. eauto. }
  cdes BSTEP_.
  unfold ES.icf.
  erewrite basic_step_cf; eauto.
  rewrite inter_union_l.
  apply union_more.

  { rewrite <- immediate_transp.
    erewrite basic_step_imm_sb; eauto.
    rewrite transp_union, immediate_transp.
    rewrite !seq_union_r, !seq_union_l.
    rewrite !inter_union_r.
    
    arewrite_false (
      cf S ∩ ((imm_sb_delta S k e e')⁻¹ ⨾ immediate (sb S))
    ).
    { step_solver. }
    arewrite_false (
      cf S ∩ (immediate (sb S)⁻¹ ⨾ imm_sb_delta S k e e')
    ).
    { step_solver. }
    arewrite_false (
      cf S ∩ ((imm_sb_delta S k e e')⁻¹ ⨾ imm_sb_delta S k e e')
    ).
    { step_solver. }
    basic_solver 10. }
  
  unfold cf_delta.
  rewrite <- immediate_transp.
  erewrite basic_step_imm_sb; eauto.
  rewrite transp_union, immediate_transp.
  rewrite !seq_union_r, !seq_union_l.
  rewrite !inter_union_l, !inter_union_r.
  
  arewrite_false (
    (ES.cont_cf_dom S k × eq e)^⋈ ∩ (immediate (sb S)⁻¹ ⨾ immediate (sb S))
  ).
  { step_solver. }
  arewrite_false (
    (ES.cont_cf_dom S k × eq e) ^⋈ ∩ ((imm_sb_delta S k e e')⁻¹ ⨾ imm_sb_delta S k e e')
  ).
  { step_solver. }
  arewrite_false (
    (ES.cont_cf_dom S k × eq_opt e')^⋈ ∩ (immediate (sb S)⁻¹ ⨾ immediate (sb S))
  ).
  { step_solver. }
  arewrite_false (
    (ES.cont_cf_dom S k × eq_opt e') ^⋈ ∩ ((imm_sb_delta S k e e')⁻¹ ⨾ imm_sb_delta S k e e')
  ).
  { step_solver. }
  arewrite_false (
    (ES.cont_cf_dom S k × eq_opt e') ^⋈ ∩ (immediate (sb S)⁻¹ ⨾ imm_sb_delta S k e e')
  ).
  { step_solver. }
  arewrite_false (
    (ES.cont_cf_dom S k × eq_opt e') ^⋈ ∩ ((imm_sb_delta S k e e')⁻¹ ⨾ immediate (sb S))
  ).
  { step_solver. }
  relsf.

  rewrite !csE.
  rewrite !inter_union_l.
  arewrite_false (
    ES.cont_cf_dom S k × eq e ∩ ((imm_sb_delta S k e e')⁻¹ ⨾ immediate (sb S))
  ).
  { step_solver. }
  arewrite_false (
    (ES.cont_cf_dom S k × eq e)⁻¹ ∩ (immediate (sb S)⁻¹ ⨾ imm_sb_delta S k e e')
  ).
  { step_solver. }
  relsf.
  
  unfold icf_delta, ES.cont_icf_dom.
  rewrite csE, transp_cross.
  rewrite unionC. apply union_more.
  { unfold imm_sb_delta.
    rewrite seq_union_r, inter_union_r.
    arewrite_false (immediate (sb S)⁻¹ ⨾ eq e × eq_opt e').
    { step_solver. } 
    rewrite inter_false_r, union_false_r.
    split. 
    { unfolder. ins. desf.
      splits; auto.
      eexists; splits; eauto. 
      eapply ES.cont_cf_tid; eauto. }
    rewrite <- immediate_transp.
    unfolder. ins. desf.
    splits; auto.
    { unfold ES.cont_last, ES.cont_cf_dom in *.
      destruct k. 
      { split; auto.
        apply ES.sbE in H1; auto.
        generalize H1. basic_solver. }
      right. basic_solver 10. }
    exists x0; splits; eauto. }
  unfold imm_sb_delta.
  rewrite transp_union, !seq_union_l, inter_union_r.
  arewrite_false ((eq e × eq_opt e')⁻¹ ⨾ immediate (sb S)).
  { step_solver. } 
  rewrite inter_false_r, union_false_r.
  split. 
  { unfolder. ins. desf.
    splits; auto.
    eexists; splits; eauto. 
    eapply ES.cont_cf_tid; eauto. }
  unfolder. ins. desf.
  splits; auto.
  { unfold ES.cont_last, ES.cont_cf_dom in *.
    destruct k. 
    { split; auto.
      apply ES.sbE in H1; auto.
      generalize H1. basic_solver. }
    right. basic_solver 10. }
  exists x0; splits; eauto. 
Qed.

Lemma basic_step_icf_restr lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S')
      (wfE: ES.Wf S) :
  restr_rel (E S) (icf S') ≡ icf S. 
Proof. 
  rewrite basic_step_icf; eauto.
  rewrite restr_union.
  arewrite_false 
    (restr_rel (E S) (icf_delta S k e)).
  { cdes BSTEP_. step_solver. }
  rewrite ES.icfE; auto.
  basic_solver 10.
Qed.

(******************************************************************************)
(** ** basic_step : `rmw` properties *)
(******************************************************************************)

Lemma basic_step_nupd_rmw e S S' 
      (BSTEP : basic_step e None S S') :
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
(** ** basic_step : continuation properties *)
(******************************************************************************)

Lemma basic_step_cont_thread lang k st e e' S S' 
      (BSTEP_ : basic_step e e' S S') 
      (WF : ES.Wf S)
      (KK : K S (k, existT _ lang st)) :
  ES.cont_thread S' k = ES.cont_thread S k. 
Proof. 
  unfold ES.cont_thread.
  destruct k; auto. 
  eapply basic_step_tid_eq_dom; eauto.
  eapply ES.K_inEninit; eauto.
Qed.

Lemma basic_step_cont_thread' lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') :
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

Lemma basic_step_cont_sb_dom lang k st e e' S S' 
      (BSTEP : basic_step e e' S S') 
      (WF : ES.Wf S)
      (KK : K S (k, existT _ lang st)) :
  ES.cont_sb_dom S' k ≡₁ ES.cont_sb_dom S k.
Proof. 
  unfold ES.cont_sb_dom.
  destruct k.
  { erewrite basic_step_acts_init_set; eauto. }
  cdes BSTEP; cdes BSTEP_.
  rewrite !crE. relsf.
  apply set_union_Propere; auto.
  rewrite SB'. 
  rewrite seq_union_l.
  rewrite dom_union.
  arewrite_false (sb_delta S k e e' ⨾ ⦗eq eid⦘).
  2 : basic_solver.
  arewrite (eq eid ⊆₁ E S).
  2 : step_solver.
  arewrite (eq eid ⊆₁ dom_rel ((sb S)^? ⨾ ⦗eq eid⦘)).
  { basic_solver. }
  fold (ES.cont_sb_dom S (CEvent eid)).
  eapply ES.cont_sb_domE; eauto.
Qed.

Lemma basic_step_cont_sb_dom' lang k k' st st' e e' S S' 
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (WF : ES.Wf S) :
  ES.cont_sb_dom S' k' ≡₁ ES.cont_sb_dom S k ∪₁ eq e ∪₁ eq_opt e'.
Proof.
  cdes BSTEP_.
  unfold ES.cont_sb_dom at 1. 
  subst k'. rewrite SB'. 
  unfold opt_ext, eq_opt in *.
  destruct e' as [e'|].
  { unfold sb_delta. 
    rewrite crE. relsf.
    arewrite_false (sb S ⨾ ⦗eq e'⦘). 
    { step_solver. }
    arewrite_false (ES.cont_sb_dom S k × eq e ⨾ ⦗eq e'⦘). 
    { step_solver. }    
    basic_solver 10. }
  unfold sb_delta. 
  rewrite crE. relsf.
  arewrite_false (sb S ⨾ ⦗eq e⦘). 
  { step_solver. }
  basic_solver 10. 
Qed.

Lemma basic_step_sb_cont_icf_cont_sb_e lang k k' st st' e e' S S' 
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (WF : ES.Wf S) :
  dom_rel (sb S ⨾ ⦗ES.cont_icf_dom S k⦘) ⊆₁ dom_rel (sb S' ⨾ ⦗eq e⦘).
Proof. 
  cdes BSTEP_.
  erewrite basic_step_sbe; eauto.
  rewrite dom_cross.
  2 : { intros EQx. eapply EQx. edone. }
  unfolder. ins. desf.
  eapply ES.cont_sb_dom_sb_cont_icf; eauto.
  basic_solver 10.
Qed.

Lemma basic_step_cont_set lang k k' st st' e e' S S' 
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') :
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
      (BSTEP_ : basic_step_ lang k k' st st' e None S S') :
  K S' ≡₁ K S ∪₁ eq (CEvent e, existT _ lang st').
Proof. 
  cdes BSTEP_.
  erewrite basic_step_cont_set; eauto. 
  by unfold opt_ext.
Qed.

Lemma basic_step_cont_adjacent lang k k' kk kk' st st' c e e' a a' S S' 
      (WF : ES.Wf S) 
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (KK : K S (kk, c))
      (ADJ : ES.cont_adjacent S' kk kk' a a') :
  ⟪ AJD_OLD : ES.cont_adjacent S kk kk' a a' ⟫ \/ (
    ⟪ EQkk  : kk  = k  ⟫ /\
    ⟪ EQkk' : kk' = k' ⟫ /\
    ⟪ EQa   : a   = e ⟫ /\
    ⟪ EQa'  : a'  = e' ⟫
  ).
Proof. 
  cdes BSTEP_.
  assert (basic_step e e' S S') as BSTEP.
  { red. eauto 20. }
  assert 
    (exists lang' kkst, c = existT _ lang' kkst)
    as [lang' [kkst EQc]]; [|subst c]. 
  { exists (projT1 c), (projT2 c). eapply sigT_eta. }
  
  unfold ES.cont_adjacent in ADJ. desc.
  erewrite basic_step_cont_sb_dom in kSBDOM; eauto.  
  erewrite basic_step_cont_thread in kEQTID; eauto.
  eapply basic_step_acts_ninit_set in nINITe; eauto.
  
  destruct nINITe as [[nINITa | EQe] | EQe'].
  { left. red.
    assert (eq a ⊆₁ E S) as Ea.
    { generalize nINITa. 
      unfold ES.acts_ninit_set.
      basic_solver. }
    assert (eq a × eq_opt a' ⊆ rmw S) as RMWe'.
    { destruct a' as [a'|].
      2 : basic_solver.
      unfold eq_opt in *. 
      assert (rmw S' a a') as RMW.
      { generalize RMWe. basic_solver. }
      apply RMW' in RMW.
      destruct RMW as [RMW|RMW].
      { apply ES.rmwE in RMW; auto.
        generalize RMW. basic_solver. }
      exfalso. 
      eapply basic_step_acts_set_ne; eauto.
      unfold rmw_delta in RMW.
      unfolder in RMW. desc.
      subst a. apply nINITa. }
    assert (eq_opt a' ⊆₁ Eninit S) as ENINITa'.
    { unfold eq_opt in *.
      destruct a' as [a'|].
      2 : basic_solver. 
      intros x EQx. subst x.
      assert (rmw S a a') as RMW.
      { generalize RMWe'. basic_solver. }
      eapply ES.rmw_codom_ninit; eauto.
      basic_solver. }
    edestruct ES.event_K 
      with (e := opt_ext a a') as [c' KK']; eauto.
    { generalize nINITa, ENINITa'. basic_solver. }
    { unfold eq_opt, opt_ext in *.
      destruct a' as [a'|].
      { eapply ES.rmw_codom_ndom; eauto. 
        generalize RMWe'. basic_solver. }
      intros HH. unfolder in HH. desc. 
      apply nRMWde; auto.
      eexists. apply RMW'. basic_solver. }
    red in KK'.
    assert 
      (exists lang'' kkst', c' = existT _ lang'' kkst')
      as [lang'' [kkst' EQc']]; [|subst c']. 
    { exists (projT1 c'), (projT2 c'). eapply sigT_eta. }
    constructor; splits; auto.
    { erewrite <- basic_step_cont_thread
        with (k := kk'); eauto.
      subst kk'. apply KK'. }
    { intros EQa' [b RMW].
      eapply nRMWde; auto.
      exists b. apply RMW'.
      basic_solver. }
    rewrite kSBDOM.
    rewrite SB'. relsf.
    arewrite_false (sb_delta S k e e' ⨾ ⦗eq a⦘).
    { rewrite Ea. step_solver. }
    basic_solver. }

  { right. subst a.
    assert (a' = e') as EQa'.
    { destruct a' as [a'|].
      { assert (rmw S' e a') as RMW.
        { apply RMWe. basic_solver. }
        apply RMW' in RMW.
        unfold rmw_delta in RMW.
        destruct RMW as [RMW|RMW].
        2 : generalize RMW; basic_solver.
        exfalso. 
        eapply basic_step_acts_set_ne; eauto.
        apply ES.rmwE in RMW; auto.
        generalize RMW. basic_solver. }
      destruct e' as [e'|]; auto.
      exfalso. apply nRMWde; auto.
      eexists. apply RMW'.
      unfold rmw_delta. basic_solver. }
    subst a'.
    splits; auto; try congruence.
    eapply ES.same_sb_dom_same_k; eauto.
    { rewrite kEQTID.
      erewrite <- basic_step_cont_thread' 
        with (k := k) (k' := k'); eauto.
      by subst k' kk'. }
    rewrite kSBDOM.
    rewrite basic_step_sbe; eauto.
    basic_solver. }

  exfalso.
  unfold eq_opt, opt_ext in *.
  destruct e' as [e'|]; auto.
  eapply basic_step_acts_set_ne; eauto.
  assert (eq a ≡₁ eq_opt (Some e')) as HH.
  { basic_solver. }
  eapply ES.cont_sb_domE 
    with (k := kk); eauto.
  rewrite HH in kSBDOM.
  rewrite basic_step_sbe' in kSBDOM; eauto.
  apply kSBDOM.
  basic_solver. 
Qed.

Lemma basic_step_K_adj e e' S S' 
      (WF : ES.Wf S) 
      (BSTEP : basic_step e e' S S') :
  forall (lang : Language.t (list label)) st st' k k' a a' 
         (KK  : K S' (k,  existT _ lang st )) 
         (KK' : K S' (k', existT _ lang st')) 
         (ADJ : ES.cont_adjacent S' k k' a a'),
  exists lbl lbl', 
    ⟪ LBL  : lbl  = (lab S') a ⟫ /\
    ⟪ LBL' : lbl' = option_map (lab S') a' ⟫ /\
    ⟪ STEP : (Language.step lang) (opt_to_list lbl' ++ [lbl]) st st' ⟫.
Proof.
  ins. cdes BSTEP.
  eapply basic_step_cont_set in KK. 
  2 : { cdes BSTEP; eauto. }
  eapply basic_step_cont_set in KK'. 
  2 : { cdes BSTEP; eauto. }
  destruct KK  as [KK  | KK ];
  destruct KK' as [KK' | KK'].

  { edestruct basic_step_cont_adjacent
      with (kk := k) as [ADJ_OLD | ADJ_NEW]; eauto.
    { red in ADJ_OLD.
      arewrite (lab S' a = lab S a).
      { eapply basic_step_lab_eq_dom; eauto. 
        eapply ES.cont_adjacent_ninit_e; eauto. }
      arewrite (option_map (lab S') a' = option_map (lab S) a').
      { destruct a' as [a'|]; auto.
        unfold option_map.
        erewrite basic_step_lab_eq_dom; eauto.
        eapply ES.cont_adjacent_ninit_e'; eauto. }
      eapply ES.K_adj; eauto. }
    desc. subst k0 k'0 a a'.
    cdes BSTEP_.
    exfalso. subst k'.
    eapply ES.K_inEninit in KK'; auto.
    unfold opt_ext in *.
    destruct e' as [e'|].
    { eapply basic_step_acts_set_ne'; eauto. apply KK'. }
    eapply basic_step_acts_set_ne; eauto. apply KK'. }

  { inversion KK' as [[EQk' EQlang EQc]].
    subst lang0.
    edestruct basic_step_cont_adjacent
      with (kk := k) as [ADJ_OLD | ADJ_NEW]; eauto.
    { red in ADJ_OLD. exfalso.
      set (ADJ_OLD' := ADJ_OLD).
      cdes ADJ_OLD'.
      unfold opt_ext in *.
      destruct e' as [e'|];
      destruct a' as [a'|].
      { eapply basic_step_acts_set_ne'; eauto. 
        arewrite (e' = a') by congruence.
        eapply ES.cont_adjacent_ninit_e'; eauto. }
      { eapply basic_step_acts_set_ne'; eauto. 
        arewrite (e' = a) by congruence.
        eapply ES.cont_adjacent_ninit_e; eauto. }
      { eapply basic_step_acts_set_ne; eauto. 
        arewrite (e = a') by congruence.
        eapply ES.cont_adjacent_ninit_e'; eauto. }
      eapply basic_step_acts_set_ne; eauto. 
      arewrite (e = a) by congruence.
      eapply ES.cont_adjacent_ninit_e; eauto. }
    desc. subst k0 k'0 a a'.
    cdes BSTEP_.
    set (c1 := (k, existT _ lang st )).
    set (c2 := (k, existT _ lang st0)).
    assert (fst c1 = fst c2) as HH by done.
    eapply ES.unique_K in HH; eauto.
    subst c1 c2. simpl in HH.
    assert (st0 = st) as STEQ.
    { eapply inj_pair2; eauto. }
    assert (st'0 = st') as EQST'.
    { eapply inj_pair2; eauto. }
    subst st0 st'0.
    exists lbl, lbl'.
    splits; auto.
    { rewrite LAB'.
      rewrite updo_opt, upds; auto.
      unfold eq_opt, opt_ext in *.
      basic_solver. }
    rewrite LAB'.
    unfold option_map, opt_same_ctor, upd_opt in *. 
    destruct e' as [e'|]; auto;
    destruct lbl'; intuition. 
      by rewrite upds. }

  { cdes ADJ. exfalso.
    inversion KK as [[EQk EQlang EQc]].
    eapply basic_step_acts_ninit_set in nINITe; eauto.
    destruct nINITe as [[nINITe | EQe] | EQe'].
    { 
      assert (ES.cont_sb_dom S' k ⊆₁ E S) 
        as kSBE.
      { rewrite kSBDOM.
        arewrite (sb S' ⨾ ⦗eq a⦘ ≡ sb S ⨾ ⦗eq a⦘).
        { split. 
          { rewrite <- seq_eqvK at 1.
            arewrite (eq a ⊆₁ E S) at 1.
            { unfold ES.acts_ninit_set in nINITe.
              generalize nINITe. basic_solver. }
            seq_rewrite basic_step_sbE; eauto.
            basic_solver. } 
          erewrite basic_step_sb_mon; eauto.
          basic_solver. }
        rewrite ES.sbE; auto.
        basic_solver. }
      unfold ES.cont_sb_dom, opt_ext in *.
      destruct k; [congruence|].
      inversion EQk. subst eid.
      destruct e' as [e'|].
      { eapply basic_step_acts_set_ne'; eauto.
        generalize kSBE. basic_solver 10. }
      eapply basic_step_acts_set_ne; eauto.
      generalize kSBE. basic_solver 10. }      
    { subst a.
      assert (a' = e') as EQa'.
      { destruct a' as [a'|]; auto.
        { assert (rmw S' e a') as RMW.
          { apply RMWe. basic_solver. }
          destruct e' as [e'|]; auto.
          { cdes BSTEP_.
            apply RMW' in RMW.
            destruct RMW as [RMW|RMW].
            { exfalso. 
              eapply basic_step_acts_set_ne; eauto.
              apply ES.rmwE in RMW; auto.
              generalize RMW. basic_solver. }
            unfold rmw_delta in RMW.
            generalize RMW. basic_solver. }
          cdes BSTEP_.
          unfold rmw_delta, eq_opt in RMW'.
          rewrite cross_false_r, union_false_r 
            in RMW'.
          apply RMW' in RMW.
          exfalso. 
          eapply basic_step_acts_set_ne; eauto.
          unfold rmw_delta in RMW.
          apply ES.rmwE in RMW; auto.
          generalize RMW. basic_solver. }
        destruct e' as [e'|]; auto.
        exfalso. 
        apply nRMWde; auto.
        cdes BSTEP_.
        eexists. apply RMW'.
        unfold rmw_delta. basic_solver. }
      subst a'.
      destruct k; [congruence|].
      inversion EQk. subst eid.
      erewrite basic_step_sbe in kSBDOM; eauto.
      rewrite dom_cross in kSBDOM.
      2 : { intros HH. eapply HH. edone. }
      unfold ES.cont_sb_dom in kSBDOM at 1.
      rewrite crE, seq_union_l, seq_id_l in kSBDOM.
      unfold opt_ext in kSBDOM.
      destruct e' as [e'|].
      { eapply basic_step_acts_set_ne'; eauto.
        eapply ES.cont_sb_domE with (k:=k0); eauto.
        { cdes BSTEP_. apply CONT. }
        apply kSBDOM. basic_solver. }
      eapply basic_step_acts_set_ne; eauto.
      eapply ES.cont_sb_domE with (k:=k0); eauto.
      { cdes BSTEP_. apply CONT. }
      apply kSBDOM. basic_solver. }
    unfold eq_opt in EQe'.
    destruct e' as [e'|]; auto.
    subst a.
    unfold eq_opt, opt_ext in *.
    destruct a' as [a'|]; auto.
    { assert (rmw S' e' a') as RMW.
      { apply RMWe. basic_solver. }
      cdes BSTEP_.
      apply RMW' in RMW.
      destruct RMW as [RMW|RMW].
      { eapply basic_step_acts_set_ne'; eauto.
        apply ES.rmwE in RMW; auto.
        generalize RMW. basic_solver. } 
      unfold rmw_delta in RMW.
      assert (e = e') as EQee'.
      { generalize RMW. basic_solver. }
      unfold opt_ext in EEQ. omega. }
    subst k.
    unfold ES.cont_sb_dom in kSBDOM.
    assert (eq e' ≡₁ eq_opt (Some e')) as HH.
    { basic_solver. }
    rewrite crE, seq_union_l, seq_id_l in kSBDOM.
    rewrite dom_union, dom_eqv in kSBDOM.
    rewrite HH in kSBDOM at 2 3. 
    erewrite !basic_step_sbe' in kSBDOM; eauto.
    rewrite !dom_union, !dom_cross in kSBDOM.
    2,3 : intros HE; eapply HE; edone. 
    assert ((ES.cont_sb_dom S k0 ∪₁ eq e) e') as 
      HE'.
    { generalize kSBDOM. basic_solver. }
    destruct HE' as [kSBe' | EQee'].
    { eapply basic_step_acts_set_ne'; eauto.
      eapply ES.cont_sb_domE with (k:=k0); eauto.
      cdes BSTEP_. apply CONT. }
    cdes BSTEP_. unfold opt_ext in EEQ. omega. }
  
  inversion KK  as [[EQk  EQlang  EQc ]].
  inversion KK' as [[EQk' EQlang' EQc']].
  cdes ADJ.
  eapply basic_step_acts_ninit_set 
    in nINITe; eauto.
  destruct nINITe as [[nINITa | EQae] | EQae'].
  { exfalso.
    destruct kSBDOM as [kSBDOM _].
    assert (dom_rel (sb S' ⨾ ⦗eq a⦘) ⊆₁ E S) as HSB.
    { arewrite (eq a ⊆₁ E S). 
      { generalize nINITa.
        unfold ES.acts_ninit_set.
        basic_solver. }
      erewrite basic_step_sbE; eauto. 
      rewrite ES.sbE; auto.
      basic_solver. }
    rewrite HSB in kSBDOM.
    unfold ES.cont_sb_dom in kSBDOM.
    destruct k; [congruence|].
    inversion EQk. subst eid.
    unfold opt_ext in kSBDOM.
    destruct e' as [e'|].
    { eapply basic_step_acts_set_ne'; eauto.
      apply kSBDOM. basic_solver 10. }
    eapply basic_step_acts_set_ne; eauto.
    apply kSBDOM. basic_solver 10. }
  { subst a. exfalso.
    unfold ES.cont_sb_dom in kSBDOM.
    destruct k; [congruence|].
    inversion EQk as [EQeid].
    unfold opt_ext in EQeid.
    erewrite basic_step_sbe in kSBDOM; eauto.
    rewrite dom_cross in kSBDOM.
    2 : { intros HH. eapply HH. edone. }
    destruct kSBDOM as [kSBDOM _].
    erewrite ES.cont_sb_domE in kSBDOM; eauto.
    2 : { cdes BSTEP_. apply CONT. }
    destruct e' as [e'|]; subst eid.
    { eapply basic_step_acts_set_ne'; eauto.
      generalize kSBDOM. basic_solver 10. }
    eapply basic_step_acts_set_ne; eauto.
    generalize kSBDOM. basic_solver 10. }
  unfold eq_opt in EQae'.
  destruct e' as [e'|]; try done.
  subst a. exfalso.
  unfold ES.cont_sb_dom in kSBDOM.
  destruct k; [congruence|].
  inversion EQk as [EQeid].
  unfold opt_ext in EQeid.
  subst eid.
  destruct kSBDOM as [kSBDOM _].
  assert (eq e' ≡₁ eq_opt (Some e')) as HA. 
  { basic_solver. }
  rewrite HA in kSBDOM at 2.
  erewrite basic_step_sbe' in kSBDOM; eauto.
  rewrite dom_union, !dom_cross in kSBDOM.
  2,3: intros HH; eapply HH; edone.
  assert ((ES.cont_sb_dom S k0 ∪₁ eq e) e') as HE.
  { generalize kSBDOM. basic_solver 10. }
  destruct HE as [kEe' | EQe'].
  { eapply basic_step_acts_set_ne'; eauto.
    eapply ES.cont_sb_domE; eauto.
    cdes BSTEP_. apply CONT. }
  cdes BSTEP_.
  unfold opt_ext in *.
  omega.
Qed.

(******************************************************************************)
(** ** Well-formedness *)
(******************************************************************************)

Lemma basic_step_sb_irr e e' S S'
      (BSTEP : basic_step e e' S S')
      (WF : ES.Wf S) :
  irreflexive (sb S'). 
Proof.
  cdes BSTEP. cdes BSTEP_.
  rewrite SB'.
  apply irreflexive_union. split.
  { apply WF. }
  unfold sb_delta. 
  repeat (apply irreflexive_union; split).
  3: { unfolder. ins; desf. simpls. omega. }
  all: unfolder; intros x [HH]; repeat (simpls; desf).
  2: assert (~ E S (Datatypes.S (ES.next_act S))) as XX.
  assert (~ E S (ES.next_act S)) as XX.
  1,3: intros XX; red in XX; omega.
  all: apply XX; eapply ES.cont_sb_domE; eauto.
Qed.

Lemma basic_step_sb_delta_prcl e e' S S' k k' lang st st'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (WF : ES.Wf S) :
  sb S ⨾ sb_delta S k e e' ⊆ sb_delta S k e e'.
Proof.
  assert (forall X,
             sb S ⨾ ES.cont_sb_dom S k × X ⊆
                ES.cont_sb_dom S k × X) as AA.
  { unfolder; ins; desf. split; auto.
    eapply ES.cont_sb_prcl; eauto.
    { cdes BSTEP_. eauto. }
    eexists. apply seq_eqv_r. split; eauto. }
  unfold sb_delta.
  rewrite !seq_union_r.
  arewrite_false (sb S ⨾ eq e × eq_opt e').
  { cdes BSTEP_. step_solver. }
  rewrite union_false_r.
  rewrite !AA. basic_solver.
Qed.

Lemma basic_step_sb_delta_transitive e e' S S' k k' lang st st'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (WF : ES.Wf S) :
  transitive (sb_delta S k e e').
Proof.
  apply transitiveI.
  arewrite (sb_delta S k e e' ⊆
            ⦗ E S ∪₁ eq e ⦘ ⨾ sb_delta S k e e')
  at 2.
  { generalize (basic_step_sb_delta_dom BSTEP_ WF). basic_solver. }
  rewrite id_union, !seq_union_l, !seq_union_r.
  unionL.
  { rewrite <- seqA.
    rewrite basic_step_sb_deltaE; eauto.
    basic_solver. }
  arewrite (⦗eq e⦘ ⨾ sb_delta S k e e' ⊆ eq e × eq_opt e').
  { unfold sb_delta.
    rewrite ES.cont_sb_domE; eauto.
    2: { cdes BSTEP_. eauto. }
    cdes BSTEP_. step_solver. }
  unfold sb_delta.
  assert (forall ee, eq_opt e' ee -> eq e ee -> False) as XX.
  2: { generalize XX. basic_solver. }
  intros ee AA BB; subst.
  cdes BSTEP_. step_solver.
Qed.

Lemma basic_step_sb_trans e e' S S'
      (BSTEP : basic_step e e' S S')
      (WF : ES.Wf S) :
  transitive (sb S'). 
Proof.
  apply transitiveI.
  cdes BSTEP. cdes BSTEP_.
  rewrite SB'.
  rewrite seq_union_r, !seq_union_l.
  unionL.
  { generalize WF.(ES.sb_trans). basic_solver. }
  { rewrite (dom_l WF.(ES.sbE)) at 1.
    rewrite <- seqA.
    rewrite basic_step_sb_deltaE; eauto. basic_solver. }
  { rewrite basic_step_sb_delta_prcl; eauto. eauto with hahn. }
  unionR right.
  apply transitiveI.
  eapply basic_step_sb_delta_transitive; eauto.
Qed.

Lemma basic_step_sb_same_thread' e e' S S'
      (BSTEP : basic_step e e' S S')
      (WF : ES.Wf S) : 
  sb S ∩ ES.same_tid S' ≡ sb S ∩ ES.same_tid S.
Proof.
  rewrite WF.(ES.sbE) at 1.
  rewrite seq_eqv_inter_ll. rewrite seq_eqv_inter_lr.
  rewrite seq_eqv_inter.
  rewrite interC.
  rewrite <- restr_relE.
  rewrite basic_step_same_tid_restr; eauto.
  rewrite restr_relE. rewrite WF.(ES.sbE) at 2.
  basic_solver.
Qed.

Lemma basic_step_sb_prcl e e' S S'
      (BSTEP : basic_step e e' S S')
      (WF : ES.Wf S) : 
  downward_total (sb S' ∩ ES.same_tid S').
Proof.
  cdes BSTEP. cdes BSTEP_. 
  rewrite SB'. rewrite inter_union_l.
  rewrite basic_step_sb_same_thread'; eauto.
  red. ins; desf.
  destruct Ryz as [YY|YY].
  { assert ((sb S ∩ ES.same_tid S) x z) as HH.
    2: { generalize (WF.(ES.sb_prcl) HH YY).
         basic_solver 10. }
    destruct Rxz as [|[SB ST]]; auto.
    exfalso. eapply basic_step_sb_deltaE; eauto.
    apply seq_eqv_r. split; eauto.
    destruct YY as [YY _]. apply WF.(ES.sbE) in YY.
    generalize YY. basic_solver. }
  destruct Rxz as [XX|XX].
  { exfalso. eapply basic_step_sb_deltaE; eauto.
    apply seq_eqv_r. split; [by apply YY|].
    destruct XX as [XX _]. apply WF.(ES.sbE) in XX.
    generalize XX. basic_solver. }
  destruct XX as [SBX TX]. destruct YY as [SBY TY].
  assert (ES.same_tid S' x y) as AA.
  { eapply ES.same_tid_trans; eauto. 
      by apply ES.same_tid_sym. }
  assert (ES.same_tid S' y x) as BB by (by apply ES.same_tid_sym).
  assert ((E S ∪₁ eq (ES.next_act S)) x) as EX.
  { eapply basic_step_sb_delta_dom; eauto.
    eexists; eauto. }
  assert ((E S ∪₁ eq (ES.next_act S)) y) as EY.
  { eapply basic_step_sb_delta_dom; eauto.
    eexists; eauto. }
  destruct EX as [EX|]; subst.
  2: { destruct EY as [EY|]; subst; red.
       2: by intuition.
       do 2 right. red. right.
       split; auto. red. left.
       assert (y <> ES.next_act S) as DD.
       { intros HH; subst. red in EY. omega. }
       red in SBY. generalize SBY DD. basic_solver. }
  assert (x <> ES.next_act S) as NNX.
  { intros HH; subst. red in EX. omega. }
  destruct EY as [EY|]; subst.
  2: { red. right. left. red. right.
       split; auto. red. left.
       red in SBX. generalize SBX NNX. basic_solver. }
  assert (y <> ES.next_act S) as NNY.
  { intros HH; subst. red in EY. omega. }
  assert ((sb S ∩ ES.same_tid S)⁼ x y) as DD.
  2: { generalize DD. basic_solver 10. }
  assert ((ES.same_tid S) x y) as SX.
  { eapply inclusion_restr.
    apply (basic_step_same_tid_restr BSTEP).
    red. splits; auto. }
  assert ((ES.same_tid S) y x) as SY by (by apply ES.same_tid_sym).
  assert ((sb S)⁼ x y) as DD.
  2: { generalize SX SY DD. basic_solver. }

  assert ((tid S') z = ES.cont_thread S k) as TT.
  { rewrite TID'.
    unfold sb_delta in SBX.
    unfolder in SBX. desf.
    { unfold upd_opt; desf; simpls; desf.
      { rewrite updo; [|omega].
        by rewrite upds. }
      by rewrite upds. }
    unfold upd_opt. 
    by rewrite upds. }
  assert (ES.cont_thread S k <> tid_init) as TNI.
  { intros XX. eapply WF.(ES.init_tid_K); eauto. }
  rewrite <- TT in TNI.
  
  assert (tid S' x = tid S x) as TXE.
  { eapply basic_step_tid_eq_dom; eauto. }
  assert (tid S' y = tid S y) as TYE.
  { eapply basic_step_tid_eq_dom; eauto. }

  assert (Eninit S x) as NIX.
  { red. split; auto. intros NN. destruct NN as [_ NN].
    apply TNI. rewrite <- TX. by rewrite TXE. }
  assert (Eninit S y) as NIY.
  { red. split; auto. intros NN. destruct NN as [_ NN].
    apply TNI. rewrite <- TY. by rewrite TYE. }

  assert (ES.cont_sb_dom S k x) as CX.
  { red in SBX. generalize NNX SBX. basic_solver. }
  assert (ES.cont_sb_dom S k y) as CY.
  { red in SBY. generalize NNY SBY. basic_solver. }
  red in CX. red in CY; desf.
  { exfalso. apply NIX. apply CX. }
  destruct CX as [ex CX]. apply seq_eqv_r in CX; desf.
  destruct CY as [ey CY]. apply seq_eqv_r in CY; desf.
  destruct CX as [|CX]; subst.
  { destruct CY as [|CY]; subst.
    2: generalize CY.
    all: basic_solver. }
  destruct CY as [|CY]; subst.
  { generalize CX. basic_solver. }
  destruct (classic (x = y)) as [|NEQ]; subst.
  { basic_solver. }
  red. right. eapply WF.(ES.sb_tot) with (e:=ey); eauto.
  { apply WF.(ES.sbE) in CX. generalize CX. basic_solver. }
  all: split; [|by try apply NIX; try apply NIY]. 
  all: eexists; apply seq_eqv_r; split; eauto.
Qed.

(******************************************************************************)
(** ** seqn properties *)
(******************************************************************************)

Lemma basic_step_seqn_eq_dom e e' S S'
      (BSTEP : basic_step e e' S S') 
      (WF : ES.Wf S) :
  eq_dom (E S) (ES.seqn S') (ES.seqn S). 
Proof. 
  cdes BSTEP; cdes BSTEP_.
  red. intros x. ins.
  unfold ES.seqn.
  rewrite <- seq_eqv_inter_lr.
  arewrite (sb S' ⨾ ⦗eq x⦘ ≡ sb S ⨾ ⦗eq x⦘). 
  { red. split. 
    { rewrite <- seq_eqvK, <- seqA. 
      arewrite (eq x ⊆₁ E S).
      { basic_solver. }
      rewrite <- seqA, basic_step_sbE; eauto.
      basic_solver. }
    rewrite SB'. basic_solver. }
  rewrite seq_eqv_inter_lr.
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
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (WF : ES.Wf S) :
  ES.seqn S' e = 0. 
Proof.   
  cdes BSTEP_.
  assert (basic_step e e' S S') as BSTEP. 
  { econstructor; eauto. }
  autounfold with ESStepDb in *.  
  unfold ES.seqn.
  arewrite (sb S' ∩ ES.same_tid S' ⨾ ⦗eq e⦘ ≡ ∅₂); 
    [|by rewrite dom_empty; apply countNatP_empty].
  split; [|done]. 
  rewrite <- seq_eqv_inter_lr.
  arewrite (sb S' ⨾ ⦗eq e⦘ ≡ ES.cont_sb_dom S k × eq e). 
  { rewrite SB'. 
    rewrite !seq_union_l.
    arewrite_false (sb S ⨾ ⦗eq e⦘).
    { step_solver. }
    arewrite_false (ES.cont_sb_dom S k × eq_opt e' ⨾ ⦗eq e⦘).
    { step_solver. }
    arewrite_false (eq e × eq_opt e' ⨾ ⦗eq e⦘).
    { step_solver. }
    basic_solver 10. }
  unfold ES.cont_sb_dom. subst. 
  unfold ES.same_tid.
  unfold ES.acts_init_set.
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
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (WF : ES.Wf S) :
  ES.seqn S' e = 1 + ES.seqn S x. 
Proof.
  cdes BSTEP_.
  assert (basic_step e e' S S') as BSTEP. 
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
     (although it really uses only sb-related properties). 
     However, since here we are working with basic step, 
     we can only assume well-formedness of `sb`. 
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
      (BSTEP : basic_step e (Some e') S S') 
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

Lemma basic_step_cont_sb_dom_eq S S' e e'
      kC state
      (WFS : ES.Wf S)
      (BSTEP : basic_step e e' S S')
      (INK : K S (kC, state)) :
  ES.cont_sb_dom S' kC ≡₁ ES.cont_sb_dom S kC.
Proof.
  unfold ES.cont_sb_dom. desf.
  { eapply basic_step_acts_init_set; eauto. }
  arewrite ((sb S')^? ⨾ ⦗eq eid⦘ ≡ (sb S)^? ⨾ ⦗eq eid⦘).
  2: basic_solver.
  split.
  2: by erewrite basic_step_sb_mon; eauto.
  rewrite !crE, !seq_union_l. apply union_mori; [done|].
  arewrite (⦗eq eid⦘ ⊆ ⦗E S⦘ ⨾ ⦗eq eid⦘).
  2: { rewrite <- !seqA. by rewrite basic_step_sbE; eauto. }
  unfolder. ins. desf. splits; auto.
  eapply ES.K_inEninit; eauto.
Qed.

End BasicStep.

(* Section hides the tactics and hints, so we repeat it here.
 * TODO: invent a better solution, 
 *       perhaps it is better to get rid of notation here at all. 
 *)
Hint Unfold sb_delta rmw_delta cf_delta : ESStepDb.

Hint Rewrite
     basic_step_rel_in_rel
     basic_step_acq_in_acq
     basic_step_sc_in_sc
     basic_step_r_in_r
     basic_step_w_in_w
     basic_step_f_in_f
     basic_step_rel_eq_rel
     basic_step_acq_eq_acq
     basic_step_sc_eq_sc
     basic_step_r_eq_r
     basic_step_w_eq_w
     basic_step_f_eq_f
     basic_step_fr_eq_fr
     basic_step_fw_eq_fw
     basic_step_fracq_eq_fracq
     basic_step_fwrel_eq_fwrel
  : same_lab_solveDb.

Ltac step_solver := 
  repeat autounfold with ESStepDb in *; 
  unfold eq_opt, opt_ext in *; 
  rewrite 1?ES.sbE, 1?ES.rmwE, 1?ES.cfE, 
    1?ES.cont_sb_domE, 1?ES.cont_cf_domE,
    1?ES.jfE, 1?ES.jfiE, 1?ES.jfeE,
    1?ES.rfE, 1?ES.coE, 1?ES.ewE, 
    1?rsE, 1?releaseE, 1?swE, 1?hbE;
  unfold ES.acts_ninit_set, ES.acts_init_set, ES.acts_set in *;
  eauto; unfolder; ins; splits; desf; omega.
