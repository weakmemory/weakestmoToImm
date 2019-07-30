From hahn Require Import Hahn.
From imm Require Import Events AuxRel. 
Require Import AuxRel.
Require Import AuxDef.
Require Import EventStructure.
Require Import Consistency.
Require Import Execution.
Require Import BasicStep.
Require Import AddJF.
Require Import AddEW.
Require Import AddCO.

Set Implicit Arguments.

(* Open a section here to hide the notations inside it.
 * TODO: invent a better solution, 
 *       perhaps it is better to get rid of notation here at all. 
 *)
Section Step.

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
Notation "'fr' S" := S.(ES.fr) (at level 10).
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

Notation "'same_mod' S" := (same_mod S.(ES.lab)) (at level 10).
Notation "'same_loc' S" := (same_loc S.(ES.lab)) (at level 10).
Notation "'same_val' S" := (same_val S.(ES.lab)) (at level 10).

Notation "'K' S" := (S.(ES.cont_set)) (at level 10).

Notation "'Tid_' S" := (fun t e => S.(ES.tid) e = t) (at level 1).
Notation "'Mod_' S" := (fun m x => mod S x = m) (at level 1).
Notation "'Loc_' S" := (fun l x => loc S x = l) (at level 1).
Notation "'Val_' S" := (fun v e => val S e = v) (at level 1).

Definition fence_step
           (e  : eventid)
           (e' : option eventid)
           (S S' : ES.t) : Prop :=
  ⟪ nUPD : e' = None ⟫ /\
  ⟪ FF  : F S' e ⟫ /\
  ⟪ JF' : jf S' ≡ jf S ⟫ /\
  ⟪ EW' : ew S' ≡ ew S ⟫ /\
  ⟪ CO' : co S' ≡ co S ⟫.

Definition load_step
           (e  : eventid)
           (e' : option eventid)
           (S S' : ES.t) : Prop :=
  exists w, 
    ⟪ nUPD : e' = None ⟫ /\
    ⟪ AJF : add_jf w e S S' ⟫ /\
    ⟪ EW' : ew S' ≡ ew S ⟫ /\
    ⟪ CO' : co S' ≡ co S ⟫.

Definition store_step
           (e  : eventid)
           (e' : option eventid)
           (S S' : ES.t) : Prop :=
  exists ews ws, 
    ⟪ nUPD : e' = None ⟫ /\
    ⟪ JF' : jf S' ≡ jf S ⟫ /\
    ⟪ AEW : add_ew ews e S S' ⟫ /\
    ⟪ ACO : add_co ews ws e S S' ⟫.

Definition update_step
           (e  : eventid)
           (e' : option eventid)
           (S S' : ES.t) : Prop := 
  exists w ews ws w',
    ⟪ SLOC : same_loc S' e w' ⟫ /\
    ⟪ UPD : e' = Some w' ⟫ /\
    ⟪ REX : R_ex S' e ⟫ /\
    ⟪ AJF : add_jf w e S S' ⟫ /\
    ⟪ AEW : add_ew ews w' S S' ⟫ /\
    ⟪ ACO : add_co ews ws w' S S' ⟫.

Definition step_ e e' S S' :=
  fence_step e e' S S' \/ load_step e e' S S' \/ store_step e e' S S' \/ update_step e e' S S'.

Definition step (m : model) (S S' : ES.t) : Prop := exists e e',
  ⟪ TT : step_ e e' S S' ⟫ /\
  ⟪ BSTEP : basic_step e e' S S' ⟫ /\
  ⟪ CONS : @es_consistent S' m ⟫.

(******************************************************************************)
(** ** Unfold step helper tactics *)
(******************************************************************************)

Ltac unfold_step_ H := 
  unfold step_, 
  fence_step, 
  load_step, 
  store_step, 
  update_step 
    in H; 
  destruct H as [HA | [HB | [HC | HD]]]; desc.

Ltac unfold_step H := 
  unfold step in H; 
  destruct H as [H [BSTEP_ CONS]];
  red in BSTEP_;
  unfold_step_ H.

(******************************************************************************)
(** ** Tactic for R/W/F sets after step lemmas *)
(******************************************************************************)

Ltac step_type_solver :=
  erewrite basic_step_acts_set; eauto;
  unfold eq_opt;
  rewrite !set_inter_union_l;
  autorewrite with same_lab_solveDb; 
  eauto; type_solver 10.


(******************************************************************************)
(** ** Fence step properties *)
(******************************************************************************)

Lemma fence_step_E e e' S S'
      (BSTEP : basic_step e e' S S')
      (FSTEP: fence_step e e' S S') :
  E S' ≡₁ E S ∪₁ eq e.
Proof. cdes FSTEP. subst. by apply basic_step_nupd_acts_set. Qed.

Lemma fence_step_R e e' S S'
      (BSTEP : basic_step e e' S S')
      (FSTEP: fence_step e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ R S' ≡₁ E S ∩₁ R S.
Proof. cdes FSTEP. step_type_solver. Qed.  

Lemma fence_step_W e e' S S'
      (BSTEP : basic_step e e' S S')
      (FSTEP: fence_step e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ W S' ≡₁ E S ∩₁ W S.
Proof. cdes FSTEP. step_type_solver. Qed.  

Lemma fence_step_F e e' S S'
      (BSTEP : basic_step e e' S S')
      (FSTEP: fence_step e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ F S' ≡₁ E S ∩₁ F S ∪₁ eq e.
Proof. cdes FSTEP. step_type_solver. Qed.  

Lemma fence_step_acq e e' S S'
      (BSTEP : basic_step e e' S S')
      (FSTEP: fence_step e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ FR S' ∩₁ Acq S' ≡₁ E S ∩₁ FR S ∩₁ Acq S ∪₁ eq e ∩₁ Acq S'.
Proof. cdes FSTEP. step_type_solver. Qed.  

Lemma fence_step_Rel e e' S S'
      (BSTEP : basic_step e e' S S')
      (FSTEP: fence_step e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ FW S' ∩₁ Rel S' ≡₁ E S ∩₁ FW S ∩₁ Rel S ∪₁ eq e ∩₁ Rel S'.
Proof. cdes FSTEP. step_type_solver. Qed.  

(******************************************************************************)
(** ** Load step properties *)
(******************************************************************************)

Lemma load_step_E e e' S S'
      (BSTEP : basic_step e e' S S')
      (LSTEP: load_step e e' S S') :
  E S' ≡₁ E S ∪₁ eq e.
Proof. cdes LSTEP. subst. by apply basic_step_nupd_acts_set. Qed.

Lemma load_step_R e e' S S'
      (BSTEP : basic_step e e' S S')
      (LSTEP: load_step e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ R S' ≡₁ E S ∩₁ R S ∪₁ eq e.
Proof. cdes LSTEP; cdes AJF. step_type_solver. Qed.  

Lemma load_step_W e e' S S'
      (BSTEP : basic_step e e' S S')
      (LSTEP: load_step e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ W S' ≡₁ E S ∩₁ W S.
Proof. cdes LSTEP; cdes AJF. step_type_solver. Qed.  

Lemma load_step_F e e' S S'
      (BSTEP : basic_step e e' S S')
      (LSTEP: load_step e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ F S' ≡₁ E S ∩₁ F S.
Proof. cdes LSTEP; cdes AJF. step_type_solver. Qed.  

Lemma load_step_acq e e' S S'
      (BSTEP : basic_step e e' S S')
      (LSTEP: load_step e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ FR S' ∩₁ Acq S' ≡₁ E S ∩₁ FR S ∩₁ Acq S ∪₁ eq e ∩₁ Acq S'.
Proof. cdes LSTEP; cdes AJF. step_type_solver. Qed.  

Lemma load_step_Rel e e' S S'
      (BSTEP : basic_step e e' S S')
      (LSTEP: load_step e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ FW S' ∩₁ Rel S' ≡₁ E S ∩₁ FW S ∩₁ Rel S.
Proof. cdes LSTEP; cdes AJF. step_type_solver. Qed.  

(******************************************************************************)
(** ** Store step properties *)
(******************************************************************************)

Lemma store_step_E e e' S S'
      (BSTEP : basic_step e e' S S')
      (SSTEP: store_step e e' S S') :
  E S' ≡₁ E S ∪₁ eq e.
Proof. cdes SSTEP. subst. by apply basic_step_nupd_acts_set. Qed.

Lemma store_step_R e e' S S'
      (BSTEP : basic_step e e' S S')
      (SSTEP: store_step e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ R S' ≡₁ E S ∩₁ R S.
Proof. cdes SSTEP; cdes ACO. step_type_solver. Qed.  

Lemma store_step_W e e' S S'
      (BSTEP : basic_step e e' S S')
      (SSTEP: store_step e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ W S' ≡₁ E S ∩₁ W S ∪₁ eq e.
Proof. cdes SSTEP; cdes ACO. step_type_solver. Qed.  

Lemma store_step_F e e' S S'
      (BSTEP : basic_step e e' S S')
      (SSTEP: store_step e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ F S' ≡₁ E S ∩₁ F S.
Proof. cdes SSTEP; cdes ACO. step_type_solver. Qed.  

Lemma store_step_acq e e' S S'
      (BSTEP : basic_step e e' S S')
      (SSTEP: store_step e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ FR S' ∩₁ Acq S' ≡₁ E S ∩₁ FR S ∩₁ Acq S.
Proof. cdes SSTEP; cdes ACO. step_type_solver. Qed.  

Lemma store_step_Rel e e' S S'
      (BSTEP : basic_step e e' S S')
      (SSTEP: store_step e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ FW S' ∩₁ Rel S' ≡₁ E S ∩₁ FW S ∩₁ Rel S ∪₁ eq e ∩₁ Rel S'.
Proof. cdes SSTEP; cdes ACO. step_type_solver. Qed.  

(******************************************************************************)
(** ** Update step properties *)
(******************************************************************************)

Lemma update_step_E e e' S S'
      (BSTEP : basic_step e (Some e') S S')
      (USTEP: update_step e (Some e') S S') :
  E S' ≡₁ E S ∪₁ eq e ∪₁ eq e'.
Proof. cdes USTEP. erewrite basic_step_acts_set; eauto. basic_solver. Qed.

Lemma update_step_R e e' S S'
      (BSTEP : basic_step e (Some e') S S')
      (USTEP: update_step e (Some e') S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ R S' ≡₁ E S ∩₁ R S ∪₁ eq e.
Proof. cdes USTEP; cdes AJF; cdes ACO. step_type_solver. Qed.  

Lemma update_step_W e e' S S'
      (BSTEP : basic_step e (Some e') S S')
      (USTEP: update_step e (Some e') S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ W S' ≡₁ E S ∩₁ W S ∪₁ eq e'.
Proof. cdes USTEP; cdes AJF; cdes ACO. step_type_solver. Qed.  

Lemma update_step_F e e' S S'
      (BSTEP : basic_step e (Some e') S S')
      (USTEP: update_step e (Some e') S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ F S' ≡₁ E S ∩₁ F S.
Proof. cdes USTEP; cdes AJF; cdes ACO. 
step_type_solver. Qed.  

Lemma update_step_acq e e' S S'
      (BSTEP : basic_step e (Some e') S S')
      (USTEP: update_step e (Some e') S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ FR S' ∩₁ Acq S' ≡₁ E S ∩₁ FR S ∩₁ Acq S ∪₁ eq e ∩₁ Acq S'.
Proof. cdes USTEP; cdes AJF; cdes ACO. step_type_solver. Qed.  

Lemma update_step_Rel e e' S S'
      (BSTEP : basic_step e (Some e') S S')
      (USTEP: update_step e (Some e') S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ FW S' ∩₁ Rel S' ≡₁ E S ∩₁ FW S ∩₁ Rel S ∪₁ (eq e' ∩₁ Rel S').
Proof. cdes USTEP; cdes AJF; cdes ACO. step_type_solver. Qed.  

(******************************************************************************)
(** ** Step (same jf) properties *)
(******************************************************************************)

Lemma step_same_jf_jfi e e' S S'
      (BSTEP : basic_step e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (wf : ES.Wf S) : 
  jfi S' ≡ jfi S.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold ES.jfi.
  rewrite SB', JF'.
  rewrite inter_union_r.
  arewrite_false (jf S ∩ sb_delta S k e e').
  { step_solver. }
  basic_solver.
Qed.

Lemma step_same_jf_jfe e e' S S'
      (BSTEP : basic_step e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (wf : ES.Wf S) : 
  jfe S' ≡ jfe S.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold ES.jfe.
  rewrite SB', JF'.
  rewrite minus_union_r.
  rewrite minus_disjoint with (r' := sb_delta S k e e').
  2 : { split; [|done]. step_solver. }
  basic_solver.
Qed.

Lemma step_same_jf_sb_jf lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (wf : ES.Wf S) : 
  (sb S' ∪ jf S')＊ ≡ 
    (sb S ∪ jf S)＊ ⨾ (sb_delta S k e e')^?. 
Proof. 
  cdes BSTEP_.
  assert (basic_step e e' S S') as BSTEP.
  { econstructor. eauto. }
  rewrite SB', JF'. 
  arewrite 
    (sb S ∪ sb_delta S k e e' ∪ jf S ≡
      sb_delta S k e e' ∪ (sb S ∪ jf S))
    by basic_solver.
  erewrite rt_unionE. 
  apply seq_more; auto.
  rewrite rt_begin with (r := sb S ∪ jf S).
  rewrite seq_union_r, seq_id_r. 
  arewrite_false 
    (sb_delta S k e e' ⨾ (sb S ∪ jf S)).
  { step_solver. }
  relsf. 
  rewrite rtE, crE.
  apply union_more; auto.
  (* unroll transitive closure up to 3 iterations *)
  do 3 rewrite ct_begin, rtE.
  rewrite !seq_union_r, !seq_id_r.
  rewrite <- !seqA.
  rewrite basic_step_sb_delta_seq_sb_delta; eauto.
  arewrite_false 
    ((ES.cont_sb_dom S k × eq_opt e') ⨾ (sb_delta S k e e')).
  { step_solver. }
  unfold sb_delta. 
  basic_solver 10. 
Qed.

Lemma step_same_jf_sb_jfE e e' S S'
      (BSTEP : basic_step e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (wfE: ES.Wf S) :
  (sb S' ∪ jf S')＊ ⨾ ⦗E S⦘ ≡ (sb S ∪ jf S)＊ ⨾ ⦗E S⦘.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  erewrite step_same_jf_sb_jf; eauto.
  rewrite crE. relsf.
  rewrite <- union_false_r with (r := (sb S ∪ jf S)＊ ⨾ ⦗E S⦘) at 2. 
  apply union_more; auto.
  split; [|done].
  step_solver.
Qed.

Lemma step_same_jf_cc lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (wfE: ES.Wf S) :
  cc S' ≡ cc S ∪ 
     cf S' ∩  (jfe S ⨾ (sb S ∪ jf S)＊ ⨾ (jfe S ⨾ sb_delta S k e e')).
Proof. 
  cdes BSTEP_.
  assert (basic_step e e' S S') as BSTEP.
  { econstructor. eauto. }
  unfold cc at 1. 
  rewrite step_same_jf_jfe; eauto.
  erewrite dom_rel_helper with (r := jfe S) at 2.
  2 : { rewrite ES.jfeE; [|auto]. rewrite dom_seq, dom_eqv. auto. }
  rewrite !seqA. 
  rewrite <- seqA with (r2 := ⦗E S⦘).
  rewrite step_same_jf_sb_jfE; eauto.
  rewrite !seqA.
  rewrite <- !seqA with (r1 := ⦗E S⦘).
  erewrite <- dom_rel_helper with (r := jfe S).
  2 : { rewrite ES.jfeE; [|auto]. rewrite dom_seq, dom_eqv. auto. }
  rewrite SB'. 
  rewrite cr_union_l. relsf.
  rewrite !inter_union_r.
  apply union_more; auto.
  rewrite basic_step_cf; eauto. 
  autounfold with ESStepDb.
  rewrite <- unionA, !inter_union_l, unionA.
  rewrite <- union_false_r with (r := cc S).
  apply union_more.
  { by unfold cc. }
  split; [|done].
  step_solver. 
Qed.

Lemma step_same_jf_ccE e e' S S'
      (BSTEP : basic_step e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (wfE: ES.Wf S) :
  cc S' ⨾ ⦗E S⦘ ≡ cc S.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  rewrite step_same_jf_cc; eauto.
  rewrite seq_union_l.
  rewrite interC.
  rewrite <- lib.AuxRel.seq_eqv_inter_lr.
  rewrite !seqA.
  arewrite_false 
    (sb_delta S k e e' ⨾ ⦗E S⦘).
  { step_solver. }
  relsf.
  rewrite ccE. basic_solver.
Qed.

Lemma step_same_jf_rsE e e' S S'
      (BSTEP : basic_step e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (RMW' : rmw S' ≡ rmw S) 
      (wfE: ES.Wf S) :
  rs S' ⨾ ⦗E S⦘ ≡ rs S ⨾ ⦗E S⦘.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold rs at 1. rewrite !seqA.
  rewrite JF', RMW'.
  arewrite ((jf S ⨾ rmw S)＊ ⨾ ⦗E S⦘ ≡ ⦗E S⦘ ⨾ (jf S ⨾ rmw S)＊ ⨾ ⦗E S⦘).
  { rewrite rtE. relsf.
    apply union_more; auto.
    rewrite restr_clos_trans_eq with (s := E S).
    2 : { rewrite ES.jfE, ES.rmwE; auto. basic_solver 10. }
    basic_solver. }
  seq_rewrite basic_step_w_sb_loc_wE; eauto.
  unfold rs.
  rewrite !seqA.
  basic_solver.
Qed.

Lemma step_same_jf_releaseE e e' S S'
      (BSTEP : basic_step e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (RMW' : rmw S' ≡ rmw S) 
      (wfE: ES.Wf S) :
  release S' ⨾ ⦗E S⦘ ≡ release S ⨾ ⦗E S⦘.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold release at 1. 
  rewrite !seqA.
  seq_rewrite step_same_jf_rsE; eauto.
  rewrite rsE; auto.
  rewrite !seqA.
  seq_rewrite basic_step_rel_f_sbE; eauto. 
  unfold release.
  rewrite ES.sbE, rsE; auto.
  basic_solver 20.
Qed.

Lemma step_same_jf_sw lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (RMW' : rmw S' ≡ rmw S) 
      (wfE: ES.Wf S) :
  sw S' ≡ sw S ∪ sw_delta S S' k e e'.
Proof. 
  cdes BSTEP_.
  assert (basic_step e e' S S') as BSTEP.
  { econstructor. eauto. }
  unfold sw at 1.
  rewrite JF'. 
  rewrite ES.jfE; auto.
  rewrite !seqA, <- seqA.
  rewrite step_same_jf_releaseE; eauto.
  rewrite !seqA.
  seq_rewrite <- ES.jfE; auto.
  rewrite SB'. relsf.
  rewrite cr_union_l. relsf.
  apply union_more.
  { rewrite basic_step_jf_sb_f_acq; eauto. }
  unfold sw_delta.
  rewrite JF'.
  arewrite_false (jf S ⨾ ⦗eq e⦘).
  { step_solver. }
  basic_solver 10.
Qed.  

Lemma step_same_jf_hb lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (RMW' : rmw S' ≡ rmw S) 
      (wfE: ES.Wf S) :
  hb S' ≡ hb S ∪ hb_delta S S' k e e'.
Proof.
  cdes BSTEP_.
  assert (basic_step e e' S S') as BSTEP.
  { subst. econstructor. eauto. }
  unfold hb at 1.
  rewrite SB'. 
  rewrite step_same_jf_sw; eauto.
  arewrite 
    (sb S ∪ sb_delta S k e e' ∪ (sw S ∪ sw_delta S S' k e e') ≡
     (sb_delta S k e e' ∪ sw_delta S S' k e e') ∪ (sb S ∪ sw S))
    by basic_solver.
  rewrite ct_unionE.
  unfold hb. 
  apply union_more; auto.
  rewrite <- cr_of_ct.
  rewrite basic_step_hb_delta_alt; eauto.
Qed.

Lemma step_same_jf_hb_dom e e' S S' 
      (BSTEP : basic_step e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (RMW' : rmw S' ≡ rmw S) 
      (wfE: ES.Wf S) :
  dom_rel (hb S') ⊆₁ E S ∪₁ eq e.
Proof. 
  cdes BSTEP.
  rewrite step_same_jf_hb; eauto.
  rewrite dom_union.
  rewrite basic_step_hb_delta_dom; eauto.
  rewrite hbE; auto.
  basic_solver.
Qed. 

Lemma step_same_jf_hbE e e' S S' 
      (BSTEP : basic_step e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (RMW' : rmw S' ≡ rmw S) 
      (wfE: ES.Wf S) :
  hb S' ⨾ ⦗E S⦘ ≡ hb S.
Proof. 
  cdes BSTEP.
  rewrite step_same_jf_hb; eauto.
  relsf.
  rewrite basic_step_hb_deltaE; eauto.
  rewrite hbE; auto. basic_solver 5.
Qed. 

Lemma step_same_jf_ecf_restr e e' S S'
      (BSTEP : basic_step e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (RMW' : rmw S' ≡ rmw S) 
      (wfE: ES.Wf S) :
  restr_rel (E S) (ecf S') ≡ ecf S. 
Proof. 
  cdes BSTEP.
  unfold ecf.
  rewrite !crE. relsf.
  rewrite !restr_union.
  repeat apply union_more.
  { eapply basic_step_cf_restr; eauto. }
  { rewrite restr_relE, !seqA.
    arewrite (⦗E S⦘ ⨾ (hb S')⁻¹ ≡ (hb S)⁻¹ ⨾ ⦗E S⦘).
    { rewrite <- transp_eqv_rel, <- transp_seq.
      rewrite step_same_jf_hbE; eauto.
      rewrite hbE; auto.
      basic_solver 10. }
    rewrite <- restr_relE.
    rewrite basic_step_cf_restr; eauto. }
  { rewrite restr_relE, !seqA.
    rewrite step_same_jf_hbE; eauto.
    rewrite hbE; auto.
    arewrite (⦗E S⦘ ⨾ cf S' ⨾ ⦗E S⦘ ≡ cf S).
    { rewrite <- restr_relE.
      rewrite basic_step_cf_restr; eauto. }
    rewrite hbE; auto.
    basic_solver 10. }
  rewrite restr_relE, !seqA.
  arewrite (⦗E S⦘ ⨾ (hb S')⁻¹ ≡ (hb S)⁻¹ ⨾ ⦗E S⦘).
  { rewrite <- transp_eqv_rel, <- transp_seq. 
    rewrite step_same_jf_hbE; eauto.
    rewrite hbE; auto.
    basic_solver 10. }
  arewrite ((hb S') ⨾ ⦗E S⦘ ≡ ⦗E S⦘ ⨾ (hb S) ).
  { rewrite step_same_jf_hbE; eauto.
    rewrite hbE; auto.
    basic_solver 10. }
  arewrite (⦗E S⦘ ⨾ cf S' ⨾ ⦗E S⦘ ≡ cf S).
  { rewrite <- restr_relE.
    rewrite basic_step_cf_restr; eauto. }
  done.
Qed.

Lemma step_same_jf_jf_necf e e' S S'
      (BSTEP_ : basic_step e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (RMW' : rmw S' ≡ rmw S) 
      (wfE: ES.Wf S) 
      (JF_nECF : jf S ∩ ecf S ≡ ∅₂) :
  jf S' ∩ ecf S' ≡ ∅₂. 
Proof. 
  split; [|done].
  rewrite JF'.
  rewrite ES.jfE; auto.
  rewrite <- restr_relE.
  rewrite <- restr_inter_absorb_r.
  rewrite step_same_jf_ecf_restr; eauto.
  rewrite restr_relE.
  rewrite <- ES.jfE; auto.
  apply JF_nECF.
Qed.

(******************************************************************************)
(** ** Step properties *)
(******************************************************************************)

Lemma step_jf_mon e e' S S'
      (STEP : step_ e e' S S') :
  jf S ⊆ jf S'.
Proof. 
  unfold_step_ STEP;
    try cdes AJF;
    rewrite JF';
    basic_solver.
Qed.

Lemma step_ew_mon e e' S S'
      (STEP : step_ e e' S S') :
  ew S ⊆ ew S'.
Proof. 
  unfold_step_ STEP;
    try cdes AEW;
    rewrite EW';
    basic_solver.
Qed.  

Lemma step_co_mon e e' S S'
      (STEP : step_ e e' S S') :
  co S ⊆ co S'.
Proof. 
  unfold_step_ STEP;
    try cdes ACO;
    rewrite CO';
    basic_solver.
Qed.

Lemma step_rf_mon e e' S S'
      (BSTEP : basic_step e e' S S') 
      (STEP : step_ e e' S S') 
      (wfE: ES.Wf S) :
  rf S ⊆ rf S'.
Proof. 
  unfold ES.rf.
  intros x y [[z [EW JF]] nCF].
  split.
  { exists z. split.
    { eapply step_ew_mon; eauto. }
    eapply step_jf_mon; eauto. }
  intros CF. apply nCF.
  eapply basic_step_cf_restr
    with (S' := S'); eauto.
  red; splits; auto.
  { apply ES.ewE in EW; auto.
    generalize EW. basic_solver. }
  apply ES.jfE in JF; auto.
  generalize JF. basic_solver.
Qed.

Lemma step_fr_mon e e' S S'
      (BSTEP : basic_step e e' S S') 
      (STEP : step_ e e' S S') 
      (wfE: ES.Wf S) :
  fr S ⊆ fr S'.
Proof. 
  unfold ES.fr.
  apply seq_mori.
  { apply transp_mori.
    eapply step_rf_mon; eauto. }
  eapply step_co_mon; eauto.
Qed.  

Lemma step_ccE e e' S S'
      (BSTEP : basic_step e e' S S') 
      (STEP : step_ e e' S S') 
      (wfE: ES.Wf S) :
  cc S' ⨾ ⦗E S⦘ ≡ cc S.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold_step_ STEP;
  desf; eauto using add_jf_ccE, step_same_jf_ccE.
Qed.

Lemma step_vis_mon e e' S S'
      (BSTEP : basic_step e e' S S') 
      (STEP : step_ e e' S S')
      (wfE: ES.Wf S) :
  vis S ⊆₁ vis S'. 
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold vis. 
  intros x VIS.
  splits; desf.
  { eapply basic_step_acts_set_mon; eauto. }
  arewrite (eq x ⊆₁ E S ∩₁ eq x) by basic_solver.
  rewrite <- seq_eqv.
  rewrite <- seqA.
  rewrite step_ccE; eauto.
  etransitivity; [apply CCEW|].
  apply seq_mori.
  { eapply step_ew_mon; eauto. }
  apply clos_refl_sym_mori.
  eapply basic_step_sb_mon; eauto.
Qed.

Lemma step_hb lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (STEP : step_ e e' S S')
      (wfE: ES.Wf S) :
  hb S' ≡ hb S ∪ hb_delta S S' k e e'.
Proof. 
  cdes BSTEP_.
  assert (rmw_delta e None ≡ ∅₂) as RMW_None.
  { split; [|done]. step_solver. }
  unfold_step_ STEP.
  all : try by (
    erewrite step_same_jf_hb; eauto;
    rewrite RMW', nUPD; 
    unfold rmw_delta;
    basic_solver
  ).
  all : rewrite add_jf_hb; eauto.
  { basic_solver. }
  cdes AEW. type_solver.
Qed.

Lemma step_hb_dom e e' S S' 
      (BSTEP : basic_step e e' S S') 
      (STEP : step_ e e' S S')
      (wfE: ES.Wf S) :
  dom_rel (hb S') ⊆₁ E S ∪₁ eq e.
Proof. 
  cdes BSTEP.
  rewrite step_hb; eauto.
  rewrite dom_union.
  rewrite basic_step_hb_delta_dom; eauto.
  rewrite hbE; auto.
  basic_solver.
Qed. 

Lemma step_hbE e e' S S' 
      (BSTEP : basic_step e e' S S') 
      (STEP : step_ e e' S S')
      (wfE: ES.Wf S) :
  hb S' ⨾ ⦗E S⦘ ≡ hb S.
Proof. 
  cdes BSTEP.
  rewrite step_hb; eauto.
  relsf.
  rewrite basic_step_hb_deltaE; eauto.
  rewrite hbE; auto. basic_solver 5.
Qed. 

Lemma step_icf_jf_irr lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (STEP : step_ e e' S S')
      (wfE: ES.Wf S) :
  irreflexive (jf S' ⨾ icf S' ⨾ (jf S')⁻¹ ⨾ ew S') <->
    irreflexive (jf S ⨾ icf S ⨾ (jf S)⁻¹ ⨾ ew S) /\
    dom_rel (jf S' ⨾ ⦗eq e⦘) ∩₁ dom_rel (ew S ⨾ jf S ⨾ ⦗ES.cont_icf_dom S k⦘) ⊆₁ ∅.
Proof. 
  cdes BSTEP_.
  assert (basic_step e e' S S') as BSTEP.
  { red. do 5 eexists. eauto. }
  assert 
    (jf S ⨾ icf S' ⨾ (jf S)⁻¹ ≡ jf S ⨾ icf S ⨾ (jf S)⁻¹)
    as JF_ICF.
  { rewrite basic_step_icf; eauto. relsf.
    arewrite_false (jf S ⨾ icf_delta S k e ⨾ (jf S)⁻¹).
    2 : by rewrite union_false_r.
    unfold icf_delta. step_solver. }
  unfold_step_ STEP.
  { rewrite JF', EW'.
    seq_rewrite JF_ICF.
    rewrite !seqA.
    split; auto.
    2 : ins; desf.
    intros IRR.
    split; auto.
    step_solver. }
  { erewrite add_jf_icf_jf_irr; eauto.
    2 : rewrite EW'; by rewrite <- ES.ewE.
    apply Morphisms_Prop.and_iff_morphism; auto.
    cdes AJF. rewrite JF'.
    rewrite seq_union_l.
    arewrite_false (jf S ⨾ ⦗eq e⦘).
    { step_solver. }
    rewrite union_false_l.
    unfold jf_delta.
    split. 
    { unfolder. intros HH. ins. desf.
      apply HH. basic_solver 10. }
    intros HA HB. eapply HA.
    basic_solver 10. }
  { rewrite JF'.
    seq_rewrite JF_ICF.
    rewrite !seqA.
    split. 
    { intros IRR. split.
      2 : step_solver. 
      erewrite add_ew_mon; eauto.
      by left. }
    intros [IRR _].
    rewrite irreflexive_seqC.
    rewrite !seqA.
    rewrite ES.jfE; auto.
    rewrite !transp_seq, !transp_eqv_rel. 
    rewrite !seqA.
    arewrite (⦗E S⦘ ⨾ ew S' ⨾ ⦗E S⦘ ≡ ew S).
    { eapply add_ew_ewE; eauto. 
        by left. }
    generalize IRR. basic_solver 10. } 
  erewrite add_jf_icf_jf_irr; eauto.
  2 : eapply add_ew_ewE; eauto; basic_solver.  
  apply Morphisms_Prop.and_iff_morphism; auto.
  cdes AJF. rewrite JF'.
  rewrite seq_union_l.
  arewrite_false (jf S ⨾ ⦗eq e⦘).
  { step_solver. }
  rewrite union_false_l.
  unfold jf_delta.
  split. 
  { unfolder. intros HH. ins. desf.
    apply HH. basic_solver 10. }
  intros HA HB. eapply HA.
  basic_solver 10. 
Qed.

(******************************************************************************)
(** ** Step preserves executions lemma  *)
(******************************************************************************)

Lemma step_preserves_old_sw X e e' S S' 
      (WF : ES.Wf S)
      (EXEC : Execution.t S X) 
      (BSTEP : basic_step e e' S S')
      (STEP : step_ e e' S S') :
  dom_rel (sw S' ⨾ ⦗X⦘) ⊆₁ X.
Proof.
  cdes BSTEP; cdes BSTEP_.
  arewrite (sw S' ≡ sw S ∪ sw_delta S S' k e e').
  { destruct STEP as [FSTEP | [LSTEP | [SSTEP | USTEP]]].
    { cdes FSTEP. erewrite step_same_jf_sw; eauto.
      eapply basic_step_nupd_rmw; subst; eauto. }
    { cdes LSTEP. erewrite add_jf_sw; eauto.
      subst. basic_solver. }
    { cdes SSTEP. erewrite step_same_jf_sw; eauto.
      eapply basic_step_nupd_rmw; subst; eauto. }
    cdes USTEP. erewrite add_jf_sw; eauto.
    cdes AEW. type_solver. }
  relsf. splits.
  { apply EXEC. }
  arewrite (X ⊆₁ E S) by apply Execution.ex_inE; auto.
  erewrite basic_step_sw_deltaE; eauto. 
  basic_solver.
Qed.

Lemma step_preserves_execution X e e' S S' 
      (WF : ES.Wf S)
      (EXEC : Execution.t S X) 
      (BSTEP : basic_step e e' S S')
      (STEP : step_ e e' S S') :
  Execution.t S' X.
Proof.       
  cdes BSTEP; cdes BSTEP_.
  constructor.
  (* ex_inE : X ⊆₁ E S; *)
  { etransitivity; [apply EXEC |].
    eapply basic_step_acts_set_mon; eauto. }
  (* init_in_ex : Einit S ⊆₁ X *)
  { erewrite basic_step_acts_init_set; eauto. apply EXEC. } 
  (* ex_sb_prcl : dom_rel (sb S ⨾ ⦗X⦘) ⊆₁ X *)
  { rewrite SB'. 
    relsf. splits.
    { apply EXEC. }
    arewrite (X ⊆₁ E S) by apply Execution.ex_inE; auto.
    erewrite basic_step_sb_deltaE; eauto. 
    basic_solver. }
  (* ex_sw_prcl : dom_rel (sw S ⨾ ⦗X⦘) ⊆₁ X *)
  { eapply step_preserves_old_sw; eauto. }
  (* ex_rmw_fwcl : codom_rel (⦗X⦘ ⨾ rmw S) ⊆₁ X *)
  { rewrite RMW'. unfold rmw_delta.
    relsf. splits.
    { apply EXEC. }
    arewrite (X ⊆₁ E S) by apply Execution.ex_inE; auto. 
    step_solver. }
  (* ex_rf_compl : X ∩₁ R S ⊆₁ codom_rel (⦗X⦘ ⨾ rf S); *)
  { intros x [Xx Rx'].
    assert (R S x) as Rx.
    { eapply basic_step_r_in_r; eauto.
      split; auto.
      eapply Execution.ex_inE; eauto. }
    edestruct Execution.ex_rf_compl 
      as [y XRF]; eauto.
    { split; eauto. }
    apply seq_eqv_l in XRF.
    destruct XRF as [Xy RF].
    exists y. 
    apply seq_eqv_l. 
    split; auto.
    eapply step_rf_mon; eauto. }
  (* ex_ncf : ES.cf_free S X *)
  { red. 
    rewrite <- set_interK with (s := X).
    rewrite id_inter.
    arewrite (X ⊆₁ E S) at 2 by apply Execution.ex_inE; auto. 
    arewrite (X ⊆₁ E S) at 2 by apply Execution.ex_inE; auto. 
    arewrite (⦗E S⦘ ⨾ cf S' ⨾ ⦗E S⦘ ≡ cf S).
    { rewrite <- restr_relE. erewrite basic_step_cf_restr; eauto. }
    apply EXEC. }
  (* ex_vis : X ⊆₁ vis S *)
  etransitivity.
  { eapply Execution.ex_vis; eauto. }
  eapply step_vis_mon; eauto. 
Qed.

End Step.
