Require Import Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events AuxRel. 
Require Import AuxRel AuxDef EventStructure Consistency BasicStep.

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

Definition jf_delta w r : relation eventid := 
  singl_rel w r.

Hint Unfold jf_delta : ESStepDb.

Definition add_jf w r' S S' : Prop :=  
  ⟪ rE' : E S' r' ⟫ /\
  ⟪ rR' : R S' r' ⟫ /\
  ⟪ wE : E S w ⟫ /\
  ⟪ wW : W S w ⟫ /\
  ⟪ LOC : same_loc S' w r' ⟫ /\
  ⟪ VAL : same_val S' w r' ⟫ /\
  ⟪ JF' : jf S' ≡ jf S ∪ jf_delta w r' ⟫.

Definition ew_delta ws w : relation eventid := 
  (ws × eq w)^⋈.

Hint Unfold ew_delta : ESStepDb.

Definition add_ew ews w' S S' : Prop :=   
  ⟪ wE' : E S' w' ⟫ /\
  ⟪ wW' : W S' w' ⟫ /\
  ⟪ ewsE : ews ⊆₁ E S ⟫ /\
  ⟪ ewsW : ews ⊆₁ W S ⟫ /\
  ⟪ ewsRLX : ews ⊆₁ Rlx S ⟫ /\
  (* TODO: replace it with `ews ⊆₁ same_lab S' w'` ??? *)
  ⟪ ewsLOC : ews ⊆₁ same_loc S' w' ⟫ /\
  ⟪ ewsVAL : ews ⊆₁ same_val S' w' ⟫ /\
  (* \End TODO *)
  ⟪ ewsCFw : ews ⊆₁ cf S' w' ⟫ /\
  ⟪ ewsCF : ews × ews \ eq ⊆ cf S ⟫ /\
  ⟪ ewsEW : ews × ews \ eq ⊆ ew S ⟫ /\
  ⟪ ewsEWprcl : dom_rel (ew S ⨾ ⦗ews⦘) ⊆₁ ews ⟫ /\
  ⟪ EW' : ew S' ≡ ew S ∪ ew_delta ews w' ⟫. 

Definition co_ws w' S S' := 
  E S ∩₁ W S ∩₁ same_loc S' w' \₁ cf S' w'.

Definition co_delta ws w' S S' : relation eventid := 
  dom_rel ((co S)^? ⨾ (ew S)^? ⨾ ⦗ws⦘) × eq w' ∪ 
          eq w' × (co_ws w' S S' \₁ dom_rel ((co S)^? ⨾ (ew S)^? ⨾ ⦗ws⦘)).

Hint Unfold co_ws co_delta : ESStepDb.

Definition add_co ws w' S S' : Prop := 
  ⟪ wE' : E S' w' ⟫ /\
  ⟪ wW' : W S' w' ⟫ /\  
  ⟪ wsCO : ws ⊆₁ co_ws w' S S' ⟫ /\
  ⟪ CO' : co S' ≡ co S ∪ co_delta ws w' S S' ⟫.

Definition t_fence
           (e  : eventid)
           (e' : option eventid)
           (S S' : ES.t) : Prop :=
  ⟪ ENONE : e' = None ⟫ /\
  ⟪ FF  : F S' e ⟫ /\
  ⟪ JF' : jf S' ≡ jf S ⟫ /\
  ⟪ EW' : ew S' ≡ ew S ⟫ /\
  ⟪ CO' : co S' ≡ co S ⟫.

Definition t_load
           (e  : eventid)
           (e' : option eventid)
           (S S' : ES.t) : Prop :=
  exists w, 
    ⟪ ENONE : e' = None ⟫ /\
    ⟪ AJF : add_jf w e S S' ⟫ /\
    ⟪ EW' : ew S' ≡ ew S ⟫ /\
    ⟪ CO' : co S' ≡ co S ⟫.

Definition t_store
           (e  : eventid)
           (e' : option eventid)
           (S S' : ES.t) : Prop :=
  exists ews ws, 
    ⟪ ENONE : e' = None ⟫ /\
    ⟪ JF' : jf S' ≡ jf S ⟫ /\
    ⟪ AEW : add_ew ews e S S' ⟫ /\
    ⟪ ACO : add_co ws e S S' ⟫.

Definition t_update
           (e  : eventid)
           (e' : option eventid)
           (S S' : ES.t) : Prop := 
  exists w ews ws w',
    ⟪ ESOME : e' = Some w' ⟫ /\
    ⟪ AJF : add_jf w e S S' ⟫ /\
    ⟪ AEW : add_ew ews w' S S' ⟫ /\
    ⟪ ACO : add_co ws w' S S' ⟫.

Definition t_ e e' S S' :=
  t_fence e e' S S' \/ t_load e e' S S' \/ t_store e e' S S' \/ t_update e e' S S'.

Definition t (m : model) (S S' : ES.t) : Prop := exists e e',
  ⟪ TT  : t_ e e' S S' ⟫ /\
  ⟪ BSTEP : ESBasicStep.t e e' S S' ⟫ /\
  ⟪ CON : @es_consistent S' m ⟫.

(******************************************************************************)
(** ** Deltas definitions *)
(******************************************************************************)

Definition jfi_delta S k w r : relation eventid := 
  ⦗ES.cont_sb_dom S k⦘ ⨾ jf_delta w r.

Definition jfe_delta S k w r : relation eventid := 
  ⦗set_compl (ES.cont_sb_dom S k)⦘ ⨾ jf_delta w r.

Definition sw_delta S S' k e e' : relation eventid := 
  release S ⨾ (jf S ⨾ ESBasicStep.sb_delta S k e e' ⨾ ⦗F S'⦘ ∪ jf S' ⨾ ⦗eq e⦘) ⨾ ⦗Acq S'⦘.

Definition hb_delta S S' k e e' : relation eventid := 
  (hb S)^? ⨾ (ESBasicStep.sb_delta S k e e' ∪ sw_delta S S' k e e') ⨾ (eq e × eq_opt e')^? . 

Hint Unfold jfi_delta jfe_delta sw_delta hb_delta : ESStepDb.

(******************************************************************************)
(** ** Deltas lemmas *)
(******************************************************************************)

Lemma step_add_jf_jf_delta_dom w e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  dom_rel (jf_delta w e) ⊆₁ E S.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  ESBasicStep.step_solver.
Qed.  

Lemma step_add_jf_jf_deltaE w e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  jf_delta w e ⨾ ⦗E S⦘ ≡ ∅₂. 
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  split; [|done].
  ESBasicStep.step_solver.
Qed.  

Lemma step_add_jf_jfi_delta_dom lang k k' st st' w e e' S S'
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  dom_rel (jfi_delta S k w e) ⊆₁ E S.
Proof. 
  cdes AJF; cdes BSTEP_.
  ESBasicStep.step_solver.
Qed.  

Lemma step_add_jf_jfe_delta_dom lang k k' st st' w e e' S S'
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  dom_rel (jfe_delta S k w e) ⊆₁ E S.
Proof. 
  cdes AJF; cdes BSTEP_.
  ESBasicStep.step_solver.
Qed.

Lemma step_add_jf_jfi_deltaE lang k k' st st' w e e' S S'
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  jfi_delta S k w e ⨾ ⦗E S⦘ ≡ ∅₂.
Proof. 
  cdes AJF; cdes BSTEP_.
  split; [|done].
  ESBasicStep.step_solver.
Qed.  

Lemma step_add_jf_jfe_deltaE lang k k' st st' w e e' S S'
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  jfe_delta S k w e ⨾ ⦗E S⦘ ≡ ∅₂.
Proof. 
  cdes AJF; cdes BSTEP_.
  split; [|done].
  ESBasicStep.step_solver.
Qed.  

Lemma basic_step_sw_delta_dom lang k k' st st' e e' S S'
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (wfE: ES.Wf S) :
  dom_rel (sw_delta S S' k e e') ⊆₁ E S.
Proof. 
  cdes BSTEP_.
  ESBasicStep.step_solver.
Qed.

Lemma basic_step_sw_deltaE lang k k' st st' e e' S S'
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (wfE: ES.Wf S) :
  sw_delta S S' k e e' ⨾ ⦗E S⦘ ≡ ∅₂.
Proof. 
  cdes BSTEP_.
  split; [|done]. 
  unfold sw_delta.
  ESBasicStep.step_solver.
Qed.

Lemma basic_step_hb_delta_dom lang k k' st st' e e' S S' 
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (wfE: ES.Wf S) :
  dom_rel (hb_delta S S' k e e') ⊆₁ E S ∪₁ eq e.
Proof. 
  cdes BSTEP_.
  unfold hb_delta.
  rewrite crE, !seq_union_l, seq_id_l. 
  rewrite !dom_union, !dom_seq.
  rewrite !set_subset_union_l.
  splits. 
  { eapply ESBasicStep.basic_step_sb_delta_dom; eauto. }
  all : ESBasicStep.step_solver.
Qed. 

Lemma basic_step_hb_deltaE lang k k' st st' e e' S S' 
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (wfE: ES.Wf S) :
  hb_delta S S' k e e' ⨾ ⦗E S⦘ ≡ ∅₂.
Proof. 
  cdes BSTEP_.
  split; [|done].
  ESBasicStep.step_solver.
Qed.

Lemma basic_step_hb_delta_alt lang k k' st st' e e' S S'
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (wfE: ES.Wf S) :
  hb_delta S S' k e e' ≡ 
    (hb S)^? ⨾ ((ESBasicStep.sb_delta S k e e' ∪ sw_delta S S' k e e') ⨾ (hb S)^?)⁺.
Proof. 
  cdes BSTEP_.
  unfold hb_delta. 
  apply seq_more; auto.
  rewrite !crE. relsf.
  rewrite hbE; auto.
  arewrite_false (ESBasicStep.sb_delta S k e e' ⨾ ⦗E S⦘).
  { eapply ESBasicStep.basic_step_sb_deltaE; eauto. }
  arewrite_false (sw_delta S S' k e e' ⨾ ⦗E S⦘).
  { eapply basic_step_sw_deltaE; eauto. }
  relsf.
  rewrite ct_begin, rtE. relsf.
  rewrite !unionA.
  do 3 (apply union_more; auto).
  { rewrite ct_begin, rtE. relsf.
    rewrite <- !seqA.
    arewrite_false (ESBasicStep.sb_delta S k e e' ⨾ sw_delta S S' k e e'). 
    { ESBasicStep.step_solver. }
    rewrite <- !seqA.
    arewrite 
      (ESBasicStep.sb_delta S k e e' ⨾ ESBasicStep.sb_delta S k e e' ≡ 
                            ESBasicStep.sb_delta S k e e' ⨾ eq e × eq_opt e').
    { rewrite dom_rel_helper with (r := ESBasicStep.sb_delta S k e e') at 2.
      2 : eapply ESBasicStep.basic_step_sb_delta_dom; eauto.
      rewrite id_union. relsf. 
      arewrite_false (ESBasicStep.sb_delta S k e e' ⨾ ⦗E S⦘).
      { ESBasicStep.step_solver. }
      relsf.
      apply seq_more; auto.
      unfold ESBasicStep.sb_delta. 
      rewrite cross_union_r. relsf.
      arewrite_false (⦗eq e⦘ ⨾ ES.cont_sb_dom S k × eq e). 
      { ESBasicStep.step_solver. }
      arewrite_false (⦗eq e⦘ ⨾ ES.cont_sb_dom S k × eq_opt e'). 
      { ESBasicStep.step_solver. }
      basic_solver 20. }
    relsf.
    rewrite ct_begin, rtE. relsf.

    arewrite_false (eq e × eq_opt e' ⨾ ESBasicStep.sb_delta S k e e').
    { ESBasicStep.step_solver. }
    arewrite_false (eq e × eq_opt e' ⨾ ESBasicStep.sb_delta S k e e').
    { ESBasicStep.step_solver. }
    arewrite_false (eq e × eq_opt e' ⨾ sw_delta S S' k e e').
    { ESBasicStep.step_solver. }
    arewrite_false (eq e × eq_opt e' ⨾ sw_delta S S' k e e').
    { ESBasicStep.step_solver. }
    basic_solver 10. }

  rewrite ct_begin, rtE. relsf.
  rewrite <- !seqA.
  arewrite_false (sw_delta S S' k e e' ⨾ sw_delta S S' k e e'). 
  { unfold sw_delta. ESBasicStep.step_solver. }
  rewrite <- !seqA.
  arewrite 
    (sw_delta S S' k e e' ⨾ ESBasicStep.sb_delta S k e e' ≡ 
              sw_delta S S' k e e' ⨾ eq e × eq_opt e').
  { rewrite dom_rel_helper with (r := ESBasicStep.sb_delta S k e e').
    2 : eapply ESBasicStep.basic_step_sb_delta_dom; eauto.
    rewrite id_union. relsf. 
    arewrite_false (sw_delta S S' k e e' ⨾ ⦗E S⦘).
    { unfold sw_delta. ESBasicStep.step_solver. }
    unfold ESBasicStep.sb_delta. 
    rewrite cross_union_r. relsf.
    arewrite_false (⦗eq e⦘ ⨾ ES.cont_sb_dom S k × eq e).
    { ESBasicStep.step_solver. }
    arewrite_false (⦗eq e⦘ ⨾ ES.cont_sb_dom S k × eq_opt e').
    { ESBasicStep.step_solver. }
    basic_solver 10. }
  
  relsf.
  rewrite ct_begin, rtE. relsf.
  arewrite_false (eq e × eq_opt e' ⨾ ESBasicStep.sb_delta S k e e').
  { ESBasicStep.step_solver. }
  arewrite_false (eq e × eq_opt e' ⨾ ESBasicStep.sb_delta S k e e').
  { ESBasicStep.step_solver. }
  arewrite_false (eq e × eq_opt e' ⨾ sw_delta S S' k e e').
  { ESBasicStep.step_solver. }
  arewrite_false (eq e × eq_opt e' ⨾ sw_delta S S' k e e').
  { ESBasicStep.step_solver. }
  basic_solver 10.   
Qed.

(******************************************************************************)
(** ** Auxiliary lemmas *)
(******************************************************************************)

Lemma basic_step_w_sb_loc_wE e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (wfE: ES.Wf S) :
  ⦗E S' ∩₁ W S'⦘ ⨾ (sb S' ∩ same_loc S')^? ⨾ ⦗W S'⦘ ⨾ ⦗E S⦘ ≡ 
  ⦗E S  ∩₁ W S ⦘ ⨾ (sb S  ∩ same_loc S )^? ⨾ ⦗W S ⦘.
Proof. 
  cdes BSTEP. cdes BSTEP_.
  arewrite (⦗W S'⦘ ⨾ ⦗E S⦘ ≡ ⦗E S⦘ ⨾ ⦗W S⦘). 
  { rewrite seq_eqvC.
    rewrite !seq_eqv.
    apply eqv_rel_more.
    eapply ESBasicStep.type_step_eq_dom; eauto. }
  arewrite ((sb S' ∩ same_loc S')^? ⨾ ⦗E S⦘ ≡ ⦗E S⦘ ⨾ (sb S ∩ same_loc S)^?).
  { rewrite !crE. relsf.
    apply union_more; auto.
    rewrite <- lib.AuxRel.seq_eqv_inter_lr.
    rewrite ESBasicStep.basic_step_sbE; eauto.
    rewrite ES.sbE at 1; auto.
    rewrite <- restr_relE, <- restr_inter_absorb_r.
    rewrite ESBasicStep.basic_step_same_loc_restr; eauto.
    rewrite restr_inter_absorb_r, restr_relE.
    rewrite ES.sbE; auto.
    basic_solver 20. }
  arewrite (⦗E S' ∩₁ W S'⦘ ⨾ ⦗E S⦘ ≡ ⦗E S ∩₁ W S⦘).
  { rewrite seq_eqv.
    rewrite ESBasicStep.basic_step_acts_set; eauto.
    relsf.
    arewrite (eq e ∩₁ W S' ∩₁ E S ≡₁ ∅).
    { split; [|done]. ESBasicStep.step_solver. }
    arewrite (eq_opt e' ∩₁ W S' ∩₁ E S ≡₁ ∅).
    { split; [|done]. ESBasicStep.step_solver. }
    relsf. apply eqv_rel_more.
    arewrite (E S ∩₁ W S' ∩₁ E S ≡₁ E S ∩₁ W S').
    { basic_solver. }
    eapply ESBasicStep.type_step_eq_dom; eauto. }
  done.
Qed.

(*******************************************************)
(* Lemmas about equality of types and modes of events
   after a basic step.                                 *)
(*******************************************************)

Hint Unfold eq_dom Events.loc Events.mod Events.xmod is_r is_w is_f is_acq is_rel is_rlx is_acqrel R_ex
     is_only_pln is_sc is_ra is_xacq
     same_lab_u2v_dom same_label_u2v :
  same_lab_unfoldDb.

Ltac basic_step_same_lab S S' :=
  repeat autounfold with same_lab_unfoldDb;
  intros x [EX REL];
  assert (lab S' x = lab S x) as HH;
  [eapply ESBasicStep.basic_step_lab_eq_dom; eauto |
    try (by rewrite HH in REL);
    try (by rewrite <- HH in REL)].

Lemma basic_step_rel_in_rel e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') :
  E S ∩₁ Rel S' ⊆₁ Rel S.
Proof. basic_step_same_lab S S'. Qed.

Lemma basic_step_acq_in_acq e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') :
  E S ∩₁ Acq S' ⊆₁ Acq S.
Proof. basic_step_same_lab S S'. Qed.

Lemma basic_step_sc_in_sc e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') :
  E S ∩₁ Sc S' ⊆₁ Sc S.
Proof. basic_step_same_lab S S'. Qed.

Lemma basic_step_r_in_r e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') :
  E S ∩₁ R S' ⊆₁ R S.
Proof. basic_step_same_lab S S'. Qed.

Lemma basic_step_w_in_w e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') :
  E S ∩₁ W S' ⊆₁ W S.
Proof. basic_step_same_lab S S'. Qed.

Lemma basic_step_f_in_f e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') :
  E S ∩₁ F S' ⊆₁ F S.
Proof. basic_step_same_lab S S'. Qed.

Lemma basic_step_rel_eq_rel e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') :
  E S ∩₁ Rel S' ≡₁ E S ∩₁ Rel S.
Proof. split; basic_step_same_lab S S'. Qed.

Lemma basic_step_acq_eq_acq e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') :
  E S ∩₁ Acq S' ≡₁ E S ∩₁ Acq S.
Proof. split; basic_step_same_lab S S'. Qed.

Lemma basic_step_sc_eq_sc e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') :
  E S ∩₁ Sc S' ≡₁ E S ∩₁ Sc S.
Proof. split; basic_step_same_lab S S'. Qed.

Lemma basic_step_r_eq_r e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') :
  E S ∩₁ R S' ≡₁ E S ∩₁ R S.
Proof. split; basic_step_same_lab S S'. Qed.

Lemma basic_step_w_eq_w e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') :
  E S ∩₁ W S' ≡₁ E S ∩₁ W S.
Proof. split; basic_step_same_lab S S'. Qed.

Lemma basic_step_f_eq_f e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') :
  E S ∩₁ F S' ≡₁ E S ∩₁ F S.
Proof. split; basic_step_same_lab S S'. Qed.

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
  : same_lab_solveDb.

Lemma basic_step_rel_f_sbE e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (wfE: ES.Wf S) :
  ⦗Rel S'⦘ ⨾ (⦗F S'⦘ ⨾ sb S')^? ⨾ ⦗E S⦘ ≡ 
  ⦗Rel S ⦘ ⨾ (⦗F S ⦘ ⨾ sb S )^? ⨾ ⦗E S⦘.
Proof. 
  arewrite ((⦗F S'⦘ ⨾ sb S')^? ⨾ ⦗E S⦘ ≡ ⦗E S⦘ ⨾ (⦗F S⦘ ⨾ sb S)^?).
  { rewrite !crE. relsf.
    apply union_more; auto.
    rewrite !seqA.
    rewrite ESBasicStep.basic_step_sbE; eauto.
    rewrite ES.sbE; auto.
    arewrite (⦗F S'⦘ ⨾ ⦗E S⦘ ≡ ⦗E S⦘ ⨾ ⦗F S⦘).
    { rewrite !seq_eqv.
      apply eqv_rel_more.
      rewrite set_interC.
      eapply ESBasicStep.type_step_eq_dom; eauto. }
    basic_solver. }
  arewrite (⦗Rel S'⦘ ⨾ ⦗E S⦘ ≡ ⦗Rel S⦘ ⨾ ⦗E S⦘).
  { rewrite !seq_eqv.
    apply eqv_rel_more.
    rewrite set_interC.
    autorewrite with same_lab_solveDb; eauto.
    basic_solver. }
  rewrite ES.sbE; auto.
  basic_solver 10.
Qed.

Lemma basic_step_jf_sb_f_acq e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (WF: ES.Wf S) :
  jf S ⨾ (sb S ⨾ ⦗F S'⦘)^? ⨾ ⦗Acq S'⦘ ≡ jf S ⨾ (sb S ⨾ ⦗F S⦘)^? ⨾ ⦗Acq S⦘.
Proof. 
  arewrite (sb S ⨾ ⦗F S'⦘ ≡ sb S ⨾ ⦗F S⦘).
  { rewrite ES.sbE; auto. rewrite !seqA.
    arewrite (⦗E S⦘ ⨾ ⦗F S'⦘ ≡ ⦗E S⦘ ⨾ ⦗F S⦘); auto.
    rewrite !seq_eqv.
    apply eqv_rel_more.
    eapply ESBasicStep.type_step_eq_dom; eauto. }
  assert (jf S ⨾ (sb S ⨾ ⦗F S⦘)^? ≡
          jf S ⨾ (sb S ⨾ ⦗F S⦘)^? ⨾ ⦗E S⦘) as HH.
  { split; [|basic_solver 10].
    rewrite (dom_r WF.(ES.jfE)).
    rewrite (dom_r WF.(ES.sbE)).
    basic_solver 20. }
  seq_rewrite HH. symmetry.
  seq_rewrite HH. rewrite !seqA.
  rewrite <- !id_inter.
  rewrite basic_step_acq_eq_acq with (S':=S'); eauto.
Qed.

(******************************************************************************)
(** ** Step (add_jf) properties *)
(******************************************************************************)

Lemma step_add_jf_jf_dom w e e' S S'
      (BSTEP : ESBasicStep.t e e' S S')
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  dom_rel (jf S') ⊆₁ E S.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite JF', dom_union. 
  rewrite wf.(ES.jfE).
  rewrite step_add_jf_jf_delta_dom; eauto.
  basic_solver.
Qed.

Lemma step_add_jf_jfE w e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  jf S' ⨾ ⦗E S⦘ ≡ jf S.
Proof.   
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite JF'. 
  rewrite seq_union_l.
  rewrite step_add_jf_jf_deltaE; eauto.
  rewrite ES.jfE; auto. basic_solver 5.
Qed.

Lemma step_add_jf_jfi lang k k' st st' w e e' S S'
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  jfi S' ≡ jfi S ∪ jfi_delta S k w e.
Proof. 
  cdes AJF; cdes BSTEP_.
  unfold ES.jfi, jfi_delta.
  rewrite SB', JF'.
  rewrite inter_union_l, !inter_union_r.
  arewrite_false (jf S ∩ ESBasicStep.sb_delta S k e e').
  { ESBasicStep.step_solver. }
  arewrite_false (jf_delta w e ∩ sb S). 
  { ESBasicStep.step_solver. } 
  relsf.
  apply union_more; auto.
  autounfold with ESStepDb.
  rewrite inter_union_r.
  arewrite_false (singl_rel w e ∩ (ES.cont_sb_dom S k ∪₁ eq e) × eq_opt e').
  { ESBasicStep.step_solver. }
  basic_solver 10.
Qed.

Lemma step_add_jf_jfe lang k k' st st' w e e' S S'
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  jfe S' ≡ jfe S ∪ jfe_delta S k w e.
Proof. 
  cdes AJF; cdes BSTEP_.
  unfold ES.jfe, jfe_delta.
  rewrite SB', JF'.
  rewrite minus_union_l, !minus_union_r.
  erewrite minus_disjoint 
    with (r := jf S) (r' := ESBasicStep.sb_delta S k e e').
  2 : { split; [|done]. ESBasicStep.step_solver. }
  erewrite minus_disjoint 
    with (r := jf_delta w e) (r' := sb S).
  2 : { split; [|done]. ESBasicStep.step_solver. }
  apply union_more.
  { basic_solver. }
  autounfold with ESStepDb.
  rewrite !minus_union_r.
  erewrite minus_disjoint 
    with (r := singl_rel w e) (r' := (ES.cont_sb_dom S k ∪₁ eq e) × eq_opt e').
  2 : { split; [|done]. ESBasicStep.step_solver. }
  rewrite minus_inter_compl.
  rewrite !interC with (r1 := singl_rel w e).
  rewrite !interA, !interK.
  split; [basic_solver|].
  unfolder. ins. desc.
  splits; auto. 
  red. ins. desc. auto.
Qed.

Lemma step_add_jf_jfi_dom w e e' S S'
      (BSTEP : ESBasicStep.t e e' S S')
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  dom_rel (jfi S') ⊆₁ E S.
Proof. 
  unfold ES.jfi.
  unfolder; ins; desf.
  eapply step_add_jf_jf_dom; eauto. 
  basic_solver.
Qed.

Lemma step_add_jf_jfe_dom w e e' S S'
      (BSTEP : ESBasicStep.t e e' S S')
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  dom_rel (jfe S') ⊆₁ E S.
Proof. 
  unfold ES.jfe.
  unfolder; ins; desf.
  eapply step_add_jf_jf_dom; eauto. 
  basic_solver.
Qed.

Lemma step_add_jf_jfiE w e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  jfi S' ⨾ ⦗E S⦘ ≡ jfi S.
Proof.   
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite step_add_jf_jfi; eauto.
  rewrite seq_union_l.
  rewrite step_add_jf_jfi_deltaE; eauto.
  rewrite ES.jfiE; auto. basic_solver 5.
Qed.

Lemma step_add_jf_jfeE w e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  jfe S' ⨾ ⦗E S⦘ ≡ jfe S.
Proof.   
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite step_add_jf_jfe; eauto.
  rewrite seq_union_l.
  rewrite step_add_jf_jfe_deltaE; eauto.
  rewrite ES.jfeE; auto. basic_solver 5.
Qed.

Lemma step_add_jf_sb_jf lang k k' st st' w e e' S S'
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (wfE: ES.Wf S) :
  (sb S' ∪ jf S')＊ ≡ 
    (sb S ∪ jf S)＊ ⨾ 
      (ESBasicStep.sb_delta S k e e' ∪ singl_rel w e ∪ eq w × eq_opt e')^?. 
Proof. 
  cdes AJF; cdes BSTEP_.
  assert (ESBasicStep.t e e' S S') as BSTEP.
  { econstructor. eauto. }
  autounfold with ESStepDb in *.
  rewrite SB', JF'. 
  arewrite 
    (sb S ∪ ESBasicStep.sb_delta S k e e' ∪ (jf S ∪ singl_rel w e) ≡
      ESBasicStep.sb_delta S k e e' ∪ singl_rel w e ∪ (sb S ∪ jf S))
    by basic_solver.
  erewrite rt_unionE. 
  apply seq_more; auto.
  rewrite rt_begin with (r := sb S ∪ jf S).
  rewrite seq_union_r, seq_id_r. 
  arewrite_false 
    ((ESBasicStep.sb_delta S k e e' ∪ singl_rel w e) ⨾ (sb S ∪ jf S)).
  { ESBasicStep.step_solver. }
  relsf. 
  rewrite rtE, crE.
  apply union_more; auto.
  (* unroll transitive closure up to 3 iterations *)
  do 3 rewrite ct_begin, rtE.
  rewrite !seq_union_r, !seq_id_r.
  rewrite <- !seqA.
  arewrite 
    ((ESBasicStep.sb_delta S k e e' ∪ singl_rel w e)
     ⨾ (ESBasicStep.sb_delta S k e e' ∪ singl_rel w e) ≡ 
     ES.cont_sb_dom S k × eq_opt e' ∪ eq w × eq_opt e'). 
  { unfold ESBasicStep.sb_delta.
    rewrite !seq_union_l. 
    arewrite_false 
      ((ES.cont_sb_dom S k ∪₁ eq e) × eq_opt e'
      ⨾ (ES.cont_sb_dom S k × eq e ∪ 
                        (ES.cont_sb_dom S k ∪₁ eq e) × eq_opt e' ∪ singl_rel w e)). 
    { arewrite (singl_rel w e ⊆ E S × eq e).
      { basic_solver. }
      ESBasicStep.step_solver. }
    rewrite cross_union_r. rewrite !seq_union_r.
    arewrite_false 
      (ES.cont_sb_dom S k × eq e ⨾ ES.cont_sb_dom S k × eq_opt e').
    { ESBasicStep.step_solver. }
    arewrite_false
     (ES.cont_sb_dom S k × eq e ⨾ singl_rel w e).
    { arewrite (singl_rel w e ⊆ E S × eq e).
      { basic_solver. }
      ESBasicStep.step_solver. }
    arewrite_false
      (singl_rel w e ⨾ ES.cont_sb_dom S k × eq e).
    { ESBasicStep.step_solver. }
    arewrite_false
      (singl_rel w e ⨾ ES.cont_sb_dom S k × eq_opt e').
    { ESBasicStep.step_solver. }
    arewrite_false
      (ES.cont_sb_dom S k × eq e ⨾ ES.cont_sb_dom S k × eq e).
    { ESBasicStep.step_solver. }
    arewrite_false
      (singl_rel w e ⨾ singl_rel w e).
    { arewrite (singl_rel w e ⊆ E S × eq e).
      { basic_solver. }
      ESBasicStep.step_solver. }
    basic_solver 10. }
  rewrite <- seqA.
  arewrite_false 
    ((ES.cont_sb_dom S k × eq_opt e' ∪ eq w × eq_opt e')
        ⨾ (ESBasicStep.sb_delta S k e e' ∪ singl_rel w e)).
  { arewrite (singl_rel w e ⊆ E S × eq e).
    { basic_solver. }
    ESBasicStep.step_solver. }
  unfold ESBasicStep.sb_delta. 
  basic_solver 10. 
Qed.

Lemma step_add_jf_sb_jfE w e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (AJF : add_jf w e S S') 
      (wfE: ES.Wf S) :
  (sb S' ∪ jf S')＊ ⨾ ⦗E S⦘ ≡ (sb S ∪ jf S)＊ ⨾ ⦗E S⦘.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  erewrite step_add_jf_sb_jf; eauto.
  rewrite crE. relsf.
  rewrite <- union_false_r with (r := (sb S ∪ jf S)＊ ⨾ ⦗E S⦘) at 2. 
  apply union_more; auto.
  split; [|done].
  ESBasicStep.step_solver.
Qed.

Lemma step_add_jf_sb_jf_dom w e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (AJF : add_jf w e S S') 
      (wfE: ES.Wf S) :
  dom_rel ((sb S' ∪ jf S')＊ ⨾ ⦗E S⦘) ⊆₁ E S.
Proof. 
  rewrite step_add_jf_sb_jfE; eauto.
  rewrite rtE, seq_union_l, seq_id_l. 
  rewrite ES.sbE, ES.jfE; auto.
  rewrite <- seq_union_r. 
  rewrite inclusion_ct_seq_eqv_l.
  basic_solver.
Qed.

Lemma step_add_jf_cc lang k k' st st' w e e' S S'
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (wfE: ES.Wf S) :
  cc S' ≡ cc S ∪ 
     cf S' ∩ 
     (jfe S ⨾ (sb S ∪ jf S)＊ ⨾ 
          (jfe S ⨾ ESBasicStep.sb_delta S k e e' ∪ jfe_delta S k w e ⨾ (eq e × eq_opt e')^?)).
Proof. 
  cdes AJF; cdes BSTEP_.
  assert (ESBasicStep.t e e' S S') as BSTEP.
  { econstructor. eauto. }
  unfold cc at 1. 
  erewrite dom_rel_helper with (r := jfe S') at 2.
  2 : eapply step_add_jf_jfe_dom; eauto.
  rewrite !seqA. 
  rewrite <- seqA with (r2 := ⦗E S⦘).
  erewrite dom_rel_helper with (r := (sb S' ∪ jf S')＊ ⨾ ⦗E S⦘).
  2 : eapply step_add_jf_sb_jf_dom; eauto.
  rewrite step_add_jf_sb_jfE; eauto.
  rewrite !seqA. 
  rewrite <- !seqA with (r2 := ⦗E S⦘).
  rewrite step_add_jf_jfeE; eauto.
  rewrite !seqA.
  rewrite <- !seqA with (r1 := ⦗E S⦘).
  erewrite <- dom_rel_helper with (r := jfe S').
  2 : eapply step_add_jf_jfe_dom; eauto.  
  rewrite SB'. 
  rewrite step_add_jf_jfe with (S' := S') at 1; eauto.
  rewrite cr_union_l. relsf.
  rewrite !inter_union_r.
  rewrite unionA.
  apply union_more.
  { rewrite ESBasicStep.basic_step_cf; eauto. 
    autounfold with ESStepDb.
    rewrite <- unionA, !inter_union_l, unionA.
    rewrite <- union_false_r with (r := cc S).
    apply union_more.
    { by unfold cc. }
    split; [|done].
    ESBasicStep.step_solver. }
  rewrite unionC, unionA.
  apply union_more; auto.
  rewrite !crE. relsf.
  arewrite_false (jfe_delta S k w e ⨾ sb S). 
  { autounfold with ESStepDb. 
    arewrite (singl_rel w e ⊆ E S × eq e).
    { basic_solver. }
    ESBasicStep.step_solver. }
  relsf.
  rewrite !inter_union_r.
  rewrite unionC.
  apply union_more; auto.
  apply inter_rel_more; auto.  
  do 2 (apply seq_more; auto).  
  autounfold with ESStepDb. 
  rewrite cross_union_r.
  relsf. rewrite !seqA.
  arewrite_false (singl_rel w e ⨾ ES.cont_sb_dom S k × eq e).
  { arewrite (singl_rel w e ⊆ E S × eq e).
    { basic_solver. }
    ESBasicStep.step_solver. }
  arewrite_false (singl_rel w e ⨾ ES.cont_sb_dom S k × eq_opt e').
  { arewrite (singl_rel w e ⊆ E S × eq e).
    { basic_solver. }
    ESBasicStep.step_solver. }
  basic_solver 10.
Qed.  

Lemma step_add_jf_ccE w e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (AJF : add_jf w e S S') 
      (wfE: ES.Wf S) :
  cc S' ⨾ ⦗E S⦘ ≡ cc S.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite step_add_jf_cc; eauto.
  rewrite seq_union_l.
  rewrite interC.
  rewrite <- lib.AuxRel.seq_eqv_inter_lr.
  rewrite !seqA, seq_union_l.
  rewrite !seqA.
  arewrite_false 
    (ESBasicStep.sb_delta S k e e' ⨾ ⦗E S⦘).
  { ESBasicStep.step_solver. }
  arewrite_false
   (jfe_delta S k w e ⨾ (eq e × eq_opt e')^? ⨾ ⦗E S⦘).
  { autounfold with ESStepDb. 
    arewrite (singl_rel w e ⊆ E S × eq e).
    { basic_solver. }
    ESBasicStep.step_solver. }
  relsf.
  rewrite ccE. basic_solver.
Qed.

Lemma step_add_jf_jf_rmw w e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (AJF : add_jf w e S S') 
      (wfE: ES.Wf S) :
  jf S' ⨾ rmw S' ≡ jf S ⨾ rmw S ∪ eq w × eq_opt e'.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite JF', RMW'.
  relsf. rewrite unionA.
  apply union_more; auto.
  arewrite_false (jf_delta w e ⨾ rmw S).
  { ESBasicStep.step_solver. }
  arewrite_false (jf S ⨾ ESBasicStep.rmw_delta e e').
  { ESBasicStep.step_solver. }
  autounfold with ESStepDb.
  basic_solver 10.
Qed.  

Lemma step_add_jf_jf_rmwE w e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (AJF : add_jf w e S S') 
      (wfE: ES.Wf S) :
  jf S' ⨾ rmw S' ⨾ ⦗E S⦘ ≡ jf S ⨾ rmw S.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite <- seqA.
  rewrite step_add_jf_jf_rmw; eauto.
  relsf.
  arewrite_false (eq w × eq_opt e' ⨾ ⦗E S⦘).
  { ESBasicStep.step_solver. }
  rewrite ES.rmwE; auto. basic_solver 10.
Qed.

Lemma step_add_jf_rsE w e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (AJF : add_jf w e S S') 
      (wfE: ES.Wf S) :
  rs S' ⨾ ⦗E S⦘ ≡ rs S ⨾ ⦗E S⦘.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  unfold rs at 1. rewrite !seqA.
  arewrite ((jf S' ⨾ rmw S')＊ ⨾ ⦗E S⦘ ≡ (jf S ⨾ rmw S)＊ ⨾ ⦗E S⦘).
  { rewrite !rtE. relsf.
    eapply union_more; auto.
    split. 
    { rewrite !seq_eqv_r.
      intros x y [TC Ey].
      split; auto.
      induction TC. 
      { eapply t_step.
        eapply step_add_jf_jf_rmwE; eauto.
        unfolder in *. desc. eauto. }
      eapply t_trans; eauto.
      eapply IHTC1.
      eapply step_add_jf_jf_dom; eauto.
      apply ct_begin in TC2.
      generalize TC2. basic_solver 10. }
    apply seq_mori; [|done].
    apply clos_trans_mori. 
    rewrite step_add_jf_jf_rmw with (S' := S'); eauto.
    basic_solver. }
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

Lemma step_add_jf_releaseE w e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (AJF : add_jf w e S S') 
      (wfE: ES.Wf S) :
  release S' ⨾ ⦗E S⦘ ≡ release S ⨾ ⦗E S⦘.
Proof. 
  unfold release at 1.
  rewrite !seqA.
  arewrite (rs S' ⨾ ⦗E S⦘ ≡ ⦗E S⦘ ⨾ rs S ⨾ ⦗E S⦘).
  { rewrite step_add_jf_rsE; eauto.
    rewrite rsE; auto.
    basic_solver. }
  seq_rewrite basic_step_rel_f_sbE; eauto. 
  unfold release.
  rewrite ES.sbE, rsE; auto.
  basic_solver 20.
Qed.

Lemma step_add_jf_sw lang k k' st st' w e e' S S'
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (nF' : eq_opt e' ∩₁ F S' ⊆₁ ∅)
      (wfE: ES.Wf S) :
  sw S' ≡ sw S ∪ sw_delta S S' k e e'. 
Proof. 
  cdes AJF; cdes BSTEP_.
  assert (ESBasicStep.t e e' S S') as BSTEP.
  { econstructor. eauto. }
  unfold sw_delta.
  unfold sw at 1.
  erewrite dom_rel_helper with (r := jf S').
  2 : eapply step_add_jf_jf_dom; eauto.
  rewrite !seqA, <- seqA.
  rewrite step_add_jf_releaseE; eauto.
  rewrite !seqA.
  rewrite <- seqA with (r1 := ⦗E S⦘).
  erewrite <- dom_rel_helper with (r := jf S').
  2 : eapply step_add_jf_jf_dom; eauto.
  rewrite SB', JF'.
  rewrite seq_union_l, cr_union_l.
  relsf. rewrite unionA.
  apply union_more.
  { rewrite basic_step_jf_sb_f_acq; eauto. }
  rewrite crE. relsf.
  rewrite !seqA.
  arewrite_false (ESBasicStep.sb_delta S k e e' ⨾ ⦗F S'⦘).
  { unfold ESBasicStep.sb_delta.
    clear -nF' rR'.
    rewrite seq_union_l, !seq_eqv_cross_r.
    arewrite (F S' ∩₁ eq e ⊆₁ ∅) by type_solver.
    arewrite (F S' ∩₁ eq_opt e' ⊆₁ ∅) by (by rewrite set_interC).
    basic_solver. }
  arewrite_false (jf_delta w e ⨾ sb S).
  { ESBasicStep.step_solver. }
  arewrite_false (jf S ⨾ ⦗eq e⦘).
  { ESBasicStep.step_solver. }
  unfold jf_delta.
  basic_solver 10.
Qed.  

Lemma step_add_jf_sw_dom lang k k' st st' w e e' S S'
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (nF' : eq_opt e' ∩₁ F S' ⊆₁ ∅)
      (wfE: ES.Wf S) :
  dom_rel (sw S') ⊆₁ E S.
Proof. 
  cdes AJF; cdes BSTEP_.
  rewrite step_add_jf_sw; eauto.
  ESBasicStep.step_solver.
Qed.

Lemma step_add_jf_swE w e e' S S' 
      (BSTEP : ESBasicStep.t e e' S S') 
      (AJF : add_jf w e S S') 
      (nF' : eq_opt e' ∩₁ F S' ⊆₁ ∅)
      (wfE: ES.Wf S) :
  sw S' ⨾ ⦗E S⦘ ≡ sw S.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite step_add_jf_sw; eauto.
  relsf. rewrite basic_step_sw_deltaE; eauto.
  rewrite swE; auto. basic_solver 5.
Qed.

Lemma step_add_jf_hb lang k k' st st' w e e' S S' 
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (nF' : eq_opt e' ∩₁ F S' ⊆₁ ∅)
      (wfE: ES.Wf S) :
  hb S' ≡ hb S ∪ hb_delta S S' k e e'.
Proof.
  cdes AJF; cdes BSTEP_.
  assert (ESBasicStep.t e e' S S') as BSTEP.
  { subst. econstructor. eauto. }
  unfold hb at 1.
  rewrite SB'. 
  rewrite step_add_jf_sw; eauto.
  arewrite 
    (sb S ∪ ESBasicStep.sb_delta S k e e' ∪ (sw S ∪ sw_delta S S' k e e') ≡
     (ESBasicStep.sb_delta S k e e' ∪ sw_delta S S' k e e') ∪ (sb S ∪ sw S))
    by basic_solver.
  rewrite ct_unionE.
  unfold hb. 
  apply union_more; auto.
  rewrite <- cr_of_ct.
  rewrite basic_step_hb_delta_alt; eauto.
Qed.

Lemma step_add_jf_hb_dom w e e' S S' 
      (BSTEP : ESBasicStep.t e e' S S') 
      (AJF : add_jf w e S S') 
      (nF' : eq_opt e' ∩₁ F S' ⊆₁ ∅)
      (wfE: ES.Wf S) :
  dom_rel (hb S') ⊆₁ E S ∪₁ eq e.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite step_add_jf_hb; eauto.
  rewrite dom_union.
  rewrite basic_step_hb_delta_dom; eauto.
  rewrite hbE; auto.
  basic_solver.
Qed. 

Lemma step_add_jf_hbE w e e' S S' 
      (BSTEP : ESBasicStep.t e e' S S') 
      (AJF : add_jf w e S S') 
      (nF' : eq_opt e' ∩₁ F S' ⊆₁ ∅)
      (wfE: ES.Wf S) :
  hb S' ⨾ ⦗E S⦘ ≡ hb S.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite step_add_jf_hb; eauto.
  relsf.
  rewrite basic_step_hb_deltaE; eauto.
  rewrite hbE; auto. basic_solver 5.
Qed. 

(******************************************************************************)
(** ** Step (same jf) properties *)
(******************************************************************************)

Lemma step_same_jf_jfi e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (wf : ES.Wf S) : 
  jfi S' ≡ jfi S.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold ES.jfi.
  rewrite SB', JF'.
  rewrite inter_union_r.
  arewrite_false (jf S ∩ ESBasicStep.sb_delta S k e e').
  { ESBasicStep.step_solver. }
  basic_solver.
Qed.

Lemma step_same_jf_jfe e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (wf : ES.Wf S) : 
  jfe S' ≡ jfe S.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold ES.jfe.
  rewrite SB', JF'.
  rewrite minus_union_r.
  rewrite minus_disjoint with (r' := ESBasicStep.sb_delta S k e e').
  2 : { split; [|done]. ESBasicStep.step_solver. }
  basic_solver.
Qed.

Lemma step_same_jf_sb_jf lang k k' st st' e e' S S'
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (wf : ES.Wf S) : 
  (sb S' ∪ jf S')＊ ≡ 
    (sb S ∪ jf S)＊ ⨾ (ESBasicStep.sb_delta S k e e')^?. 
Proof. 
  cdes BSTEP_.
  assert (ESBasicStep.t e e' S S') as BSTEP.
  { econstructor. eauto. }
  rewrite SB', JF'. 
  arewrite 
    (sb S ∪ ESBasicStep.sb_delta S k e e' ∪ jf S ≡
      ESBasicStep.sb_delta S k e e' ∪ (sb S ∪ jf S))
    by basic_solver.
  erewrite rt_unionE. 
  apply seq_more; auto.
  rewrite rt_begin with (r := sb S ∪ jf S).
  rewrite seq_union_r, seq_id_r. 
  arewrite_false 
    (ESBasicStep.sb_delta S k e e' ⨾ (sb S ∪ jf S)).
  { ESBasicStep.step_solver. }
  relsf. 
  rewrite rtE, crE.
  apply union_more; auto.
  (* unroll transitive closure up to 3 iterations *)
  do 3 rewrite ct_begin, rtE.
  rewrite !seq_union_r, !seq_id_r.
  rewrite <- !seqA.
  arewrite 
    ((ESBasicStep.sb_delta S k e e')
     ⨾ (ESBasicStep.sb_delta S k e e') ≡ 
     ES.cont_sb_dom S k × eq_opt e'). 
  { unfold ESBasicStep.sb_delta.
    rewrite !seq_union_l. 
    arewrite_false 
      ((ES.cont_sb_dom S k ∪₁ eq e) × eq_opt e'
      ⨾ (ES.cont_sb_dom S k × eq e ∪ 
                        (ES.cont_sb_dom S k ∪₁ eq e) × eq_opt e')). 
    { unfold eq_opt, opt_ext in *. ESBasicStep.step_solver. }
    rewrite cross_union_r. rewrite !seq_union_r.
    arewrite_false 
      (ES.cont_sb_dom S k × eq e ⨾ ES.cont_sb_dom S k × eq_opt e').
    { ESBasicStep.step_solver. }
    arewrite_false
      (ES.cont_sb_dom S k × eq e ⨾ ES.cont_sb_dom S k × eq e).
    { ESBasicStep.step_solver. }
    basic_solver 10. }
  rewrite <- seqA.
  arewrite_false 
    ((ES.cont_sb_dom S k × eq_opt e') ⨾ (ESBasicStep.sb_delta S k e e')).
  { ESBasicStep.step_solver. }
  unfold ESBasicStep.sb_delta. 
  basic_solver 10. 
Qed.

Lemma step_same_jf_sb_jfE e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
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
  ESBasicStep.step_solver.
Qed.

Lemma step_same_jf_cc lang k k' st st' e e' S S'
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (wfE: ES.Wf S) :
  cc S' ≡ cc S ∪ 
     cf S' ∩  (jfe S ⨾ (sb S ∪ jf S)＊ ⨾ (jfe S ⨾ ESBasicStep.sb_delta S k e e')).
Proof. 
  cdes BSTEP_.
  assert (ESBasicStep.t e e' S S') as BSTEP.
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
  rewrite ESBasicStep.basic_step_cf; eauto. 
  autounfold with ESStepDb.
  rewrite <- unionA, !inter_union_l, unionA.
  rewrite <- union_false_r with (r := cc S).
  apply union_more.
  { by unfold cc. }
  split; [|done].
  ESBasicStep.step_solver. 
Qed.

Lemma step_same_jf_ccE e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
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
    (ESBasicStep.sb_delta S k e e' ⨾ ⦗E S⦘).
  { ESBasicStep.step_solver. }
  relsf.
  rewrite ccE. basic_solver.
Qed.

Lemma step_same_jf_rsE e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
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
      (BSTEP : ESBasicStep.t e e' S S') 
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
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (RMW' : rmw S' ≡ rmw S) 
      (wfE: ES.Wf S) :
  sw S' ≡ sw S ∪ sw_delta S S' k e e'.
Proof. 
  cdes BSTEP_.
  assert (ESBasicStep.t e e' S S') as BSTEP.
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
  { ESBasicStep.step_solver. }
  basic_solver 10.
Qed.  

Lemma step_same_jf_hb lang k k' st st' e e' S S'
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (JF' : jf S' ≡ jf S) 
      (RMW' : rmw S' ≡ rmw S) 
      (wfE: ES.Wf S) :
  hb S' ≡ hb S ∪ hb_delta S S' k e e'.
Proof.
  cdes BSTEP_.
  assert (ESBasicStep.t e e' S S') as BSTEP.
  { subst. econstructor. eauto. }
  unfold hb at 1.
  rewrite SB'. 
  rewrite step_same_jf_sw; eauto.
  arewrite 
    (sb S ∪ ESBasicStep.sb_delta S k e e' ∪ (sw S ∪ sw_delta S S' k e e') ≡
     (ESBasicStep.sb_delta S k e e' ∪ sw_delta S S' k e e') ∪ (sb S ∪ sw S))
    by basic_solver.
  rewrite ct_unionE.
  unfold hb. 
  apply union_more; auto.
  rewrite <- cr_of_ct.
  rewrite basic_step_hb_delta_alt; eauto.
Qed.

Lemma step_same_jf_hb_dom e e' S S' 
      (BSTEP : ESBasicStep.t e e' S S') 
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
      (BSTEP : ESBasicStep.t e e' S S') 
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
      (BSTEP : ESBasicStep.t e e' S S') 
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
  { eapply ESBasicStep.basic_step_cf_restr; eauto. }
  { rewrite restr_relE, !seqA.
    arewrite (⦗E S⦘ ⨾ (hb S')⁻¹ ≡ (hb S)⁻¹ ⨾ ⦗E S⦘).
    { rewrite <- transp_eqv_rel, <- transp_seq.
      rewrite step_same_jf_hbE; eauto.
      rewrite hbE; auto.
      basic_solver 10. }
    rewrite <- restr_relE.
    rewrite ESBasicStep.basic_step_cf_restr; eauto. }
  { rewrite restr_relE, !seqA.
    rewrite step_same_jf_hbE; eauto.
    rewrite hbE; auto.
    arewrite (⦗E S⦘ ⨾ cf S' ⨾ ⦗E S⦘ ≡ cf S).
    { rewrite <- restr_relE.
      rewrite ESBasicStep.basic_step_cf_restr; eauto. }
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
    rewrite ESBasicStep.basic_step_cf_restr; eauto. }
  done.
Qed.

Lemma step_same_jf_jf_necf e e' S S'
      (BSTEP_ : ESBasicStep.t e e' S S') 
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
(** ** Step (add_co) properties *)
(******************************************************************************)

(* we'll need this hack because of the way 
     `loc` is defined in IMM *)
Definition labloc lbl :=
  match lbl with
  | Aload _ _ l _
  | Astore _ _ l _ => Some l
  | _ => None
  end.

Lemma basic_step_co_ws_alt lang k k' st st' w' lbl e e' S S'
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (wfE: ES.Wf S) 
      (LBL : lab S' w' = lbl) 
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  co_ws w' S S' ≡₁ E S ∩₁ W S ∩₁ (fun w => loc S w = labloc lbl) \₁ ES.cont_cf_dom S k.
Proof. 
  cdes BSTEP_.
  assert (ESBasicStep.t e e' S S') as BSTEP.
  { subst. econstructor. eauto. }

  assert (
    E S ∩₁ (same_loc S') w' ≡₁ E S ∩₁ (fun w : nat => (loc S) w = labloc lbl)
  ) as LOCEQV.
  { unfold Events.same_loc. 
    unfolder; splits; intros x [Ex LOCx]; splits; auto.
    { erewrite <- ESBasicStep.basic_step_loc_eq_dom; eauto.
      rewrite <- LOCx. unfold Events.loc, labloc.
      by rewrite LBL. }
    erewrite ESBasicStep.basic_step_loc_eq_dom
      with (x := x); eauto.
    rewrite LOCx. unfold Events.loc, labloc.
    by rewrite LBL. }

  assert (
    E S ∩₁ set_compl ((cf S') w') ≡₁ E S ∩₁ set_compl (ES.cont_cf_dom S k) 
  ) as CFEQV.
  { unfolder; splits; intros x [Ex nCFx]; splits; auto.
    { intros nKCFx. apply nCFx.
      eapply ESBasicStep.basic_step_cf; eauto.
      autounfold with ESStepDb.
      generalize wEE' nKCFx. 
      basic_solver 10. }
    assert (~ E S w') as nEw'.
    { red. ins. destruct wEE' as [HA | HB]; desf.
      { eapply ESBasicStep.basic_step_acts_set_ne; eauto. }
      unfold eq_opt in HB. 
      destruct e' as [e'|]; desf.
      eapply ESBasicStep.basic_step_acts_set_ne'; eauto. }
    intros CF. apply nCFx.    
    eapply ESBasicStep.basic_step_cf in CF; eauto.
    autounfold with ESStepDb in CF.
    unfolder in CF. desf; exfalso.
    { apply nEw'. apply ES.cfE, seq_eqv_lr in CF. desf. }
    all : apply nEw'; eapply ES.cont_cf_domE in CF; eauto. }

  unfold co_ws.

  arewrite (
    E S ∩₁ W S ∩₁ (same_loc S') w' \₁ (cf S') w' ≡₁
      E S ∩₁ W S ∩₁ 
        (E S ∩₁ (same_loc S') w') ∩₁ (E S \₁ (cf S') w')
  ) by basic_solver.


  arewrite (
    E S ∩₁ W S ∩₁ (fun w : nat => (loc S) w = labloc lbl) \₁ ES.cont_cf_dom S k ≡₁
    E S ∩₁ W S ∩₁ 
      (E S ∩₁ (fun w : nat => (loc S) w = labloc lbl)) ∩₁ (E S \₁ ES.cont_cf_dom S k)
  ) by basic_solver.

  apply set_inter_Propere; auto.
  apply set_inter_Propere; auto.
Qed.

(******************************************************************************)
(** ** Step properties *)
(******************************************************************************)

Lemma step_ew_mon e e' S S'
      (STEP : t_ e e' S S') :
  ew S ⊆ ew S'.
Proof. 
  unfold t_, t_fence, t_load, t_store, t_update in STEP. 
  desf; try cdes AEW; generalize EW'; basic_solver.
Qed.  

Lemma step_ccE e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (STEP : t_ e e' S S') 
      (wfE: ES.Wf S) :
  cc S' ⨾ ⦗E S⦘ ≡ cc S.
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold t_, t_fence, t_load, t_store, t_update in STEP. 
  desf; eauto using step_add_jf_ccE, step_same_jf_ccE.
Qed.

Lemma step_vis_mon e e' S S'
      (BSTEP : ESBasicStep.t e e' S S') 
      (STEP : t_ e e' S S')
      (wfE: ES.Wf S) :
  vis S ⊆₁ vis S'. 
Proof. 
  cdes BSTEP; cdes BSTEP_.
  unfold vis. 
  intros x VIS.
  splits; desf.
  { eapply ESBasicStep.basic_step_acts_set_mon; eauto. }
  arewrite (eq x ⊆₁ E S ∩₁ eq x) by basic_solver.
  rewrite <- seq_eqv.
  rewrite <- seqA.
  rewrite step_ccE; eauto.
  etransitivity; [apply CCEW|].
  apply seq_mori.
  { eapply step_ew_mon; eauto. }
  apply clos_refl_sym_mori.
  eapply ESBasicStep.basic_step_sb_mon; eauto.
Qed.

Lemma step_hb lang k k' st st' e e' S S'
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (STEP : t_ e e' S S')
      (wfE: ES.Wf S) :
  hb S' ≡ hb S ∪ hb_delta S S' k e e'.
Proof. 
  cdes BSTEP_.
  assert (ESBasicStep.rmw_delta e None ≡ ∅₂) as RMW_None.
  { split; [|done]. ESBasicStep.step_solver. }
  unfold t_, t_fence, t_load, t_store, t_update in STEP; desf.
  all : try by (
    erewrite step_same_jf_hb; eauto;
    rewrite RMW', RMW_None; 
    basic_solver
  ).
  all : rewrite step_add_jf_hb; eauto.
  { basic_solver. }
  cdes AEW. type_solver.
Qed.

Lemma step_hb_dom e e' S S' 
      (BSTEP : ESBasicStep.t e e' S S') 
      (STEP : t_ e e' S S')
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
      (BSTEP : ESBasicStep.t e e' S S') 
      (STEP : t_ e e' S S')
      (wfE: ES.Wf S) :
  hb S' ⨾ ⦗E S⦘ ≡ hb S.
Proof. 
  cdes BSTEP.
  rewrite step_hb; eauto.
  relsf.
  rewrite basic_step_hb_deltaE; eauto.
  rewrite hbE; auto. basic_solver 5.
Qed. 

(******************************************************************************)
(** ** Load step properties *)
(******************************************************************************)

Lemma load_step_E e e' S S'
      (BSTEP : ESBasicStep.t e e' S S')
      (LSTEP: t_load e e' S S') :
  E S' ≡₁ E S ∪₁ eq e.
Proof. 
  cdes LSTEP. subst. 
  by apply ESBasicStep.basic_step_nupd_acts_set.
Qed.

Lemma load_step_R e e' S S'
      (LSTEP: t_load e e' S S') :
  R S' e.
Proof. by cdes LSTEP; cdes AJF. Qed.


Lemma load_step_r e e' S S'
      (BSTEP : ESBasicStep.t e e' S S')
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
  eapply ESBasicStep.type_step_eq_dom; eauto.
Qed.  

Lemma load_step_w e e' S S'
      (BSTEP : ESBasicStep.t e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ W S' ≡₁ E S ∩₁ W S.
Proof. 
  assert (R S' e) as AA.
  { eapply load_step_R; eauto. }
  erewrite load_step_E; eauto.
  rewrite set_inter_union_l.
  arewrite (E S ∩₁ W S' ≡₁ E S ∩₁ W S).
  { eapply ESBasicStep.type_step_eq_dom; eauto. }
  arewrite (eq e ∩₁ W S' ≡₁ ∅).
  { split; [|basic_solver].
    unfolder. ins. desf.
    type_solver. }
  basic_solver.
Qed.  

Lemma load_step_f e e' S S'
      (BSTEP : ESBasicStep.t e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  E S' ∩₁ F S' ≡₁ E S ∩₁ F S.
Proof. 
  assert (R S' e) as AA.
  { eapply load_step_R; eauto. }
  erewrite load_step_E; eauto.
  rewrite set_inter_union_l.
  arewrite (E S ∩₁ F S' ≡₁ E S ∩₁ F S).
  { eapply ESBasicStep.type_step_eq_dom; eauto. }
  arewrite (eq e ∩₁ F S' ≡₁ ∅).
  { split; [|basic_solver].
    unfolder. ins. desf.
    type_solver. }
  basic_solver.
Qed.

Lemma load_step_rel e e' S S'
      (BSTEP : ESBasicStep.t e e' S S')
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
  { erewrite ESBasicStep.basic_step_mod_eq_dom in HH; eauto. }
  erewrite <- ESBasicStep.basic_step_mod_eq_dom in HH; eauto. 
Qed.

Lemma load_step_acq e e' S S'
      (BSTEP : ESBasicStep.t e e' S S')
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
  { erewrite ESBasicStep.basic_step_mod_eq_dom in HH; eauto. }
  erewrite <- ESBasicStep.basic_step_mod_eq_dom in HH; eauto.
Qed.  

(* Lemma load_step_rf e e' S S' *)
(*       (BSTEP : ESBasicStep.t e e' S S') *)
(*       (LSTEP: t_load e e' S S')  *)
(*       (wfE: ES.Wf S) :  *)
(*   rf S' ≡ rf S ∪ (ew S)^? ⨾ jf S' ⨾ ⦗eq e⦘ \ cf S'. *)
(* Proof. *)
(*   cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_. *)
(*   unfold ES.rf at 1. *)
(*   rewrite EW', JF'. *)
(*   autorewrite with hahn hahn_full. *)
(*   rewrite minus_union_l. *)
(*   arewrite ((ew S)^? ⨾ jf S \ cf S' ≡ rf S). *)
(*   { unfold ES.rf. *)
(*     admit. } *)
(*   arewrite ((ew S)^? ⨾ jf S ⨾ ⦗eq e⦘ ≡ ∅₂). *)
(*   { rewrite ES.jfE; auto. *)
(*     rewrite !seqA. *)
(*     split; [|done]. ESBasicStep.step_solver. } *)
(*   arewrite (singl_rel w e ⨾ ⦗eq e⦘ ≡ singl_rel w e);  *)
(*     basic_solver 10. *)
(* Admitted. *)

(* Lemma load_step_rf_dom e e' S S' *)
(*       (BSTEP : ESBasicStep.t e e' S S') *)
(*       (LSTEP: t_load e e' S S')  *)
(*       (wfE: ES.Wf S) :  *)
(*   dom_rel (rf S') ⊆₁ E S. *)
(* Proof.  *)
(*   erewrite load_step_rf; eauto.  *)
(*   rewrite dom_union. *)
(*   unionL. *)
(*   { rewrite ES.rfE; auto. basic_solver. } *)
(*   rewrite ES.ewE; auto.  *)
(*   rewrite dom_rel_helper with (r := jf S'). *)
(*   2 : eapply load_step_jf_dom; eauto.  *)
(*   basic_solver. *)
(* Qed. *)

(* Lemma load_step_rf_rmw e e' S S' *)
(*       (BSTEP : ESBasicStep.t e e' S S') *)
(*       (LSTEP: t_load e e' S S')  *)
(*       (wfE: ES.Wf S) :  *)
(*   rf S' ⨾ rmw S' ≡ rf S ⨾ rmw S. *)
(* Proof.  *)
(*   cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_. *)
(*   rewrite ESBasicStep.basic_step_nupd_rmw; eauto. *)
(*   unfold ES.rf.  *)
(*   rewrite JF', EW'. *)
(*   rewrite seq_union_r, minus_union_l, seq_union_l. *)
(*   arewrite (((ew S)^? ⨾ singl_rel w e \ cf S') ⨾ rmw S ≡ ∅₂).  *)
(*   { rewrite crE.  *)
(*     rewrite seq_union_l.  *)
(*     rewrite minus_union_l. *)
(*     rewrite seq_union_l.  *)
(*     rewrite seq_id_l. *)
(*     unfold same_relation; splits; [|basic_solver]. *)
(*     rewrite ES.rmwE; auto. *)
(*     apply inclusion_union_l; *)
(*       unfolder; ins; splits; desf; omega. } *)
(*   rewrite union_false_r. *)
(*   admit. *)
(* Admitted. *)

(* Lemma load_step_rs e e' S S'  *)
(*       (BSTEP : ESBasicStep.t e e' S S') *)
(*       (LSTEP: t_load e e' S S')  *)
(*       (wfE: ES.Wf S) : *)
(*   rs S' ≡ rs S. *)
(* Proof. *)
(*   cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_. *)
(*   assert (ES.Wf S') as wfE'. *)
(*   { admit. (* eapply step_wf; unfold t_; eauto. *) } *)
(*   rewrite !rs_alt; auto. *)
(*   rewrite ESBasicStep.basic_step_nupd_sb, load_step_w, load_step_jf_rmw; eauto. *)
(*   do 2 rewrite crE. *)
(*   relsf. *)
(*   apply union_more; auto. *)
(*   do 2 rewrite <- seqA. *)
(*   rewrite (seqA ⦗E S ∩₁ W S⦘). *)
(*   rewrite <- restr_relE. *)
(*   rewrite restr_inter. *)
(*   rewrite restr_union. *)
(*   arewrite (restr_rel (E S ∩₁ W S) (ES.cont_sb_dom S k × eq e) ≡ ∅₂). *)
(*   { rewrite restr_relE. *)
(*     rewrite seq_eqv_cross. *)
(*     arewrite (E S ∩₁ W S ∩₁ eq e ≡₁ ∅); [|by rewrite cross_false_r]. *)
(*     unfolder; unfold set_subset; splits; ins; desf; omega. } *)
(*   arewrite (restr_rel (E S ∩₁ W S) (same_loc S') ≡ restr_rel (E S ∩₁ W S) (same_loc S)). *)
(*   2: basic_solver 21. *)
(*   do 2 rewrite <- restr_restr. *)
(*   apply restr_rel_more; auto. *)
(*   rewrite <- ESBasicStep.basic_step_same_loc_restr; eauto. *)
(* Admitted. *)

(* Lemma load_step_release e e' S S'  *)
(*       (BSTEP : ESBasicStep.t e e' S S') *)
(*       (LSTEP: t_load e e' S S')  *)
(*       (wfE: ES.Wf S) : *)
(*   release S' ≡ release S.  *)
(* Proof.  *)
(*   cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.   *)
(*   assert (ES.Wf S') as wfE'. *)
(*   { admit. (* eapply step_wf; unfold t_; eauto. *) } *)
(*   rewrite !release_alt; auto. *)
(*   rewrite ESBasicStep.basic_step_nupd_sb, load_step_rel, load_step_f, load_step_rs; eauto. *)
(*   do 2 rewrite crE. *)
(*   relsf. *)
(*   apply union_more; auto. *)
(*   rewrite !seqA. *)
(*   arewrite (ES.cont_sb_dom S k × eq e ⨾ rs S ≡ ∅₂);  *)
(*     [|basic_solver 10]. *)
(*   rewrite rsE; auto. *)
(*   arewrite (ES.cont_sb_dom S k × eq e ⨾ ⦗E S⦘ ≡ ∅₂);  *)
(*     [ split; [|done]; ESBasicStep.step_solver | basic_solver ]. *)
(* Admitted. *)

(* Lemma load_step_sw e e' S S'  *)
(*       (BSTEP : ESBasicStep.t e e' S S') *)
(*       (LSTEP: t_load e e' S S')  *)
(*       (wfE: ES.Wf S) : *)
(*   sw S' ≡ sw S ∪ release S ⨾ jf S' ⨾ ⦗Acq S'⦘ ⨾ ⦗eq e⦘.  *)
(* Proof. *)
(*   cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.   *)
(*   assert (ES.Wf S') as wfE'. *)
(*   { admit. (* eapply step_wf; unfold t_; eauto. *) } *)
(*   rewrite !sw_alt; auto. *)
(*   rewrite JF'. *)
(*   rewrite  *)
(*     load_step_release, load_step_f, load_step_acq, *)
(*     ESBasicStep.basic_step_nupd_sb; *)
(*     eauto. *)
(*   rewrite id_union. *)
(*   rewrite !crE. *)
(*   relsf. *)
(*   rewrite !unionA. *)
(*   apply union_more; auto. *)
(*   apply union_more; auto. *)
(*   rewrite id_union, !id_inter, !seq_union_r. *)
(*   arewrite_false (ES.cont_sb_dom S k × eq e ⨾ ⦗E S⦘). *)
(*   { ESBasicStep.step_solver. } *)
(*   arewrite_false (⦗E S⦘ ⨾ ⦗F S⦘ ⨾ ⦗eq e⦘). *)
(*   { ESBasicStep.step_solver. } *)
(*   arewrite_false (jf S ⨾ ⦗eq e⦘). *)
(*   { ESBasicStep.step_solver. } *)
(*   rewrite <- !seqA with (r1 := singl_rel w e). *)
(*   arewrite_false (singl_rel w e ⨾ ⦗E S⦘). *)
(*   { ESBasicStep.step_solver. } *)
(*   rewrite <- !seqA with (r1 := singl_rel w e). *)
(*   arewrite_false (singl_rel w e ⨾ sb S). *)
(*   { ESBasicStep.step_solver. } *)
(*   arewrite_false (jf S ⨾ ⦗Acq S'⦘ ⨾ ⦗eq e⦘).  *)
(*   { ESBasicStep.step_solver. } *)
(*   basic_solver 20. *)
(* Admitted. *)

(* Lemma load_step_hb lang k k' st st' e e' S S'  *)
(*       (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S')  *)
(*       (LSTEP: t_load e e' S S')  *)
(*       (wfE: ES.Wf S) : *)
(*   hb S' ≡ hb S ∪  *)
(*      (hb S)^? ⨾ (ES.cont_sb_dom S k × eq e ∪ release S ⨾ jf S' ⨾ ⦗Acq S'⦘ ⨾ ⦗eq e⦘).  *)
(* Proof. *)
(*   cdes LSTEP; cdes AJF; cdes BSTEP_. *)
(*   assert (ESBasicStep.t e None S S') as BSTEP. *)
(*   { subst. econstructor. eauto. } *)
(*   desf. unfold hb at 1. *)
(*   rewrite ESBasicStep.basic_step_nupd_sb, load_step_sw; eauto. *)
(*   rewrite unionA. *)
(*   rewrite (unionAC (ES.cont_sb_dom S k × eq (ES.next_act S))). *)
(*   rewrite <- (unionA (sb S)). *)
(*   rewrite unionC. *)
(*   erewrite clos_trans_union_ext. *)
(*   { rewrite <- cr_of_ct. *)
(*     fold (hb S). *)
(*     basic_solver. } *)
(*   all : split; [|done]. *)
(*   all : rewrite JF'. *)
(*   all : relsf; unionL. *)
(*   all : by ESBasicStep.step_solver. *)
(* Qed. *)

(* Lemma load_step_hb_dom e e' S S' *)
(*       (BSTEP : ESBasicStep.t e e' S S') *)
(*       (LSTEP: t_load e e' S S')  *)
(*       (wfE: ES.Wf S) :  *)
(*   dom_rel (hb S') ⊆₁ E S. *)
(* Proof.  *)
(*   cdes BSTEP. cdes BSTEP_. cdes LSTEP. cdes AJF. *)
(*   rewrite load_step_hb; eauto. *)
(*   rewrite releaseE, hbE; auto. *)
(*   rewrite ES.cont_sb_domE; eauto. *)
(*   basic_solver. *)
(* Qed.   *)

(* Lemma load_step_hb_seq_E e e' S S'  *)
(*       (BSTEP : ESBasicStep.t e e' S S') *)
(*       (LSTEP: t_load e e' S S')  *)
(*       (wfE: ES.Wf S) : *)
(*   hb S' ⨾ ⦗E S⦘ ≡ hb S. *)
(* Proof.  *)
(*   cdes BSTEP. cdes BSTEP_. cdes LSTEP. cdes AJF. *)
(*   rewrite load_step_hb; eauto. *)
(*   rewrite seq_union_l, !seqA. *)
(*   arewrite ( *)
(*       (ES.cont_sb_dom S k × eq e ∪ release S ⨾ jf S' ⨾ ⦗Acq S'⦘ ⨾ ⦗eq e⦘) ⨾ ⦗E S⦘ ≡ ∅₂ *)
(*   ).  *)
(*  { split; [|done].  *)
(*    rewrite JF'. *)
(*    ESBasicStep.step_solver. } *)
(*   rewrite hbE; auto. *)
(*   basic_solver 20. *)
(* Qed. *)

End ESstep.