From hahn Require Import Hahn.
From imm Require Import Events AuxRel. 
Require Import AuxRel.
Require Import AuxDef.
Require Import EventStructure.
Require Import Consistency.
Require Import BasicStep.

Set Implicit Arguments.

Section AddJF.

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
Notation "'icf' S" := S.(ES.icf) (at level 10).

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

Notation "'same_mod' S" := (same_mod S.(ES.lab)) (at level 10).
Notation "'same_loc' S" := (same_loc S.(ES.lab)) (at level 10).
Notation "'same_val' S" := (same_val S.(ES.lab)) (at level 10).

Notation "'K' S" := (S.(ES.cont_set)) (at level 10).

Notation "'Tid' S" := (fun t e => S.(ES.tid) e = t) (at level 1).
Notation "'Mod_' S" := (fun m x => mod S x = m) (at level 1).
Notation "'Loc_' S" := (fun l x => loc S x = l) (at level 1).
Notation "'Val_' S" := (fun v e => val S e = v) (at level 1).

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
  ⟪ nCF : ~ cf S' w r' ⟫ /\
  ⟪ JF' : jf S' ≡ jf S ∪ jf_delta w r' ⟫.

(******************************************************************************)
(** ** Deltas definitions *)
(******************************************************************************)

Definition jfi_delta S k w r : relation eventid := 
  ⦗ES.cont_sb_dom S k⦘ ⨾ jf_delta w r.

Definition jfe_delta S k w r : relation eventid := 
  ⦗set_compl (ES.cont_sb_dom S k)⦘ ⨾ jf_delta w r.

Definition sw_delta S S' k e e' : relation eventid := 
  release S ⨾ (jf S ⨾ sb_delta S k e e' ⨾ ⦗F S'⦘ ∪ jf S' ⨾ ⦗eq e⦘) ⨾ ⦗Acq S'⦘.

Definition hb_delta S S' k e e' : relation eventid := 
  (hb S)^? ⨾ (sb_delta S k e e' ∪ sw_delta S S' k e e') ⨾ (eq e × eq_opt e')^? . 

Hint Unfold jfi_delta jfe_delta sw_delta hb_delta : ESStepDb.

(******************************************************************************)
(** ** Auxiliary lemmas *)
(******************************************************************************)

Lemma basic_step_w_sb_loc_wE e e' S S'
      (BSTEP : basic_step e e' S S') 
      (wfE: ES.Wf S) :
  ⦗E S' ∩₁ W S'⦘ ⨾ (sb S' ∩ same_loc S')^? ⨾ ⦗W S'⦘ ⨾ ⦗E S⦘ ≡ 
  ⦗E S  ∩₁ W S ⦘ ⨾ (sb S  ∩ same_loc S )^? ⨾ ⦗W S ⦘.
Proof. 
  cdes BSTEP. cdes BSTEP_.
  arewrite (⦗W S'⦘ ⨾ ⦗E S⦘ ≡ ⦗E S⦘ ⨾ ⦗W S⦘). 
  { rewrite seq_eqvC.
    rewrite !seq_eqv.
    apply eqv_rel_more.
    eapply basic_step_w_eq_w; eauto. }
  arewrite ((sb S' ∩ same_loc S')^? ⨾ ⦗E S⦘ ≡ ⦗E S⦘ ⨾ (sb S ∩ same_loc S)^?).
  { rewrite !crE. relsf.
    apply union_more; auto.
    rewrite <- seq_eqv_inter_lr.
    rewrite basic_step_sbE; eauto.
    rewrite ES.sbE at 1; auto.
    rewrite <- restr_relE, <- restr_inter_absorb_r.
    rewrite basic_step_same_loc_restr; eauto.
    rewrite restr_inter_absorb_r, restr_relE.
    rewrite ES.sbE; auto.
    basic_solver 20. }
  arewrite (⦗E S' ∩₁ W S'⦘ ⨾ ⦗E S⦘ ≡ ⦗E S ∩₁ W S⦘).
  { rewrite basic_step_acts_set; eauto.
    rewrite !set_inter_union_l, !id_union. relsf.
    arewrite_false (⦗eq e ∩₁ W S'⦘ ⨾ ⦗E S⦘).
    { step_solver. }
    arewrite_false (⦗eq_opt e' ∩₁ W S'⦘ ⨾ ⦗E S⦘).
    { step_solver. }
    relsf. 
    rewrite basic_step_w_eq_w; eauto.
    basic_solver. }
  done.
Qed.

Lemma basic_step_rel_f_sbE e e' S S'
      (BSTEP : basic_step e e' S S') 
      (wfE: ES.Wf S) :
  ⦗Rel S'⦘ ⨾ (⦗F S'⦘ ⨾ sb S')^? ⨾ ⦗E S⦘ ≡ 
  ⦗Rel S ⦘ ⨾ (⦗F S ⦘ ⨾ sb S )^? ⨾ ⦗E S⦘.
Proof. 
  arewrite ((⦗F S'⦘ ⨾ sb S')^? ⨾ ⦗E S⦘ ≡ ⦗E S⦘ ⨾ (⦗F S⦘ ⨾ sb S)^?).
  { rewrite !crE. relsf.
    apply union_more; auto.
    rewrite !seqA.
    rewrite basic_step_sbE; eauto.
    rewrite ES.sbE; auto.
    arewrite (⦗F S'⦘ ⨾ ⦗E S⦘ ≡ ⦗E S⦘ ⨾ ⦗F S⦘).
    { rewrite !seq_eqv.
      apply eqv_rel_more.
      rewrite set_interC.
      eapply basic_step_f_eq_f; eauto. }
    basic_solver. }
  arewrite (⦗Rel S'⦘ ⨾ ⦗E S⦘ ≡ ⦗Rel S⦘ ⨾ ⦗E S⦘).
  { rewrite !seq_eqv.
    apply eqv_rel_more.
    rewrite set_interC.
    rewrite basic_step_rel_eq_rel; eauto.
    basic_solver. }
  rewrite ES.sbE; auto.
  basic_solver 10.
Qed.

Lemma basic_step_jf_sb_f_acq e e' S S'
      (BSTEP : basic_step e e' S S') 
      (WF: ES.Wf S) :
  jf S ⨾ (sb S ⨾ ⦗F S'⦘)^? ⨾ ⦗Acq S'⦘ ≡ jf S ⨾ (sb S ⨾ ⦗F S⦘)^? ⨾ ⦗Acq S⦘.
Proof. 
  arewrite (sb S ⨾ ⦗F S'⦘ ≡ sb S ⨾ ⦗F S⦘).
  { rewrite ES.sbE; auto. rewrite !seqA.
    arewrite (⦗E S⦘ ⨾ ⦗F S'⦘ ≡ ⦗E S⦘ ⨾ ⦗F S⦘); auto.
    rewrite !seq_eqv.
    apply eqv_rel_more.
    eapply basic_step_f_eq_f; eauto. }
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
(** ** Deltas lemmas *)
(******************************************************************************)

Lemma add_jf_jf_delta_dom w e e' S S'
      (BSTEP : basic_step e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  dom_rel (jf_delta w e) ⊆₁ E S.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  step_solver.
Qed.  

Lemma add_jf_jf_deltaE w e e' S S'
      (BSTEP : basic_step e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  jf_delta w e ⨾ ⦗E S⦘ ≡ ∅₂. 
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  split; [|done].
  step_solver.
Qed.  

Lemma add_jf_jfi_delta_dom lang k k' st st' w e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  dom_rel (jfi_delta S k w e) ⊆₁ E S.
Proof. 
  cdes AJF; cdes BSTEP_.
  step_solver.
Qed.  

Lemma add_jf_jfe_delta_dom lang k k' st st' w e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  dom_rel (jfe_delta S k w e) ⊆₁ E S.
Proof. 
  cdes AJF; cdes BSTEP_.
  step_solver.
Qed.

Lemma add_jf_jfi_deltaE lang k k' st st' w e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  jfi_delta S k w e ⨾ ⦗E S⦘ ≡ ∅₂.
Proof. 
  cdes AJF; cdes BSTEP_.
  split; [|done].
  step_solver.
Qed.  

Lemma add_jf_jfe_deltaE lang k k' st st' w e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  jfe_delta S k w e ⨾ ⦗E S⦘ ≡ ∅₂.
Proof. 
  cdes AJF; cdes BSTEP_.
  split; [|done].
  step_solver.
Qed.  

Lemma basic_step_sw_delta_dom lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (wfE: ES.Wf S) :
  dom_rel (sw_delta S S' k e e') ⊆₁ E S.
Proof. 
  cdes BSTEP_.
  step_solver.
Qed.

Lemma basic_step_sw_deltaE lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (wfE: ES.Wf S) :
  sw_delta S S' k e e' ⨾ ⦗E S⦘ ≡ ∅₂.
Proof. 
  cdes BSTEP_.
  split; [|done]. 
  unfold sw_delta.
  step_solver.
Qed.

Lemma basic_step_hb_delta_dom lang k k' st st' e e' S S' 
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (wfE: ES.Wf S) :
  dom_rel (hb_delta S S' k e e') ⊆₁ E S ∪₁ eq e.
Proof. 
  cdes BSTEP_.
  unfold hb_delta.
  rewrite crE, !seq_union_l, seq_id_l. 
  rewrite !dom_union, !dom_seq.
  rewrite !set_subset_union_l.
  splits. 
  { eapply basic_step_sb_delta_dom; eauto. }
  all : step_solver.
Qed. 

Lemma basic_step_hb_deltaE lang k k' st st' e e' S S' 
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (wfE: ES.Wf S) :
  hb_delta S S' k e e' ⨾ ⦗E S⦘ ≡ ∅₂.
Proof. 
  cdes BSTEP_.
  split; [|done].
  step_solver.
Qed.

Lemma basic_step_hb_delta_alt lang k k' st st' e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (wfE: ES.Wf S) :
  hb_delta S S' k e e' ≡ 
    (hb S)^? ⨾ ((sb_delta S k e e' ∪ sw_delta S S' k e e') ⨾ (hb S)^?)⁺.
Proof. 
  cdes BSTEP_.
  unfold hb_delta. 
  apply seq_more; auto.
  rewrite !crE. relsf.
  rewrite hbE; auto.
  arewrite_false (sb_delta S k e e' ⨾ ⦗E S⦘).
  { eapply basic_step_sb_deltaE; eauto. }
  arewrite_false (sw_delta S S' k e e' ⨾ ⦗E S⦘).
  { eapply basic_step_sw_deltaE; eauto. }
  relsf.
  rewrite ct_begin, rtE. relsf.
  rewrite !unionA.
  do 3 (apply union_more; auto).
  { rewrite ct_begin, rtE. relsf.
    rewrite <- !seqA.
    arewrite_false (sb_delta S k e e' ⨾ sw_delta S S' k e e'). 
    { step_solver. }
    rewrite <- !seqA.
    arewrite 
      (sb_delta S k e e' ⨾ sb_delta S k e e' ≡ 
                            sb_delta S k e e' ⨾ eq e × eq_opt e').
    { rewrite dom_rel_helper with (r := sb_delta S k e e') at 2.
      2 : eapply basic_step_sb_delta_dom; eauto.
      rewrite id_union. relsf. 
      arewrite_false (sb_delta S k e e' ⨾ ⦗E S⦘).
      { step_solver. }
      relsf.
      apply seq_more; auto.
      unfold sb_delta. relsf.
      arewrite_false (⦗eq e⦘ ⨾ ES.cont_sb_dom S k × eq e). 
      { step_solver. }
      arewrite_false (⦗eq e⦘ ⨾ ES.cont_sb_dom S k × eq_opt e'). 
      { step_solver. }
      basic_solver 20. }
    relsf.
    rewrite ct_begin, rtE. relsf.

    arewrite_false (eq e × eq_opt e' ⨾ sb_delta S k e e').
    { step_solver. }
    arewrite_false (eq e × eq_opt e' ⨾ sb_delta S k e e').
    { step_solver. }
    arewrite_false (eq e × eq_opt e' ⨾ sw_delta S S' k e e').
    { step_solver. }
    arewrite_false (eq e × eq_opt e' ⨾ sw_delta S S' k e e').
    { step_solver. }
    basic_solver 10. }

  rewrite ct_begin, rtE. relsf.
  rewrite <- !seqA.
  arewrite_false (sw_delta S S' k e e' ⨾ sw_delta S S' k e e'). 
  { unfold sw_delta. step_solver. }
  rewrite <- !seqA.
  arewrite 
    (sw_delta S S' k e e' ⨾ sb_delta S k e e' ≡ 
              sw_delta S S' k e e' ⨾ eq e × eq_opt e').
  { rewrite dom_rel_helper with (r := sb_delta S k e e').
    2 : eapply basic_step_sb_delta_dom; eauto.
    rewrite id_union. relsf. 
    arewrite_false (sw_delta S S' k e e' ⨾ ⦗E S⦘).
    { unfold sw_delta. step_solver. }
    unfold sb_delta. relsf.
    arewrite_false (⦗eq e⦘ ⨾ ES.cont_sb_dom S k × eq e).
    { step_solver. }
    arewrite_false (⦗eq e⦘ ⨾ ES.cont_sb_dom S k × eq_opt e').
    { step_solver. }
    basic_solver 10. }
  
  relsf.
  rewrite ct_begin, rtE. relsf.
  arewrite_false (eq e × eq_opt e' ⨾ sb_delta S k e e').
  { step_solver. }
  arewrite_false (eq e × eq_opt e' ⨾ sb_delta S k e e').
  { step_solver. }
  arewrite_false (eq e × eq_opt e' ⨾ sw_delta S S' k e e').
  { step_solver. }
  arewrite_false (eq e × eq_opt e' ⨾ sw_delta S S' k e e').
  { step_solver. }
  basic_solver 10.   
Qed.

(******************************************************************************)
(** ** add_jf properties *)
(******************************************************************************)

Lemma add_jf_jf_dom w e e' S S'
      (BSTEP : basic_step e e' S S')
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  dom_rel (jf S') ⊆₁ E S.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite JF', dom_union. 
  rewrite wf.(ES.jfE).
  rewrite add_jf_jf_delta_dom; eauto.
  basic_solver.
Qed.

Lemma add_jf_jfE w e e' S S'
      (BSTEP : basic_step e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  jf S' ⨾ ⦗E S⦘ ≡ jf S.
Proof.   
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite JF'. 
  rewrite seq_union_l.
  rewrite add_jf_jf_deltaE; eauto.
  rewrite ES.jfE; auto. basic_solver 5.
Qed.

Lemma add_jf_jfi lang k k' st st' w e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  jfi S' ≡ jfi S ∪ jfi_delta S k w e.
Proof. 
  cdes AJF; cdes BSTEP_.
  unfold ES.jfi, jfi_delta.
  rewrite SB', JF'.
  rewrite inter_union_l, !inter_union_r.
  arewrite_false (jf S ∩ sb_delta S k e e').
  { step_solver. }
  arewrite_false (jf_delta w e ∩ sb S). 
  { step_solver. } 
  relsf.
  apply union_more; auto.
  autounfold with ESStepDb.
  rewrite !inter_union_r.
  arewrite_false (singl_rel w e ∩ ES.cont_sb_dom S k × eq_opt e').
  { step_solver. }
  arewrite_false (singl_rel w e ∩ eq e × eq_opt e').
  { step_solver. }
  basic_solver 10.
Qed.

Lemma add_jf_jfe lang k k' st st' w e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  jfe S' ≡ jfe S ∪ jfe_delta S k w e.
Proof. 
  cdes AJF; cdes BSTEP_.
  unfold ES.jfe, jfe_delta.
  rewrite SB', JF'.
  rewrite minus_union_l, !minus_union_r.
  erewrite minus_disjoint 
    with (r := jf S) (r' := sb_delta S k e e').
  2 : { split; [|done]. step_solver. }
  erewrite minus_disjoint 
    with (r := jf_delta w e) (r' := sb S).
  2 : { split; [|done]. step_solver. }
  apply union_more.
  { basic_solver. }
  autounfold with ESStepDb.
  rewrite !minus_union_r.
  erewrite minus_disjoint 
    with (r := singl_rel w e) (r' := ES.cont_sb_dom S k × eq_opt e').
  erewrite minus_disjoint 
    with (r := singl_rel w e) (r' := eq e × eq_opt e').
  2,3 : split; [|done]; step_solver. 
  rewrite minus_inter_compl.
  rewrite !interC with (r1 := singl_rel w e).
  rewrite !interA, !interK.
  split; [basic_solver|].
  unfolder. ins. desc.
  splits; auto. 
  red. ins. desc. auto.
Qed.

Lemma add_jf_jfi_dom w e e' S S'
      (BSTEP : basic_step e e' S S')
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  dom_rel (jfi S') ⊆₁ E S.
Proof. 
  unfold ES.jfi.
  unfolder; ins; desf.
  eapply add_jf_jf_dom; eauto. 
  basic_solver.
Qed.

Lemma add_jf_jfe_dom w e e' S S'
      (BSTEP : basic_step e e' S S')
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  dom_rel (jfe S') ⊆₁ E S.
Proof. 
  unfold ES.jfe.
  unfolder; ins; desf.
  eapply add_jf_jf_dom; eauto. 
  basic_solver.
Qed.

Lemma add_jf_jfiE w e e' S S'
      (BSTEP : basic_step e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  jfi S' ⨾ ⦗E S⦘ ≡ jfi S.
Proof.   
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite add_jf_jfi; eauto.
  rewrite seq_union_l.
  rewrite add_jf_jfi_deltaE; eauto.
  rewrite ES.jfiE; auto. basic_solver 5.
Qed.

Lemma add_jf_jfeE w e e' S S'
      (BSTEP : basic_step e e' S S') 
      (AJF : add_jf w e S S') 
      (wf : ES.Wf S) : 
  jfe S' ⨾ ⦗E S⦘ ≡ jfe S.
Proof.   
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite add_jf_jfe; eauto.
  rewrite seq_union_l.
  rewrite add_jf_jfe_deltaE; eauto.
  rewrite ES.jfeE; auto. basic_solver 5.
Qed.

Lemma add_jf_sb_jf lang k k' st st' w e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (wfE: ES.Wf S) :
  (sb S' ∪ jf S')＊ ≡ 
    (sb S ∪ jf S)＊ ⨾ 
      (sb_delta S k e e' ∪ singl_rel w e ∪ eq w × eq_opt e')^?. 
Proof. 
  cdes AJF; cdes BSTEP_.
  assert (basic_step e e' S S') as BSTEP.
  { econstructor. eauto. }
  autounfold with ESStepDb in *.
  rewrite SB', JF'. 
  arewrite 
    (sb S ∪ sb_delta S k e e' ∪ (jf S ∪ singl_rel w e) ≡
      sb_delta S k e e' ∪ singl_rel w e ∪ (sb S ∪ jf S))
    by basic_solver.
  erewrite rt_unionE. 
  apply seq_more; auto.
  rewrite rt_begin with (r := sb S ∪ jf S).
  rewrite seq_union_r, seq_id_r. 
  arewrite_false 
    ((sb_delta S k e e' ∪ singl_rel w e) ⨾ (sb S ∪ jf S)).
  { step_solver. }
  relsf. 
  rewrite rtE, crE.
  apply union_more; auto.
  (* unroll transitive closure up to 3 iterations *)
  do 3 rewrite ct_begin, rtE.
  rewrite !seq_union_r, !seq_id_r.
  rewrite <- !seqA.
  arewrite 
    ((sb_delta S k e e' ∪ singl_rel w e)
     ⨾ (sb_delta S k e e' ∪ singl_rel w e) ≡ 
     ES.cont_sb_dom S k × eq_opt e' ∪ eq w × eq_opt e'). 
  { unfold sb_delta at 1.
    rewrite !seq_union_l. 
    relsf.
    arewrite_false 
      (ES.cont_sb_dom S k × eq e ⨾ singl_rel w e).
    { step_solver. }
    arewrite_false 
      (ES.cont_sb_dom S k × eq_opt e' ⨾ sb_delta S k e e').
    { step_solver. }
    arewrite_false 
      (ES.cont_sb_dom S k × eq_opt e' ⨾ singl_rel w e).
    { step_solver. }
    arewrite_false 
      (eq e × eq_opt e' ⨾ sb_delta S k e e').
    { step_solver. }
    arewrite_false
      (eq e × eq_opt e' ⨾ singl_rel w e).
    { step_solver. }
    arewrite_false
      (singl_rel w e ⨾ singl_rel w e).
    { step_solver. }
    relsf.
    apply union_more.
    { unfold sb_delta. relsf.
      arewrite_false
        (ES.cont_sb_dom S k × eq e ⨾ ES.cont_sb_dom S k × eq e).
      { step_solver. }
      arewrite_false
        (ES.cont_sb_dom S k × eq e ⨾ ES.cont_sb_dom S k × eq_opt e').
      { step_solver. }
      basic_solver 10. }
    unfold sb_delta. relsf.
    arewrite_false
      (singl_rel w e ⨾ ES.cont_sb_dom S k × eq e).
    { step_solver. }
    arewrite_false
      (singl_rel w e ⨾ ES.cont_sb_dom S k × eq_opt e').
    { step_solver. }
    basic_solver 10. }
  rewrite <- seqA.
  arewrite_false 
    ((ES.cont_sb_dom S k × eq_opt e' ∪ eq w × eq_opt e')
        ⨾ (sb_delta S k e e' ∪ singl_rel w e)).
  { arewrite (singl_rel w e ⊆ E S × eq e).
    { basic_solver. }
    step_solver. }
  unfold sb_delta. 
  basic_solver 10. 
Qed.

Lemma add_jf_sb_jfE w e e' S S'
      (BSTEP : basic_step e e' S S') 
      (AJF : add_jf w e S S') 
      (wfE: ES.Wf S) :
  (sb S' ∪ jf S')＊ ⨾ ⦗E S⦘ ≡ (sb S ∪ jf S)＊ ⨾ ⦗E S⦘.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  erewrite add_jf_sb_jf; eauto.
  rewrite crE. relsf.
  rewrite <- union_false_r with (r := (sb S ∪ jf S)＊ ⨾ ⦗E S⦘) at 2. 
  apply union_more; auto.
  split; [|done].
  step_solver.
Qed.

Lemma add_jf_sb_jf_dom w e e' S S'
      (BSTEP : basic_step e e' S S') 
      (AJF : add_jf w e S S') 
      (wfE: ES.Wf S) :
  dom_rel ((sb S' ∪ jf S')＊ ⨾ ⦗E S⦘) ⊆₁ E S.
Proof. 
  rewrite add_jf_sb_jfE; eauto.
  rewrite rtE, seq_union_l, seq_id_l. 
  rewrite ES.sbE, ES.jfE; auto.
  rewrite <- seq_union_r. 
  rewrite inclusion_ct_seq_eqv_l.
  basic_solver.
Qed.

Lemma add_jf_cc lang k k' st st' w e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (wfE: ES.Wf S) :
  cc S' ≡ cc S ∪ 
     cf S' ∩ 
     (jfe S ⨾ (sb S ∪ jf S)＊ ⨾ 
          (jfe S ⨾ sb_delta S k e e' ∪ jfe_delta S k w e ⨾ (eq e × eq_opt e')^?)).
Proof. 
  cdes AJF; cdes BSTEP_.
  assert (basic_step e e' S S') as BSTEP.
  { econstructor. eauto. }
  unfold cc at 1. 
  erewrite dom_rel_helper with (r := jfe S') at 2.
  2 : eapply add_jf_jfe_dom; eauto.
  rewrite !seqA. 
  rewrite <- seqA with (r2 := ⦗E S⦘).
  erewrite dom_rel_helper with (r := (sb S' ∪ jf S')＊ ⨾ ⦗E S⦘).
  2 : eapply add_jf_sb_jf_dom; eauto.
  rewrite add_jf_sb_jfE; eauto.
  rewrite !seqA. 
  rewrite <- !seqA with (r2 := ⦗E S⦘).
  rewrite add_jf_jfeE; eauto.
  rewrite !seqA.
  rewrite <- !seqA with (r1 := ⦗E S⦘).
  erewrite <- dom_rel_helper with (r := jfe S').
  2 : eapply add_jf_jfe_dom; eauto.  
  rewrite SB'. 
  rewrite add_jf_jfe with (S' := S') at 1; eauto.
  rewrite cr_union_l. relsf.
  rewrite !inter_union_r.
  rewrite unionA.
  apply union_more.
  { rewrite basic_step_cf; eauto. 
    autounfold with ESStepDb.
    rewrite <- unionA, !inter_union_l, unionA.
    rewrite <- union_false_r with (r := cc S).
    apply union_more.
    { by unfold cc. }
    split; [|done].
    step_solver. }
  rewrite unionC, unionA.
  apply union_more; auto.
  rewrite !crE. relsf.
  arewrite_false (jfe_delta S k w e ⨾ sb S). 
  { autounfold with ESStepDb. 
    arewrite (singl_rel w e ⊆ E S × eq e).
    { basic_solver. }
    step_solver. }
  relsf.
  rewrite !inter_union_r.
  rewrite unionC.
  apply union_more; auto.
  apply inter_rel_more; auto.  
  do 2 (apply seq_more; auto).  
  autounfold with ESStepDb. 
  relsf. rewrite !seqA.
  arewrite_false (singl_rel w e ⨾ ES.cont_sb_dom S k × eq e).
  { arewrite (singl_rel w e ⊆ E S × eq e).
    { basic_solver. }
    step_solver. }
  arewrite_false (singl_rel w e ⨾ ES.cont_sb_dom S k × eq_opt e').
  { arewrite (singl_rel w e ⊆ E S × eq e).
    { basic_solver. }
    step_solver. }
  basic_solver 10.
Qed.  

Lemma add_jf_ccE w e e' S S'
      (BSTEP : basic_step e e' S S') 
      (AJF : add_jf w e S S') 
      (wfE: ES.Wf S) :
  cc S' ⨾ ⦗E S⦘ ≡ cc S.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite add_jf_cc; eauto.
  rewrite seq_union_l.
  rewrite interC.
  rewrite <- seq_eqv_inter_lr.
  rewrite !seqA, seq_union_l.
  rewrite !seqA.
  arewrite_false 
    (sb_delta S k e e' ⨾ ⦗E S⦘).
  { step_solver. }
  arewrite_false
   (jfe_delta S k w e ⨾ (eq e × eq_opt e')^? ⨾ ⦗E S⦘).
  { autounfold with ESStepDb. 
    arewrite (singl_rel w e ⊆ E S × eq e).
    { basic_solver. }
    step_solver. }
  relsf.
  rewrite ccE. basic_solver.
Qed.

Lemma add_jf_jf_rmw w e e' S S'
      (BSTEP : basic_step e e' S S') 
      (AJF : add_jf w e S S') 
      (wfE: ES.Wf S) :
  jf S' ⨾ rmw S' ≡ jf S ⨾ rmw S ∪ eq w × eq_opt e'.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite JF', RMW'.
  relsf. rewrite unionA.
  apply union_more; auto.
  arewrite_false (jf_delta w e ⨾ rmw S).
  { step_solver. }
  arewrite_false (jf S ⨾ rmw_delta e e').
  { step_solver. }
  autounfold with ESStepDb.
  basic_solver 10.
Qed.  

Lemma add_jf_jf_rmwE w e e' S S'
      (BSTEP : basic_step e e' S S') 
      (AJF : add_jf w e S S') 
      (wfE: ES.Wf S) :
  jf S' ⨾ rmw S' ⨾ ⦗E S⦘ ≡ jf S ⨾ rmw S.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite <- seqA.
  rewrite add_jf_jf_rmw; eauto.
  relsf.
  arewrite_false (eq w × eq_opt e' ⨾ ⦗E S⦘).
  { step_solver. }
  rewrite ES.rmwE; auto. basic_solver 10.
Qed.

Lemma add_jf_rsE w e e' S S'
      (BSTEP : basic_step e e' S S') 
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
        eapply add_jf_jf_rmwE; eauto.
        unfolder in *. desc. eauto. }
      eapply t_trans; eauto.
      eapply IHTC1.
      eapply add_jf_jf_dom; eauto.
      apply ct_begin in TC2.
      generalize TC2. basic_solver 10. }
    apply seq_mori; [|done].
    apply clos_trans_mori. 
    rewrite add_jf_jf_rmw with (S' := S'); eauto.
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

Lemma add_jf_releaseE w e e' S S'
      (BSTEP : basic_step e e' S S') 
      (AJF : add_jf w e S S') 
      (wfE: ES.Wf S) :
  release S' ⨾ ⦗E S⦘ ≡ release S ⨾ ⦗E S⦘.
Proof. 
  unfold release at 1.
  rewrite !seqA.
  arewrite (rs S' ⨾ ⦗E S⦘ ≡ ⦗E S⦘ ⨾ rs S ⨾ ⦗E S⦘).
  { rewrite add_jf_rsE; eauto.
    rewrite rsE; auto.
    basic_solver. }
  seq_rewrite basic_step_rel_f_sbE; eauto. 
  unfold release.
  rewrite ES.sbE, rsE; auto.
  basic_solver 20.
Qed.

Lemma add_jf_sw lang k k' st st' w e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (nF' : eq_opt e' ∩₁ F S' ⊆₁ ∅)
      (wfE: ES.Wf S) :
  sw S' ≡ sw S ∪ sw_delta S S' k e e'. 
Proof. 
  cdes AJF; cdes BSTEP_.
  assert (basic_step e e' S S') as BSTEP.
  { econstructor. eauto. }
  unfold sw_delta.
  unfold sw at 1.
  erewrite dom_rel_helper with (r := jf S').
  2 : eapply add_jf_jf_dom; eauto.
  rewrite !seqA, <- seqA.
  rewrite add_jf_releaseE; eauto.
  rewrite !seqA.
  rewrite <- seqA with (r1 := ⦗E S⦘).
  erewrite <- dom_rel_helper with (r := jf S').
  2 : eapply add_jf_jf_dom; eauto.
  rewrite SB', JF'.
  rewrite seq_union_l, cr_union_l.
  relsf. rewrite unionA.
  apply union_more.
  { rewrite basic_step_jf_sb_f_acq; eauto. }
  rewrite crE. relsf.
  rewrite !seqA.
  arewrite_false (sb_delta S k e e' ⨾ ⦗F S'⦘).
  { unfold sb_delta.
    clear -nF' rR'.
    rewrite !seq_union_l, <- !cross_inter_r.
    arewrite (eq e ∩₁ F S' ⊆₁ ∅).
    { type_solver. }
    rewrite nF'.
    basic_solver. }
  arewrite_false (jf_delta w e ⨾ sb S).
  { step_solver. }
  arewrite_false (jf S ⨾ ⦗eq e⦘).
  { step_solver. }
  unfold jf_delta.
  basic_solver 10.
Qed.  

Lemma add_jf_sw_dom lang k k' st st' w e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (nF' : eq_opt e' ∩₁ F S' ⊆₁ ∅)
      (wfE: ES.Wf S) :
  dom_rel (sw S') ⊆₁ E S.
Proof. 
  cdes AJF; cdes BSTEP_.
  rewrite add_jf_sw; eauto.
  step_solver.
Qed.

Lemma add_jf_swE w e e' S S' 
      (BSTEP : basic_step e e' S S') 
      (AJF : add_jf w e S S') 
      (nF' : eq_opt e' ∩₁ F S' ⊆₁ ∅)
      (wfE: ES.Wf S) :
  sw S' ⨾ ⦗E S⦘ ≡ sw S.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite add_jf_sw; eauto.
  relsf. rewrite basic_step_sw_deltaE; eauto.
  rewrite swE; auto. basic_solver 5.
Qed.

Lemma add_jf_hb lang k k' st st' w e e' S S' 
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (nF' : eq_opt e' ∩₁ F S' ⊆₁ ∅)
      (wfE: ES.Wf S) :
  hb S' ≡ hb S ∪ hb_delta S S' k e e'.
Proof.
  cdes AJF; cdes BSTEP_.
  assert (basic_step e e' S S') as BSTEP.
  { subst. econstructor. eauto. }
  unfold hb at 1.
  rewrite SB'. 
  rewrite add_jf_sw; eauto.
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

Lemma add_jf_hb_dom w e e' S S' 
      (BSTEP : basic_step e e' S S') 
      (AJF : add_jf w e S S') 
      (nF' : eq_opt e' ∩₁ F S' ⊆₁ ∅)
      (wfE: ES.Wf S) :
  dom_rel (hb S') ⊆₁ E S ∪₁ eq e.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite add_jf_hb; eauto.
  rewrite dom_union.
  rewrite basic_step_hb_delta_dom; eauto.
  rewrite hbE; auto.
  basic_solver.
Qed.

Lemma add_jf_hbE w e e' S S' 
      (BSTEP : basic_step e e' S S') 
      (AJF : add_jf w e S S') 
      (nF' : eq_opt e' ∩₁ F S' ⊆₁ ∅)
      (wfE: ES.Wf S) :
  hb S' ⨾ ⦗E S⦘ ≡ hb S.
Proof. 
  cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite add_jf_hb; eauto.
  relsf.
  rewrite basic_step_hb_deltaE; eauto.
  rewrite hbE; auto. basic_solver 5.
Qed. 

Lemma add_jf_icf_jf lang k k' st st' w e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (wfE: ES.Wf S) :
  jf S' ⨾ icf S' ⨾ (jf S')⁻¹ ≡
    jf S ⨾ icf S ⨾ (jf S)⁻¹ ∪ 
      (dom_rel (jf S ⨾ ⦗ES.cont_icf_dom S k⦘) × eq w)^⋈.
Proof. 
  cdes AJF; cdes BSTEP_.
  rewrite JF'.
  rewrite transp_union.
  seq_rewrite !seq_union_r.
  rewrite !seq_union_l.
  rewrite <- !unionA.
  do 2 rewrite unionA.
  apply union_more.
  { rewrite basic_step_icf; eauto.
    relsf.
    arewrite_false 
      (jf S ⨾ icf_delta S k e ⨾ (jf S)⁻¹).
    { unfold icf_delta. step_solver. }
    basic_solver 10. }
  arewrite_false
    (jf_delta w e ⨾ icf S' ⨾ (jf_delta w e)⁻¹).
  { rewrite basic_step_icf; eauto.
    unfold icf_delta. relsf. 
    rewrite ES.cont_icf_domE; auto.
    rewrite ES.icfE; auto.
    step_solver. }
  rewrite union_false_r.
  arewrite (
    jf_delta w e ⨾ icf S' ⨾ (jf S)⁻¹ ≡
      (jf S ⨾ icf S' ⨾ (jf_delta w e)⁻¹)⁻¹
  ).
  { rewrite !transp_seq.
    rewrite transp_inv.
    erewrite transp_sym_equiv
      with (r := icf S').
    2 : apply ES.icf_sym. 
    basic_solver. }
  rewrite unionC.
  rewrite <- csE.
  apply clos_sym_more.
  rewrite basic_step_icf; eauto.
  relsf.
  arewrite_false 
    (jf S ⨾ icf S ⨾ (jf_delta w e)⁻¹).
  { rewrite ES.icfE; auto. step_solver. }
  rewrite union_false_l.
  unfold icf_delta.
  rewrite csE. relsf.
  arewrite_false
    (jf S ⨾ eq e × ES.cont_icf_dom S k).
  { step_solver. }
  unfold jf_delta.
  basic_solver 10.
Qed.

Lemma add_jf_icf_jf_irr lang k k' st st' w e e' S S'
      (BSTEP_ : basic_step_ lang k k' st st' e e' S S') 
      (AJF : add_jf w e S S') 
      (EW_RESTR : ⦗E S⦘ ⨾ ew S' ⨾ ⦗E S⦘ ≡ ew S)
      (wfE: ES.Wf S) :
  irreflexive (jf S' ⨾ icf S' ⨾ (jf S')⁻¹ ⨾ ew S') <->
    irreflexive (jf S ⨾ icf S ⨾ (jf S)⁻¹ ⨾ ew S) /\
    ~ dom_rel (ew S ⨾ jf S ⨾ ⦗ES.cont_icf_dom S k⦘) w.
Proof. 
  etransitivity.
  { apply irreflexive_more.
    do 2 rewrite <- seqA.
    rewrite seqA with (r1 := jf S').
    rewrite add_jf_icf_jf. 
    2-4: eauto. 
    rewrite seq_union_l.
    rewrite !seqA.
    done. }
  rewrite irreflexive_union.
  apply Morphisms_Prop.and_iff_morphism.

  { rewrite irreflexive_seqC.
    rewrite !seqA.
    arewrite 
      ((jf S)⁻¹ ⨾ ew S' ⨾ jf S ≡ (jf S)⁻¹ ⨾ ew S ⨾ jf S).
    { rewrite ES.jfE; auto.
      rewrite !transp_seq, !transp_eqv_rel.
      rewrite !seqA.
      seq_rewrite EW_RESTR. 
      rewrite ES.jfE; auto.
      basic_solver 20. }
    do 2 rewrite <- seqA.
    rewrite <- irreflexive_seqC.
    basic_solver. }

  split.  
  { intros IRR HH. 
    destruct HH as [y [z [EW HH]]].
    apply seq_eqv_r in HH.
    destruct HH as [JF ICFd].
    eapply IRR.
    eexists. split.
    { left. red. 
      split; [|done].
      basic_solver 10. }
    apply EW_RESTR in EW.
    unfolder in EW. desf. }
  intros nDD x HH.
  destruct HH as [y [HH EW]].
  destruct HH as [HH|HH].
  { destruct HH as [[z HH] EQy].
    apply seq_eqv_r in HH. subst y.
    destruct HH as [JF kICF].
    apply nDD.
    do 2 eexists. split.
    2 : basic_solver. 
    apply EW_RESTR.
    apply seq_eqv_lr.
    splits; auto.
    { by cdes AJF. }
    apply ES.jfE in JF; auto.
    generalize JF. basic_solver. }
  destruct HH as [[z HH] EQy].
  apply seq_eqv_r in HH. subst x.
  destruct HH as [JF kICF].
  apply nDD.
  do 2 eexists. split.
  2 : basic_solver. 
  apply ES.ew_sym; auto.
  apply EW_RESTR.
  apply seq_eqv_lr.
  splits; auto.
  2 : { by cdes AJF. }
  apply ES.jfE in JF; auto.
  generalize JF. basic_solver.
Qed.    

End AddJF.

(* Section hides the tactics and hints, so we repeat it here.
 * TODO: invent a better solution, 
 *       perhaps it is better to get rid of notation here at all. 
 *)
Hint Unfold jf_delta jfi_delta jfe_delta sw_delta hb_delta : ESStepDb.
