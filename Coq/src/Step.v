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
  ⟪ BSTEP : ESBasicStep.t e e' S S' ⟫ /\
  ⟪ CON : @es_consistent S' m ⟫.

(******************************************************************************)
(** ** Load step properties *)
(******************************************************************************)

Lemma load_step_E e e' S S'
      (BSTEP : ESBasicStep.t e e' S S')
      (LSTEP: t_load e e' S S') :
  E S' ≡₁ E S ∪₁ eq e.
Proof. 
  assert (e' = None) by inv LSTEP. subst.
    by apply ESBasicStep.basic_step_nupd_acts_set.
Qed.

Lemma load_step_R e e' S S'
      (LSTEP: t_load e e' S S') :
  R S' e.
Proof. apply LSTEP. Qed.

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

Lemma load_step_jf_dom e e' S S'
      (BSTEP : ESBasicStep.t e e' S S')
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
      (BSTEP : ESBasicStep.t e e' S S')
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
      (BSTEP : ESBasicStep.t e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) : 
  jfe S' ≡ jfe S ∪ jfe S' ⨾ ⦗eq e⦘.
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  unfold ES.jfe.
  erewrite ESBasicStep.basic_step_nupd_sb. 
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
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  (sb S' ∪ jf S')＊ ≡ (sb S ∪ jf S)＊ ⨾ (ES.cont_sb_dom S k × eq e ∪ jf S' ⨾ ⦗eq e⦘)^?. 
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP_.
  assert (ESBasicStep.t e e' S S') as BSTEP.
  { econstructor. eauto. }
  erewrite ESBasicStep.basic_step_nupd_sb. 
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
      (BSTEP : ESBasicStep.t e e' S S')
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
    split; [|done]. ESBasicStep.step_solver. }
  arewrite (singl_rel w e ⨾ ⦗eq e⦘ ≡ singl_rel w e); 
    basic_solver 10.
Admitted.

Lemma load_step_rf_dom e e' S S'
      (BSTEP : ESBasicStep.t e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) : 
  dom_rel (rf S') ⊆₁ E S.
Proof. 
  erewrite load_step_rf; eauto. 
  rewrite dom_union.
  unionL.
  { rewrite ES.rfE; auto. basic_solver. }
  rewrite ES.ewE; auto. 
  rewrite dom_rel_helper with (r := jf S').
  2 : eapply load_step_jf_dom; eauto. 
  basic_solver.
Qed.

Lemma load_step_jf_rmw e e' S S'
      (BSTEP : ESBasicStep.t e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) : 
  jf S' ⨾ rmw S' ≡ jf S ⨾ rmw S.
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite ESBasicStep.basic_step_nupd_rmw; [|subst;eauto].
  rewrite JF'.
  rewrite seq_union_l. 
  arewrite_false (singl_rel w e ⨾ rmw S).
  { ESBasicStep.step_solver. }
  basic_solver.
Qed.

Lemma load_step_rf_rmw e e' S S'
      (BSTEP : ESBasicStep.t e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) : 
  rf S' ⨾ rmw S' ≡ rf S ⨾ rmw S.
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  rewrite ESBasicStep.basic_step_nupd_rmw; eauto.
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
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  cc S' ≡ cc S ∪ 
     ES.cont_cf_dom S k × eq e ∩ 
     (jfe S ⨾ (sb S ∪ jf S)＊ ⨾ (jfe S ⨾ ES.cont_sb_dom S k × eq e ∪ jfe S')). 
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP_.
  assert (ESBasicStep.t e e' S S') as BSTEP.
  { econstructor. eauto. }
  unfold cc. 
  erewrite load_step_sb_jf; eauto. 
  erewrite ESBasicStep.basic_step_nupd_sb with (S' := S'). 
  2 : { desf; eauto. }
  erewrite ESBasicStep.basic_step_nupd_cf; eauto. 
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
        { eapply ESBasicStep.type_step_eq_dom with (S' := S'); eauto. done. }
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
      { eapply ESBasicStep.type_step_eq_dom with (S' := S'); eauto. done. }
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
    eapply ESBasicStep.basic_step_acts_set_ne; eauto. desf. }
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
      (BSTEP : ESBasicStep.t e e' S S')
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
      (BSTEP : ESBasicStep.t e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) : 
  vis S ⊆₁ vis S'. 
Proof. 
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  unfold vis. 
  intros x VIS.
  splits; desf.
  { eapply ESBasicStep.basic_step_acts_set_mon; eauto. }
  arewrite (eq x ⊆₁ E S ∩₁ eq x) by basic_solver.
  unfold set_inter. rewrite <- seq_eqv.
  rewrite <- seqA.
  erewrite load_step_cc_seqE; eauto. 
  rewrite EW'.
  etransitivity; eauto.  
  apply seq_mori; [done|]. 
  apply clos_refl_sym_mori. 
  eapply ESBasicStep.basic_step_sb_mon; eauto.  
Qed.
  
Lemma load_step_rs e e' S S' 
      (BSTEP : ESBasicStep.t e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  rs S' ≡ rs S.
Proof.
  assert (e' = None) by inv LSTEP. subst.
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.
  assert (ES.Wf S') as wfE'.
  { admit. (* eapply step_wf; unfold t_; eauto. *) }
  rewrite !rs_alt; auto.
  rewrite ESBasicStep.basic_step_nupd_sb, load_step_w, load_step_jf_rmw; eauto.
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
  rewrite <- ESBasicStep.basic_step_same_loc_restr; eauto.
Admitted.

Lemma load_step_release e e' S S' 
      (BSTEP : ESBasicStep.t e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  release S' ≡ release S. 
Proof. 
  assert (e' = None) by inv LSTEP. subst.
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.  
  assert (ES.Wf S') as wfE'.
  { admit. (* eapply step_wf; unfold t_; eauto. *) }
  rewrite !release_alt; auto.
  rewrite ESBasicStep.basic_step_nupd_sb, load_step_rel, load_step_f, load_step_rs; eauto.
  do 2 rewrite crE.
  relsf.
  apply union_more; auto.
  rewrite !seqA.
  arewrite (ES.cont_sb_dom S k × eq e ⨾ rs S ≡ ∅₂); 
    [|basic_solver 10].
  rewrite rsE; auto.
  arewrite (ES.cont_sb_dom S k × eq e ⨾ ⦗E S⦘ ≡ ∅₂); 
    [ split; [|done]; ESBasicStep.step_solver | basic_solver ].
Admitted.

Lemma load_step_sw e e' S S' 
      (BSTEP : ESBasicStep.t e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  sw S' ≡ sw S ∪ release S ⨾ jf S' ⨾ ⦗Acq S'⦘ ⨾ ⦗eq e⦘. 
Proof.
  assert (e' = None) by inv LSTEP. subst.
  cdes LSTEP; cdes AJF; cdes BSTEP; cdes BSTEP_.  
  assert (ES.Wf S') as wfE'.
  { admit. (* eapply step_wf; unfold t_; eauto. *) }
  rewrite !sw_alt; auto.
  rewrite JF'.
  rewrite 
    load_step_release, load_step_f, load_step_acq,
    ESBasicStep.basic_step_nupd_sb;
    eauto.
  rewrite id_union.
  rewrite !crE.
  relsf.
  rewrite !unionA.
  apply union_more; auto.
  apply union_more; auto.
  rewrite id_union, !id_inter, !seq_union_r.
  arewrite_false (ES.cont_sb_dom S k × eq e ⨾ ⦗E S⦘).
  { ESBasicStep.step_solver. }
  arewrite_false (⦗E S⦘ ⨾ ⦗F S⦘ ⨾ ⦗eq e⦘).
  { ESBasicStep.step_solver. }
  arewrite_false (jf S ⨾ ⦗eq e⦘).
  { ESBasicStep.step_solver. }
  rewrite <- !seqA with (r1 := singl_rel w e).
  arewrite_false (singl_rel w e ⨾ ⦗E S⦘).
  { ESBasicStep.step_solver. }
  rewrite <- !seqA with (r1 := singl_rel w e).
  arewrite_false (singl_rel w e ⨾ sb S).
  { ESBasicStep.step_solver. }
  arewrite_false (jf S ⨾ ⦗Acq S'⦘ ⨾ ⦗eq e⦘). 
  { ESBasicStep.step_solver. }
  basic_solver 20.
Admitted.

Lemma load_step_hb lang k k' st st' e e' S S' 
      (BSTEP_ : ESBasicStep.t_ lang k k' st st' e e' S S') 
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  hb S' ≡ hb S ∪ 
     (hb S)^? ⨾ (ES.cont_sb_dom S k × eq e ∪ release S ⨾ jf S' ⨾ ⦗Acq S'⦘ ⨾ ⦗eq e⦘). 
Proof.
  assert (e' = None) by inv LSTEP. subst.
  assert (ESBasicStep.t e None S S') as BSTEP.
  { econstructor. eauto. }
  cdes LSTEP; cdes AJF; cdes BSTEP_; desf.
  unfold hb at 1.
  rewrite ESBasicStep.basic_step_nupd_sb, load_step_sw; eauto.
  rewrite unionA.
  rewrite (unionAC (ES.cont_sb_dom S k × eq (ES.next_act S))).
  rewrite <- (unionA (sb S)).
  rewrite unionC.
  erewrite clos_trans_union_ext.
  { rewrite <- cr_of_ct.
    fold (hb S).
    basic_solver. }
  all : split; [|done].
  all : rewrite JF'.
  all : relsf; unionL.
  all : by ESBasicStep.step_solver.
Qed.

Lemma load_step_hb_dom e e' S S'
      (BSTEP : ESBasicStep.t e e' S S')
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
      (BSTEP : ESBasicStep.t e e' S S')
      (LSTEP: t_load e e' S S') 
      (wfE: ES.Wf S) :
  hb S' ⨾ ⦗E S⦘ ≡ hb S.
Proof. 
  cdes BSTEP. cdes BSTEP_. cdes LSTEP. cdes AJF.
  rewrite load_step_hb; eauto.
  rewrite seq_union_l, !seqA.
  arewrite (
      (ES.cont_sb_dom S k × eq e ∪ release S ⨾ jf S' ⨾ ⦗Acq S'⦘ ⨾ ⦗eq e⦘) ⨾ ⦗E S⦘ ≡ ∅₂
  ). 
 { split; [|done]. 
   rewrite JF'.
   ESBasicStep.step_solver. }
  rewrite hbE; auto.
  basic_solver 20.
Qed.

End ESstep.