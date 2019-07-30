Require Import Omega.
From hahn Require Import Hahn.
From imm Require Import Events AuxRel. 
Require Import AuxRel.
Require Import AuxDef.
Require Import EventStructure.
Require Import BasicStep.
Require Import AddJF.
Require Import AddEW.
Require Import AddCO.
Require Import Step.

Set Implicit Arguments.

Section ESstepWf.

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
Notation "'ORlx' S" := (fun a => is_true (is_only_rlx S.(ES.lab) a)) (at level 10).
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
Notation "'Loc_' S" := (fun l x => loc S x = l) (at level 1).

(******************************************************************************)
(** ** StepWf ew properties *)
(******************************************************************************)

Lemma step_same_ew_ewE e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (EW' : ew S' ≡ ew S) :
  ew S' ≡ ⦗E S'⦘ ⨾ ew S' ⨾ ⦗E S'⦘. 
Proof. 
  rewrite EW'. rewrite ES.ewE; auto. 
  assert (E S ⊆₁ E S') as Emon.
  { eapply basic_step_acts_set_mon; eauto. }
  basic_solver 10.
Qed.

Lemma step_add_ew_ewE ews w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  ew S' ≡ ⦗E S'⦘ ⨾ ew S' ⨾ ⦗E S'⦘. 
Proof. 
  cdes BSTEP; cdes BSTEP_; cdes AEW.
  rewrite EW'. relsf.
  apply union_more.
  { rewrite ES.ewE; auto.
    erewrite basic_step_acts_set
      with (S' := S'); eauto.
    basic_solver 10. }
  unfold ew_delta.
  rewrite csE, transp_cross.
  relsf. 
  erewrite basic_step_acts_set
      with (S' := S'); eauto.
  rewrite set_unionA, id_union. relsf.
  rewrite <- !cross_inter_r. 
  rewrite <- !cross_inter_l. 
  arewrite (E S ∩₁ eq w' ≡₁ ∅).
  { split; try done. unfolder in wEE'; desf; step_solver. }
  arewrite ((eq e ∪₁ eq_opt e') ∩₁ ews ≡₁ ∅).
  { split; try done. rewrite ewsE. unfolder in wEE'; desf; step_solver. }
  relsf. generalize wEE'. basic_solver 10.
Qed.

Lemma step_same_ew_ewD e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (EW' : ew S' ≡ ew S) :
  ew S' ≡ ⦗W S'⦘ ⨾ ew S' ⨾ ⦗W S'⦘. 
Proof. 
  rewrite EW'.
  arewrite (⦗W S'⦘ ⨾ ew S ⨾ ⦗W S'⦘ ≡ ⦗E S ∩₁ W S'⦘ ⨾ ew S ⨾ ⦗E S ∩₁ W S'⦘).
  { rewrite ES.ewE; auto. basic_solver. }
  erewrite basic_step_w_eq_w; eauto. 
  rewrite ES.ewE, ES.ewD; auto. 
  basic_solver. 
Qed.

Lemma step_add_ew_ewD ews w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  ew S' ≡ ⦗W S'⦘ ⨾ ew S' ⨾ ⦗W S'⦘. 
Proof. 
  cdes BSTEP; cdes BSTEP_; cdes AEW.
  rewrite EW'. relsf.
  apply union_more.
  { arewrite (⦗W S'⦘ ⨾ ew S ⨾ ⦗W S'⦘ ≡ ⦗E S ∩₁ W S'⦘ ⨾ ew S ⨾ ⦗E S ∩₁ W S'⦘).
    { rewrite ES.ewE; auto. basic_solver. }
    erewrite basic_step_w_eq_w; eauto. 
    rewrite ES.ewE, ES.ewD; auto. 
    basic_solver. }
  unfold ew_delta.
  assert (ews ⊆₁ W S') as wsW'.
  { red. ins. unfold is_w.
    arewrite (lab S' x = lab S x).
    { erewrite basic_step_lab_eq_dom; eauto. }
    fold (is_w (lab S) x). basic_solver. }
  basic_solver 10. 
Qed.

Lemma step_same_ew_ewm e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (EW' : ew S' ≡ ew S) :
  ew S' ⊆ (set_compl (Rel S') × set_compl (Rel S'))^?.
Proof. 
  rewrite EW'. 
  intros x y EW.
  assert (E S x) as Ex.
  { apply ES.ewE in EW; auto. 
    generalize EW. basic_solver. }
  assert (E S y) as Ey.
  { apply ES.ewE in EW; auto. 
    generalize EW. basic_solver. }
  apply ES.ewm in EW; auto.
  destruct EW as [EQ | [xRlx yRlx]].
  { basic_solver. }
  unfolder. right. 
  unfold is_rel. 
  erewrite basic_step_mod_eq_dom
    with (S' := S'); eauto.
  erewrite basic_step_mod_eq_dom
    with (S' := S'); eauto.
Qed.

Lemma step_add_ew_ewm ews w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  ew S' ⊆ (set_compl (Rel S') × set_compl (Rel S'))^?.
Proof. 
  cdes AEW.
  rewrite EW'.
  unfold ew_delta. 
  rewrite csE, transp_cross.
  unionL. 
  { intros x y EW.
    assert (E S x) as Ex.
    { apply ES.ewE in EW; auto. 
      generalize EW. basic_solver. }
    assert (E S y) as Ey.
    { apply ES.ewE in EW; auto. 
      generalize EW. basic_solver. }
    apply ES.ewm in EW; auto.
    destruct EW as [EQ | [xRlx yRlx]].
    { basic_solver. }
    unfolder. right. 
    unfold is_rel. 
    erewrite basic_step_mod_eq_dom
      with (S' := S'); eauto.
    erewrite basic_step_mod_eq_dom
      with (S' := S'); eauto. }
  { basic_solver. }
  { intros x y [xEWS EQy]. subst y.
    assert (~ Rel S' x) as nRELx.
    { unfold is_rel in *. 
      erewrite basic_step_mod_eq_dom
        with (S' := S'); eauto. 
      by apply ewsnREL. }
    unfolder. right. split; auto.
    destruct 
      (excluded_middle_informative (Rel S' w'))
      as [wREL | nwREL]; auto.
    exfalso. apply nRELx.
    unfold is_rel. 
    apply ewsMOD in xEWS.
    red in xEWS. by rewrite <- xEWS. }
  intros x y [EQx yEWS]. subst x.
  assert (~ Rel S' y) as nRELy.
  { unfold is_rel.
    erewrite basic_step_mod_eq_dom
      with (S' := S'); eauto. 
    by apply ewsnREL. }
  unfolder. right. split; auto.
  destruct 
    (excluded_middle_informative (Rel S' w'))
    as [wREL | nwREL]; auto.
  exfalso. apply nRELy.
  unfold is_rel. 
  apply ewsMOD in yEWS.
  red in yEWS. by rewrite <- yEWS.
Qed.    

Lemma step_same_ew_ewl e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (EW' : ew S' ≡ ew S) :
  ew S' ⊆ same_loc S'. 
Proof. 
  rewrite EW'. 
  intros x y EW.
  assert 
    ((restr_rel (E S) (same_loc S')) x y) 
    as HH.
  { eapply basic_step_same_loc_restr; eauto.
    unfolder; splits.
    { apply ES.ewl; auto. }
    { apply ES.ewE in EW; auto. 
      generalize EW. basic_solver. }
    apply ES.ewE in EW; auto. 
    generalize EW. basic_solver. }
  generalize HH. basic_solver.
Qed.

Lemma step_add_ew_ewl ews w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  ew S' ⊆ same_loc S'. 
Proof. 
  cdes AEW.
  rewrite EW'.
  unfold ew_delta. 
  rewrite csE, transp_cross.
  rewrite ewsLOC.
  unionL.
  2-4 : basic_solver.
  intros x y EW.
  assert 
    ((restr_rel (E S) (same_loc S')) x y) 
    as HH.
  { eapply basic_step_same_loc_restr; eauto.
    unfolder; splits.
    { apply ES.ewl; auto. }
    { apply ES.ewE in EW; auto. 
      generalize EW. basic_solver. }
    apply ES.ewE in EW; auto. 
    generalize EW. basic_solver. }
  generalize HH. basic_solver. 
Qed.

Lemma step_same_ew_ewv e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (EW' : ew S' ≡ ew S) :
  ew S' ⊆ same_val S'. 
Proof. 
  rewrite EW'. 
  intros x y EW.
  assert 
    ((restr_rel (E S) (same_val S')) x y) 
    as HH.
  { eapply basic_step_same_val_restr; eauto.
    unfolder; splits.
    { apply ES.ewv; auto. }
    { apply ES.ewE in EW; auto. 
      generalize EW. basic_solver. }
    apply ES.ewE in EW; auto. 
    generalize EW. basic_solver. }
  generalize HH. basic_solver.
Qed.

Lemma step_add_ew_ewv ews w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  ew S' ⊆ same_val S'. 
Proof. 
  cdes AEW.
  rewrite EW'.
  unfold ew_delta. 
  rewrite csE, transp_cross.
  rewrite ewsVAL.
  unionL.
  2-4 : basic_solver.
  intros x y EW.
  assert 
    ((restr_rel (E S) (same_val S')) x y) 
    as HH.
  { eapply basic_step_same_val_restr; eauto.
    unfolder; splits.
    { apply ES.ewv; auto. }
    { apply ES.ewE in EW; auto. 
      generalize EW. basic_solver. }
    apply ES.ewE in EW; auto. 
    generalize EW. basic_solver. }
  generalize HH. basic_solver. 
Qed.

Lemma step_add_ew_ewc ews w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  ew S' ⊆ (cf S')^?.
Proof. 
  cdes AEW.
  rewrite EW'.
  unfold ew_delta.
  rewrite ewsCF.
  rewrite csE, transp_cross.
  unionL.
  { rewrite ES.ewc; auto. 
    apply clos_refl_mori.
    eapply basic_step_cf_mon; eauto. }
  { basic_solver. }
  { unfolder. ins. desf. right. by eapply ES.cf_sym. }
  basic_solver.
Qed.

Lemma step_add_ew_ew_refl ews w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') 
      (wWW' : E S' ∩₁ W S' ≡₁ E S ∩₁ W S ∪₁ eq w') : 
  ⦗E S' ∩₁ W S'⦘ ⊆ ew S'.
Proof. 
  cdes BSTEP; cdes BSTEP_; cdes AEW.
  rewrite EW', wWW'.
  rewrite id_union.
  apply union_mori.
  { by apply ES.ew_refl. }
  unfold ew_delta.
  basic_solver.
Qed.

Lemma step_add_ew_ew_trans ews w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  transitive (ew S').
Proof. 
  cdes BSTEP; cdes BSTEP_; cdes AEW.
  rewrite EW'.
  unfold ew_delta.
  rewrite csE, transp_cross.
  apply transitiveI. relsf.
  arewrite_false (eq w' × eq w' ⨾ ew S).
  { unfolder in wEE'; desf; step_solver. }
  arewrite_false (ews × eq w' ⨾ ew S).
  { unfolder in wEE'; desf; step_solver. }
  arewrite_false (ew S ⨾ eq w' × eq w').
  { unfolder in wEE'; desf; step_solver. }
  arewrite_false (eq w' × ews ⨾ eq w' × eq w').
  { rewrite ewsE. unfolder in wEE'; desf; step_solver. }
  arewrite_false (eq w' × eq w' ⨾ ews × eq w').
  { rewrite ewsE. unfolder in wEE'; desf; step_solver. }
  arewrite_false (ews × eq w' ⨾ ews × eq w').
  { rewrite ewsE. unfolder in wEE'; desf; step_solver. }
  arewrite_false (ew S ⨾ eq w' × ews).
  { rewrite ewsE. unfolder in wEE'; desf; step_solver. }
  arewrite_false (eq w' × ews ⨾ eq w' × ews).
  { rewrite ewsE. unfolder in wEE'; desf; step_solver. }
  relsf.
  arewrite (ew S ⨾ ew S ⊆ ew S).
  { apply transitiveI. apply ES.ew_trans; auto. }
  arewrite (eq w' × ews ⨾ ew S ⊆ eq w' × ews).
  { unfolder. ins. desc. 
    splits; auto.
    eapply add_ew_ews_ew_fwcl; eauto. 
    basic_solver 10. }
  arewrite (ew S ⨾ ews × eq w' ⊆ ews × eq w').
  { unfolder. ins. desc. 
    splits; auto.
    eapply ewsEWprcl. basic_solver 10. }
  arewrite (ews × eq w' ⨾ eq w' × ews ⊆ ew S).
  { by rewrite seq_cross_eq. }
  basic_solver 10.
Qed.

Lemma step_add_ew_ew_sym ews w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  symmetric (ew S').
Proof. 
  cdes AEW.
  rewrite EW'.
  unfold ew_delta. 
  apply union_sym.
  { apply ES.ew_sym; auto. } 
  apply union_sym.
  { basic_solver. }
  apply cs_sym.
Qed.

Lemma step_add_ew_ew_co ews ws w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S') 
      (ACO : add_co ews ws w' S S')
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  ew S' ∩ co S' ≡ ∅₂.
Proof. 
  cdes BSTEP; cdes BSTEP_; cdes AEW; cdes ACO.
  split; [|done].
  rewrite EW', CO'.
  rewrite !inter_union_l, !inter_union_r.
  erewrite ES.ew_co; auto.
  arewrite_false (ew S ∩ co_delta ews ws w' S).
  { unfold co_delta.
    unfolder in wEE'; desf; step_solver. }
  arewrite_false (ew_delta ews w' ∩ co S).
  { unfold ew_delta.
    unfolder in wEE'; desf; step_solver. }
  relsf. unfold ew_delta, co_delta.
  rewrite csE, transp_cross.
  rewrite !inter_union_l, !inter_union_r.
  arewrite_false (ews × eq w' ∩ ws × eq w').
  { unfolder. ins. desf. eapply ws_ews. basic_solver. }
  arewrite_false (eq w' × ews ∩ eq w' × ws_compl ews ws S).
  { unfolder. ins. desf. 
    eapply add_co_ews_inter_ws_compl_false; eauto.  
    basic_solver. }
  relsf.
  erewrite add_co_ws_complE; auto.
  rewrite wsE, ewsE.
  unfolder in wEE'; desf; step_solver.
Qed.

Lemma step_add_ew_ew_co_in_co ews ws w' e e' S S'
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S')
      (AEW : add_ew ews w' S S')
      (ACO : add_co ews ws w' S S')
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  ew S' ⨾ co S' ⊆ co S'.
Proof.
  cdes BSTEP; cdes BSTEP_; cdes AEW; cdes ACO.
  rewrite EW', CO'.
  unfold ew_delta, co_delta.
  rewrite !csE, !transp_cross. relsf.
  arewrite_false (eq w' × eq w' ⨾ co S).
  { unfolder in wEE'; desf; step_solver. }
  arewrite_false (ews × eq w' ⨾ co S).
  { unfolder in wEE'; desf; step_solver. }
  arewrite_false (eq w' × eq w' ⨾ ws × eq w').
  { rewrite wsE. unfolder in wEE'; desf; step_solver. }
  arewrite_false (ews × eq w' ⨾ ws × eq w').
  { rewrite wsE. unfolder in wEE'; desf; step_solver. }
  arewrite_false (eq w' × ews ⨾ ws × eq w').
  { unfolder. ins. desf.
    eapply ws_ews. basic_solver. }
  arewrite_false (ew S ⨾ eq w' × ws_compl ews ws S).
  { unfolder in wEE'; desf; step_solver. }
  arewrite_false (eq w' × ews ⨾ eq w' × ws_compl ews ws S).
  { rewrite ewsE at 1. unfolder in wEE'; desf; step_solver. }
  relsf.
  arewrite (ew S ⨾ co S ⊆ co S).
  { by apply ES.ew_co_in_co. }
  arewrite (eq w' × ews ⨾ co S ⊆ eq w' × ws_compl ews ws S).
  { unfolder. ins. desf. splits; auto.
    eapply add_co_ews_co_codom; eauto.
    basic_solver 10. }
  arewrite (ew S ⨾ ws × eq w' ⊆ ws × eq w').
  { unfolder. ins. desf. splits; auto.
    eapply add_co_ws_ew_prcl; eauto.
    basic_solver 10. }
  rewrite !seq_cross_eq.
  erewrite add_co_ews_cross_ws_compl_in_co; eauto.
  basic_solver.
Qed.

Lemma step_add_ew_co_ew_in_co ews ws w' e e' S S'
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S')
      (AEW : add_ew ews w' S S')
      (ACO : add_co ews ws w' S S')
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  co S' ⨾ ew S' ⊆ co S'.
Proof.
  cdes BSTEP; cdes BSTEP_; cdes AEW; cdes ACO.
  rewrite EW', CO'.
  unfold ew_delta, co_delta.
  rewrite !csE, !transp_cross. relsf.
  rewrite !seq_cross_eq.
  arewrite_false (ws × eq w' ⨾ ew S).
  { unfolder in wEE'; desf; step_solver. }
  arewrite_false (co S ⨾ eq w' × eq w').
  { unfolder in wEE'; desf; step_solver. }
  arewrite_false (eq w' × ws_compl ews ws S ⨾ eq w' × eq w').
  { rewrite add_co_ws_complE; auto.
    unfolder in wEE'; desf; step_solver. }
  arewrite_false (ws × eq w' ⨾ ews × eq w').
  { rewrite ewsE; auto.
    unfolder in wEE'; desf; step_solver. }
  arewrite_false (eq w' × ws_compl ews ws S ⨾ ews × eq w').
  { unfolder. ins. desf.
    eapply add_co_ews_inter_ws_compl_false; eauto.
    basic_solver. }
  arewrite_false (co S ⨾ eq w' × ews).
  { unfolder in wEE'; desf; step_solver. }
  arewrite_false (eq w' × ws_compl ews ws S ⨾ eq w' × ews).
  { rewrite add_co_ws_complE; auto.
    unfolder in wEE'; desf; step_solver. }
  relsf.
  arewrite (co S ⨾ ew S ⊆ co S).
  { by apply ES.co_ew_in_co. }
  arewrite (eq w' × ws_compl ews ws S ⨾ ew S ⊆ eq w' × ws_compl ews ws S).
  { unfolder. ins. desf. splits; auto.
    eapply add_co_ws_compl_ew_fwcl; eauto.
    basic_solver 10. }
  arewrite (co S ⨾ ews × eq w' ⊆ ws × eq w').
  { unfolder. ins. desf. splits; auto.
    apply ewsCOprcl. basic_solver 10. }
  arewrite (ws × ews ⊆ co S).
  { eapply add_co_ws_cross_ews_in_co; eauto. } 
  basic_solver.
Qed.

(******************************************************************************)
(** ** StepWf co properties *)
(******************************************************************************)

Lemma step_same_co_coE e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (CO' : co S' ≡ co S) :
  co S' ≡ ⦗E S'⦘ ⨾ co S' ⨾ ⦗E S'⦘. 
Proof. 
  rewrite CO'. rewrite ES.coE; auto. 
  assert (E S ⊆₁ E S') as Emon.
  { eapply basic_step_acts_set_mon; eauto. }
  basic_solver 10.
Qed.

Lemma step_add_co_coE ews ws w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (ACO : add_co ews ws w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  co S' ≡ ⦗E S'⦘ ⨾ co S' ⨾ ⦗E S'⦘. 
Proof. 
  cdes BSTEP; cdes BSTEP_; cdes ACO.
  rewrite CO'. relsf.
  apply union_more.
  { rewrite ES.coE; auto.
    erewrite basic_step_acts_set
      with (S' := S'); eauto.
    basic_solver 10. }
  unfold co_delta.
  rewrite seq_union_l, seq_union_r. apply union_more.
  { erewrite basic_step_acts_set
      with (S' := S'); eauto.
    rewrite set_unionA, id_union. relsf.
    arewrite_false (ws × eq w' ⨾ ⦗E S⦘).
    { unfolder in wEE'; desf; step_solver. }
    arewrite_false (⦗eq e ∪₁ eq_opt e'⦘ ⨾ ws × eq w').
    { rewrite wsE. step_solver. }
    relsf. basic_solver 10. }
  erewrite basic_step_acts_set
      with (S' := S'); eauto.
  rewrite set_unionA, id_union. relsf.
  arewrite_false !(⦗E S⦘ ⨾ eq w' × ws_compl ews ws S).
  { unfolder in wEE'; desf; step_solver. }
  arewrite_false (eq w' × ws_compl ews ws S ⨾ ⦗eq e ∪₁ eq_opt e'⦘).
  { rewrite add_co_ws_complE; auto. step_solver. }
  assert (ws_compl ews ws S ⊆₁ E S).
  { apply add_co_ws_complE; auto. } 
  relsf. basic_solver 10.
Qed.

Lemma step_same_co_coD e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (CO' : co S' ≡ co S) :
  co S' ≡ ⦗W S'⦘ ⨾ co S' ⨾ ⦗W S'⦘. 
Proof. 
  rewrite CO'.
  arewrite (⦗W S'⦘ ⨾ co S ⨾ ⦗W S'⦘ ≡ ⦗E S ∩₁ W S'⦘ ⨾ co S ⨾ ⦗E S ∩₁ W S'⦘).
  { rewrite ES.coE; auto. basic_solver. }
  erewrite basic_step_w_eq_w; eauto. 
  rewrite ES.coE, ES.coD; auto. 
  basic_solver. 
Qed.

Lemma step_add_co_coD ews ws w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (ACO : add_co ews ws w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  co S' ≡ ⦗W S'⦘ ⨾ co S' ⨾ ⦗W S'⦘. 
Proof. 
  cdes BSTEP; cdes BSTEP_; cdes ACO.
  rewrite CO'. relsf.
  apply union_more.
  { arewrite (⦗W S'⦘ ⨾ co S ⨾ ⦗W S'⦘ ≡ ⦗E S ∩₁ W S'⦘ ⨾ co S ⨾ ⦗E S ∩₁ W S'⦘).
    { rewrite ES.coE; auto. basic_solver. }
    erewrite basic_step_w_eq_w; eauto. 
    rewrite ES.coE, ES.coD; auto. 
    basic_solver. }
  unfold co_delta.
  relsf. apply union_more.
  { assert (ws ⊆₁ W S') as wsW'.
    { red. ins. unfold is_w.
      arewrite (lab S' x = lab S x).
      { erewrite basic_step_lab_eq_dom; eauto. }
      fold (is_w (lab S) x). basic_solver. }
    basic_solver 10. }
  assert (ws_compl ews ws S ⊆₁ W S') as wsW'.
  { red. ins. unfold is_w.
    arewrite (lab S' x = lab S x).
    { erewrite basic_step_lab_eq_dom; eauto. 
      eapply add_co_ws_complE; eauto. }
    fold (is_w (lab S) x). 
    eapply add_co_ws_complW; eauto. }
  basic_solver 10.
Qed.

Lemma step_same_co_col e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (CO' : co S' ≡ co S) :
  co S' ⊆ same_loc S'. 
Proof. 
  rewrite CO'. 
  intros x y CO.
  assert 
    ((restr_rel (E S) (same_loc S')) x y) 
    as HH.
  { eapply basic_step_same_loc_restr; eauto.
    unfolder; splits.
    { apply ES.col; auto. }
    { apply ES.coE in CO; auto. 
      generalize CO. basic_solver. }
    apply ES.coE in CO; auto. 
    generalize CO. basic_solver. }
  generalize HH. basic_solver.
Qed.

Lemma step_add_co_col ews ws w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S') 
      (ACO : add_co ews ws w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  co S' ⊆ same_loc S'. 
Proof. 
  cdes ACO.
  rewrite CO'.
  unionL.
  { intros x y CO.
    assert 
      ((restr_rel (E S) (same_loc S')) x y) 
      as HH.
    { eapply basic_step_same_loc_restr; eauto.
      unfolder; splits.
      { apply ES.col; auto. }
      { apply ES.coE in CO; auto. 
        generalize CO. basic_solver. }
      apply ES.coE in CO; auto. 
      generalize CO. basic_solver. }
    generalize HH. basic_solver. }
  { rewrite wsLOC. basic_solver. }
  erewrite add_co_ws_compl_loc; eauto.
  basic_solver.
Qed.

Lemma step_same_co_init e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (CO' : co S' ≡ co S) 
      (WW' : E S' ∩₁ W S' ≡₁ E S ∩₁ W S) : 
  ⦗Einit S'⦘ ⨾ same_loc S' ⨾ ⦗Eninit S' ∩₁ W S'⦘ ⊆ co S'.
Proof. 
  assert (Eninit S' ∩₁ W S' ≡₁ Eninit S ∩₁ W S) as WW.
  { unfold ES.acts_ninit_set.
    rewrite !set_inter_minus_l. rewrite WW'.
    erewrite basic_step_acts_init_set; eauto. }

  rewrite WW, CO'. 
  rewrite basic_step_acts_init_set; eauto.
  rewrite <- seq_eqvK with (dom := Einit S).
  rewrite <- seq_eqvK with (dom := Eninit S ∩₁ W S).
  rewrite seqA.
  arewrite (⦗Einit S⦘ ⨾ same_loc S' ⨾ ⦗Eninit S ∩₁ W S⦘ ⊆ same_loc S).
  2: by apply ES.co_init.
  arewrite (Einit S ⊆₁ E S).
  { unfold ES.acts_init_set. basic_solver. }
  arewrite (Eninit S ∩₁ W S ⊆₁ E S).
  { unfold ES.acts_ninit_set. basic_solver. }
  rewrite <- restr_relE.
  rewrite basic_step_same_loc_restr; eauto.
  basic_solver.
Qed.

Lemma step_add_co_co_init ews ws w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S') 
      (ACO : add_co ews ws w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') 
      (WW' : E S' ∩₁ W S' ≡₁ E S ∩₁ W S ∪₁ eq w') : 
  ⦗Einit S'⦘ ⨾ same_loc S' ⨾ ⦗Eninit S' ∩₁ W S'⦘ ⊆ co S'.
Proof. 
  cdes ACO.
  assert (Eninit S' ∩₁ W S' ≡₁ Eninit S ∩₁ W S ∪₁ eq w') as WW.
  { unfold ES.acts_ninit_set.
    rewrite !set_inter_minus_l. rewrite WW'.
    erewrite basic_step_acts_init_set; eauto.
    rewrite set_minus_union_l.
    arewrite (eq w' \₁ Einit S ≡₁ eq w'); [|done].
    split; [basic_solver|].
    unfolder. ins. desf.
    splits; auto.
    intros [AA BB].
    red in wEE'. desf.
    { eapply basic_step_acts_set_ne in AA; eauto. }
    red in wEE'. desf.
    eapply basic_step_acts_set_ne' in AA; eauto. }
  rewrite WW, CO'.
  rewrite id_union. relsf.
  rewrite basic_step_acts_init_set; eauto.
  apply union_mori.
  { rewrite <- seq_eqvK with (dom := Einit S).
    rewrite <- seq_eqvK with (dom := Eninit S ∩₁ W S).
    rewrite seqA.
    arewrite (⦗Einit S⦘ ⨾ same_loc S' ⨾ ⦗Eninit S ∩₁ W S⦘ ⊆ same_loc S).
    2: by apply ES.co_init.
    arewrite (Einit S ⊆₁ E S).
    { unfold ES.acts_init_set. basic_solver. }
    arewrite (Eninit S ∩₁ W S ⊆₁ E S).
    { unfold ES.acts_ninit_set. basic_solver. }
    rewrite <- restr_relE.
    rewrite basic_step_same_loc_restr; eauto.
    basic_solver. }
  unfold co_delta.
  apply inclusion_union_r. left.
  rewrite seq_eqv_lr.
  intros x y [xInit [eqLOC EQy]]. subst y.
  unfolder; split; auto.
  apply wsEinit.
  unfolder; split; auto.
  red in eqLOC.
  arewrite (loc S x = loc S' x); auto.
  symmetry. 
  eapply basic_step_loc_eq_dom; eauto.
  apply xInit.
Qed.

Lemma step_add_co_irr ews ws w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (ACO : add_co ews ws w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  irreflexive (co S').
Proof. 
  cdes BSTEP; cdes BSTEP_; cdes ACO. 
  rewrite CO'.
  unfold co_delta.
  unfolder. 
  intros x [CO | [[wWS EQx] | [EQx wWS]]]. 
  { eapply ES.co_irr; eauto. }
  { subst x. apply wsE in wWS.
    unfolder in wEE'. 
    desf; step_solver. }
  subst x. apply add_co_ws_complE in wWS; eauto.
  unfolder in wEE'. 
  desf; step_solver.
Qed.

Lemma step_add_co_trans ews ws w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S')
      (ACO : add_co ews ws w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  transitive (co S').
Proof. 
  cdes BSTEP; cdes BSTEP_; cdes ACO. 
  apply transitiveI.
  rewrite CO'.
  unfold co_delta.
  relsf.
  arewrite_false (ws × eq w' ⨾ co S).
  { unfolder in wEE'; desf; step_solver. } 
  arewrite_false (ws × eq w' ⨾ ws × eq w').
  { rewrite wsE. unfolder in wEE'; desf; step_solver. } 
  arewrite_false (co S ⨾ eq w' × ws_compl ews ws S).
  { erewrite add_co_ws_complE; auto. unfolder in wEE'; desf; step_solver. }
  arewrite_false (eq w' × ws_compl ews ws S ⨾ eq w' × ws_compl ews ws S).
  { erewrite add_co_ws_complE; auto. unfolder in wEE'; desf; step_solver. }
  arewrite_false (eq w' × ws_compl ews ws S ⨾ ws × eq w').
  { unfolder. ins. desf.
    eapply add_co_ws_inter_ws_compl_false; eauto.
    basic_solver. }
  relsf.
  arewrite (co S ⨾ co S ⊆ co S).
  { apply transitiveI. by apply ES.co_trans. }
  arewrite (eq w' × ws_compl ews ws S ⨾ co S ⊆ eq w' × ws_compl ews ws S).
  { unfolder. ins. desc. splits; auto.
    eapply add_co_ws_compl_co_fwcl; eauto. basic_solver 10. }
  arewrite (co S ⨾ ws × eq w' ⊆ ws × eq w').
  { unfolder. ins. desc. splits; auto.
    eapply add_co_ws_co_prcl; eauto. basic_solver 10. }
  arewrite (ws × eq w' ⨾ eq w' × ws_compl ews ws S ⊆ co S).
  { unfolder. ins. desf.
    eapply add_co_ws_cross_ws_compl_in_co; eauto.
    basic_solver. }
  basic_solver.
Qed.    

Lemma step_same_co_total e e' S S'
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S')
      (EW' : ew S' ≡ ew S) 
      (CO' : co S' ≡ co S) 
      (WW' : E S' ∩₁ W S' ≡₁ E S ∩₁ W S) : 
  forall ol a b 
             (aW : (E S' ∩₁ W S' ∩₁ Loc_ S' ol) a) 
             (bW : (E S' ∩₁ W S' ∩₁ Loc_ S' ol) b) 
             (nEW : ~ ew S' a b),
        co S' a b \/ co S' b a.
Proof. 
  ins. 
  assert ((E S ∩₁ W S) a) as Ha.
  { apply WW'. generalize aW. basic_solver. }
  assert ((E S ∩₁ W S) b) as Hb.
  { apply WW'. generalize bW. basic_solver. }
  destruct Ha as [aE aWW]. destruct Hb as [bE bWW].
  assert (loc S a = ol) as aLOC.
  { arewrite (loc S a = loc S' a).
    { symmetry. eapply basic_step_loc_eq_dom; eauto. }
    generalize aW. basic_solver. }
  assert (loc S b = ol) as bLOC.
  { arewrite (loc S b = loc S' b).
    { symmetry. eapply basic_step_loc_eq_dom; eauto. }
    generalize bW. basic_solver. }
  assert ((co S) a b \/ (co S) b a) as HCO.
  { eapply ES.co_total; eauto.
    { unfolder; splits; try apply aLOC; auto. } 
    { unfolder; splits; auto. } 
    intros EW. 
    by apply nEW, EW'. }
  generalize CO' HCO. basic_solver.
Qed.

Lemma add_co_split_writes ews ws w' S S'
      (wfE : ES.Wf S) 
      (ACO : add_co ews ws w' S S') : 
  E S ∩₁ W S ∩₁ Loc_ S (loc S' w') \₁ ews ⊆₁ 
  ws ∪₁ ws_compl ews ws S.
Proof. 
  cdes ACO.
  intros w [[[wE wW] eqLOC] nEWS].
  destruct 
    (excluded_middle_informative (ws w))
    as [wWS | nwWS].
  { by left. }
  right. unfold ws_compl. unfolder. splits.
  2 : red; ins; desf.
  edestruct is_w_loc as [l wLOC]; eauto.
  edestruct ES.initL as [wi [wiInit wiLOC]]; eauto.
  exists wi, wi. splits; auto.
  { right. eapply wsEinit.
    split; auto. congruence. }
  apply ES.co_init; auto.
  apply seq_eqv_lr; unfolder; splits; auto.
  { red. congruence. }
  split; auto.
  intros HH.
  apply nwWS. apply wsEinit.
  split; auto.
Qed.

Lemma step_add_co_total_helper ews ws w' e e' S S'
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S')
      (AEW : add_ew ews w' S S')
      (ACO : add_co ews ws w' S S')
      (wEE' : (eq e ∪₁ eq_opt e') w')
      (WW' : E S' ∩₁ W S' ≡₁ E S ∩₁ W S ∪₁ eq w') : 
  forall a (aW : (E S ∩₁ W S ∩₁ Loc_ S (loc S' w')) a) 
         (nEW : ~ (ew S') a w'),
      co S' a w' \/ co S' w' a.
Proof. 
  ins. 
  destruct aW as [[aE aW] aLOC].
  edestruct 
    add_co_split_writes
    as [aWS | anWS]; eauto.
  { unfolder; splits; eauto.
    cdes AEW. intros aEWS. 
    eapply nEW. apply EW'.
    unfold ew_delta.
    basic_solver 10. }
  { left. cdes ACO. apply CO'. 
    unfold co_delta.
    basic_solver. }
  right. cdes ACO. apply CO'.
  unfold co_delta.
  basic_solver.
Qed.

Lemma step_add_co_total ews ws w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S') 
      (ACO : add_co ews ws w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') 
      (wWW' : E S' ∩₁ W S' ≡₁ E S ∩₁ W S ∪₁ eq w') : 
  forall ol a b 
             (aW : (E S' ∩₁ W S' ∩₁ Loc_ S' ol) a) 
             (bW : (E S' ∩₁ W S' ∩₁ Loc_ S' ol) b) 
             (nEW : ~ ew S' a b),
        co S' a b \/ co S' b a.
Proof. 
  ins. 
  destruct 
    (classic (loc S' w' = ol))
    as [lEQ | lnEQ].
  { subst ol.
    assert ((E S ∩₁ W S ∪₁ eq w') a) as Ha.
    { apply wWW'. generalize aW. basic_solver. }
    assert ((E S ∩₁ W S ∪₁ eq w') b) as Hb.
    { apply wWW'. generalize bW. basic_solver. }
    destruct (Ha, Hb) as [[[Ea Wa] | EQa] [[Eb Wb] | EQb]];
      clear Ha Hb.
    { assert (loc S a = loc S' w') as aLOC.
      { eapply basic_step_loc_in_loc; eauto.
        generalize aW. basic_solver. }
      assert (loc S b = loc S' w') as bLOC.
      { eapply basic_step_loc_in_loc; eauto.
        generalize bW. basic_solver. }
      assert ((co S) a b \/ (co S) b a) as HCO.
      { eapply ES.co_total; eauto.
        { unfolder; splits; try apply aLOC; auto. } 
        { unfolder; splits; auto. } 
        intros EW. apply nEW.
        cdes AEW. apply EW'. by left. }
      destruct HCO as [COab | COba].
      { cdes ACO. left. apply CO'. basic_solver. }
      cdes ACO. right. apply CO'. basic_solver. }
    { subst b. eapply step_add_co_total_helper; eauto. 
      unfolder; splits; auto. 
      eapply basic_step_loc_in_loc; eauto.
      generalize aW. basic_solver. }
    { subst a. apply or_comm. 
      eapply step_add_co_total_helper; eauto. 
      unfolder; splits; auto.
      { eapply basic_step_loc_in_loc; eauto. 
        generalize bW. basic_solver. }
      red. ins. apply nEW. 
      eapply step_add_ew_ew_sym; eauto. }
    exfalso. subst a b. apply nEW. 
    cdes AEW. apply EW'. 
    unfold ew_delta.
    basic_solver. }
  assert ((E S ∩₁ W S) a) as Ha.
  { destruct aW as [HH LOCa].
    apply wWW' in HH.
    unfolder in HH. desf. }
  assert ((E S ∩₁ W S) b) as Hb.
  { destruct bW as [HH LOCb].
    apply wWW' in HH.
    unfolder in HH. desf. }
  destruct Ha as [aE aWW].
  destruct Hb as [bE bWW].
  assert (loc S a = ol) as aLOC.
  { arewrite (loc S a = loc S' a).
    { symmetry. eapply basic_step_loc_eq_dom; eauto. }
    generalize aW. basic_solver. }
  assert (loc S b = ol) as bLOC.
  { arewrite (loc S b = loc S' b).
    { symmetry. eapply basic_step_loc_eq_dom; eauto. }
    generalize bW. basic_solver. }
  assert ((co S) a b \/ (co S) b a) as HCO.
  { eapply ES.co_total; eauto.
    { unfolder; splits; try apply aLOC; auto. } 
    { unfolder; splits; auto. } 
    intros EW. apply nEW. 
    cdes AEW. apply EW'. basic_solver. }
  destruct HCO as [COab | COba].
  { cdes ACO. left. apply CO'. basic_solver. }
  cdes ACO. right. apply CO'. basic_solver.
Qed.  

(******************************************************************************)
(** ** StepWf Lemma *)
(******************************************************************************)

Lemma step_wf S S' e e'
      (WF : ES.Wf S)
      (ILOC : forall l (LL : loc S' e = Some l), ES.init_loc S' l)
      (TT    : step_ e e' S S')
      (BSTEP : basic_step e e' S S') :
  ES.Wf S'.
Proof.
  assert (E S ⊆₁ E S') as EES.
  { rewrite basic_step_acts_set with (S':=S'); eauto.
    basic_solver. }
  assert (eq e ⊆₁ E S') as EIES.
  { rewrite basic_step_acts_set; eauto.
    basic_solver. }
  assert (eq_opt e' ⊆₁ E S') as EIES'.
  { rewrite basic_step_acts_set; eauto.
    basic_solver. }

  assert (~ E S (ES.next_act S)) as NES.
  { intros HH. red in HH. omega. }
  assert (~ E S (Datatypes.S (ES.next_act S))) as NESN.
  { intros HH. red in HH. omega. }

  assert (forall l (HH : ES.init_loc S l), ES.init_loc S' l) as PP.
  { ins. red. cdes HH. exists a. split.
    2: { erewrite basic_step_loc_eq_dom; eauto.
         apply EINA. }
    split.
    { eapply basic_step_acts_set; eauto.
      do 2 left. apply EINA. }
    erewrite basic_step_tid_eq_dom; eauto.
    all: apply EINA. }
  
  constructor.
  { ins; desf.
    cdes BSTEP. cdes BSTEP_.
    ins; subst.
    eapply basic_step_acts_set in EB; eauto.
    destruct EB as [[EB|EB]|EB].
    { apply PP. eapply WF; eauto.
      erewrite <- basic_step_loc_eq_dom; eauto. }
    all: apply ILOC.
    { by rewrite EB. }
    rewrite <- LB.
    red in EB. desf.
    red in LABEL'. desf.
    red in TT. desf; cdes TT; desf. }
  { ins.
    set (EE:=INIT).
    eapply basic_step_acts_init_set with (S:=S) in EE; eauto.
    apply WF.(ES.init_lab) in EE. desf.
    eexists.
    assert ((E S) e0) as HH.
    { eapply basic_step_acts_init_set with (S:=S) in INIT; eauto.
      apply INIT. }
    edestruct basic_step_tid_eq_dom; eauto.
    rewrite <- EE.
    eapply basic_step_lab_eq_dom; eauto. }
  { rewrite basic_step_acts_init_set with (S:=S); eauto.
    red. ins.
    erewrite basic_step_loc_eq_dom in EQ; eauto.
    2: by apply SX.
    erewrite basic_step_loc_eq_dom with (S:=S) (S':=S')in EQ;
      eauto.
    2: by apply SY.
    eapply WF; auto. }
  { apply dom_helper_3.
    cdes BSTEP. cdes BSTEP_.
    rewrite SB'.
    unfold sb_delta.
    rewrite ES.cont_sb_domE; eauto.
    arewrite (sb S ⊆ E S × E S).
    { rewrite WF.(ES.sbE) at 1. basic_solver. }
    sin_rewrite !EES.
    sin_rewrite !EIES.
    sin_rewrite !EIES'.
    basic_solver. }
  { rewrite basic_step_acts_init_set; eauto.
    rewrite basic_step_acts_ninit_set; eauto.
    rewrite set_unionA. rewrite cross_union_l.
    cdes BSTEP. cdes BSTEP_.
    rewrite SB'. apply union_mori.
    unionL.
    { by rewrite WF.(ES.sb_init). }
    unfold sb_delta.
    rewrite ES.cont_sb_dom_Einit; eauto.
    basic_solver. }
  { rewrite basic_step_acts_init_set; eauto.
    cdes BSTEP. cdes BSTEP_.
    rewrite SB'. rewrite seq_union_l.
    rewrite WF.(ES.sb_ninit).
    split; [|basic_solver].
    arewrite (Einit S ⊆₁ E S).
    { unfold ES.acts_init_set. basic_solver. }
    rewrite basic_step_sb_deltaE; eauto.
    basic_solver. }
  { cdes BSTEP. cdes BSTEP_.
    rewrite SB'. rewrite seq_union_r.
    unionL.
    { rewrite (dom_l WF.(ES.sbE)), <- seqA.
      rewrite <- id_inter.
      arewrite (Eninit S' ∩₁ E S ⊆₁ Eninit S).
      { unfold ES.acts_ninit_set.
        erewrite basic_step_acts_init_set with (S:=S); eauto.
        basic_solver. }
      rewrite <- inclusion_restr with (r:=ES.same_tid S')
                                      (dom:=S.(ES.acts_set)).
      arewrite (⦗Eninit S⦘ ⨾ sb S ⊆ restr_rel (E S) (⦗Eninit S⦘ ⨾ sb S)).
      { rewrite WF.(ES.sbE) at 1. basic_solver. }
      rewrite basic_step_same_tid_restr; eauto.
      apply restr_rel_mori; auto.
      apply WF. }
    unfold sb_delta.
    arewrite (eq e ⊆₁ fun x => tid S' x = ES.cont_thread S k).
    { unfolder. ins. desf. eapply basic_step_tid_e; eauto. }
    arewrite (eq_opt e' ⊆₁ fun x => tid S' x = ES.cont_thread S k).
    { unfolder. ins. desf. eapply basic_step_tid_e'; eauto. }
    rewrite !seq_union_r, <- !cross_inter_l.
    arewrite (Eninit S' ∩₁ ES.cont_sb_dom S k ⊆₁
                     fun x => tid S' x = ES.cont_thread S k).
    2: { unfold ES.same_tid. unfolder. ins. desf.
         all: by match goal with
         | H : ?X = ES.cont_thread ?S ?k |- _ => rewrite H
         end. }
    arewrite (ES.cont_sb_dom S k ⊆₁ E S ∩₁ ES.cont_sb_dom S k).
    { apply set_subset_inter_r; split; auto.
      eapply ES.cont_sb_domE; eauto. }
    rewrite <- set_interA.
    arewrite (Eninit S' ∩₁ E S ⊆₁ Eninit S).
    { rewrite basic_step_acts_ninit_set; eauto.
      rewrite !set_inter_union_l.
      unionL.
      { basic_solver. }
      all: unfolder; ins; desf; simpls; desf.
      all: match goal with
      | H : (E ?S) ?X |- _ => red in H
      end.
      all: omega. }
    arewrite (Eninit S ∩₁ ES.cont_sb_dom S k ⊆₁
              ES.cont_sb_dom S k \₁ Einit S ∪₁ ES.cont_cf_dom S k).
    { unfold ES.acts_ninit_set. basic_solver. }
    rewrite <- ES.cont_thread_sb_cf; eauto.
    unfolder. ins. desf.
    match goal with
    | H : ?X = ES.cont_thread ?S ?k |- _ => rewrite <- H
    end.
    eapply basic_step_tid_eq_dom; eauto. }
  { eapply basic_step_sb_irr; eauto. }
  { eapply basic_step_sb_trans; eauto. }
  { eapply basic_step_sb_prcl; eauto. }
  { ins. erewrite basic_step_acts_init_set; eauto.
    eapply basic_step_acts_set in EE; eauto.
    cdes BSTEP. cdes BSTEP_.
    assert (is_total (ES.cont_sb_dom S k \₁ Einit S) (sb S)) as CC.
    { unfold ES.cont_sb_dom. desf.
      { basic_solver. }
      red. ins.
      red in IWa. red in IWb. desf.
      destruct IWa as [eida IWa]. destruct_seq_r IWa as AA.
      destruct IWb as [eidb IWb]. destruct_seq_r IWb as BB.
      destruct IWa as [|SBA];
        destruct IWb as [|SBB]; desf.
      { by right. }
      { by left. }
      eapply WF.(ES.sb_tot); auto.
      2,3: split; auto; eexists; apply seq_eqv_r; split; eauto.
      apply (dom_r WF.(ES.sbE)) in SBB. by destruct_seq_r SBB as BB. }

    destruct EE as [[EE|EE]|EE]; desf.
    { arewrite (⦗eq e0⦘ ⊆ ⦗E S⦘ ⨾ ⦗eq e0⦘).
      { generalize EE. basic_solver. }
      arewrite (sb S' ⨾ ⦗E S⦘ ⊆ sb S).
      { eapply basic_step_sbE; eauto. }
      eapply is_total_mori.
      3: by apply WF; eauto.
      { done. }
      rewrite SB'. basic_solver. }
    { rewrite SB' at 1. rewrite seq_union_l.
      arewrite (sb S ⨾ ⦗eq (ES.next_act S)⦘ ⊆ ∅₂).
      { rewrite (dom_r WF.(ES.sbE)), !seqA.
        unfolder. ins. desf. }
      unfold sb_delta.
      rewrite !seq_union_l.
      rewrite <- !cross_inter_r.
      arewrite (eq_opt e' ∩₁ eq (ES.next_act S) ⊆₁ ∅).
      { unfolder. ins. desf. simpls. omega. }
      relsf.
      2 : { intros HH. eapply HH. edone. }
      eapply is_total_mori.
      { reflexivity. }
      { rewrite SB'. unionR left. reflexivity. }
      apply CC. }
    rewrite SB' at 1. rewrite seq_union_l.
    arewrite (sb S ⨾ ⦗eq e0⦘ ⊆ ∅₂).
    { rewrite (dom_r WF.(ES.sbE)), !seqA.
      unfolder. ins. desf.
      match goal with
      | H : (E ?S) ?X |- _ => red in H
      end.
      red in EE.
      simpls; desf. simpls. omega. }
    unfold sb_delta.
    rewrite seq_union_l.
    rewrite <- !cross_inter_r.
    assert (eq e0 ∩₁ eq (ES.next_act S) ⊆₁ ∅) as DD.
    { red in EE. desf. unfolder. ins. desf. simpls. omega. }
    rewrite set_interC. 
    relsf.
    2: { intros HH. eapply HH. split; eauto. }
    rewrite SB'.
    red. ins.
    destruct IWa as [IWa|IWa];
    destruct IWb as [IWb|IWb].
    { assert (sb S a b \/ sb S b a) as RR.
      { unfolder in IWa.
        unfolder in IWb.
        apply CC; auto; desf. }
      generalize RR. basic_solver. }
    3: by inv IWa; inv IWb.
    all: unfold sb_delta.
    all: generalize IWa IWb; basic_solver 10. }
  { rewrite basic_step_acts_set; eauto.
    assert
      (E S ⊆₁ codom_rel
         (⦗fun x0 : eventid => ES.seqn S' x0 = 0⦘ ⨾
          (sb S')^? ∩ ES.same_tid S')) as AA.
    { intros x EX.
      set (XX := EX).
      apply WF.(ES.seqn_after_null) in XX.
      red in XX. destruct XX as [y XX].
      destruct_seq_l XX as YY. destruct XX as [SB ST].
      assert (E S y) as EY.
      { destruct SB as [|SB]; desf.
        apply (dom_l WF.(ES.sbE)) in SB.
          by destruct_seq_l SB as OO. }
      exists y. apply seq_eqv_l; split.
      { rewrite <- YY.
        eapply basic_step_seqn_eq_dom; eauto. }
      split.
      { cdes BSTEP. cdes BSTEP_.
        destruct SB as [|SB]; desf; [by left|right].
        apply SB'. by left. }
      red.
      repeat
        (erewrite basic_step_tid_eq_dom with (S':=S'); eauto). }

    assert
      (exists x,
          (⦗fun x : eventid => ES.seqn S' x = 0⦘ ⨾
           (sb S')^? ∩ ES.same_tid S') x e) as [x EE].
    { cdes BSTEP. destruct k.
      { exists e. apply seq_eqv_l. split.
        2: { split; [left|red]; done. }
        eapply basic_step_seqn_kinit; eauto. }
      assert (E S eid) as EEID.
      { cdes BSTEP_. eapply WF.(ES.K_inEninit); eauto. }
      set (EE:=EEID).
      apply AA in EE. red in EE. desf.
      exists x. destruct_seq_l EE as XX.
      apply seq_eqv_l. split; auto.
      split.
      { right. eapply rewrite_trans_seq_cr_l.
        { eapply basic_step_sb_trans; eauto. }
        eexists. split.
        { apply EE. }
        cdes BSTEP_.
        apply SB'. right.
        red. left. left. red. split; auto.
        red. red. 
        eexists. apply seq_eqv_r. split; eauto. }
      red. destruct EE as [_ EE]. rewrite EE.
      erewrite basic_step_tid_e with (e:=e); eauto.
      arewrite (tid S' eid = tid S eid).
      { eapply basic_step_tid_eq_dom; eauto. }
      cdes BSTEP_. desf. }

    unionL; auto.
    { red. intros y HH; desf. rename y into e.
      eexists. eauto. }
    destruct_seq_l EE as CC.
    destruct EE as [EE DD].
    red. intros y HH.
    cdes BSTEP. cdes BSTEP_.
    red in HH. desf. rename y into e'.
    exists x. apply seq_eqv_l. split; auto.
    split; [right|].
    { eapply rewrite_trans_seq_cr_l.
      { eapply basic_step_sb_trans; eauto. }
      eexists. split.
      { apply EE. }
      apply SB'. unfold sb_delta. basic_solver 10. }
    red. rewrite DD.
    rewrite TID'. simpls. rewrite upds.
    rewrite updo.
    { by rewrite upds. }
    omega. }
  { apply dom_helper_3.
    cdes BSTEP. cdes BSTEP_.
    rewrite RMW'. unionL.
    { rewrite WF.(ES.rmwD), WF.(ES.rmwE), !seqA.
      rewrite <- id_inter, <- !seqA, <- id_inter.
      rewrite set_interC, <- basic_step_r_ex_eq_r_ex; eauto.
      rewrite <- basic_step_w_eq_w; eauto.
      basic_solver. }
    unfold rmw_delta.
    intros x y [AA BB]. red in BB. desf.
    red in TT. desf; cdes TT; desf; auto.
    cdes ACO. cdes AJF.
    red. split; auto. }
  { cdes BSTEP. cdes BSTEP_.
    rewrite RMW'. unionL.
    { rewrite WF.(ES.rmwE). unfolder. ins. desf.
      eapply basic_step_same_loc_restr; eauto.
      red. splits; auto. by apply WF.(ES.rmwl). }
    unfold rmw_delta.
    intros x y [AA BB]. red in BB. desf.
    red in TT. desf; cdes TT; desf; auto. }
  { cdes BSTEP. cdes BSTEP_.
    rewrite SB'. rewrite RMW'.
    rewrite WF.(ES.rmwE). unfold rmw_delta.
    rewrite WF.(ES.sbE).
    arewrite (sb_delta S k e e' ≡
              ⦗ E S ∪₁ eq e ⦘ ⨾ sb_delta S k e e' ⨾ ⦗ set_compl (E S) ⦘).
    { split; [|basic_solver].
      arewrite (sb_delta S k e e' ⊆
                sb_delta S k e e' ⨾ ⦗ E S ∪₁ set_compl (E S) ⦘).
      { rewrite set_compl_union_id. basic_solver. }
      rewrite id_union, seq_union_r.
      rewrite basic_step_sb_deltaE; eauto.
      rewrite union_false_l.
      hahn_frame.
      apply dom_rel_helper_in.
      eapply basic_step_sb_delta_dom; eauto. }
    unionL.
    { intros x y RMW. destruct_seq RMW as [XX YY].
      red. split.
      { left. apply seq_eqv_l. split; auto.
        apply seq_eqv_r. split; auto.
          by apply WF.(ES.rmwi). }
      ins.
      destruct R1 as [R1|R1]; destruct_seq R1 as [A1 B1];
        destruct R2 as [R2|R2]; destruct_seq R2 as [A2 B2]; desf.
      eapply WF.(ES.rmwi); eauto. }
    intros x y [CC DD]; subst. red in DD. desf.
    red. split.
    { right. apply seq_eqv_l. split.
      { by right. }
      apply seq_eqv_r. split.
      2: { red. intros AA. red in AA. simpls. omega. }
      red. right. red. split.
      { done. }
        by red. }
    ins.
    destruct R1 as [R1|R1]; destruct_seq R1 as [A1 B1];
      destruct R2 as [R2|R2]; destruct_seq R2 as [A2 B2]; desf.
    destruct A1 as [A1|A1]; desf.
    destruct A2 as [A2|A2]; desf.
    red in R1. destruct R1 as [[R1|R1]|R1]; red in R1; simpls; desf.
    2,3: omega.
    eapply ES.cont_sb_domE in R1; eauto. }
  { split; [|basic_solver].
    red in TT. desf; cdes TT; desf.
    2,4: cdes AJF.
    all: rewrite JF'; unionL.
    1,2,4,6: rewrite WF.(ES.jfE) at 1; sin_rewrite !EES; basic_solver.
    all: unfold jf_delta; apply EES in wE; generalize wE rE'; basic_solver. }
  { split; [|basic_solver].
    assert (jf S ⊆ ⦗W S'⦘ ⨾ jf S ⨾ ⦗R S'⦘) as AA.
    { rewrite WF.(ES.jfD) at 1.
      rewrite WF.(ES.jfE) at 2.
      rewrite !seqA.
      rewrite <- id_inter, <- !seqA, <- id_inter.
      rewrite set_interC with (s:=W S').
      rewrite basic_step_w_eq_w; eauto.
      rewrite basic_step_r_eq_r; eauto.
      rewrite WF.(ES.jfE) at 1.
      basic_solver 10. }
    red in TT. desf; cdes TT; desf.
    2,4: cdes AJF.
    all: rewrite JF'; unionL; auto.
    1,3: rewrite AA at 1; basic_solver.
    all: assert (W S' w) as WW
        by (eapply basic_step_w_eq_w; eauto; by split);
      generalize WW rR'; unfold jf_delta;
        basic_solver. }
  { assert (jf S ⊆ same_loc S') as AA.
    { rewrite WF.(ES.jfE). intros x y HH.
      destruct_seq HH as [EX EY].
      eapply basic_step_same_loc_restr; eauto.
      red. split; auto. by apply WF.(ES.jfl). }
    red in TT. desf; cdes TT; desf.
    2,4: cdes AJF.
    all: rewrite JF'; unionL; auto.
    all: unfold jf_delta; unfolder; intros x y HH; desf. }
  { assert (funeq (val S') (jf S)) as AA.
    { rewrite WF.(ES.jfE). intros x y HH.
      destruct_seq HH as [EX EY].
      eapply basic_step_same_val_restr; eauto.
      red. split; auto. by apply WF.(ES.jfv). }
    red in TT. desf; cdes TT; desf.
    2,4: cdes AJF.
    all: rewrite JF'; try apply funeq_union; auto.
    all: unfold jf_delta; unfolder; intros x y HH; desf. }
  { assert (functional (jf S)⁻¹) as AA by apply WF.
    red in TT. desf; cdes TT; desf.
    2,4: cdes AJF.
    all: rewrite JF'; try rewrite transp_union; auto.
    all: apply functional_union; auto.
    1,3: by unfold jf_delta, singl_rel, transp; red; ins; desf. 
    all: unfold jf_delta; unfolder.
    all: intros x [y JF] HH; desf.
    all: apply (dom_r WF.(ES.jfE)) in JF; destruct_seq_r JF as EE.
    all: eapply basic_step_acts_set_ne; eauto. }
  { assert (jf S ⊆ jf S') as BB.
    { cdes BSTEP. cdes BSTEP_.
      red in TT. desf; cdes TT; desf.
      2,4: cdes AJF.
      all: rewrite JF'; basic_solver. }
    assert (E S ∩₁ R S' ⊆₁ codom_rel (jf S')) as AA.
    { rewrite <- BB.
      rewrite basic_step_r_eq_r; eauto.
      apply WF. }
    rewrite basic_step_acts_set; eauto.
    rewrite !set_inter_union_l.
    rewrite set_unionA.
    apply set_subset_union_l. split; auto.
    cdes BSTEP. cdes BSTEP_.
    red in TT. desf; cdes TT; desf.
    3: cdes AEW.
    1,3: type_solver.
    all: cdes AJF; rewrite JF'.
    all: rewrite codom_union; unionR right.
    all: unfold eq_opt, jf_delta.
    { basic_solver. }
    unfolder. ins. desf; eauto.
    cdes ACO. type_solver. }
  { split; [|basic_solver].
    cdes BSTEP. cdes BSTEP_.
    assert (jf S ∩ ((ES.cont_cf_dom S k × eq (ES.next_act S)) ^⋈) ⊆ ∅₂)
      as BB.
    { rewrite WF.(ES.jfE). generalize NES. basic_solver. }
    assert (jf S ∩ cf_delta S k (ES.next_act S) None ⊆ ∅₂) as AA.
    { ins. unfold cf_delta; simpls.
      arewrite ((ES.cont_cf_dom S k × eq_opt None)^⋈ ⊆ ∅₂).
        by rewrite union_false_r. }
    red in TT. desf; cdes TT; desf; try cdes AJF; rewrite JF'.
    2,4: unfold jf_delta; rewrite inter_union_l; unionL;
      [|generalize nCF; basic_solver].
    all: rewrite basic_step_cf; eauto;
      rewrite inter_union_r; unionL; [by apply WF|]; auto.
    unfold cf_delta; simpls. subst.
    unfold eq_opt; auto.
    rewrite inter_union_r. unionL; auto.
    rewrite WF.(ES.jfE). generalize NESN. basic_solver 10. }

  (* co and ew properties *)
  { red in TT. desf; cdes TT; desf.
    1,2 : eapply step_same_co_coE; eauto. 
    all : eapply step_add_co_coE; eauto; basic_solver. }
  { red in TT. desf; cdes TT; desf.
    1,2 : eapply step_same_co_coD; eauto. 
    all : eapply step_add_co_coD; eauto; basic_solver. }
  { red in TT. desf; cdes TT; desf.
    1,2 : eapply step_same_co_col; eauto. 
    all : eapply step_add_co_col; eauto; basic_solver. }
  { red in TT. desf; cdes TT; desf.
    1,2 : eapply step_same_co_init; eauto. 
    { eapply fence_step_W; eauto. }
    { eapply load_step_W; eauto. }
    all : eapply step_add_co_co_init; eauto. 
    1,3 : basic_solver.
    { eapply store_step_W; eauto. }
    eapply update_step_W; eauto. }
  { red in TT. desf; cdes TT; desf.
    1,2 : rewrite CO'; apply ES.co_irr; auto. 
    all : eapply step_add_co_irr; eauto; basic_solver. }
  { red in TT. desf; cdes TT; desf.
    1,2 : rewrite CO'; apply ES.co_trans; auto. 
    all : eapply step_add_co_trans; eauto; basic_solver. }
  { red in TT. desf; cdes TT; desf.
    { eapply step_same_co_total; eauto.
      eapply fence_step_W; eauto. }
    { eapply step_same_co_total; eauto.
      eapply load_step_W; eauto. }
    { eapply step_add_co_total; eauto.
      { basic_solver. }
      eapply store_step_W; eauto. }
    eapply step_add_co_total; eauto.
    { basic_solver. }
    eapply update_step_W; eauto. }

  { red in TT. desf; cdes TT; desf.
    1,2 : eapply step_same_ew_ewE; eauto. 
    all : eapply step_add_ew_ewE; eauto; basic_solver. }
  { red in TT. desf; cdes TT; desf.
    1,2 : eapply step_same_ew_ewD; eauto. 
    all : eapply step_add_ew_ewD; eauto; basic_solver. }
  { red in TT. desf; cdes TT; desf.
    1,2 : eapply step_same_ew_ewm; eauto. 
    all : eapply step_add_ew_ewm; eauto; basic_solver. }
  { red in TT. desf; cdes TT; desf.
    1,2 : eapply step_same_ew_ewl; eauto. 
    all : eapply step_add_ew_ewl; eauto; basic_solver. }
  { red in TT. desf; cdes TT; desf.
    1,2 : eapply step_same_ew_ewv; eauto. 
    all : eapply step_add_ew_ewv; eauto; basic_solver. }
  { red in TT. desf; cdes TT; desf.
    1,2 : rewrite EW', ES.ewc; auto; 
          apply clos_refl_mori; eapply basic_step_cf_mon; eauto.
    all : eapply step_add_ew_ewc; eauto; basic_solver. }
  { red in TT. desf; cdes TT; desf.
    { rewrite EW'. erewrite fence_step_W; eauto. by apply ES.ew_refl. }
    { rewrite EW'. erewrite load_step_W; eauto. by apply ES.ew_refl. }
    all : eapply step_add_ew_ew_refl; eauto. 
    1,3 : basic_solver.
    { erewrite store_step_W; eauto. }
    erewrite update_step_W; eauto. }
  { red in TT. desf; cdes TT; desf.
    1,2 : rewrite EW'; apply ES.ew_sym; auto. 
    all : eapply step_add_ew_ew_sym; eauto; basic_solver. }
  { red in TT. desf; cdes TT; desf.
    1,2 : rewrite EW'; apply ES.ew_trans; auto. 
    all : eapply step_add_ew_ew_trans; eauto; basic_solver. }
  { red in TT. desf; cdes TT; desf.
    1,2 : rewrite EW', CO'; apply ES.ew_co; auto. 
    all : eapply step_add_ew_ew_co; eauto; basic_solver. }
  { red in TT. desf; cdes TT; desf.
    1,2 : rewrite EW', CO'; apply ES.ew_co_in_co; auto. 
    all : eapply step_add_ew_ew_co_in_co; eauto; basic_solver. }
  { red in TT. desf; cdes TT; desf.
    1,2 : rewrite EW', CO'; apply ES.co_ew_in_co; auto. 
    all : eapply step_add_ew_co_ew_in_co; eauto; basic_solver. }

  { red. ins. desf.
    red in KK. unfold ES.cont_thread in CTK.
    cdes BSTEP. cdes BSTEP_.
    rewrite CONT' in KK.
    inv KK.
    2: { apply WF.(ES.init_tid_K).
         do 2 eexists. splits; eauto.
         unfold ES.cont_thread; desf.
         rewrite <- CTK. symmetry.
         eapply basic_step_tid_eq_dom; eauto.
         eapply ES.K_inEninit; eauto. }
    simpls.
    unfold opt_ext in CTK. rewrite TID' in CTK.
    unfold upd_opt in CTK. desf.
    all: rewrite upds in *.
    all: eapply WF.(ES.init_tid_K); eauto. }
  { cdes BSTEP. cdes BSTEP_.
    unfold ES.cont_set. rewrite CONT'.
    intros HH. desf.
    red in RMW. desf.
    apply RMW' in RMW. destruct RMW as [RMW|RMW].
    { inv KK.
      { apply (dom_l WF.(ES.rmwE)) in RMW.
        destruct_seq_l RMW as EE.
        unfold opt_ext in *. desf. }
      apply WF.(ES.rmw_K). do 2 eexists. splits; eauto.
      red. eauto. }
    unfold opt_ext in *.
    red in RMW. 
    unfold eq_opt in *. inv RMW. desf.
    inv KK; [omega|].
    destruct c. apply NES. eapply ES.K_inE; eauto. }
  { ins. red in CK. red in CK'.
    cdes BSTEP. cdes BSTEP_.
    rewrite CONT' in *.
    inv CK; inv CK'.
    3: { eapply WF.(ES.unique_K); eauto. }
    destruct c' as [k' langst'].
    2: destruct c as [k' langst'].
    all: simpls; subst.
    all: unfold opt_ext in *.
    all: destruct e'.
    all: exfalso.
    1,3: eapply basic_step_acts_set_ne'; eauto;
      eapply ES.K_inEninit; eauto.
    all: eapply basic_step_acts_set_ne; eauto;
      eapply ES.K_inEninit; eauto. }
  { ins. destruct EE as [AA BB].
    eapply basic_step_acts_set in AA; eauto.
    assert (~ (Einit S) e0) as CC.
    { intros HH. apply BB.
      eapply basic_step_acts_init_set; eauto. }
    cdes BSTEP. cdes BSTEP_.
    assert (~ dom_rel (rmw S) e0) as DD.
    { intros HH. apply NRMW.
      destruct HH.
      eexists. apply RMW'. basic_solver. }
    unfold ES.cont_set. rewrite CONT'.
    subst.
    destruct AA as [[AA|AA]|AA].
    { edestruct ES.event_K as [y HH]; eauto.
      { by split. }
      basic_solver. }
    { subst. unfold opt_ext.
      destruct e'.
      2: { eexists. unnw. subst. constructor. eauto. }
      exfalso. apply NRMW. eexists. apply RMW'.
      right. red. red. simpls. }
    red in AA. desf. unfold opt_ext.
    eexists. unnw. constructor. eauto. }
  { ins. cdes BSTEP. cdes BSTEP_. desf.
    red in inK. rewrite CONT' in inK.
    inv inK.
    2: { eapply basic_step_acts_ninit_set; eauto.
         repeat left. eapply WF.(ES.K_inEninit); eauto. }
    eapply basic_step_acts_ninit_set; eauto.
    unfold opt_ext. basic_solver. }
  { eapply basic_step_K_adj; eauto. }
Qed.
 
End ESstepWf.
