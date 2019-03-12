Require Import Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events AuxRel. 
Require Import AuxRel AuxDef EventStructure Consistency BasicStep Step.

Set Implicit Arguments.

Export ListNotations.

Section ESstepWf.

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
Notation "'Loc_' S" := (fun l x => loc S x = l) (at level 1).

(******************************************************************************)
(** ** StepWf co properties *)
(******************************************************************************)

Lemma step_same_co_coE e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : ESBasicStep.t e e' S S') 
      (CO' : co S' ≡ co S) :
  co S' ≡ ⦗E S'⦘ ⨾ co S' ⨾ ⦗E S'⦘. 
Proof. 
  rewrite CO'. rewrite ES.coE; auto. 
  assert (E S ⊆₁ E S') as Emon.
  { eapply ESBasicStep.basic_step_acts_set_mon; eauto. }
  basic_solver 10.
Qed.

Lemma step_add_co_coE ews ws w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : ESBasicStep.t e e' S S') 
      (ACO : ESstep.add_co ews ws w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  co S' ≡ ⦗E S'⦘ ⨾ co S' ⨾ ⦗E S'⦘. 
Proof. 
  cdes BSTEP; cdes BSTEP_; cdes ACO.
  rewrite CO'. relsf.
  apply union_more.
  { rewrite ES.coE; auto.
    erewrite ESBasicStep.basic_step_acts_set
      with (S' := S'); eauto.
    basic_solver 10. }
  unfold ESstep.co_delta.
  rewrite seq_union_l, seq_union_r. apply union_more.
  { erewrite ESBasicStep.basic_step_acts_set
      with (S' := S'); eauto.
    rewrite set_unionA, id_union. relsf.
    arewrite_false (ws × eq w' ⨾ ⦗E S⦘).
    { unfolder in wEE'; desf; ESBasicStep.step_solver. }
    arewrite_false (⦗eq e ∪₁ eq_opt e'⦘ ⨾ ws × eq w').
    { rewrite wsE. ESBasicStep.step_solver. }
    relsf. basic_solver 10. }
  erewrite ESBasicStep.basic_step_acts_set
      with (S' := S'); eauto.
  rewrite set_unionA, id_union. relsf.
  arewrite_false !(⦗E S⦘ ⨾ eq w' × ESstep.ws_compl ews ws S).
  { unfolder in wEE'; desf; ESBasicStep.step_solver. }
  arewrite_false (eq w' × ESstep.ws_compl ews ws S ⨾ ⦗eq e ∪₁ eq_opt e'⦘).
  { rewrite ESstep.ws_complE; auto. ESBasicStep.step_solver. }
  assert (ESstep.ws_compl ews ws S ⊆₁ E S).
  { apply ESstep.ws_complE; auto. } 
  relsf. basic_solver 10.
Qed.

Lemma step_same_co_coD e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : ESBasicStep.t e e' S S') 
      (CO' : co S' ≡ co S) :
  co S' ≡ ⦗W S'⦘ ⨾ co S' ⨾ ⦗W S'⦘. 
Proof. 
  rewrite CO'.
  arewrite (⦗W S'⦘ ⨾ co S ⨾ ⦗W S'⦘ ≡ ⦗E S ∩₁ W S'⦘ ⨾ co S ⨾ ⦗E S ∩₁ W S'⦘).
  { rewrite ES.coE; auto. basic_solver. }
  erewrite ESstep.basic_step_w_eq_w; eauto. 
  rewrite ES.coE, ES.coD; auto. 
  basic_solver. 
Qed.

Lemma step_add_co_coD ews ws w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : ESBasicStep.t e e' S S') 
      (ACO : ESstep.add_co ews ws w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  co S' ≡ ⦗W S'⦘ ⨾ co S' ⨾ ⦗W S'⦘. 
Proof. 
  cdes BSTEP; cdes BSTEP_; cdes ACO.
  rewrite CO'. relsf.
  apply union_more.
  { arewrite (⦗W S'⦘ ⨾ co S ⨾ ⦗W S'⦘ ≡ ⦗E S ∩₁ W S'⦘ ⨾ co S ⨾ ⦗E S ∩₁ W S'⦘).
    { rewrite ES.coE; auto. basic_solver. }
    erewrite ESstep.basic_step_w_eq_w; eauto. 
    rewrite ES.coE, ES.coD; auto. 
    basic_solver. }
  unfold ESstep.co_delta.
  relsf. apply union_more.
  { assert (ws ⊆₁ W S') as wsW'.
    { red. ins. unfold is_w.
      arewrite (lab S' x = lab S x).
      { erewrite ESBasicStep.basic_step_lab_eq_dom; eauto. }
      fold (is_w (lab S) x). basic_solver. }
    basic_solver 10. }
  assert (ESstep.ws_compl ews ws S ⊆₁ W S') as wsW'.
  { red. ins. unfold is_w.
    arewrite (lab S' x = lab S x).
    { erewrite ESBasicStep.basic_step_lab_eq_dom; eauto. 
      eapply ESstep.ws_complE; eauto. }
    fold (is_w (lab S) x). 
    eapply ESstep.ws_complW; eauto. }
  basic_solver 10.
Qed.

Lemma step_same_co_col e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : ESBasicStep.t e e' S S') 
      (CO' : co S' ≡ co S) :
  co S' ⊆ same_loc S'. 
Proof. 
  rewrite CO'. 
  intros x y CO.
  assert 
    ((restr_rel (E S) (same_loc S')) x y) 
    as HH.
  { eapply ESBasicStep.basic_step_same_loc_restr; eauto.
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
      (BSTEP : ESBasicStep.t e e' S S') 
      (AEW : ESstep.add_ew ews w' S S') 
      (ACO : ESstep.add_co ews ws w' S S') 
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
    { eapply ESBasicStep.basic_step_same_loc_restr; eauto.
      unfolder; splits.
      { apply ES.col; auto. }
      { apply ES.coE in CO; auto. 
        generalize CO. basic_solver. }
      apply ES.coE in CO; auto. 
      generalize CO. basic_solver. }
    generalize HH. basic_solver. }
  { rewrite wsLOC. basic_solver. }
  erewrite ESstep.ws_compl_loc; eauto.
  basic_solver.
Qed.

Lemma step_same_co_connex_helper e e' S S'
      (wfE: ES.Wf S)
      (BSTEP : ESBasicStep.t e e' S S')
      (CO' : co S' ≡ co S) 
      (WW' : E S' ∩₁ W S' ≡₁ E S ∩₁ W S) : 
  forall ol a b 
             (aW : (E S' ∩₁ W S' ∩₁ Loc_ S' ol) a) 
             (bW : (E S' ∩₁ W S' ∩₁ Loc_ S' ol) b) 
             (nEQ : a <> b) (nCF : ~ cf S' a b),
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
    { symmetry. eapply ESBasicStep.basic_step_loc_eq_dom; eauto. }
    generalize aW. basic_solver. }
  assert (loc S b = ol) as bLOC.
  { arewrite (loc S b = loc S' b).
    { symmetry. eapply ESBasicStep.basic_step_loc_eq_dom; eauto. }
    generalize bW. basic_solver. }
  assert ((co S) a b \/ (co S) b a) as HCO.
  { eapply ES.co_connex; eauto.
    { unfolder; splits; try apply aLOC; auto. } 
    { unfolder; splits; auto. } 
    intros CF. eapply ESBasicStep.basic_step_cf_restr in CF; eauto.
    apply nCF. generalize CF. basic_solver. }
  generalize CO' HCO. basic_solver.
Qed.

Lemma add_co_split_writes ews ws w' S S'
      (wfE : ES.Wf S) 
      (ACO : ESstep.add_co ews ws w' S S') : 
  E S ∩₁ W S ∩₁ Loc_ S (loc S' w') \₁ ews ⊆₁ 
    (ws ∪₁ codom_rel (⦗ews ∪₁ ws⦘ ⨾ co S) \₁ (ews ∪₁ ws)).
Proof. 
  cdes ACO.
  intros w [[[wE wW] eqLOC] nEWS].
  destruct 
    (excluded_middle_informative (ws w))
    as [wWS | nwWS].
  { by left. }
  right. unfolder. splits.
  2 : red; ins; desf.
  edestruct is_w_loc as [l wLOC]; eauto.
  edestruct ES.initL as [wi [wiInit wiLOC]]; eauto.
  exists wi, wi. splits; auto.
  { right. eapply wsEinit.
    split; auto. congruence. }
  admit. 
Admitted.

Lemma step_add_co_connex_helper ews ws w' e e' S S'
      (wfE: ES.Wf S)
      (BSTEP : ESBasicStep.t e e' S S')
      (AEW : ESstep.add_ew ews w' S S')
      (ACO : ESstep.add_co ews ws w' S S')
      (wEE' : (eq e ∪₁ eq_opt e') w')
      (WW' : E S' ∩₁ W S' ≡₁ E S ∩₁ W S ∪₁ eq w') : 
  forall a (aW : (E S ∩₁ W S ∩₁ Loc_ S' (loc S' w')) a) 
         (nCF : ~ (cf S') a w')
         (nEQ : a <> w'),
      co S' a w' \/ co S' w' a.
Proof. 
  ins. 
  destruct aW as [[aE aW] aLOC].
  edestruct 
    add_co_split_writes
    as [aWS | anWS]; eauto.
  { unfolder; splits; eauto.
    { arewrite (loc S a = loc S' a); auto.
      symmetry. eapply ESBasicStep.basic_step_loc_eq_dom; eauto. }
    cdes AEW. intros aEWS. 
    eapply nCF. apply ES.cf_sym. 
    generalize aEWS ewsCF. basic_solver 10. }
  { left. cdes ACO. apply CO'. 
    autounfold with ESStepDb.
    basic_solver. }
  right. cdes ACO. apply CO'. 
  autounfold with ESStepDb.
  generalize anWS. basic_solver.   
Qed.

Lemma step_add_co_connex ews ws w' e e' S S' 
      (wfE: ES.Wf S)
      (BSTEP : ESBasicStep.t e e' S S') 
      (AEW : ESstep.add_ew ews w' S S') 
      (ACO : ESstep.add_co ews ws w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') 
      (wWW' : E S' ∩₁ W S' ≡₁ E S ∩₁ W S ∪₁ eq w') : 
  forall ol a b 
             (aW : (E S' ∩₁ W S' ∩₁ Loc_ S' ol) a) 
             (bW : (E S' ∩₁ W S' ∩₁ Loc_ S' ol) b) 
             (nEQ : a <> b) (nCF : ~ cf S' a b),
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
      { arewrite (loc S a = loc S' a).
        { symmetry. eapply ESBasicStep.basic_step_loc_eq_dom; eauto. }
        generalize aW. basic_solver. }
      assert (loc S b = loc S' w') as bLOC.
      { arewrite (loc S b = loc S' b).
        { symmetry. eapply ESBasicStep.basic_step_loc_eq_dom; eauto. }
        generalize bW. basic_solver. }
      assert ((co S) a b \/ (co S) b a) as HCO.
      { eapply ES.co_connex; eauto.
        { unfolder; splits; try apply aLOC; auto. } 
        { unfolder; splits; auto. } 
        intros CF. eapply ESBasicStep.basic_step_cf_restr in CF; eauto.
        apply nCF. generalize CF. basic_solver. }
      destruct HCO as [COab | COba].
      { cdes ACO. left. apply CO'. basic_solver. }
      cdes ACO. right. apply CO'. basic_solver. }
    { subst b. eapply step_add_co_connex_helper; eauto. 
      unfolder; splits; auto. generalize aW. basic_solver. }
    { subst a. apply or_comm. eapply step_add_co_connex_helper; eauto. 
      unfolder; splits; auto. generalize bW. basic_solver. 
      red. ins. apply nCF. by apply ES.cf_sym. }
    exfalso. congruence. }
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
    { symmetry. eapply ESBasicStep.basic_step_loc_eq_dom; eauto. }
    generalize aW. basic_solver. }
  assert (loc S b = ol) as bLOC.
  { arewrite (loc S b = loc S' b).
    { symmetry. eapply ESBasicStep.basic_step_loc_eq_dom; eauto. }
    generalize bW. basic_solver. }
  assert ((co S) a b \/ (co S) b a) as HCO.
  { eapply ES.co_connex; eauto.
    { unfolder; splits; try apply aLOC; auto. } 
    { unfolder; splits; auto. } 
    intros CF. eapply ESBasicStep.basic_step_cf_restr in CF; eauto.
    apply nCF. generalize CF. basic_solver. }
  destruct HCO as [COab | COba].
  { cdes ACO. left. apply CO'. basic_solver. }
  cdes ACO. right. apply CO'. basic_solver.
Qed.  

(******************************************************************************)
(** ** StepWf Lemma *)
(******************************************************************************)

Lemma step_wf S S' e e'
      (WF : ES.Wf S)
      (TT    : ESstep.t_ e e' S S')
      (BSTEP : ESBasicStep.t e e' S S') :
  ES.Wf S'.
Proof.
  assert (E S ⊆₁ E S') as EES.
  { rewrite ESBasicStep.basic_step_acts_set with (S':=S'); eauto.
    basic_solver. }
  assert (eq e ⊆₁ E S') as EIES.
  { rewrite ESBasicStep.basic_step_acts_set; eauto.
    basic_solver. }
  assert (eq_opt e' ⊆₁ E S') as EIES'.
  { rewrite ESBasicStep.basic_step_acts_set; eauto.
    basic_solver. }
  
  constructor.
  { ins; desf.
    (* TODO :
       Currently, it's not provable.
       We need to state somehow that there is an initial write for
       every location mentioned in the program used to construct
       an event structure. *)
    admit. }
  { ins.
    set (EE:=INIT).
    eapply ESBasicStep.basic_step_acts_init_set with (S:=S) in EE; eauto.
    apply WF.(ES.init_lab) in EE. desf.
    eexists.
    assert ((E S) e0) as HH.
    { eapply ESBasicStep.basic_step_acts_init_set with (S:=S) in INIT; eauto.
      apply INIT. }
    edestruct ESBasicStep.basic_step_tid_eq_dom; eauto.
    rewrite <- EE.
    eapply ESBasicStep.basic_step_lab_eq_dom; eauto. }
  { rewrite ESBasicStep.basic_step_acts_init_set with (S:=S); eauto.
    red. ins.
    erewrite ESBasicStep.basic_step_loc_eq_dom in EQ; eauto.
    2: by apply SX.
    erewrite ESBasicStep.basic_step_loc_eq_dom with (S:=S) (S':=S')in EQ;
      eauto.
    2: by apply SY.
    eapply WF; auto. }
  { apply dom_helper_3.
    cdes BSTEP. cdes BSTEP_.
    rewrite SB'.
    unfold ESBasicStep.sb_delta.
    rewrite ES.cont_sb_domE; eauto.
    arewrite (sb S ⊆ E S × E S).
    { rewrite WF.(ES.sbE) at 1. basic_solver. }
    sin_rewrite EES.
    sin_rewrite EIES.
    sin_rewrite EIES'.
    basic_solver. }
  { rewrite ESBasicStep.basic_step_acts_init_set; eauto.
    rewrite ESBasicStep.basic_step_acts_ninit_set; eauto.
    rewrite set_unionA. rewrite cross_union_l.
    cdes BSTEP. cdes BSTEP_.
    rewrite SB'. apply union_mori.
    unionL.
    { by rewrite WF.(ES.sb_init). }
    unfold ESBasicStep.sb_delta.
    rewrite ES.cont_sb_dom_Einit; eauto.
    basic_solver. }
  { rewrite ESBasicStep.basic_step_acts_init_set; eauto.
    cdes BSTEP. cdes BSTEP_.
    rewrite SB'. rewrite seq_union_l.
    rewrite WF.(ES.sb_ninit).
    split; [|basic_solver].
    arewrite (Einit S ⊆₁ E S).
    { unfold ES.acts_init_set. basic_solver. }
    rewrite ESBasicStep.basic_step_sb_deltaE; eauto.
    basic_solver. }
  { cdes BSTEP. cdes BSTEP_.
    rewrite SB'. rewrite seq_union_r.
    unionL.
    { rewrite (dom_l WF.(ES.sbE)), <- seqA.
      rewrite <- id_inter.
      arewrite (Eninit S' ∩₁ E S ⊆₁ Eninit S).
      { unfold ES.acts_ninit_set.
        erewrite ESBasicStep.basic_step_acts_init_set with (S:=S); eauto.
        basic_solver. }
      rewrite <- inclusion_restr with (r:=ES.same_tid S')
                                      (dom:=S.(ES.acts_set)).
      arewrite (⦗Eninit S⦘ ⨾ sb S ⊆ restr_rel (E S) (⦗Eninit S⦘ ⨾ sb S)).
      { rewrite WF.(ES.sbE) at 1. basic_solver. }
      rewrite ESBasicStep.basic_step_same_tid_restr; eauto.
      apply restr_rel_mori; auto.
      apply WF. }
    unfold ESBasicStep.sb_delta.
    arewrite (eq e ⊆₁ fun x => tid S' x = ES.cont_thread S k).
    { unfolder. ins. desf. eapply ESBasicStep.basic_step_tid_e; eauto. }
    arewrite (eq_opt e' ⊆₁ fun x => tid S' x = ES.cont_thread S k).
    { unfolder. ins. desf. eapply ESBasicStep.basic_step_tid_e'; eauto. }
    rewrite cross_union_r.
    rewrite !seq_union_r, !seq_eqv_cross_l.
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
    { rewrite ESBasicStep.basic_step_acts_ninit_set; eauto.
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
    eapply ESBasicStep.basic_step_tid_eq_dom; eauto. }
  { eapply ESBasicStep.basic_step_sb_irr; eauto. }
  { eapply ESBasicStep.basic_step_sb_trans; eauto. }
  { eapply ESBasicStep.basic_step_sb_prcl; eauto. }
  { ins. erewrite ESBasicStep.basic_step_acts_init_set; eauto.
    eapply ESBasicStep.basic_step_acts_set in EE; eauto.
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
    { arewrite (⦗eq e0⦘ ⊆ ⦗E S⦘ ;; ⦗eq e0⦘).
      { generalize EE. basic_solver. }
      arewrite (sb S' ⨾ ⦗E S⦘ ⊆ sb S).
      { eapply ESBasicStep.basic_step_sbE; eauto. }
      eapply is_total_mori.
      3: by apply WF; eauto.
      { done. }
      rewrite SB'. basic_solver. }
    { rewrite SB' at 1. rewrite seq_union_l.
      arewrite (sb S ⨾ ⦗eq (ES.next_act S)⦘ ⊆ ∅₂).
      { rewrite (dom_r WF.(ES.sbE)), !seqA.
        unfolder. ins. desf.
        match goal with
        | H : (E ?S) ?X |- _ => red in H
        end. omega. }
      unfold ESBasicStep.sb_delta.
      rewrite seq_union_l.
      rewrite !seq_eqv_cross_r.
      arewrite (eq (ES.next_act S) ∩₁ eq_opt e' ⊆₁ ∅).
      { unfolder. ins. desf. simpls. omega. }
      relsf.
      2: { intros HH. eapply HH. eauto. }
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
    unfold ESBasicStep.sb_delta.
    rewrite seq_union_l.
    rewrite !seq_eqv_cross_r.
    assert (eq e0 ∩₁ eq (ES.next_act S) ⊆₁ ∅) as DD.
    { red in EE. desf. unfolder. ins. desf. simpls. omega. }
    rewrite !DD.
    relsf.
    2: { intros HH. eapply HH. split; eauto. }
    rewrite SB'.
    red. ins.
    destruct IWa as [IWa|IWa];
      destruct IWb as [IWb|IWb].
    { assert (sb S a b \/ sb S b a) as RR.
      { apply CC; auto. }
      generalize RR. basic_solver. }
    3: by inv IWa; inv IWb.
    all: unfold ESBasicStep.sb_delta.
    all: generalize IWa IWb; basic_solver 10. }
  { rewrite ESBasicStep.basic_step_acts_set; eauto.
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
        eapply ESBasicStep.basic_step_seqn_eq_dom; eauto. }
      split.
      { cdes BSTEP. cdes BSTEP_.
        destruct SB as [|SB]; desf; [by left|right].
        apply SB'. by left. }
      red.
      repeat
        (erewrite ESBasicStep.basic_step_tid_eq_dom with (S':=S'); eauto). }

    assert
      (exists x,
          (⦗fun x : eventid => ES.seqn S' x = 0⦘ ⨾
           (sb S')^? ∩ ES.same_tid S') x e) as [x EE].
    { cdes BSTEP. destruct k.
      { exists e. apply seq_eqv_l. split.
        2: { split; [left|red]; done. }
        eapply ESBasicStep.basic_step_seqn_kinit; eauto. }
      assert (E S eid) as EEID.
      { cdes BSTEP_. eapply WF.(ES.K_inEninit); eauto. }
      set (EE:=EEID).
      apply AA in EE. red in EE. desf.
      exists x. destruct_seq_l EE as XX.
      apply seq_eqv_l. split; auto.
      split.
      { right. eapply rewrite_trans_seq_cr_l.
        { eapply ESBasicStep.basic_step_sb_trans; eauto. }
        eexists. split.
        { apply EE. }
        cdes BSTEP_.
        apply SB'. right.
        red. left. red. split; auto.
        red. red. 
        eexists. apply seq_eqv_r. split; eauto. }
      red. destruct EE as [_ EE]. rewrite EE.
      erewrite ESBasicStep.basic_step_tid_e with (e:=e); eauto.
      arewrite (tid S' eid = tid S eid).
      { eapply ESBasicStep.basic_step_tid_eq_dom; eauto. }
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
      { eapply ESBasicStep.basic_step_sb_trans; eauto. }
      eexists. split.
      { apply EE. }
      apply SB'. unfold ESBasicStep.sb_delta. basic_solver 10. }
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
      rewrite set_interC, <- ESstep.basic_step_r_eq_r; eauto.
      rewrite <- ESstep.basic_step_w_eq_w; eauto.
      basic_solver. }
    unfold ESBasicStep.rmw_delta.
    intros x y [AA BB]. red in BB. desf.
    red in TT. desf; cdes TT; desf; auto.
    cdes ACO. cdes AJF.
    red. eauto. }
  { cdes BSTEP. cdes BSTEP_.
    rewrite RMW'. unionL.
    { rewrite WF.(ES.rmwE). unfolder. ins. desf.
      eapply ESBasicStep.basic_step_same_loc_restr; eauto.
      red. splits; auto. by apply WF.(ES.rmwl). }
    unfold ESBasicStep.rmw_delta.
    intros x y [AA BB]. red in BB. desf.
    red in TT. desf; cdes TT; desf; auto.
    admit. }
  { cdes BSTEP. cdes BSTEP_.
    rewrite SB'. rewrite RMW'.
    rewrite WF.(ES.rmwE). unfold ESBasicStep.rmw_delta.
    rewrite WF.(ES.sbE).
    arewrite (ESBasicStep.sb_delta S k e e' ≡
              <| E S ∪₁ eq e |> ;; ESBasicStep.sb_delta S k e e' ;; <| set_compl (E S) |>).
    { split; [|basic_solver].
      arewrite (ESBasicStep.sb_delta S k e e' ⊆
                ESBasicStep.sb_delta S k e e' ;; <| E S ∪₁ set_compl (E S) |>).
      { rewrite set_compl_union_id. basic_solver. }
      rewrite id_union, seq_union_r.
      rewrite ESBasicStep.basic_step_sb_deltaE; eauto.
      rewrite union_false_l.
      hahn_frame.
      apply dom_rel_helper_in.
      eapply ESBasicStep.basic_step_sb_delta_dom; eauto. }
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
      { by right. }
        by red. }
    ins.
    destruct R1 as [R1|R1]; destruct_seq R1 as [A1 B1];
      destruct R2 as [R2|R2]; destruct_seq R2 as [A2 B2]; desf.
    { red in B2. omega. }
    { red in A1. omega. }
    destruct A2 as [A2|A2]; desf.
    red in R1. destruct R1 as [R1|R1]; red in R1; simpls; desf.
    2: omega.
    eapply ES.cont_sb_domE in R1; eauto. }
  { split; [|basic_solver].
    red in TT. desf; cdes TT; desf.
    2,4: cdes AJF.
    all: rewrite JF'; unionL.
    1,2,4,6: rewrite WF.(ES.jfE) at 1; sin_rewrite !EES; basic_solver.
    all: unfold ESstep.jf_delta; apply EES in wE; generalize wE rE'; basic_solver. }
  { split; [|basic_solver].
    assert (jf S ⊆ ⦗W S'⦘ ⨾ jf S ⨾ ⦗R S'⦘) as AA.
    { rewrite WF.(ES.jfD) at 1.
      rewrite WF.(ES.jfE) at 2.
      rewrite !seqA.
      rewrite <- id_inter, <- !seqA, <- id_inter.
      rewrite set_interC with (s:=W S').
      rewrite ESstep.basic_step_w_eq_w; eauto.
      rewrite ESstep.basic_step_r_eq_r; eauto.
      rewrite WF.(ES.jfE) at 1.
      basic_solver 10. }
    red in TT. desf; cdes TT; desf.
    2,4: cdes AJF.
    all: rewrite JF'; unionL; auto.
    1,3: rewrite AA at 1; basic_solver.
    all: assert (W S' w) as WW
        by (eapply ESstep.basic_step_w_eq_w; eauto; by split);
      generalize WW rR'; unfold ESstep.jf_delta;
        basic_solver. }
  { assert (jf S ⊆ same_loc S') as AA.
    { rewrite WF.(ES.jfE). intros x y HH.
      destruct_seq HH as [EX EY].
      eapply ESBasicStep.basic_step_same_loc_restr; eauto.
      red. split; auto. by apply WF.(ES.jfl). }
    red in TT. desf; cdes TT; desf.
    2,4: cdes AJF.
    all: rewrite JF'; unionL; auto.
    all: unfold ESstep.jf_delta; unfolder; intros x y HH; desf. }
  { assert (funeq (val (lab S')) (jf S)) as AA.
    { rewrite WF.(ES.jfE). intros x y HH.
      destruct_seq HH as [EX EY].
      eapply ESBasicStep.basic_step_same_val_restr; eauto.
      red. split; auto. by apply WF.(ES.jfv). }
    red in TT. desf; cdes TT; desf.
    2,4: cdes AJF.
    all: rewrite JF'; try apply funeq_union; auto.
    all: unfold ESstep.jf_delta; unfolder; intros x y HH; desf. }
  { assert (functional (jf S)⁻¹) as AA by apply WF.
    red in TT. desf; cdes TT; desf.
    2,4: cdes AJF.
    all: rewrite JF'; try rewrite transp_union; auto.
    all: apply functional_union; auto.
    1,3: by unfold ESstep.jf_delta, singl_rel, transp; red; ins; desf. 
    all: unfold ESstep.jf_delta; unfolder.
    all: intros x [y JF] HH; desf.
    all: apply (dom_r WF.(ES.jfE)) in JF; destruct_seq_r JF as EE.
    all: eapply ESBasicStep.basic_step_acts_set_ne; eauto. }
  { assert (jf S ⊆ jf S') as BB.
    { cdes BSTEP. cdes BSTEP_.
      red in TT. desf; cdes TT; desf.
      2,4: cdes AJF.
      all: rewrite JF'; basic_solver. }
    assert (E S ∩₁ R S' ⊆₁ codom_rel (jf S')) as AA.
    { rewrite <- BB.
      rewrite ESstep.basic_step_r_eq_r; eauto.
      apply WF. }
    rewrite ESBasicStep.basic_step_acts_set; eauto.
    rewrite !set_inter_union_l.
    rewrite set_unionA.
    apply set_subset_union_l. split; auto.
    cdes BSTEP. cdes BSTEP_.
    red in TT. desf; cdes TT; desf.
    3: cdes AEW.
    1,3: type_solver.
    all: cdes AJF; rewrite JF'.
    all: rewrite codom_union; unionR right.
    all: unfold eq_opt, ESstep.jf_delta.
    { basic_solver. }
    unfolder. ins. desf; eauto.
    cdes ACO. type_solver. }

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
  1-2 : admit.

  { red in TT. desf; cdes TT; desf.
    { eapply step_same_co_connex_helper; eauto.
      admit. }
    { eapply step_same_co_connex_helper; eauto.
      eapply ESstep.load_step_w; eauto. }
    { eapply step_add_co_connex; eauto.
      { basic_solver. }
      admit. }
    eapply step_add_co_connex; eauto.
    { basic_solver. }
    admit. }

  1-9: admit.

  { red. ins. desf.
    red in KK. unfold ES.cont_thread in CTK.
    cdes BSTEP. cdes BSTEP_.
    rewrite CONT' in KK.
    inv KK.
    2: { apply WF.(ES.init_tid_K).
         do 2 eexists. splits; eauto.
         unfold ES.cont_thread; desf.
         rewrite <- CTK. symmetry.
         eapply ESBasicStep.basic_step_tid_eq_dom; eauto.
         eapply ES.K_inEninit; eauto. }
    simpls.
    unfold opt_ext in CTK. rewrite TID' in CTK.
    unfold upd_opt in CTK. desf.
    all: rewrite upds in *.
    all: eapply WF.(ES.init_tid_K); eauto. }
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
    1,3: eapply ESBasicStep.basic_step_acts_set_ne'; eauto;
      eapply ES.K_inEninit; eauto.
    all: eapply ESBasicStep.basic_step_acts_set_ne; eauto;
      eapply ES.K_inEninit; eauto. }
  { ins. destruct EE as [AA BB].
    eapply ESBasicStep.basic_step_acts_set in AA; eauto.
    assert (~ (Einit S) e0) as CC.
    { intros HH. apply BB.
      eapply ESBasicStep.basic_step_acts_init_set; eauto. }
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
  ins. cdes BSTEP. cdes BSTEP_. desf.
  red in inK. rewrite CONT' in inK.
  inv inK.
  2: { eapply ESBasicStep.basic_step_acts_ninit_set; eauto.
       repeat left. eapply WF.(ES.K_inEninit); eauto. }
  eapply ESBasicStep.basic_step_acts_ninit_set; eauto.
  unfold opt_ext. basic_solver.
Admitted.
 
End ESstepWf.