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

Lemma step_wf S S'
      (STEP : ESstep.t Weakestmo S S')
      (WF : ES.Wf S) :
  ES.Wf S'.
Proof.
  cdes STEP.
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
    red. rewrite LAB'. unfold is_r, is_w.
    simpls. subst. destruct lbl' as [lbl'|]; [|by desf].
    rewrite upds. rewrite updo.
    2: omega.
    rewrite upds.
    red in STEP0. simpls.
    
    (* TODO: We need something about language transitions. *)
    admit. }
  { admit. }
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
  { rewrite ESBasicStep.basic_step_acts_set; eauto.
    rewrite !set_inter_union_l.
    rewrite ESstep.basic_step_r_eq_r; eauto.
    cdes BSTEP. cdes BSTEP_.
    red in TT. desf; cdes TT; desf.
    2,4: cdes AJF.
    all: rewrite JF'; try rewrite codom_union; auto.

Admitted.
 
End ESstepWf.