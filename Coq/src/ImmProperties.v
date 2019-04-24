From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import AuxRel
     Events Execution Execution_eco imm_s_hb imm_s imm_common
     Prog ProgToExecution ProgToExecutionProperties
     CombRelations CombRelationsMore
     TraversalConfig Traversal TraversalConfigAlt SimTraversal SimTraversalProperties
     CertExecution2.
Require Import AuxRel.
Require Import AuxDef.

Set Implicit Arguments.

Lemma same_label_u2v_val {A} (lab lab' : A -> label) x
      (U2V : same_label_u2v (lab x) (lab' x))
      (VAL : val lab x = val lab' x) :
  lab x = lab' x.
Proof. unfold same_label_u2v, val in *. desf; desf. Qed.

Section Properties.

Variable G : execution.

Notation "'E'" := G.(acts_set).

Notation "'Tid' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid' t" := (fun x => tid x <> t) (at level 1).

Lemma is_init_tid : 
  is_init ⊆₁ Tid tid_init. 
Proof. unfolder. unfold is_init. ins. desf. Qed.

Lemma tid_initi prog 
      (GPROG : program_execution prog G)
      (PROG_NINIT : ~ (IdentMap.In tid_init prog)) : 
  E ∩₁ Tid tid_init ⊆₁ is_init.
Proof. 
  red. unfolder. 
  intros e [EE TIDe].
  unfold tid, is_init in *.
  destruct e eqn:Heq; auto.
  destruct GPROG as [HH _].
  rewrite <- Heq in EE.
  specialize (HH e EE).
  desf. 
Qed.

Variable WF : Wf G.
Variable sc : relation actid.
Variable CON : imm_consistent G sc.

Variable TC : trav_config.
Variable TCCOH : tc_coherent G sc TC.

Notation "'C'" := (covered TC).
Notation "'I'" := (issued TC).

Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).

Notation "'fr'" := G.(fr).
Notation "'coe'" := G.(coe).
Notation "'coi'" := G.(coi).
Notation "'deps'" := G.(deps).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).
Notation "'detour'" := G.(detour).
Notation "'hb'" := G.(hb).
Notation "'sw'" := G.(sw).
Notation "'release'" := G.(release).

Notation "'lab'" := G.(lab).
(* Notation "'loc'" := (loc lab). *)
(* Notation "'val'" := (val lab). *)
(* Notation "'mod'" := (mod lab). *)
(* Notation "'same_loc'" := (same_loc lab). *)

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'Loc_' l" := (fun x => loc lab x = Some l) (at level 1).
Notation "'W_ex'" := G.(W_ex).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Lemma rfi_D_in_D thread (NINIT : thread <> tid_init):
  dom_rel (rfi ⨾ ⦗ D G TC thread ⦘) ⊆₁ D G TC thread.
Proof.
  intros w [r RFI]. destruct_seq_r RFI as DR.
  apply wf_rfiD in RFI; auto. destruct_seq RFI as [WW RR].
  apply wf_rfiE in RFI; auto. destruct_seq RFI as [EW ER].
  red in DR. unfold set_union in DR. desf.
  { apply C_in_D. eapply dom_sb_covered; eauto.
    eexists. apply seq_eqv_r. split; eauto. apply RFI. }
  { eapply issuedW in DR; eauto. type_solver. }
  { red. do 3 left. right. split; auto.
    edestruct sb_tid_init as [AA|AA]; auto.
    { apply RFI. }
    { rewrite AA. apply DR. }
    destruct w; simpls. intros BB; desf. }
  { red. do 2 left. right.
    destruct DR as [z [v [[EE|EE] DR]]].
    { desf. generalize RFI DR. basic_solver 10. }
    apply wf_rfiD in EE; auto. destruct_seq EE as [WR RV].
    clear -RR WR. type_solver. }
  { apply I_in_D. destruct DR as [v DR].
    destruct_seq_l DR as IV.
    assert (v = w); desf.
    eapply wf_rff; eauto.
    { apply DR. }
    apply RFI. }
  destruct DR as [v DR].
  destruct_seq_r DR as IV.
  assert (v = w); desf.
  { eapply wf_rff; eauto.
    { apply DR. }
    apply RFI. }
  unfold Execution.rfi, Execution.rfe in *.
  generalize RFI DR. basic_solver.
Qed.

Lemma rfe_E0D_in_D thread (NINIT : thread <> tid_init):
  dom_rel (rfe ⨾ ⦗ Tid_ thread ∩₁ (C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘))
               ∩₁ D G TC thread ⦘) ⊆₁
          D G TC thread.
Proof.
  intros w [r RFE]. destruct_seq_r RFE as DR.
  apply wf_rfeD in RFE; auto. destruct_seq RFE as [WW RR].
  apply wf_rfeE in RFE; auto. destruct_seq RFE as [EW ER].
  destruct DR as [[TR EE0] DR].
  assert (C r -> D G TC thread w) as UU.
  { intros HH. apply I_in_D. eapply dom_rf_covered; eauto.
    eexists. apply seq_eqv_r. split; eauto. apply RFE. }
  destruct EE0 as [EE0|EE0].
  { intuition. }

  red in DR. unfold set_union in DR. desf.
  { intuition. }
  { eapply issuedW in DR; eauto. type_solver. }
  { exfalso. by apply DR. }
  { red. apply I_in_D.
    destruct DR as [z [v [[EE|EE] DR]]].
    2: { apply wf_rfiD in EE; auto. destruct_seq EE as [WR RV].
         clear -RR WR. type_solver. }
    desf. eapply dom_rfe_ppo_issued; eauto.
    do 2 eexists. eauto. }
  { exfalso. destruct DR as [v DR].
    destruct_seq_l DR as IV.
    assert (v = w); desf.
    eapply wf_rff; eauto.
    { apply DR. }
    { apply RFE. }
    apply RFE. apply DR. }
  destruct EE0 as [t EE0]. destruct_seq_r EE0 as IT.
  destruct EE0 as [|EE0]; subst.
  { eapply issuedW in IT; eauto. type_solver. }
  apply I_in_D.
  eapply dom_rfe_acq_sb_issued; eauto.
  destruct DR as [v DR].
  destruct_seq_r DR as IV.
  assert (v = w); desf.
  { eapply wf_rff; eauto.
    { apply DR. }
    apply RFE. }
  generalize DR IV IT EE0. basic_solver 10.
Qed.

Lemma rf_E0D_in_D thread (NINIT : thread <> tid_init):
  dom_rel (rf ⨾ ⦗ Tid_ thread ∩₁ (C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘))
               ∩₁ D G TC thread ⦘) ⊆₁
          D G TC thread.
Proof.
  intros w [r RF]. destruct_seq_r RF as DR.
  apply rfi_union_rfe in RF. destruct RF as [RF|RF].
  { apply rfi_D_in_D; auto. eexists.
    apply seq_eqv_r; split; eauto. apply DR. }
  apply rfe_E0D_in_D; auto. eexists.
  apply seq_eqv_r; split; eauto.
Qed.

Lemma itrav_step_thread_ninit prog e TC'
      (GPROG : program_execution prog G)
      (PROG_NINIT : ~ (IdentMap.In tid_init prog))
      (STEP : itrav_step G sc e TC TC') :
  tid e <> tid_init.
Proof.
  intros AA.
  assert (E e) as EE.
  { cdes STEP. desf.
    { apply COV. }
    apply ISS. }
  assert (is_init e) as INIT.
  { eapply tid_initi; eauto. by split. }
  cdes STEP. desf.
  { apply NEXT. eapply init_covered; eauto. by split. }
  apply NISS. eapply init_issued; eauto. by split.
Qed.

Lemma isim_trav_step_thread_ninit prog thread TC'
      (GPROG : program_execution prog G)
      (PROG_NINIT : ~ (IdentMap.In tid_init prog))
      (STEP : isim_trav_step G sc thread TC TC') :
  thread <> tid_init.
Proof.
  apply sim_trav_step_to_step in STEP. desf.
  eapply itrav_step_thread_ninit; eauto.
Qed.

Lemma isim_trav_step_new_e_tid_alt thread TC' 
      (ITV : isim_trav_step G sc thread TC TC') : 
  covered TC' ∪₁ issued TC' ≡₁ 
    (covered TC ∪₁ issued TC) ∩₁ NTid thread ∪₁ (covered TC' ∪₁ issued TC') ∩₁ Tid thread.
Proof. 
  rewrite isim_trav_step_new_e_tid at 1; 
    eauto; split; [|basic_solver].
    rewrite set_subset_union_l. splits.
  { rewrite <- set_inter_full_r 
      with (s := C ∪₁ I) at 1.
    rewrite <- tid_set_dec 
      with (thread := thread).
    rewrite set_unionC 
      with (s := Tid thread) (s' := NTid thread).
    rewrite set_inter_union_r.
    apply set_union_Proper; auto.
    rewrite sim_trav_step_covered_le,
            sim_trav_step_issued_le
              at 1.
    2,3 : eexists; eauto.
    done. }
  basic_solver.
Qed.

Variable RELCOV : W ∩₁ Rel ∩₁ I ⊆₁ C.

Lemma release_rf_rmw_step : release ⨾ rf ⨾ rmw ⊆ release.
Proof.
  unfold imm_s_hb.release at 1. unfold rs.
  rewrite !seqA.
  arewrite (rf ⨾ rmw ⊆ (rf ⨾ rmw)＊) at 2.
    by rewrite rt_rt.
Qed.

Lemma release_rf_rmw_steps : release ⨾ (rf ⨾ rmw)＊ ⊆ release.
Proof.
  unfold imm_s_hb.release at 1. unfold rs.
  rewrite !seqA.
    by rewrite rt_rt.
Qed.

Lemma sw_in_Csw_sb : sw ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗ I ⦘)⦘ ⊆ ⦗ C ⦘ ⨾ sw ∪ sb.
Proof.
  rewrite !id_union. rewrite seq_union_r. 
  unionL.
  { rewrite sw_covered; eauto. basic_solver. }
  arewrite (sw ⊆ ⦗ C ∪₁ set_compl C ⦘ ⨾ sw) at 1.
  { rewrite set_compl_union_id. by rewrite seq_id_l. }
  rewrite id_union. relsf.
  apply union_mori; [basic_solver|].
  unfold imm_s_hb.sw.
  arewrite ((sb ⨾ ⦗F⦘)^? ⊆ sb ⨾ ⦗F⦘ ∪ ⦗ fun _ => True ⦘) by basic_solver.
  rewrite !seq_union_l, !seq_union_r.
  unionL.
  { rewrite !seqA.
    seq_rewrite <- !id_inter. rewrite <- !set_interA.
    arewrite (sb ⨾ ⦗F ∩₁ Acq ∩₁ dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆
              ⦗ C ⦘ ⨾ sb ⨾ ⦗F ∩₁ Acq ∩₁ dom_rel (sb^? ⨾ ⦗I⦘)⦘).
    { unfolder. ins. desf; splits; auto.
      2,4: by do 2 eexists; splits; eauto.
      2: eapply TCCOH.(dom_sb_covered).
      2: eexists; apply seq_eqv_r; split; eauto.
      all: match goal with H : I _ |- _ => apply TCCOH in H; apply H end.
      all: eexists; apply seq_eqv_r; split; eauto.
      { apply sb_to_f_in_fwbob. apply seq_eqv_r. split; [|split]; auto.
        mode_solver. }
      apply sb_from_f_in_fwbob. apply seq_eqv_l. split; [split|]; auto.
      mode_solver. }
    sin_rewrite release_rf_covered; eauto.
    basic_solver. }
  rewrite seq_id_l.
  arewrite (rf ⊆ ⦗ I ∪₁ set_compl I⦘ ⨾ rf).
  { rewrite set_compl_union_id. basic_solver. }
  rewrite id_union. relsf.
  unionL.
  { sin_rewrite release_issued; eauto. basic_solver. }
  rewrite rfi_union_rfe. relsf.
  unionL.
  2: { arewrite (⦗set_compl I⦘ ⨾ rfe ⨾ ⦗Acq⦘ ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆ ∅₂).
       2: basic_solver.
       seq_rewrite <- !id_inter.
       unfolder. ins. desf.
       { match goal with H : I _ |- _ => apply TCCOH.(issuedW) in H end.
         match goal with H : rfe _ _ |- _ =>
                         apply wf_rfeD in H; auto; (destruct_seq H as [XX YY])
         end.
         type_solver. }
       match goal with H : ~ (I _) |- _ => apply H end.
       apply TCCOH.(dom_rfe_acq_sb_issued).
       eexists. eexists. split; eauto.
       apply seq_eqv_l. split; [split|]; auto.
       2: { apply seq_eqv_r. split; eauto. }
       match goal with H : rfe _ _ |- _ =>
                       apply wf_rfeD in H; auto; (destruct_seq H as [XX YY]); auto
       end. }
  unfold imm_s_hb.release, rs.
  arewrite
    (⦗set_compl C⦘ ⨾ (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc lab)^? ⨾ ⦗W⦘ ⨾ (rf ⨾ rmw)＊) ⊆
     ⦗set_compl C⦘ ⨾ (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ ⦗W⦘ ⨾
       (sb ∩ same_loc lab)^? ⨾ ⦗W⦘ ⨾ ⦗ set_compl I ⦘ ⨾ (⦗ set_compl I ⦘ ⨾ rf ⨾ rmw)＊)).
  { intros x y HH.
    destruct_seq_l HH as NC.
    do 4 apply seqA in HH. destruct HH as [v [HH SUF]].
    apply seq_eqv_l. split; auto.
    
    Ltac _ltt :=
      apply seqA;
      apply seqA with (r1 := ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^?);
      apply seqA with (r1 := (⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^?) ⨾ ⦗W⦘);
      apply seqA with (r1 := ((⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^?) ⨾ ⦗W⦘) ⨾ (sb ∩ same_loc lab)^?).
    
    _ltt.
    exists v. split.
    { generalize HH. basic_solver. }
    assert (release x v) as REL.
    { unfold imm_s_hb.release, rs. _ltt.
      eexists. split; eauto. apply rt_refl. }
    apply seq_eqv_l. split.
    { intros II. apply NC. eapply dom_release_issued; eauto.
      eexists. apply seq_eqv_r. split; eauto. }
    assert (codom_rel (⦗ set_compl C ⦘ ⨾ release) v) as XX.
    { exists x. apply seq_eqv_l. split; auto. }
    assert (~ I v) as NI.
    { intros II. apply NC. eapply dom_release_issued; eauto.
      eexists. apply seq_eqv_r. split; eauto. }
    clear x NC HH REL.
    induction SUF.
    2: by apply rt_refl.
    { apply rt_step. apply seq_eqv_l. split; auto. }
    eapply rt_trans.
    { by apply IHSUF1. }
    assert (codom_rel (⦗set_compl C⦘ ⨾ release) y) as YY.
    { destruct XX as [v XX]. destruct_seq_l XX as CC.
      eexists. apply seq_eqv_l. split; eauto.
      apply release_rf_rmw_steps.
      eexists. split; eauto. }
    apply IHSUF2; auto.
    intros II.
    destruct YY as [v YY]. destruct_seq_l YY as CC. apply CC.
    eapply dom_release_issued; eauto.
    eexists. apply seq_eqv_r. split; eauto. }
  arewrite ((⦗set_compl I⦘ ⨾ rf ⨾ rmw)＊ ⨾
             ⦗set_compl I⦘ ⨾ rfi ⨾ ⦗Acq⦘ ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆
            sb^? ⨾ ⦗set_compl I⦘ ⨾ rfi ⨾ ⦗Acq⦘ ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘).
  2: { unfold Execution.rfi.
       generalize (@sb_trans G). basic_solver. }
  intros x y [v [HH XX]].
  eexists. split; [|by eauto].
  assert (dom_rel (sb ⨾ ⦗ I ⦘) v) as VV.
  { generalize XX (@sb_trans G). unfold Execution.rfi. basic_solver 40. }
  clear y XX.
  induction HH as [x y HH| | ].
  2: by apply r_refl.
  { apply r_step.
    destruct_seq_l HH as NIX. destruct HH as [v [RF RMW]].
    apply rfi_union_rfe in RF. destruct RF as [RF|RF].
    { by eapply (@sb_trans G); [apply RF|apply rmw_in_sb]. }
    exfalso. destruct VV as [z VV]. destruct_seq_r VV as AZ.
    set (IZ := AZ).
    apply TCCOH in IZ.
    apply NIX. destruct IZ as [NN _]. apply NN.
    eexists. apply seq_eqv_r. split; eauto.
    eexists. split; [by right; eauto|left].
    red. apply seq_eqv_l. split.
    { apply wf_rfeD in RF; auto. generalize RF. basic_solver. }
    apply seq_eqv_r. split.
    2: by eapply issuedW; eauto.
    apply ct_step. left; right. apply seq_eqv_l. split.
    { apply wf_rmwD in RMW; auto. generalize RMW. basic_solver. }
    eapply (@sb_trans G); eauto. by apply rmw_in_sb. }
  specialize (IHHH2 VV).
  eapply (transitive_cr (@sb_trans G) _ IHHH2); eauto.

  Unshelve.
  apply IHHH1. generalize VV (@sb_trans G) IHHH2. basic_solver 10.
Qed.

Lemma hb_in_Chb_sb : hb ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗ I ⦘)⦘ ⊆ ⦗ C ⦘ ⨾ hb ∪ sb.
Proof.
  unfold imm_s_hb.hb.
  intros x y HH.
  destruct_seq_r HH as DOM.
  apply clos_trans_tn1 in HH.
  induction HH as [y [HH|HH]|y z AA].
  { by right. }
  { assert ((⦗C⦘ ⨾ sw ∪ sb) x y) as [ZZ|ZZ].
    3: by right.
    2: { destruct_seq_l ZZ as CX.
         left. apply seq_eqv_l. split; auto.
         apply ct_step. by right. }
    apply sw_in_Csw_sb. apply seq_eqv_r. splits; auto. }
  assert (sb y z -> (C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)) y) as DOMY.
  { intros SB.
    destruct DOM as [DOM|DOM].
    2: { right. generalize (@sb_trans G) SB DOM. basic_solver 10. }
    left.
    eapply dom_sb_covered; eauto. eexists.
    apply seq_eqv_r. split; eauto. }

  assert ((C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)) y) as BB.
  2: { set (CC:=BB). apply IHHH in CC.
       destruct CC as [CC|CC].
       { left.
         destruct_seq_l CC as XX.
         apply seq_eqv_l. split; auto.
         apply ct_ct. eexists. split; eauto. }
       destruct AA as [AA|AA].
       { right. eapply (@sb_trans G); eauto. }
       assert ((sw ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)⦘) y z) as DD.
       { apply seq_eqv_r. by split. }
       eapply sw_in_Csw_sb in DD.
       destruct DD as [DD|DD].
       2: { right. eapply (@sb_trans G); eauto. }
       left.
       apply seq_eqv_l. split.
       2: { apply ct_ct. eexists.
            split; apply ct_step; [left|right]; eauto. }
       assert (C y) as CY.
       { by destruct_seq_l DD as XX. }
       eapply dom_sb_covered; eauto. eexists.
       apply seq_eqv_r. split; eauto. }
  destruct AA as [|AA]; [by intuition|].
  assert ((sw ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)⦘) y z) as DD.
  { apply seq_eqv_r. by split. }
  eapply sw_in_Csw_sb in DD.
  destruct DD as [DD|]; [|by intuition].
  left. by destruct_seq_l DD as CY.
Qed.

Lemma sc_sb_I_dom_C: dom_rel (sc ⨾ sb ⨾ ⦗I⦘) ⊆₁ C.
Proof.
  cdes CON.
  rewrite (dom_r Wf_sc.(wf_scD)).
  unfolder. ins. desf.
  cdes TCCOH.
  assert (C z) as AA.
  2: { apply CC in AA. red in AA.
       unfolder in AA. desf.
       1,2: type_solver.
       eapply AA2. eexists.
       apply seq_eqv_r. split; eauto. }
  eapply II; eauto.
  eexists. apply seq_eqv_r. split; eauto.
  apply sb_from_f_in_fwbob.
  apply seq_eqv_l. split; [split|]; auto.
  mode_solver.
Qed.

Lemma scCsbI_C : sc ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆ ⦗C⦘ ⨾ sc.
Proof.
  rewrite id_union. rewrite seq_union_r. unionL.
  { eapply sc_covered; eauto. }
  unfolder. ins. desf.
  all: eapply wf_scD in H; [|by apply CON].
  all: destruct_seq H as [XX YY].
  { eapply issuedW in H2; eauto.
    type_solver. }
  split; auto.
  assert (C y) as CY.
  2: { eapply dom_sc_covered; eauto. eexists. apply seq_eqv_r.
       split; eauto. }
  eapply tc_fwbob_I.
  { apply tc_coherent_implies_tc_coherent_alt; eauto. apply CON. }
  eexists. apply seq_eqv_r. split; eauto.
  eapply sb_from_f_in_fwbob. apply seq_eqv_l.
  split; auto.
  mode_solver.
Qed.

Lemma sbCsbI_CsbI : sb ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⨾ sb.
Proof.
  rewrite id_union, !seq_union_r, !seq_union_l.
  apply union_mori.
  { rewrite sb_covered; eauto. basic_solver. }
  generalize (@sb_trans G). basic_solver 10.
Qed.

Lemma initninit_in_ext_sb : is_init × (set_compl is_init) ⊆ ext_sb.
Proof. unfold ext_sb. basic_solver. Qed.

End Properties.