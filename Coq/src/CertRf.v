From hahn Require Import Hahn.
From imm Require Import Events Execution TraversalConfig TraversalConfigAlt
     imm_common imm_s imm_s_hb CertExecution1 CertExecution2 AuxRel
     CombRelations Execution_eco.
Require Import AuxRel.
Require Import AuxDef.
Require Import ImmProperties.

Section CertRf.
Variable G  : execution.
Variable sc : relation actid.
Variable TC : trav_config.
Variable thread : thread_id.

Notation "'C'"  := (covered TC).
Notation "'I'"  := (issued TC).

Notation "'E'"  := G.(acts_set).
Notation "'lab'" := (G.(lab)).
Notation "'rmw'" := G.(rmw).

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Notation "'D'" := (Tid_ thread ∩₁ D G TC thread).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).

Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).

Notation "'sb'" := (G.(sb)).
Notation "'sw'" := (G.(imm_s_hb.sw)).
Notation "'hb'" := (G.(imm_s_hb.hb)).
Notation "'rf'" := (G.(rf)).
Notation "'rfi'" := (G.(rfi)).
Notation "'co'" := (G.(co)).
Notation "'loc'" := (loc lab).

Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).
Notation "'R_' l" := (R ∩₁ Loc_ l) (at level 1).

Notation "'furr'" := (furr G sc).

Definition E0 := (Tid_ thread ∩₁ (C ∪₁ dom_rel (sb^? ⨾ ⦗ I ⦘))).

Definition vf := ⦗ W ⦘ ⨾ (rf ⨾ ⦗ C ⦘)^? ⨾ hb^? ⨾
                    sc^? ⨾ hb^? ⨾ ⦗ E ⦘ ∪
                 rf ⨾ ⦗ D ⦘ ⨾ sb^?.

Definition cert_rf :=
  vf ∩ same_loc lab ⨾ ⦗ E0 ∩₁ R ⦘ \ co ⨾ vf.
Definition cert_rfi := ⦗  Tid_ thread ⦘ ⨾ cert_rf ⨾ ⦗ Tid_ thread ⦘.
Definition cert_rfe := ⦗ NTid_ thread ⦘ ⨾ cert_rf ⨾ ⦗ Tid_ thread ⦘.

Section Properties.
Variable WF  : Wf G.
Variable COH : imm_consistent G sc.
Variable TCCOH : tc_coherent G sc TC.
Variable RELCOH : W ∩₁ Rel ∩₁ I ⊆₁ C.

Lemma E0_in_E : E0 ⊆₁ E.
Proof.
  unfold E0.
  rewrite coveredE, issuedE; try edone.
  rewrite (dom_l (@wf_sbE G)).
  basic_solver.
Qed.

Lemma vfE : vf ≡ ⦗ E ⦘ ⨾ vf ⨾ ⦗ E ⦘.
Proof.
  apply dom_helper_3.
  unfold vf.
  rewrite WF.(wf_rfE).
  rewrite (dom_l WF.(wf_hbE)).
  cdes COH.
  rewrite (dom_l (wf_scE Wf_sc)).
  rewrite (dom_r (@wf_sbE G)).
  basic_solver.
Qed.

Lemma vf_dom : vf ≡ ⦗ W ⦘ ⨾ vf.
Proof.
  split; [|basic_solver].
  unfold vf.
  rewrite (dom_l WF.(wf_rfD)) at 2.
  rewrite !seqA. rewrite seq_union_r.
    by seq_rewrite seq_eqvK.
Qed.

Lemma vf_in_furr : vf ⊆ furr.
Proof.
  cdes COH.
  unfold vf.
  arewrite_id ⦗D⦘. arewrite_id ⦗E⦘. arewrite_id ⦗C⦘.
  rewrite !seq_id_r, !seq_id_l.
  rewrite furr_alt; auto.
  unionL; [done|].
  rewrite (dom_l WF.(wf_rfD)) at 1.
  rewrite sb_in_hb.
  basic_solver 20.
Qed.

Lemma sb_in_vf : ⦗ W ⦘ ⨾ sb ⊆ vf.
Proof. 
  unfold vf.
  rewrite wf_sbE.
  rewrite sb_in_hb at 1.
  basic_solver 20.
Qed.

Lemma vf_sb_in_vf : vf ⨾ sb ⊆ vf.
Proof. 
  unfold vf.
  rewrite seq_union_l, !seqA.
  apply union_mori.
  { do 4 (apply seq_mori; [done|]).
    rewrite wf_sbE.
    rewrite sb_in_hb.
    generalize hb_trans.
    basic_solver. }
  do 2 (apply seq_mori; [done|]).
  generalize sb_trans.
  basic_solver.
Qed.

Lemma cert_rf_in_vf : cert_rf ⊆ vf.
Proof. unfold cert_rf. basic_solver. Qed.

Lemma cert_rfE : cert_rf ≡ ⦗E⦘ ⨾ cert_rf ⨾ ⦗E⦘.
Proof.
  cdes COH.
  apply dom_helper_3.
  rewrite cert_rf_in_vf.
  apply dom_helper_3.
  apply vfE.
Qed.

Lemma cert_rf_codomE0 : cert_rf ≡ cert_rf ⨾ ⦗E0⦘.
Proof. unfold cert_rf. basic_solver. Qed.

Lemma cert_rf_codomt : cert_rf ≡ cert_rf ⨾ ⦗Tid_ thread⦘.
Proof.
  split; [|basic_solver].
  rewrite cert_rf_codomE0 at 1.
  unfold E0. basic_solver.
Qed.

Lemma cert_rfD : cert_rf ≡ ⦗W⦘ ⨾ cert_rf ⨾ ⦗R⦘.
Proof.
  apply dom_helper_3.
  unfold cert_rf.
  rewrite inclusion_minus_rel.
  rewrite inter_inclusion.
  rewrite vf_dom.
  basic_solver.
Qed.

Lemma cert_rfl : cert_rf ⊆ same_loc lab.
Proof. unfold cert_rf. basic_solver. Qed.

Lemma cert_rff : functional cert_rf⁻¹.
Proof.
  rewrite cert_rfD, cert_rfE.
  red. intros x y z AA BB.
  assert (exists l, loc y = Some l) as HH.
  { generalize (is_w_loc lab). unfolder in *.
    basic_solver 12. }
  desc.

  assert (loc z = Some l) as GG.
  { hahn_rewrite cert_rfl in AA.
    hahn_rewrite cert_rfl in BB.
    unfold same_loc in *.
    unfolder in *.
    desf. congruence. }

  unfolder in *.
  destruct (classic (y=z)) as [|X]; eauto; desf.
  exfalso.
  eapply wf_co_total in X; try basic_solver 22.
  2: { unfolder. splits; eauto. congruence. }
  unfold cert_rf in *. desf; unfolder in *; basic_solver 40.
Qed.

Lemma cert_rf_complete : forall b (IN: (E0 ∩₁ R) b), exists a, cert_rf a b.
Proof.
  ins; unfolder in *; desc.
  assert (exists l, loc b = Some l); desc.
  { by generalize (is_r_loc lab); unfolder in *; basic_solver 12. }

  assert (E b) as UU.
  { by apply E0_in_E. }

  assert (E (InitEvent l)).
  { by apply WF; eauto. }
  assert (lab (InitEvent l) = Astore Xpln Opln l 0).
  { by apply WF. }
  assert (loc (InitEvent l) = Some l).
  { by unfold Events.loc; rewrite (wf_init_lab WF). }
  assert (W_ l (InitEvent l)).
  { by unfolder; unfold is_w, Events.loc; desf; eauto. }
  assert (sb (InitEvent l) b).
  { by apply init_ninit_sb; eauto; eapply read_or_fence_is_not_init; eauto. }
  assert (vf (InitEvent l) b).
  { left. red.
    exists (InitEvent l); splits.
    { red. splits; desf; by apply WF.(init_w). }
    unfold eqv_rel; eauto.
    hahn_rewrite <- sb_in_hb.
    basic_solver 21. }

  forward (eapply last_exists with (s:=co ⨾ ⦗fun x => vf x b⦘) 
                                   (dom:= filterP (W_ l) G.(acts)) (a:=(InitEvent l))).
  { eapply acyclic_mon.
    apply trans_irr_acyclic; [apply co_irr| apply co_trans]; eauto.
    basic_solver. }
  { ins.
    assert (A: (co ⨾ ⦗fun x : actid => vf x b⦘)^? (InitEvent l) c).
    { apply rt_of_trans; try done.
      apply transitiveI.
      arewrite_id ⦗fun x : actid => vf x b⦘ at 1.
      rewrite seq_id_l.
      arewrite (co ⨾ co ⊆ co); [|done].
      apply transitiveI.
      eapply co_trans; eauto. }
    unfolder in A; desf.
    { by apply in_filterP_iff; split; auto. }
    apply in_filterP_iff.
    hahn_rewrite WF.(wf_coE) in A.
    hahn_rewrite WF.(wf_coD) in A.
    hahn_rewrite WF.(wf_col) in A.
    unfold same_loc in *; unfolder in *; desf; splits; eauto; congruence. }
  ins; desc.
  assert (A: (co ⨾ ⦗fun x : actid => vf x b⦘)^? (InitEvent l) b0).
  { apply rt_of_trans; [|by subst].
    apply transitiveI.
    arewrite_id ⦗fun x : actid => vf x b⦘ at 1.
    rewrite seq_id_l.
    arewrite (co ⨾ co ⊆ co); [|done].
    apply transitiveI.
    eapply co_trans; eauto. }
  assert (loc b0 = Some l).
  { unfolder in A; desf.
    hahn_rewrite WF.(wf_col) in A.
    unfold same_loc in *; desf; unfolder in *; congruence. }
  exists b0; red; split.
  { unfold urr, same_loc.
    unfolder in A; desf; unfolder; ins; desf; splits; try basic_solver 21; congruence. }
  unfold max_elt in *.
  unfolder in *; ins; desf; intro; desf; basic_solver 11.
Qed.

Lemma cert_rf_mod: E0 ∩₁ R ≡₁ codom_rel cert_rf.
Proof.
  split.
  { intros x HH.
    apply cert_rf_complete in HH.
    desc. eexists. eauto. }
  rewrite (dom_r cert_rfD).
  rewrite cert_rf_codomE0.
  rewrite !codom_eqv1.
  basic_solver 10.
Qed.

Lemma cert_rf_in_furr: cert_rf ⊆ furr.
Proof. rewrite cert_rf_in_vf. apply vf_in_furr. Qed.

Lemma cert_rf_hb_sc_hb_irr: irreflexive (cert_rf ⨾ hb ⨾ (sc ⨾ hb)^?).
Proof.
  rewrite cert_rf_in_furr.
  apply furr_hb_sc_hb_irr; auto.
  all: apply COH.
Qed.

Lemma cert_rf_hb_irr: irreflexive (cert_rf ⨾ hb).
Proof.
  arewrite (cert_rf ⨾ hb ⊆ cert_rf ⨾ hb ⨾ (sc ⨾ hb)^?).
  { rewrite crE. relsf. }
  apply cert_rf_hb_sc_hb_irr.
Qed.

Lemma rf_D_in_vf : rf ⨾ ⦗D⦘ ⊆ vf.
Proof.
  rewrite (dom_l WF.(wf_rfD)).
  arewrite (D ⊆₁ D ∩₁ E).
  { generalize (@D_in_E G sc TC thread WF TCCOH). 
    basic_solver. }
  unfold vf. basic_solver 20.
Qed.

Lemma rf_vf_in_cert_rf : (rf ⨾ ⦗E0⦘) ∩ vf ⊆ cert_rf.
Proof.
  unfold cert_rf.
  rewrite minus_inter_compl.
  apply inclusion_inter_r.
  { rewrite (dom_r WF.(wf_rfD)).
    rewrite WF.(wf_rfl). basic_solver. }
  rewrite vf_in_furr.
  unfolder. ins. desf.
  intros HH. desf.
  eapply eco_furr_irr; eauto.
  all: try apply COH.
  eexists. split; eauto.
  apply fr_in_eco. eexists. split; eauto.
Qed.

Lemma rf_D_in_cert_rf : rf ⨾ ⦗ D ∩₁ E0 ⦘ ⊆ cert_rf.
Proof.
  rewrite <- rf_vf_in_cert_rf.
  apply inclusion_inter_r.
  { basic_solver 10. }
  rewrite <- rf_D_in_vf. basic_solver.
Qed.

Lemma rf_C_in_cert_rf : rf ⨾ ⦗ Tid_ thread ∩₁ C ⦘ ⊆ cert_rf.
Proof.
  rewrite <- rf_D_in_cert_rf.
  arewrite (Tid_ thread ∩₁ C ⊆₁ D ∩₁ E0); [|done].
  unfold CertExecution2.D, E0.
  basic_solver 10.
Qed.

Lemma rfi_in_cert_rf : rfi ⨾ ⦗ E0 ⦘ ⊆ cert_rf.
Proof.
  unfold cert_rf. rewrite minus_inter_compl.
  apply inclusion_inter_r.
  { rewrite (dom_r WF.(wf_rfiD)), !seqA.
    arewrite (⦗R⦘ ⨾ ⦗E0⦘ ⊆ ⦗E0 ∩₁ R⦘) by basic_solver.
    hahn_frame.
    unfold Execution.rfi. 
    apply inclusion_inter_r.
    2: { rewrite WF.(wf_rfl). basic_solver. }
    unfold vf. unionR left.
    rewrite (dom_l WF.(wf_rfD)), (dom_r WF.(wf_rfE)).
    rewrite sb_in_hb. basic_solver 30. }
  unfold Execution.rfi.
  rewrite vf_in_furr.
  unfolder. ins. desf.
  intros HH. desf.
  eapply eco_furr_irr; eauto.
  all: try apply COH.
  eexists. split; eauto.
  apply fr_in_eco. eexists. split; eauto.
Qed.

Lemma cert_rfi_union_cert_rfe : cert_rf ≡ cert_rfi ∪ cert_rfe.
Proof.
  unfold cert_rfi, cert_rfe.
  rewrite <- seq_union_l.
  rewrite <- id_union.
  arewrite (Tid_ thread ∪₁ NTid_ thread ≡₁ ⊤₁).
  { split; [basic_solver|].
    unfolder. ins. apply classic. }
  rewrite seq_id_l. by rewrite cert_rf_codomt at 1.
Qed.

Lemma cert_rf_D_in_rf : cert_rf ⨾ ⦗ D ∩₁ E0 ⦘ ⊆ rf.
Proof.
  arewrite (cert_rf ⊆ cert_rf ⨾ ⦗ E ∩₁ R ⦘).
  { rewrite (dom_r cert_rfD), (dom_r cert_rfE) at 1.
    basic_solver. }
  cdes COH. red in Comp. rewrite Comp.
  unfolder. ins. desf.
  assert (x0 = x); try subst x0; desf.
  eapply cert_rff; eauto.
  apply rf_D_in_cert_rf.
  apply seq_eqv_r.
  do 3 (split; auto).
  desf.
Qed.

Lemma cert_rf_D_eq_rf_D : cert_rf ⨾ ⦗ D ∩₁ E0 ⦘ ≡ rf ⨾ ⦗ D ∩₁ E0 ⦘.
Proof. generalize cert_rf_D_in_rf, rf_D_in_cert_rf. basic_solver 10. Qed.

Lemma cert_rf_Acq_in_rf : cert_rf ⨾ ⦗ Acq ⦘ ⊆ rf.
Proof.
  rewrite cert_rf_codomE0.
  arewrite (cert_rf ⊆ cert_rf ⨾ ⦗ E ∩₁ R ⦘).
  { rewrite (dom_r cert_rfD), (dom_r cert_rfE) at 1.
    basic_solver. }
  cdes COH. red in Comp. rewrite Comp.
  rewrite rfi_union_rfe at 1.
  rewrite codom_union, id_union, !seq_union_l, !seq_union_r.
  unfold Execution.rfi.
  rewrite cert_rf_codomt at 2.
  rewrite !seqA.
  rewrite <- !id_inter.
  arewrite (Tid_ thread ∩₁ (codom_rel (rfe G) ∩₁ (E0 ∩₁ Acq)) ⊆₁
            D ∩₁ E0).
  { apply set_subset_inter_r; split; [|basic_solver].
    unfold CertExecution2.D.
    apply set_inter_Proper; auto.
    unionR right. rewrite WF.(wf_rfeD) at 1. basic_solver. }
  unionL.
  2: by apply cert_rf_D_in_rf.
  unfolder. ins. desf.
  assert (x0 = x); desf.
  eapply cert_rff; eauto.
  apply rfi_in_cert_rf. apply seq_eqv_r.
  do 2 (split; auto).
Qed.

Lemma cert_rf_D_rf : cert_rf ⨾ ⦗ D ⦘ ⊆ rf.
Proof.
  rewrite cert_rf_codomE0, !seqA.
  rewrite <- id_inter, set_interC.
  apply cert_rf_D_in_rf.
Qed.

Lemma cert_rf_sb_F_Acq_in_rf :
  cert_rf ⨾ sb ⨾ ⦗F⦘ ⨾ ⦗ Acq ⦘ ⨾ ⦗ E0 ⦘ ⊆ rf ⨾ sb.
Proof.
  rewrite (dom_r cert_rfD), !seqA.
  rewrite (dom_r cert_rfE), !seqA.
  rewrite <- !id_inter, <- !set_interA.
  arewrite (⦗E⦘ ⨾ ⦗R⦘ ⊆ ⦗E∩₁R⦘) by basic_solver.

  assert (dom_rel (⦗E ∩₁ R⦘ ⨾ sb ⨾ ⦗F ∩₁ Acq ∩₁ E0⦘) ⊆₁ D) as AA.
  2: { rewrite (dom_rel_helper AA).
       sin_rewrite cert_rf_D_rf. basic_solver. }
  unfold CertExecution2.D.
  apply set_subset_inter_r. split.
  { unfolder. ins. desf.
    match goal with 
    | H: sb _ _ |- _ => apply sb_tid_init in H
    end.
    match goal with
    | H: E0 _ |- _ => inv H
    end.
    desf.
    exfalso.
    eapply read_or_fence_is_not_init with (G:=G); auto.
    2: by eauto.
    eauto. }
  repeat unionR left.
  unfolder. ins. desf.
  assert (C y) as AA.
  2: { eapply dom_sb_covered; eauto.
       basic_solver 10. }
  match goal with
  | H: E0 _ |- _ => inv H
  end.
  match goal with
  | H: (C ∪₁ _) _ |- _ => inv H
  end.
  destruct H7 as [z HH]. destruct_seq_r HH as IZ.
  destruct HH as [HH|HH].
  { rewrite HH in *. eapply issuedW in IZ; eauto. type_solver. }
  eapply issued_in_issuable in IZ; eauto.
  apply IZ. eexists. apply seq_eqv_r. split; eauto.
  red. right. apply seq_eqv_l. do 2 (split; auto).
  mode_solver.
Qed.

Lemma cert_rf_F_Acq_in_rf :
  cert_rf ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗ Acq ⦘ ⨾ ⦗ E0 ⦘ ⊆ rf ⨾ sb^?.
Proof.
  rewrite !crE, !seq_union_l, !seq_union_r, !seq_id_l, !seq_id_r, !seqA.
  apply union_mori.   
  { sin_rewrite cert_rf_Acq_in_rf. basic_solver. }
  apply cert_rf_sb_F_Acq_in_rf.
Qed.

Lemma non_I_cert_rf: ⦗set_compl I⦘ ⨾ cert_rf ⊆ sb.
Proof.
  cdes COH.
  rewrite cert_rf_codomE0. rewrite (dom_r cert_rfD).
  rewrite cert_rf_in_vf. rewrite !seqA.
  unfold vf.
  assert (E0 ⊆₁ C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)) as E0CI by (unfold E0; basic_solver 10).
  assert (⦗set_compl I⦘ ⨾ ⦗W⦘ ⨾ ⦗C⦘ ⊆ ∅₂) as TTU.
  { unfolder. ins. desf.
    match goal with H : ~ I _ |- _ => apply H end.
    eapply w_covered_issued; [|split]; eauto. }

  assert (rf ⨾ ⦗C⦘ ⊆ ⦗I⦘ ⨾ rf ⨾ ⦗C⦘) as IRFC.
  { eapply rf_covered; eauto. }

  assert (⦗set_compl I⦘ ⨾ ⦗W⦘ ⨾ rf ⨾ ⦗D⦘ ⨾ ⦗C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆ sb) as RFSB_I.
  { unfold CertExecution2.D.
    set (A := C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)).
    relsf.
    rewrite !id_union.
    rewrite !seq_union_l, !seq_union_r.
    unionL.
    { arewrite (Tid_ thread ∩₁ C ⊆₁ C) by basic_solver.
      sin_rewrite IRFC. basic_solver. }
    { arewrite (Tid_ thread ∩₁ I ⊆₁ W).
      { rewrite issuedW; eauto. basic_solver. }
      rewrite (dom_r WF.(wf_rfD)).
      type_solver. }
    { basic_solver. }
    { rewrite rfi_union_rfe.
      rewrite !seq_union_l, !seq_union_r.
      unionL.
      { generalize (@sb_trans G). unfold Execution.rfi. basic_solver. }
      arewrite (rfe G ⨾ ⦗Tid_ thread ∩₁ dom_rel (rfi^? ⨾ imm_common.ppo G ⨾ ⦗I⦘)⦘ ⊆
                rfe G ⨾ ⦗dom_rel (imm_common.ppo G ⨾ ⦗I⦘)⦘).
      2: { arewrite (rfe G ⨾ ⦗dom_rel (imm_common.ppo G ⨾ ⦗I⦘)⦘ ⊆
                     ⦗I⦘ ⨾ rfe G ⨾ ⦗dom_rel (imm_common.ppo G ⨾ ⦗I⦘)⦘).
           { generalize (dom_rfe_ppo_issued TCCOH). basic_solver 20. }
           basic_solver. }
      erewrite set_subset_inter_l.
      2: right; reflexivity.
      rewrite crE. relsf.
      rewrite id_union, !seq_union_r.
      unionL; [done|].
      rewrite (dom_l WF.(wf_rfiD)), (dom_r WF.(wf_rfeD)), !seqA, dom_eqv1.
      type_solver. }
    { arewrite (rf ⨾ ⦗Tid_ thread ∩₁ codom_rel (⦗I⦘ ⨾ rfi)⦘ ⊆ sb).
      2: { generalize (@sb_trans G). basic_solver. }
      unfolder; ins; desf.
      match goal with H : rfi _ _ |- _ => destruct H as [AA BB] end.
      eapply wf_rff in H; eauto.
      apply H in AA. by rewrite AA. }
    unfold A.
    rewrite !id_union. rewrite !seq_union_r.
    unionL.
    { rewrite seq_eqvC. sin_rewrite IRFC. basic_solver. }
    rewrite rfi_union_rfe. rewrite !seq_union_l, !seq_union_r.
    unionL.
    { unfold Execution.rfi. basic_solver. }
    assert (∅₂ ⊆ sb) as UU by done.
    etransitivity; eauto.
    unfolder; ins; desf.
    { match goal with H : I _ |- _ => eapply issuedW in H; eauto end.
      rewrite H2 in *. type_solver. }
    match goal with H : ~ I _ |- _ => apply H end.
    eapply dom_rfe_acq_sb_issued; eauto.
    eexists. eexists. split; eauto.
    apply seq_eqv_l. split; [split|]; auto.
    apply seq_eqv_r. split; eauto. }

  assert (⦗set_compl I⦘ ⨾ ⦗W⦘ ⨾ rf ⨾ ⦗D⦘ ⨾ ⦗E0⦘ ⊆ sb) as RFSB by (by rewrite E0CI).

  assert (hb ⨾ ⦗E0⦘ ⊆ (⦗C⦘ ⨾ hb ∪ sb) ⨾ ⦗E0⦘) as HBA.
  { seq_rewrite <- seq_eqvK.
    arewrite (hb ⨾ ⦗E0⦘ ⊆ ⦗C⦘ ⨾ hb ∪ sb). 2: basic_solver 10.
    rewrite E0CI. eapply hb_in_Chb_sb; eauto. }

  assert (sc ⨾ hb ⨾ ⦗E0⦘ ⊆ ⦗C⦘ ⨾ sc ⨾ hb) as SCA.
  { rewrite HBA at 1. rewrite !seq_union_l, !seq_union_r, !seqA.
    unionL.
    { sin_rewrite sc_covered; eauto. basic_solver. }
    rewrite E0CI.
    rewrite sbCsbI_CsbI; eauto.
    sin_rewrite (scCsbI_C WF COH TCCOH RELCOH).
    rewrite sb_in_hb. basic_solver. }

  assert (⦗set_compl I⦘ ⨾ ⦗W⦘ ⨾ rf ⨾ ⦗D⦘ ⨾ hb ⨾ ⦗E0⦘ ⊆ sb) as BB.
  { rewrite HBA, !seq_union_l, !seq_union_r, !seqA.
    unionL.
    { arewrite (⦗D⦘ ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ ⦗D⦘) by basic_solver.
      sin_rewrite IRFC. basic_solver. }
    rewrite E0CI. rewrite sbCsbI_CsbI; eauto.
    sin_rewrite RFSB_I. generalize (@sb_trans G). basic_solver. }

  rewrite !seq_union_l, !seq_union_r.
  unionL.
  2: { rewrite !seqA.
       rewrite (dom_l WF.(wf_rfD)), !seqA.
       arewrite_id ⦗R⦘. rewrite seq_id_l.
       rewrite crE. rewrite !seq_union_l, !seq_union_r, seq_id_l.
       rewrite sb_in_hb at 1.
       unionL; auto. }
  
  rewrite !seqA.
  arewrite (⦗set_compl I⦘ ⨾ ⦗W⦘ ⨾ (rf ⨾ ⦗C⦘)^? ⊆ ⦗set_compl I⦘ ⨾ ⦗W⦘).
  { rewrite crE. rewrite !seq_union_r, seq_id_r. unionL; [done|].
    sin_rewrite IRFC. basic_solver. }

  arewrite_id ⦗E⦘. rewrite seq_id_l.

  rewrite !crE.
  repeat (rewrite seq_union_l, seq_id_l).
  rewrite !seq_union_r.
  unionL.
  all: try (rewrite Wf_sc.(wf_scD); type_solver).
  { type_solver. }
  all: arewrite_id ⦗R⦘; rewrite seq_id_l; auto.
  all: try (sin_rewrite rewrite_trans; [|by apply hb_trans]).
  1-3: rewrite E0CI; sin_rewrite hb_in_Chb_sb; eauto; relsf;
    unionL; [sin_rewrite TTU|]; basic_solver.
  all: rewrite SCA.
  sin_rewrite hb_covered; eauto; rewrite !seqA.
  sin_rewrite TTU. basic_solver.
Qed.

Lemma cert_rf_ntid_sb : cert_rf ⊆ ⦗ NTid_ thread ⦘ ⨾ cert_rf ∪ sb.
Proof.
  arewrite (cert_rf ⊆ ⦗Tid_ thread ∪₁ NTid_ thread⦘ ⨾ cert_rf ⨾ ⦗Tid_ thread⦘).
  { unfolder. intros x y HH. splits; auto.
    { apply classic. }
    generalize HH. unfold cert_rf, E0. unfolder. basic_solver. }
  rewrite id_union, seq_union_l.
  unionL; [|basic_solver].
  unionR right.
  rewrite cert_rfD, !seqA.
  unfolder. intros x y [[TX WX] [VF [RY TY]]].
  apply cert_rfE in VF. destruct_seq VF as [EX EY].
  assert (~ is_init y) as NIY. 
  { intros HH. eapply init_w in HH; eauto. type_solver. }
  destruct (classic (is_init x)) as [|NIX].
  { by apply init_ninit_sb. }
  edestruct same_thread with (x:=x) (y:=y) as [[|SB]|SB]; eauto.
  { by rewrite TX. }
  { type_solver. }
  exfalso.
  eapply cert_rf_hb_irr. eexists; splits; eauto.
    by apply sb_in_hb.
Qed.

Lemma cert_rfi_in_sb (NINITT : thread <> tid_init) : 
  cert_rfi ⊆ sb.
Proof. 
  unfold cert_rfi. unfolder. intros x y [TX [RFXY TY]].
  red in RFXY.
  (* destruct RFXY as [RFXY [EEY NDY]] *)
  (* apply seq_eqv_r in RFXY. destruct RFXY as [RFXY [EEY NDY]]. *)
  apply cert_rfE in RFXY; auto. destruct_seq RFXY as [EX EY].
  apply cert_rfD in RFXY. destruct_seq RFXY as [WX RY].
  edestruct same_thread with (x:=x) (y:=y) as [[|SBXY]|SBXY]; eauto.
  { intros HH.
    destruct x; simpls.
    rewrite <- TX in *. desf. }
  { by rewrite TX. }
  { subst. exfalso. type_solver. }
  exfalso. eapply cert_rf_hb_sc_hb_irr; eauto.
  eexists. splits; eauto.
  eexists. splits.
  { eapply imm_s_hb.sb_in_hb; eauto. }
    by left. 
Qed.

Lemma E0_sbprcl : doma (⦗Tid_ thread ⦘ ⨾ sb ⨾ ⦗E0⦘) E0.
Proof. 
  red. intros x y SBXY.
  destruct_seq SBXY as [TX TY]. destruct TY as [TY EEY].
  split; auto.
  destruct EEY as [COVY|ISSY]; [left|right].
  { eapply dom_sb_covered; eauto.
    eexists. apply seq_eqv_r. eauto. }
  destruct ISSY as [z ISSY].
  apply seq_eqv_r in ISSY. destruct ISSY as [SBYZ ISSZ].
  exists z. apply seq_eqv_r. split; auto.
  generalize (@sb_trans G) SBXY SBYZ. basic_solver. 
Qed.

End Properties.

End CertRf.