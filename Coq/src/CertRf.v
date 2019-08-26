From hahn Require Import Hahn.
From imm Require Import Events Execution TraversalConfig TraversalConfigAlt
     imm_common imm_s imm_s_hb CertExecution1 (*CertExecution2*)
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

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).

Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).

Notation "'sb'"  := (G.(sb)).
Notation "'ppo'" := (G.(ppo)).
Notation "'sw'"  := (G.(imm_s_hb.sw)).
Notation "'hb'"  := (G.(imm_s_hb.hb)).
Notation "'rf'"  := (G.(rf)).
Notation "'rfi'" := (G.(rfi)).
Notation "'rfe'" := (G.(rfe)).
Notation "'co'"  := (G.(co)).
Notation "'loc'" := (loc lab).

Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).
Notation "'R_' l" := (R ∩₁ Loc_ l) (at level 1).

Notation "'furr'" := (furr G sc).

(* TODO: make up a better name *)
Definition E0 := (C ∪₁ dom_rel (sb^? ⨾ ⦗ I ⦘)).

Definition D := 
  C ∪₁ I ∪₁
  dom_rel (rfi^? ⨾ ppo ⨾ ⦗ I ⦘) ∪₁ 
  codom_rel (⦗I⦘ ⨾ rfi) ∪₁ 
  codom_rel (rfe ⨾ ⦗ R ∩₁ Acq ⦘).

Definition vf := 
  ⦗ W ⦘ ⨾ (rf ⨾ ⦗ C ⦘)^? ⨾ hb^? ⨾ sc^? ⨾ hb^? ⨾ ⦗ E ⦘ ∪
  rf ⨾ ⦗ D ⦘ ⨾ sb^?.

(* Definition cert_rf := *)
(*   vf ∩ same_loc lab ⨾ ⦗ E0 ∩₁ R ⦘ \ co ⨾ vf. *)

Definition cert_rf :=
  vf ∩ same_loc lab ⨾ ⦗ R ⦘ \ co ⨾ vf.

Definition cert_rfi := ⦗  Tid_ thread ⦘ ⨾ cert_rf ⨾ ⦗ Tid_ thread ⦘.
Definition cert_rfe := ⦗ NTid_ thread ⦘ ⨾ cert_rf ⨾ ⦗ Tid_ thread ⦘.

Section Properties.
Variable WF  : Wf G.
Variable COH : imm_consistent G sc.
Variable TCCOH : tc_coherent G sc TC.
Variable RELCOH : W ∩₁ Rel ∩₁ I ⊆₁ C.

Lemma D_in_E : D ⊆₁ E.
Proof. 
  unfold D.
  rewrite (wf_ppoE WF), (wf_rfiE WF), (wf_rfeE WF), (coveredE TCCOH).
  rewrite (issuedE TCCOH) at 1.
  basic_solver 21. 
Qed.

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

Lemma cert_rfD : cert_rf ≡ ⦗W⦘ ⨾ cert_rf ⨾ ⦗R⦘.
Proof.
  apply dom_helper_3.
  unfold cert_rf.
  rewrite inclusion_minus_rel.
  rewrite inter_inclusion.
  rewrite vf_dom.
  basic_solver.
Qed.

(* Lemma cert_rf_codomE0 : cert_rf ≡ cert_rf ⨾ ⦗E0⦘. *)
(* Proof. unfold cert_rf. basic_solver. Qed. *)

(* Lemma cert_rf_codomt : cert_rf ≡ cert_rf ⨾ ⦗Tid_ thread⦘. *)
(* Proof. *)
(*   split; [|basic_solver]. *)
(*   rewrite cert_rf_codomE0 at 1. *)
(*   unfold E0. basic_solver. *)
(* Qed. *)

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

(* Lemma cert_rf_mod: E0 ∩₁ R ≡₁ codom_rel cert_rf. *)
(* Proof. *)
(*   split. *)
(*   { intros x HH. *)
(*     apply cert_rf_complete in HH. *)
(*     desc. eexists. eauto. } *)
(*   rewrite (dom_r cert_rfD). *)
(*   rewrite cert_rf_codomE0. *)
(*   rewrite !codom_eqv1. *)
(*   basic_solver 10. *)
(* Qed. *)

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
  { generalize D_in_E. basic_solver. }
  unfold vf. basic_solver 20.
Qed.

(* Lemma rf_vf_in_cert_rf : (rf ⨾ ⦗E0⦘) ∩ vf ⊆ cert_rf. *)
Lemma rf_vf_in_cert_rf : rf ∩ vf ⊆ cert_rf.
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

Lemma rf_D_in_cert_rf : rf ⨾ ⦗ D ⦘ ⊆ cert_rf.
Proof.
  rewrite <- rf_vf_in_cert_rf.
  apply inclusion_inter_r.
  { basic_solver 10. }
  rewrite <- rf_D_in_vf. basic_solver.
Qed.

Lemma rf_C_in_cert_rf : rf ⨾ ⦗ C ⦘ ⊆ cert_rf.
Proof.
  rewrite <- rf_D_in_cert_rf.
  unfold D.
  rewrite !id_union, !seq_union_r.
  basic_solver 10.
Qed.

Lemma rfi_in_cert_rf : rfi ⊆ cert_rf.
Proof.
  unfold cert_rf. rewrite minus_inter_compl.
  apply inclusion_inter_r.
  { rewrite (dom_r WF.(wf_rfiD)). 
    (* arewrite (⦗R⦘ ⨾ ⦗E0⦘ ⊆ ⦗E0 ∩₁ R⦘) by basic_solver. *)
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

(* Lemma cert_rfi_union_cert_rfe : cert_rf ≡ cert_rfi ∪ cert_rfe. *)
(* Proof. *)
(*   unfold cert_rfi, cert_rfe. *)
(*   rewrite <- seq_union_l. *)
(*   rewrite <- id_union. *)
(*   arewrite (Tid_ thread ∪₁ NTid_ thread ≡₁ ⊤₁). *)
(*   { split; [basic_solver|]. *)
(*     unfolder. ins. apply classic. } *)
(*   rewrite seq_id_l. by rewrite cert_rf_codomt at 1. *)
(* Qed. *)

Lemma cert_rf_D_in_rf : cert_rf ⨾ ⦗ D ⦘ ⊆ rf.
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
Qed.

Lemma cert_rf_C_in_rf : cert_rf ⨾ ⦗ C ⦘ ⊆ rf.
Proof.
  arewrite (C ⊆₁ D).
  { unfold D. basic_solver 10. }
  apply cert_rf_D_in_rf.
Qed.

Lemma cert_rf_D_eq_rf_D : cert_rf ⨾ ⦗ D ⦘ ≡ rf ⨾ ⦗ D ⦘.
Proof. generalize cert_rf_D_in_rf, rf_D_in_cert_rf. basic_solver 10. Qed.

Lemma cert_rf_Acq_in_rf : cert_rf ⨾ ⦗ Acq ⦘ ⊆ rf.
Proof.
  (* rewrite cert_rf_codomE0. *)
  arewrite (cert_rf ⊆ cert_rf ⨾ ⦗ E ∩₁ R ⦘).
  { rewrite (dom_r cert_rfD), (dom_r cert_rfE) at 1.
    basic_solver. }
  cdes COH. red in Comp. rewrite Comp.
  rewrite rfi_union_rfe at 1.
  rewrite codom_union, id_union, !seq_union_l, !seq_union_r.
  unfold Execution.rfi.
  (* rewrite cert_rf_codomt at 2. *)
  (* rewrite !seqA. *)
  rewrite <- !id_inter.
  arewrite (codom_rel rfe ∩₁ Acq ⊆₁ D).
  { unfold D.
    rewrite WF.(wf_rfeD).
    basic_solver 10. }
  unionL.
  2: by apply cert_rf_D_in_rf.
  unfolder. ins. desf.
  assert (x0 = x); desf.
  eapply cert_rff; eauto.
  apply rfi_in_cert_rf.
  apply seq_eqv_r.
  basic_solver.
Qed.

Lemma cert_rf_sb_F_Acq_in_rf :
  cert_rf ⨾ sb ⨾ ⦗F⦘ ⨾ ⦗ Acq ⦘ ⨾ ⦗E0⦘ ⊆ rf ⨾ sb.
Proof.
  arewrite (sb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘ ⨾ ⦗E0⦘ ⊆ ⦗C⦘ ⨾ sb).
  2 : by sin_rewrite cert_rf_C_in_rf.
  rewrite <- !id_inter, seq_eqv_r, seq_eqv_l. 
  intros x y [SB [Fy [ACQy E0y]]].
  splits; auto.
  eapply dom_sb_covered; eauto.
  exists y. apply seq_eqv_r.
  splits; auto.
  destruct E0y as [Cy | SBIy]; auto.
  destruct SBIy as [z HH].
  apply seq_eqv_r in HH.
  destruct HH as [[EQz | SB'] Iy].
  { subst. eapply issuedW in Iy; eauto. type_solver. }
  eapply dom_F_sb_issued; eauto.
  unfold is_ra.
  basic_solver 20.
Qed.

Lemma cert_rf_F_Acq_in_rf :
  cert_rf ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗ Acq ⦘ ⨾ ⦗ E0 ⦘ ⊆ rf ⨾ sb^?.
Proof.
  rewrite !crE, !seq_union_l, !seq_union_r, !seq_id_l, !seq_id_r, !seqA.
  apply union_mori.   
  { sin_rewrite cert_rf_Acq_in_rf. basic_solver. }
  apply cert_rf_sb_F_Acq_in_rf.
Qed.  

Lemma nI_rf_D_E0_in_sb :
  ⦗set_compl I⦘ ⨾ rf ⨾ ⦗D⦘ ⨾ ⦗E0⦘ ⊆ sb.
Proof. 
  unfold D.
  relsf.
  rewrite !id_union.
  rewrite !seq_union_l, !seq_union_r.
  unionL.
  { seq_rewrite rf_covered; eauto. basic_solver. }
  { rewrite issuedW at 2; eauto. 
    rewrite (dom_r WF.(wf_rfD)).
    type_solver. }
  { rewrite rfi_union_rfe.
    rewrite !seq_union_l, !seq_union_r.
    unionL.
    { generalize (@sb_trans G). unfold Execution.rfi. basic_solver. }
    arewrite (
      rfe ⨾ ⦗dom_rel (rfi^? ⨾ ppo ⨾ ⦗I⦘)⦘ ⊆ rfe ⨾ ⦗dom_rel (ppo ⨾ ⦗I⦘)⦘
    ).
    { rewrite crE. relsf.
      rewrite id_union, !seq_union_r.
      unionL; [done|].
      rewrite (dom_l WF.(wf_rfiD)), 
              (dom_r WF.(wf_rfeD)). 
      rewrite !seqA, dom_eqv1.
      type_solver. }
    arewrite (
      rfe ⨾ ⦗dom_rel (ppo ⨾ ⦗I⦘)⦘ ⊆ ⦗I⦘ ⨾ rfe ⨾ ⦗dom_rel (ppo ⨾ ⦗I⦘)⦘
    ).
    { generalize (dom_rfe_ppo_issued TCCOH). basic_solver 20. }
    basic_solver. }
  { arewrite (rf ⨾ ⦗codom_rel (⦗I⦘ ⨾ rfi)⦘ ⊆ sb).
    2: { generalize (@sb_trans G). basic_solver. }
    unfolder; ins; desf.
    match goal with H : rfi _ _ |- _ => destruct H as [AA BB] end.
    eapply wf_rff in H; eauto.
    apply H in AA. by rewrite AA. }
  unfold E0.
  rewrite !id_union. rewrite !seq_union_r.
  unionL.
  { rewrite seq_eqvC. seq_rewrite rf_covered; eauto. basic_solver. } 
  rewrite rfi_union_rfe. rewrite !seq_union_l, !seq_union_r.
  unionL.
  { unfold Execution.rfi. basic_solver. }
  assert (∅₂ ⊆ sb) as UU by done.
  etransitivity; eauto.
  unfolder; ins; desf.
  { match goal with H : I _ |- _ => eapply issuedW in H; eauto end.
    type_solver. }
  match goal with H : ~ I _ |- _ => apply H end.
  eapply dom_rfe_acq_sb_issued; eauto.
  eexists. eexists. split; eauto.
  apply seq_eqv_l. split; [split|]; auto.
  apply seq_eqv_r. split; eauto. 
Qed.

Lemma non_I_cert_rf: ⦗set_compl I⦘ ⨾ cert_rf ⨾ ⦗E0⦘ ⊆ sb.
Proof.
  cdes COH.
  rewrite (dom_r (cert_rfD)).
  rewrite cert_rf_in_vf. 
  unfold vf.
  arewrite_id (⦗E⦘).
  relsf. rewrite !seqA. unionL.

  { (* TODO: make lemmas about `C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)` ? *)
    assert (hb ⨾ ⦗E0⦘ ⊆ (⦗C⦘ ⨾ hb ∪ sb) ⨾ ⦗E0⦘) as HBA.
    { seq_rewrite <- seq_eqvK.
      arewrite (hb ⨾ ⦗E0⦘ ⊆ ⦗C⦘ ⨾ hb ∪ sb).
      2: basic_solver 10.
      eapply hb_in_Chb_sb; eauto. }

    assert (sc ⨾ hb ⨾ ⦗E0⦘ ⊆ ⦗C⦘ ⨾ sc ⨾ hb) as SCA.
    { rewrite HBA at 1. 
      rewrite !seq_union_l, !seq_union_r, !seqA.
      unionL.
      { sin_rewrite sc_covered; eauto. basic_solver. }
      unfold E0.
      rewrite sbCsbI_CsbI; eauto.
      sin_rewrite (scCsbI_C WF COH TCCOH RELCOH).
      rewrite sb_in_hb. basic_solver. }

    assert (⦗set_compl I⦘ ⨾ rf ⨾ ⦗D⦘ ⨾ hb ⨾ ⦗E0⦘ ⊆ sb) as BB.
    { rewrite HBA, !seq_union_l, !seq_union_r, !seqA.
      unionL.
      { arewrite (⦗D⦘ ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ ⦗D⦘) by basic_solver.
        seq_rewrite rf_covered; eauto.
        basic_solver. }
      unfold E0. 
      rewrite sbCsbI_CsbI; eauto.
      fold E0.
      sin_rewrite nI_rf_D_E0_in_sb.
      generalize (@sb_trans G). 
      basic_solver. }

    rewrite !crE.
    repeat (rewrite seq_union_l, seq_id_l).
    rewrite !seq_union_r.
    unionL.
    all: try (
      try rewrite (dom_r WF.(wf_rfD)); 
      try rewrite Wf_sc.(wf_scD); 
      by type_solver 
    ).
    5-9: 
      erewrite rf_covered; eauto; 
      basic_solver.
    all: arewrite_id (⦗R⦘); seq_rewrite seq_id_r.
    3 : sin_rewrite rewrite_trans; [|by apply hb_trans].
    1-3: unfold E0; sin_rewrite hb_in_Chb_sb; eauto.
    1-3: rewrite !seq_union_r; seq_rewrite <- !id_inter. 
    1-3: rewrite set_interA; erewrite w_covered_issued; eauto.
    1-3: basic_solver.
    rewrite SCA. sin_rewrite hb_covered; eauto.
    rewrite !seqA. seq_rewrite <- !id_inter. 
    rewrite set_interA; erewrite w_covered_issued; eauto.
    basic_solver. }

  arewrite_id (⦗R⦘); seq_rewrite seq_id_r.
  arewrite (sb^? ⨾ ⦗E0⦘ ⊆ ⦗E0⦘ ⨾ sb^?).
  { unfold E0.
    rewrite id_union. 
    rewrite seq_union_r, seq_union_l.
    rewrite crE at 1 2 4 6. relsf.
    repeat apply union_mori; try done.
    { rewrite dom_rel_helper; 
        [|eapply dom_sb_covered; eauto].
      basic_solver. }
    rewrite !seq_eqv_l, !seq_eqv_r.
    unfolder; ins; desf; splits; auto.
    { do 2 eexists; splits; eauto. }
    do 2 eexists; splits.
    2-3: eauto.
    right. eapply sb_trans; eauto. }
  sin_rewrite nI_rf_D_E0_in_sb.
  generalize sb_trans. basic_solver.
Qed.

(* Lemma cert_rf_ntid_sb : cert_rf ⊆ ⦗ NTid_ thread ⦘ ⨾ cert_rf ∪ sb. *)
(* Proof. *)
(*   arewrite (cert_rf ⊆ ⦗Tid_ thread ∪₁ NTid_ thread⦘ ⨾ cert_rf ⨾ ⦗Tid_ thread⦘). *)
(*   { unfolder. intros x y HH. splits; auto. *)
(*     { apply classic. } *)
(*     generalize HH. unfold cert_rf, E0. unfolder. basic_solver. } *)
(*   rewrite id_union, seq_union_l. *)
(*   unionL; [|basic_solver]. *)
(*   unionR right. *)
(*   rewrite cert_rfD, !seqA. *)
(*   unfolder. intros x y [[TX WX] [VF [RY TY]]]. *)
(*   apply cert_rfE in VF. destruct_seq VF as [EX EY]. *)
(*   assert (~ is_init y) as NIY.  *)
(*   { intros HH. eapply init_w in HH; eauto. type_solver. } *)
(*   destruct (classic (is_init x)) as [|NIX]. *)
(*   { by apply init_ninit_sb. } *)
(*   edestruct same_thread with (x:=x) (y:=y) as [[|SB]|SB]; eauto. *)
(*   { by rewrite TX. } *)
(*   { type_solver. } *)
(*   exfalso. *)
(*   eapply cert_rf_hb_irr. eexists; splits; eauto. *)
(*     by apply sb_in_hb. *)
(* Qed. *)

(* Lemma cert_rfi_in_sb (NINITT : thread <> tid_init) :  *)
(*   cert_rfi ⊆ sb. *)
(* Proof.  *)
(*   unfold cert_rfi. unfolder. intros x y [TX [RFXY TY]]. *)
(*   red in RFXY. *)
(*   (* destruct RFXY as [RFXY [EEY NDY]] *) *)
(*   (* apply seq_eqv_r in RFXY. destruct RFXY as [RFXY [EEY NDY]]. *) *)
(*   apply cert_rfE in RFXY; auto. destruct_seq RFXY as [EX EY]. *)
(*   apply cert_rfD in RFXY. destruct_seq RFXY as [WX RY]. *)
(*   edestruct same_thread with (x:=x) (y:=y) as [[|SBXY]|SBXY]; eauto. *)
(*   { intros HH. *)
(*     destruct x; simpls. *)
(*     rewrite <- TX in *. desf. } *)
(*   { by rewrite TX. } *)
(*   { subst. exfalso. type_solver. } *)
(*   exfalso. eapply cert_rf_hb_sc_hb_irr; eauto. *)
(*   eexists. splits; eauto. *)
(*   eexists. splits. *)
(*   { eapply imm_s_hb.sb_in_hb; eauto. } *)
(*     by left.  *)
(* Qed. *)

(* Lemma E0_sbprcl : doma (⦗Tid_ thread ⦘ ⨾ sb ⨾ ⦗E0⦘) E0. *)
(* Proof.  *)
(*   unfold E0. *)
(*   red. intros x y SBXY. *)
(*   destruct_seq SBXY as [TX TY].  *)
(*   destruct TY as [TY EEY]. *)
(*   split; auto. *)
(*   destruct EEY as [COVY|ISSY]; [left|right]. *)
(*   { eapply dom_sb_covered; eauto. *)
(*     eexists. apply seq_eqv_r. eauto. } *)
(*   destruct ISSY as [z ISSY]. *)
(*   apply seq_eqv_r in ISSY. destruct ISSY as [SBYZ ISSZ]. *)
(*   exists z. apply seq_eqv_r. split; auto. *)
(*   generalize (@sb_trans G) SBXY SBYZ. basic_solver.  *)
(* Qed. *)

Lemma E0_rmwsfcl (RMWCOV : forall r w, rmw r w -> C r <-> C w) :
  ⦗E0⦘ ⨾ rmw ≡ ⦗E0⦘ ⨾ rmw ⨾ ⦗E0⦘.
Proof.
  split; [|basic_solver].
  unfold E0.
  (* rewrite !id_inter. *)
  (* rewrite seq_eqvC at 1 2. rewrite !seqA. *)
  (* arewrite (⦗Tid_ thread⦘ ⨾ rmw ⊆ ⦗Tid_ thread⦘ ⨾ rmw ⨾ ⦗Tid_ thread⦘). *)
  (* { arewrite (rmw ⊆ rmw ∩ same_tid) at 1. *)
  (*   2: basic_solver. *)
  (*   apply inclusion_inter_r; [done|]. apply WF.(wf_rmwt). } *)
  rewrite !id_union. 
  rewrite !seq_union_l, !seq_union_r.
  unionL.
  { repeat unionR left.
    unfolder. ins. splits; desf.
    match goal with
    | H : rmw ?x ?y |- _ => eapply RMWCOV in H
    end.
    intuition. }
  unionR right -> right.
  rewrite WF.(wf_rmwD) at 1.
  unfolder. ins. splits; desf.
  1,3: exfalso;
    match goal with
    | H : I ?y |- _ => rename H into AA
    end;
    eapply issuedW in AA; eauto;
      type_solver.
  all: do 2 eexists.
  { splits; eauto. }
  splits; [| |by eauto].
  2: done.
  destruct (classic (y = y0)) as [|NEQ]; eauto.
  right.
  match goal with
  | H : rmw ?x ?y |- _ => rename H into RMW 
  end.
  apply WF.(rmw_from_non_init) in RMW.
  destruct_seq_l RMW as AA.
  edestruct sb_semi_total_l with (x:=x); eauto.
  { by apply rmw_in_sb. }
  exfalso.
  eapply wf_rmwi; eauto.
Qed.

End Properties.

End CertRf.
