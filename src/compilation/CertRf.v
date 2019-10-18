From hahn Require Import Hahn.
From imm Require Import
     AuxDef
     Events Execution TraversalConfig TraversalConfigAlt
     SimTraversal SimTraversalProperties
     imm_common imm_s imm_s_hb CertExecution1
     CombRelations Execution_eco.
Require Import AuxRel.
Require Import AuxDef.
Require Import ImmProperties.

Section CertRf.
Variable G  : execution.
Variable sc : relation actid.
Variable TC : trav_config.

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

Definition CsbI := (C ∪₁ dom_rel (sb^? ⨾ ⦗ I ⦘)).

(* TODO: rename to `determined`,
 * i.e. in the same style as `covered`/`issued` *)
Definition D :=
  C ∪₁ I ∪₁
  dom_rel (rfi^? ⨾ ppo ⨾ ⦗ I ⦘) ∪₁
  codom_rel (⦗I⦘ ⨾ rfi) ∪₁
  codom_rel (rfe ⨾ ⦗ R ∩₁ Acq ⦘).

Definition vf :=
  ⦗ W ⦘ ⨾ (rf ⨾ ⦗ C ⦘)^? ⨾ hb^? ⨾ sc^? ⨾ hb^? ⨾ ⦗ E ⦘ ∪
  rf ⨾ ⦗ D ⦘ ⨾ sb^?.

Definition cert_rf :=
  vf ∩ same_loc lab ⨾ ⦗ CsbI ∩₁ R ⦘ \ co ⨾ vf.

Definition cert_rfi := cert_rf ∩ sb.
Definition cert_rfe := cert_rf \  sb.

Section Properties.
Variable WF  : Wf G.
Variable COH : imm_consistent G sc.
Variable TCCOH : tc_coherent G sc TC.
Variable RELCOH : W ∩₁ Rel ∩₁ I ⊆₁ C.

(******************************************************************************)
(** ** CsbI propeties *)
(******************************************************************************)

Lemma CsbI_in_E : CsbI ⊆₁ E.
Proof.
  unfold CsbI.
  rewrite coveredE, issuedE; try edone.
  rewrite (dom_l (@wf_sbE G)).
  basic_solver.
Qed.

Lemma CsbI_sb_prcl :
  dom_rel (sb ⨾ ⦗ CsbI ⦘) ⊆₁ CsbI.
Proof.
  unfold CsbI.
  rewrite id_union.
  rewrite seq_union_r.
  rewrite dom_union.
  apply set_union_Proper.
  { eapply dom_sb_covered; eauto. }
  rewrite !seq_eqv_r.
  unfolder; ins; desf; splits; auto.
  { do 2 eexists; splits; eauto. }
  do 2 eexists; splits.
  2-3: eauto.
  right. eapply sb_trans; eauto.
Qed.

Lemma CsbI_rmw_fwcl (RMWCOV : forall r w, rmw r w -> C r <-> C w) :
  ⦗CsbI⦘ ⨾ rmw ≡ ⦗CsbI⦘ ⨾ rmw ⨾ ⦗CsbI⦘.
Proof.
  split; [|basic_solver].
  unfold CsbI.
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

Lemma CsbI_hb_prcl :
  dom_rel (hb ⨾ ⦗ CsbI ⦘) ⊆₁ CsbI.
Proof.
  unfold CsbI.
  rewrite <- seq_eqvK.
  sin_rewrite hb_in_Chb_sb; eauto.
  rewrite seq_union_l, dom_union.
  unionL; [|apply CsbI_sb_prcl].
  rewrite !seqA, !dom_seq.
  basic_solver.
Qed.

Lemma sc_hb_CsbI_in_C :
  dom_rel (sc ⨾ hb ⨾ ⦗CsbI⦘) ⊆₁ C.
Proof.
  arewrite (hb ⨾ ⦗CsbI⦘ ⊆ ⦗CsbI⦘ ⨾ hb).
  { generalize CsbI_hb_prcl. basic_solver. }
  unfold CsbI.
  rewrite <- seqA.
  erewrite scCsbI_C; eauto.
  basic_solver.
Qed.

Lemma hb_sc_hb_CsbI_alt :
  hb^? ⨾ sc^? ⨾ hb^? ⨾ ⦗CsbI⦘ ⊆
    (⦗C⦘ ⨾ hb^? ⨾ sc^? ⨾ hb^? ∪ sb)^?.
Proof.
  rewrite crE
    with (r := hb) at 1 2.
  rewrite crE
    with (r := sc) at 1.
  relsf.
  arewrite (hb ⨾ hb ⊆ hb).
  rewrite !unionA.
  apply union_mori.
  { basic_solver. }
  unionL.

  1,4,5 : unfold CsbI;
          rewrite hb_in_Chb_sb;
          eauto; basic_solver 10.

  { unfold CsbI.
    erewrite scCsbI_C; eauto.
    basic_solver 10. }

  { erewrite dom_rel_helper.
    2 : eapply sc_hb_CsbI_in_C; eauto.
    basic_solver 10. }

  { unfold CsbI.
    erewrite scCsbI_C; eauto.
    sin_rewrite hb_covered; eauto.
    basic_solver 10. }

  erewrite dom_rel_helper
    with (r := hb ⨾ ⦗CsbI⦘).
  2 : eapply CsbI_hb_prcl; eauto.
  arewrite
    (sc ⨾ ⦗CsbI⦘ ⊆ ⦗C⦘ ⨾ sc).
  { unfold CsbI at 1.
    erewrite scCsbI_C; eauto; done. }
  sin_rewrite hb_covered; eauto.
  basic_solver 10.
Qed.

(******************************************************************************)
(** ** D propeties *)
(******************************************************************************)

Lemma D_in_E : D ⊆₁ E.
Proof.
  unfold D.
  rewrite (wf_ppoE WF), (wf_rfiE WF), (wf_rfeE WF), (coveredE TCCOH).
  rewrite (issuedE TCCOH) at 1.
  basic_solver 21.
Qed.

Lemma D_R : D ∩₁ R ≡₁ C ∩₁ R ∪₁
  dom_rel (ppo ⨾ ⦗ I ⦘) ∪₁
  codom_rel (⦗I⦘ ⨾ rfi) ∪₁
  codom_rel (rfe ⨾ ⦗ R ∩₁ Acq ⦘).
Proof.
  unfold D.
  rewrite !set_inter_union_l.
  rewrite crE. relsf.
  arewrite
    (I ∩₁ R ≡₁ ∅).
  { split; [|done].
    rewrite issuedW; eauto.
    type_solver. }
  arewrite
    (dom_rel (rfi ⨾ ppo ⨾ ⦗I⦘) ∩₁ R ≡₁ ∅).
  { rewrite wf_rfiD; auto. type_solver. }
  rewrite wf_rfiD, wf_rfeD, wf_ppoD; auto.
  basic_solver 20.
Qed.

Lemma C_in_D : C ⊆₁ D.
Proof. unfold D. by repeat left. Qed.

Lemma I_in_D : I ⊆₁ D.
Proof. unfold D. do 3 left. by right. Qed.

Lemma CI_in_D : C ∪₁ I ⊆₁ D.
Proof. unfold D. by do 3 left. Qed.

Lemma rfi_D_in_D :
  dom_rel (rfi ⨾ ⦗ D ⦘) ⊆₁ D.
Proof.
  intros w [r RFI]. destruct_seq_r RFI as DR.
  apply wf_rfiD in RFI; auto. destruct_seq RFI as [WW RR].
  apply wf_rfiE in RFI; auto. destruct_seq RFI as [EW ER].
  red in DR. unfold set_union in DR. desf.
  { apply C_in_D. eapply dom_sb_covered; eauto.
    eexists. apply seq_eqv_r. split; eauto. apply RFI. }
  { eapply issuedW in DR; eauto. type_solver. }
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

Lemma rfe_D_CsbI_in_D :
  dom_rel (rfe ⨾ ⦗ D ∩₁ CsbI ⦘) ⊆₁ D.
Proof.
  intros w [r RFE]. destruct_seq_r RFE as DR.
  apply wf_rfeD in RFE; auto. destruct_seq RFE as [WW RR].
  apply wf_rfeE in RFE; auto. destruct_seq RFE as [EW ER].
  destruct DR as [DR CsbIr].
  assert (C r -> D w) as UU.
  { intros HH. apply I_in_D. eapply dom_rf_covered; eauto.
    eexists. apply seq_eqv_r. split; eauto. apply RFE. }
  destruct CsbIr as [EE0|EE0].
  { intuition. }

  red in DR. unfold set_union in DR. desf.
  { intuition. }
  { eapply issuedW in DR; eauto. type_solver. }
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

Lemma rf_D_CsbI_in_D :
  dom_rel (rf ⨾ ⦗ D ∩₁ CsbI ⦘) ⊆₁ D.
Proof.
  intros w [r RF]. destruct_seq_r RF as DR.
  apply rfi_union_rfe in RF. destruct RF as [RF|RF].
  { apply rfi_D_in_D; auto. eexists.
    apply seq_eqv_r; split; eauto. apply DR. }
  apply rfe_D_CsbI_in_D; auto. eexists.
  apply seq_eqv_r; split; eauto.
Qed.

(******************************************************************************)
(** ** vf propeties *)
(******************************************************************************)

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

Lemma vf_alt :
  vf ≡ ⦗ W ⦘ ⨾ (rf ⨾ ⦗ C ⦘)^? ⨾ hb^? ⨾ sc^? ⨾ hb^? ⨾ ⦗ E ⦘ ∪
        rf ⨾ ⦗ C ⦘ ⨾ sb^? ∪
        rf ⨾ ⦗ dom_rel (ppo ⨾ ⦗ I ⦘) ⦘ ⨾ sb^? ∪
        ⦗I⦘ ⨾ rfi ⨾ sb^? ∪
        rfe ⨾ ⦗ Acq ⦘ ⨾ sb^?.
Proof.
  unfold vf.
  rewrite !unionA.
  apply union_more; try done.
  rewrite <- !seqA, <- !unionA.
  rewrite <- !seq_union_l.
  apply seq_more; try done.
  arewrite (rf ⨾ ⦗D⦘ ≡ rf ⨾ ⦗D ∩₁ R⦘).
  { rewrite wf_rfD; auto. basic_solver. }
  rewrite D_R.
  rewrite !id_union, !seq_union_r.
  repeat apply union_more; try done.
  { rewrite wf_rfD; auto. basic_solver. }
  { rewrite seq_eqv_l, seq_eqv_r.
    unfolder; splits.
    { intros x y [RF [z [Iz RFI]]].
      arewrite (x = z); auto.
      eapply wf_rff; eauto.
      apply RFI. }
    intros x y [Ix RFI].
    split; [apply RFI|].
    exists x; splits; auto. }
  rewrite seq_eqv_r
    with (dom := R ∩₁ Acq).
  rewrite seq_eqv_r
    with (dom := Acq).
  rewrite seq_eqv_r.
  unfolder; splits.
  { intros x y [RF [z [RFE [Ry ACQy]]]].
    arewrite (x = z); auto.
    eapply wf_rff; eauto.
    apply RFE. }
  intros x y [RFE ACQy].
  split; [apply RFE|].
  exists x; splits; auto.
  apply wf_rfeD in RFE; auto.
  generalize RFE. basic_solver.
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

(******************************************************************************)
(** ** cert_rf propeties *)
(******************************************************************************)

Lemma cert_rfE : cert_rf ≡ ⦗E⦘ ⨾ cert_rf ⨾ ⦗E⦘.
Proof.
  cdes COH.
  apply dom_helper_3.
  unfold cert_rf.
  rewrite vfE.
  basic_solver.
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

Lemma cert_rf_codom : cert_rf ≡ cert_rf ⨾ ⦗CsbI⦘.
Proof. unfold cert_rf. basic_solver. Qed.

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

Lemma cert_rf_complete : forall b (IN: (CsbI ∩₁ R) b), exists a, cert_rf a b.
Proof.
  ins; unfolder in *; desc.
  assert (exists l, loc b = Some l); desc.
  { by generalize (is_r_loc lab); unfolder in *; basic_solver 12. }

  assert (E b) as UU.
  { by apply CsbI_in_E. }

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

Lemma cert_rf_in_vf : cert_rf ⊆ vf.
Proof. unfold cert_rf. basic_solver. Qed.

Lemma cert_rf_in_furr : cert_rf ⊆ furr.
Proof. rewrite cert_rf_in_vf. apply vf_in_furr. Qed.

Lemma cert_rf_hb_sc_hb_irr: irreflexive (cert_rf ⨾ hb ⨾ (sc ⨾ hb)^?).
Proof.
  rewrite cert_rf_in_furr.
  apply furr_hb_sc_hb_irr; auto.
  all: apply COH.
Qed.

Lemma cert_rf_hb_irr: irreflexive (cert_rf ⨾ hb).
Proof. generalize cert_rf_hb_sc_hb_irr. basic_solver 10. Qed.

Lemma cert_rf_tid_in_sb thread (NINITT : thread <> tid_init) :
  ⦗ Tid_ thread ⦘ ⨾ cert_rf ⨾ ⦗ Tid_ thread ⦘ ⊆ sb.
Proof.
  intros x y CertRF.
  destruct_seq CertRF as [TIDx TIDy].
  apply cert_rfE in CertRF; auto. destruct_seq CertRF as [EX EY].
  apply cert_rfD in CertRF. destruct_seq CertRF as [WX RY].
  edestruct same_thread
    with (x:=x) (y:=y) as [[|SB]|SB]; eauto.
  { intros INITx.
    assert (is_w lab y)
      as INITy; [|type_solver].
    apply init_w; auto.
    unfold tid, is_init in *.
    destruct x, y; auto; congruence. }
  { congruence. }
  { type_solver. }
  exfalso. eapply cert_rf_hb_sc_hb_irr; eauto.
  eexists. splits; eauto.
  eexists. splits.
  { eapply imm_s_hb.sb_in_hb; eauto. }
    by left.
Qed.

Lemma rf_D_in_vf : rf ⨾ ⦗D⦘ ⊆ vf.
Proof.
  rewrite (dom_l WF.(wf_rfD)).
  arewrite (D ⊆₁ D ∩₁ E).
  { generalize D_in_E. basic_solver. }
  unfold vf. basic_solver 20.
Qed.

Lemma rf_vf_in_cert_rf : (rf ⨾ ⦗CsbI⦘) ∩ vf ⊆ cert_rf.
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

Lemma rf_D_in_cert_rf : rf ⨾ ⦗ D ∩₁ CsbI ⦘ ⊆ cert_rf.
Proof.
  rewrite <- rf_vf_in_cert_rf.
  apply inclusion_inter_r.
  { basic_solver 10. }
  rewrite <- rf_D_in_vf. basic_solver.
Qed.

Lemma rf_C_in_cert_rf : rf ⨾ ⦗ C ⦘ ⊆ cert_rf.
Proof.
  rewrite <- rf_D_in_cert_rf.
  unfold D, CsbI.
  rewrite !set_inter_union_l,
          !id_union, !seq_union_r.
  basic_solver 10.
Qed.

Lemma rfi_in_cert_rf : rfi ⨾ ⦗ CsbI ⦘ ⊆ cert_rf.
Proof.
  unfold cert_rf. rewrite minus_inter_compl.
  apply inclusion_inter_r.
  { rewrite (dom_r WF.(wf_rfiD)).
    unfold Execution.rfi.
    rewrite <- seq_eqv_inter_lr
      with (r := vf).
    apply inclusion_inter_r.
    2: { rewrite WF.(wf_rfl). basic_solver. }
    unfold vf.
    rewrite seq_union_l.
    unionR left.
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
  rewrite cert_rf_codom, !seqA, <- id_inter.
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
  { unfold D, CsbI. basic_solver 10. }
  apply cert_rf_D_in_rf.
Qed.

Lemma cert_rf_D_eq_rf_D : cert_rf ⨾ ⦗ D ∩₁ CsbI ⦘ ≡ rf ⨾ ⦗ D ∩₁ CsbI ⦘.
Proof. generalize cert_rf_D_in_rf, rf_D_in_cert_rf. basic_solver 10. Qed.

Lemma cert_rf_Acq_in_rf : cert_rf ⨾ ⦗ Acq ⦘ ⊆ rf.
Proof.
  arewrite (cert_rf ⊆ cert_rf ⨾ ⦗ E ∩₁ R ⦘).
  { rewrite (dom_r cert_rfD), (dom_r cert_rfE) at 1.
    basic_solver. }
  cdes COH. red in Comp. rewrite Comp.
  rewrite rfi_union_rfe at 1.
  rewrite codom_union, id_union, !seq_union_l, !seq_union_r.
  unfold Execution.rfi.
  rewrite <- !id_inter.
  arewrite (codom_rel rfe ∩₁ Acq ⊆₁ D).
  { unfold D.
    rewrite WF.(wf_rfeD).
    basic_solver 10. }
  unionL.
  2: by apply cert_rf_D_in_rf.
  rewrite cert_rf_codom.
  unfolder. ins. desf.
  assert (x0 = x); desf.
  eapply cert_rff; eauto.
  apply rfi_in_cert_rf.
  apply seq_eqv_r.
  basic_solver.
Qed.

Lemma cert_rf_sb_F_Acq_in_rf :
  cert_rf ⨾ sb ⨾ ⦗F⦘ ⨾ ⦗ Acq ⦘ ⨾ ⦗CsbI⦘ ⊆ rf ⨾ sb.
Proof.
  arewrite (sb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘ ⨾ ⦗CsbI⦘ ⊆ ⦗C⦘ ⨾ sb).
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
  cert_rf ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗ Acq ⦘ ⨾ ⦗ CsbI ⦘ ⊆ rf ⨾ sb^?.
Proof.
  rewrite !crE, !seq_union_l, !seq_union_r, !seq_id_l, !seq_id_r, !seqA.
  apply union_mori.
  { sin_rewrite cert_rf_Acq_in_rf. basic_solver. }
  apply cert_rf_sb_F_Acq_in_rf.
Qed.

Lemma nI_rf_D_CsbI_in_sb :
  ⦗set_compl I⦘ ⨾ rf ⨾ ⦗D⦘ ⨾ ⦗CsbI⦘ ⊆ sb.
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
    { generalize (dom_rfe_ppo_issued WF TCCOH). basic_solver 20. }
    basic_solver. }
  { arewrite (rf ⨾ ⦗codom_rel (⦗I⦘ ⨾ rfi)⦘ ⊆ sb).
    2: { generalize (@sb_trans G). basic_solver. }
    unfolder; ins; desf.
    match goal with H : rfi _ _ |- _ => destruct H as [AA BB] end.
    eapply wf_rff in H; eauto.
    apply H in AA. by rewrite AA. }
  unfold CsbI.
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

Lemma non_I_cert_rf: ⦗set_compl I⦘ ⨾ cert_rf ⊆ sb.
Proof.
  cdes COH.
  rewrite (dom_r (cert_rfD)).
  rewrite cert_rf_codom.
  rewrite cert_rf_in_vf.
  unfold vf.
  arewrite_id (⦗E⦘).
  relsf. rewrite !seqA. unionL.

  { rewrite !crE.
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
    1-3: unfold CsbI; sin_rewrite hb_in_Chb_sb; eauto.
    1-3: rewrite !seq_union_r; seq_rewrite <- !id_inter.
    1-3: rewrite set_interA; erewrite w_covered_issued; eauto.
    1-3: basic_solver.
    arewrite (sc ⨾ hb ⨾ ⦗CsbI⦘ ⊆ ⦗C⦘ ⨾ sc ⨾ hb).
    { generalize sc_hb_CsbI_in_C. basic_solver 10. }
    sin_rewrite hb_covered; eauto.
    rewrite !seqA. seq_rewrite <- !id_inter.
    rewrite set_interA; erewrite w_covered_issued; eauto.
    basic_solver. }

  arewrite_id (⦗R⦘); seq_rewrite seq_id_r.
  arewrite (sb^? ⨾ ⦗CsbI⦘ ⊆ ⦗CsbI⦘ ⨾ sb^?).
  { rewrite crE. relsf.
    apply union_mori; try done.
    generalize CsbI_sb_prcl. basic_solver. }
  sin_rewrite nI_rf_D_CsbI_in_sb.
  generalize sb_trans. basic_solver.
Qed.

Lemma cert_rf_iss_sb :
  cert_rf ⊆ ⦗ I ⦘ ⨾ cert_rf ∪ sb ∩ same_tid.
Proof.
  rewrite <- seq_id_l
    with (r := cert_rf) at 1.
  rewrite <- set_compl_union_id
    with (s := I).
  rewrite id_union, seq_union_l.
  apply union_mori; try done.
  rewrite seq_eqv_l.
  intros x y [nI CertRF].
  assert (sb x y) as SB.
  { apply non_I_cert_rf. basic_solver. }
  split; auto.
  apply sb_tid_init in SB.
  destruct SB as [TID | INITx]; auto.
  exfalso. apply nI.
  eapply init_issued; eauto.
  split; auto.
  apply cert_rfE in CertRF.
  by destruct_seq CertRF as [AA BB].
Qed.

Lemma cert_rf_ntid_iss_sb thread (NINITT : thread <> tid_init) :
  cert_rf ⨾ ⦗ Tid_ thread ⦘ ⊆
    ⦗ NTid_ thread ∩₁ I ⦘ ⨾ cert_rf ∪ sb ∩ same_tid.
Proof.
  rewrite <- seq_id_l
    with (r := cert_rf) at 1.
  rewrite <- tid_set_dec with (thread := thread).
  rewrite set_unionC, id_union, !seq_union_l, !seqA.
  apply union_mori.
  { rewrite cert_rf_iss_sb at 1.
    unfold same_tid.
    basic_solver 10. }
  apply inclusion_inter_r.
  { apply cert_rf_tid_in_sb; auto. }
  unfold same_tid.
  basic_solver.
Qed.

Lemma dom_cert_rfe :
  dom_rel cert_rfe ⊆₁ I.
Proof.
  unfold cert_rfe.
  rewrite cert_rf_iss_sb.
  basic_solver.
Qed.

End Properties.

End CertRf.

Section CertRfLemmas.
Variable G  : execution.
Variable sc : relation actid.
Variable WF  : Wf G.
Variable COH : imm_consistent G sc.

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

Lemma sim_trav_step_CsbI_mon TC TC'
      (TCOH : tc_coherent G sc TC)
      (TRAV_STEP : sim_trav_step G sc TC TC') :
  CsbI G TC ⊆₁ CsbI G TC'.
Proof.
  unfold CsbI.
  rewrite sim_trav_step_covered_le; eauto.
  rewrite sim_trav_step_issued_le; eauto.
Qed.

Lemma sim_trav_step_D_mon TC TC'
      (TCOH : tc_coherent G sc TC)
      (TRAV_STEP : sim_trav_step G sc TC TC') :
  D G TC ⊆₁ D G TC'.
Proof.
  unfold D.
  rewrite sim_trav_step_covered_le; eauto.
  rewrite sim_trav_step_issued_le; eauto.
Qed.

Lemma sim_trav_step_vf_mon TC TC'
      (TCOH : tc_coherent G sc TC)
      (TRAV_STEP : sim_trav_step G sc TC TC') :
  vf G sc TC ⊆ vf G sc TC'.
Proof.
  unfold vf.
  rewrite sim_trav_step_covered_le; eauto.
  rewrite sim_trav_step_D_mon; eauto.
  done.
Qed.

Lemma sim_trav_step_cert_rf_co TC TC'
      (TCOH : tc_coherent G sc TC)
      (TRAV_STEP : sim_trav_step G sc TC TC') :
  cert_rf G sc TC ⨾ (cert_rf G sc TC')⁻¹ ⊆ co^?.
Proof.
  intros x y [z [CertRF CertRF']].
  red in CertRF'.
  destruct (classic (x = y))
    as [EQ|nEQ].
  { basic_solver. }
  edestruct wf_co_total
    as [CO|CO]; eauto.
  { unfolder. splits.
    { apply cert_rfE in CertRF; auto.
      generalize CertRF. basic_solver. }
    { apply cert_rfD in CertRF; auto.
      generalize CertRF. basic_solver. }
    edone. }
  { unfolder. splits.
    { apply cert_rfE in CertRF'; auto.
      generalize CertRF'. basic_solver. }
    { apply cert_rfD in CertRF'; auto.
      generalize CertRF'. basic_solver. }
    symmetry.
    apply cert_rfl in CertRF.
    apply cert_rfl in CertRF'.
    congruence. }
  exfalso.
  unfold cert_rf in *.
  apply CertRF'.
  exists x; splits; auto.
  eapply sim_trav_step_vf_mon; eauto.
  generalize CertRF. basic_solver.
Qed.

Lemma isim_trav_step_vf_ntid thread TC TC'
      (NINITT : thread <> tid_init)
      (TCOH : tc_coherent G sc TC)
      (RELCOH : W ∩₁ Rel ∩₁ (issued TC) ⊆₁ covered TC)
      (ITRAV_STEP : isim_trav_step G sc thread TC TC') :
  vf G sc TC' ⨾ ⦗CsbI G TC ∩₁ NTid_ thread⦘ ⊆ vf G sc TC.
Proof.
  assert (sim_trav_step G sc TC TC')
    as TRAV_STEP.
  { eexists; edone. }
  assert (tc_coherent G sc TC')
    as TCCOH'.
  { eapply sim_trav_step_coherence; eauto. }
  assert (W ∩₁ Rel ∩₁ issued TC' ⊆₁ covered TC')
    as RELCOH'.
  { eapply sim_trav_step_rel_covered; eauto. }
  rewrite !vf_alt; eauto.
  rewrite !seq_union_l.

  rewrite !seqA.
  arewrite
    (sb^? ⨾ ⦗CsbI G TC ∩₁ NTid_ thread⦘ ⊆ ⦗CsbI G TC ∩₁ NTid_ thread⦘ ⨾ sb^?).
  { rewrite !crE. relsf.
    apply union_mori; try done.
    rewrite seq_eqv_l, seq_eqv_r.
    intros x y [SB [CsbIy nTIDy]].
    unfolder; splits; auto.
    { eapply CsbI_sb_prcl; eauto. basic_solver 10. }
    intros TIDx.
    apply sb_tid_init in SB.
    destruct SB as [EQtid | INITx].
    { congruence. }
    apply is_init_tid in INITx.
    congruence. }

  repeat apply union_mori.

  { rewrite crE
      with (r := rf ⨾ ⦗covered TC'⦘).
    relsf. unionL.
    { basic_solver 20. }
    rewrite !seqA.
    arewrite
      (⦗E⦘ ⨾ ⦗CsbI G TC ∩₁ NTid_ thread⦘ ⊆
       ⦗CsbI G TC⦘ ⨾ ⦗NTid_ thread⦘ ⨾ ⦗E⦘).
    { basic_solver. }
    arewrite
      (hb^? ⨾ sc^? ⨾ hb^? ⨾ ⦗CsbI G TC⦘ ⊆
       (⦗covered TC⦘ ⨾ hb^? ⨾ sc^? ⨾ hb^? ∪ sb)^?).
    { eapply hb_sc_hb_CsbI_alt; auto. }
    rewrite crE. relsf. unionL.
    { erewrite isim_trav_step_new_covered_tid;
        eauto.
      basic_solver 20. }
    { basic_solver 20. }
    arewrite
      (sb ⨾ ⦗NTid_ thread⦘ ⊆ ⦗NTid_ thread⦘ ⨾ sb).
    { rewrite seq_eqv_r, seq_eqv_l.
      intros x y [SB nTIDy].
      split; auto.
      apply sb_tid_init in SB.
      destruct SB as [EQtid | INITx].
      { congruence. }
      apply is_init_tid in INITx.
      congruence. }
    erewrite isim_trav_step_new_covered_tid;
      eauto.
    rewrite sb_in_hb.
    basic_solver 20. }

  { erewrite isim_trav_step_new_covered_tid;
      eauto.
    basic_solver 10. }

  { seq_rewrite !seq_eqv_r.
    intros x y [z [HH SB']].
    destruct HH as [HH [CsbIz nTIDz]].
    destruct HH as [RF [z' [PPO Iy']]].
    do 2 (eexists; splits; eauto).
    (* TODO: introduce lemma `I' ∩ Ntid thread ⊆ I` *)
    eapply isim_trav_step_new_issued_tid in Iy'; eauto.
    destruct Iy' as [[Iy _] | [Iy' TIDy]]; auto.
    assert (SB := PPO).
    apply ppo_in_sb in SB; auto.
    apply sb_tid_init in SB.
    destruct SB as [EQtid | INITx].
    { congruence. }
    eapply init_w in INITx; eauto.
    apply wf_ppoD in PPO.
    exfalso.
    generalize PPO.
    type_solver. }

  { arewrite
      (rfi ⨾ ⦗CsbI G TC ∩₁ NTid_ thread⦘ ⊆ ⦗CsbI G TC ∩₁ NTid_ thread⦘ ⨾ rfi).
    { rewrite seq_eqv_l, seq_eqv_r.
      intros x y [RFI [CsbIy nTIDy]].
      assert (sb x y) as SB.
      { apply RFI. }
      unfolder; splits; auto.
      { eapply CsbI_sb_prcl; eauto. basic_solver 10. }
      intros TIDx.
      apply sb_tid_init in SB.
      destruct SB as [EQtid | INITx].
      { congruence. }
      apply is_init_tid in INITx.
      congruence. }
    erewrite isim_trav_step_new_issued_tid;
      eauto.
    basic_solver 10. }

  basic_solver 10.

Qed.

Lemma isim_trav_step_cert_rf_ntid thread TC TC'
      (NINITT : thread <> tid_init)
      (TCOH : tc_coherent G sc TC)
      (RELCOH : W ∩₁ Rel ∩₁ (issued TC) ⊆₁ covered TC)
      (ITRAV_STEP : isim_trav_step G sc thread TC TC') :
  cert_rf G sc TC ⨾ ⦗NTid_ thread⦘ ⊆ cert_rf G sc TC'.
Proof.
  assert (sim_trav_step G sc TC TC')
    as TRAV_STEP.
  { eexists; edone. }
  unfold cert_rf.
  rewrite !seq_eqv_r
    with (dom := CsbI G TC ∩₁ R).
  rewrite !seq_eqv_r.
  intros x y [CertRF nTIDy].
  destruct CertRF as [VF nCOVF].
  destruct VF as [[VF EQloc] [CsbIy Ry]].
  unfolder; splits; auto.
  { eapply sim_trav_step_vf_mon; eauto. }
  { eapply sim_trav_step_CsbI_mon; eauto. }
  intros [z [CO VF']].
  apply nCOVF.
  exists z; splits; auto.
  eapply isim_trav_step_vf_ntid; eauto.
  basic_solver.
Qed.

End CertRfLemmas.
