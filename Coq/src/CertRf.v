Require Import Program.Basics.
From hahn Require Import Hahn.
From imm Require Import Events Execution TraversalConfig
     imm_common imm_s imm_s_hb CertExecution1 CertExecution2 AuxRel
     CombRelations Execution_eco.
Require Import Vf AuxRel.

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

Notation "'sb'" := (G.(sb)).
Notation "'sw'" := (G.(imm_s_hb.sw)).
Notation "'hb'" := (G.(imm_s_hb.hb)).
Notation "'rf'" := (G.(rf)).
Notation "'co'" := (G.(co)).
Notation "'loc'" := (loc lab).

Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).
Notation "'R_' l" := (R ∩₁ Loc_ l) (at level 1).

Notation "'furr'" := (furr G sc).

Definition E0 := (Tid_ thread ∩₁ (C ∪₁ dom_rel (sb^? ⨾ ⦗ I ⦘))).
Definition vf := ⦗ W ⦘ ⨾ (rf ⨾ ⦗ D ⦘)^? ⨾ hb^? ⨾
                    sc^? ⨾ hb^? ⨾ ⦗ E ⦘.

Definition cert_rf :=
  vf ∩ same_loc lab ⨾ ⦗ E0 ∩₁ R ⦘ \ co ⨾ vf.
Definition cert_rfi := ⦗  Tid_ thread ⦘ ⨾ cert_rf ⨾ ⦗ Tid_ thread ⦘.
Definition cert_rfe := ⦗ NTid_ thread ⦘ ⨾ cert_rf ⨾ ⦗ Tid_ thread ⦘.

Section Properties.
Variable WF  : Wf G.
Variable COH : imm_consistent G sc.
Variable TCCOH : tc_coherent G sc TC.
Variable RELCOH : W ∩₁ Rel ∩₁ I ⊆₁ C.

Lemma vfE : vf ≡ ⦗ E ⦘ ⨾ vf ⨾ ⦗ E ⦘.
Proof.
  apply dom_helper_3.
  unfold vf.
  rewrite (dom_l WF.(wf_rfE)).
  rewrite (dom_l WF.(wf_hbE)).
  cdes COH.
  rewrite (dom_l (wf_scE Wf_sc)).
  basic_solver.
Qed.

Lemma vf_dom : vf ≡ ⦗ W ⦘ ⨾ vf.
Proof.
  split; [|basic_solver].
    by unfold vf; seq_rewrite seq_eqvK.
Qed.

Lemma E0_in_E : E0 ⊆₁ E.
Proof.
  unfold E0.
  rewrite coveredE, issuedE; try edone.
  rewrite (dom_l (@wf_sbE G)).
  basic_solver.
Qed.

Lemma vf_in_furr : vf ⊆ furr.
Proof.
  cdes COH.
  unfold vf.
  arewrite_id ⦗D⦘. arewrite_id ⦗E⦘. rewrite !seq_id_r.
    by rewrite furr_alt; auto.
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

Lemma cert_rf_codom : cert_rf ≡ cert_rf ⨾ ⦗ E0 ⦘.
Proof.
  unfold cert_rf.
  rewrite AuxRel.seq_eqv_minus_lr.
  rewrite seqA.
  rewrite <- id_inter.
  arewrite (E0 ∩₁ R ∩₁ E0 ≡₁ E0 ∩₁ R).
  2: done.
  basic_solver 20.
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

Lemma cert_rf_comp : forall b (IN: (E0 ∩₁ R) b), exists a, cert_rf a b.
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
  { red.
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
    apply cert_rf_comp in HH.
    desc. eexists. eauto. }
  rewrite (dom_r cert_rfD).
  rewrite cert_rf_codom.
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

Lemma rf_D_in_vf : rf ⨾ ⦗D⦘ ⊆ vf.
Proof.
  rewrite (dom_l WF.(wf_rfD)).
  arewrite (D ⊆₁ D ∩₁ E).
  { generalize (@D_in_E G sc TC thread WF TCCOH). 
    basic_solver. }
  unfold vf. basic_solver 20.
Qed.

Lemma cert_rf_D_rf : cert_rf ⨾ ⦗ D ⦘ ⊆ rf.
Proof.
  unfold cert_rf.
  arewrite (E0 ∩₁ R ⊆₁ R) by basic_solver.
  unfolder. ins. desf.
  assert ((E ∩₁ R) y) as HH.
  { split; auto.
    eapply D_in_E; eauto. }
  cdes COH. edestruct Comp as [z RF]; eauto.
  destruct (classic (x = z)) as [EQ|NEQ].
  { by rewrite EQ. }
  exfalso.
  set (AA := RF).
  apply WF.(wf_rfl) in AA.
  assert (exists l, loc y = Some l) as [l BB].
  { unfold Events.loc, is_r in *. desf; eauto. }
  edestruct WF.(wf_co_total); eauto.
  { red. split.
    2: { rewrite H5. eauto. }
    split.
    { apply (dom_l vfE) in H. apply seq_eqv_l in H. desf. }
    apply vf_dom in H. apply seq_eqv_l in H. desf. }
  { red. split.
    2: { rewrite AA. eauto. }
    split.
    { apply (dom_l WF.(wf_rfE)) in RF. apply seq_eqv_l in RF. desf. }
    apply (dom_l WF.(wf_rfD)) in RF. apply seq_eqv_l in RF. desf. }
  { apply H2. eexists. split; eauto.
    apply rf_D_in_vf. apply seq_eqv_r. split; auto.
    red. desf. }
  clear -RF H3 H Csc Cint HH NEQ WF Wf_sc.
  red in H. unfolder in *. desf.
  { type_solver. }
  { apply NEQ. eapply wf_rff; eauto. }
  all: try by (eapply Cint; eexists; split; eauto; right;
               apply fr_in_eco; eexists; eauto).
  all: try (apply (dom_r Wf_sc.(wf_scD)) in H2;
    apply seq_eqv_r in H2; type_solver).
  all: try by (eapply Cint; eexists; split; eauto; right;
               red; right; eexists; split; [eexists|right]; eauto).
  { eapply Cint; eexists; split.
    2: { right. apply fr_in_eco. eexists; eauto. }
    eapply hb_trans; eauto. }
  { eapply Cint; eexists; split.
    2: { right. red. right.
         eexists. split; [eexists|right]; eauto. }
    eapply hb_trans; eauto. }
  { apply (dom_l Wf_sc.(wf_scD)) in H2.
    apply seq_eqv_l in H2.
    apply (dom_r WF.(wf_coD)) in H3.
    apply seq_eqv_r in H3.
    type_solver. }
  { apply (dom_l Wf_sc.(wf_scD)) in H2.
    apply seq_eqv_l in H2.
    apply (dom_r WF.(wf_rfD)) in H0.
    apply seq_eqv_r in H0.
    type_solver. }
  { eapply Csc. eexists. split; eauto.
    eexists. split; eauto. right.
    eexists. split; eauto.
    apply fr_in_eco. eexists; eauto. }
  eapply Csc. eexists. split; eauto.
  eexists. split; eauto. right.
  eexists. split; eauto.
  red. right. 
  eexists. split; [eexists|right]; eauto.
Qed.

(* TODO: move to a more general file.*)
Lemma dom_r2l_rt {A} (r r' : relation A) (s : A -> Prop)
      (HH : r ⨾ ⦗s⦘ ⊆ ⦗s⦘ ⨾ r') :
  r＊ ⨾ ⦗s⦘ ⊆ ⦗s⦘ ⨾ r'＊.
Proof.
  unfolder in *. ins. desf.
  induction H.
  { edestruct HH; eauto. split; auto.
      by apply rt_step. }
  { split; auto. apply rt_refl. }
  destruct IHclos_refl_trans2; auto.
  destruct IHclos_refl_trans1; auto.
  split; auto.
  eapply transitive_rt; eauto.
Qed.

(* TODO: move to a more general file.*)
Lemma sw_sb_I_dom_C: dom_rel (sw ⨾ sb ⨾ ⦗I⦘) ⊆₁ C.
Proof.
  (* unfold imm_s_hb.sw, release, rs. unfolder. *)
  (* (* unfold imm_s_hb.sw. unfolder. *) *)
  (* ins. desf. *)
  (* { apply rfi_union_rfe in H0. red in H0. desf. *)
  (*   { *)
Admitted.

(* TODO: move to a more general file.*)
Lemma sc_sb_I_dom_C: dom_rel (sc ⨾ sb ⨾ ⦗I⦘) ⊆₁ C.
Proof.
  cdes COH.
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

Lemma non_I_cert_rf: ⦗set_compl I⦘ ⨾ cert_rf ⊆ sb.
Proof.
  cdes COH.
  rewrite cert_rf_codom. rewrite (dom_r cert_rfD).
  rewrite cert_rf_in_vf. rewrite !seqA.
  unfold vf.
  arewrite_id ⦗E⦘. rewrite seq_id_l.
  arewrite (E0 ⊆₁ C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)).
  { unfold E0. basic_solver 10. }
  rewrite id_union. rewrite !seq_union_r.
  assert (hb^? ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ hb^? /\ sc^? ⨾ ⦗C⦘ ⊆ ⦗C⦘ ⨾ sc^?) as [AA BB].
  { split.
    all: rewrite crE; relsf; apply inclusion_union_mon; [done|].
    { eapply hb_covered; eauto. }
    eapply sc_covered; eauto. }
  assert (⦗set_compl I⦘ ⨾ ⦗W⦘ ⨾ (rf ⨾ ⦗D⦘)^? ⨾ ⦗C⦘ ⊆ ∅₂) as QQ.
  { arewrite_id ⦗D⦘.
    rewrite crE. relsf.
    unionL.
    { generalize (w_covered_issued TCCOH).
      basic_solver. }
    rewrite rf_covered; eauto. basic_solver. }
  assert (⦗set_compl I⦘ ⨾ ⦗W⦘ ⨾ (rf ⨾ ⦗D⦘)^? ⨾ hb^? ⨾ ⦗C⦘ ⊆ ∅₂) as YY.
  { sin_rewrite AA. sin_rewrite QQ. basic_solver. }
  assert (⦗set_compl I⦘ ⨾ ⦗W⦘ ⨾ (rf ⨾ ⦗D⦘)^? ⨾ hb^? ⨾ sc^? ⨾ ⦗C⦘ ⊆ ∅₂) as CC.
  { sin_rewrite BB. sin_rewrite YY. basic_solver. }
  unionL.
  { arewrite_id ⦗R⦘. rewrite seq_id_l.
    sin_rewrite AA. sin_rewrite CC. basic_solver. }

  rewrite seq_eqvC with (doma:=R).
  cdes TCCOH.
  
  assert (sw ⨾ sb^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆
          ⦗C⦘ ⨾ sw ⨾ sb^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘) as JJ.
  { intros x y TT. apply seq_eqv_l. split; auto.
    unfolder in TT. desf.
    { apply (dom_r WF.(wf_swD)) in TT. apply seq_eqv_r in TT.
      eapply issuedW in TT3; eauto. type_solver. }
    all: apply sw_sb_I_dom_C.
    all: eexists; eexists.
    all: split; eauto.
    all: apply seq_eqv_r; split; [|by eauto]; eauto.
    eapply sb_trans; eauto. }
    
  assert ((sb ⨾ sw＊)＊ ⨾ sb ⨾ sw＊ ⊆ hb) as VV.
  { rewrite <- ct_end. rewrite sb_in_hb, sw_in_hb.
    rewrite <- ct_begin. rewrite ct_of_ct.
    apply ct_of_trans. apply hb_trans. }

  assert (hb^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆
          ⦗ C ⦘ ⨾ hb^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ∪
            sb^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘) as PP.
  { arewrite (hb^? ⊆ ⦗ C ∪₁ set_compl C ⦘ ⨾ hb^?) at 1. 
    { rewrite set_compl_union_id. by rewrite seq_id_l. }
    rewrite id_union, seq_union_l.
    apply union_mori; [done|].
    unfold imm_s_hb.hb.
    rewrite cr_of_ct.
    rewrite unionC.
    rewrite path_ut.
    2: by apply sb_trans.
    rewrite !seqA.
    rewrite !rtE.
    rewrite !seq_union_l, !seq_union_r.
    rewrite !seq_id_l.
    unionL.
    { arewrite_id ⦗set_compl C⦘. by rewrite seq_id_l. }
    { rewrite ct_end, !seqA.
      rewrite ct_end at 2. rewrite !seqA.
      rewrite JJ.
      rewrite inclusion_t_rt.
      sin_rewrite VV.
      sin_rewrite hb_covered; eauto.
      rewrite !seqA.
      arewrite (⦗set_compl C⦘ ⨾ ⦗C⦘ ⊆ ∅₂); basic_solver. }
    { rewrite ct_end, !seqA.
      rewrite JJ.
      sin_rewrite dom_r2l_rt.
      2: by eapply sw_covered; eauto.
      rewrite !seqA.
      arewrite (⦗set_compl C⦘ ⨾ ⦗C⦘ ⊆ ∅₂); basic_solver. }
    rewrite ct_end with (r := sb ⨾ sw⁺).
    rewrite ct_end at 3. rewrite !seqA.
    rewrite JJ.
    rewrite inclusion_t_rt.
    sin_rewrite VV.
    sin_rewrite hb_covered; eauto. rewrite !seqA.
    sin_rewrite dom_r2l_rt.
    2: by eapply sw_covered; eauto.
    rewrite !seqA.
    arewrite (⦗set_compl C⦘ ⨾ ⦗C⦘ ⊆ ∅₂); basic_solver. }
      
  sin_rewrite PP.
  rewrite !seq_union_l, !seq_union_r, !seqA.
  unionL.
  { sin_rewrite CC. basic_solver. }
  assert (sb^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆
          ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⨾ sb^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘) as XX.
  { generalize (@sb_trans G). basic_solver 20. }
  sin_rewrite XX.
  arewrite (sb^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆ sb^?).
  arewrite (sc^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆
            ⦗ C ⦘ ⨾ sc ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ∪ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘).
  { rewrite crE. rewrite unionC, !seq_union_l.
    apply union_mori.
    2: by rewrite seq_id_l.
    intros x y HH. apply seq_eqv_l. split; auto.
    unfolder in HH. desf.
    2: { apply sc_sb_I_dom_C. unfolder. eauto 10. } 
    apply (dom_r Wf_sc.(wf_scD)) in HH. apply seq_eqv_r in HH.
    eapply issuedW in HH2; eauto.
    type_solver. }

  rewrite !seq_union_l, !seq_union_r, !seqA.
  unionL.
  { sin_rewrite YY. basic_solver. }
  sin_rewrite PP.
  rewrite !seq_union_l, !seq_union_r, !seqA.
  unionL.
  { sin_rewrite QQ. basic_solver. }
  
  rewrite crE at 1.
  rewrite !seq_union_l, !seq_union_r, !seq_id_l, !seqA.
  unionL.
  { rewrite !crE.
    rewrite !seq_union_l, !seq_union_r, !seq_id_l.
    unionL.
    { type_solver. }
    2,3: generalize (@sb_trans G).
    all: basic_solver. }
  arewrite (⦗set_compl I⦘ ⨾ ⦗W⦘ ⨾ rf ⨾ ⦗D⦘ ⨾ sb^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆ sb).
  2: { generalize (@sb_trans G). basic_solver. }
  
  (* Proving ⦗set_compl I⦘ ⨾ ⦗W⦘ ⨾ rf ⨾ ⦗D⦘ ⨾ sb^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆ sb *)
  unfold CertExecution2.D.
  relsf.
  rewrite !id_union.
  rewrite !seq_union_l, !seq_union_r.
  unionL.
  { arewrite (Tid_ thread ∩₁ C ⊆₁ C).
    { basic_solver. }
    arewrite (rf ⨾ ⦗C⦘ ⊆ ⦗I⦘ ⨾ rf ⨾ ⦗C⦘).
    { eapply rf_covered; eauto. }
    basic_solver. }
  { rewrite (dom_r WF.(wf_rfD)), !seqA.
    arewrite (⦗R⦘ ⨾ ⦗Tid_ thread ∩₁ I⦘ ⊆ ∅₂).
    2: basic_solver.
    arewrite (I ⊆₁ W).
    2: type_solver.
    eapply issuedW; eauto. }
  { basic_solver. }
  { rewrite rfi_union_rfe.
    rewrite !seq_union_l, !seq_union_r.
    unionL.
    { generalize (@sb_trans G). unfold Execution.rfi. basic_solver. }
    arewrite (rfe G ⨾ ⦗Tid_ thread ∩₁ dom_rel ((rfi G)^? ⨾ imm_common.ppo G ⨾ ⦗I⦘)⦘ ⊆
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
  { arewrite (rf ⨾ ⦗Tid_ thread ∩₁ codom_rel (⦗I⦘ ⨾ rfi G)⦘ ⊆ sb).
    2: { generalize (@sb_trans G). basic_solver. }
    unfolder; ins; desf.
    destruct H2.
    eapply wf_rff in H; eauto.
    apply H in H0. desf. }
  unfolder; ins; desf.
  { apply (dom_r WF.(wf_rfeD)) in H6.
    eapply issuedW in H5; eauto.
    type_solver. }
  { exfalso. apply H.
    eapply dom_rfe_acq_sb_issued; eauto.
    eexists. exists z. split.
    { assert (x0 = x); desf.
      eapply WF.(wf_rff); eauto.
      apply H6. }
    eexists. split.
    { split; eauto. by split. }
    apply seq_eqv_r. eauto. }
  { exfalso. apply H.
    eapply dom_rfe_acq_sb_issued; eauto.
    eexists. exists y. split.
    { assert (x0 = x); desf.
      eapply WF.(wf_rff); eauto.
      apply H6. }
    eexists. split.
    { split; eauto. by split. }
    apply seq_eqv_r. eauto. }
  exfalso. apply H.
  eapply dom_rfe_acq_sb_issued; eauto.
  eexists. exists z. split.
  { assert (x0 = x); desf.
    eapply WF.(wf_rff); eauto.
    apply H6. }
  eexists. split.
  { split; eauto. by split. }
  apply seq_eqv_r. split; [|by eauto].
  eapply sb_trans; eauto.
Qed.

  (* rewrite (cert_rfD). *)
  (* arewrite (⦗E0 \₁ I⦘ ⨾ ⦗W⦘ ⊆ ⦗E0 \₁ I⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗W⦘). *)
  (* { by revert IT_new_co; unfolder; firstorder. } *)
  (* rewrite (cert_rfE). *)
  (* arewrite (E \₁ D ⊆₁ E ∩₁ Tid_ thread). *)
  (* { by unfold D; unfolder; ins; desf; tauto. } *)
  (* unfolder; ins; desf. *)
  (* eapply (@same_thread G) in H3; desf. *)
  (* destruct H3; [subst x; type_solver|]. *)
  (* 2: by intro K; apply (init_w WF) in K; type_solver. *)
  (* exfalso; generalize cert_rf_hb. *)
  (* generalize (@sb_in_hb G); basic_solver 12. *)
(* Qed. *)

(* Lemma cert_rfe_Acq : (cert_rf \ Gsb) ⨾ ⦗R∩₁Acq⦘ ⊆ ∅₂. *)
(* Proof. *)
(*   rewrite cert_rfE. *)
(*   arewrite (⦗E⦘ ⊆ ⦗E \₁ I⦘ ∪ ⦗E ∩₁ I⦘). *)
(*   unfolder; ins; desf; tauto. *)
(*   relsf. *)
(*   rewrite minus_union_l. *)
(*   relsf; unionL. *)
(*   sin_rewrite non_I_cert_rf. *)
(*   basic_solver. *)
(*   rewrite cert_rfD. *)
(*   arewrite (cert_rf ⊆ cert_rf ∩ Gsame_loc). *)
(*   generalize (cert_rfl); basic_solver. *)

(*   unfolder; ins; desf. *)

(*   assert (Lx:exists l, Gloc x = Some l); desc. *)
(*     by apply is_w_loc. *)

(*     assert (Ly:Gloc y = Some l). *)
(*     unfold same_loc in *; congruence. *)

(*     forward (apply COMP_ACQ). *)
(*       by basic_solver. *)

(*       ins; desc. *)

(*       apply rfi_union_rfe in H10; unfolder in H10; desf; cycle 1. *)
(*         by generalize R_Acq_codom_rfe; basic_solver 12. *)

(*         ie_unfolder; unfolder in H10; desf. *)

(*         hahn_rewrite (wf_rfD WF) in H10. *)
(*         hahn_rewrite (wf_rfE WF) in H10. *)

(*         unfolder in H10; desf. *)

(*         assert (Lz:Gloc z = Some l). *)
(*           by apply (wf_rfl WF) in H14; unfold same_loc in *; congruence. *)

(*           forward (apply ((wf_co_total WF) (Some l) z)). *)
(*           basic_solver. *)
(*           instantiate (1 := x). *)
(*           basic_solver. *)

(*           intro; desf. *)

(*           intro; desf. *)

(*   - *)
(*     eapply eco_furr_irr; try edone. *)
(*     eexists; splits; [|eby apply cert_rf_in_furr]. *)
(*     unfold eco, fr. *)
(*     basic_solver 12. *)
(*   - eapply H3. *)
(*     exists z; split; [| apply furr_alt; basic_solver 12]. *)
(*     apply I_co_in_cert_co; basic_solver. *)
(* Qed. *)

End Properties.

End CertRf.