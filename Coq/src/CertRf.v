Require Import Program.Basics.
From hahn Require Import Hahn.
From imm Require Import Events Execution TraversalConfig
     imm imm_hb CertExecution2 AuxRel.
Require Import Vf.

Section CertRf.
Variable G  : execution.
Variable sc : relation actid.
Variable TC : trav_config.
Variable thread : thread_id.

Notation "'C'"  := (covered TC).
Notation "'I'"  := (issued TC).

Notation "'D'" := (D G TC thread).

Notation "'E'"  := G.(acts_set).
Notation "'lab'" := (G.(lab)).
Notation "'rmw'" := G.(rmw).

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).

Notation "'sb'" := (G.(sb)).
Notation "'hb'" := (G.(imm_hb.hb)).
Notation "'psc'" := (G.(imm.psc)).
Notation "'rf'" := (G.(rf)).
Notation "'co'" := (G.(co)).
Notation "'loc'" := (loc lab).

Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).
Notation "'R_' l" := (R ∩₁ Loc_ l) (at level 1).

Notation "'E0'" := (Tid_ thread ∩₁ (C ∪₁ dom_rel (sb^? ⨾ ⦗ I ⦘))).
Notation "'vf'" := (Avf E lab (rf ;; <| D |>) hb psc).

Definition cert_rf :=
  vf ∩ same_loc lab ⨾ ⦗ (E0 \₁ D) ∩₁ R ⦘ \ co ⨾ vf.
Definition cert_rfi := ⦗  Tid_ thread ⦘ ⨾ cert_rf ⨾ ⦗ Tid_ thread ⦘.
Definition cert_rfe := ⦗ NTid_ thread ⦘ ⨾ cert_rf ⨾ ⦗ Tid_ thread ⦘.

Section Properties.
Variable WF  : Wf G.
Variable COH : imm_consistent G.
Variable TCCOH : tc_coherent G sc TC.
  
Lemma cert_rfE : cert_rf ≡ ⦗E⦘ ⨾ cert_rf ⨾ ⦗E⦘.
Proof.
  apply dom_helper_3.
  unfold cert_rf.
  rewrite AvfE.
  { basic_solver 21. }
  { rewrite (dom_l WF.(wf_rfE)) at 1.
      by rewrite seqA. }
  all: eapply dom_l.
  { by apply wf_hbE. }
    by apply wf_pscE.
Qed.

Lemma cert_rf_codom : cert_rf ≡ cert_rf ;; <| E0 \₁ D |>.
Proof.
  unfold cert_rf.
  rewrite AuxRel.seq_eqv_minus_lr.
  rewrite seqA.
  rewrite <- id_inter.
  arewrite ((E0 \₁ D) ∩₁ R ∩₁ (E0 \₁ D) ≡₁ (E0 \₁ D) ∩₁ R).
  2: done.
  basic_solver 20.
Qed.

Lemma cert_rfD : cert_rf ≡ ⦗W⦘ ⨾ cert_rf ⨾ ⦗R⦘.
Proof.
  apply dom_helper_3.
  unfold cert_rf.
  unfold Gvf, Avf.
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

Lemma cert_rf_comp : forall b (IN: ((E0 \₁ D) ∩₁ R) b), exists a, cert_rf a b.
Proof.
  ins; unfolder in *; desc.
  assert (exists l, loc b = Some l); desc.
  { by generalize (is_r_loc lab); unfolder in *; basic_solver 12. }

  assert (E b) as UU.
  { desf.
    { eapply coveredE; eauto. }
    { eapply issuedE; eauto. }
    apply (dom_l G.(wf_sbE)) in IN2.
    apply seq_eqv_l in IN2. desf. }

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
  { exists (InitEvent l); splits.
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
    clear IN2.
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
  { clear IN2.
    unfolder in A; desf.
    hahn_rewrite WF.(wf_col) in A.
    unfold same_loc in *; desf; unfolder in *; congruence. }
  exists b0; red; split.
  { unfold Gvf, Avf, same_loc.
    unfolder in A; desf; unfolder; ins; desf; splits; try basic_solver 21; congruence. }
  unfold max_elt in *.
  unfolder in *; ins; desf; intro; desf; basic_solver 11.
Qed.

Lemma cert_rf_mod: (E0 \₁ D) ∩₁ R ≡₁ codom_rel cert_rf.
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

Lemma cert_rf_in_vf: cert_rf ⊆ vf.
Proof. unfold cert_rf; basic_solver. Qed.

Lemma Cvf_in_Gvf : vf ⊆ G.(Gvf).
Proof.
  unfold Gvf, Avf.
  arewrite_id ⦗D⦘. by rewrite seq_id_r.
Qed.

Lemma cert_rf_hb: irreflexive (cert_rf ⨾ hb).
Proof.
  rewrite cert_rf_in_vf.
  rewrite Cvf_in_Gvf.
  cdes COH. by apply Gvf_hb_irr.
Qed.

Lemma non_I_cert_rf: ⦗set_compl I⦘ ⨾ cert_rf ⊆ sb.
Proof.
  assert (cert_rf_hb: irreflexive (cert_rf ⨾ hb))
    by apply cert_rf_hb.
  (* TODO: continue from here *)
Admitted.

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