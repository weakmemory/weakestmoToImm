Require Import Program.Basics.
From hahn Require Import Hahn.
From imm Require Import Events Execution TraversalConfig
     imm_s imm_s_hb CertExecution1 CertExecution2 AuxRel
     CombRelations.
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
Notation "'F'" := (fun a => is_true (is_f lab a)).

Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'sb'" := (G.(sb)).
Notation "'hb'" := (G.(imm_s_hb.hb)).
Notation "'rf'" := (G.(rf)).
Notation "'co'" := (G.(co)).
Notation "'loc'" := (loc lab).

Notation "'Loc_' l" := (fun x => loc x = Some l) (at level 1).
Notation "'W_' l" := (W ∩₁ Loc_ l) (at level 1).
Notation "'R_' l" := (R ∩₁ Loc_ l) (at level 1).

Notation "'furr'" := (furr G sc).

Definition E0 := (Tid_ thread ∩₁ (C ∪₁ dom_rel (sb^? ⨾ ⦗ I ⦘))).
Definition vf := <| W |> ;; (rf ;; <| D |>)^? ;; hb^? ;;
                    sc^? ;; hb^? ;; <| E |>.

Definition cert_rf :=
  vf ∩ same_loc lab ⨾ ⦗ (E0 \₁ D) ∩₁ R ⦘ \ co ⨾ vf.
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

Lemma cert_rf_comp : forall b (IN: ((E0 \₁ D) ∩₁ R) b), exists a, cert_rf a b.
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

Lemma cert_rf_in_furr: cert_rf ⊆ furr.
Proof. rewrite cert_rf_in_vf. apply vf_in_furr. Qed.

Lemma cert_rf_hb_sc_hb_irr: irreflexive (cert_rf ⨾ hb ⨾ (sc ⨾ hb)^?).
Proof.
  rewrite cert_rf_in_furr.
  apply furr_hb_sc_hb_irr; auto.
  all: apply COH.
Qed.

Lemma non_I_cert_rf: ⦗set_compl I⦘ ⨾ cert_rf ⊆ sb.
Proof.
  cdes COH.
  rewrite cert_rf_codom.
  rewrite cert_rf_in_vf.
  unfold vf.
  arewrite_id ⦗E⦘. rewrite seq_id_l.
  arewrite (E0 \₁ D ⊆₁ C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘)).
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
  { sin_rewrite AA. sin_rewrite CC. basic_solver. }

  assert (hb^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆
          <| C |> ;; hb^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ∪
            sb^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘) as PP.
  { admit. } 
  sin_rewrite PP.
  rewrite !seq_union_r.
  unionL.
  { sin_rewrite CC. basic_solver. }
  assert (sb^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆
          ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⨾ sb^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘) as XX.
  { generalize (@sb_trans G). basic_solver 20. }
  sin_rewrite XX.
  arewrite (sb^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆ sb^?).
  arewrite (sc^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆
            <| C |> ;; sc^? ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ∪ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘).
  { admit. } 
  rewrite !seq_union_l, !seq_union_r, !seqA.
  unionL.
  { sin_rewrite YY. basic_solver. }
  sin_rewrite PP.
  rewrite !seq_union_l, !seq_union_r, !seqA.
  unionL.
  { sin_rewrite QQ. basic_solver. }

  (* arewrite (hb^? ⨾ ⦗(E0 \₁ D) ∩₁ R⦘ ⊆ ⦗E0 \₁ D ∪₁ C⦘ ;; hb^? ⨾ ⦗(E0 \₁ D) ∩₁ R⦘). *)
  (* { rewrite crE. rewrite !seq_union_l, !seq_union_r. *)
  (*   rewrite !seq_id_l. *)
  (*   apply inclusion_union_mon. *)
  (*   { basic_solver 10. } *)
  (*   admit. } *)

  (* TODO: continue from here *)

  (* arewrite ((hb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ psc^? ⨾ hb^? ⨾ ⦗(E0 \₁ D) ∩₁ R⦘ ⊆ *)
  (*           ⦗E0 \₁ D ∪₁ C⦘ ⨾ *)
  (*           (hb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ psc^? ⨾ hb^? ⨾ ⦗(E0 \₁ D) ∩₁ R⦘). *)

  (* rewrite crE at 1. *)
  (* rewrite !seq_union_l. rewrite !seq_union_r. *)
  (* rewrite !seq_id_l. *)
  (* unionL. *)
  (* 2: { rewrite !seqA. *)
  (*      arewrite (⦗set_compl I ∩₁ W⦘ ⨾ rf ⨾ ⦗D⦘ ⊆ ∅₂). *)
  (*      2: basic_solver. *)



  (* assert (cert_rf_hb: irreflexive (cert_rf ⨾ hb)) *)
  (*   by apply cert_rf_hb. *)
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