From hahn Require Import Hahn.
From imm Require Import AuxDef Events.
Require Import AuxRel.
Require Import EventStructure.
Require Import AuxDef.

Inductive model := Weakest | Weakestmo.

Section Consistency.

Variable S : ES.t.

Notation "'E'" := S.(ES.acts_set).
Notation "'Einit'" := S.(ES.acts_init_set).
Notation "'Eninit'" := S.(ES.acts_ninit_set).

Notation "'lab'" := S.(ES.lab).

Notation "'sb'" := S.(ES.sb).
Notation "'rmw'" := S.(ES.rmw).
Notation "'ew'" := S.(ES.ew).
Notation "'jf'" := S.(ES.jf).
Notation "'rf'" := S.(ES.rf).
Notation "'fr'" := S.(ES.fr).
Notation "'co'" := S.(ES.co).
Notation "'cf'" := S.(ES.cf).
Notation "'icf'" := S.(ES.icf).

Notation "'jfe'" := S.(ES.jfe).
Notation "'rfe'" := S.(ES.rfe).
Notation "'coe'" := S.(ES.coe).
Notation "'jfi'" := S.(ES.jfi).
Notation "'rfi'" := S.(ES.rfi).
Notation "'coi'" := S.(ES.coi).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).

Notation "'same_tid'" := S.(ES.same_tid).
Notation "'same_lab'" := S.(ES.same_lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).

Notation "'Pln'" := (fun a => is_true (is_only_pln S.(ES.lab) a)) (at level 10).
Notation "'Rlx'" := (fun a => is_true (is_rlx S.(ES.lab) a)) (at level 10).
Notation "'Rel'" := (fun a => is_true (is_rel S.(ES.lab) a)) (at level 10).
Notation "'Acq'" := (fun a => is_true (is_acq S.(ES.lab) a)) (at level 10).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel S.(ES.lab) a)) (at level 10).
Notation "'Sc'" := (fun a => is_true (is_sc S.(ES.lab) a)) (at level 10).

Notation "'K'"     := S.(ES.cont_set).

(* causality conflict  *)

Definition cc :=
  cf ∩ (jfe ⨾ (sb ∪ jf)＊ ⨾ jfe ⨾ sb^?).

(* visible events *)

Definition vis e :=
  ⟪ EE : E e ⟫ /\ ⟪ CCEW : cc ⨾ ⦗ eq e ⦘ ⊆ ew ⨾ sb⁼ ⟫.

(* release sequence *)

Definition rs := ⦗E ∩₁ W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (jf ⨾ rmw)＊.

Definition release := ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ rs.

(* synchronizes with *)

Definition sw := release ⨾ jf ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘.

(* happens before *)

Definition hb : relation eventid := (sb ∪ sw)⁺.

(* extended conflict *)

Definition ecf : relation eventid :=
  (hb⁻¹)^? ⨾ cf ⨾ hb^?.

(* coherence *)

Definition co_strong : relation eventid :=
  (⦗ W ⦘ ⨾ hb ⨾ ⦗ W ⦘) ∩ same_loc.

Definition mco (m : model) : relation eventid :=
  match m with
  | Weakest   => co_strong
  | Weakestmo => co
  end.

Definition mfr (m : model) : relation eventid := rf⁻¹ ⨾ mco m.

Definition eco (m : model) : relation eventid :=
  (rf ∪ (mco m) ∪ (mfr m))⁺.

(* sc order *)

Definition psc_f (m : model) : relation eventid :=
  ⦗F ∩₁ Sc⦘ ⨾ hb ⨾ (eco m ⨾ hb)^? ⨾ ⦗F ∩₁ Sc⦘.

Definition scb :=
  sb ∪ (sb \ same_loc) ⨾ hb ⨾ (sb \ same_loc) ∪ hb ∩ same_loc ∪ co ∪ fr.

Definition psc_base :=
  ⦗Sc⦘ ⨾ (⦗F⦘ ⨾ hb)^? ⨾ scb ⨾ (hb ⨾ ⦗F⦘)^? ⨾ ⦗Sc⦘.

Record es_consistent {m} :=
  { ecf_irf : irreflexive ecf;
    jf_necf : jf ∩ ecf ≡ ∅₂;
    jfe_vis : dom_rel jfe ⊆₁ vis;
    coh : irreflexive (hb ⨾ (eco m)^?);

    icf_R : dom_rel icf ⊆₁ R;
    icf_jf : irreflexive (jf ⨾ icf ⨾ jf⁻¹ ⨾ ew);
  }.

Record good_restriction (A : eventid -> Prop) :=
  { visA : A ⊆₁ vis ;
    ncfA : ES.cf_free S A ;
    hbA  : dom_rel (hb ⨾ ⦗A⦘) ⊆₁ A ;
  }.

(******************************************************************************)
(** ** Properties *)
(******************************************************************************)

Section Properties.
Variable WF : ES.Wf S.
Variable m : model.

(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

Lemma dom_cc_jfe : dom_rel cc ⊆₁ dom_rel jfe.
Proof. unfold cc. basic_solver. Qed.

Lemma cc_tid : cc ⊆ same_tid.
Proof. unfold cc, ES.cf. basic_solver. Qed.

Lemma cc_ninit : cc ⊆ Eninit × Eninit.
Proof. unfold cc, ES.cf. basic_solver. Qed.

Lemma cf_in_ecf : cf ⊆ ecf.
Proof.
  unfold ecf. rewrite !crE, !seq_union_l, !seq_union_r.
  repeat unionR left. basic_solver 10.
Qed.

Lemma ecf_sym : symmetric ecf.
Proof.
  unfold ecf, seq.
  intros a b [c [HB [d [CF tHB]]]].
  eexists. split.
  { apply transp_cr in tHB.
    unfold transp in tHB.
    apply tHB. }
  eexists. split.
  { eapply ES.cf_sym. eauto. }
  apply transp_cr in HB.
  by unfold transp in HB.
Qed.

Lemma hb_trans : transitive hb.
Proof. vauto. Qed.

Lemma sb_in_hb : sb ⊆ hb.
Proof. vauto. Qed.

Lemma sw_in_hb : sw ⊆ hb.
Proof. vauto. Qed.

Lemma cr_hb_hb : hb^? ⨾ hb ≡ hb.
Proof. generalize hb_trans; basic_solver. Qed.

Lemma cr_hb_cr_hb : hb^? ⨾ hb^? ≡ hb^?.
Proof. generalize hb_trans; basic_solver 20. Qed.

Lemma hb_sb_sw : hb ≡ hb^? ⨾ (sb ∪ sw).
Proof. unfold hb; rewrite ct_end at 1; rels. Qed.

Lemma sw_ninit : sw ⨾ ⦗Einit⦘ ≡ ∅₂.
Proof.
  split; [|done].
  unfold sw.
  rewrite crE. relsf.
  unionL.
  { rewrite ES.jfD; auto.
    rewrite ES.acts_init_set_inW; auto.
    type_solver. }
  rewrite !seqA.
  arewrite (sb ⨾ ⦗F⦘ ⨾ ⦗Acq⦘ ⨾ ⦗Einit⦘ ≡ sb ⨾ ⦗Einit⦘ ⨾ ⦗F⦘ ⨾ ⦗Acq⦘).
  { basic_solver. }
  rewrite <- seqA with (r1 := sb).
  rewrite ES.sb_ninit; auto.
  basic_solver.
Qed.

Lemma hb_ninit : hb ⨾ ⦗Einit⦘ ≡ ∅₂.
Proof.
  split; [|done].
  unfold hb.
  rewrite seq_eqv_r.
  intros x y [TC INIT].
  induction TC; [|intuition].
  destruct H as [SB | SW].
  { eapply ES.sb_ninit; eauto.
    apply seq_eqv_r; eauto. }
  eapply sw_ninit; auto.
  apply seq_eqv_r; eauto.
Qed.

Lemma rf_in_eco (m' : model) : rf ⊆ eco m'.
Proof.
  unfold eco. etransitivity.
  2: by apply ct_step.
  basic_solver.
Qed.

Lemma co_in_eco : co ⊆ eco Weakestmo.
Proof.
  unfold eco. simpls. etransitivity.
  2: by apply ct_step.
  basic_solver.
Qed.

Lemma fr_in_eco : fr ⊆ eco Weakestmo.
Proof.
  unfold eco. etransitivity.
  2: by apply ct_step.
  basic_solver.
Qed.

Lemma mco_in_eco : mco m ⊆ eco m.
Proof.
  unfold eco. etransitivity.
  2: by apply ct_step.
  basic_solver.
Qed.

Lemma mfr_in_eco : mfr m ⊆ eco m.
Proof.
  unfold eco. etransitivity.
  2: by apply ct_step.
  basic_solver.
Qed.

Lemma mco_trans : transitive (mco m).
Proof.
  destruct m; simpls.
  2: by apply ES.co_trans.
  unfold co_strong.
  red. intros x y z [XY LA] [YZ LB]. split.
  2: { red. by rewrite LA. }
  destruct_seq XY as [WX WY].
  destruct_seq YZ as [YY WZ].
  apply seq_eqv_l; split; auto.
  apply seq_eqv_r; split; auto.
  eapply hb_trans; eauto.
Qed.

Lemma eco_trans (m' : model) : transitive (eco m').
Proof. unfold eco. apply transitive_ct. Qed.

Lemma ra_jf_in_hb  :
  ⦗Rel⦘ ⨾ jf ⨾ ⦗Acq⦘ ⊆ hb.
Proof.
  rewrite <- sw_in_hb.
  unfold sw.
  rewrite <- inclusion_id_cr. rewrite seq_id_l.
  rewrite (dom_l WF.(ES.jfE)) at 1.
  rewrite (dom_l WF.(ES.jfD)) at 1.
  rewrite !seqA.
  arewrite (⦗Rel⦘ ⨾ ⦗E⦘ ⨾ ⦗W⦘ ⊆ release); [|done].
  unfold release, rs.
  basic_solver 20.
Qed.

Lemma ra_rf_in_hb  :
  ⦗Rel⦘ ⨾ rf ⨾ ⦗Acq⦘ ⊆ hb.
Proof.
  unfold ES.rf.
  rewrite inclusion_minus_rel, seqA.
  arewrite (⦗Rel⦘ ⨾ ew ⊆ ⦗Rel⦘).
  { rewrite WF.(ES.ewm). basic_solver. }
  apply ra_jf_in_hb.
Qed.

(******************************************************************************)
(** ** Sets and Relations in graph *)
(******************************************************************************)

Lemma visE : vis ⊆₁ E.
Proof. unfold vis. basic_solver. Qed.

Lemma ccE : cc ≡ ⦗E⦘ ⨾ cc ⨾ ⦗E⦘.
Proof.
  unfold cc.
  rewrite <- restr_relE, restr_inter, restr_inter_absorb_r.
  by rewrite ES.cfE, restr_relE at 1.
Qed.

Lemma rsE : rs ≡ ⦗E⦘ ⨾ rs ⨾ ⦗E⦘.
Proof.
  split; [|basic_solver 12].
  unfold rs.
  rewrite rtE; relsf; unionL.
  { apply inclusion_union_r1_search.
    rewrite (ES.sbE WF).
    basic_solver 21. }
  unionR right.
  rewrite (dom_r (ES.rmwE WF)) at 1.
  rewrite <- !seqA.
  sin_rewrite inclusion_ct_seq_eqv_r.
  rewrite !seqA.
  hahn_frame.
  arewrite (⦗E⦘ ⨾ ⦗E ∩₁ W⦘ ≡ ⦗E ∩₁ W⦘) by basic_solver.
Qed.

Lemma releaseE : release ≡ ⦗E⦘ ⨾ release ⨾ ⦗E⦘.
Proof.
  unfold release.
  rewrite rsE.
  rewrite (ES.sbE WF) at 1.
  basic_solver 42.
Qed.

Lemma swE_right : sw ≡ sw ⨾ ⦗E⦘.
Proof.
  split; [|basic_solver].
  unfold sw.
  rewrite (ES.sbE WF) at 1 2.
  rewrite (ES.jfE WF) at 1.
  basic_solver 42.
Qed.

Lemma swE : sw ≡ ⦗E⦘ ⨾ sw ⨾ ⦗E⦘.
Proof.
  split; [|basic_solver].
  rewrite swE_right at 1.
  hahn_frame.
  unfold sw.
  rewrite releaseE.
  rewrite (dom_l (ES.jfE WF)).
  rewrite (dom_l (ES.sbE WF)).
  basic_solver 40.
Qed.

Lemma hbE : hb ≡ ⦗E⦘ ⨾ hb ⨾ ⦗E⦘.
Proof.
  split; [|basic_solver].
  unfold hb.
  rewrite <- inclusion_ct_seq_eqv_r, <- inclusion_ct_seq_eqv_l.
  apply inclusion_t_t.
  rewrite (ES.sbE WF) at 1.
  rewrite swE at 1.
  basic_solver 42.
Qed.

Lemma ecfE : ecf ≡ ⦗E⦘ ⨾ ecf ⨾ ⦗E⦘.
Proof.
  split; [|basic_solver].
  unfold ecf.
  rewrite ES.cfE, hbE.
  basic_solver 42.
Qed.

(******************************************************************************)
(** ** Domains and codomains  *)
(******************************************************************************)

Lemma ccW : cc ≡ ⦗W⦘ ⨾ cc.
Proof.
  unfold cc.
  rewrite interC.
  rewrite <- seq_eqv_inter_ll.
  rewrite <- !seqA.
  erewrite <- dom_l with (d := W) (r := jfe).
  2 : by eapply ES.jfeD.
  basic_solver.
Qed.

Lemma rsD : rs ≡ ⦗W⦘ ⨾ rs ⨾ ⦗W⦘.
Proof.
  split; [|basic_solver].
  unfold rs.
  rewrite rtE; relsf; unionL; [basic_solver 12|].
  rewrite (dom_r (ES.rmwD WF)) at 1.
  rewrite <- !seqA.
  rewrite inclusion_ct_seq_eqv_r.
  basic_solver 42.
Qed.

Lemma releaseD : release ≡ ⦗FW ∩₁ Rel⦘ ⨾ release ⨾ ⦗W⦘.
Proof.
  split; [|basic_solver].
  unfold release.
  rewrite rsD at 1.
  basic_solver 42.
Qed.

Lemma swD : sw ≡ ⦗FW ∩₁ Rel⦘ ⨾ sw ⨾ ⦗FR ∩₁ Acq⦘.
Proof.
  split; [|basic_solver].
  unfold sw.
  rewrite releaseD at 1.
  rewrite (ES.jfD WF) at 1.
  basic_solver 42.
Qed.

Lemma mcoD : mco m ≡ ⦗ W ⦘ ⨾ mco m ⨾ ⦗ W ⦘.
Proof.
  destruct m; simpls.
  2: by apply ES.coD.
  unfold co_strong. basic_solver 10.
Qed.

Lemma mfr_weakestmo : mfr Weakestmo ≡ fr.
Proof. unfold mfr, ES.fr. simpls. Qed.

Lemma mfrD : mfr m ≡ ⦗ R ⦘ ⨾ mfr m ⨾ ⦗ W ⦘.
Proof.
  unfold mfr. rewrite mcoD.
  rewrite WF.(ES.rfD).
  basic_solver 10.
Qed.

(******************************************************************************)
(** ** Alternative representations of sets and relations *)
(******************************************************************************)

Lemma rs_alt : rs ≡ ⦗E ∩₁ W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗E ∩₁ W⦘ ⨾ (jf ⨾ rmw)＊.
Proof.
  unfold rs.
  rewrite (ES.sbE WF).
  basic_solver 42.
Qed.

Lemma release_alt : release ≡ ⦗E ∩₁ FW ∩₁ Rel⦘ ⨾ (⦗E ∩₁ F⦘ ⨾ sb)^? ⨾ rs.
Proof.
  rewrite releaseE, releaseD.
  unfold release.
  rewrite (ES.sbE WF), rsD, rsE.
  basic_solver 42.
Qed.

Lemma sw_alt : sw ≡ release ⨾ jf ⨾ (sb ⨾ ⦗E ∩₁ F⦘)^? ⨾ ⦗E ∩₁ FR ∩₁ Acq⦘.
Proof.
  rewrite swD.
  unfold sw.
  rewrite releaseD.
  rewrite (ES.sbE WF), (ES.jfE WF).
  basic_solver 42.
Qed.

Lemma eco_alt : eco Weakestmo ≡ rf ∪ co ⨾ rf^? ∪ fr ⨾ rf^?.
Proof.
  split.
  2: { rewrite rf_in_eco, co_in_eco, fr_in_eco.
       generalize eco_trans. basic_solver. }
  unfold eco. simpls. rewrite mfr_weakestmo.
  rewrite !crE; relsf.
  rewrite WF.(ES.rfD), WF.(ES.coD), WF.(ES.frD).
  intros x y H. induction H.
  { generalize H. basic_solver 20. }
  clear H H0. unfolder in *. desf.
  all: try type_solver.
  all: try eauto 20 using WF.(ES.co_trans) with hahn.
  { left. right. left. splits; auto.
    eapply ES.rffr_in_co; auto.
    eexists. eauto. }
  { left. right. right. eexists z0. splits; auto.
    eapply ES.rffr_in_co; auto.
    eexists. eauto. }
  { assert (co z0 z).
    { apply ES.rffr_in_co; auto. eexists. eauto. }
    eauto 10 using WF.(ES.co_trans) with hahn. }
  { assert (co z0 z1).
    { apply ES.rffr_in_co; auto. eexists. eauto. }
    eauto 20 using WF.(ES.co_trans) with hahn. }
  { right. left. splits; auto.
    eapply ES.frco_in_fr; auto.
    eexists. eauto. }
  { assert (fr x z0).
    { eapply ES.frco_in_fr; auto. eexists. eauto. }
    right. right. splits; auto.
    exists z0. splits; eauto. }
  { assert (co z0 z).
    { apply ES.rffr_in_co; auto. eexists. splits; eauto. }
    right. left. splits; auto.
    apply ES.frco_in_fr; auto. eexists. eauto. }
  assert (co z0 z1).
  { apply ES.rffr_in_co; auto. eexists. splits; eauto. }
  assert (fr x z1).
  { apply ES.frco_in_fr; auto. eexists. splits; eauto. }
  right. right. eexists. splits; eauto.
Qed.

(******************************************************************************)
(** ** Alternative representations of properties *)
(******************************************************************************)

Lemma ecf_irr_hb_cf_irr : irreflexive ecf -> irreflexive (hb ⨾ cf).
Proof.
  unfold ecf.
  rewrite !crE. relsf.
  unfold irreflexive.
  intros ECFIRR x HH.
  destruct HH as [y [HB CF]].
  eapply ECFIRR.
  left. right.
  unfold transp.
  eexists; split; eauto.
  by apply ES.cf_sym.
Qed.

Lemma ecf_irr_thb_cf_hb_irr : irreflexive ecf -> irreflexive (hb⁻¹ ⨾ cf ⨾ hb).
Proof.
  unfold ecf.
  rewrite !crE. relsf.
  unfold irreflexive.
  intros ECFIRR x HH.
  destruct HH as [y [THB [z [CF HB]]]].
  eapply ECFIRR.
  right. right.
  unfold seq.
  exists y; split; eauto.
Qed.

Lemma ecf_irr_alt :
  irreflexive ecf <-> irreflexive (hb ⨾ cf) /\  irreflexive (hb⁻¹ ⨾ cf ⨾ hb).
Proof.
  split.
  { ins. split.
    { by apply ecf_irr_hb_cf_irr. }
    by apply ecf_irr_thb_cf_hb_irr. }
  unfold ecf. rewrite !crE. relsf.
  unfold irreflexive.
  intros [HBCF THBCFHB].
  unfold union.
  ins; desf.
  { eapply ES.cf_irr. eauto. }
  { destruct H as [y [HB CF]].
    unfold transp in HB.
    eapply HBCF.
    apply ES.cf_sym in CF.
    unfold seq. eauto. }
  { destruct H as [y [CF HB]].
    eapply HBCF.
    unfold seq. eauto. }
  eapply THBCFHB. eauto.
Qed.

Lemma jf_necf_jf_ncf : jf ∩ ecf ≡ ∅₂ -> jf ∩ cf ≡ ∅₂.
Proof.
  intros [JFnECF _].
  split; [|basic_solver].
  by sin_rewrite cf_in_ecf.
Qed.

Lemma jf_necf_hb_jf_ncf : jf ∩ ecf ≡ ∅₂ -> (hb ⨾ jf) ∩ cf ≡ ∅₂.
Proof.
  unfold ecf.
  intros [JFnECF _].
  split; [|basic_solver].
  intros x y [[z [HB JF]] CF].
  eapply JFnECF. split; eauto.
  red. exists x. splits; auto.
  red. exists y. splits; auto.
Qed.

Lemma jf_necf_hb_tjf_ncf : jf ∩ ecf ≡ ∅₂ -> (hb ⨾ jf⁻¹) ∩ cf ≡ ∅₂.
Proof.
  unfold ecf.
  intros [JFnECF _].
  split; [|basic_solver].
  intros x y [[z [HB tJF]] CF].
  eapply JFnECF. split.
  { unfold transp in tJF. eauto. }
  red. exists y. splits.
  { unfolder; auto. }
  red. exists x. splits; auto.
  by apply ES.cf_sym.
Qed.

Lemma jf_necf_hb_jf_thb_ncf : jf ∩ ecf ≡ ∅₂ -> (hb ⨾ jf ⨾ hb⁻¹) ∩ cf ≡ ∅₂.
Proof.
  unfold ecf.
  intros [JFnECF _].
  split; [|basic_solver].
  intros x y [[z [HB [z' [JF tHB]]]] CF].
  eapply JFnECF. split; eauto.
  red. exists x. splits.
  { unfolder; auto. }
  red. exists y. splits; auto.
Qed.

Lemma jf_necf_alt :
  jf ∩ ecf ≡ ∅₂ <->
    jf ∩ cf ≡ ∅₂ /\
    (hb ⨾ jf) ∩ cf ≡ ∅₂ /\
    (hb ⨾ jf⁻¹) ∩ cf ≡ ∅₂ /\
    (hb ⨾ jf ⨾ hb⁻¹) ∩ cf ≡ ∅₂.
Proof.
  split.
  { intros [JFnECF _].
    splits; red; splits; try by intuition.
    { by apply jf_necf_jf_ncf. }
    { by apply jf_necf_hb_jf_ncf. }
    { by apply jf_necf_hb_tjf_ncf. }
    by apply jf_necf_hb_jf_thb_ncf. }
  intros [[JFnCF _] [[HBJFnCF _] [[HBtJFnCF _] [HBJFtHBnCF _]]]].
  split; [|basic_solver].
  unfold ecf.
  rewrite !crE, !seq_union_l, !seq_union_r,
    !seq_id_r, !seq_id_l, !inter_union_r.
  unfold union. intros x y HH. desf.
  { eapply JFnCF; eauto. }
  { destruct HH as [JF [z [CF HB]]].
    eapply HBtJFnCF. split.
    { unfolder; eauto. }
      by apply ES.cf_sym. }
  { destruct HH as [JF [z [tHB CF]]].
    eapply HBJFnCF.
    split; unfolder; eauto. }
  destruct HH as [JF HH].
  destruct HH as [z [tHB [z' [CF HB]]]].
  eapply HBJFtHBnCF. split; eauto.
  red. exists x. splits; eauto.
  red. exists y. splits; eauto.
Qed.

(******************************************************************************)
(** ** Consistent EventStructure properties *)
(******************************************************************************)

Section ConsistentProps.

  Variable ESC : @es_consistent m.

  Lemma hb_irr : irreflexive hb.
  Proof.
    specialize (coh ESC) as hb_eco_irr.
    apply irreflexive_inclusion with (r' :=  hb ⨾ (eco m)^?).
    { basic_solver. }
    eauto with hahn.
  Qed.

  Lemma hb_acyclic : acyclic hb.
  Proof.
    apply (trans_irr_acyclic hb_irr hb_trans).
  Qed.

  Lemma hb_imm_split_l :
    hb ≡ immediate hb ⨾ hb^?.
  Proof.
    eapply ct_imm_split_l.
    { eapply hb_irr. }
    { eapply hb_trans. }
    rewrite (dom_l hbE).
    rewrite dom_seq, dom_eqv, ES.E_alt.
    auto.
  Qed.

  Lemma hb_imm_split_r :
    hb ≡ hb^? ⨾ immediate hb.
  Proof.
    eapply ct_imm_split_r.
    { eapply hb_irr. }
    { eapply hb_trans. }
    rewrite (dom_l hbE).
    rewrite dom_seq, dom_eqv, ES.E_alt.
    auto.
  Qed.

  Lemma r_hb_in_imm_sb_hb :
    ⦗R⦘ ⨾ hb ⊆ immediate sb ⨾ hb^?.
  Proof.
    rewrite hb_imm_split_l at 1; auto.
    rewrite <- seqA. apply seq_mori; [|done].
    unfold hb. rewrite imm_clos_trans.
    rewrite imm_union, seq_union_r.
    apply inclusion_union_l; [basic_solver|].
    rewrite immediate_in, (dom_l swD ). type_solver.
  Qed.

  Lemma hb_w_in_hb_imm_sb :
    hb ⨾ ⦗W⦘ ⊆ hb^? ⨾ immediate sb.
  Proof.
    rewrite hb_imm_split_r at 1; auto.
    rewrite seqA. apply seq_mori; [done|].
    unfold hb. rewrite imm_clos_trans.
    rewrite imm_union, seq_union_l.
    apply inclusion_union_l; [basic_solver|].
    rewrite immediate_in, (dom_r swD). type_solver.
  Qed.

  Lemma t_rmw_hb_in_hb :
    rmw⁻¹ ⨾ hb ⊆ hb^?.
  Proof.
    rewrite WF.(ES.rmwD), R_ex_in_R.
    rewrite (dom_l WF.(ES.rmwEninit)).
    rewrite !transp_seq, WF.(ES.rmwi).
    rewrite !seqA, !transp_eqv_rel.
    rewrite r_hb_in_imm_sb_hb; eauto.
    rewrite <- seq_eqvK with (dom := Eninit), seqA.
    rewrite <- seqA with (r1 := (immediate sb)⁻¹).
    rewrite <- transp_eqv_rel with (d := Eninit) at 1.
    rewrite <- transp_seq.
    rewrite <- seqA with (r3 := hb^?).
    arewrite (⦗Eninit⦘ ⨾ immediate sb ⊆ immediate sb ∩ same_tid).
    { erewrite <- inter_absorb_l with (r := ⦗Eninit⦘ ⨾ immediate sb)
                                     (r' := immediate sb ); [|basic_solver].
      erewrite seq_mori; [|apply inclusion_refl2 | apply immediate_in].
      rewrite ES.sb_tid; eauto with hahn. }
    rewrite transp_inter.
    erewrite transp_sym_equiv with (r := (same_tid)); [| apply ES.same_tid_sym].
    rewrite <- seqA with (r3 := hb^?).
    rewrite HahnEquational.inter_trans; [| apply ES.same_tid_trans].
    rewrite ES.imm_tsb_imm_sb_in_icf; auto.
    arewrite (⦗W⦘ ⨾ (icf)^? ≡ ⦗W⦘).
    { rewrite crE, seq_union_r, seq_id_r.
      rewrite (dom_rel_helper ESC.(icf_R)).
      type_solver. }
    basic_solver.
  Qed.

  Lemma cont_sb_dom_rmw k s
        (INK : K (k, s)) :
    codom_rel (⦗ES.cont_sb_dom S k⦘ ⨾ rmw) ⊆₁ ES.cont_sb_dom S k.
  Proof.
    unfold ES.cont_sb_dom.
    desf.
    { sin_rewrite WF.(ES.acts_init_set_inW).
      rewrite WF.(ES.rmwD). mode_solver. }
    rewrite WF.(ES.rmwE).
    rewrite WF.(ES.sbE) at 1.
    unfolder. ins. desf.
    { exfalso. apply WF.(ES.rmw_K). unfold dom_rel. eauto 10. }
    destruct (classic (x = y)) as [|NEQ]; subst.
    { do 2 eexists. splits.
      { by left. }
      all: eauto. }
    do 2 (exists y). splits; auto.
    right.
    apply WF.(ES.sb_imm_split_l) in H5.
    destruct H5 as [z [SBI SB]].
    destruct (classic (z = x)) as [|XZNEQ]; subst.
    { destruct SB; desf. }
    exfalso.
    assert (icf x z) as CF.
    2: { apply WF.(ES.rmwD) in H0.
         assert (R x) as RX.
         { eapply icf_R; eauto. eexists. eauto. }
         destruct_seq H0 as [RR WW].
         type_solver. }
    set (SBIX := H0).
    apply WF.(ES.rmwi) in SBIX.
    apply WF.(ES.rmwEninit) in H0.
    destruct_seq H0 as [EZ EX].
    edestruct WF.(ES.imm_tsb_imm_sb_in_icf).
    { split.
      { exists z0. splits.
        { apply SBI. }
        apply SBIX. }
      red.
      erewrite <- WF.(ES.sb_tid) with (x:=z0).
      { by apply WF.(ES.rmwt). }
      apply seq_eqv_l. split; auto. apply SBI. }
    { desf. }
      by apply ES.icf_sym.
  Qed.

  Lemma jf_tsb : jf ∩ sb⁻¹ ⊆ ∅₂.
  Proof.
    intros x y [JF tSB].
    eapply coh; [apply ESC|].
    eexists. split.
    { apply sb_in_hb. basic_solver. }
    apply r_step. unfold eco.
    apply t_step. unfold ES.rf.
    do 2 left. split.
    { apply ES.jf_in_ew_jf; auto. }
    intros CF.
    apply ES.cf_sym in CF.
    eapply ES.n_sb_cf; eauto.
  Qed.

  Lemma jfi_alt : jfi ≡ ⦗Einit⦘ ⨾ jf ∪ (jf ∩ same_tid).
  Proof.
    unfold ES.jfi.
    rewrite ES.sb_Einit_Eninit; auto.
    rewrite inter_union_r.
    apply union_more.
    { red. split.
      { basic_solver. }
      rewrite ES.jfE at 1; auto.
      rewrite ES.acts_set_split at 2.
      rewrite id_union. relsf.
      arewrite_false (jf ⨾ ⦗Einit⦘).
      { rewrite ES.jfD, ES.acts_init_set_inW; auto. type_solver. }
      basic_solver. }
    rewrite ES.jf_same_tid; auto.
    rewrite ES.same_thread; auto.
    rewrite crsE. relsf.
    rewrite !inter_union_r.
    arewrite_false (jf ∩ ⦗Eninit⦘).
    { rewrite ES.jfD; auto. type_solver. }
    arewrite_false (jf ∩ (⦗Eninit⦘ ⨾ sb⁻¹ ⨾ ⦗Eninit⦘)).
    { generalize jf_tsb. basic_solver. }
    arewrite_false (jf ∩ cf).
    { eapply ES.jf_ncf; auto. }
    basic_solver 10.
  Qed.

  Lemma jfe_alt : jfe ≡ ⦗Eninit⦘ ⨾ jf ∩ compl_rel same_tid.
  Proof.
    unfold ES.jfe.
    erewrite <- inter_absorb_r
      with (r := jf) at 1.
    2 : eapply ES.jf_nEinit_alt; auto.
    rewrite inter_union_r, minus_union_l.
    arewrite_false (jf ∩ Einit × Eninit \ sb).
    { rewrite ES.sb_init; auto. basic_solver. }
    relsf. split.
    { intros x y [[JF [Enix Eniy]] nSB].
      apply seq_eqv_l. unfold inter_rel.
      splits; auto.
      intros STID. unfold ES.same_tid in STID.
      edestruct ES.same_thread_alt as [crsSB | CF];
        try apply STID; eauto.
      { apply Enix. }
      { apply crsE in crsSB.
        destruct crsSB as [[ID | SB] | tSB]; auto.
        { unfolder in ID. desc.
          eapply ES.jf_eq; eauto.
          split; eauto. }
        eapply jf_tsb. basic_solver. }
      eapply ES.jf_ncf; eauto.
      basic_solver. }
    rewrite seq_eqv_l.
    unfold compl_rel, ES.same_tid.
    intros x y [Enix [JF nSTID]].
    unfolder; splits; auto.
    { eapply ES.jf_nEinit_alt in JF; auto.
      generalize JF. basic_solver. }
    intros SB. apply nSTID.
    apply ES.sb_tid; auto.
    basic_solver.
  Qed.

  Lemma jfe_dom_ninit : dom_rel jfe ⊆₁ Eninit.
  Proof. rewrite jfe_alt. basic_solver. Qed.

  Lemma jfe_nsame_tid : jfe ⊆ compl_rel same_tid.
  Proof. rewrite jfe_alt. basic_solver. Qed.

  Lemma rfe_ew_jfe : rfe ≡ ew ⨾ jfe.
  Proof.
    split; [apply ES.rfe_in_ew_jfe; auto|].
    unfold ES.rfe, ES.rf.
    rewrite jfe_alt.
    rewrite seq_eqv_l.
    intros x y [z [EW [nINITx [JF nSTID]]]].
    unfolder; eexists; splits; eauto.
    { intros CF.
      apply nSTID.
      etransitivity.
      { eapply ES.ew_tid; auto.
        apply ES.ew_sym; eauto. }
        by apply ES.cf_same_tid. }
    intros SB.
    apply ES.ewc in EW; auto.
    destruct EW as [EQ | CF].
    { subst. apply nSTID.
      apply ES.sb_tid; auto.
      basic_solver. }
    apply nSTID.
    etransitivity.
    { apply ES.cf_same_tid.
      apply ES.cf_sym; eauto. }
    apply ES.sb_Einit_Eninit in SB; auto.
    destruct SB as [[INITx _] | HH].
    { exfalso.
      eapply ES.ncfEinit_l.
      basic_solver. }
    apply ES.sb_tid; auto.
    generalize HH.
    basic_solver 20.
  Qed.

  Lemma ew_rfe_in_rfe : ew ⨾ rfe ⊆ rfe.
  Proof.
    rewrite rfe_ew_jfe.
    rewrite <- seqA.
    apply seq_mori; [|done].
    rewrite transitiveI.
    apply WF.
  Qed.

  Lemma rfe_dom_ninit : dom_rel rfe ⊆₁ Eninit.
  Proof.
    rewrite rfe_ew_jfe,
            jfe_alt,
            ES.ewEninit;
      auto.
    basic_solver.
  Qed.

  Lemma rfe_nsame_tid : rfe ⊆ compl_rel same_tid.
  Proof.
    rewrite rfe_ew_jfe,
            ES.ew_tid,
            jfe_nsame_tid;
      auto.
    unfold ES.same_tid.
    basic_solver.
  Qed.

  Lemma cc_alt :
    cc ≡ cf ∩ (jfe ⨾ (sb ∪ jf)＊).
  Proof.
    unfold cc.
    split.
    { apply inclusion_inter_mon; [done|].
      arewrite (jfe ⊆ (sb ∪ jf)＊) at 2.
      arewrite (sb^? ⊆ (sb ∪ jf)＊).
      by rewrite !rt_rt. }
    rewrite <- interK with (r := cf) at 1.
    rewrite interA.
    apply inclusion_inter_mon; auto with hahn.
    rewrite rtE at 1.
    rewrite seq_union_r, seq_id_r, inter_union_r.
    apply inclusion_union_l.
    { rewrite ES.cf_same_tid.
      rewrite jfe_alt at 1; eauto.
      basic_solver. }
    rewrite ES.jfi_union_jfe at 1.
    rewrite <- !unionA.
    arewrite (sb ∪ jfi ⊆ sb).
    rewrite path_ut_last.
    rewrite seq_union_r, inter_union_r.
    apply inclusion_union_l.
    { arewrite_false (cf ∩ (jfe ⨾ sb⁺)); [|done].
      rewrite (ct_of_trans (ES.sb_trans WF)).
      arewrite (jfe ⊆ compl_rel same_tid ⨾ ⦗Eninit⦘).
      { rewrite jfe_alt; eauto.
        rewrite ES.jf_nEinit_alt; eauto.
        basic_solver. }
      rewrite ES.sb_tid; eauto.
      rewrite ES.cf_same_tid.
      rewrite compl_seq_l;
        [basic_solver |
         apply ES.same_tid_sym |
         apply ES.same_tid_trans]. }
    rewrite inclusion_inter_l2.
    repeat apply inclusion_seq_mon; eauto with hahn.
    apply (rt_of_trans (ES.sb_trans WF)).
  Qed.

  Lemma seq_rmw_cf_in_cf :
    rmw ⨾ cf ⊆ cf.
  Proof.
    unfold ES.cf.
    rewrite (dom_l (ES.rmwEninit WF)), !seqA.
    apply inclusion_seq_mon; [done|].
    rewrite <- !seqA.
    apply inclusion_seq_mon; [|done].
    rewrite seqA.
    rewrite inclusion_seq_eqv_l.
    rewrite minus_inter_compl at 2.
    apply inclusion_inter_r.
    { rewrite ES.rmwt; auto.
      specialize ES.same_tid_trans.
      basic_solver. }
    rewrite minus_inter_compl.
    unfolder. intros r w HH. intro SBEQ.
    desf; unfold "~" in HH1; apply HH1;
      rename HH into RMW, HH0 into TID; clear HH1.
    { right. right.
      apply ES.rmw_in_sb; eauto. }
    { apply ES.sb_imm_split_l in SBEQ; auto.
      unfold seq in SBEQ. desf.
      assert (TID_ZZ0 : ES.same_tid S z z0).
      { apply immediate_in in SBEQ.
        eapply ES.same_tid_trans with (y := r).
        { apply ES.rmwt in RMW; basic_solver. }
        assert (NINIT_R : Eninit r).
        { apply (dom_l (ES.rmwEninit WF)) in RMW.
          unfolder in RMW.
          basic_solver. }
        specialize ES.sb_tid.
        basic_solver 5. }
      assert (ICF : icf^? z z0).
      { apply ES.imm_tsb_imm_sb_in_icf; auto.
        apply ES.rmwi in RMW; auto.
        basic_solver. }
      unfolder in ICF. desf.
      { unfolder in SBEQ0; basic_solver. }
      apply (dom_r (ES.rmwD WF)) in RMW.
      unfolder in RMW.
      assert (R z); [|type_solver].
      eapply icf_R; eauto. basic_solver. }
    right; right.
    apply ES.rmw_in_sb in RMW; auto.
    specialize ES.sb_trans.
    basic_solver.
  Qed.

  Lemma hb_jf_prcl_cc_prcl {A}
        (JF_PRCL : prcl jf A)
        (HB_PRCL : prcl hb A) :
    prcl cc A.
  Proof.
    rewrite cc_alt; eauto.
    rewrite inclusion_inter_l2.
    unfold prcl. rewrite seqA.
    arewrite ((sb ∪ jf)＊ ⨾ ⦗A⦘ ⊆ ⦗A⦘ ⨾ (sb ∪ jf)＊).
    { apply dom_r2l_rt.
      assert (DOM': dom_rel((sb ∪ jf) ⨾ ⦗A⦘) ⊆₁ A).
      { rewrite sb_in_hb. relsf. }
      rewrite (dom_rel_helper DOM'). basic_solver. }
    arewrite (jfe ⊆ jf).
    rewrite <- seqA, dom_seq. auto.
  Qed.

  Lemma ncf_hb_jf_prcl_vis {A}
        (AE : A ⊆₁ E)
        (NCF : ES.cf_free S A)
        (JF_PRCL : prcl jf A)
        (HB_PRCL : prcl hb A) :
    A ⊆₁ vis.
  Proof.
    unfold vis; splits; constructor;
      rename x into v, H into vA; auto.
    arewrite (cc ⨾ ⦗eq v⦘ ⊆ ∅₂); [|done].
    arewrite (eq v ⊆₁ A); [basic_solver|].
    rewrite (dom_rel_helper (hb_jf_prcl_cc_prcl JF_PRCL HB_PRCL)).
    unfold cc. by rewrite inclusion_inter_l1.
  Qed.

End ConsistentProps.

Section WeakestMOConsistentProps.

  Variable ESC : @es_consistent Weakestmo.

  Lemma co_jf_hb_tjf_irr :
    irreflexive (co ⨾ jf^? ⨾ hb ⨾ jf⁻¹).
  Proof.
    apply irreflexive_seqC. rewrite !seqA.
    apply irreflexive_seqC. rewrite !seqA.
    seq_rewrite <- ES.fr_alt; auto.
    arewrite (fr ⨾ jf^? ⊆ (eco Weakestmo)^?).
    2: by apply ESC.
    rewrite ES.jf_in_rf; auto.
    rewrite fr_in_eco.
    arewrite (rf ⊆ eco Weakestmo).
    generalize (eco_trans Weakestmo).
    basic_solver.
  Qed.

End WeakestMOConsistentProps.

End Properties.

End Consistency.

Require Import Setoid.

Add Parametric Morphism : good_restriction with signature
  eq ==> set_equiv ==> iff as good_restriction_more.
Proof.
  intros S s s' EQV.
  split; intros GRestr; constructor.
  1-3 : rewrite <- EQV; apply GRestr.
  all : rewrite EQV; apply GRestr.
Qed.
