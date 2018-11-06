From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events.
Require Import AuxRel EventStructure AuxDef.

Inductive model := Weakest | Weakestmo.

Section Consistency.

Variable S : ES.t.

Notation "'E'" := S.(ES.acts_set).
Notation "'E_init'" := S.(ES.acts_init_set).
Notation "'lab'" := S.(ES.lab).
Notation "'sb'" := S.(ES.sb).
Notation "'rmw'" := S.(ES.rmw).
Notation "'ew'" := S.(ES.ew).
Notation "'jf'" := S.(ES.jf).
Notation "'rf'" := S.(ES.rf).
Notation "'fr'" := S.(ES.fr).
Notation "'co'" := S.(ES.co).
Notation "'cf'" := S.(ES.cf).
Notation "'cc'" := S.(ES.cc).

Notation "'jfe'" := S.(ES.jfe).
Notation "'rfe'" := S.(ES.rfe).
Notation "'coe'" := S.(ES.coe).
Notation "'jfi'" := S.(ES.jfi).
Notation "'rfi'" := S.(ES.rfi).
Notation "'coi'" := S.(ES.coi).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
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

Definition same_lab x y := lab x = lab y.

Definition vis :=
  codom_rel (cc ∩ (ew ⨾ sb ⁼)).

(* release sequence *)
Definition rs := ⦗E ∩₁ W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (rf ⨾ rmw)＊.

Definition release := ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ rs.

(* synchronizes with *)
Definition sw := release ⨾ rf ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘.

(* happens before *)
Definition hb : relation eventid := (sb ∪ sw)⁺.

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

Definition psc (m : model) : relation eventid :=
  ⦗ Sc ⦘ ⨾ hb ⨾ eco m ⨾ hb ⨾ ⦗ Sc ⦘.

(* TODO : prbly just `sb` in the second disjunct *)
Definition cf_imm : relation eventid :=
  cf \ (sb⁻¹ ⨾ cf ∪ cf ⨾ sb⁻¹).

Record es_consistent {m} :=
  { jf_vis : jf ⊆ sb ∪ vis × E;
    hb_jf_not_cf  : (hb ⨾ jf⁻¹) ∩ cf ≡ ∅₂;
    es_coherent : irreflexive (hb ⨾ (eco m)^?);
    jf_not_cf : jf ∩ cf ≡ ∅₂;
    jfpo_irr :
      irreflexive (jfe ⨾ (sb ∪ jf)＊ ⨾ sb ⨾
                   jfe⁻¹ ⨾ ((sb ∪ jf)＊)⁻¹ ⨾
                   (cf \ (ew ⨾ sb⁼ ∪ sb⁼ ⨾ ew)));
    labeq : dom_rel (cf_imm ∩ same_lab) ⊆₁ R;
    labeq_jf_irr : irreflexive (jf ⨾ cf_imm ⨾ jf⁻¹ ⨾ ew^?);
  }.

(******************************************************************************)
(** ** Properties *)
(******************************************************************************)

Section Properties.
Variable WF : ES.Wf S.
Variable m : model.
Variable ESC : @es_consistent m.

(******************************************************************************)
(** ** Basic properties *)
(******************************************************************************)

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
Proof.
unfold hb; rewrite ct_end at 1; rels.
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

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma rsE : rs ≡ ⦗E⦘ ⨾ rs ⨾ ⦗E⦘.
Proof.
  split; [|basic_solver 12].
  unfold rs.
  rewrite rtE; relsf; unionL.
  { rewrite (ES.sbE WF); basic_solver 21. }
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
rewrite (ES.rfE WF) at 1.
basic_solver 42.
Qed.

Lemma swE : sw ≡ ⦗E⦘ ⨾ sw ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
rewrite swE_right at 1.
hahn_frame.
unfold sw.
rewrite releaseE.
rewrite (dom_l (ES.rfE WF)).
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

(******************************************************************************)
(** ** Domains and codomains  *)
(******************************************************************************)

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
rewrite (ES.rfD WF) at 1.
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
(** ** Alternative representations of relations *)
(******************************************************************************)

Lemma rs_alt : rs ≡ ⦗E ∩₁ W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗E ∩₁ W⦘ ⨾ (rf ⨾ rmw)＊.
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

Lemma sw_alt : sw ≡ release ⨾ rf ⨾ (sb ⨾ ⦗E ∩₁ F⦘)^? ⨾ ⦗E ∩₁ FR ∩₁ Acq⦘.
Proof.
  rewrite swD.
  unfold sw.
  rewrite releaseD.
  rewrite (ES.sbE WF), (ES.rfE WF).
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
(** ** Consistent rf properties *)
(******************************************************************************)

Lemma jf_in_rf : jf ⊆ rf.
Proof.
  unfold ES.rf.
  generalize ESC.(jf_not_cf).
  basic_solver.
Qed.

Lemma rf_complete : E ∩₁ R ⊆₁ codom_rel rf.
Proof. rewrite <- jf_in_rf. apply WF. Qed.

End Properties.

End Consistency.