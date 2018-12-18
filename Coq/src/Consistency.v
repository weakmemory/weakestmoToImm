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

Notation "'jfe'" := S.(ES.jfe).
Notation "'rfe'" := S.(ES.rfe).
Notation "'coe'" := S.(ES.coe).
Notation "'jfi'" := S.(ES.jfi).
Notation "'rfi'" := S.(ES.rfi).
Notation "'coi'" := S.(ES.coi).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).

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

(* immediate conflict *)

Definition icf : relation eventid :=
  cf \ (sb⁻¹ ⨾ cf ∪ cf ⨾ sb).

(* causality conflict  *)

Definition cc := 
  cf ∩ (jfe ⨾ (sb ∪ jf)＊ ⨾ jfe ⨾ sb^?). 

(* visible events *)

Definition vis e := 
  ⟪ EE : E e ⟫ /\ ⟪ CCEW : cc ⨾ ⦗ eq e ⦘ ⊆ ew ⨾ sb⁼ ⟫.

(* release sequence *)

Definition rs := ⦗E ∩₁ W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (rf ⨾ rmw)＊.

Definition release := ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ sb)^? ⨾ rs.

(* synchronizes with *)

Definition sw := release ⨾ rf ⨾ (sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘.

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

Definition psc (m : model) : relation eventid :=
  ⦗ Sc ⦘ ⨾ hb ⨾ eco m ⨾ hb ⨾ ⦗ Sc ⦘.

Record es_consistent {m} :=
  { ecf_irf : irreflexive ecf;
    jf_necf : jf ∩ ecf ≡ ∅₂; 
    jfe_vis : dom_rel jfe ⊆₁ vis;
    (* jf_not_cf : jf ∩ cf ≡ ∅₂; *)
    (* hb_jf_not_cf  : (hb ⨾ jf⁻¹) ∩ cf ≡ ∅₂; *)
    coh : irreflexive (hb ⨾ (eco m)^?);
    (* jfpo_irr : *)
    (*   irreflexive (jfe ⨾ (sb ∪ jf)＊ ⨾ sb ⨾ *)
    (*                jfe⁻¹ ⨾ ((sb ∪ jf)＊)⁻¹ ⨾ *)
    (*                (cf \ (ew ⨾ sb⁼ ∪ sb⁼ ⨾ ew))); *)
    icf_lab : dom_rel (icf ∩ same_lab) ⊆₁ R;
    icf_jf : irreflexive (jf ⨾ icf ⨾ jf⁻¹ ⨾ ew^?);
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

Lemma cf_in_ecf : cf ⊆ ecf.
Proof.
  unfold ecf. rewrite !crE, !seq_union_l, !seq_union_r.
  repeat unionR left. basic_solver 10.
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

Lemma ccW : cc ≡ ⦗W⦘ ⨾ cc. 
Proof. 
  unfold cc. 
  rewrite interC.
  rewrite <- AuxRel.seq_eqv_inter_ll.
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
(** ** Alternative representations of sets and relations *)
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
(** ** Alternative representations of properties *)
(******************************************************************************)

Lemma jf_necf_jf_ncf : jf ∩ ecf ≡ ∅₂ -> jf ∩ cf ≡ ∅₂.
Proof. 
  intros [JFnECF _]. 
  split; [|basic_solver].
  by sin_rewrite cf_in_ecf.
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
(** ** Consistent rf properties *)
(******************************************************************************)

Variable ESC : @es_consistent m.

Lemma jf_in_rf : jf ⊆ rf.
Proof.
  unfold ES.rf.
  generalize (jf_necf_jf_ncf ESC.(jf_necf)).
  basic_solver.
Qed.

Lemma rf_complete : E ∩₁ R ⊆₁ codom_rel rf.
Proof. rewrite <- jf_in_rf. apply WF. Qed.

End Properties.

End Consistency.