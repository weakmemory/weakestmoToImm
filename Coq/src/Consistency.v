From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events.
Require Import AuxRel EventStructure.

Set Implict Arguments.

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

Notation "'Pln'" := (is_only_pln lab).
Notation "'Rlx'" := (is_rlx lab).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).
Notation "'Sc'" := (is_sc lab).

Definition same_lab x y := lab x = lab y.

Definition vis :=
  codom_rel (cc ∩ (ew ⨾ sb ⁼)).

(* release sequence *)
Definition rs := ⦗E ∩₁ W⦘ ⨾ (sb ∩ same_loc)^? ⨾ ⦗E ∩₁ W⦘ ⨾ (rf ⨾ rmw)＊.

Definition release := ⦗E ∩₁ Rel⦘ ⨾ (⦗E ∩₁ F⦘ ⨾ sb)^? ⨾ rs.

(* synchronizes with *)
Definition sw := release ⨾ rf ⨾ (sb ⨾ ⦗E ∩₁ F⦘)^? ⨾ ⦗E ∩₁ Acq⦘.

(* happens before *)
Definition hb : relation eventid := (sb ∪ sw)⁺.

Definition co_strong : relation eventid :=
  ⦗ W ⦘ ⨾ hb ⨾ ⦗ W ⦘ ∩ same_loc.

Definition mco (m : model) : relation eventid :=
  match m with
  | Weakest   => co_strong 
  | Weakestmo => co
  end.

Definition mfr (m : model) : relation eventid :=
  (rf⁻¹ ⨾ mco m) \ cf^?.

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

(******************************************************************************)
(** ** Relations in graph *)
(******************************************************************************)

Lemma rsE : rs ≡ ⦗E⦘ ⨾ rs ⨾ ⦗E⦘.
Proof.
unfold rs.
split; [|basic_solver 12].
rewrite rtE; relsf; unionL.
rewrite (ES.sbE WF); basic_solver 21.
rewrite (dom_r (ES.rmwE WF)) at 1.
rewrite <- !seqA.
sin_rewrite inclusion_ct_seq_eqv_r.
rewrite !seqA.
arewrite (⦗E⦘ ⨾ ⦗E ∩₁ W⦘ ≡ ⦗E ∩₁ W⦘ ⨾ ⦗E⦘) by basic_solver.
hahn_frame.
rewrite ct_begin.
rewrite (dom_l (ES.sbE WF)) at 1.
rewrite (dom_l (ES.rfE WF)) at 1.
basic_solver 25.
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