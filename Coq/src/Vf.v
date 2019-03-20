From hahn Require Import Hahn.
From imm Require Import Events Execution Execution_eco imm_hb imm AuxRel.
(* Require Import EventStructure Consistency. *)

Set Implicit Arguments.

Section Vf.
Variable A : Type.
Variable E : A -> Prop.
Variable lab : A -> label.
Variable rf : relation A.
Variable hb : relation A.
Variable sc : relation A.

Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).
  
Definition Avf : relation A := ⦗ W ⦘ ⨾ rf^? ⨾ (hb ⨾ ⦗ F∩₁Sc ⦘)^? ⨾ sc^? ⨾ hb^? ⨾ ⦗ E ⦘.

Lemma Avf_dom : Avf ≡ ⦗ W ⦘ ⨾ Avf.
Proof. unfold Avf. seq_rewrite seq_eqvK. done. Qed.

Lemma AvfE (RF : rf ≡ ⦗ E ⦘ ⨾ rf)
      (HB : hb ≡ ⦗ E ⦘ ⨾ hb)
      (SC : sc ≡ ⦗ E ⦘ ⨾ sc)
  : Avf ≡ ⦗ E ⦘ ⨾ Avf ⨾ ⦗ E ⦘.
Proof.
  split; [|basic_solver].
  unfold Avf.
  rewrite RF at 1.
  rewrite HB at 1 2.
  rewrite SC at 1.
  basic_solver 21.
Qed.
End Vf.

Definition Gvf (G : execution) :=
  Avf G.(acts_set) G.(lab) G.(rf) G.(imm_hb.hb) G.(imm.psc).

(* Definition Svf (m : model) (S : ES.t) := *)
(*   Avf S.(ES.acts_set) S.(ES.lab) S.(ES.jf) S.(Consistency.hb) (Consistency.psc S m). *)

Section GvfProperties.
Variable G : execution.
Variable WF : Wf G.
Variable COH : coherence G.
Variable COMP : complete G.
Variable ACYC_EXT : acyc_ext G.

Notation "'E'" := G.(acts_set).
Notation "'psc'" := G.(imm.psc).
Notation "'hb'" := G.(imm_hb.hb).
Notation "'rf'" := G.(rf).
Notation "'eco'" := G.(Execution_eco.eco).
Notation "'lab'" := G.(lab).
Notation "'vf'" := (Gvf G).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'ar'" := (imm.ar G).

Lemma GvfE : vf ≡ ⦗ E ⦘ ⨾ vf ⨾ ⦗ E ⦘.
Proof.
  apply AvfE.
  all: eapply dom_l.
  { apply WF.(wf_rfE). }
  { apply WF.(wf_hbE). }
  apply WF.(wf_pscE).
Qed.

Lemma Gvf_hb_irr : irreflexive (vf ⨾ hb).
Proof.
  unfold Gvf, Avf.
  arewrite_id ⦗W⦘.
  arewrite_id ⦗E⦘.
  arewrite_id ⦗F ∩₁ Sc⦘.
  rels.
  
  arewrite (rf ⊆ eco).
  generalize (Execution_eco.eco_trans WF); ins; relsf.

  generalize (@imm_hb.hb_trans G); ins; relsf.

  assert (irreflexive hb) by (by apply hb_irr).
  assert (irreflexive (eco ⨾ hb)).
  { rotate 1. apply COH. }
  assert (irreflexive (eco ⨾ psc ⨾ hb)).
  { rewrite (wf_pscD), !seqA.
    rewrite (dom_r (wf_ecoD WF)). type_solver. }
  assert (irreflexive (psc ⨾ hb)).
  { unfold imm.psc.
    arewrite_id ⦗F ∩₁ Sc⦘.
    relsf.
    rotate 2.
    generalize (@imm_hb.hb_trans G); ins; relsf. }
  assert (irreflexive (hb ⨾ psc ⨾ hb)).
  { rotate 2.
    generalize (@imm_hb.hb_trans G); ins; relsf. }

  repeat (rewrite crE; relsf; apply irreflexive_union; split; auto).
  rewrite wf_pscD, !seqA.
  rotate 2.
  arewrite (⦗F ∩₁ Sc⦘ ⨾ hb ⨾ eco ⨾ hb ⨾ ⦗F ∩₁ Sc⦘ ≡ psc).
  arewrite (psc ⊆ ar).
  arewrite (ar ⊆ ar⁺). rewrite ct_ct.
  apply ACYC_EXT.
Qed.

(* Lemma Gvf_hb_sc_hb_irr : irreflexive (vf ⨾ hb ⨾ (psc ⨾ hb)^?). *)
(* Proof. *)
(*   case_refl _. *)
(*   { apply Gvf_hb_irr. } *)
(*   arewrite (vf ⨾ hb ⨾ psc ⊆ vf). *)
(*   2: by apply Gvf_hb_irr. *)
(*   unfold Gvf, Avf. *)
(*   arewrite_id ⦗E⦘ at 1. rels. *)
(*   rewrite (dom_r WF.(wf_pscE)) at 2. *)
(*   arewrite ((hb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ psc^? ⨾ hb^? ⨾ hb ⨾ psc ⊆ *)
(*                             (hb ⨾ ⦗F ∩₁ Sc⦘)^? ⨾ psc^? ⨾ hb^?). *)
(*   2: done. *)
(*   rewrite !crE. relsf. *)
(* Qed. *)

End GvfProperties.