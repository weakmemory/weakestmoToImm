From hahn Require Import Hahn.
From imm Require Import Events Execution imm_hb imm.
Require Import EventStructure Consistency.

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

Lemma AvfE (RF : rf ≡ <| E |> ;; rf)
      (HB : hb ≡ <| E |> ;; hb)
      (SC : sc ≡ <| E |> ;; sc)
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

Definition Svf (m : model) (S : ES.t) :=
  Avf S.(ES.acts_set) S.(ES.lab) S.(ES.jf) S.(Consistency.hb) (Consistency.psc S m).

(* Section GvfProperties. *)
(* Variable G : execution. *)
(* Variable WF : Wf G. *)

(* Notation "'E'" := G.(acts_set). *)
(* Notation "'psc'" := G.(imm.psc). *)
(* Notation "'hb'" := G.(imm_hb.hb). *)
(* Notation "'rf'" := G.(rf). *)
(* Notation "'lab'" := G.(lab). *)
(* Notation "'vf'" := (Gvf G). *)
(* Notation "'W'" := (fun a => is_true (is_w lab a)). *)
(* Notation "'F'" := (fun a => is_true (is_f lab a)). *)
(* Notation "'Sc'" := (fun a => is_true (is_sc lab a)). *)

(* Lemma GvfE : vf ≡ ⦗ E ⦘ ⨾ vf ⨾ ⦗ E ⦘. *)
(* Proof. *)
(*   split; [|basic_solver]. *)
(*   unfold Gvf, Avf. *)
(*   rewrite (wf_rfE WF) at 1. *)
(*   rewrite (wf_hbE WF) at 1 2. *)
(*   rewrite (wf_pscE WF) at 1. *)
(*   basic_solver 21. *)
(* Qed. *)

(* Lemma vf_hb_irr l WF WF_SC CSC COH ACYC_EXT: irreflexive (vf ⨾ hb). *)
(* Proof. *)
(*   unfold vf. *)
(*   arewrite_id ⦗W_ l⦘. *)
(*   arewrite_id ⦗F ∩₁ Sc⦘. *)
(*   rels. *)

(*   arewrite (rf^? ⊆ eco^?). *)
(*   generalize (eco_trans WF); ins; relsf. *)
(*   rewrite (crE sc). *)

(*   generalize (@hb_trans G); ins; relsf. *)

(*   relsf; repeat (splits; try apply irreflexive_union). *)
(*   - *)
(*       by rotate 1; apply COH. *)
(*   -  *)
(*     rewrite crE at 1; relsf; repeat (splits; try apply irreflexive_union). *)
(*     * rotate 1; relsf. *)
(*       rewrite (wf_scD WF_SC). *)
(*       rotate 1. *)
(*       sin_rewrite (f_sc_hb_f_sc_in_sc WF WF_SC ACYC_EXT). *)
(*       destruct WF_SC; relsf. *)
(*     *  *)
(*       rewrite (wf_scD WF_SC), !seqA. *)
(*       rewrite crE; relsf; apply irreflexive_union; splits; *)
(*         [rewrite (dom_r (wf_ecoD WF)); type_solver|]. *)
(*       revert CSC; unfold coh_sc; basic_solver 21. *)
(* Qed. *)

(* Lemma Gvf_hb_sc_hb_irr WF WF_SC CSC COH ACYC_EXT l: *)
(*   irreflexive (vf ⨾ hb ⨾ (sc ⨾ hb)^?). *)
(* Proof. *)
(* case_refl _. *)
(* apply (vf_hb_irr WF WF_SC CSC COH ACYC_EXT). *)
(* arewrite (vf ⨾ hb ⨾ sc ⊆ vf). *)
(* generalize (@vf_hb_sc_hb l WF WF_SC ACYC_EXT); basic_solver 21. *)
(* apply (vf_hb_irr WF WF_SC CSC COH ACYC_EXT). *)
(* Qed. *)

(* End GvfProperties. *)