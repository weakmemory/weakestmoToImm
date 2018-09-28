From hahn Require Import Hahn.
From imm Require Import Events Execution imm_hb imm.
Require Import EventStructure Consistency.

Set Implicit Arguments.

Section Vf.
  Variable A : Type.
  Variable lab : A -> label.
  Variable rf : relation A.
  Variable hb : relation A.
  Variable sc : relation A.

  Notation "'F'" := (fun a => is_true (is_f lab a)).
  Notation "'Sc'" := (fun a => is_true (is_sc lab a)).
  
  Definition vf : relation A := rf^? ⨾ (hb ⨾ ⦗ F∩₁Sc ⦘)^? ⨾ sc^? ⨾ hb^?.
End Vf.

Definition Gvf (G : execution) :=
  vf G.(lab) G.(rf) G.(imm_hb.hb) G.(imm.psc).

Definition Svf (m : model) (S : ES.t) :=
  vf S.(ES.lab) S.(ES.jf) S.(Consistency.hb) (Consistency.psc S m).