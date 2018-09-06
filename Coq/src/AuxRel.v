From hahn Require Import Hahn.

Set Implicit Arguments.

Section AuxRel.

  Variables A B : Type.
  Variable cond : A -> Prop.
  Variable f : A -> B.
  Variables r r' : relation A.

  Definition eq_class_rel : relation A := (r ∪ r⁻¹) ^?.
End AuxRel.

Notation "a ⁼" := (eq_class_rel a) (at level 1, format "a ⁼").
Notation "a ^=" := (eq_class_rel a) (at level 1, only parsing).

Hint Unfold eq_class_rel : unfolderDb. 