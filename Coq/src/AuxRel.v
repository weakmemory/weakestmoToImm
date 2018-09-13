From hahn Require Import Hahn.

Set Implicit Arguments.

Section AuxRel.

  Variables A B : Type.
  Variable cond : A -> Prop.
  Variable f : A -> B.
  Variable s : A -> Prop.
  Variables r r' : relation A.

  Definition eq_class_rel : relation A := (r ∪ r⁻¹) ^?.
  
  Definition set_image (x : B) : Prop :=
    exists y,
      << INS : s y >> /\
      << IMG : x = f y >>.
End AuxRel.

Notation "a ⁼" := (eq_class_rel a) (at level 1, format "a ⁼").
Notation "a ^=" := (eq_class_rel a) (at level 1, only parsing).
Notation "f ∘ s" := (set_image f s) (at level 1, only parsing).

Hint Unfold eq_class_rel set_image : unfolderDb. 

