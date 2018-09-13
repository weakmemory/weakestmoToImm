From hahn Require Import Hahn.

Set Implicit Arguments.

Section AuxRel.

  Variables A B : Type.
  Variable cond : A -> Prop.
  Variable f : A -> B.
  Variables s s' : A -> Prop.
  Variables r r' : relation A.

  Definition eq_class_rel : relation A := (r ∪ r⁻¹) ^?.
  
  Definition set_image (x : B) : Prop :=
    exists y,
      << INS : s y >> /\
      << IMG : x = f y >>.

  Definition rel_image (x x' : B) : Prop :=
    exists y y',
      << INR  : r y y' >> /\
      << IMG  : x  = f y >> /\
      << IMG' : x' = f y' >>.
  
End AuxRel.

Notation "a ⁼" := (eq_class_rel a) (at level 1, format "a ⁼").
Notation "a ^=" := (eq_class_rel a) (at level 1, only parsing).
Notation "f ∘₁ s" := (set_image f s) (at level 10).
Notation "f ∘ r"  := (rel_image f r) (at level 10).

Hint Unfold eq_class_rel set_image rel_image : unfolderDb. 

Section Props.

Variables A B : Type.
Variable cond : A -> Prop.
Variable f : A -> B.
Variable a : A.
Variable b : B.
Variables s s' : A -> Prop.
Variables r r' : relation A.

Lemma set_image_union : f ∘₁ (s ∪₁ s') ≡₁ f ∘₁ s ∪₁ f ∘₁ s'.
Proof. basic_solver. Qed.

Lemma set_image_eq : f ∘₁ (eq a) ≡₁ eq (f a).
Proof. basic_solver. Qed.

Lemma set_image_updo (NC : ~ s a) : (upd f a b) ∘₁ s ≡₁ f ∘₁ s.
Proof.
  autounfold with unfolderDb.
  split; red; ins; desf.
  all: eexists; splits; eauto.
  all: rewrite updo; auto.
  all: by intros HH; subst.
Qed.

End Props.


