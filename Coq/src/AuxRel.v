From hahn Require Import Hahn.

Set Implicit Arguments.

Section AuxRel.

  Variables A B : Type.
  Variable cond : A -> Prop.
  Variable f : A -> B.
  Variables s s' : A -> Prop.
  Variables r r' : relation A.

  Definition eq_class_rel : relation A := (r ∪ r⁻¹) ^?.
    
End AuxRel.

Definition inj_dom {A B} (s : A -> Prop) (f: A -> B) :=
  forall (x y : A) (SX : s y) (EQ : f x = f y),
    x = y.

Notation "a ⁼" := (eq_class_rel a) (at level 1, format "a ⁼").
Notation "a ^=" := (eq_class_rel a) (at level 1, only parsing).
Notation "f ∘₁ s" := (set_collect f s) (at level 45).
Notation "f ∘ r"  := (collect_rel f r) (at level 45).

Hint Unfold eq_class_rel : unfolderDb. 

Section Props.

Variables A B : Type.
Variable f g : A -> B.
Variable a : A.
Variable b : B.
Variables s s' : A -> Prop.
Variables r r' : relation A.

Lemma set_collect_updo (NC : ~ s a) : (upd f a b) ∘₁ s ≡₁ f ∘₁ s.
Proof.
  assert (forall x: A, s x -> x <> a). 
  { ins. intros HH. by subst. }
  autounfold with unfolderDb.
  splits; unfold set_subset; ins.
  all: desf; eexists; splits; eauto.
  all: rewrite updo; auto.
Qed.

Lemma set_collect_eqv : f ∘ ⦗ s ⦘ ≡ ⦗ f ∘₁ s ⦘.
Proof.
  autounfold with unfolderDb.
  splits; ins; desf; eauto.
  eexists. eexists.
  splits; eauto.
Qed.

Lemma collect_rel_seq
      (INJ : inj_dom (codom_rel r) f) : 
  f ∘ (r ⨾ r') ≡ (f ∘ r) ⨾ (f ∘ r').
Proof.
  autounfold with unfolderDb.
  split; ins; desf; eauto.
  all: repeat eexists; eauto.
  apply INJ in H1; desf.
  red. eauto.
Qed.

Lemma set_collect_restr (INJ: inj_dom s f) :
  f ∘ (restr_rel s r) ≡ restr_rel (f ∘₁ s) (f ∘ r).
Proof.
  autounfold with unfolderDb.
  splits; ins; desf; splits; eauto.
  assert (x' = y1) by (apply INJ; auto). subst.
  assert (y' = y0) by (apply INJ; auto). subst.
  eexists. eexists.
  splits; eauto.
Qed.

Lemma set_collect_restr_eq (HH : f ∘₁ s ≡₁ g ∘₁ s) :
  f ∘ (restr_rel s r) ≡ g ∘ (restr_rel s r).
Proof.
Admitted.

End Props.