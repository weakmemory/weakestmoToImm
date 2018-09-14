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

Definition injective {A B} (f: A -> B) := forall x y: A, f(x) = f(y) -> x = y.

Notation "a ⁼" := (eq_class_rel a) (at level 1, format "a ⁼").
Notation "a ^=" := (eq_class_rel a) (at level 1, only parsing).
Notation "f ∘₁ s" := (set_collect f s) (at level 10).
Notation "f ∘ r"  := (collect_rel f r) (at level 10).

Hint Unfold eq_class_rel : unfolderDb. 

Section Props.

Variables A B : Type.
(* Variable cond : A -> Prop. *)
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

Lemma set_collect_eqv : f ∘ <| s |> ≡ <| f ∘₁ s |>.
Proof.
  autounfold with unfolderDb.
  splits; ins; desf; eauto.
  eexists. eexists.
  splits; eauto.
Qed.

Lemma collect_rel_seq
  (INJ: injective f) : 
  (f ∘ (r ;; r') ≡ (f ∘ r) ;; (f ∘ r')).
Proof.
  autounfold with unfolderDb.
  split; ins; desf; eauto.
  all: repeat eexists; eauto.
  apply INJ in H1. desf.
Qed.

Lemma eqv_rel_union : <| s ∪₁ s' |> ≡ <| s |> ∪ <| s' |>.
Proof. clear. admit. 
Admitted.

Lemma set_collect_restr : f ∘₁ s ≡₁ g ∘₁ s -> f ∘ (restr_rel s r) ≡ g ∘ (restr_rel s r).
Proof. clear. admit. 
Admitted.

End Props.