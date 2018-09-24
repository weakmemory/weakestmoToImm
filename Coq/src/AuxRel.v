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

Definition eq_dom {A B} (s : A -> Prop) (f g: A -> B) := 
  forall (x: A) (SX: s x), f x = g x. 

Definition inj_dom {A B} (s : A -> Prop) (f: A -> B) :=
  forall (x y : A) (SY: s y) (EQ : f x = f y),
    x = y.

Notation "a ⁼" := (eq_class_rel a) (at level 1, format "a ⁼").
Notation "a ^=" := (eq_class_rel a) (at level 1, only parsing).
Notation "f ∘₁ s" := (set_collect f s) (at level 39).
Notation "f ∘ r"  := (collect_rel f r) (at level 45).

Hint Unfold eq_class_rel : unfolderDb. 

Section Props.

Variables A B : Type.
Variable f g : A -> B.
Variable a : A.
Variable b : B.
Variables s s' : A -> Prop.
Variables q q' : A -> Prop.
Variables r r' : relation A.

Lemma seq_eqv_cross_l : ⦗q⦘ ⨾ s × s' ≡ (q ∩₁ s) × s'.
Proof. basic_solver. Qed.
Lemma seq_eqv_cross_r : s × s' ⨾ ⦗q'⦘ ≡ s × (q' ∩₁ s').
Proof. basic_solver. Qed.
Lemma seq_eqv_cross : ⦗q⦘ ⨾ s × s' ⨾ ⦗q'⦘ ≡ (q ∩₁ s) × (q' ∩₁ s').
Proof. basic_solver. Qed.

Lemma set_compl_inter_id : set_compl s ∩₁ s ≡₁ ∅.
Proof. basic_solver. Qed.

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

Lemma collect_rel_seq_l
      (INJ : inj_dom (codom_rel r) f) : 
  f ∘ (r ⨾ r') ≡ (f ∘ r) ⨾ (f ∘ r').
Proof.
  autounfold with unfolderDb.
  split; ins; desf; eauto.
  all: repeat eexists; eauto.
  apply INJ in H1; desf.
  red. eauto.
Qed.

Lemma collect_rel_seq_r
      (INJ : inj_dom (dom_rel r') f) : 
  f ∘ (r ⨾ r') ≡ (f ∘ r) ⨾ (f ∘ r').
Proof.
  autounfold with unfolderDb.
  split; ins; desf; eauto.
  all: repeat eexists; eauto.
  symmetry in H1.
  apply INJ in H1; desf.
  red. eexists. eauto.
Qed.     

Lemma set_collect_restr : 
  forall (s: A -> Prop) (f: A -> B), inj_dom s f ->
  f ∘ (restr_rel s r) ≡ restr_rel (f ∘₁ s) (f ∘ r).
Proof.
  ins.
  autounfold with unfolderDb.
  splits; ins; desf; splits; eauto.
  assert (x' = y1) by (apply H; auto). subst.
  assert (y' = y0) by (apply H; auto). subst.
  eexists. eexists.
  splits; eauto.
Qed.

Lemma collect_rel_eq_dom : forall (s s': A -> Prop) (EQs: eq_dom s f g) (EQs': eq_dom s' f g),
  f ∘ (<| s |> ;; r ;; <| s' |>) ≡ g ∘ (<| s |> ;; r ;; <| s' |>).
Proof.
  ins.
  autounfold with unfolderDb.
  splits; ins; desf; repeat eexists; eauto; 
  symmetry; [apply (EQs z) | apply (EQs' y')]; auto.
Qed.

Lemma collect_rel_restr_eq_dom (HH : eq_dom s f g) :
  f ∘ (restr_rel s r) ≡ g ∘ (restr_rel s r).
Proof.
  rewrite restr_relE.
  apply collect_rel_eq_dom; auto.
Qed.

Lemma restr_set_union :
  restr_rel (s ∪₁ s') r ≡
    restr_rel s r ∪ restr_rel s' r ∪
    <| s |> ;; r ;; <| s' |> ∪ <| s' |> ;; r ;; <| s |>.
Proof.
  autounfold with unfolderDb.
  splits; ins; desf; splits; eauto.
  { left. left. left. auto. }
  { right. eexists. splits; eauto. }
  { left. right. eexists. splits; eauto. }
  { left. left. right. auto. }
Qed.

Lemma restr_irrefl_eq (IRRFLX: irreflexive r):
  forall x:A, (restr_rel (eq x) r) ≡ ∅₂.
Proof. basic_solver. Qed.


End Props.

Require Import Setoid.

Add Parametric Morphism A B : (@inj_dom A B) with signature 
  set_equiv ==> eq ==> iff as inj_dom_more.
Proof. 
  intros s s' Heq f. red. 
  unfold inj_dom in *.
  splits; ins; specialize (H x y); apply H; auto; apply Heq; auto.
Qed.

Add Parametric Morphism A : (@set_compl A) with signature 
  set_equiv ==> set_equiv as set_compl_more.
Proof. red; autounfold with unfolderDb; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@set_compl A) with signature 
  set_subset --> set_subset as set_compl_mori.
Proof. red; autounfold with unfolderDb; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A B : (@set_collect A B) with signature 
  eq ==> set_equiv ==> set_equiv as set_collect_more.
Proof. red; autounfold with unfolderDb; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A B : (@set_collect A B) with signature 
  eq ==> set_subset ==> set_subset as set_collect_mori.
Proof. red; autounfold with unfolderDb; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@dom_rel A) with signature
   inclusion ==> set_subset as dom_rel_mori.
Proof. red; autounfold with unfolderDb; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@dom_rel A) with signature
   same_relation ==> set_equiv as dom_rel_more.
Proof. red; autounfold with unfolderDb; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@codom_rel A) with signature
   inclusion ==> set_subset as codom_rel_mori.
Proof. red; autounfold with unfolderDb; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@codom_rel A) with signature
   same_relation ==> set_equiv as codom_rel_more.
Proof. red; autounfold with unfolderDb; splits; ins; desf; eauto. Qed.