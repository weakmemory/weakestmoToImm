Require Import Program.Basics.
From hahn Require Import Hahn.

Set Implicit Arguments.

Section AuxRel.

  Variables A B : Type.
  Variable cond : A -> Prop.
  Variable f : A -> B.
  Variables s s' : A -> Prop.
  Variables r r' : relation A.

  Definition eq_class_rel : relation A := (r ∪ r⁻¹) ^?.
  
  Definition img_rel : A -> B -> Prop :=
    fun x y => y = f x.
End AuxRel.

Definition eq_opt {A} (a: option A) : A -> Prop := fun b => 
  match a with
  | None => False
  | Some a => eq a b
  end.
  
Definition compl_rel {A} (r : relation A) := fun a b => ~ r a b.

Definition eq_dom {A B} (s : A -> Prop) (f g: A -> B) := 
  forall (x: A) (SX: s x), f x = g x. 

Definition inj_dom {A B} (s : A -> Prop) (f: A -> B) :=
  forall (x y : A) (SY: s y) (EQ : f x = f y),
    x = y.

Definition restr_fun {A B} (s : A -> Prop) (f : A -> B) (g : A -> B) := fun x =>
  if excluded_middle_informative (s x) then f x else g x.

Notation "a ⁼" := (eq_class_rel a) (at level 1, format "a ⁼").
Notation "a ^=" := (eq_class_rel a) (at level 1, only parsing).
Notation "f □₁ s" := (set_collect f s) (at level 39).
Notation "f □ r"  := (collect_rel f r) (at level 45).
Notation "↑ f" := (img_rel f) (at level 1, format "↑ f").

Hint Unfold eq_opt compl_rel eq_class_rel : unfolderDb. 

Section Props.

Variables A B : Type.
Variable f g : A -> B.
Variable a : A.
Variable b : B.
Variables s s' s'' : A -> Prop.
Variables q q' : A -> Prop.
Variables r r' : relation A.

Lemma seq_eqv_cross_l : ⦗q⦘ ⨾ s × s' ≡ (q ∩₁ s) × s'.
Proof. basic_solver. Qed.

Lemma seq_eqv_cross_r : s × s' ⨾ ⦗q'⦘ ≡ s × (q' ∩₁ s').
Proof. basic_solver. Qed.

Lemma seq_eqv_cross : ⦗q⦘ ⨾ s × s' ⨾ ⦗q'⦘ ≡ (q ∩₁ s) × (q' ∩₁ s').
Proof. basic_solver. Qed.

Lemma transp_singl_rel (x y : A) : (singl_rel x y)⁻¹ ≡ singl_rel y x.
Proof. basic_solver. Qed.

Lemma set_compl_inter_id : set_compl s ∩₁ s ≡₁ ∅.
Proof. basic_solver. Qed.

Lemma max_elt_eqv_rel : set_compl s ⊆₁ max_elt ⦗s⦘.
Proof. basic_solver. Qed.

Lemma max_elt_cross : set_compl s ⊆₁ max_elt (s × s'). 
Proof. basic_solver. Qed.
  
Lemma seq_codom_dom_inter : codom_rel r ∩₁ dom_rel r' ≡₁ ∅ -> r ⨾ r' ≡ ∅₂.
Proof.
  unfold set_equiv, set_subset; ins; desf. 
  unfold same_relation; splits; [|basic_solver].
  unfold seq, inclusion. 
  intros x y [z HH]. 
  specialize (H z).
  apply H. 
  basic_solver.
Qed.

Lemma set_subset_inter_l (LL : s ⊆₁ s'' \/ s' ⊆₁ s'') :
  s ∩₁ s' ⊆₁ s''.
Proof.
  desf.
  all: rewrite LL.
  all: basic_solver.
Qed.

Lemma set_collect_updo (NC : ~ s a) : (upd f a b) □₁ s ≡₁ f □₁ s.
Proof.
  assert (forall x: A, s x -> x <> a). 
  { ins. intros HH. by subst. }
  autounfold with unfolderDb.
  splits; unfold set_subset; ins.
  all: desf; eexists; splits; eauto.
  all: rewrite updo; auto.
Qed.

Lemma set_collect_eqv : f □ ⦗ s ⦘ ≡ ⦗ f □₁ s ⦘.
Proof.
  autounfold with unfolderDb.
  splits; ins; desf; eauto.
  eexists. eexists.
  splits; eauto.
Qed.

Lemma set_collect_dom : f □₁ dom_rel r ≡₁ dom_rel (f □ r).
Proof.
  autounfold with unfolderDb.
  split; intros x HH; desf; eauto.
  repeat eexists. eauto.
Qed.

(* Note that inclusion in other direction doesn't hold.
   For example, if `f` is constant and `a <> b`, then
   `f □₁ (eq a ∩₁ eq b) ≡₁ ∅` and `f □₁ eq a ∩₁ f □₁ eq b ≡₁ f □₁ eq a`.
 *)
Lemma set_collect_inter : f □₁ (s ∩₁ s') ⊆₁ f □₁ s ∩₁ f □₁ s'.
Proof. basic_solver. Qed.

Lemma collect_seq_eqv_l rr : f □ ⦗ s ⦘ ⨾ rr ⊆ ⦗ f □₁ s ⦘ ⨾ (f □ rr).
Proof.
  autounfold with unfolderDb.
  intros x y HH; desf; eauto.
  eexists; splits; eauto.
Qed.

Lemma collect_seq_eqv_r rr : f □ rr ⨾ ⦗ s' ⦘ ⊆ (f □ rr) ⨾ ⦗ f □₁ s' ⦘.
Proof.
  autounfold with unfolderDb.
  intros x y HH; desf; eauto.
  eexists; splits; eauto.
Qed.

Lemma collect_seq_eqv_lr rr :
  f □ ⦗ s ⦘ ⨾ rr ⨾ ⦗ s' ⦘ ⊆
  ⦗ f □₁ s ⦘ ⨾ (f □ rr) ⨾ ⦗ f □₁ s' ⦘.
Proof. rewrite collect_seq_eqv_l. by rewrite collect_seq_eqv_r. Qed.

Lemma collect_eq e :f □₁ eq e ≡₁ eq (f e).
Proof. basic_solver. Qed.

Lemma collect_rel_seq_l
      (INJ : inj_dom (codom_rel r) f) : 
  f □ (r ⨾ r') ≡ (f □ r) ⨾ (f □ r').
Proof.
  autounfold with unfolderDb.
  split; ins; desf; eauto.
  all: repeat eexists; eauto.
  apply INJ in H1; desf.
  red. eauto.
Qed.

Lemma collect_rel_seq_r
      (INJ : inj_dom (dom_rel r') f) : 
  f □ (r ⨾ r') ≡ (f □ r) ⨾ (f □ r').
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
  f □ (restr_rel s r) ≡ restr_rel (f □₁ s) (f □ r).
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
  f □ (⦗ s ⦘ ⨾ r ⨾ ⦗ s' ⦘) ≡ g □ (⦗ s ⦘ ⨾ r ⨾ ⦗ s' ⦘).
Proof.
  ins.
  autounfold with unfolderDb.
  splits; ins; desf; repeat eexists; eauto; 
  symmetry; [apply (EQs z) | apply (EQs' y')]; auto.
Qed.

Lemma collect_rel_restr_eq_dom (HH : eq_dom s f g) :
  f □ (restr_rel s r) ≡ g □ (restr_rel s r).
Proof.
  rewrite restr_relE.
  apply collect_rel_eq_dom; auto.
Qed.

Lemma restr_set_union :
  restr_rel (s ∪₁ s') r ≡
    restr_rel s r ∪ restr_rel s' r ∪
    ⦗ s ⦘ ⨾ r ⨾ ⦗ s' ⦘ ∪ ⦗ s' ⦘ ⨾ r ⨾ ⦗ s ⦘.
Proof.
  autounfold with unfolderDb.
  splits; ins; desf; splits; eauto.
  { left. left. left. auto. }
  { right. eexists. splits; eauto. }
  { left. right. eexists. splits; eauto. }
  { left. left. right. auto. }
Qed.

Lemma restr_set_inter :
  restr_rel (s ∩₁ s') r ≡
    restr_rel s r ∩ restr_rel s' r.
Proof.
  autounfold with unfolderDb.
  splits; ins; desf. 
Qed.

Lemma restr_irrefl_eq (IRRFLX: irreflexive r):
  forall x:A, (restr_rel (eq x) r) ≡ ∅₂.
Proof. basic_solver. Qed.

Lemma eq_dom_union: eq_dom (s ∪₁ s') f g <-> eq_dom s f g /\ eq_dom s' f g.
Proof. 
  split.
  { ins. unfold eq_dom in *. 
    splits; ins; apply (H x); basic_solver. }
  intros [Hs Hs'].
  unfold eq_dom in *. ins. 
  unfold set_union in SX. 
  desf; basic_solver.
Qed.  

Lemma rt_dom_ri (HH : r ⊆ ⦗ s ⦘ ⨾ r) : r＊ ⨾ ⦗ s ⦘ ⊆ (r ⨾ ⦗ s ⦘)＊.
Proof.
  rewrite rtE at 1.
  rewrite seq_union_l.
  apply inclusion_union_l; [basic_solver|].
  rewrite HH at 1.
  rewrite clos_trans_rotl.
  rewrite !seqA.
  rewrite <- ct_end.
  rewrite inclusion_t_rt.
  basic_solver.
Qed. 

Lemma clos_trans_union_ext (Hrr : r ⨾ r ≡ ∅₂) (Hrr' : r ⨾ r' ≡ ∅₂) : 
  (r ∪ r')⁺ ≡ r'⁺ ∪ r'＊ ⨾ r.
Proof. 
  rewrite ct_unionE.
  arewrite ((r ⨾ r'＊)⁺ ≡ r); auto. 
  unfold same_relation; splits.
  { unfold inclusion; ins. 
    induction H. 
    { eapply seq_rtE_r in H. 
      unfold union in H; desf.
      repeat unfold seq in *; desf. 
      exfalso. 
      eapply Hrr'. 
      eexists; splits; eauto. }
    exfalso. 
    eapply Hrr. 
    unfold seq; exists y; splits; eauto. }
  rewrite seq_rtE_r.
  unfold inclusion; ins. 
  eapply clos_trans_mori.
  2: { eapply t_step. eauto. }
  apply inclusion_union_r1.
Qed.   

End Props.

Require Import Setoid.

Add Parametric Morphism A : (@eq_class_rel A) with signature 
  inclusion ==> inclusion as eq_class_mori.
Proof.
  red; ins; do 2 autounfold with unfolderDb in *; basic_solver.
Qed.

Add Parametric Morphism A : (@eq_class_rel A) with signature 
  same_relation ==> same_relation as eq_class_more.
Proof.
  red; ins; do 2 autounfold with unfolderDb in *; basic_solver.
Qed.

Add Parametric Morphism A : (@compl_rel A) with signature 
  same_relation ==> same_relation as compl_more.
Proof. red; autounfold with unfolderDb; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@compl_rel A) with signature 
  inclusion --> inclusion as compl_mori.
Proof. red; autounfold with unfolderDb; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A B : (@inj_dom A B) with signature 
  set_equiv ==> eq ==> iff as inj_dom_more.
Proof. 
  intros s s' Heq f. red. 
  unfold inj_dom in *.
  splits; ins; specialize (H x y); apply H; auto; apply Heq; auto.
Qed.

Add Parametric Morphism A B : (@inj_dom A B) with signature 
  set_subset --> eq ==> impl as inj_dom_mori.
Proof. 
  intros s s' Heq f Hinj. 
  unfold inj_dom in *. ins.
  apply Hinj; auto.
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