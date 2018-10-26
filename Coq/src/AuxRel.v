Require Import Program.Basics.
From hahn Require Import Hahn.

Set Implicit Arguments.

Section AuxRel.

  Variables A B : Type.
  Variable cond : A -> Prop.
  Variable f g : A -> B.
  Variables s s' : A -> Prop.
  Variables r r' : relation A.

  Definition clos_sym : relation A := fun x y => r x y \/ r y x. 

  Definition clos_refl_sym : relation A := fun x y => x = y \/ r x y \/ r y x. 

  Definition img_rel : A -> B -> Prop :=
    fun x y => y = f x.

  Definition eq_opt (a: option A) : A -> Prop := fun b => 
  match a with
  | None => False
  | Some a => eq a b
  end.
  
  Definition compl_rel := fun a b => ~ r a b.

  Definition eq_dom := 
    forall (x: A) (SX: s x), f x = g x. 

  Definition inj_dom :=
    forall (x y : A) (SY: s y) (EQ : f x = f y),
      x = y.

  Definition restr_fun := fun x => 
    if excluded_middle_informative (s x) then f x else g x.

End AuxRel.


Notation "⊤₁" := set_full.
Notation "⊤₂" := (fun _ _ => True).

Notation "a ^⋈" := (clos_sym a) (at level 1).
Notation "a ⁼" := (clos_refl_sym a) (at level 1, format "a ⁼").
Notation "a ^=" := (clos_refl_sym a) (at level 1, only parsing).
Notation "f □₁ s" := (set_collect f s) (at level 39).
Notation "f □ r"  := (collect_rel f r) (at level 45).
Notation "↑ f" := (img_rel f) (at level 1, format "↑ f").

Hint Unfold clos_sym clos_refl_sym eq_opt compl_rel : unfolderDb. 

Section Props.

Variables A B : Type.
Variable f g : A -> B.
Variable a : A.
Variable b : B.
Variables s s' s'' : A -> Prop.
Variables q q' : A -> Prop.
Variables r r' r'': relation A.

Lemma csE : r^⋈  ≡ r ∪ r⁻¹.
Proof. basic_solver. Qed.

Lemma crsE : r⁼ ≡ ⦗⊤₁⦘ ∪ r ∪ r⁻¹.
Proof. basic_solver. Qed.

Lemma codom_cross_incl : codom_rel (s × s') ⊆₁ s'.
Proof. basic_solver. Qed.

Lemma cross_union_l : s × (s' ∪₁ s'')  ≡ s × s' ∪ s × s''.
Proof. basic_solver. Qed.

Lemma cross_union_r : (s ∪₁ s') × s'' ≡ s × s'' ∪ s' × s''.
Proof. basic_solver. Qed.

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

Lemma dom_seq : dom_rel (r ⨾ r') ⊆₁ dom_rel r.
Proof. basic_solver. Qed.
  
Lemma compl_top_minus : forall (r : relation A), compl_rel r ≡ (fun _ _ => True) \ r.
Proof. basic_solver. Qed.

Lemma minus_union_r : forall (r r' r'': relation A), r \ (r' ∪ r'') ≡ (r \ r') ∩ (r \ r'').
Proof. 
  autounfold with unfolderDb; splits; ins; desf; splits; auto.
  unfold not; basic_solver.
Qed.

Lemma compl_union : compl_rel (r ∪ r')  ≡ compl_rel r ∩ compl_rel r'.
Proof. 
  repeat rewrite compl_top_minus; by apply minus_union_r.
Qed.

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
      (INJ : inj_dom f (codom_rel r)) : 
  f □ (r ⨾ r') ≡ (f □ r) ⨾ (f □ r').
Proof.
  autounfold with unfolderDb.
  split; ins; desf; eauto.
  all: repeat eexists; eauto.
  apply INJ in H1; desf.
  red. eauto.
Qed.

Lemma collect_rel_seq_r
      (INJ : inj_dom f (dom_rel r')) : 
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
  forall (s: A -> Prop) (f: A -> B), inj_dom f s ->
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

Lemma collect_rel_eq_dom : forall (s s': A -> Prop) (EQs: eq_dom f g s) (EQs': eq_dom f g s'),
  f □ (⦗ s ⦘ ⨾ r ⨾ ⦗ s' ⦘) ≡ g □ (⦗ s ⦘ ⨾ r ⨾ ⦗ s' ⦘).
Proof.
  ins.
  autounfold with unfolderDb.
  splits; ins; desf; repeat eexists; eauto; 
  symmetry; [apply (EQs z) | apply (EQs' y')]; auto.
Qed.

Lemma collect_rel_restr_eq_dom (HH : eq_dom f g s) :
  f □ (restr_rel s r) ≡ g □ (restr_rel s r).
Proof.
  rewrite restr_relE.
  apply collect_rel_eq_dom; auto.
Qed.

Lemma restr_set_subset 
      (SUBS : s' ⊆₁ s) 
      (EQ   : restr_rel s r ≡ restr_rel s r') :
  restr_rel s' r ≡ restr_rel s' r'.
Proof. 
  autounfold with unfolderDb in *.
  destruct EQ as [INCL INCR].
  splits; ins; splits; desf;
    [ apply (INCL x y) | apply (INCR x y) ]; 
    auto.
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
  restr_rel (s ∩₁ s') r ≡ restr_rel s r ∩ restr_rel s' r.
Proof.
  autounfold with unfolderDb.
  splits; ins; desf. 
Qed.

Lemma restr_inter_absorb_l :
  restr_rel s r ∩ restr_rel s r' ≡ r ∩ restr_rel s r'.
Proof. basic_solver. Qed.

Lemma restr_inter_absorb_r :
  restr_rel s r ∩ restr_rel s r' ≡ restr_rel s r ∩ r'.
Proof. basic_solver. Qed.

Lemma restr_irrefl_eq (IRRFLX: irreflexive r):
  forall x:A, (restr_rel (eq x) r) ≡ ∅₂.
Proof. basic_solver. Qed.

Lemma restr_clos_trans : (restr_rel s r)⁺ ⊆ restr_rel s r⁺.
Proof.
  unfold inclusion, restr_rel; ins. 
  induction H; desf; splits; eauto using t_step, t_trans. 
Qed.

Lemma eq_dom_union: eq_dom f g (s ∪₁ s') <-> eq_dom f g s /\ eq_dom f g s'.
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

Add Parametric Morphism A : (@clos_sym A) with signature 
  inclusion ==> inclusion as clos_sym_mori.
Proof. basic_solver. Qed.

Add Parametric Morphism A : (@clos_sym A) with signature 
  same_relation  ==> same_relation as clos_sym_more.
Proof. basic_solver. Qed.

Add Parametric Morphism A : (@clos_refl_sym A) with signature 
  inclusion ==> inclusion as clos_refl_sym_mori.
Proof. basic_solver. Qed.

Add Parametric Morphism A : (@clos_refl_sym A) with signature 
  same_relation  ==> same_relation as clos_refl_sym_more.
Proof. basic_solver. Qed.

Add Parametric Morphism A : (@compl_rel A) with signature 
  same_relation ==> same_relation as compl_more.
Proof. red; autounfold with unfolderDb; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@compl_rel A) with signature 
  inclusion --> inclusion as compl_mori.
Proof. red; autounfold with unfolderDb; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A B : (@inj_dom A B) with signature 
  eq ==> set_equiv ==> iff as inj_dom_more.
Proof. 
  intros f s s' Heq. red. 
  unfold inj_dom in *.
  splits; ins; specialize (H x y); apply H; auto; apply Heq; auto.
Qed.

Add Parametric Morphism A B : (@inj_dom A B) with signature 
  eq ==> set_subset --> impl as inj_dom_mori.
Proof. 
  intros f s s' Heq Hinj. 
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