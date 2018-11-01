Require Import Program.Basics.
From hahn Require Import Hahn.

Set Implicit Arguments.
Local Open Scope program_scope.

Section AuxRel.

  Variables A B : Type.
  Variable cond : A -> Prop.
  Variables s s' : A -> Prop.
  Variable f g : A -> B.
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

Hint Unfold clos_sym clos_refl_sym img_rel eq_opt compl_rel : unfolderDb. 

Section Props.

Variables A B C : Type.
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

Lemma crs_cs : r⁼ ≡ ⦗⊤₁⦘ ∪ r^⋈.
Proof. basic_solver. Qed. 

Lemma cs_union : (r ∪ r')^⋈  ≡ r^⋈ ∪ r'^⋈.
Proof. basic_solver. Qed.

Lemma crs_union : (r ∪ r')⁼  ≡ r⁼ ∪ r'⁼.
Proof. basic_solver. Qed.

Lemma cs_cross : (s × s')^⋈ ≡ s × s' ∪ s' × s.
Proof. basic_solver. Qed.

Lemma crs_cross : (s × s')⁼ ≡ ⦗⊤₁⦘ ∪ s × s' ∪ s' × s.
Proof. basic_solver. Qed.

Lemma cs_restr : (restr_rel s r)^⋈ ≡ restr_rel s r^⋈.
Proof. basic_solver. Qed.

Lemma crs_restr1 : (restr_rel s r)⁼ ≡ ⦗⊤₁⦘ ∪ restr_rel s r^⋈.
Proof. basic_solver 10. Qed.

Lemma crs_restr2 : restr_rel s r⁼ ≡ restr_rel s ⦗⊤₁⦘ ∪ restr_rel s r^⋈.
Proof. basic_solver 10. Qed.
  
Lemma cs_sym : symmetric r^⋈.
Proof. basic_solver. Qed.

Lemma crs_sym : symmetric r⁼.
Proof. basic_solver. Qed.

Lemma eqv_sym : forall (s : A -> Prop), symmetric ⦗s⦘.
Proof. basic_solver. Qed.

Lemma minus_sym : symmetric r -> symmetric r' -> symmetric (r \ r').
Proof. basic_solver. Qed.

Lemma transp_sym : forall (r : relation A), symmetric r -> r⁻¹ ≡ r. 
Proof. basic_solver. Qed.

Lemma restr_sym : forall (r : relation A), symmetric r -> symmetric (restr_rel s r). 
Proof. basic_solver. Qed.

Lemma seq_incl_cross : dom_rel r ⊆₁ s -> codom_rel r' ⊆₁ s' -> r ⨾ r' ⊆ s × s'.
Proof. basic_solver. Qed.

Lemma codom_cross_incl : codom_rel (s × s') ⊆₁ s'.
Proof. basic_solver. Qed.

Lemma cross_union_l : s × (s' ∪₁ s'') ≡ s × s' ∪ s × s''.
Proof. basic_solver. Qed.

Lemma cross_union_r : (s ∪₁ s') × s'' ≡ s × s'' ∪ s' × s''.
Proof. basic_solver. Qed.

Lemma seq_eqv_cross_l : ⦗q⦘ ⨾ s × s' ≡ (q ∩₁ s) × s'.
Proof. basic_solver. Qed.

Lemma seq_eqv_cross_r : s × s' ⨾ ⦗q'⦘ ≡ s × (q' ∩₁ s').
Proof. basic_solver. Qed.

Lemma seq_eqv_cross : ⦗q⦘ ⨾ s × s' ⨾ ⦗q'⦘ ≡ (q ∩₁ s) × (q' ∩₁ s').
Proof. basic_solver. Qed.

Lemma restr_cross : restr_rel s r ≡ s × s ∩ r.
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

Lemma eq_opt_someE : eq_opt (Some a) ≡₁ eq a.
Proof. basic_solver. Qed. 

Lemma eq_opt_noneE : eq_opt (None : option A) ≡₁ ∅.
Proof. basic_solver. Qed. 

Lemma set_subset_union_minus : s ⊆₁ s \₁ s' ∪₁ s'. 
Proof. 
  by unfold set_minus, set_union, set_subset; clear; intros; tauto.
Qed.

Lemma set_union_minus : s' ⊆₁ s -> s ≡₁ s \₁ s' ∪₁ s'. 
Proof. 
  intros. 
  unfold set_equiv; splits; 
    [by apply set_subset_union_minus|basic_solver].
Qed.

Lemma union_minus : r' ⊆ r -> r ≡ r \ r' ∪ r'.
Proof. 
  intros H.
  unfold same_relation; splits.
  { by apply inclusion_union_minus. }
  basic_solver.
Qed.

Lemma minus_eqv_absorb_rr : r' ⨾ ⦗ s ⦘ ≡ ∅₂ -> (r \ r') ⨾ ⦗ s ⦘ ≡ r ⨾ ⦗ s ⦘.
Proof. 
  autounfold with unfolderDb.
  ins; splits; ins; desf.
  { eexists; splits; eauto. }
  { eexists; splits; eauto. 
    red. ins. apply (H x y). 
    eexists; splits; eauto. } 
Qed.

Lemma minus_eqv_absorb_rl : ⦗ s ⦘ ⨾ r' ≡ ∅₂ -> ⦗ s ⦘ ⨾ (r \ r') ≡ ⦗ s ⦘ ⨾ r.
Proof. 
  autounfold with unfolderDb.
  ins; splits; ins; desf.
  { eexists; splits; eauto. }
  { eexists; splits; eauto. 
    red. ins. apply (H z y). 
    eexists; splits; eauto. } 
Qed.

Lemma cross_minus_compl_l : s × s' \ (set_compl s) × s'' ≡ s × s'.
Proof. 
  autounfold with unfolderDb; splits; ins; splits; desf; unfold not; ins; desf. 
Qed.

Lemma cross_minus_compl_r : s × s' \ s'' × (set_compl s') ≡ s × s'.
Proof. 
  autounfold with unfolderDb; splits; ins; splits; desf; unfold not; ins; desf. 
Qed.
  
Lemma minus_inter_compl : r \ r' ≡ r ∩ compl_rel r'.
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

Lemma seq_cross_singl_l x y : s' x -> s × s' ⨾ singl_rel x y ≡ s × eq y.
Proof. 
  ins. 
  autounfold with unfolderDb.
  splits; ins; splits; desf; eauto. 
Qed.

Lemma seq_cross_singl_r x y : s y -> singl_rel x y ⨾ s × s' ≡ eq x × s'.
Proof. 
  ins. 
  autounfold with unfolderDb.
  splits; ins; splits; desf; eauto. 
Qed.

Lemma seq_eqv_inter_lr : ⦗s⦘ ⨾ (r ∩ r') ⨾ ⦗s'⦘ ≡ (⦗s⦘ ⨾ r ⨾ ⦗s'⦘) ∩ (⦗s⦘ ⨾ r' ⨾ ⦗s'⦘).
Proof. 
  repeat rewrite seq_eqv_lr. 
  unfold inter_rel.
  unfold same_relation, inclusion.
  splits; ins; splits; desf. 
Qed.

Lemma seq_transp_sym : symmetric r -> ⦗ s ⦘ ⨾ r ⨾ ⦗ s' ⦘ ≡ (⦗ s' ⦘ ⨾ r ⨾ ⦗ s ⦘)⁻¹.
Proof. 
  ins. 
  repeat rewrite transp_seq. 
  repeat rewrite seqA.
  repeat rewrite transp_sym; auto; apply eqv_sym.
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

Lemma set_collect_compose (h : B -> C) : h □₁ (f □₁ s) ≡₁ (h ∘ f) □₁ s.
Proof. 
  autounfold with unfolderDb. unfold set_subset. 
  ins; splits; ins; splits; desf; eauto.
Qed.

Lemma img_rel_eqv_eq (h : A -> A) : ⦗s⦘ ⨾ ↑ h ⊆ eq -> s ≡₁ h □₁ s.
Proof. 
  autounfold with unfolderDb; unfold img_rel, set_subset.
  ins; splits; ins; splits; desf.
  { specialize (H x (h x)).
    eexists; splits; eauto.
    symmetry; apply H.
    eexists; splits; eauto. }
  specialize (H y (h y)).
  arewrite (h y = y); auto.
  symmetry; apply H.
  eexists; splits; eauto. 
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

Lemma collect_eq e: f □₁ eq e ≡₁ eq (f e).
Proof. basic_solver. Qed.

Lemma collect_rel_seqi : f □ (r ⨾ r') ⊆ (f □ r) ⨾ (f □ r').
Proof. basic_solver 30. Qed.

Lemma collect_rel_seq_l
      (INJ : inj_dom (codom_rel r) f) : 
  f □ (r ⨾ r') ≡ (f □ r) ⨾ (f □ r').
Proof.
  split; [by apply collect_rel_seqi|].
  autounfold with unfolderDb.
  ins; desf; eauto.
  repeat eexists; eauto.
  apply INJ in H1; desf.
  red. eauto.
Qed.

Lemma collect_rel_seq_r
      (INJ : inj_dom (dom_rel r') f) : 
  f □ (r ⨾ r') ≡ (f □ r) ⨾ (f □ r').
Proof.
  split; [by apply collect_rel_seqi|].
  autounfold with unfolderDb.
  ins; desf; eauto.
  repeat eexists; eauto.
  symmetry in H1.
  apply INJ in H1; desf.
  red. eexists. eauto.
Qed.     

Lemma collect_rel_ct : f □ r⁺ ⊆ (f □ r)⁺.
Proof.
  unfolder. ins. desf.
  induction H.
  { apply ct_step. eexists. eexists. splits; eauto. }
  eapply t_trans; eauto.
Qed.

Lemma collect_rel_irr (HH : irreflexive (f □ r)): irreflexive r.
Proof. generalize HH. basic_solver 10. Qed.

Lemma collect_rel_acyclic (HH : acyclic (f □ r)): acyclic r.
Proof.
  red. red.
  assert (forall x y, r⁺ x y -> x <> y) as AA.
  2: { ins. eapply AA; eauto. }
  ins. induction H; intros BB; subst.
  { eapply HH. apply ct_step. red.
    eexists. eexists. splits; eauto. }
  eapply HH.
  apply collect_rel_ct.
  red. eexists. eexists. splits.
  { eapply t_trans; eauto. }
  all: done.
Qed.

Lemma collect_rel_cr : f □ r^? ⊆  (f □ r)^?.
Proof.
  unfolder. ins; desf; auto.
  right. eexists. eexists. eauto.
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

Lemma collect_rel_eq_dom :
  forall (s s': A -> Prop) (EQs: eq_dom s f g) (EQs': eq_dom s' f g),
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

Lemma eq_dom_union :
  eq_dom (s ∪₁ s') f g <-> eq_dom s f g /\ eq_dom s' f g.
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

Lemma set_compl_union_id : s ∪₁ set_compl s ≡₁ fun _ => True.
Proof.
  split; [basic_solver|].
  intros x _.
  destruct (classic (s x)).
  { by left. }
    by right.
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
    set_equiv ==> eq ==> iff as inj_dom_more.
Proof. 
  intros s s' Heq f. red. 
  unfold inj_dom in *.
  splits; ins; specialize (H x y); apply H; auto; apply Heq; auto.
Qed.

Add Parametric Morphism A B : (@inj_dom A B) with signature 
  set_subset --> eq ==> impl as inj_dom_mori.
Proof. unfold impl, inj_dom. basic_solver. Qed.

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

Add Parametric Morphism A : (@set_minus A) with signature 
  set_equiv ==> set_equiv ==> set_equiv as set_minus_more.
Proof. red; autounfold with unfolderDb; splits; ins; desf; split; eauto. Qed.

Add Parametric Morphism A : (@set_minus A) with signature 
  set_subset ==> set_subset --> set_subset as set_minus_mori.
Proof. red; autounfold with unfolderDb; splits; ins; desf; eauto. Qed.