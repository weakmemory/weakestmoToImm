Require Import Program.Basics.
From hahn Require Import Hahn.

Set Implicit Arguments.
Local Open Scope program_scope.

Section AuxRel.

  Variables A B : Type.
  Variable cond : A -> Prop.
  Variables s s' : A -> Prop.
  Variable f g : A -> B.
  Variable h : A -> A.
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

  Definition inj_dom_s :=
    forall (x y : A) (SY: s y) (EQ : f x = f y),
      x = y.

  Definition inj_dom :=
    forall (x y : A) (SX : s x) (SY: s y) (EQ : f x = f y),
      x = y.

  Definition restr_fun := fun x => 
    if excluded_middle_informative (s x) then f x else g x.

  Definition fixset := 
    forall (x : A) (SX : s x), x = h x.
End AuxRel.

Notation "⊤₁" := set_full.
Notation "⊤₂" := (fun _ _ => True).

Notation "a ^⋈" := (clos_sym a) (at level 1).
Notation "a ⁼" := (clos_refl_sym a) (at level 1, format "a ⁼").
Notation "a ^=" := (clos_refl_sym a) (at level 1, only parsing).
Notation "f □₁ s" := (set_collect f s) (at level 39).
Notation "f □ r"  := (collect_rel f r) (at level 45).
Notation "↑ f" := (img_rel f) (at level 1, format "↑ f").

Hint Unfold 
     clos_sym clos_refl_sym 
     inj_dom_s inj_dom eq_dom
     img_rel eq_opt compl_rel fixset : unfolderDb. 

Section Props.

Variables A B C : Type.
Variable f g : A -> B.
Variable h : A -> A.
Variable a : A.
Variable b : B.
Variables s s' s'' : A -> Prop.
Variables q q' : A -> Prop.
Variables r r' r'': relation A.

Lemma seqA_rev : r ⨾ r' ⨾ r'' ⊆ (r ⨾ r') ⨾ r''.
Proof. apply seqA. Qed.

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

Lemma codom_singl_rel (x y : A) : codom_rel (singl_rel x y) ≡₁ eq y. 
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
  unfolder.
  ins; splits; ins; desf.
  eexists; splits; eauto. 
Qed.

Lemma minus_eqv_absorb_rl : ⦗ s ⦘ ⨾ r' ≡ ∅₂ -> ⦗ s ⦘ ⨾ (r \ r') ≡ ⦗ s ⦘ ⨾ r.
Proof. 
  unfolder.
  ins; splits; ins; desf.
  eexists; splits; eauto.
Qed.

Lemma cross_minus_compl_l : s × s' \ (set_compl s) × s'' ≡ s × s'.
Proof. 
  unfolder; splits; ins; splits; desf; unfold not; ins; desf. 
Qed.

Lemma cross_minus_compl_r : s × s' \ s'' × (set_compl s') ≡ s × s'.
Proof. 
  unfolder; splits; ins; splits; desf; unfold not; ins; desf. 
Qed.
  
Lemma minus_inter_compl : r \ r' ≡ r ∩ compl_rel r'.
Proof. basic_solver. Qed.

Lemma compl_top_minus : forall (r : relation A), compl_rel r ≡ (fun _ _ => True) \ r.
Proof. basic_solver. Qed.

Lemma minus_union_r : forall (r r' r'': relation A), r \ (r' ∪ r'') ≡ (r \ r') ∩ (r \ r'').
Proof. 
  unfolder; splits; ins; desf; splits; auto.
  unfold not; basic_solver.
Qed.

Lemma compl_union : compl_rel (r ∪ r')  ≡ compl_rel r ∩ compl_rel r'.
Proof. 
  rewrite !compl_top_minus; by apply minus_union_r.
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
  rewrite !seq_eqv_lr. 
  unfold inter_rel.
  unfold same_relation, inclusion.
  splits; ins; splits; desf. 
Qed.

Lemma seq_transp_sym : symmetric r -> ⦗ s ⦘ ⨾ r ⨾ ⦗ s' ⦘ ≡ (⦗ s' ⦘ ⨾ r ⨾ ⦗ s ⦘)⁻¹.
Proof. 
  ins. 
  rewrite !transp_seq. 
  rewrite !seqA.
  rewrite !transp_sym; auto; apply eqv_sym.
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

Lemma fixset_img_rel : fixset s h <-> ⦗s⦘ ⨾ ↑ h ⊆ eq.
Proof. 
  split; autounfold with unfolderDb.
  { ins; desf; auto. }
  ins; desf; auto.
  apply (H x (h x)).
  eauto. 
Qed.

Lemma fixset_set_fixpoint : fixset s h -> s ≡₁ h □₁ s.
Proof. 
  autounfold with unfolderDb; unfold set_subset.
  intros FIX.
  splits. 
  { ins. eexists. 
    specialize (FIX x). 
    splits; [|symmetry]; eauto. } 
  ins; desf. 
  erewrite <- (FIX y); auto. 
Qed.

Lemma inj_dom_s_inj_dom (INJ : inj_dom_s s f) : inj_dom s f.
Proof. unfolder in *. ins. by apply INJ. Qed.

Lemma set_collect_compose (f' : A -> B) (g' : B -> C) :
  g' □₁ (f' □₁ s) ≡₁ (g' ∘ f') □₁ s.
Proof. 
  autounfold with unfolderDb. unfold set_subset. 
  ins; splits; ins; splits; desf; eauto.
Qed.

Lemma set_collect_updo (NC : ~ s a) : (upd f a b) □₁ s ≡₁ f □₁ s.
Proof.
  assert (forall x: A, s x -> x <> a). 
  { ins. intros HH. by subst. }
  unfolder.
  splits; unfold set_subset; ins.
  all: desf; eexists; splits; eauto.
  all: rewrite updo; auto.
Qed.

Lemma set_collect_eqv : f □ ⦗ s ⦘ ≡ ⦗ f □₁ s ⦘.
Proof.
  unfolder.
  splits; ins; desf; eauto.
  eexists. eexists.
  splits; eauto.
Qed.

Lemma set_collect_dom : f □₁ dom_rel r ≡₁ dom_rel (f □ r).
Proof.
  unfolder.
  split; intros x HH; desf; eauto.
  repeat eexists. eauto.
Qed.

Lemma set_collect_subset (INJ : inj_dom_s s' f) : 
  f □₁ s ⊆₁ f □₁ s' -> s ⊆₁ s'.
Proof.   
  unfolder in *. 
  intros FSUBS x SX. 
  assert (exists y : A, s y /\ f y = f x) as HH by eauto. 
  destruct (FSUBS (f x) HH) as [y [S'y EQfxy]].
  erewrite INJ; eauto.  
Qed.

(* Note that inclusion in other direction doesn't hold.
   For example, if `f` is constant and `a <> b`, then
   `f □₁ (eq a ∩₁ eq b) ≡₁ ∅` and `f □₁ eq a ∩₁ f □₁ eq b ≡₁ f □₁ eq a`.
 *)
Lemma set_collect_inter : f □₁ (s ∩₁ s') ⊆₁ f □₁ s ∩₁ f □₁ s'.
Proof. basic_solver. Qed.

Lemma collect_seq_eqv_l rr : f □ ⦗ s ⦘ ⨾ rr ⊆ ⦗ f □₁ s ⦘ ⨾ (f □ rr).
Proof.
  unfolder.
  intros x y HH; desf; eauto.
  eexists; splits; eauto.
Qed.

Lemma collect_seq_eqv_r rr : f □ rr ⨾ ⦗ s' ⦘ ⊆ (f □ rr) ⨾ ⦗ f □₁ s' ⦘.
Proof.
  unfolder.
  intros x y HH; desf; eauto.
  eexists; splits; eauto.
Qed.

Lemma collect_seq_eqv_lr rr :
  f □ ⦗ s ⦘ ⨾ rr ⨾ ⦗ s' ⦘ ⊆
  ⦗ f □₁ s ⦘ ⨾ (f □ rr) ⨾ ⦗ f □₁ s' ⦘.
Proof. rewrite collect_seq_eqv_l. by rewrite collect_seq_eqv_r. Qed.

Lemma collect_rel_interi : f □ (r ∩ r') ⊆ (f □ r) ∩ (f □ r').
Proof. basic_solver 10. Qed.

Lemma collect_eq e : f □₁ eq e ≡₁ eq (f e).
Proof. basic_solver. Qed.

Lemma collect_rel_seqi : f □ (r ⨾ r') ⊆ (f □ r) ⨾ (f □ r').
Proof. basic_solver 30. Qed.

Lemma collect_rel_seq_l
      (INJ : inj_dom_s (codom_rel r) f) : 
  f □ (r ⨾ r') ≡ (f □ r) ⨾ (f □ r').
Proof.
  split; [by apply collect_rel_seqi|].
  unfolder.
  ins; desf; eauto.
  repeat eexists; eauto.
  apply INJ in H1; desf.
  red. eauto.
Qed.

Lemma collect_rel_seq_r
      (INJ : inj_dom_s (dom_rel r') f) : 
  f □ (r ⨾ r') ≡ (f □ r) ⨾ (f □ r').
Proof.
  split; [by apply collect_rel_seqi|].
  unfolder.
  ins; desf; eauto.
  repeat eexists; eauto.
  symmetry in H1.
  apply INJ in H1; desf.
  red. eexists. eauto.
Qed.     

Lemma collect_rel_cr (rr : relation A) : f □ rr^? ⊆  (f □ rr)^?.
Proof.
  unfolder. ins; desf; auto.
  right. eexists. eexists. eauto.
Qed.

Lemma collect_rel_ct (rr : relation A) : f □ rr⁺ ⊆ (f □ rr)⁺.
Proof.
  unfolder. ins. desf.
  induction H.
  { apply ct_step. eexists. eexists. splits; eauto. }
  eapply t_trans; eauto.
Qed.

Lemma collect_rel_crt (rr : relation A) : f □ rr＊ ⊆  (f □ rr)＊.
Proof.
  rewrite <- !cr_of_ct. 
  by rewrite <- collect_rel_ct, <- collect_rel_cr.
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

Lemma set_collect_restr : 
  forall (s: A -> Prop) (f: A -> B), inj_dom_s s f ->
  f □ (restr_rel s r) ≡ restr_rel (f □₁ s) (f □ r).
Proof.
  ins.
  unfolder.
  splits; ins; desf; splits; eauto.
  assert (x' = y1) by (apply H; auto). subst.
  assert (y' = y0) by (apply H; auto). subst.
  eexists. eexists.
  splits; eauto.
Qed.

Lemma set_collect_eq_dom (EQ : eq_dom s f g) :
  f □₁ s ≡₁ g □₁ s.
Proof. 
  unfolder in *. 
  split. 
  { ins. desf. 
    specialize (EQ y H).
    eauto. }
  ins. desf. eauto. 
Qed.

Lemma collect_rel_eq_dom :
  forall (s s': A -> Prop) (EQs: eq_dom s f g) (EQs': eq_dom s' f g),
  f □ (⦗ s ⦘ ⨾ r ⨾ ⦗ s' ⦘) ≡ g □ (⦗ s ⦘ ⨾ r ⨾ ⦗ s' ⦘).
Proof.
  ins.
  unfolder.
  splits; ins; desf; repeat eexists; eauto; symmetry.
  { by apply EQs. }
  by apply EQs'.
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
  unfolder in *.
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
  unfolder.
    by splits; ins; desf; splits; eauto; left; left; [left|right].
Qed.

Lemma restr_set_inter :
  restr_rel (s ∩₁ s') r ≡ restr_rel s r ∩ restr_rel s' r.
Proof.
  unfolder.
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

Lemma dom_r2l_rt (HH : r ⨾ ⦗s⦘ ⊆ ⦗s⦘ ⨾ r') : r＊ ⨾ ⦗s⦘ ⊆ ⦗s⦘ ⨾ r'＊.
Proof.
  unfolder in *. ins. desf.
  induction H.
  { edestruct HH; eauto. split; auto.
      by apply rt_step. }
  { split; auto. apply rt_refl. }
  destruct IHclos_refl_trans2; auto.
  destruct IHclos_refl_trans1; auto.
  split; auto.
  eapply transitive_rt; eauto.
Qed.

Lemma set_collect_if_then (ft fe: A -> B) (HH : s ⊆₁ s') :
  (fun e : A =>
     if excluded_middle_informative (s' e)
     then ft e
     else fe e) □₁ s ≡₁ ft □₁ s.
Proof.
  unfolder. split; ins; desf; eauto.
  2: eexists; splits; eauto; desf.
  all: by exfalso; match goal with H : ~ _ |- _ => apply H end; apply HH.
Qed.

Lemma set_collect_if_else (ft fe: A -> B) (HH : s ∩₁ s' ⊆₁ ∅) :
  (fun e : A =>
     if excluded_middle_informative (s' e)
     then ft e
     else fe e) □₁ s ≡₁ fe □₁ s.
Proof.
  unfolder. split; ins; desf; eauto.
  2: eexists; splits; eauto; desf.
  all: exfalso; eapply HH; split; eauto.
Qed.

Lemma collect_rel_if_then
      (ft fe: A -> B) (DOM : dom_rel r ⊆₁ s) (CODOM : codom_rel r ⊆₁ s) :
  (fun e : A =>
     if excluded_middle_informative (s e)
     then ft e
     else fe e) □ r ≡ ft □ r.
Proof.
  unfolder. split; ins; desf; eauto.
  4: do 2 eexists; splits; eauto; desf.
  1,3,5: by exfalso; match goal with H : ~ _ |- _ => apply H end;
    eapply CODOM; eexists; eauto.
  all: by exfalso; match goal with H : ~ _ |- _ => apply H end;
    eapply DOM; eexists; eauto.
Qed.

Lemma collect_rel_if_else
      (ft fe: A -> B) (DOM : dom_rel r ∩₁ s ⊆₁ ∅) (CODOM : codom_rel r ∩₁ s ⊆₁ ∅) :
  (fun e : A =>
     if excluded_middle_informative (s e)
     then ft e
     else fe e) □ r ≡ fe □ r.
Proof.
  unfolder. split; ins; desf; eauto.
  4: do 2 eexists; splits; eauto; desf.
  1,2,4: by exfalso; eapply DOM; split; [eexists|]; eauto.
  all: exfalso; eapply CODOM; split; [eexists|]; eauto.
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
Proof. red; unfolder; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@compl_rel A) with signature 
  inclusion --> inclusion as compl_mori.
Proof. red; unfolder; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A B : (@inj_dom_s A B) with signature 
    set_equiv ==> eq ==> iff as inj_dom_s_more.
Proof. 
  intros s s' Heq f. red. 
  unfold inj_dom_s in *.
  splits; ins; specialize (H x y); apply H; auto; apply Heq; auto.
Qed.

Add Parametric Morphism A B : (@inj_dom_s A B) with signature 
  set_subset --> eq ==> impl as inj_dom_s_mori.
Proof. unfold impl, inj_dom_s. basic_solver. Qed.

Add Parametric Morphism A B : (@inj_dom A B) with signature 
  set_subset --> eq ==> impl as inj_dom_mori.
Proof. unfold impl, inj_dom. basic_solver. Qed.

Add Parametric Morphism A : (@fixset A) with signature 
    set_equiv ==> eq ==> iff as fixset_more.
Proof. 
  intros s s' Heq f. red. 
  unfold fixset.
  splits; ins; specialize (H x); apply H; auto; apply Heq; auto.
Qed.

Add Parametric Morphism A : (@fixset A) with signature 
  set_subset --> eq ==> impl as fixset_mori.
Proof. unfold impl, fixset. basic_solver. Qed.

Add Parametric Morphism A : (@set_compl A) with signature 
  set_equiv ==> set_equiv as set_compl_more.
Proof. red; unfolder; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@set_compl A) with signature 
  set_subset --> set_subset as set_compl_mori.
Proof. red; unfolder; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A B : (@set_collect A B) with signature 
  eq ==> set_equiv ==> set_equiv as set_collect_more.
Proof. red; unfolder; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A B : (@set_collect A B) with signature 
  eq ==> set_subset ==> set_subset as set_collect_mori.
Proof. red; unfolder; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@dom_rel A) with signature
   inclusion ==> set_subset as dom_rel_mori.
Proof. red; unfolder; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@dom_rel A) with signature
   same_relation ==> set_equiv as dom_rel_more.
Proof. red; unfolder; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@codom_rel A) with signature
   inclusion ==> set_subset as codom_rel_mori.
Proof. red; unfolder; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@codom_rel A) with signature
   same_relation ==> set_equiv as codom_rel_more.
Proof. red; unfolder; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A : (@set_minus A) with signature 
  set_equiv ==> set_equiv ==> set_equiv as set_minus_more.
Proof. red; unfolder; splits; ins; desf; split; eauto. Qed.

Add Parametric Morphism A : (@set_minus A) with signature 
  set_subset ==> set_subset --> set_subset as set_minus_mori.
Proof. red; unfolder; splits; ins; desf; eauto. Qed.