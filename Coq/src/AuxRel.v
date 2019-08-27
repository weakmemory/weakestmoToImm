Require Import Program.Basics.
From hahn Require Import Hahn.

Set Implicit Arguments.
Local Open Scope program_scope.

Section AuxRel.

  Definition clos_sym {A : Type} (r : relation A) : relation A := 
    r ∪ r⁻¹. 

  Definition clos_refl_sym {A : Type} (r : relation A) : relation A := 
    (r ∪ r⁻¹)^?. 

  Definition eq_opt {A : Type} (a: option A) : A -> Prop := 
    fun b => 
      match a with
      | None => False
      | Some a => eq a b
      end.
  
  Definition compl_rel {A : Type} (r : relation A) : relation A := 
    fun a b => ~ r a b.

  Definition inj_dom {A B : Type} (s : A -> Prop) (f : A -> B) := 
    forall (x y : A) (SX : s x) (SY: s y) (EQ : f x = f y), 
      x = y.

  Definition restr_fun {A B : Type} (s : A -> Prop) (f g : A -> B) := 
    fun x => if excluded_middle_informative (s x) then f x else g x.

  Definition fixset {A : Type} (s : A -> Prop) (f : A -> A) := 
    forall (x : A) (SX : s x), f x = x.

  Definition downward_total {A : Type} (r : relation A) := 
    forall x y z (Rxz : r x z) (Ryz : r y z), clos_refl_sym r x y.

  Definition set_map {A B : Type} (f : A -> B) (s : B -> Prop) := 
    fun x => s (f x).

End AuxRel.

Notation "⊤₁" := set_full.
Notation "⊤₂" := (fun _ _ => True).

Notation "a ^⋈" := (clos_sym a) (at level 1).
Notation "a ⁼" := (clos_refl_sym a) (at level 1, format "a ⁼").
Notation "a ^=" := (clos_refl_sym a) (at level 1, only parsing).
Notation "f ⋄₁ s"  := (set_map f s) (at level 39).
Notation "f □₁ s" := (set_collect f s) (at level 39).
Notation "f ⋄ r"  := (map_rel f r) (at level 45).
Notation "f □ r"  := (collect_rel f r) (at level 45).

Hint Unfold 
     clos_sym clos_refl_sym 
     inj_dom restr_fun set_map
     eq_opt compl_rel fixset : unfolderDb. 

Section Props.

Variables A B C : Type.
Variables s s' s'' : A -> Prop.
Variables p p' p'' : B -> Prop.
Variables r r' r'' : relation A.

(******************************************************************************)
(** ** clos_sym/clos_refl_sym properties *)
(******************************************************************************)

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

(******************************************************************************)
(** ** symmetry of relations *)
(******************************************************************************)

Lemma cr_sym : symmetric r -> symmetric r^?.
Proof. basic_solver. Qed.

Lemma cs_sym : symmetric r^⋈.
Proof. basic_solver. Qed.

Lemma crs_sym : symmetric r⁼.
Proof. basic_solver. Qed.

Lemma eqv_sym : forall (s : A -> Prop), symmetric ⦗s⦘.
Proof. basic_solver. Qed.

Lemma union_sym : symmetric r -> symmetric r' -> symmetric (r ∪ r').
Proof. basic_solver. Qed.

Lemma inter_sym : symmetric r -> symmetric r' -> symmetric (r ∩ r').
Proof. basic_solver. Qed.

Lemma minus_sym : symmetric r -> symmetric r' -> symmetric (r \ r').
Proof. basic_solver. Qed.

Lemma transp_sym : symmetric r -> symmetric r⁻¹.
Proof. basic_solver. Qed.

Lemma restr_sym : symmetric r -> symmetric (restr_rel s r). 
Proof. basic_solver. Qed.

(******************************************************************************)
(** ** dom/codom properties *)
(******************************************************************************)

Lemma dom_singl_rel (x y : A) : dom_rel (singl_rel x y) ≡₁ eq x. 
Proof. basic_solver. Qed.

Lemma codom_singl_rel (x y : A) : codom_rel (singl_rel x y) ≡₁ eq y. 
Proof. basic_solver. Qed.

Lemma dom_seq (rr rr' : relation A) : dom_rel (rr ⨾ rr') ⊆₁ dom_rel rr.
Proof. basic_solver. Qed.

Lemma dom_minus : dom_rel (r \ r') ⊆₁ dom_rel r. 
Proof. basic_solver. Qed.

(* TODO : rename *)
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

Lemma codom_rel_helper (rr : relation A) 
      (IN : codom_rel rr ⊆₁ s) :
  rr ≡ rr ⨾ ⦗s⦘.
Proof. unfolder in *. basic_solver. Qed.

Lemma dom_codom_rel_helper 
      (IN_DOM : dom_rel r ⊆₁ s)
      (IN_CODOM : codom_rel r ⊆₁ s'):
  r ≡ ⦗s⦘ ⨾ r ⨾ ⦗s'⦘.
Proof. unfolder in *. basic_solver 7. Qed.

Lemma functional_codom_inclusion (rr rr' : relation A) 
      (INCL : rr ⊆ rr') 
      (CODOM_INCL : codom_rel rr' ⊆₁ codom_rel rr)
      (FUNC : functional rr'⁻¹) :
  rr ≡ rr'.
Proof.
  split; auto.
  intros a1 a2 R'12.
  specialize (CODOM_INCL a2).
  destruct CODOM_INCL as [a3 R32]; [basic_solver|].  
  apply INCL in R32 as R'32.
  by arewrite (a1 = a3). 
Qed.

Lemma functional_dom_inclusion 
      (INCL : r ⊆ r') 
      (CODOM_INCL : dom_rel r' ⊆₁ dom_rel r)
      (FUNC : functional r') :
  r ≡ r'.
Proof.
  apply same_relation_transpE.
  apply inclusion_transpE in INCL.
  apply functional_codom_inclusion; auto. 
Qed.

Lemma dom_eqv_tr_codom :  
  dom_rel r ≡₁ codom_rel r⁻¹.
Proof. basic_solver. Qed.

Lemma tr_dom_eqv_codom (rr : relation A) :
  dom_rel rr⁻¹ ≡₁ codom_rel rr.
Proof. basic_solver. Qed.

Lemma codom_rel_eqv_dom_rel : 
  codom_rel (⦗dom_rel r⦘ ⨾ r') ≡₁ codom_rel (r⁻¹ ⨾ r').
Proof. basic_solver. Qed.

Lemma eqv_dom_in_seq_tr : 
  ⦗dom_rel r⦘ ⊆ r ⨾ r⁻¹. 
Proof. basic_solver. Qed.

Lemma eqv_codom_in_seq_tr : 
  ⦗codom_rel r⦘ ⊆ r⁻¹ ⨾ r. 
Proof. basic_solver. Qed.

Lemma dom_ct (rr : relation A) : 
  dom_rel rr⁺ ≡₁ dom_rel rr.
Proof.
  rewrite ct_begin.
  basic_solver 7.
Qed.

Lemma codom_ct (rr : relation A) : 
      codom_rel rr⁺ ≡₁ codom_rel rr.
Proof.
  split.
  { rewrite ct_end.
    basic_solver. }
  by rewrite <- ct_step.
Qed.

(******************************************************************************)
(** ** cross_rel properties *)
(******************************************************************************)

Lemma cross_union_l : s × (s' ∪₁ s'') ≡ s × s' ∪ s × s''.
Proof. basic_solver. Qed.

Lemma cross_union_r : (s ∪₁ s') × s'' ≡ s × s'' ∪ s' × s''.
Proof. basic_solver. Qed.

Lemma cross_inter_l : (s ∩₁ s') × s'' ≡ ⦗s⦘ ⨾ s' × s''.
Proof. basic_solver. Qed.

Lemma cross_inter_r : s × (s' ∩₁ s'') ≡ s × s' ⨾ ⦗s''⦘.
Proof. basic_solver. Qed.

Lemma seq_cross_eq x : s × eq x ⨾ eq x × s' ≡ s × s'.
Proof. basic_solver 10. Qed.

(* Lemma seq_eqv_cross : ⦗q⦘ ⨾ s × s' ⨾ ⦗q'⦘ ≡ (q ∩₁ s) × (q' ∩₁ s'). *)
(* Proof. basic_solver. Qed. *)

Lemma restr_cross : restr_rel s r ≡ r ∩ s × s.
Proof. basic_solver. Qed.

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

(******************************************************************************)
(** ** transp properties *)
(******************************************************************************)

Lemma transp_singl_rel (x y : A) : (singl_rel x y)⁻¹ ≡ singl_rel y x.
Proof. basic_solver. Qed.

Lemma transp_sym_equiv : symmetric r -> r⁻¹ ≡ r. 
Proof. basic_solver. Qed.

Lemma sym_transp_equiv : symmetric r <-> r⁻¹ ≡ r. 
Proof.
  split.
  { basic_solver. }
  intros HH.
  red. ins. by apply HH.
Qed.

(* TODO : rename *)
Lemma seq_transp_sym : symmetric r -> ⦗ s ⦘ ⨾ r ⨾ ⦗ s' ⦘ ≡ (⦗ s' ⦘ ⨾ r ⨾ ⦗ s ⦘)⁻¹.
Proof. 
  ins. 
  rewrite !transp_seq. 
  rewrite !seqA.
  rewrite !transp_sym_equiv; auto. 
  rewrite !transp_eqv_rel. 
  done.
Qed.

(******************************************************************************)
(** ** set_collect properties *)
(******************************************************************************)

Lemma transp_collect_rel (f : A -> B) :
  f □ r⁻¹ ≡  (f □ r)⁻¹.
Proof. basic_solver 10. Qed.

Lemma set_collect_eq_dom (f g : A -> B) (EQ : eq_dom s f g) :
  f □₁ s ≡₁ g □₁ s.
Proof. 
  unfolder in *. 
  split. 
  { ins. desf. 
    specialize (EQ y H).
    eauto. }
  ins. desf. eauto. 
Qed.

(* Note that inclusion in other direction doesn't hold.
   For example, if `f` is constant and `a <> b`, then
   `f □₁ (eq a ∩₁ eq b) ≡₁ ∅` and `f □₁ eq a ∩₁ f □₁ eq b ≡₁ f □₁ eq a`.
 *)
Lemma set_collect_inter (f : A -> B) : 
  f □₁ (s ∩₁ s') ⊆₁ f □₁ s ∩₁ f □₁ s'.
Proof. basic_solver. Qed.

Lemma set_collect_inter_inj (f : A -> B)
      (INJ : inj_dom (s ∪₁ s') f) :
  f □₁ (s ∩₁ s') ≡₁ f □₁ s ∩₁ f □₁ s'.
Proof.
  split; [by apply set_collect_inter|].
  intros b [[a [sa eq1]] [a' [s'a' eq2]]].
  assert (a = a').
  { apply INJ; basic_solver. }
  basic_solver.
Qed.

Lemma set_collect_dom (f : A -> B) : 
  f □₁ dom_rel r ≡₁ dom_rel (f □ r).
Proof.
  unfolder.
  split; intros x HH; desf; eauto.
  repeat eexists. eauto.
Qed.

Lemma set_collect_codom (f : A -> B) : 
  f □₁ codom_rel r ≡₁ codom_rel (f □ r).
Proof.
  unfolder.
  split; intros x HH; desf; eauto.
  repeat eexists. eauto.
Qed.

Lemma set_collect_eq_opt (f : A -> B) (a : option A) : 
  f □₁ eq_opt a ≡₁ eq_opt (option_map f a).
Proof. unfold eq_opt, option_map. basic_solver. Qed.

Lemma set_collect_compose (f : A -> B) (g : B -> C) :
  g □₁ (f □₁ s) ≡₁ (g ∘ f) □₁ s.
Proof. 
  autounfold with unfolderDb. unfold set_subset. 
  ins; splits; ins; splits; desf; eauto.
Qed.

Lemma set_collect_updo (f : A -> B) (a : A) (b : B) (NC : ~ s a) : 
  (upd f a b) □₁ s ≡₁ f □₁ s.
Proof.
  assert (forall x: A, s x -> x <> a). 
  { ins. intros HH. by subst. }
  unfolder.
  splits; unfold set_subset; ins.
  all: desf; eexists; splits; eauto.
  all: rewrite updo; auto.
Qed.

Lemma set_collect_restr_fun (f g : A -> B) : 
  s' ⊆₁ s -> (restr_fun s f g) □₁ s' ≡₁ f □₁ s'.
Proof. 
  clear.
  unfolder. ins. split. 
  all : 
    ins; desc; 
    eexists; split; eauto; 
    destruct (excluded_middle_informative (s y)); 
    eauto; exfalso; intuition. 
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

(******************************************************************************)
(** ** collect_rel properties *)
(******************************************************************************)

(* Lemma collect_rel_eq_dom : *)
(*   forall (s s': A -> Prop) (EQs: eq_dom s f g) (EQs': eq_dom s' f g), *)
(*   f □ (⦗ s ⦘ ⨾ r ⨾ ⦗ s' ⦘) ≡ g □ (⦗ s ⦘ ⨾ r ⨾ ⦗ s' ⦘). *)
(* Proof. *)
(*   ins. *)
(*   unfolder. *)
(*   splits; ins; desf; repeat eexists; eauto; symmetry. *)
(*   { by apply EQs. } *)
(*   by apply EQs'. *)
(* Qed. *)

Lemma collect_rel_restr_eq_dom (f g : A -> B) (EQ : eq_dom s f g) :
  f □ (restr_rel s r) ≡ g □ (restr_rel s r).
Proof. 
  unfolder. split.
  { ins; desf; repeat eexists; eauto; 
      symmetry; eapply EQ; auto. }
  ins; desf; repeat eexists; eauto; 
    symmetry; eapply EQ; auto.
Qed.

Lemma collect_rel_singl (f : A -> B) x y : 
  f □ singl_rel x y ≡ singl_rel (f x) (f y).
Proof. basic_solver 42. Qed.

Lemma collect_rel_transp (f : A -> B) : 
  f □ r⁻¹ ≡ (f □ r)⁻¹.
Proof. basic_solver 42. Qed.

Lemma collect_rel_eqv (f : A -> B) : 
  f □ ⦗ s ⦘ ≡ ⦗ f □₁ s ⦘.
Proof.
  unfolder.
  splits; ins; desf; eauto.
  eexists. eexists.
  splits; eauto.
Qed.

Lemma collect_rel_interi (f : A -> B) : 
  f □ (r ∩ r') ⊆ (f □ r) ∩ (f □ r').
Proof. basic_solver 10. Qed.

Lemma collect_rel_inter (f : A -> B) 
      (INJ_dom : inj_dom (dom_rel r ∪₁ dom_rel r') f)  
      (INJ_codom : inj_dom (codom_rel r ∪₁ codom_rel r') f) :  
  f □ (r ∩ r') ≡ (f □ r) ∩ (f □ r').
Proof.
  split; [by apply collect_rel_interi|].
  unfolder.
  intros b1 b2 [[a1 [a2 HH]] [a1' [a2' HH']]].
  assert (EQ1 : a1 = a1').
  { apply INJ_dom; basic_solver. }
  assert (EQ2 : a2 = a2').
  { apply INJ_codom; basic_solver. }
  exists a1, a2. 
  basic_solver.
Qed.

Lemma collect_rel_seqi (rr rr' : relation A) (f : A -> B) : 
  f □ (rr ⨾ rr') ⊆ (f □ rr) ⨾ (f □ rr').
Proof. basic_solver 30. Qed.

Lemma collect_rel_seq (rr rr' : relation A) (f : A -> B)
      (INJ : inj_dom (codom_rel rr ∪₁ dom_rel rr') f) : 
  f □ (rr ⨾ rr') ≡ (f □ rr) ⨾ (f □ rr').
Proof.
  split; 
    [by apply collect_rel_seqi|].
  unfolder.
  ins; desf; eauto.
  repeat eexists; eauto.
  erewrite INJ; eauto;
    unfolder; eauto.
Qed.

Lemma collect_rel_cr (f : A -> B) (rr : relation A) : 
  f □ rr^? ⊆  (f □ rr)^?.
Proof.
  unfolder. ins; desf; auto.
  right. eexists. eexists. eauto.
Qed.

Lemma collect_rel_ct (f : A -> B) (rr : relation A) : 
  f □ rr⁺ ⊆ (f □ rr)⁺.
Proof.
  unfolder. ins. desf.
  induction H.
  { apply ct_step. eexists. eexists. splits; eauto. }
  eapply t_trans; eauto.
Qed.

Lemma collect_rel_crt (f : A -> B) (rr : relation A) : 
  f □ rr＊ ⊆  (f □ rr)＊.
Proof.
  by rewrite <- !cr_of_ct, 
             <- collect_rel_ct, 
             <- collect_rel_cr.
Qed.

Lemma collect_rel_irr (rr : relation A) (f : A -> B) (Irr : irreflexive (f □ rr)): 
  irreflexive rr.
Proof. generalize Irr. basic_solver 10. Qed.

Lemma collect_rel_acyclic (rr : relation A) (f : A -> B) (ACYC : acyclic (f □ rr)): 
  acyclic rr.
Proof.
  red. red.
  assert (forall x y, rr⁺ x y -> x <> y) as AA.
  2: { ins. eapply AA; eauto. }
  ins. induction H; intros BB; subst.
  { eapply ACYC. apply ct_step. red.
    eexists. eexists. splits; eauto. }
  eapply ACYC.
  apply collect_rel_ct.
  red. eexists. eexists. splits.
  { eapply t_trans; eauto. }
  all: done.
Qed.

Lemma collect_rel_compose (f : A -> B) (g : B -> C) :
  g □ (f □ r) ≡ (g ∘ f) □ r.
Proof. 
  unfolder. unfold compose.
  ins; splits; ins; splits; desf; eauto.
  do 2 eexists. splits; eauto.
Qed.

Lemma collect_rel_fixset (f : A -> A) (FIX : fixset s f) :
  f □ restr_rel s r ≡ restr_rel s r.
Proof.
  unfolder in *.
  split; ins; desf.
  2: { do 2 eexists. splits; eauto. }
  assert (f x' = x') as HX. 
  { specialize (FIX x'). auto. }
  assert (f y' = y') as HY. 
  { specialize (FIX y'). auto. }
  splits; congruence.
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

Lemma functional_collect_rel_inj (f : A -> B)
      (INJ : inj_dom s f) :
  functional (f □ (restr_rel s r)) <-> functional (restr_rel s r). 
Proof.
  split; [basic_solver 15|].
  unfolder.
  intros P b1 b2 b3 [a1 [a2 [pr1 [eq1 eq2]]]]
         [a1' [a2' [pr1' [eq1' eq2']]]].
  subst.
  assert (a2 = a2'); [|congruence].
  assert (a1 = a1'); [|by eapply P; eauto; desf].
  apply INJ; desf.
Qed.

Lemma transitive_collect_rel_inj (f : A -> B)
      (INJ : inj_dom s f) :
  transitive (f □ restr_rel s r) <-> transitive (restr_rel s r).
Proof. 
  split.
  { unfolder.
    intros HH a1 a2 a3 R12 R23.
    specialize (HH (f a1) (f a2) (f a3)).
    destruct HH as [a1' HH]. 
    { exists a1, a2. desf. }
    { exists a2, a3. desf. }
    destruct HH as [a3' HH].
    assert (a1 = a1'); [apply INJ; by desf|].
    assert (a3 = a3'); [apply INJ; by desf|].
    basic_solver. }
  unfolder. 
  intros HH b1 b2 b3 [a1 [a2 P]] [a2' [a3 PP]].
  assert (a2' = a2); [apply INJ; by desf|].
  exists a1, a3.
  split; [|by desf].
  eapply HH with (y := a2); basic_solver.
Qed.

Lemma total_collect_rel (f : A -> B) :
  is_total s r -> is_total (f □₁ s) (f □ r).
Proof.
  unfolder.
  intros HH b1 [a1 P1] b2 [a2 P2] NEQ.
  desf.
  assert (a1 <> a2) as NEQ' by congruence.
  specialize (HH a1 P1 a2 P2 NEQ').
  desf.
  { left. eauto. }
  right. eauto.
Qed.

Lemma collect_rel_irr_inj (rr : relation A) (f : A -> B)
      (INJ : inj_dom s f) :
  irreflexive (f □ (restr_rel s rr)) <-> irreflexive (restr_rel s rr).
Proof.
  split; [by apply collect_rel_irr|].
  unfolder. ins. desf. rename H2 into EQ.
  apply INJ in EQ; eauto.
  basic_solver.
Qed.

Lemma collect_rel_ct_inj (f : A -> B) (rr : relation A)
      (INJ : inj_dom s f) : 
  f □ (restr_rel s rr)⁺ ≡ (f □ (restr_rel s rr))⁺.
Proof.
  split; [by apply collect_rel_ct|].
  apply inclusion_t_ind_right.
  { by rewrite <- ct_step. }  
  rewrite <- collect_rel_seq.
  { by rewrite ct_unit. }
  intros x y Hx Hy.
  destruct Hx as [[z  Hx]|[z  Hx]];
    destruct Hy as [[z' Hy]|[z' Hy]].
  all: try apply restr_ct in Hx.
  all: try apply restr_ct in Hy.
  all: unfolder in *; basic_solver.
Qed.

Lemma collect_rel_acyclic_inj (f : A -> B)
      (INJ : inj_dom s f) : 
  acyclic (f □ restr_rel s r) <-> acyclic (restr_rel s r).
Proof.
  split; [by apply collect_rel_acyclic|].
  unfold acyclic.
  rewrite <- collect_rel_ct_inj; auto.
  arewrite ((restr_rel s r)⁺ ≡ restr_rel s (restr_rel s r)⁺).
  { rewrite codom_rel_helper, dom_rel_helper at 1.
    1: by rewrite <- restr_relE. 
    { rewrite dom_seq, dom_ct. basic_solver. }
    rewrite codom_ct. basic_solver. }
  by apply collect_rel_irr_inj.
Qed.

Lemma collect_rel_minus (f : A -> B) :
  f □ r \ f □ r' ⊆ f □ (r \ r').
Proof. basic_solver 15. Qed.

(* TODO : the INJ requirement could be weaker *)
Lemma collect_rel_minus_inj (f : A -> B)
      (INJ_DOM : inj_dom (dom_rel r ∪₁ dom_rel r') f)
      (INJ_CODOM : inj_dom (codom_rel r ∪₁ codom_rel r') f) : 
  f □ (r \ r') ≡ f □ r \ f □ r'.
Proof.
  split; [|by apply collect_rel_minus].
  intros b1 b2 [a1 [a2 [[R NR'] HH]]].
  split; [by exists a1, a2|]. 
  intros [a1' [a2' HH']].
  apply NR'.
  arewrite (a1 = a1').
  { apply INJ_DOM ; basic_solver. }
  arewrite (a2 = a2').
  { apply INJ_CODOM ; basic_solver. }
  desf.
Qed.

(******************************************************************************)
(** ** set_map properties *)
(******************************************************************************)

Lemma set_map_union (f : A -> B) : 
  f ⋄₁ (p ∪₁ p') ⊆₁ f ⋄₁ p ∪₁ f ⋄₁ p'.
Proof. basic_solver. Qed.

Lemma set_map_inter (f : A -> B) : 
  f ⋄₁ (p ∩₁ p') ⊆₁ f ⋄₁ p ∩₁ f ⋄₁ p'.
Proof. basic_solver. Qed.

(******************************************************************************)
(** ** set_map/set_collect properties *)
(******************************************************************************)

Lemma collect_map_in_set (f : A -> B) : 
  f □₁ (f ⋄₁ p) ⊆₁ p.
Proof. basic_solver. Qed.

Lemma set_in_map_collect (f : A -> B) : 
  s ⊆₁ f ⋄₁ (f □₁ s).
Proof. basic_solver. Qed.

(******************************************************************************)
(** ** inj_dom properties *)
(******************************************************************************)

Lemma inj_dom_union 
      (f : A -> B)
      (INJ : inj_dom s f) 
      (INJ' : inj_dom s' f) 
      (DISJ : set_disjoint (f □₁ s) (f □₁ s')) :
  inj_dom (s ∪₁ s') f. 
Proof. 
  unfolder in *. 
  ins; desf; 
    try (by exfalso; eapply DISJ; eauto).
  { by apply INJ. }
    by apply INJ'. 
Qed.

Lemma inj_dom_eq (f : A -> B) (a : A) :
  inj_dom (eq a) f. 
Proof. basic_solver. Qed.

Lemma inj_dom_eq_opt (f : A -> B) (a : option A) :
  inj_dom (eq_opt a) f. 
Proof. basic_solver. Qed.

(******************************************************************************)
(** ** fixset properties *)
(******************************************************************************)

Lemma fixset_union (f : A -> A) : 
  fixset (s ∪₁ s') f <-> fixset s f /\ fixset s' f.
Proof. clear; unfolder; split; ins; intuition. Qed.

Lemma fixset_eq_dom (f g : A -> A) (EQD : eq_dom s f g) : 
  fixset s f <-> fixset s g.
Proof. 
  unfolder in *. 
  split; ins; 
    specialize (EQD x SX);
    specialize (H x SX);
    congruence.
Qed.

Lemma fixset_set_fixpoint (f : A -> A) : 
  fixset s f -> s ≡₁ f □₁ s.
Proof. 
  autounfold with unfolderDb; unfold set_subset.
  intros FIX.
  splits. 
  { ins. eexists. 
    specialize (FIX x). 
    splits; eauto. } 
  ins; desf. 
  erewrite (FIX y); auto. 
Qed.

Lemma fixset_swap (f' : A -> B) (g' : B -> A) : 
  fixset s (g' ∘ f') -> fixset (f' □₁ s) (f' ∘ g').
Proof.
  unfolder.
  intros FIX x [y [DOM Fy]].
  unfold compose. 
  rewrite <- Fy.
  fold (compose g' f' y).
  rewrite FIX; auto. 
Qed.

(******************************************************************************)
(** ** restr_rel properties *)
(******************************************************************************)

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

Lemma restr_clos_trans_eq (Hrestr : r ≡ restr_rel s r) : 
  clos_trans (r) ≡ restr_rel s (clos_trans (r)).
Proof. 
  split; [|basic_solver].
  rewrite <- restr_clos_trans. 
  by rewrite Hrestr at 1.
Qed.

Lemma seq_restr (rr rr' : relation A) :
  restr_rel s rr ⨾ restr_rel s rr' ⊆ restr_rel s (rr ⨾ rr'). 
Proof. basic_solver. Qed.

Lemma seq_restr_prcl (rr rr' : relation A)
      (PRCL : dom_rel (rr' ⨾ ⦗s⦘) ⊆₁ s) :
  restr_rel s rr ⨾ restr_rel s rr' ≡ restr_rel s (rr ⨾ rr'). 
Proof.
  split; [by apply seq_restr|].
  rewrite !restr_relE, !seqA.
  rewrite (dom_rel_helper PRCL).
  basic_solver 10.
Qed.

Lemma seq_restr_prcl_cr_r 
      (PRCL : dom_rel (r' ⨾ ⦗s⦘) ⊆₁ s) :
  restr_rel s r ⨾ (restr_rel s r')^? ≡ restr_rel s (r ⨾ r'^?). 
Proof.
  rewrite !crE, !seq_union_r, !seq_id_r.
  rewrite restr_union.
  apply union_more; [done | by apply seq_restr_prcl].
Qed.
  
Lemma seq_restr_prcl_cr_l 
      (PRCL : dom_rel (r' ⨾ ⦗s⦘) ⊆₁ s) :
  (restr_rel s r)^? ⨾ restr_rel s r' ≡ restr_rel s (r^? ⨾ r'). 
Proof.
  rewrite !crE, !seq_union_l, !seq_id_l.
  rewrite restr_union.
  apply union_more; [done | by apply seq_restr_prcl].
Qed.

Lemma seq_restr_fwcl {rr rr' : relation A}
      (FWCL : codom_rel (⦗s⦘ ⨾ rr) ⊆₁ s) :
  restr_rel s rr ⨾ restr_rel s rr' ≡ restr_rel s (rr ⨾ rr'). 
Proof.
  split; [by apply seq_restr|].
  rewrite !restr_relE, !seqA.
  seq_rewrite (codom_rel_helper FWCL).
  basic_solver 10.
Qed.

Lemma seq_restr_fwcl_cr_r 
      (FWCL : codom_rel (⦗s⦘ ⨾ r) ⊆₁ s) :
  restr_rel s r ⨾ (restr_rel s r')^? ≡ restr_rel s (r ⨾ r'^?). 
Proof.
  rewrite !crE, !seq_union_r, !seq_id_r.
  rewrite restr_union.
  apply union_more; [done | by apply seq_restr_fwcl].
Qed.
  
Lemma seq_restr_fwcl_cr_l 
      (FWCL : codom_rel (⦗s⦘ ⨾ r) ⊆₁ s) :
  (restr_rel s r)^? ⨾ restr_rel s r' ≡ restr_rel s (r^? ⨾ r'). 
Proof.
  rewrite !crE, !seq_union_l, !seq_id_l.
  rewrite restr_union.
  apply union_more; [done | by apply seq_restr_fwcl].
Qed.

Lemma immediate_restr :  
      restr_rel s (immediate r) ⊆ immediate (restr_rel s r).
Proof. basic_solver. Qed. 

Lemma transp_restr_rel :  
  restr_rel s r⁻¹ ≡ (restr_rel s r)⁻¹.
Proof. basic_solver. Qed.

Lemma restr_eqv :
  restr_rel s ⦗s'⦘ ≡ ⦗s ∩₁ s'⦘.
Proof. basic_solver. Qed.

(******************************************************************************)
(** ** prcl/fwcl properties *)
(******************************************************************************)

Lemma eqv_rel_mori' (ss ss' : A -> Prop) :
  ⦗ss⦘ ⊆ ⦗ss'⦘ -> ss ⊆₁ ss'.
Proof.
  unfolder in *. intros HH a1 a2.
  eapply HH; eauto.
Qed.

Lemma prcl_cr (rr : relation A)
      (PRCL : dom_rel (rr ⨾ ⦗s⦘) ⊆₁ s) :
  dom_rel (rr^? ⨾ ⦗s⦘) ⊆₁ s.
Proof.
  rewrite crE.
  rewrite seq_union_l, dom_union, seq_id_l.
  eapply set_subset_union_l.
  split; auto. basic_solver.
Qed.

Lemma prcl_rt (rr : relation A)
      (PRCL : dom_rel (rr ⨾ ⦗s⦘) ⊆₁ s) :
  dom_rel (rr＊ ⨾ ⦗s⦘) ⊆₁ s.
Proof.
  apply eqv_rel_mori'.
  apply rt_ind_right with (P := fun x => ⦗dom_rel (x ⨾ ⦗s⦘)⦘).
  { red. splits; [red; red|]; basic_solver 10. }
  { basic_solver. }
  intros r1 PRCL'.
  apply eqv_rel_mori' in PRCL'.
  apply eqv_rel_mori.
  rewrite seqA.
  rewrite (dom_rel_helper PRCL).
  by rewrite <- seqA, dom_seq.
Qed.

Lemma prcl_ct (rr : relation A)
      (PRCL : dom_rel (rr ⨾ ⦗s⦘) ⊆₁ s) :
  dom_rel (rr⁺ ⨾ ⦗s⦘) ⊆₁ s.
Proof.
  rewrite ct_end, seqA.
  rewrite <- dom_rel_eqv_dom_rel, PRCL.
  by apply prcl_rt.
Qed.

Lemma fwcl_cr
      (FWCL : codom_rel (⦗s⦘ ⨾ r) ⊆₁ s) :
  codom_rel (⦗s⦘ ⨾ r^?) ⊆₁ s.
Proof.
  rewrite <- tr_dom_eqv_codom in FWCL. 
  rewrite <- tr_dom_eqv_codom. 
  rewrite transp_seq, transp_eqv_rel in *.
  rewrite transp_cr in *. by apply prcl_cr.
Qed.

Lemma fwcl_rt
      (FWCL : codom_rel (⦗s⦘ ⨾ r) ⊆₁ s) :
  codom_rel (⦗s⦘ ⨾ r＊) ⊆₁ s.
Proof.
  rewrite <- tr_dom_eqv_codom in FWCL. 
  rewrite <- tr_dom_eqv_codom. 
  rewrite transp_seq, transp_eqv_rel in *.
  rewrite transp_rt in *. by apply prcl_rt.
Qed.
  
Lemma fwcl_ct 
      (FWCL : codom_rel (⦗s⦘ ⨾ r) ⊆₁ s) :
  codom_rel (⦗s⦘ ⨾ r⁺) ⊆₁ s.
Proof.
  rewrite <- tr_dom_eqv_codom in FWCL. 
  rewrite <- tr_dom_eqv_codom. 
  rewrite transp_seq, transp_eqv_rel in *.
  rewrite transp_ct in *. by apply prcl_ct.
Qed.

Lemma prcl_fwcl_swap 
      (PRCL : dom_rel (r ⨾ ⦗s⦘) ⊆₁ s)
      (FWCL : codom_rel (⦗s⦘ ⨾ r) ⊆₁ s) :
  r ⨾ ⦗s⦘ ≡ ⦗s⦘ ⨾ r. 
Proof.
    by rewrite (dom_rel_helper PRCL), (codom_rel_helper FWCL), seqA.
Qed.

Lemma restr_ct_prcl 
      (PRCL : dom_rel (r ⨾ ⦗s⦘) ⊆₁ s) :
  restr_rel s r⁺ ≡ (restr_rel s r)⁺.
Proof.
  split; [| by apply restr_ct]. 
  apply ct_ind_right with (P := fun x => restr_rel s x).
  { unfold good_ctx, Morphisms.Proper, Morphisms.respectful.
    basic_solver 10. }
  { apply ct_step. }
  intros r1 INCL.
  rewrite <- seq_restr_prcl; [| done].
  rewrite INCL.
  apply ct_unit.
Qed.

Lemma restr_rt_prcl
      (PRCL : dom_rel (r ⨾ ⦗s⦘) ⊆₁ s) :
  restr_rel s r＊ ≡ ⦗s⦘ ⨾ (restr_rel s r)＊.
Proof.
  rewrite !rtE.
  rewrite restr_union, seq_union_r.
  apply union_more; [basic_solver |].
  rewrite restr_ct_prcl; [| done].
  eapply dom_rel_helper.
  rewrite dom_ct.
  basic_solver.
Qed.

Lemma restr_cr_prcl_l
      (PRCL : dom_rel (r ⨾ ⦗s⦘) ⊆₁ s) :
  restr_rel s r^? ≡ ⦗s⦘ ⨾ (restr_rel s r)^?.
Proof.
  rewrite !crE.
  rewrite restr_union, seq_union_r.
  apply union_more; basic_solver.
Qed.

Lemma restr_cr_prcl_r
      (PRCL : dom_rel (r ⨾ ⦗s⦘) ⊆₁ s) :
  restr_rel s r^? ≡ (restr_rel s r)^? ⨾ ⦗s⦘.
Proof.
  rewrite !crE.
  rewrite restr_union, seq_union_l.
  apply union_more; basic_solver.
Qed.

Lemma fwcl_hom
      (FWCL : codom_rel (⦗s⦘ ⨾ r) ⊆₁ s)
      (FWCL' : codom_rel (⦗s'⦘ ⨾ r) ⊆₁ s'):
  codom_rel (⦗s ∪₁ s'⦘ ⨾ r) ⊆₁ s ∪₁ s'.
Proof.
  unfolder in *.
  basic_solver 10.
Qed.

(******************************************************************************)
(** ** TODO : structure other properties *)
(******************************************************************************)

Lemma seq_eqv : ⦗ s ⦘ ⨾ ⦗ s' ⦘ ≡ ⦗ s ∩₁ s' ⦘.
Proof. basic_solver. Qed.

Lemma set_compl_inter_id : set_compl s ∩₁ s ≡₁ ∅.
Proof. basic_solver. Qed.

Lemma eq_opt_someE (a : A) : eq_opt (Some a) ≡₁ eq a.
Proof. basic_solver. Qed. 

Lemma eq_opt_noneE : eq_opt (None : option A) ≡₁ ∅.
Proof. basic_solver. Qed. 

Lemma empty_irr : r ≡ ∅₂ -> irreflexive r. 
Proof. basic_solver. Qed.

Lemma restr_fun_fst (f g : A -> B) x : 
  s x -> restr_fun s f g x = f x. 
Proof. clear. unfolder. basic_solver. Qed.

Lemma restr_fun_snd (f g : A -> B) x : 
  ~ s x -> restr_fun s f g x = g x. 
Proof. clear. unfolder. basic_solver. Qed.

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

Lemma minus_disjoint : r ∩ r' ≡ ∅₂ -> r \ r' ≡ r. 
Proof. clear. basic_solver 5. Qed.

Lemma cross_minus_compl_l : s × s' \ (set_compl s) × s'' ≡ s × s'.
Proof. 
  unfolder; splits; ins; splits; desf; unfold not; ins; desf. 
Qed.

Lemma cross_minus_compl_r : s × s' \ s'' × (set_compl s') ≡ s × s'.
Proof. 
  unfolder; splits; ins; splits; desf; unfold not; ins; desf. 
Qed.
  
Lemma set_minus_inter_set_compl : s \₁ s' ≡₁ s ∩₁ set_compl s'.
Proof. basic_solver. Qed.

Lemma minus_inter_compl : r \ r' ≡ r ∩ compl_rel r'.
Proof. basic_solver. Qed.

Lemma compl_top_minus : forall (r : relation A), compl_rel r ≡ (fun _ _ => True) \ r.
Proof. basic_solver. Qed.

Lemma minus_union_r : forall (r r' r'': relation A), r \ (r' ∪ r'') ≡ (r \ r') ∩ (r \ r'').
Proof. 
  unfolder; splits; ins; desf; splits; auto.
  unfold not; basic_solver.
Qed.

Lemma minus_inter_absorb : 
  r ∩ r'' \ r' ∩ r'' ≡ r ∩ r'' \ r'.
Proof.
  split; [basic_solver|].
  unfolder. ins. splits. 
  1,2: by desf. 
  intro. desf. 
Qed.

Lemma compl_union : compl_rel (r ∪ r')  ≡ compl_rel r ∩ compl_rel r'.
Proof. 
  rewrite !compl_top_minus; by apply minus_union_r.
Qed.

Lemma seq_eqv_inter : ⦗s⦘ ⨾ (r ∩ r') ⨾ ⦗s'⦘ ≡ (⦗s⦘ ⨾ r ⨾ ⦗s'⦘) ∩ (⦗s⦘ ⨾ r' ⨾ ⦗s'⦘).
Proof. 
  rewrite !seq_eqv_lr. 
  unfold inter_rel.
  unfold same_relation, inclusion.
  splits; ins; splits; desf. 
Qed.

Lemma seq_eqv_inter_rr :
        r ∩ (r' ⨾ ⦗s⦘) ≡ r ∩ r' ⨾ ⦗s⦘.
Proof. basic_solver. Qed.

Lemma map_collect_id (f : A -> B) :
  r ⊆ f ⋄ (f □ r).
Proof. basic_solver 10. Qed.

Lemma set_subset_inter_l (LL : s ⊆₁ s'' \/ s' ⊆₁ s'') :
  s ∩₁ s' ⊆₁ s''.
Proof.
  desf.
  all: rewrite LL.
  all: basic_solver.
Qed.

Lemma set_minus_remove_l (IN : s ⊆₁ s') :
  s \₁ s'' ⊆₁ s'.
Proof. generalize IN. basic_solver. Qed.

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

Lemma clos_refl_trans_union_ext (Hrr : r ⨾ r ≡ ∅₂) (Hrr' : r ⨾ r' ≡ ∅₂) : 
  (r ∪ r')＊ ≡ r'＊ ⨾ r^?.
Proof. 
  clear r'' s s' s'' p p' p'' B C.
  rewrite crE, seq_union_r, seq_id_r.
  rewrite rt_unionE.
  rewrite <- cr_of_ct with (r := (r ⨾ r'＊)).
  rewrite crE, seq_union_r.
  apply union_more.
  { basic_solver. }
  arewrite (r ⨾ r'＊ ≡ r). 
  { rewrite <- cr_of_ct, crE, seq_union_r.
    arewrite (r ⨾ r'⁺ ≡ ∅₂).
    { split; [|basic_solver].
      intros x y HH.  
      destruct HH as [z [HA HB]].
      induction HB. 
      { eapply Hrr'. unfolder. eauto. }
      intuition. }
    basic_solver. }
  arewrite (r⁺ ≡ r); auto. 
  split. 
  { intros x y HH. 
    induction HH; auto.  
    exfalso. eapply Hrr. unfolder. eauto. }
  red. ins. constructor. auto. 
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

Lemma set_compl_union_id : s ∪₁ set_compl s ≡₁ ⊤₁.
Proof.
  split; [basic_solver|].
  intros x _.
  destruct (classic (s x)).
  { by left. }
    by right.
Qed.

Lemma set_split : s' ∪₁ s'' ≡₁ ⊤₁ -> s ≡₁ s ∩₁ s' ∪₁ s ∩₁ s''.
Proof. 
  unfolder. intros [_ HS]. 
  split; [|basic_solver].
  intros x Sx. 
  specialize (HS x I).
  basic_solver. 
Qed.

Lemma set_split_comlete : s' ≡₁ s' ∩₁ s ∪₁ s' ∩₁ (set_compl s).
Proof. 
  (* copy paste of previous lemma because of section variables :( *)
  unfolder. 
  split; [|basic_solver].
  intros x Sx. 
  pose proof set_compl_union_id as [_ HH].
  specialize (HH x I).
  unfolder in HH.
  basic_solver. 
Qed.

Lemma eqv_l_set_compl_eqv_l : r ⊆ ⦗s⦘ ⨾ r ∪ r' -> ⦗set_compl s⦘ ⨾ r ⊆ r'.
Proof. 
  rewrite !seq_eqv_l.
  intros Hr x y [nSx Rxy].
  apply Hr in Rxy.
  unfolder in Rxy. desf.
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

Lemma inter_trans : transitive r -> transitive r' -> transitive (r ∩ r').
Proof. 
  clear.
  unfolder.
  intros TR TR' x y z.
  specialize (TR x y z).
  specialize (TR' x y z).
  intuition.
Qed.

Lemma immediate_in (rr : relation A) :
  immediate rr ⊆ rr. 
Proof. basic_solver. Qed.

Lemma immediate_inter : 
  (immediate r) ∩ r' ⊆ immediate (r ∩ r').
Proof. basic_solver. Qed.

Lemma immediate_transp :
  (immediate r)⁻¹ ≡ immediate (r⁻¹).
Proof. basic_solver. Qed.

Lemma immediate_collect (rr : relation A) (f : A -> B) : 
  immediate (f □ rr) ⊆ f □ (immediate rr).
Proof. basic_solver 15. Qed. 
  
Lemma immediate_collect_inj (f : A -> B)
      (INJ : inj_dom s f) :
      f □ (immediate (restr_rel s r)) ≡ immediate (f □ (restr_rel s r)).
Proof.
  split; [|by apply immediate_collect].
  split; rename x into b1, y into b2, H into FIb12.
  { destruct FIb12 as [a1 [a2 [IRa12 [eq1 eq2]]]].
    exists a1, a2.
    splits; auto. by apply immediate_in. }
  intros b3 Fb13 Fb32.
  destruct Fb13 as [a1 [a3 [ra13 [eq11 eq33]]]].
  destruct Fb32 as [a3' [a2 [ra32 [eq33' eq22]]]].
  assert (a3 = a3').
  { cdes ra32. cdes ra13.
    apply INJ; basic_solver. }
  subst.
  cdes FIb12.
  cdes FIb0.
  apply FIb4 with (c := a3').
  { unfolder in FIb3. unfolder in ra13.
    apply INJ in FIb1; basic_solver. }
  unfolder in FIb3. unfolder in ra32.
  apply INJ in FIb2; basic_solver.
Qed.

Lemma ct_imm_split_l
      (IRR: irreflexive r)
      (TANS: transitive r)
      (acts : list A)
      (DOM_IN_ACTS: dom_rel r ⊆₁ (fun x : A => In x acts)):
  r ≡ immediate r ⨾ r^?.
Proof.
  split; [|basic_solver].
  rewrite ct_imm1 at 1; eauto.
  rewrite ct_begin. apply seq_mori; [done|].
  rewrite immediate_in. apply rt_of_trans; eauto.
Qed.

Lemma ct_imm_split_r
      (IRR: irreflexive r)
      (TANS: transitive r)
      (acts : list A)
      (DOM_IN_ACTS: dom_rel r ⊆₁ (fun x : A => In x acts)):
  r ≡ r^? ⨾ immediate r.
Proof.
  split; [|basic_solver].
  rewrite ct_imm1 at 1; eauto.
  rewrite ct_end. apply seq_mori; [|done].
  rewrite immediate_in. apply rt_of_trans; eauto.
Qed.

Lemma dwt_imm_f
      (TOTAL : downward_total r) :
  functional (immediate r)⁻¹.
Proof.
  unfold downward_total in TOTAL.
  unfolder.
  intros a1 a2 a3 [R21 HH21] [R31 HH31].
  specialize (TOTAL a2 a3 a1 R21 R31).
  destruct TOTAL as [HH|HH]; auto.
  destruct HH; exfalso; eauto.
Qed.

Lemma imm_clos_trans :
  immediate r⁺ ⊆ immediate r.
Proof.
  unfold "⊆". intros a1 a2 HH.
  apply immediate_clos_trans_elim in HH.
  specialize ct_step.
  basic_solver.
Qed.

Lemma imm_union :  
  immediate (r ∪ r') ⊆ immediate r ∪ immediate r'.
Proof. basic_solver 10. Qed.

Lemma seq_eqv_imm :  
  ⦗s⦘ ⨾ immediate r ⊆ immediate (⦗s⦘ ⨾ r).
Proof. basic_solver. Qed.

Lemma trans_prcl_immediate_seqr_split x y
      (TRANS : transitive r) (PRCL : downward_total r) (IMM : (immediate r) x y) :
  r ⨾ ⦗ eq y ⦘ ≡ (eq x ∪₁ dom_rel (r ⨾ ⦗ eq x ⦘)) × eq y.
Proof. 
  red; split. 
  { unfolder.
    intros z y' [Rzy EQy].
    split; auto.
    assert (r^= z x) as Rzx. 
    { eapply PRCL; eauto; desf.  
      by apply immediate_in. }
    unfolder in *.
    unfold clos_refl_sym in Rzx.
    desf; eauto. 
    exfalso. eapply IMM0; eauto. }
  unfolder.  ins. desf.
  { splits; desf.
    by apply immediate_in. }
  splits; desf. 
  eapply TRANS; eauto. 
  by apply immediate_in.
Qed. 

Lemma clos_refl_trans_ind_step_left 
        (R : relation A) (P : A -> Prop) x y (Px : P x)
        (rtR : R＊ x y)
        (STEP : forall z z', P z -> R z z' -> R＊ z' y -> P z') :
    P y.
Proof. 
  generalize dependent Px.
  induction rtR; auto.
  { intros Px.
    specialize (STEP x y).
    apply STEP; auto.
    apply rt_refl. }
  intros Px.
  apply IHrtR2; auto.
  apply IHrtR1; auto.
  ins. eapply STEP; eauto.
  eapply rt_trans; eauto.
Qed.

Lemma set_equiv_exp_equiv :
  s ≡₁ s' <-> forall x : A, s x <-> s' x.
Proof.
  split.
  { apply set_equiv_exp. }
  intros HH. by split; red; ins; apply HH.
Qed.

Lemma ct_seq_eqv_l :
  (⦗s⦘ ⨾ r)⁺ ≡ ⦗s⦘ ⨾ (⦗s⦘ ⨾ r)⁺.
Proof.
  apply dom_rel_helper.
  rewrite dom_ct.
  basic_solver.
Qed.

Lemma ct_seq_eqv_r :
  (r ⨾ ⦗s⦘)⁺ ≡  (r ⨾ ⦗s⦘)⁺ ⨾ ⦗s⦘.
Proof.
  apply codom_rel_helper.
  rewrite codom_ct.
  basic_solver.
Qed.

Lemma restr_id :  
  restr_rel s ⦗(fun _ : A => True)⦘ ≡ ⦗s⦘.
Proof. basic_solver. Qed.

Lemma trans_singl_rel (a1 a2 : A) :
  transitive (singl_rel a1 a2).
Proof. basic_solver. Qed.

Lemma ct_singl_rel (a1 a2 : A) :
  (singl_rel a1 a2)⁺ ≡ singl_rel a1 a2.
Proof.
  split; [|by apply ct_step].
  apply ct_of_trans, trans_singl_rel.
Qed.

Lemma dwt_imm_seq_eq (a1 a2 : A)
      (DWT : downward_total r)
      (IMM : immediate r a1 a2):
  immediate r ⨾ ⦗eq a2⦘ ≡ singl_rel a1 a2.
Proof.
  apply dwt_imm_f in DWT.
  unfolder in *.
  basic_solver 5.
Qed.

Lemma compl_seq_l
      (SYM : symmetric r)
      (TRANS : transitive r) :
  compl_rel r ⨾ r ⊆ compl_rel r.
Proof. basic_solver 10. Qed.

Lemma seq_codom_empty :
  r ⨾ r' ⊆ ∅₂ -> ⦗codom_rel r⦘ ⨾ r' ⊆ ∅₂.
Proof. basic_solver. Qed.

Lemma transp_empty :
  r ⊆ ∅₂ <-> r⁻¹ ⊆ ∅₂.
Proof. split; basic_solver. Qed.

End Props.

Require Import Setoid.

Add Parametric Morphism A : (@symmetric A) with signature
  same_relation ==> iff as symmetric_more.
Proof. unfolder. ins. desf. split; ins; auto. Qed.

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

Add Parametric Morphism A : (@downward_total A) with signature 
    same_relation ==> iff as downward_total_more.
Proof. 
  intros x y EQ. unfold downward_total. split; ins.
  eapply clos_refl_sym_more; [symmetry|]; eauto.
  2: eapply clos_refl_sym_more; eauto.
  all: apply EQ in Rxz.
  all: apply EQ in Ryz.
  all: eapply H; eauto.
Qed.

Add Parametric Morphism A B : (@eq_dom A B) with signature 
    set_equiv ==> eq ==> eq ==> iff as eq_dom_more.
Proof. 
  intros s s' Heq f g. 
  unfold eq_dom. 
  split; ins; 
    specialize (H x); 
    apply H; auto; 
    apply Heq; auto.
Qed.

Add Parametric Morphism A B : (@eq_dom A B) with signature 
    set_subset --> eq ==> eq ==> impl as eq_dom_mori.
Proof. basic_solver. Qed.

Add Parametric Morphism A B : (@inj_dom A B) with signature 
    set_equiv ==> eq ==> iff as inj_dom_more.
Proof. 
  intros s s' Heq f. red. 
  unfold inj_dom in *.
  splits; ins; specialize (H x y); apply H; auto; apply Heq; auto.
Qed.

Add Parametric Morphism A B : (@inj_dom A B) with signature 
  set_subset --> eq ==> impl as inj_dom_mori.
Proof. basic_solver. Qed.

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

Add Parametric Morphism A B : (@set_map A B) with signature 
  eq ==> set_equiv ==> set_equiv as set_map_more.
Proof. red; unfolder; splits; ins; desf; eauto. Qed.

Add Parametric Morphism A B : (@set_map A B) with signature 
  eq ==> set_subset ==> set_subset as set_map_mori.
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
  
