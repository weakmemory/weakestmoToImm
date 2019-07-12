Require Import Setoid Omega.
From hahn Require Import Hahn.
From imm Require Import Events.
Require Import AuxRel.

Tactic Notation "destruct_seq" constr(x)
       "as" "[" ident(y) ident(z) "]" :=
  apply seq_eqv_l in x; destruct x as [y x];
  apply seq_eqv_r in x; destruct x as [x z].

Tactic Notation "destruct_seq_l" constr(x)
       "as" ident(y) :=
  apply seq_eqv_l in x; destruct x as [y x].

Tactic Notation "destruct_seq_r" constr(x)
       "as" ident(y) :=
  apply seq_eqv_r in x; destruct x as [x y].

Export ListNotations.

Lemma pair_inj {A B} (a c : A) (b d : B) (EQ: (a, b) = (c, d)) :
  a = c /\ b = d.
Proof. ins. inv EQ. Qed.

Definition opt_same_ctor {A B} (a : option A) (b : option B) : Prop := 
  match a, b with
  | None  , None
  | Some _, Some _ => True
  | _, _ => False
  end.

Definition opt_ext {A} (def : A) (a : option A) : A := 
  match a with
  | None => def
  | Some a => a
  end.

Definition opt_to_list {A} (a : option A) : list A :=
  match a with
  | None => []
  | Some a => [a]
  end.

Definition upd_opt {A} {B} (f : A -> B) (a : option A) (b : option B) := 
  match a, b with
  | Some a, Some b => upd f a b
  | _, _ => f
  end.

Definition same_mod {A} (lab : A -> label) : relation A :=
  (fun x y => Events.mod lab x = Events.mod lab y).

Definition same_val {A} (lab : A -> label) : relation A :=
  (fun x y => Events.val lab x = Events.val lab y).

Fixpoint countNatP (p: nat -> Prop) (n : nat) : nat :=
  match n with
  | 0 => 0 
  | S n =>
    let shift := if excluded_middle_informative (p n)
                 then 1 else 0
    in
    shift + countNatP p n
  end.

Fixpoint indexed_list_helper {A} (i : nat) (l : list A) :
  list (nat * A) :=
  match l with
  | nil => nil
  | h :: l => (i, h) :: (indexed_list_helper (S i) l)
  end.

Definition indexed_list {A} (l : list A) : list (nat * A) :=
  indexed_list_helper 0 l.

Fixpoint list_to_fun {A B}
         (DEC : forall (x y : A), {x = y} + {x <> y})
         (def : B) (l : list (A * B)) : A -> B :=
  fun v =>
    match l with
    | nil => def
    | (hv, hf) :: l =>
      if DEC hv v
      then hf
      else list_to_fun DEC def l v
    end.

Lemma In_map_fst {A B} (a : A) (b : B) l (IN : In (a, b) l) :
  In a (map fst l).
Proof. induction l; inv IN; simpls; eauto. Qed.

Lemma In_map_snd {A B} (a : A) (b : B) l (IN : In (a, b) l) :
  In b (map snd l).
Proof. induction l; inv IN; simpls; eauto. Qed.

Lemma l2f_in {A B} l (a : A) (b def : B) DEC
      (NODUP : NoDup (map fst l))
      (IN : In (a,b) l) :
  list_to_fun DEC def l a = b.
Proof.
  induction l; inv IN; simpls; desf.
  { destruct (classic (b0 = b)) as [|NEQ]; auto.
    exfalso.
    eapply NoDup_cons_iff; eauto.
    simpls.
    eapply In_map_fst; eauto. }
  inv NODUP. intuition.
Qed.

Lemma l2f_v {A B} (l : list (A * B)) a def
      (DEC : forall x y : A, {x = y} + {x <> y})
      (NDP : NoDup (map fst l)) :
  (exists b,
      ⟪ BIN : In (a, b) l ⟫) \/
  ((~ exists b, ⟪ BIN : In (a, b) l ⟫) /\
   ⟪ VV  : list_to_fun DEC def l a = def ⟫).
Proof.
  induction l. 
  { right. splits; eauto.
    intros HH. desf. }
  destruct a0 as [a' b'].
  destruct (DEC a' a) as [EQ|NEQ]; subst.
  { left. eexists. splits; eauto.
    constructor. eauto. }
  simpls. inv NDP.
  apply IHl in H2. desf; [left|right].
  { eexists. splits; eauto. }
  splits; eauto. intros HH. desf.
  apply H2. eauto.
Qed.

Lemma l2f_nin {A B} l (a : A) (def : B) DEC
      (NIN : ~ exists b, In (a,b) l) :
  list_to_fun DEC def l a = def.
Proof.
  induction l; simpls.
  desf.
  2: { apply IHl. intros HH; desf. apply NIN. eauto. }
  exfalso. eapply NIN. eauto.
Qed.


Lemma indexed_list_helper_in_to_range {A} a (l : list A) m n
      (IN : In (n, a) (indexed_list_helper m l)) :
  m <= n < m + length l.
Proof.
  generalize dependent m.
  generalize dependent a.
  induction l; ins; desf.
  { omega. }
  apply IHl in IN.
  omega.
Qed.

Lemma indexed_list_helper_nodup {A} n (l : list A) :
  NoDup (indexed_list_helper n l).
Proof.
  generalize dependent n.
  induction l; ins.
  constructor.
  2: by intuition.
  intros IN. apply indexed_list_helper_in_to_range in IN. omega.
Qed.

Lemma indexed_list_nodup {A} (l : list A) : NoDup (indexed_list l).
Proof. apply indexed_list_helper_nodup. Qed.

Lemma indexed_list_helper_fst_eq {A} n (l : list A) x y
      (INX : In x (indexed_list_helper n l))
      (INY : In y (indexed_list_helper n l))
      (EQ : fst x = fst y) :
  x = y.
Proof.
  generalize dependent y.
  generalize dependent x.
  generalize dependent n.
  induction l; ins; desf.
  3: by eapply IHl; eauto.
  destruct x; simpls; desf.
  2: destruct y; simpls; desf.
  all: match goal with
       | H : In _ _ |- _ => apply indexed_list_helper_in_to_range in H; omega
       end.
Qed.

Lemma indexed_list_fst_eq {A} (l : list A) x y
      (INX : In x (indexed_list l))
      (INY : In y (indexed_list l))
      (EQ : fst x = fst y) :
  x = y.
Proof. eapply indexed_list_helper_fst_eq; eauto. Qed.

Lemma indexed_list_fst_nodup {A} (l : list A) :
  NoDup (map fst (indexed_list l)).
Proof.
  apply nodup_map.
  { apply indexed_list_helper_nodup. }
  ins. intros HH.
  eapply indexed_list_fst_eq in HH; eauto.
Qed.

Lemma indexed_list_helper_range {A} (l : list A) m n :
  (exists a, In (n, a) (indexed_list_helper m l)) <->
  m <= n < m + length l.
Proof.
  split.
  { intros [a HH]. eapply indexed_list_helper_in_to_range; eauto. }
  generalize dependent m.
  induction l; ins; desf.
  { omega. }
  apply le_lt_or_eq in H. desf.
  2: { eexists; eauto. }
  edestruct IHl as [a' HH]; eauto.
  omega.
Qed.

Lemma indexed_list_range {A} (l : list A) n :
  (exists a, In (n, a) (indexed_list l)) <->
  n < length l.
Proof.
  arewrite (n < length l <-> 0 <= n < 0 + length l).
  2: by apply indexed_list_helper_range.
  omega.
Qed.

Lemma indexed_list_helper_map_snd {A} n (l : list A) :
  map snd (indexed_list_helper n l) = l.
Proof.
  generalize dependent n.
  induction l; ins.
    by rewrite IHl.
Qed.

Lemma indexed_list_map_snd {A} (l : list A) :
  map snd (indexed_list l) = l.
Proof. apply indexed_list_helper_map_snd. Qed.

Lemma indexed_list_helper_snd_nodup {A} n a b c (l : list A) (NODUP : NoDup l)
      (INA : In (a, c) (indexed_list_helper n l))
      (INB : In (b, c) (indexed_list_helper n l)) :
  a = b.
Proof.
  generalize dependent n.
  induction l; ins; desf.
  3: { eapply IHl; eauto. inv NODUP. }
  all: exfalso.
  all: inv NODUP; apply H1.
  apply In_map_snd in INA.
  2: apply In_map_snd in INB.
  all: erewrite <- indexed_list_helper_map_snd; eauto.
Qed.

Lemma indexed_list_snd_nodup {A} a b c (l : list A) (NODUP : NoDup l)
      (INA : In (a, c) (indexed_list l))
      (INB : In (b, c) (indexed_list l)) :
  a = b.
Proof. eapply indexed_list_helper_snd_nodup; eauto. Qed.

Lemma indexed_list_helper_length {A} n (l : list A) :
  length (indexed_list_helper n l) = length l.
Proof.
  generalize dependent n.
  induction l; ins. by rewrite IHl.
Qed.

Lemma indexed_list_length {A} (l : list A) :
  length (indexed_list l) = length l.
Proof.
  unfold indexed_list.
  apply indexed_list_helper_length.
Qed.

Lemma indexed_list_helper_in_exists {A} m a (l : list A) (IN : In a l) :
  exists n, In (n, a) (indexed_list_helper m l).
Proof.
  generalize dependent m.
  induction l; ins; desf; eauto.
  specialize (IHl IN (S m)). desf. eauto.
Qed.

Lemma indexed_list_in_exists {A} a (l : list A) (IN : In a l) :
  exists n, In (n, a) (indexed_list l).
Proof. unfold indexed_list. by apply indexed_list_helper_in_exists. Qed.

Hint Unfold upd_opt : unfolderDb.

Lemma option_map_same_ctor (A B : Type) (a : option A) (f : A -> B): 
  opt_same_ctor (option_map f a) a.
Proof. unfold option_map. red. destruct a; auto. Qed.

Lemma opt_to_list_none (A : Type) : 
  opt_to_list (None : option A) = [].
Proof. by unfold opt_to_list. Qed.

Lemma opt_to_list_some (A : Type) (a : A) : 
  opt_to_list (Some a) = [a].
Proof. by unfold opt_to_list. Qed.

Lemma opt_to_list_app_singl (A : Type) (a a' : A) (b b' : option A) :
  opt_to_list b ++ [a] = opt_to_list b' ++ [a'] -> a = a' /\ b = b'.
Proof. 
  unfold opt_to_list, app. ins.
  destruct b, b'; inversion H; intuition.
Qed.

Lemma opt_to_list_app_singl_singl (A : Type) (a a' : A) (b : option A) :
  opt_to_list b ++ [a] = [a'] -> a = a' /\ b = None.
Proof. 
  unfold opt_to_list.
  destruct b as [b|];
    unfold app; intros EQ; 
    by inversion EQ. 
Qed.

Lemma opt_to_list_app_singl_pair (A : Type) (a a' : A) (b : option A) (b' : A) :
  opt_to_list b ++ [a] = [b'; a'] -> a = a' /\ b = Some b'.
Proof. 
  unfold opt_to_list.
  destruct b as [b|];
    unfold app; intros EQ; 
    by inversion EQ. 
Qed.

Lemma upd_opt_none_l (A B : Type) (f : A -> B) b : upd_opt f None b = f. 
Proof. 
  by unfold upd_opt.
Qed.

Lemma upd_opt_none_r (A B : Type) (f : A -> B) a : upd_opt f a None = f. 
Proof. 
  destruct a; by unfold upd_opt.
Qed.

Lemma upd_opt_some (A B : Type) (f : A -> B) a b : upd_opt f (Some a) (Some b) = upd f a b. 
Proof. 
  by unfold upd_opt.
Qed.

Add Parametric Morphism : countNatP with signature
    set_subset ==> eq ==> le as countP_mori.
Proof.
  ins. unfold countNatP.
  induction y0.
  { simpls. }
  ins. desf; simpls.
  1,3: omega.
  exfalso. apply n. by apply H.
Qed.

Lemma updo_opt (A B : Type) (f : A -> B) a b x 
      (NEQ : ~ eq_opt a x) 
      (CTOR : opt_same_ctor a b) : 
  upd_opt f a b x = f x.
Proof. 
  unfold upd_opt, eq_opt in *. 
  destruct a, b; auto. 
  apply updo. auto. 
Qed.

Lemma set_collect_updo_opt (A B : Type) (f : A -> B) a b s 
      (DISJ : set_disjoint s (eq_opt a)) 
      (CTOR : opt_same_ctor a b) : 
  (upd_opt f a b) □₁ s ≡₁ f □₁ s.
Proof. 
  unfold upd_opt, eq_opt, set_disjoint in *. 
  destruct a, b; auto. 
  apply set_collect_updo. 
  specialize (DISJ a).
  intuition.
Qed.

Lemma countNatP_lt e n s s' (IN : s ⊆₁ s') (NSE : ~ s e) (SE : s' e) (LE : e < n) :
  countNatP s n < countNatP s' n.
Proof.
  ins. unfold countNatP.
  generalize dependent e.
  induction n.
  { ins. omega. }
  ins. apply lt_n_Sm_le in LE.
  destruct LE as [|m].
  { desf; simpls. apply le_lt_n_Sm.
    apply countP_mori; auto. }
  apply NPeano.Nat.add_le_lt_mono.
  { destruct (excluded_middle_informative (s (S m))) as [SS|SS].
    2: omega.
    clear -IN SS. desf. exfalso. apply n. by apply IN. }
  eapply IHn; eauto.
  omega.
Qed.

Add Parametric Morphism : countNatP with signature
    set_equiv ==> eq ==> eq as countNatP_more.
Proof.
  ins.
  induction y0.
  { simpls. }
  ins. desf; simpls.
  { by rewrite IHy0. }
  { apply H in x0. desf. }
  apply H in y1. desf.
Qed.

Lemma countNatP_empty n : countNatP ∅ n = 0.
Proof. induction n; simpls; desf. Qed.

Lemma countNatP_zero s n : countNatP s n = 0 <-> forall m, s m -> n <= m.
Proof. 
  red. split. 
  { induction n. 
    { ins; omega. }
    unfold countNatP. 
    destruct (excluded_middle_informative (s n)) as [HH | nHH].
    { ins; omega. }
    rewrite Nat.add_0_l.
    intros HH m Sm. 
    eapply IHn in HH; eauto. 
    destruct HH; intuition. } 
  intros Hm. 
  induction n.  
  { ins; omega. }
  unfold countNatP. 
  destruct (excluded_middle_informative (s n)) as [HH | nHH].
  { specialize (Hm n). intuition. }
  rewrite Nat.add_0_l.
  apply IHn.
  intros m Sm.
  specialize (Hm m). 
  intuition.
Qed.

Lemma countNatP_eq m n (LT : m < n) : countNatP (eq m) n = 1.
Proof.
  generalize dependent m.
  induction n; ins; [omega|].
  destruct (excluded_middle_informative (m = n)) as [HH | nHH].
  { arewrite (countNatP (eq m) n = 0); [|omega]. 
    eapply countNatP_zero. 
    intuition. }
  rewrite Nat.add_0_l.
  rewrite Nat.lt_succ_r in LT.
  destruct LT; intuition.
Qed.

Lemma countNatP_union (s s' : nat -> Prop) n 
      (DISJ : set_disjoint s s') : 
  countNatP (s ∪₁ s') n = countNatP s n + countNatP s' n.
Proof. 
  induction n; simpls.
  destruct (excluded_middle_informative ((s ∪₁ s') n)) as [HH | nHH].
  { unfold set_union in HH. 
    destruct HH as [S | S'].
    { assert (~ s' n) as nS'. 
      { red. ins. by apply (DISJ n). }
      desf; omega. }
    assert (~ s n) as nS. 
    { red. ins. by apply (DISJ n). }
    desf; omega. }
  unfold not, set_union in nHH.
  desf; exfalso; auto.  
Qed.

Lemma countNatP_lt_eq (s : nat -> Prop) m n (LT : m < n) (HH : forall e (EE : s e), e < m):
  countNatP s n = countNatP s m.
Proof.
  generalize dependent m.
  induction n; ins.
  { omega. }
  apply le_lt_or_eq in LT. desf; simpls.
  2: { apply IHn; auto. omega. }
  all: exfalso; apply HH in s0; omega.
Qed.

Fixpoint first_nat_list (n : nat) : list nat :=
  match n with
  | 0 => []
  | S m => m :: first_nat_list m
  end.

Lemma first_nat_list_In_alt (n m : nat) : In m (first_nat_list n) <-> m < n.
Proof.
  induction n; simpls.
  { omega. }
  split; intros HH; desf.
  { specialize_full IHn; auto. }
  inversion HH; auto.
Qed.

Lemma app_eq_unit2 {A} (x y : list A) (a b : A)
      (EQ : x ++ y = [a; b]) :
  x = [] /\ y = [a; b] \/
  x = [a] /\ y = [b] \/
  x = [a; b] /\ y = [].
Proof.
  destruct x; simpls; eauto.
  inv EQ.
  apply app_eq_unit in H0. desf; eauto.
Qed.
