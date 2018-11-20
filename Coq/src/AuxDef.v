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

Definition same_val {A} (lab : A -> label) : relation A :=
  (fun x y => val lab x = val lab y).

Fixpoint countNatP (p: nat -> Prop) (n : nat) : nat :=
  match n with
  | 0 => 0 
  | S n =>
    let shift := if excluded_middle_informative (p n)
                 then 1 else 0
    in
    shift + countNatP p n
  end.

Hint Unfold upd_opt : unfolderDb.

Lemma opt_to_list_none (A : Type) : 
  opt_to_list (None : option A) = [].
Proof. by unfold opt_to_list. Qed.

Lemma opt_to_list_some (A : Type) (a : A) : 
  opt_to_list (Some a) = [a].
Proof. by unfold opt_to_list. Qed.

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
