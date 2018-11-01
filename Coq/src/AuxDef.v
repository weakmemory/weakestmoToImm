Require Import Setoid Omega.
From hahn Require Import Hahn.
From imm Require Import Events.

Tactic Notation "destruct_seq" constr(x)
       "as" "[" ident(y) ident(z) "]" :=
  apply seq_eqv_l in x; destruct x as [y x];
  apply seq_eqv_r in x; destruct x as [x z].

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

Fixpoint countNatP (f: nat -> Prop) (n : nat) : nat :=
  match n with
  | 0 => 0 
  | S n =>
    let shift := if excluded_middle_informative (f n)
                 then 1 else 0
    in
    shift + countNatP f n
  end.

Hint Unfold upd_opt : unfolderDb.

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