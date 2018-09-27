Require Import Setoid Omega.
From hahn Require Import Hahn.
From imm Require Import Events.

Tactic Notation "destruct_seq" constr(x)
       "as" "[" ident(y) ident(z) "]" :=
  apply seq_eqv_l in x; destruct x as [y x];
  apply seq_eqv_r in x; destruct x as [x z].

Export ListNotations.

Definition opt_to_list {A} (a : option A) : list A :=
  match a with
  | None => []
  | Some a => [a]
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