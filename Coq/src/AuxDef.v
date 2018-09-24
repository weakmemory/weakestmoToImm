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