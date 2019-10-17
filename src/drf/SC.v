
(******************************************************************************)
(** * Definition of the SC memory model *)
(******************************************************************************)
From hahn Require Import Hahn.
From imm Require Import Execution.
Set Implicit Arguments.
Remove Hints plus_n_O.

Section SC.

Variable G : execution.

Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'fr'" := G.(fr).

(******************************************************************************)
(** ** Consistency  *)
(******************************************************************************)

Definition sc_consistent :=
  ⟪ Comp : complete G ⟫ /\
  ⟪ Cat  : rmw_atomicity G ⟫ /\
  ⟪ Cacyclic : acyclic (sb ∪ rf ∪ co ∪ fr) ⟫.

End SC.
