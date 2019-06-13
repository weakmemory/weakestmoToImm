From hahn Require Import Hahn.
From imm Require Import Events.
Require Import AuxRel.
Require Import EventStructure.
Require Import Consistency.
Require Import Execution.

Module Races.
  
Section Races.

Variable S : ES.t.

Notation "'lab'" := S.(ES.lab).

Notation "'cf'" := S.(ES.cf).
Notation "'hb'" := S.(hb).


Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).

Notation "'Rel'" := (fun a => is_true (is_rel S.(ES.lab) a)) (at level 10).
Notation "'Acq'" := (fun a => is_true (is_acq S.(ES.lab) a)) (at level 10).
Notation "'Sc'" := (fun a => is_true (is_sc S.(ES.lab) a)) (at level 10).

Definition one {A : Type} (X : A -> Prop) a b := X a \/ X b. 

Definition race (X : eventid -> Prop) :=
  dom_rel ((X × X) \ (hb⁼ ∪ cf) ∩ same_loc ∩ one W). (* hb should be hbc11? *)

Definition RLX_race_free (X : eventid -> Prop) :=
  race X ⊆₁ (Rel ∩₁ W) ∪₁ (Acq ∩₁ R). 
       
Definition RA_race_free (X : eventid -> Prop) :=
  race X ⊆₁ Sc.

End Races.

End Races.
