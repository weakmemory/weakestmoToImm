From hahn Require Import Hahn.
From imm Require Import Events Prog RC11.
Require Import SC.

Require Import AuxRel.
Require Import EventStructure.
Require Import Consistency.
Require Import Execution.
Require Import ExecutionToG.
Require Import Step.
Require Import ProgES.

Section Race.

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

Definition rc11_consistent_x (S : ES.t) (X : eventid -> Prop) := exists G,
    ⟪ x2g  : X2G S X G ⟫ /\
    ⟪ rc11 : rc11_consistent G ⟫.

Definition RA_race_free (X : eventid -> Prop) :=
  race X ⊆₁ Sc.

Definition sc_consistent_x (S : ES.t) (X : eventid -> Prop) := exists G,
    ⟪ x2g  : X2G S X G ⟫ /\
    ⟪ sc : sc_consistent G ⟫.

End Race.

Definition program_execution P S X :=
  ⟪ STEPS : (step Weakestmo)＊ (prog_es_init P) S⟫ /\
  ⟪ EXEC : Execution.t S X ⟫.

Definition RC11_RLX_race_free_program P :=
  (forall S X, program_execution P S X -> rc11_consistent_x S X -> RLX_race_free S X).

Definition SC_RA_race_free_program P :=
  (forall S X, program_execution P S X -> sc_consistent_x S X -> RA_race_free S X).
