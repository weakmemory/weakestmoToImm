From hahn Require Import Hahn.
From imm Require Import Events Execution imm_s_hb Prog ProgToExecutionProperties RC11.

Require Import SC.

Require Import AuxRel. (* ⁼ *)

Set Implicit Arguments.

Section Race_G.

Variable G : execution.

Notation "'E'" := G.(acts_set).
Notation "'lab'" := G.(lab).
Notation "'hb'" := G.(hb).

Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'R'" := (fun a => is_true (is_r lab a)).

Notation "'Sc'" := (fun a => is_true (is_sc lab a)).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).

Notation "'same_loc'" := (same_loc lab).

Definition one {A : Type} (X : A -> Prop) a b := X a \/ X b.

Definition race :=
  dom_rel (((E × E) \ hb⁼) ∩ same_loc ∩ one W).

Definition ra_race_free_G :=
  race ⊆₁ Sc.

Definition rlx_race_free_G :=
  race ⊆₁ (Rel ∩₁ W) ∪₁ (Acq ∩₁ R).

End Race_G.

Definition sc_ra_race_free_program_G P :=
  (forall G, ProgToExecutionProperties.program_execution P G -> sc_consistent G -> ra_race_free_G G).

Definition rc11_rlx_race_free_program_G P :=
  (forall G, ProgToExecutionProperties.program_execution P G -> rc11_consistent G -> rlx_race_free_G G).
