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
Notation "'F'" := (fun a => is_true (is_f lab a)).

Notation "'Sc'" := (fun a => is_true (is_sc lab a)).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).

Notation "'same_loc'" := (same_loc lab).

Definition race :=
  dom_rel (((E × E) \ hb⁼) ∩ same_loc ∩ one_of W).

(* TODO: unify with Race.race_rw *)
Lemma race_rw :
  race ⊆₁ R ∪₁ W.
Proof.
  unfold race.
  unfold Events.same_loc.
  assert (HH : (R ∪₁ (W ∪₁ F)) \₁ F ⊆₁ R ∪₁ W) by basic_solver.
  rewrite <- HH.
  rewrite set_minus_inter_set_compl.
  apply set_subset_inter_r. split.
  { unfolder. ins.
    apply lab_rwf. }
  rewrite interA, inclusion_inter_l2.
  intros x [y [EQ_LAB ONE]].
  unfold set_compl, is_f.
  unfold one_of, is_w in ONE.
  unfold loc in EQ_LAB.
  desf.
Qed.

Definition ra_race_free_G :=
  race ⊆₁ Sc.

Definition rlx_race_free_G :=
  race ⊆₁ (Rel ∩₁ W) ∪₁ (Acq ∩₁ R).

(* TODO: move to more appropriate place or unify with ES.sc_in_rel *)
Lemma sc_in_rel :
  Sc ⊆₁ Rel.
Proof.
  unfold is_sc, is_rel.
  basic_solver.
Qed.

(* TODO: move to more appropriate place or unify with ES.sc_in_acq *)
Lemma sc_in_acq :
  Sc ⊆₁ Acq.
Proof.
  unfold is_sc, is_acq.
  basic_solver.
Qed.

(* TODO: redefine using ⊆₁ *)
Lemma ra_race_free_G_in_rlx_race_free_G :
  ra_race_free_G -> rlx_race_free_G.
Proof.
  intros RArf.
  unfold ra_race_free_G in RArf.
  unfold rlx_race_free_G.
  arewrite (race ⊆₁ Sc ∩₁ (R ∪₁ W)).
  { specialize race_rw. basic_solver. }
  rewrite <- sc_in_rel, <- sc_in_acq.
  basic_solver.
Qed.


End Race_G.


Definition sc_ra_race_free_program_G P :=
  (forall G, ProgToExecutionProperties.program_execution P G -> sc_consistent G -> ra_race_free_G G).

Definition rc11_rlx_race_free_program_G P :=
  (forall G, ProgToExecutionProperties.program_execution P G -> rc11_consistent G -> rlx_race_free_G G).
