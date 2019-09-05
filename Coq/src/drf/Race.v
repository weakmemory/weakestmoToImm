From hahn Require Import Hahn.
From imm Require Import Events Prog RC11.
Require Import SC.

Require Import AuxRel.
Require Import EventStructure.
Require Import Consistency.
Require Import Execution.
Require Import ExecutionToGraph.
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
Notation "'F'" := (fun a => is_true (is_f lab a)).

Notation "'Rel'" := (fun a => is_true (is_rel S.(ES.lab) a)) (at level 10).
Notation "'Acq'" := (fun a => is_true (is_acq S.(ES.lab) a)) (at level 10).
Notation "'Sc'" := (fun a => is_true (is_sc S.(ES.lab) a)) (at level 10).

Definition race (X : eventid -> Prop) :=
  dom_rel (((X × X) \ (hb⁼ ∪ cf)) ∩ same_loc ∩ one_of W).

Lemma race_rw X :
  race X ⊆₁ R ∪₁ W.
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

Definition rlx_race_free (X : eventid -> Prop) :=
  race X ⊆₁ (Rel ∩₁ W) ∪₁ (Acq ∩₁ R).

Definition ra_race_free (X : eventid -> Prop) :=
  race X ⊆₁ Sc.

Lemma ra_race_free_in_rlx_race_free :
  ra_race_free ⊆₁ rlx_race_free.
Proof.
  intros X RArf.
  unfold ra_race_free in RArf.
  unfold rlx_race_free.
  arewrite (race X ⊆₁ Sc ∩₁ (R ∪₁ W)).
  { specialize race_rw. basic_solver. }
  rewrite <- ES.sc_in_rel, <- ES.sc_in_acq.
  basic_solver.
Qed.

End Race.

(* TODO: move to a more appropriate place *)
Definition program_execution P S X :=
  ⟪ STEPS : (step Weakestmo)＊ (prog_es_init P) S⟫ /\
  ⟪ EXEC : Execution.t S X ⟫.

Definition rc11_rlx_race_free_program P :=
  (forall S X, program_execution P S X -> rc11_consistent_ex S X -> rlx_race_free S X).

Definition sc_ra_race_free_program P :=
  (forall S X, program_execution P S X -> sc_consistent_ex S X -> ra_race_free S X).
