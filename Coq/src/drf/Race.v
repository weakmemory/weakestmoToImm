From hahn Require Import Hahn.
From imm Require Import Events Prog RC11 Execution.
Require Import SC.

Require Import AuxRel.
Require Import EventStructure.
Require Import Consistency.
Require Import Execution.
Require Import ExecutionToGraph.
Require Import Step.
Require Import ProgES.
Require Import EventToAction.
Require Import ExecutionEquivalence.

Require Import Race_G.

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

Definition rc11_rlx_race_free_program P :=
  (forall S X, program_execution P S X -> rc11_consistent_ex S X -> rlx_race_free S X).

Definition sc_ra_race_free_program P :=
  (forall S X, program_execution P S X -> sc_consistent_ex S X -> ra_race_free S X).

Lemma X2G_race_transfer S X G
      (WF : ES.Wf S)
      (WF_G : Wf G)
      (EXEC : Execution.t S X)
      (MATCH : X2G S X G) :
  e2a S □₁ race S X ⊆₁ Race_G.race G.
Proof.
  intros a [e [HH EQ]].
  desf.
  destruct HH as [e' HH].
  exists (e2a S e').
  assert (INCL : e2a S □ ((X × X \ ((hb S)⁼ ∪ ES.cf S)) ∩
                          same_loc (ES.lab S) ∩
                          one_of (fun a : eventid => is_w (ES.lab S) a))
                 ⊆
                 (acts_set G × acts_set G \ (imm_s_hb.hb G)⁼) ∩
                 same_loc (lab G) ∩
                 one_of (fun a : actid => is_w (lab G) a)).
  { arewrite ((X × X \ ((hb S)⁼ ∪ ES.cf S)) ∩
              same_loc (ES.lab S) ∩
              one_of (fun a : eventid => is_w (ES.lab S) a)
              ⊆
              (X × X \ ((hb S)⁼ ∪ ES.cf S)) ∩
              restr_rel X (same_loc (ES.lab S)) ∩
              one_of (X ∩₁ (fun a : eventid => is_w (ES.lab S) a)))
      by basic_solver.
    rewrite !collect_rel_interi, collect_rel_one_of.
    rewrite X2G_same_loc, <- X2G_W; eauto.
    arewrite (e2a S □ (X × X \ ((hb S)⁼ ∪ ES.cf S)) ⊆
              acts_set G × acts_set G \ (imm_s_hb.hb G)⁼).
    { rewrite minus_union_r.
      rewrite minus_disjoint with (r' := ES.cf S).
      2: { rewrite interC, <- restr_cross, restr_relE.
           split; [by apply Execution.ex_ncf | done]. }
      rewrite inclusion_inter_l1.
      arewrite (X × X \ (hb S)⁼ ⊆ X × X \ (restr_rel X (hb S)⁼)).
      rewrite collect_rel_minus_inj.
      2,3: rewrite (hbE S WF); destruct EXEC;
        specialize e2a_inj; basic_solver.
      arewrite (acts_set G × acts_set G \ (imm_s_hb.hb G)⁼ ≡
                acts_set G × acts_set G \ restr_rel (acts_set G) (imm_s_hb.hb G)⁼).
      { split; [apply inclusion_minus_mon|]; basic_solver 5. }
      apply inclusion_minus_mon.
      { cdes MATCH. by rewrite collect_rel_cross, GACTS. }
      rewrite crs_restr2.
      rewrite crs_restr2 with (s := X).
      rewrite collect_rel_union.
      apply inclusion_union_mon.
      { rewrite !restr_eqv. cdes MATCH. relsf.
        by rewrite collect_rel_eqv, GACTS. }
      rewrite <- !cs_restr, cs_collect_rel.
      rewrite X2G_hb_transfer'; eauto.
      basic_solver 10. }
    basic_solver. }
  eapply map_collect_id in HH.
  by apply INCL in HH.
Qed.

Lemma rlx_race_free_transer S X G
      (WF : ES.Wf S)
      (WF_G : Wf G)
      (EXEC : Execution.t S X)
      (MATCH : X2G S X G)
      (RLX_RACE_FREE_G : rlx_race_free_G G) :
  rlx_race_free S X.
Proof.
  unfold rlx_race_free.
  eapply set_subset_trans.
  2: { apply set_subset_inter_l with (s := X).
       right. apply set_subset_rel. }
  eapply set_subset_collect_inj with (s := race S X) (f := e2a S).
  { unfold race. destruct EXEC.
    specialize e2a_inj. basic_solver. }
  rewrite X2G_race_transfer; eauto.
  unfold rlx_race_free_G in RLX_RACE_FREE_G.
  arewrite (Race_G.race G ⊆₁ Race_G.race G ∩₁ acts_set G)
    by unfold Race_G.race; basic_solver.
  rewrite RLX_RACE_FREE_G.
  rewrite set_inter_union_r.
  rewrite set_collect_union.
  assert (HH : forall (s s' s'' : eventid -> Prop), s ∩₁ (s' ∩₁ s'') ≡₁ (s ∩₁ s') ∩₁ (s ∩₁ s''))
    by basic_solver.
  rewrite HH, set_collect_inter_inj.
  2: { destruct EXEC. specialize e2a_inj. basic_solver. }
  rewrite <- X2G_W, <- X2G_Rel; eauto.

  rewrite HH, set_collect_inter_inj.
  2: { destruct EXEC. specialize e2a_inj. basic_solver. }
  rewrite <- X2G_R, <- X2G_Acq; eauto.
  basic_solver 10.
Qed.

Lemma rc11_rlx_race_free_program_transfer P
      (NINIT : ~ Basic.IdentMap.In tid_init P)
      (RACE_FREE_G : rc11_rlx_race_free_program_G (stable_prog_to_prog P)) :
  rc11_rlx_race_free_program P.
Proof.
  intros S X EXEC RC11.
  cdes EXEC.
  specialize (X2G_steps P S X EXEC) as HH.
  desf.
  eapply rlx_race_free_transer; eauto.
  { eby eapply steps_es_wf. }
  apply RACE_FREE_G; auto.
  unfold rc11_consistent_ex in RC11.
  desf.
  apply rc11_x_equiv with (G := G0); auto.
  eapply X2G_x_equiv; eauto.
  { eby eapply steps_es_wf. }
  { eby eapply steps_es_consistent. }
  basic_solver.
Qed.
