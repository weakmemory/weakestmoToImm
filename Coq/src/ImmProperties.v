Require Import Omega.
From hahn Require Import Hahn.
From PromisingLib Require Import Basic.
From imm Require Import 
     AuxDef 
     Events Execution Execution_eco imm_s_hb imm_s imm_common
     Prog ProgToExecution ProgToExecutionProperties
     CombRelations CombRelationsMore
     SimState
     TraversalConfig Traversal TraversalConfigAlt SimTraversal SimTraversalProperties
     CertExecution2.
Require Import AuxRel.
Require Import AuxDef.

Set Implicit Arguments.

Section Properties.

Variable G : execution.

Notation "'E'" := G.(acts_set).

Notation "'Tid' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid' t" := (fun x => tid x <> t) (at level 1).

Variable WF : Wf G.
Variable sc : relation actid.
Variable CON : imm_consistent G sc.

Variable TC : trav_config.
Variable TCCOH : tc_coherent G sc TC.

Notation "'C'" := (covered TC).
Notation "'I'" := (issued TC).

Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).

Notation "'fr'" := G.(fr).
Notation "'coe'" := G.(coe).
Notation "'coi'" := G.(coi).
Notation "'deps'" := G.(deps).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).
Notation "'detour'" := G.(detour).
Notation "'hb'" := G.(hb).
Notation "'sw'" := G.(sw).
Notation "'release'" := G.(release).

Notation "'lab'" := G.(lab).
(* Notation "'loc'" := (loc lab). *)
(* Notation "'val'" := (val lab). *)
(* Notation "'mod'" := (mod lab). *)
(* Notation "'same_loc'" := (same_loc lab). *)

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'Loc_' l" := (fun x => loc lab x = Some l) (at level 1).
Notation "'W_ex'" := G.(W_ex).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Lemma rfi_D_in_D thread (NINIT : thread <> tid_init):
  dom_rel (rfi ⨾ ⦗ D G TC thread ⦘) ⊆₁ D G TC thread.
Proof.
  intros w [r RFI]. destruct_seq_r RFI as DR.
  apply wf_rfiD in RFI; auto. destruct_seq RFI as [WW RR].
  apply wf_rfiE in RFI; auto. destruct_seq RFI as [EW ER].
  red in DR. unfold set_union in DR. desf.
  { apply C_in_D. eapply dom_sb_covered; eauto.
    eexists. apply seq_eqv_r. split; eauto. apply RFI. }
  { eapply issuedW in DR; eauto. type_solver. }
  { red. do 3 left. right. split; auto.
    edestruct sb_tid_init as [AA|AA]; auto.
    { apply RFI. }
    { rewrite AA. apply DR. }
    destruct w; simpls. intros BB; desf. }
  { red. do 2 left. right.
    destruct DR as [z [v [[EE|EE] DR]]].
    { desf. generalize RFI DR. basic_solver 10. }
    apply wf_rfiD in EE; auto. destruct_seq EE as [WR RV].
    clear -RR WR. type_solver. }
  { apply I_in_D. destruct DR as [v DR].
    destruct_seq_l DR as IV.
    assert (v = w); desf.
    eapply wf_rff; eauto.
    { apply DR. }
    apply RFI. }
  destruct DR as [v DR].
  destruct_seq_r DR as IV.
  assert (v = w); desf.
  { eapply wf_rff; eauto.
    { apply DR. }
    apply RFI. }
  unfold Execution.rfi, Execution.rfe in *.
  generalize RFI DR. basic_solver.
Qed.

Lemma rfe_E0D_in_D thread (NINIT : thread <> tid_init):
  dom_rel (rfe ⨾ ⦗ Tid_ thread ∩₁ (C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘))
               ∩₁ D G TC thread ⦘) ⊆₁
          D G TC thread.
Proof.
  intros w [r RFE]. destruct_seq_r RFE as DR.
  apply wf_rfeD in RFE; auto. destruct_seq RFE as [WW RR].
  apply wf_rfeE in RFE; auto. destruct_seq RFE as [EW ER].
  destruct DR as [[TR EE0] DR].
  assert (C r -> D G TC thread w) as UU.
  { intros HH. apply I_in_D. eapply dom_rf_covered; eauto.
    eexists. apply seq_eqv_r. split; eauto. apply RFE. }
  destruct EE0 as [EE0|EE0].
  { intuition. }

  red in DR. unfold set_union in DR. desf.
  { intuition. }
  { eapply issuedW in DR; eauto. type_solver. }
  { exfalso. by apply DR. }
  { red. apply I_in_D.
    destruct DR as [z [v [[EE|EE] DR]]].
    2: { apply wf_rfiD in EE; auto. destruct_seq EE as [WR RV].
         clear -RR WR. type_solver. }
    desf. eapply dom_rfe_ppo_issued; eauto.
    do 2 eexists. eauto. }
  { exfalso. destruct DR as [v DR].
    destruct_seq_l DR as IV.
    assert (v = w); desf.
    eapply wf_rff; eauto.
    { apply DR. }
    { apply RFE. }
    apply RFE. apply DR. }
  destruct EE0 as [t EE0]. destruct_seq_r EE0 as IT.
  destruct EE0 as [|EE0]; subst.
  { eapply issuedW in IT; eauto. type_solver. }
  apply I_in_D.
  eapply dom_rfe_acq_sb_issued; eauto.
  destruct DR as [v DR].
  destruct_seq_r DR as IV.
  assert (v = w); desf.
  { eapply wf_rff; eauto.
    { apply DR. }
    apply RFE. }
  generalize DR IV IT EE0. basic_solver 10.
Qed.

Lemma rf_E0D_in_D thread (NINIT : thread <> tid_init):
  dom_rel (rf ⨾ ⦗ Tid_ thread ∩₁ (C ∪₁ dom_rel (sb^? ⨾ ⦗I⦘))
               ∩₁ D G TC thread ⦘) ⊆₁
          D G TC thread.
Proof.
  intros w [r RF]. destruct_seq_r RF as DR.
  apply rfi_union_rfe in RF. destruct RF as [RF|RF].
  { apply rfi_D_in_D; auto. eexists.
    apply seq_eqv_r; split; eauto. apply DR. }
  apply rfe_E0D_in_D; auto. eexists.
  apply seq_eqv_r; split; eauto.
Qed.

Lemma itrav_step_thread_ninit prog e TC'
      (GPROG : program_execution prog G)
      (PROG_NINIT : ~ (IdentMap.In tid_init prog))
      (STEP : itrav_step G sc e TC TC') :
  tid e <> tid_init.
Proof.
  intros AA.
  assert (E e) as EE.
  { cdes STEP. desf.
    { apply COV. }
    apply ISS. }
  assert (is_init e) as INIT.
  { eapply tid_initi; eauto. by split. }
  cdes STEP. desf.
  { apply NEXT. eapply init_covered; eauto. by split. }
  apply NISS. eapply init_issued; eauto. by split.
Qed.

Lemma isim_trav_step_thread_ninit prog thread TC'
      (GPROG : program_execution prog G)
      (PROG_NINIT : ~ (IdentMap.In tid_init prog))
      (STEP : isim_trav_step G sc thread TC TC') :
  thread <> tid_init.
Proof.
  apply sim_trav_step_to_step in STEP. desf.
  eapply itrav_step_thread_ninit; eauto.
Qed.

End Properties.
