From hahn Require Import Hahn.
From imm Require Import Events Prog ProgToExecutionProperties RC11.
From PromisingLib Require Import Basic Language.
Require Import AuxDef.
Require Import AuxRel.
Require Import EventStructure.
Require Import Consistency.
Require Import Execution.
Require Import Step.
Require Import Race.
Require Import ProgES.
Require Import StepWf.
Require Import ExecutionToG.

Set Implicit Arguments.

Lemma steps_es_wf P
      (nInitProg : ~ IdentMap.In tid_init P)
      (S : ES.t)
      (STEPS : (step Weakestmo)＊ (prog_es_init P) S) :
  ES.Wf S.
Proof.
Admitted.

Lemma steps_es_consistent P
      (S : ES.t)
      (STEPS : (step Weakestmo)＊ (prog_es_init P) S) :
  @es_consistent S Weakestmo.
Proof.
  apply rtE in STEPS.
  unfolder in STEPS. desf.
  { apply prog_es_init_consistent. }
  assert (HH :  codom_rel (step Weakestmo) S).
  { apply codom_ct.
    basic_solver. }
  cdes HH.
  unfold step in HH0. desf.
Qed.

(*
Lemma basic_step_init_loc e e' S S'
      (BSTEP : BasicStep.basic_step e e' S S')
      (WF : ES.Wf S) :
  ES.init_loc S ≡₁ ES.init_loc S'.
Proof.
  specialize (BasicStep.basic_step_acts_init_set BSTEP WF) as EINIT.
  unfolder. splits; unfold ES.init_loc; ins; desf.
  { exists a. splits; [by apply EINIT|].
    arewrite (loc S' a = loc S a); [|done].
    apply (BasicStep.basic_step_loc_eq_dom BSTEP).
    apply ES.acts_set_split. basic_solver. }
  exists a. splits; [by apply EINIT|].
  arewrite (loc S a = loc S' a); [|done].
  rewrite (BasicStep.basic_step_loc_eq_dom BSTEP); auto.
  apply EINIT in EINA.
  apply ES.acts_set_split. basic_solver.
Qed.

Notation "'thread_syntax' t"  :=
  (Language.syntax (thread_lts t)) (at level 10, only parsing).

Notation "'thread_init_st' t" :=
  (Language.init (thread_lts t)) (at level 10, only parsing).

Notation "'thread_cont_st' t" :=
  (fun st => existT _ (thread_lts t) st) (at level 10, only parsing).

Notation "'thread_st' t" :=
  (Language.state (thread_lts t)) (at level 10, only parsing).

Notation "'K' S" := (ES.cont_set S) (at level 1).

Lemma wf_es P
      (nInitProg : ~ IdentMap.In tid_init P)
      (S : ES.t)
      (STEPS : (step Weakestmo)＊ (prog_es_init P) S):
  ⟪ LTS : forall k lang (state : lang.(Language.state))
            (INK : K S (k, existT _ lang state)),
      lang = thread_lts (ES.cont_thread S k) ⟫ /\
  ⟪ INIT_LOC : ES.init_loc S ≡₁ ES.init_loc (prog_es_init P) ⟫ /\
  ⟪ contreach :
      forall k (state : thread_st (ES.cont_thread S k))
        (lprog : thread_syntax (ES.cont_thread S k))
        (INPROG : IdentMap.find (ES.cont_thread S k) (stable_prog_to_prog P) =
                  Some lprog)
        (INK : K S (k, thread_cont_st (ES.cont_thread S k) state)),
        (ProgToExecution.step (ES.cont_thread S k))＊
                                   (thread_init_st (ES.cont_thread S k) lprog)
                                   state ⟫ /\
  ⟪ WF : ES.Wf S ⟫.
Proof.
  eapply clos_refl_trans_ind_left with (z := S); eauto.
  { splits; [| done | | admit].
    { ins. unfold ES.cont_thread.
      unfold prog_es_init, prog_l_es_init, ES.init, ES.cont_set, ES.cont, prog_init_K in INK.
      apply in_map_iff in INK. desf. }
    admit. }
  clear dependent S.
  intros S S' STESPS IH STEP.
  assert(LTS': forall (k : cont_label)
                (lang : Language.t)
                (state : Language.state lang),
            (K S') (k, existT Language.state lang state) ->
            lang = thread_lts (ES.cont_thread S' k)).
  { intros k lang state INK.
    cdes STEP. cdes BSTEP.
    eapply BasicStep.basic_step_cont_set in INK; eauto.
    red in INK. desf.
    { erewrite BasicStep.basic_step_cont_thread; eauto. }
    cdes BSTEP_; desf.
    apply LTS in CONT; subst.
    erewrite <- BasicStep.basic_step_cont_thread; eauto. }
  assert (INIT_LOC': ES.init_loc S' ≡₁ ES.init_loc (prog_es_init P)).
  { cdes STEP.
    erewrite <- basic_step_init_loc; eauto. }
  splits; auto; desf. admit.
  clear contreach.

  cdes STEP.
  cdes BSTEP.
  eapply step_wf; eauto.
  ins.
  apply INIT_LOC'.
  apply prog_es_init_init_loc.

  cdes BSTEP_.
  assert (CONT'' : (K S') (k', existT Language.state lang st')).
  { red. rewrite CONT'. basic_solver. }
  apply LTS' in CONT'' as HH. subst.
  simpls. desf.
  simpls.

  unfold LblStep.ilbl_step in STEP0.
  unfold LblStep.ineps_step in STEP0.
  unfold ProgToExecution.istep in STEP0.
Admitted.
 *)

(******************************************************************************)
(** ** Prefix executional properties *)
(******************************************************************************)

Section HB_prefix.

Variable S : ES.t.
Variable WF : ES.Wf S.

Notation "'E'" := S.(ES.acts_set).
Notation "'Einit'" := S.(ES.acts_init_set).
Notation "'Eninit'" := S.(ES.acts_ninit_set).

Notation "'sb'" := S.(ES.sb).
Notation "'rmw'" := S.(ES.rmw).
Notation "'jf'" := S.(ES.jf).
Notation "'rf'" := S.(ES.rf).
Notation "'cf'" := S.(ES.cf).
Notation "'hb'" := S.(hb).
Notation "'jfe'" := S.(ES.jfe).

Notation "'lab'" := S.(ES.lab).
Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).


Definition hb_pref v := dom_rel (hb^? ⨾ ⦗eq v⦘).

Definition hb_pref2 v1 v2 := dom_rel (hb^? ⨾ (⦗eq v1⦘ ∪ ⦗eq v2⦘)).

Lemma hb_pref2_alt v1 v2:
  hb_pref2 v1 v2 ≡₁ hb_pref v1 ∪₁ hb_pref v2.
Proof.
  unfold hb_pref, hb_pref2.
  basic_solver 10.
Qed.

Lemma hb_pref_inE (v : eventid)
      (vE : E v) :
  hb_pref v ⊆₁ E.
Proof.
  unfold hb_pref.
  rewrite hbE; auto.
  basic_solver.
Qed.

Lemma hb_pref2_inE v1 v2
      (v1E : E v1)
      (v2E : E v2) :
  hb_pref2 v1 v2 ⊆₁ E.
Proof.
  rewrite hb_pref2_alt.
  rewrite !hb_pref_inE; auto.
  basic_solver.
Qed.

Lemma init_in_hb_pref v
      (vEninit : Eninit v) :
  Einit ⊆₁ hb_pref v.
Proof.
  unfold hb_pref.
  rewrite <- sb_in_hb.
  rewrite <- ES.sb_init; auto.
  basic_solver 10.
Qed.

Lemma hb_pref_hb_bwcl v :
  dom_rel (hb ⨾ ⦗hb_pref v⦘) ⊆₁ hb_pref v.
Proof.
  unfold hb_pref.
  specialize (hb_trans S).
  basic_solver 10.
Qed.

Variable CONS : es_consistent S (m := Weakestmo).

Lemma hb_pref_rmw_fwcl v
      (nvRMW : ⦗eq v⦘ ⨾ rmw ⊆ ∅₂) :
  codom_rel (⦗hb_pref v⦘ ⨾ rmw) ⊆₁ hb_pref v.
Proof.
   unfold hb_pref.
   rewrite codom_rel_eqv_dom_rel, <- tr_dom_eqv_codom.
   apply dom_rel_mori.
   rewrite !transp_seq, !transp_inv.
   rewrite crE at 1.
   rewrite seq_union_l, seq_union_r, seq_id_l.
   apply inclusion_union_l.
   { apply inclusion_transpE.
     rewrite transp_seq, transp_eqv_rel, transp_inv.
     rewrite nvRMW. basic_solver. }
   eby rewrite <- seqA, t_rmw_hb_in_hb.
Qed.

Lemma jf_prcl_rf_compl {A}
      (AE : A ⊆₁ E)
      (JF_PRCL : dom_rel(jf ⨾ ⦗A⦘) ⊆₁ A):
  A ∩₁ R ⊆₁ codom_rel (⦗A⦘ ⨾ rf).
Proof.
  rewrite <- set_interK with (s := A) at 1.
  rewrite AE at 2; auto.
  rewrite set_interA, (ES.jf_complete WF).
  rewrite set_interC, <- codom_eqv1.
  rewrite (dom_rel_helper JF_PRCL).
  rewrite ES.jf_in_rf; auto.
  basic_solver.
Qed.

Lemma hb_pref2_ncf e w
      (JF : jf w e):
  ES.cf_free S (hb_pref2 e w).
Proof.
  unfold hb_pref2.
  red. rewrite eqv_dom_in_seq_tr, !seqA.
  arewrite ((hb^? ⨾ (⦗eq e⦘ ∪ ⦗eq w⦘))⁻¹ ⨾
             cf ⨾
             hb^? ⨾ (⦗eq e⦘ ∪ ⦗eq w⦘) ⊆ ∅₂); [|basic_solver].
  rewrite transp_seq, transp_union, transp_cr, !transp_eqv_rel, !seqA.
  rewrite !seq_union_r, !seq_union_l.
  apply inclusion_union_l; apply inclusion_union_l.
  1, 4:
    rewrite <- seqA with (r3 := hb^? ⨾ ⦗eq _⦘);
    rewrite <- seqA with (r3 := ⦗eq _⦘);
    rewrite <- restr_relE;
    rewrite restr_irrefl_eq; eauto with hahn;
    rewrite !seqA;
    apply (ecf_irf S CONS).
  2:
    apply inclusion_transpE;
    rewrite !transp_seq, !transp_eqv_rel;
    rewrite !transp_cr, transp_inv, !seqA;
    rewrite transp_sym_equiv with (r := cf); [| apply ES.cf_sym];
    rewrite transp_sym_equiv with (r := ∅₂); [| basic_solver].
  all:
    erewrite <- jf_necf; eauto;
    apply inclusion_inter_r; [basic_solver|];
    rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r; eauto with hahn.
Qed.


Lemma hb_jf_prcl_cc_prcl {A}
           (JF_PRCL : dom_rel(jf ⨾ ⦗A⦘) ⊆₁ A)
           (HB_PRCL : dom_rel(hb ⨾ ⦗A⦘) ⊆₁ A):
  dom_rel (cc S ⨾ ⦗A⦘) ⊆₁ A.
Proof.
  assert (EE_DOM : dom_rel(jfe ⨾ (sb ∪ jf)＊ ⨾ ⦗A⦘) ⊆₁ A).
  { arewrite ((sb ∪ jf)＊ ⨾ ⦗A⦘ ⊆ ⦗A⦘ ⨾ (sb ∪ jf)＊).
    { apply dom_r2l_rt.
      assert (DOM': dom_rel((sb ∪ jf) ⨾ ⦗A⦘) ⊆₁ A).
      { rewrite sb_in_hb. relsf. }
      rewrite (dom_rel_helper DOM'). basic_solver. }
    arewrite (jfe ⊆ jf).
    rewrite <-seqA, dom_seq. auto. }
  rewrite cc_alt; eauto.
  rewrite <- seq_eqv_inter_rr, seqA.
  rewrite (dom_rel_helper EE_DOM).
  basic_solver.
Qed.

Lemma ncf_hb_jf_prcl_vis {A}
      (AE : A ⊆₁ E)
      (NCF : ES.cf_free S A)
      (JF_PRCL : dom_rel(jf ⨾ ⦗A⦘) ⊆₁ A)
      (HB_PRCL : dom_rel(hb ⨾ ⦗A⦘) ⊆₁ A):
  (A ⊆₁ vis S).
Proof.
  unfold vis; splits; constructor;
  rename x into v, H into vA; auto.
  arewrite (cc S ⨾ ⦗eq v⦘ ⊆ ∅₂); [|done].
  arewrite (eq v ⊆₁ A); [basic_solver|].
  rewrite (dom_rel_helper (hb_jf_prcl_cc_prcl JF_PRCL HB_PRCL)).
  unfold cc. rewrite inclusion_inter_l1.
  auto.
Qed.

Lemma rmw_pref r w
      (RMW : rmw r w):
  hb_pref w ⊆₁ hb_pref r ∪₁ eq w.
Proof.
  assert (NINIT_r : Eninit r).
  { apply (ES.rmwEninit WF) in RMW.
    unfolder in RMW. basic_solver. }
  assert (wW : W w).
  { apply (ES.rmwD WF) in RMW.
    unfolder in RMW. basic_solver. }
  unfold hb_pref.
  rewrite crE, seq_union_l, seq_id_l, dom_union at 1.
  rewrite set_unionC.
  apply set_subset_union; [|basic_solver].
  arewrite (⦗eq w⦘ ⊆ ⦗W⦘ ⨾ ⦗eq w⦘); [ basic_solver|].
  rewrite <- seqA, hb_w_in_hb_imm_sb, seqA; eauto.
  assert (ISB_W'_DOM : dom_rel (immediate sb ⨾ ⦗eq w⦘) ⊆₁ Eninit).
  { unfolder. ins.
    desf.
    apply ES.sb_Einit_Eninit in H; auto.
    unfold "∪" in H.
    desf. 2: { unfolder in H. basic_solver. }
    exfalso. apply (H1 r).
    { apply ES.sb_Einit_Eninit; auto. unfolder.
      left. unfolder in H.
      basic_solver. }
  apply ES.rmw_in_sb; auto. }
  rewrite (dom_rel_helper ISB_W'_DOM).
  apply ES.rmwi in RMW; auto.
  rewrite <- seqA with (r3 := ⦗eq w⦘).
  rewrite seq_eqv_imm.
  rewrite dwt_imm_seq_eq with (a1 := r).
  { basic_solver. }
  { rewrite ES.sb_same_tid_alt; auto.
    eapply ES.sb_prcl; eauto. }
  apply seq_eqv_imm.
  unfold seq. basic_solver.
Qed.

Lemma hb_pref2_rmw_ncf e w w'
           (JF : jf w e)
           (RMW : rmw e w'):
  ES.cf_free S (hb_pref2 w' w).
Proof.
  rewrite hb_pref2_alt.
  rewrite rmw_pref; eauto.
  rewrite set_unionC, <- set_unionA.
  rewrite set_unionC with (s := hb_pref w).
  rewrite <- hb_pref2_alt.
  unfold ES.cf_free.
  rewrite !id_union, !seq_union_l, !seq_union_r.
  apply inclusion_union_l; apply inclusion_union_l.
  4: { specialize ES.cf_irr. basic_solver. }
  2: apply transp_empty; rewrite <- seq_transp_sym; [|apply ES.cf_sym].
  2,3: arewrite (eq w' ⊆₁ codom_rel (⦗eq e⦘ ⨾ rmw)); [basic_solver|];
    apply seq_codom_empty;
    rewrite seqA;
    rewrite <- seqA with (r1 := rmw);
    rewrite seq_rmw_cf_in_cf; eauto;
    arewrite (eq e ⊆₁ hb_pref2 e w); [unfold hb_pref2; basic_solver 7|].
  all: by apply hb_pref2_ncf.
Qed.

End HB_prefix.

(******************************************************************************)
(** ** DRF lemmas *)
(******************************************************************************)

Section DRF.

Variable  P : IdentMap.t {linstr : list Instr.t & LblStep.stable_lprog linstr}.
Variable (nInitProg : ~ IdentMap.In tid_init P).

Notation "'E' S" := S.(ES.acts_set) (at level 10).
Notation "'Einit' S"  := S.(ES.acts_init_set) (at level 10).
Notation "'Eninit' S" := S.(ES.acts_ninit_set) (at level 10).

Notation "'tid' S" := S.(ES.tid) (at level 10).
Notation "'lab' S" := S.(ES.lab) (at level 10).
Notation "'mod' S" := (Events.mod S.(ES.lab)) (at level 10).
Notation "'loc' S" := (Events.loc S.(ES.lab)) (at level 10).
Notation "'val' S" := (Events.val S.(ES.lab)) (at level 10).

Notation "'sb' S" := S.(ES.sb) (at level 10).
Notation "'rmw' S" := S.(ES.rmw) (at level 10).
Notation "'ew' S" := S.(ES.ew) (at level 10).
Notation "'jf' S" := S.(ES.jf) (at level 10).
Notation "'rf' S" := S.(ES.rf) (at level 10).
Notation "'co' S" := S.(ES.co) (at level 10).
Notation "'cf' S" := S.(ES.cf) (at level 10).
Notation "'hb' S" := S.(hb) (at level 10).

Notation "'jfe' S" := S.(ES.jfe) (at level 10).
Notation "'rfe' S" := S.(ES.rfe) (at level 10).
Notation "'coe' S" := S.(ES.coe) (at level 10).
Notation "'jfi' S" := S.(ES.jfi) (at level 10).
Notation "'rfi' S" := S.(ES.rfi) (at level 10).
Notation "'coi' S" := S.(ES.coi) (at level 10).

Notation "'R' S" := (fun a => is_true (is_r S.(ES.lab) a)) (at level 10).
Notation "'W' S" := (fun a => is_true (is_w S.(ES.lab) a)) (at level 10).
Notation "'F' S" := (fun a => is_true (is_f S.(ES.lab) a)) (at level 10).

Notation "'Rel' S" := (fun a => is_true (is_rel S.(ES.lab) a)) (at level 10).
Notation "'Acq' S" := (fun a => is_true (is_acq S.(ES.lab) a)) (at level 10).

Lemma jf_in_hb
      (RACE_FREE : RC11_RLX_race_free_program P)
      (S : ES.t)
      (STEPS : (step Weakestmo)＊ (prog_es_init P) S):
  jf S ⊆ hb S.
Proof.
  eapply clos_refl_trans_ind_left with (P := fun s => jf s ⊆ hb s); eauto.
  { basic_solver. }
  clear dependent S.
  intros S S' STEPS IH STEP.
  assert (STEPS_S' : (step Weakestmo)＊ (prog_es_init P) S').
  { eapply transitive_rt; eauto. apply rt_step. auto. }
  assert (WF_S : ES.Wf S).
  2: assert (WF_S' : ES.Wf S').
  1, 2: eby eapply steps_es_wf.
  generalize (hb_trans S'). intro HB_TRANS.
  inversion_clear STEP as [e [e' HH]]. desf.
  assert (HB_MON: hb S ⊆ hb S').
  { eapply step_hb_mon; eauto. }
  rename TT into STEP_.
  inversion STEP_ as [ST | [ST | [ST | ST]]].
  1, 3: inversion_clear ST; desf; rewrite JF'; basic_solver.
  { inversion ST as [w HH]. desf.
    unfold AddJF.add_jf in AJF. desf.
    unfold AddJF.jf_delta in JF'.
    rename rE' into eE', rR' into eR'.
    assert (wW' : is_w (lab S') w).
    { eapply load_step_W; eauto. intuition. }
    assert (WE_JF' : jf S' w e).
    { apply JF'. apply inclusion_union_r2. basic_solver. }
    assert (ACTS_MON : E S ⊆₁ E S').
    { eapply BasicStep.basic_step_nupd_acts_mon; eauto. }

    assert (HB : ((hb S')⁼ w e) \/ (not ((hb S')⁼ w e))) by apply classic.
    destruct HB as [[WE_EQ | [ WE_HB | EW_HB]] | WE_NHB].
    { type_solver. }
    { rewrite JF'. basic_solver. }
    { unfold transp in EW_HB.
      exfalso. eapply coh; eauto.
      eexists. split; eauto.
      apply r_step. apply rf_in_eco.
      apply ES.jf_in_rf; eauto. }
    exfalso.
      assert (HB_DOM : dom_rel (hb S') ⊆₁ E S).
    { eapply step_nupd_hb_dom; eauto. }
    assert (PREF_HB_BWCL : dom_rel(hb S' ⨾ ⦗hb_pref2 S' e w⦘) ⊆₁ hb_pref2 S' e w).
    { rewrite hb_pref2_alt.
      rewrite id_union, seq_union_r, dom_union.
      rewrite !hb_pref_hb_bwcl. auto. }
    assert (PREF_JF_BWCL : dom_rel(jf S' ⨾ ⦗hb_pref2 S' e w⦘) ⊆₁ hb_pref2 S' e w).
    { unfold hb_pref2.
      rewrite dom_rel_eqv_dom_rel.
      rewrite JF', IH.
      type_solver 9. }
    assert (PREF_EXEC : program_execution P S' (hb_pref2 S' e w)).
    { red. splits; auto. constructor.
      { apply hb_pref2_inE; eauto. }
      { rewrite hb_pref2_alt.
        specialize (BasicStep.basic_step_acts_ninit_set BSTEP WF_S).
        specialize (init_in_hb_pref WF_S').
        basic_solver 10. }
      { rewrite sb_in_hb. apply PREF_HB_BWCL. }
      { rewrite sw_in_hb. apply PREF_HB_BWCL. }
      { rewrite hb_pref2_alt.
        apply fwcl_hom; apply hb_pref_rmw_fwcl; auto.
        { rewrite BasicStep.basic_step_nupd_rmw; eauto.
          rewrite ES.rmwE; eauto.
          specialize (BasicStep.basic_step_acts_set_ne BSTEP).
          basic_solver. }
        rewrite ES.rmwD; eauto.
        type_solver. }
      { apply jf_prcl_rf_compl; auto.
        apply hb_pref2_inE; auto. }
      { apply hb_pref2_ncf; auto. }
      assert (AE' : hb_pref2 S' e w ⊆₁ E S').
      { apply hb_pref2_inE; eauto. }
      apply ncf_hb_jf_prcl_vis; auto.
      apply hb_pref2_ncf; auto. }
    assert (PREF_RC11 : rc11_consistent_x S' (hb_pref2 S' e w)).
    { red. exists (x2g S' (hb_pref2 S' e w)). splits.
      { apply x2g_X2G; auto. by cdes PREF_EXEC. }
      apply x2g_rc11_consistent; auto.
      { by cdes PREF_EXEC. }
      rewrite restr_relE.
      rewrite seq_union_l, seq_union_r.
      rewrite <- restr_relE with (r := rf S').
      fold (Execution.ex_rf S' (hb_pref2 S' e w)).
      rewrite (Execution.ex_rf_restr_jf); auto.
      2: { by cdes PREF_EXEC. }
      rewrite <- restr_relE.
      rewrite JF', <- union_restr.
      rewrite !inclusion_restr, <- unionA.
      rewrite acyclic_absorb.
      2: { left. rewrite WF_S.(ES.jfE).
           rewrite dom_rel_helper with (r := sb S').
           2: { eapply step_nupd_sb_dom; eauto. }
           specialize (BasicStep.basic_step_acts_set_ne BSTEP) as NE.
           rewrite seq_union_r.
           rewrite codom_rel_helper with (rr := singl_rel w e).
           2: { apply codom_singl_rel. }
           rewrite !seqA.
           arewrite_false !(⦗eq e⦘ ⨾ ⦗E S⦘); [basic_solver|].
           basic_solver. }
      split.
      { rewrite sb_in_hb, IH, HB_MON, unionK. eby eapply hb_acyclic. }
      unfold acyclic. rewrite ct_singl_rel.
      assert (NEQ : w <> e).
      { intro. apply WE_NHB. basic_solver. }
      basic_solver. }
    specialize (RACE_FREE S' (hb_pref2 S' e w) PREF_EXEC PREF_RC11).
    assert (RACE_W : race S' (hb_pref2 S' e w) w).
    { unfold race. unfold dom_rel. exists e.
      unfolder. splits.
      1,2,4: unfold hb_pref2; basic_solver 10.
      { apply and_not_or. split; auto. }
      unfold one. auto. }
    assert (RACE_E : race S' (hb_pref2 S' e w) e).
    { unfold race. unfold dom_rel. exists w.
      unfolder. splits.
      1,2,4: unfold hb_pref2; basic_solver 10.
      { apply and_not_or. split.
        { unfolder in WE_NHB. intuition. }
        intro HH. by apply ES.cf_sym in HH. }
      unfold one. auto. }
    specialize (RACE_FREE w RACE_W) as QW.
    specialize (RACE_FREE e RACE_E) as QE.
    destruct QE as [|wREL]; destruct QW as [eACQ|].
    1, 2, 4: type_solver.
    unfold RLX_race_free in RACE_FREE.
    unfolder in WE_NHB.
    apply WE_NHB. right. left.
    apply ra_jf_in_hb; auto.
    apply proj1 in eACQ. apply proj1 in wREL.
    basic_solver. }

  inversion ST as [w HH]. desf.
  unfold AddJF.add_jf in AJF. desf.
  unfold AddJF.jf_delta in JF'.
  rename rE' into eE', rR' into eR'.
  assert (w'W : is_w (lab S') w).
  { eapply update_step_W; eauto. basic_solver. }
  assert (w'W' : is_w (lab S') w').
  { eapply update_step_W; eauto. basic_solver. }
  assert (w'E' : (E S') w').
  { eapply update_step_E; eauto. basic_solver. }
  assert (WE_JF' : jf S' w e).
  { apply JF'. apply inclusion_union_r2. basic_solver. }
  assert (ACTS_MON : E S ⊆₁ E S').
  { eapply BasicStep.basic_step_nupd_acts_mon; eauto. }
  assert (HB : ((hb S')⁼ w e) \/ (not ((hb S')⁼ w e))) by apply classic.
  destruct HB as [[WE_EQ | [ WE_HB | EW_HB]] | WE_NHB].
  { type_solver. }
  { rewrite JF'. basic_solver. }
  { unfold transp in EW_HB.
      exfalso. eapply coh; eauto.
      eexists. split; eauto.
      apply r_step. apply rf_in_eco.
      apply ES.jf_in_rf; eauto. }
  exfalso.
  assert (PREF_HB_BWCL : dom_rel(hb S' ⨾ ⦗hb_pref2 S' w' w⦘) ⊆₁ hb_pref2 S' w' w).
  { unfold hb_pref2.
    rewrite dom_rel_eqv_dom_rel.
    rewrite <- seqA, (rewrite_trans_seq_cr_r (hb_trans S')).
    basic_solver 10. }
  specialize (step_hb_dom BSTEP STEP_ WF_S) as HB_DOM.
  assert (PREF_JF_BWCL : dom_rel(jf S' ⨾ ⦗hb_pref2 S' w' w⦘) ⊆₁ hb_pref2 S' w' w).
  { unfold hb_pref2.
    rewrite dom_rel_eqv_dom_rel.
    rewrite JF', IH.
    type_solver 9. }

  assert (EW'_RMW : rmw S' e w').
  { cdes BSTEP. cdes BSTEP_.
    unfold BasicStep.rmw_delta in RMW'.
    apply RMW'. basic_solver. }
  assert (EW'_HB : hb S' e w').
  { apply ES.rmw_in_sb, sb_in_hb in EW'_RMW; auto. }

  assert (PREF_EXEC : program_execution P S' (hb_pref2 S' w' w)).
  { red. splits; auto. constructor.
    { apply hb_pref2_inE; eauto. }
    { rewrite hb_pref2_alt.
      specialize (BasicStep.basic_step_acts_ninit_set BSTEP WF_S).
      specialize (init_in_hb_pref WF_S').
      basic_solver 10. }
    { rewrite sb_in_hb. apply PREF_HB_BWCL. }
    { rewrite sw_in_hb. apply PREF_HB_BWCL. }
    { rewrite hb_pref2_alt.
      apply fwcl_hom; apply hb_pref_rmw_fwcl; auto.
      all: rewrite ES.rmwD; auto; type_solver. }
    { apply jf_prcl_rf_compl; auto.
      apply hb_pref2_inE; auto. }
    { eapply hb_pref2_rmw_ncf; eauto. }
    apply ncf_hb_jf_prcl_vis; auto.
    apply hb_pref2_inE; auto.
    eapply hb_pref2_rmw_ncf; eauto. }

  assert (PREF_RC11 : rc11_consistent_x S' (hb_pref2 S' w' w)).
  { red. exists (x2g S' (hb_pref2 S' w' w)). splits.
    { apply x2g_X2G; auto. by cdes PREF_EXEC. }
    apply x2g_rc11_consistent; auto.
    { by cdes PREF_EXEC. }
    rewrite restr_relE.
    rewrite seq_union_l, seq_union_r.
    rewrite <- restr_relE with (r := rf S').
    fold (Execution.ex_rf S' (hb_pref2 S' w' w)).
    rewrite (Execution.ex_rf_restr_jf); auto.
    2: { by cdes PREF_EXEC. }
    rewrite <- restr_relE.
    rewrite JF', <- union_restr.
    rewrite !inclusion_restr, <- unionA.
    cdes BSTEP.
    arewrite (sb S' ⊆ sb S ∪ (E S ∪₁ eq e) × eq w' ∪ E S × eq e).
    { cdes BSTEP_.
      unfold BasicStep.sb_delta in SB'.
      rewrite eq_opt_someE in SB'.
      rewrite SB' at 1.
      rewrite ES.cont_sb_domE at 1 2 3; eauto.
      basic_solver 20. }
    arewrite (sb S ∪ (E S ∪₁ eq e) × eq w' ∪ E S × eq e ∪ jf S ∪ singl_rel w e
                 ⊆
              sb S ∪ jf S ∪ (E S ∪₁ eq e) × eq w' ∪ E S × eq e).
    { basic_solver 20. }
    assert (nEe : ~ E S e).
    { eby eapply BasicStep.basic_step_acts_set_ne. }
    assert (SB_JF_DOM : (sb S ∪ jf S) ⊆ ⦗E S⦘ ⨾ ⊤₂).
    { rewrite (dom_l WF_S.(ES.sbE)), (dom_l WF_S.(ES.jfE)).
      basic_solver. }
    apply acyclic_absorb; [left|].
    { rewrite seq_union_r.
      apply inclusion_union_l.
      { rewrite SB_JF_DOM at 1.
        seq_rewrite <- cross_inter_r.
        basic_solver. }
      basic_solver. }
    assert (nEw' : ~ E S w').
    { eby eapply BasicStep.basic_step_acts_set_ne'. }
    split.
    2: { apply acyclic_disj. basic_solver. }
    apply acyclic_absorb; [left|].
    { rewrite SB_JF_DOM at 1.
      basic_solver. }
    split.
    { rewrite sb_in_hb, IH, HB_MON, unionK. eby eapply hb_acyclic. }
    apply acyclic_disj.
    assert (NEQ : e <> w').
    { intro HH. eapply ES.sb_irr, ES.rmw_in_sb; eauto.
      eby rewrite HH in EW'_RMW. }
    basic_solver. }
    specialize (RACE_FREE S' (hb_pref2 S' w' w) PREF_EXEC PREF_RC11).
    assert (RACE_W : race S' (hb_pref2 S' w' w) w).
    { unfold race. unfold dom_rel. exists e.
      unfolder. splits.
      1,2,4: unfold hb_pref2; basic_solver 10.
      { apply and_not_or. split; auto. }
      unfold one. auto. }
    assert (RACE_E : race S' (hb_pref2 S' w' w) e).
    { unfold race. unfold dom_rel. exists w.
      unfolder. splits.
      1,2,4: unfold hb_pref2; basic_solver 10.
      { apply and_not_or. split.
        { unfolder in WE_NHB. intuition. }
        intro HH. by apply ES.cf_sym in HH. }
      unfold one. auto. }
    specialize (RACE_FREE w RACE_W) as QW.
    specialize (RACE_FREE e RACE_E) as QE.
    destruct QE as [|wREL]; destruct QW as [eACQ|].
    1, 2, 4: type_solver.
    unfold RLX_race_free in RACE_FREE.
    unfolder in WE_NHB.
    apply WE_NHB. right. left.
    apply ra_jf_in_hb; auto.
    apply proj1 in eACQ. apply proj1 in wREL.
    basic_solver.
Qed.

Lemma rf_in_jf (S : ES.t) (X : eventid -> Prop)
      (WF : ES.Wf S)
      (EXEC : Execution.t S X)
      (JF_IN_HB : jf S ⊆ hb S):
  restr_rel X (rf S) ⊆ jf S.
Proof.
  rewrite restr_relE.
  unfolder; intros x y HH.
  destruct HH as [xX [xyRF yX]].
  unfold ES.rf in xyRF; unfolder in xyRF.
  destruct xyRF as [[z [xzEW zyJF]] NCF].
  specialize (JF_IN_HB z y zyJF) as zyHB.
  assert (zX: X z).
  { apply (Execution.hb_prcl S X EXEC).
    unfolder. eauto. }
  eapply ES.ewc in xzEW as HH; auto.
  destruct HH; [basic_solver|].
  specialize (Execution.ex_ncf S X EXEC) as CF_FREE.
  destruct CF_FREE with (x := x) (y := z).
  basic_solver.
Qed.

Lemma po_rf_acyclic (S : ES.t) (X : eventid -> Prop)
      (WF : ES.Wf S)
      (CONS : es_consistent S (m := Weakestmo))
      (EXEC : Execution.t S X)
      (JF_IN_HB : jf S ⊆ hb S):
  acyclic (restr_rel X (sb S ∪ rf S)).
Proof.
  rewrite sb_in_hb.
  rewrite <- union_restr, (rf_in_jf WF EXEC JF_IN_HB).
  rewrite JF_IN_HB, inclusion_restr, unionK.
  eby eapply hb_acyclic.
Qed.

Theorem drf_rlx S X
      (EXEC : program_execution P S X)
      (RACE_FREE : RC11_RLX_race_free_program P) :
  rc11_consistent_x S X.
Proof.
  cdes EXEC.
  assert (WF : ES.Wf S).
  { eby eapply steps_es_wf. }
  assert (CONS : @es_consistent S Weakestmo).
  { eby eapply steps_es_consistent. }
  red. exists (x2g S X). splits.
  { by apply x2g_X2G. }
  apply x2g_rc11_consistent; auto.
  { rewrite jf_in_hb; auto.
    by apply Execution.hb_prcl. }
  apply po_rf_acyclic; auto.
  by apply jf_in_hb.
Qed.
End DRF.



