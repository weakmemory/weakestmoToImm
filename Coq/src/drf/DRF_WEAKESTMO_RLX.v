From hahn Require Import Hahn.
From imm Require Import Events Prog ProgToExecutionProperties RC11.
From PromisingLib Require Import Basic.
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

Module DRF_WEAKESTMO_RLX.

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

Lemma ra_jf_in_hb S (WF : ES.Wf S) :
  ⦗Rel S⦘ ⨾ S.(ES.jf) ⨾ ⦗Acq S⦘ ⊆ S.(hb).
Proof.
  rewrite <- sw_in_hb.
  unfold sw.
  rewrite <- inclusion_id_cr. rewrite seq_id_l.
  rewrite (dom_l WF.(ES.jfE)) at 1.
  rewrite (dom_l WF.(ES.jfD)) at 1.
  rewrite !seqA.
  arewrite (⦗Rel S⦘ ⨾ ⦗E S⦘ ⨾ ⦗W S⦘ ⊆ release S); [|done].
  unfold release, rs.
  basic_solver 20.
Qed.

Lemma ct_imm_split_l {A} (r : relation A)
      (IRR: irreflexive r)
      (TANS: transitive r)
      (acts : list A)
      (DOM_IN_ACTS: dom_rel r ⊆₁ (fun x : A => In x acts)):
  r ≡ immediate r ⨾ r^?.
Proof.
  split; [|basic_solver].
  rewrite ct_imm1 at 1; eauto.
  rewrite ct_begin. apply seq_mori; [done|].
  rewrite immediate_in. apply rt_of_trans; eauto.
Qed.

Lemma ct_imm_split_r {A} (r : relation A)
      (IRR: irreflexive r)
      (TANS: transitive r)
      (acts : list A)
      (DOM_IN_ACTS: dom_rel r ⊆₁ (fun x : A => In x acts)):
  r ≡ r^? ⨾ immediate r.
Proof.
  split; [|basic_solver].
  rewrite ct_imm1 at 1; eauto.
  rewrite ct_end. apply seq_mori; [|done].
  rewrite immediate_in. apply rt_of_trans; eauto.
Qed.

Lemma hb_imm_split_l S
      (WF: ES.Wf S)
      (CONS : es_consistent S (m := Weakestmo)):
  S.(hb) ≡ immediate S.(hb) ⨾ S.(hb)^?.
Proof.
  eapply ct_imm_split_l.
  { eapply hb_irr. eauto. }
  { eapply hb_trans. } 
  rewrite (dom_l (hbE S WF)).
  rewrite dom_seq, dom_eqv, ES.E_alt.
  eauto.
Qed.

Lemma hb_imm_split_r S
      (WF: ES.Wf S)
      (CONS : es_consistent S (m := Weakestmo)):
  S.(hb) ≡ S.(hb)^? ⨾ immediate S.(hb).
Proof.
  eapply ct_imm_split_r.
  { eapply hb_irr. eauto. }
  { eapply hb_trans. } 
  rewrite (dom_l (hbE S WF)).
  rewrite dom_seq, dom_eqv, ES.E_alt.
  eauto.
Qed.

Lemma r_hb_in_imm_sb_hb S
      (WF : ES.Wf S)
      (CONS : es_consistent S (m := Weakestmo)):
  ⦗R S⦘ ⨾ S.(hb) ⊆ immediate S.(ES.sb) ⨾ S.(hb)^?.
Proof.
  rewrite hb_imm_split_l at 1; auto.
  rewrite <- seqA. apply seq_mori; [|done]. 
  unfold hb. rewrite imm_clos_trans.
  rewrite imm_union, seq_union_r.
  apply inclusion_union_l; [basic_solver|].
  rewrite immediate_in, (dom_l (swD S WF)). type_solver. 
Qed.

Lemma hb_w_in_hb_imm_sb S
      (WF : ES.Wf S)
      (CONS : es_consistent S (m := Weakestmo)):
  S.(hb) ⨾ ⦗W S⦘ ⊆ S.(hb)^? ⨾ immediate S.(ES.sb).
Proof.
  rewrite hb_imm_split_r at 1; auto.
  rewrite seqA. apply seq_mori; [done|]. 
  unfold hb. rewrite imm_clos_trans.
  rewrite imm_union, seq_union_l.
  apply inclusion_union_l; [basic_solver|].
  rewrite immediate_in, (dom_r (swD S WF)). type_solver. 
Qed.

(* This lemma was removed from the project during the working on the DRF theorem. 
   However, the proof relies on it.*)
Lemma icf_R {S}
      (WF : ES.Wf S)
      (CONS : es_consistent S (m := Weakestmo)) :
  ES.icf S ≡ ⦗R S⦘ ⨾ ES.icf S ⨾ ⦗R S⦘.
Admitted.

Lemma t_rmw_hb_in_hb S
      (WF : ES.Wf S)
      (CONS : es_consistent S (m := Weakestmo)) :
  S.(ES.rmw)⁻¹ ⨾ S.(hb) ⊆ S.(hb)^?.
Proof.
  rewrite WF.(ES.rmwD).
  rewrite R_ex_in_R.
  rewrite (dom_l WF.(ES.rmwEninit)).
  repeat rewrite transp_seq.
  rewrite ES.rmwi; eauto.
  rewrite !seqA, !transp_eqv_rel.
  rewrite r_hb_in_imm_sb_hb; eauto.
  rewrite <- seq_eqvK with (dom := Eninit S), seqA.
  rewrite <- seqA with (r1 := (immediate (sb S))⁻¹).
  rewrite <- transp_eqv_rel with (d := Eninit S) at 1.
  rewrite <- transp_seq.
  rewrite <- seqA with (r3 := (hb S)^?).
  arewrite !(⦗Eninit S⦘ ⨾ immediate (sb S) ⊆ immediate (sb S) ∩  ES.same_tid S).
  { erewrite <- inter_absorb_l with (r := ⦗Eninit S⦘ ⨾ immediate (sb S))
                                   (r' := immediate (sb S)); [|basic_solver].
    erewrite seq_mori; [|apply inclusion_refl2|apply immediate_in].
    rewrite ES.sb_tid; eauto with hahn. }
  rewrite transp_inter.
  erewrite transp_sym_equiv with (r := (ES.same_tid S)); [| apply ES.same_tid_sym].
  rewrite <- seqA with (r3 := (hb S)^?).
  rewrite HahnEquational.inter_trans; [| apply ES.same_tid_trans].
  rewrite ES.imm_tsb_imm_sb_in_icf; auto.
  arewrite (⦗W S⦘ ⨾ (ES.icf S)^? ≡ ⦗W S⦘).
  { rewrite (icf_R WF CONS). type_solver. }
  basic_solver.
Qed.

Lemma jfe_in_jf (S : ES.t)
      (WF : ES.Wf S):
  S.(ES.jfe) ⊆ S.(ES.jf).
Proof.
  eauto with hahn.
Qed.

Lemma union_seq_compl_sym_trans_rr {A} (e r1 r2 : relation A)
      (SYM : symmetric e)
      (TRANS : transitive e)
      (R2_IN_CE : r2 ⊆ e):
  ((compl_rel e) ∩ (r1 ⨾ r2) ≡ (compl_rel e) ∩ r1 ⨾ r2).
Proof.
  basic_solver 10.
Qed.

Lemma compl_seq_r {A} ( r : relation A)
      (SYM : symmetric r)
      (TRANS : transitive r):
  (r ⨾ compl_rel r ⊆ compl_rel r).
Proof.
  basic_solver 5.
Qed.

 
Lemma compl_rel_invol {A} (r : relation A)
  (DECID : forall x y : A, Decidable.decidable (r x y)):
  (compl_rel (compl_rel r) ≡ r).
Proof.
  generalize NNPP. ins.
  unfolder. split. 
  { ins. apply H. auto. }
  ins. apply Decidable.not_not; intuition.
Qed.

Lemma union_seq_compl_equiv_rr2 {A} (e r1 r2 : relation A)
      (DECID : forall x y : A, Decidable.decidable (e x y))
      (SYM : symmetric (compl_rel e))
      (TRANS : transitive (compl_rel e))
      (R2_IN_CE : r2 ⊆ compl_rel e):
  (e ∩ (r1 ⨾ r2) ≡ e ∩ r1 ⨾ r2).
Proof.
  set (e' := compl_rel e) in *.
  arewrite (e ≡ compl_rel e').
  { apply same_rel_Symmetric. eapply compl_rel_invol; eauto. }
  apply union_seq_compl_sym_trans_rr; eauto.
Qed.
    
Lemma trans_prcl_immediate_seqr {A} (r : relation A) (x y : A)
      (TRANS : transitive r)
      (PRCL : downward_total r)
      (IMM : immediate r x y):
  immediate r ⨾ ⦗eq y⦘ ≡ singl_rel x y. 
Proof. 
  red; split. 
  { unfolder. 
    intros z y' [Rzy EQy].
    split; auto. desf.
    assert (r^= z x) as Rzx.
    { apply PRCL with (z := y'); auto.
      apply immediate_in. auto. }
    unfolder in Rzx.
    desf.
    { apply immediate_in in IMM. exfalso. eapply Rzy0; eauto. }
    exfalso. unfolder in IMM. basic_solver. }
  unfolder in *.
  basic_solver.
Qed. 

Lemma cc_alt (S : ES.t) (m : model) (CONS : es_consistent S (m := m)) (WF : ES.Wf S):
  cc S ≡ S.(ES.cf) ∩ (S.(ES.jfe) ⨾ (S.(ES.sb) ∪ S.(ES.jf))＊).
Proof.
  unfold cc.
  split.
  { apply inclusion_inter_mon; auto with hahn.
    rewrite jfe_in_jf at 2; auto.
    apply inclusion_seq_mon; auto with hahn.
    rewrite crE, !seq_union_r, seq_id_r.
    apply inclusion_union_l.
    { rewrite <- rt_unit at 2. basic_solver 10. }
    rewrite <- rt_unit at 2. 
    rewrite <- rt_unit at 2. 
    basic_solver 10. }
  rewrite <- interK with (r := cf S) at 1.
  rewrite interA.
  apply inclusion_inter_mon; auto with hahn.
  rewrite rtE at 1.
  rewrite seq_union_r, seq_id_r, inter_union_r.
  apply inclusion_union_l.
  { rewrite ES.cf_same_tid. rewrite jfe_alt at 1; eauto.
    basic_solver. }
  rewrite ES.jfi_union_jfe at 1.
  rewrite <- !unionA.
  arewrite (jfi S ⊆ sb S).
  rewrite unionK.
  rewrite path_ut_last.
  rewrite seq_union_r, inter_union_r.
  apply inclusion_union_l.
  { arewrite (cf S ∩ (jfe S ⨾ (sb S)⁺) ⊆ ∅₂); [|done].
    rewrite (ct_of_trans (ES.sb_trans WF)).
    arewrite (jfe S ⊆ compl_rel(ES.same_tid S) ⨾ ⦗Eninit S⦘).
    { rewrite jfe_alt; eauto.
      rewrite ES.jf_nEinit_alt; eauto.
      basic_solver. }
    rewrite ES.sb_tid; eauto.
    rewrite ES.cf_same_tid.
    arewrite (compl_rel (ES.same_tid S) ⨾ ES.same_tid S ⊆
                        compl_rel (ES.same_tid S)); [|basic_solver].
    unfolder. intros p q HH. destruct HH as [z [NPZ SQ]]. 
    intro PQ.
    apply ES.same_tid_sym in SQ.
    generalize ES.same_tid_trans. basic_solver. }
  rewrite inclusion_inter_l2.
  repeat apply inclusion_seq_mon; eauto with hahn.
  apply (rt_of_trans (ES.sb_trans WF)).
Qed.

Lemma cc_in_hb (S : ES.t)
      (WF : ES.Wf S)
      (JF_IN_HB : jf S ⊆ hb S):
    cc S ⊆ hb S.
Proof.
  unfold cc. rewrite inclusion_inter_l2.
  rewrite jfe_in_jf; auto.
  rewrite sb_in_hb, JF_IN_HB.
  specialize (hb_trans S) as HB_TRANS.
  relsf. 
Qed.
  
(******************************************************************************)
(** ** Prefix executional properties *)
(******************************************************************************)

Definition hb_pref S v := dom_rel (S.(hb)^? ⨾ ⦗eq v⦘).
                                        
Definition hb_pref2 S v1 v2 := dom_rel (S.(hb)^? ⨾ (⦗eq v1⦘ ∪ ⦗eq v2⦘)).

Lemma hb_pref2_alt S v1 v2:
  hb_pref2 S v1 v2 ≡₁ hb_pref S v1 ∪₁ hb_pref S v2.
Proof.
  unfold hb_pref, hb_pref2.
  basic_solver 10.
Qed. 
  
Lemma hb_pref_inE (S : ES.t) 
      (WF : ES.Wf S)
      (v : eventid)
      (vE : (E S) v) :
  hb_pref S v ⊆₁ E S.
Proof.
  unfold hb_pref.
  rewrite hbE; auto.
  basic_solver.
Qed.

Lemma hb_pref2_inE (S : ES.t)
      (WF : ES.Wf S)
      (v1 v2 : eventid)
      (v1E : (E S) v1)
      (v2E : (E S) v2) :
  hb_pref2 S v1 v2 ⊆₁ E S.
Proof.
  rewrite hb_pref2_alt.
  rewrite !hb_pref_inE; auto.
  basic_solver.
Qed.

Lemma init_in_hb_pref (S : ES.t)  
      (WF : ES.Wf S)
      (v : eventid)
      (vEninit : (Eninit S) v) :
  Einit S ⊆₁ hb_pref S v.
Proof.
  unfold hb_pref.
  rewrite <- sb_in_hb.
  rewrite <- ES.sb_init; auto.
  basic_solver 10.
Qed.

Lemma hb_pref_hb_bwcl (S : ES.t)
      (v : eventid) :
  dom_rel(hb S⨾ ⦗hb_pref S v⦘) ⊆₁ hb_pref S v.
Proof.
  unfold hb_pref.
  specialize (hb_trans S).
  basic_solver 10.
Qed.

Lemma hb_pref_rmw_fwcl (S : ES.t)
      (WF : ES.Wf S)
      (CONS : es_consistent S (m := Weakestmo))
      (v : eventid)
      (nvRMW : ⦗eq v⦘ ⨾ rmw S ⊆ ∅₂) :
  codom_rel (⦗hb_pref S v⦘ ⨾ rmw S) ⊆₁ hb_pref S v.
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
   rewrite <- seqA, (t_rmw_hb_in_hb WF CONS).
   done.
Qed.

Lemma fwcl_hom {A}
      (T1 T2 : A -> Prop)
      (r : relation A)
      (T1_FWCL : codom_rel (⦗T1⦘ ⨾ r) ⊆₁ T1)
      (T2_FWCL : codom_rel (⦗T2⦘ ⨾ r) ⊆₁ T2):
  codom_rel (⦗T1 ∪₁ T2⦘ ⨾ r) ⊆₁ T1 ∪₁ T2.
Proof.
  unfolder in *.
  basic_solver 10.
Qed.

Lemma jf_bwcl_rf_compl (S : ES.t)
      (WF : ES.Wf S)
      (A : eventid -> Prop)
      (AE : A ⊆₁ E S)
      (JF_BWCL : dom_rel(jf S ⨾ ⦗A⦘) ⊆₁ A):
  A ∩₁ R S ⊆₁ codom_rel (⦗A⦘ ⨾ rf S).
Proof.
  rewrite <- set_interK with (s := A) at 1.
  rewrite AE at 2; auto.
  rewrite set_interA, (ES.jf_complete WF).
  rewrite set_interC, <- codom_eqv1.
  rewrite (dom_rel_helper JF_BWCL).
  rewrite ES.jf_in_rf; auto.
  basic_solver.
Qed.
     
Lemma hb_pref2_ncf (S : ES.t)
           (WF : ES.Wf S)
           (CONS : es_consistent (m := Weakestmo) S)
           (e w : eventid)
           (JF : jf S w e):
  ES.cf_free S (hb_pref2 S e w).
Proof.
  unfold hb_pref2.
  red. rewrite eqv_dom_in_seq_tr, !seqA.
  arewrite (((hb S)^? ⨾ (⦗eq e⦘ ∪ ⦗eq w⦘))⁻¹ ⨾
             cf S ⨾
             (hb S)^? ⨾ (⦗eq e⦘ ∪ ⦗eq w⦘) ⊆ ∅₂); [|basic_solver].
  rewrite transp_seq, transp_union, transp_cr, !transp_eqv_rel, !seqA.
  rewrite !seq_union_r, !seq_union_l.
  apply inclusion_union_l; apply inclusion_union_l.
  1, 4:
    rewrite <- seqA with (r3 := (hb S)^? ⨾ ⦗eq _⦘);
    rewrite <- seqA with (r3 := ⦗eq _⦘);
    rewrite <- restr_relE;
    rewrite restr_irrefl_eq; eauto with hahn;
    rewrite !seqA;
    apply (ecf_irf S CONS).
  2:
    apply inclusion_transpE;
    rewrite !transp_seq, !transp_eqv_rel;
    rewrite !transp_cr, transp_inv, !seqA;
    rewrite transp_sym_equiv with (r := cf S); [| apply ES.cf_sym];
    rewrite transp_sym_equiv with (r := ∅₂); [| basic_solver].
  all:
    erewrite <- jf_necf; eauto;
    apply inclusion_inter_r; [basic_solver|];
    rewrite inclusion_seq_eqv_l, inclusion_seq_eqv_r; eauto with hahn. 
Qed.


Lemma hb_jf_bwcl_cc_bwcl (S : ES.t)
           (WF : ES.Wf S)
           (CONS : es_consistent (m := Weakestmo) S)
           (A : eventid -> Prop)
           (JF_BWCL : dom_rel(jf S ⨾ ⦗A⦘) ⊆₁ A)
           (HB_BWCL : dom_rel(hb S ⨾ ⦗A⦘) ⊆₁ A):
  dom_rel (cc S ⨾ ⦗A⦘) ⊆₁ A. 
Proof.
  assert (EE_DOM : dom_rel(jfe S ⨾ (sb S ∪ jf S)＊ ⨾ ⦗A⦘) ⊆₁ A). 
  { arewrite ((sb S ∪ jf S)＊ ⨾ ⦗A⦘ ⊆ ⦗A⦘ ⨾ (sb S ∪ jf S)＊).
    { apply dom_r2l_rt.
      assert (DOM': dom_rel((sb S ∪ jf S) ⨾ ⦗A⦘) ⊆₁ A).
      { rewrite sb_in_hb. relsf. }
      rewrite (dom_rel_helper DOM'). basic_solver. }
    rewrite jfe_in_jf; eauto.
    rewrite <-seqA, dom_seq. auto. }
  rewrite cc_alt; eauto.
  rewrite <- seq_eqv_inter_rr, seqA. 
  rewrite (dom_rel_helper EE_DOM).
  basic_solver. 
Qed.

Lemma ncf_hb_jf_bwcl_vis (S : ES.t)
      (WF : ES.Wf S)
      (CONS : es_consistent (m := Weakestmo) S)
      (A : eventid -> Prop)
      (AE : A ⊆₁ E S)
      (NCF : ES.cf_free S A)
      (JF_BWCL : dom_rel(jf S ⨾ ⦗A⦘) ⊆₁ A)
      (HB_BWCL : dom_rel(hb S ⨾ ⦗A⦘) ⊆₁ A):
  (A ⊆₁ vis S).
Proof.
  unfold vis; splits; constructor;
  rename x into v, H into vA; auto.   
  arewrite (cc S ⨾ ⦗eq v⦘ ⊆ ∅₂); [|done].
  arewrite (eq v ⊆₁ A); [basic_solver|]. 
  rewrite (dom_rel_helper (hb_jf_bwcl_cc_bwcl WF CONS JF_BWCL HB_BWCL)). 
  unfold cc. rewrite inclusion_inter_l1.  
  auto. 
Qed.

Lemma sb_tid_alt (S : ES.t)
      (WF : ES.Wf S):
  ⦗Eninit S⦘ ⨾ sb S ≡ sb S ∩ ES.same_tid S.
Proof.
  split.
  { specialize (ES.sb_tid WF). basic_solver. }
  rewrite ES.sb_Einit_Eninit at 1; auto.
  rewrite inter_union_l.
  apply inclusion_union_l.
  { arewrite (Einit S × Eninit S ∩ ES.same_tid S ⊆ ∅₂); [|done].
    unfold ES.acts_ninit_set, "\₁", ES.acts_init_set, ES.same_tid, "~".
    unfolder. ins. desf. apply H2.
    split; auto.
    rewrite H3 in H0.
    auto. }
  basic_solver.
Qed.

Lemma rmw_pref (S : ES.t)
  (WF : ES.Wf S)
  (CONS : es_consistent (m := Weakestmo) S)
  (r w : eventid)
  (RMW : ES.rmw S r w):
  hb_pref S w ⊆₁ hb_pref S r ∪₁ eq w.
  assert (NINIT_r : Eninit S r).
  { apply (ES.rmwEninit WF) in RMW.
    unfolder in RMW. basic_solver. }
  assert (wW : W S w).
  { apply (ES.rmwD WF) in RMW.
    unfolder in RMW. basic_solver. }
      
  unfold hb_pref.
  rewrite crE, seq_union_l, seq_id_l, dom_union at 1.
  rewrite set_unionC.
  apply set_subset_union; [|basic_solver].
  arewrite (⦗eq w⦘ ⊆ ⦗W S⦘ ⨾ ⦗eq w⦘); [ basic_solver|].
  rewrite <- seqA, hb_w_in_hb_imm_sb, seqA; auto.
    
  assert (ISB_W'_DOM : dom_rel (immediate (sb S) ⨾ ⦗eq w⦘) ⊆₁ Eninit S).
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
  rewrite trans_prcl_immediate_seqr with (x := r); eauto.
  { basic_solver. }
  { specialize (ES.sb_trans WF). basic_solver. }
  { rewrite sb_tid_alt; auto.
    eapply ES.sb_prcl; eauto. }
  apply seq_eqv_imm.
  unfold seq. basic_solver.
Qed.

Lemma seq_rmw_cf_in_cf (S : ES.t)
      (WF : ES.Wf S)
      (CONS : es_consistent (m := Weakestmo) S):
  rmw S ⨾ cf S ⊆ cf S.
Proof.
  unfold ES.cf.
  rewrite (dom_l (ES.rmwEninit WF)), !seqA.
  apply inclusion_seq_mon; [done|].
  rewrite <- !seqA.
  apply inclusion_seq_mon; [|done].
  rewrite seqA.
  rewrite inclusion_seq_eqv_l.
  rewrite minus_inter_compl at 2.
  apply inclusion_inter_r.
  { rewrite ES.rmwt; auto.
    specialize ES.same_tid_trans.
    basic_solver. }
  rewrite minus_inter_compl.
  unfolder. intros r w HH. intro SBEQ.
  desf; unfold "~" in HH1; apply HH1;
  rename HH into RMW, HH0 into TID; clear HH1.
  { right. right.
    apply ES.rmw_in_sb; eauto. }
  { apply ES.sb_imm_split_l in SBEQ; auto.
    unfold seq in SBEQ. desf. 
    assert (TID_ZZ0 : ES.same_tid S z z0).
    { apply immediate_in in SBEQ.
      eapply ES.same_tid_trans with (y := r).
      { apply ES.rmwt in RMW; basic_solver. }
      assert (NINIT_R : Eninit S r).
      { apply (dom_l (ES.rmwEninit WF)) in RMW.
        unfolder in RMW.
        basic_solver. }
      specialize ES.sb_tid.
      basic_solver 5. }
    assert (ICF : (ES.icf S)^? z z0).
    { apply ES.imm_tsb_imm_sb_in_icf; auto.
      apply ES.rmwi in RMW; auto.
      basic_solver. }
    unfolder in ICF. desf.
    { unfolder in SBEQ0; basic_solver. }
    specialize (icf_R WF CONS) as ICF_DOM.
    assert (R S z).
    { apply ICF_DOM in ICF. unfolder in ICF. basic_solver. }
    apply (dom_r (ES.rmwD WF)) in RMW. 
    unfolder in RMW.
    type_solver. }
  right. right.
  apply ES.rmw_in_sb in RMW; auto.
  specialize (ES.sb_trans).
  basic_solver.
Qed.
  
Lemma seq_codom_empty {A} (r r' : relation A)
      (x y : A)
      (Rxy : r x y):
  r ⨾ r' ⊆ ∅₂ -> ⦗codom_rel r⦘ ⨾ r' ⊆ ∅₂.
Proof.
  basic_solver.
Qed.

Lemma transp_empty {A} (r : relation A):
  r ⊆ ∅₂ <-> r⁻¹ ⊆ ∅₂.
Proof.
  basic_solver 5.
Qed.

Lemma hb_pref2_rmw_ncf (S : ES.t)
           (WF : ES.Wf S)
           (CONS : es_consistent (m := Weakestmo) S)
           (e w w' : eventid)
           (JF : jf S w e)
           (RMW : rmw S e w'):
  ES.cf_free S (hb_pref2 S w' w).
Proof.
  rewrite hb_pref2_alt.
  rewrite rmw_pref; eauto.
  rewrite set_unionC, <- set_unionA.
  rewrite set_unionC with (s := hb_pref S w).
  rewrite <- hb_pref2_alt.
  unfold ES.cf_free.
  rewrite !id_union, !seq_union_l, !seq_union_r.
  apply inclusion_union_l; apply inclusion_union_l.
  4: { specialize ES.cf_irr. basic_solver. }
  2: apply transp_empty; rewrite <- seq_transp_sym; [|apply ES.cf_sym].
  2, 3: arewrite (eq w' ⊆₁ codom_rel (⦗eq e⦘ ⨾ rmw S)); [basic_solver|];
        eapply seq_codom_empty; [basic_solver|];
        rewrite seqA;
        rewrite <- seqA with (r1 := rmw S);
        rewrite seq_rmw_cf_in_cf; auto;
        arewrite (eq e ⊆₁ hb_pref2 S e w); [unfold hb_pref2; basic_solver 7|].
  all: apply hb_pref2_ncf; auto.
Qed.

(******************************************************************************)
(** ** DRF lemmas *)
(******************************************************************************)


Section DRF.

Variable  P : IdentMap.t {linstr : list Instr.t & LblStep.stable_lprog linstr}.
Variable (nInitProg : ~ IdentMap.In tid_init P).

Lemma jf_in_hb
      (RACE_FREE : RC11_RLX_race_free_program P)
      (S : ES.t)
      (STEPS : (step Weakestmo)＊ (prog_es_init P) S):
  S.(ES.jf) ⊆ S.(hb).
Proof.
  eapply clos_refl_trans_ind_left with (P := fun s => s.(ES.jf) ⊆ s.(hb)); eauto.
  { basic_solver. }
  clear dependent S.
  intros G G' STEPS IH STEP.
  assert (STEPS_G' : (step Weakestmo)＊ (prog_es_init P) G').
  { eapply transitive_rt; eauto. apply rt_step. auto. }
  assert (WF_G : ES.Wf G).
  2: assert (WF_G' : ES.Wf G').
  1, 2: eby eapply steps_es_wf.
  generalize (hb_trans G'). intro HB_TRANS.    
  inversion_clear STEP as [e [e' HH]]. desf.
  assert (HB_MON: G.(hb) ⊆ G'.(hb)).
  { eapply step_hb_mon; eauto. }
  rename TT into STEP_.
  inversion STEP_ as [S | [S | [S | S]]].
  1, 3: inversion_clear S; desf; rewrite JF'; basic_solver. 
  { inversion S as [w HH]. desf.
    unfold AddJF.add_jf in AJF. desf.
    unfold AddJF.jf_delta in JF'. 
    rename rE' into eE', rR' into eR'.
    assert (wW' : is_w (lab G') w). 
    { eapply load_step_W; eauto. intuition. }
    assert (WE_JF' : jf G' w e).
    { apply JF'. apply inclusion_union_r2. basic_solver. }
    assert (ACTS_MON : E G ⊆₁ E G').
    { eapply BasicStep.basic_step_nupd_acts_mon; eauto. }

    assert (HB : (G'.(hb)⁼ w e) \/ (not (G'.(hb)⁼ w e))) by apply classic.
    destruct HB as [[WE_EQ | [ WE_HB | EW_HB]] | WE_NHB].
    { type_solver. }
    { rewrite JF'. basic_solver. } 
    { unfold transp in EW_HB.
      exfalso. eapply coh; eauto.
      eexists. split; eauto.
      apply r_step. apply rf_in_eco.
      apply ES.jf_in_rf; eauto. } 
    exfalso.
      assert (HB_DOM : dom_rel (hb G') ⊆₁ E G).
    { eapply step_nupd_hb_dom; eauto. }
    assert (PREF_HB_BWCL : dom_rel(hb G' ⨾ ⦗hb_pref2 G' e w⦘) ⊆₁ hb_pref2 G' e w).
    { rewrite hb_pref2_alt.
      rewrite id_union, seq_union_r, dom_union.
      rewrite !hb_pref_hb_bwcl. auto. }      
    assert (PREF_JF_BWCL : dom_rel(jf G' ⨾ ⦗hb_pref2 G' e w⦘) ⊆₁ hb_pref2 G' e w).
    { unfold hb_pref2.
      rewrite dom_rel_eqv_dom_rel.
      rewrite JF', IH.
      type_solver 9. }
    assert (PREF_EXEC : program_execution P G' (hb_pref2 G' e w)).
    { red. splits; auto. constructor. 
      { apply hb_pref2_inE; eauto. }
      { rewrite hb_pref2_alt.
        specialize (BasicStep.basic_step_acts_ninit_set BSTEP WF_G).
        specialize (init_in_hb_pref WF_G').
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
      { apply jf_bwcl_rf_compl; auto.
        apply hb_pref2_inE; auto. }
      { apply hb_pref2_ncf; auto. }
      assert (AE' : hb_pref2 G' e w ⊆₁ E G').
      { apply hb_pref2_inE; eauto. }
      apply ncf_hb_jf_bwcl_vis; auto.
      apply hb_pref2_ncf; auto. }
    assert (PREF_RC11 : rc11_consistent_x G' (hb_pref2 G' e w)).
    { red. exists (x2g G' (hb_pref2 G' e w)). splits.
      { apply x2g_X2G; auto. by cdes PREF_EXEC. } 
      apply x2g_rc11_consistent; auto.
      { by cdes PREF_EXEC. }
      rewrite restr_relE.
      rewrite seq_union_l, seq_union_r.
      rewrite <- restr_relE with (r := rf G'). 
      fold (Execution.ex_rf G' (hb_pref2 G' e w)).
      rewrite (Execution.ex_rf_restr_jf); auto.
      2: { by cdes PREF_EXEC. }
      rewrite <- restr_relE.
      rewrite JF', <- union_restr. 
      rewrite !inclusion_restr, <- unionA. 
      rewrite acyclic_absorb.
      2: { left. rewrite WF_G.(ES.jfE).
           rewrite dom_rel_helper with (r := sb G'). 
           2: { eapply step_nupd_sb_dom; eauto. }
           specialize (BasicStep.basic_step_acts_set_ne BSTEP) as NE.
           rewrite seq_union_r.
           rewrite codom_rel_helper with (rr := singl_rel w e).
           2: { apply codom_singl_rel. }
           rewrite !seqA.
           arewrite_false !(⦗eq e⦘ ⨾ ⦗E G⦘); [basic_solver|]. 
           basic_solver. }
      split.
      { rewrite sb_in_hb, IH, HB_MON, unionK. eby eapply hb_acyclic. }
      unfold acyclic. rewrite ct_singl_rel.
      assert (NEQ : w <> e).
      { intro. apply WE_NHB. basic_solver. }
      basic_solver. }
    specialize (RACE_FREE G' (hb_pref2 G' e w) PREF_EXEC PREF_RC11).
    assert (RACE_W : race G' (hb_pref2 G' e w) w).
    { unfold race. unfold dom_rel. exists e.
      unfolder. splits.
      1,2,4: unfold hb_pref2; basic_solver 10.
      { apply and_not_or. split; auto. }
      unfold one. auto. }
    assert (RACE_E : race G' (hb_pref2 G' e w) e).
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

  inversion S as [w HH]. desf.
  unfold AddJF.add_jf in AJF. desf.
  unfold AddJF.jf_delta in JF'. 
  rename rE' into eE', rR' into eR'.
  assert (w'W : is_w (lab G') w). 
  { eapply update_step_W; eauto. basic_solver. }
  assert (w'W' : is_w (lab G') w'). 
  { eapply update_step_W; eauto. basic_solver. }
  assert (w'E' : (E G') w').
  { eapply update_step_E; eauto. basic_solver. }
  assert (WE_JF' : jf G' w e).
  { apply JF'. apply inclusion_union_r2. basic_solver. }
  assert (ACTS_MON : E G ⊆₁ E G').
  { eapply BasicStep.basic_step_nupd_acts_mon; eauto. }
  assert (HB : (G'.(hb)⁼ w e) \/ (not (G'.(hb)⁼ w e))) by apply classic.
  destruct HB as [[WE_EQ | [ WE_HB | EW_HB]] | WE_NHB].
  { type_solver. }     
  { rewrite JF'. basic_solver. } 
  { unfold transp in EW_HB.
      exfalso. eapply coh; eauto.
      eexists. split; eauto.
      apply r_step. apply rf_in_eco.
      apply ES.jf_in_rf; eauto. } 
  exfalso.
  assert (PREF_HB_BWCL : dom_rel(hb G' ⨾ ⦗hb_pref2 G' w' w⦘) ⊆₁ hb_pref2 G' w' w).
  { unfold hb_pref2.
    rewrite dom_rel_eqv_dom_rel.
    rewrite <- seqA, (rewrite_trans_seq_cr_r (hb_trans G')).      
    basic_solver 10. }
  specialize (step_hb_dom BSTEP STEP_ WF_G) as HB_DOM.
  assert (PREF_JF_BWCL : dom_rel(jf G' ⨾ ⦗hb_pref2 G' w' w⦘) ⊆₁ hb_pref2 G' w' w).
  { unfold hb_pref2.
    rewrite dom_rel_eqv_dom_rel.
    rewrite JF', IH.
    type_solver 9. }

  assert (EW'_RMW : (ES.rmw G') e w').
  { cdes BSTEP. cdes BSTEP_.
    unfold BasicStep.rmw_delta in RMW'.
    apply RMW'. basic_solver. }
  assert (EW'_HB : (hb G') e w').
  { apply ES.rmw_in_sb, sb_in_hb in EW'_RMW; auto. }
  
    
    
  assert (PREF_EXEC : program_execution P G' (hb_pref2 G' w' w)).
  { red. splits; auto. constructor. 
    { apply hb_pref2_inE; eauto. }
    { rewrite hb_pref2_alt.
      specialize (BasicStep.basic_step_acts_ninit_set BSTEP WF_G).
      specialize (init_in_hb_pref WF_G').
      basic_solver 10. }
    { rewrite sb_in_hb. apply PREF_HB_BWCL. }
    { rewrite sw_in_hb. apply PREF_HB_BWCL. }
    { rewrite hb_pref2_alt.
      apply fwcl_hom; apply hb_pref_rmw_fwcl; auto.
      all: rewrite ES.rmwD; auto; type_solver. }
    { apply jf_bwcl_rf_compl; auto.
      apply hb_pref2_inE; auto. }
    { eapply hb_pref2_rmw_ncf; eauto. }
    apply ncf_hb_jf_bwcl_vis; auto.
    apply hb_pref2_inE; auto.
    eapply hb_pref2_rmw_ncf; eauto. }

  assert (PREF_RC11 : rc11_consistent_x G' (hb_pref2 G' w' w)).
  { red. exists (x2g G' (hb_pref2 G' w' w)). splits.
    { apply x2g_X2G; auto. by cdes PREF_EXEC. } 
    apply x2g_rc11_consistent; auto.
    { by cdes PREF_EXEC. }
    rewrite restr_relE.
    rewrite seq_union_l, seq_union_r.
    rewrite <- restr_relE with (r := rf G'). 
    fold (Execution.ex_rf G' (hb_pref2 G' w' w)).
    rewrite (Execution.ex_rf_restr_jf); auto.
    2: { by cdes PREF_EXEC. }
    rewrite <- restr_relE.
    rewrite JF', <- union_restr. 
    rewrite !inclusion_restr, <- unionA. 
    cdes BSTEP.
    arewrite (sb G' ⊆ sb G ∪ (E G ∪₁ eq e) × eq w' ∪ E G × eq e).
    { cdes BSTEP_. 
      unfold BasicStep.sb_delta in SB'.
      rewrite eq_opt_someE in SB'.
      rewrite SB' at 1.
      rewrite ES.cont_sb_domE at 1 2 3; eauto.
      basic_solver 20. }
    arewrite (sb G ∪ (E G ∪₁ eq e) × eq w' ∪ E G × eq e ∪ jf G ∪ singl_rel w e
                 ⊆ 
              sb G ∪ jf G ∪ (E G ∪₁ eq e) × eq w' ∪ E G × eq e).
    { basic_solver 20. }
    assert (nEe : ~ E G e).
    { eby eapply BasicStep.basic_step_acts_set_ne. } 
    assert (SB_JF_DOM : (sb G ∪ jf G) ⊆ ⦗E G⦘ ⨾ ⊤₂).
    { rewrite (dom_l WF_G.(ES.sbE)), (dom_l WF_G.(ES.jfE)).
      basic_solver. }
    apply acyclic_absorb; [left|].
    { rewrite seq_union_r.
      apply inclusion_union_l.
      { rewrite SB_JF_DOM at 1.
        seq_rewrite <- cross_inter_r.
        basic_solver. }
      basic_solver. }
    assert (nEw' : ~ E G w').
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
    specialize (RACE_FREE G' (hb_pref2 G' w' w) PREF_EXEC PREF_RC11).
    assert (RACE_W : race G' (hb_pref2 G' w' w) w).
    { unfold race. unfold dom_rel. exists e.
      unfolder. splits.
      1,2,4: unfold hb_pref2; basic_solver 10.
      { apply and_not_or. split; auto. }
      unfold one. auto. }
    assert (RACE_E : race G' (hb_pref2 G' w' w) e).
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
      (JF_IN_HB : S.(ES.jf) ⊆ S.(hb)):
  restr_rel X S.(ES.rf) ⊆ S.(ES.jf). 
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
      (JF_IN_HB : S.(ES.jf) ⊆ S.(hb)):
  acyclic (restr_rel X (S.(ES.sb) ∪ S.(ES.rf))).
Proof.
  rewrite sb_in_hb.
  rewrite <- union_restr, (rf_in_jf WF EXEC JF_IN_HB).
  rewrite JF_IN_HB, inclusion_restr, unionK. 
  eby eapply hb_acyclic. 
Qed.

Theorem DRF_WEAKESTMO_RLX S X
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
End DRF_WEAKESTMO_RLX.
