From hahn Require Import Hahn.
From imm Require Import Events AuxRel Prog ProgToExecutionProperties RC11.
Require Import AuxDef.
Require Import AuxRel.
Require Import EventStructure.
Require Import Consistency.
Require Import Execution.
Require Import Step.
Require Import Race.
Require Import ProgES.
Require Import StepWf.

Set Implicit Arguments.

Module DRF.

Definition program_execution P S X :=
  ⟪ STEPS : (step Weakestmo)＊ (prog_es_init P) S⟫ /\
  ⟪ EXEC : Execution.t S X ⟫.

Definition RLX_race_free_program P :=
  (forall S X, program_execution P S X -> Race.rc11_consistent_x S X -> Race.RLX_race_free S X).

Lemma wf_es P
      (S : ES.t)
      (STEPS : (step Weakestmo)＊ (prog_es_init P) S):
  ES.Wf S.
Proof.
  eapply clos_refl_trans_ind_left; eauto.
  { admit. }
  clear dependent S.
  intros S S' STEPS WF_S STEP.
  inversion STEP as [e]. desf.  
  eapply step_wf; eauto.
  admit.
Admitted.

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

Lemma codom_rel_helper {A} (r : relation A) d (IN:  codom_rel r ⊆₁ d) : r ≡ r ⨾ ⦗d⦘.
Proof.
unfolder in *; basic_solver.
Qed.


Lemma ct_imm_split_l {A} (r : relation A)
      (IRR: irreflexive r)
      (TANS: transitive r)
      (acts : list A)
      (DOM_IN_ACTS: dom_rel r ⊆₁ (fun x : A => In x acts)):
  r ≡ immediate r ⨾ r^?.
Proof.
  split.
  2: { basic_solver. }
  rewrite ct_imm1 at 1; eauto.
  rewrite ct_begin. apply seq_mori; [done|].
  rewrite immediate_in. apply  rt_of_trans; eauto.
Qed.

Lemma hb_imm_split_l S
      (WF: ES.Wf S)
      (CONS : es_consistent S (m := Weakestmo)):
  S.(hb) ≡ immediate S.(hb) ⨾ S.(hb)^?.
Proof.
  eapply ct_imm_split_l.
  { eapply hb_irr. eauto. }
  { eauto with hahn. }
  rewrite (dom_l (hbE S WF)).
  rewrite dom_seq, dom_eqv, ES.E_alt.
  eauto.
Qed.

Lemma imm_clos_trans {A} (r : relation A) :
  immediate r⁺ ⊆ immediate r.
Proof.
  split.
  { assert (immediate r⁺ ⊆ r); eauto.
    rewrite immediateE.
    rewrite ct_begin at 1. rewrite rt_begin, seq_union_r, minus_union_l.
    rewrite seq_id_r. apply inclusion_union_l; eauto with hahn.
    erewrite inclusion_minus_mon with (r' := r ⨾ r ⨾ r＊) (s' := r ⨾ r ⨾ r＊); [|done|].
    { rewrite minus_absorb; done. }
    rewrite ct_begin at 1. rewrite ct_end, seqA.  apply seq_mori; eauto with hahn.
    rewrite <- seqA, rt_rt.
    rewrite <- ct_begin, ct_end.
    eauto with hahn. }
  intros. apply ct_step in R1. apply ct_step in R2.
  inversion H. eauto.
Qed.

Lemma imm_union {A} (r1 r2 : relation A):
  immediate (r1 ∪ r2) ⊆ immediate r1 ∪ immediate r2.
Proof.
  basic_solver 10.
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

Lemma dom_eqv_tr_codom {A} (r : relation A):
  dom_rel r ≡₁ codom_rel r⁻¹.
Proof.
  basic_solver.
Qed.

Lemma tr_dom_eqv_codom {A} (r : relation A):
  dom_rel r⁻¹ ≡₁ codom_rel r.
Proof.
  basic_solver.
Qed.

Lemma codom_rel_eqv_dom_rel {A} (r r' : relation A):
  codom_rel (⦗dom_rel r⦘ ⨾ r') ≡₁ codom_rel (r⁻¹ ⨾ r').
Proof.
  basic_solver.
Qed.

Lemma dom_in_seq_with_tr {A} (r: relation A):
  ⦗dom_rel r⦘ ⊆ r ⨾ r⁻¹. 
Proof.
  basic_solver.
Qed.


Lemma dom_ct {A} (r : relation A) :
  dom_rel r⁺ ≡₁ dom_rel r.
Proof.
  rewrite ct_begin.
  basic_solver 7.
Qed.

Lemma t_rmw_hb_in_hb S
      (WF : ES.Wf S)
      (CONS : es_consistent S (m := Weakestmo)):
  S.(ES.rmw)⁻¹ ⨾ S.(hb) ⊆ S.(hb)^?.
Proof.
  rewrite WF.(ES.rmwD).
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
  { erewrite  (dom_rel_helper (icf_R S CONS)). type_solver. }
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

Lemma union_seq_cf_same_tid_r (S : ES.t) (m : model)
      (CONS : es_consistent S (m := m))
      (WF : ES.Wf S)
      (r1 r2 : relation eventid)
      (SAME_TID : r2 ⊆ compl_rel (ES.same_tid S))
  : S.(ES.cf) ∩ (r1 ⨾ r2) ≡ S.(ES.cf) ∩ r1 ⨾ r2.
Admitted.
    
  

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
  red. rewrite dom_in_seq_with_tr, !seqA.
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
  apply eq_predicate in vA.
  rewrite vA.
  rewrite (dom_rel_helper (hb_jf_bwcl_cc_bwcl WF CONS JF_BWCL HB_BWCL)). 
  unfold cc. rewrite inclusion_inter_l1.  
  auto. 
Qed.

(******************************************************************************)
(** ** DRF lemmas *)
(******************************************************************************)

Lemma jf_in_hb P
      (RACE_FREE : RLX_race_free_program P)
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
  { eapply wf_es; eauto. }
  assert (WF_G' : ES.Wf G').
  { eapply wf_es; eauto. } 
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
     
    assert (PREF_RC11 : Race.rc11_consistent_x G' (hb_pref2 G' e w)).
    { unfold Race.rc11_consistent_x. admit. }
    
    specialize (RACE_FREE G' (hb_pref2 G' e w) PREF_EXEC PREF_RC11).
    
    assert (RACE_W : Race.race G' (hb_pref2 G' e w) w).
    { unfold Race.race. unfold dom_rel. exists e.
      unfolder. splits.
      1, 2: unfold hb_pref2; basic_solver 10.
      apply or_not_and. left. apply or_not_and. left. apply and_not_or. auto. }

    assert (RACE_E : Race.race G' (hb_pref2 G' e w) e).
    { unfold Race.race. unfold dom_rel. exists w.
      unfolder. splits.
      1, 2: unfold hb_pref2; basic_solver 10. 
      apply or_not_and. left. apply or_not_and. left. apply and_not_or. split.
      { unfolder in WE_NHB. intuition. }
      intro HH. auto. apply ES.cf_sym in HH. auto. }
    specialize (RACE_FREE w RACE_W) as QW.
    specialize (RACE_FREE e RACE_E) as QE.
    destruct QE as [|wREL]; destruct QW as [eACQ|].
    1, 2, 4: type_solver.
    unfold Race.RLX_race_free in RACE_FREE.
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
  assert (HB_CLOS_PREFIX : dom_rel(hb G' ⨾ ⦗hb_pref2 G' w' w⦘) ⊆₁ hb_pref2 G' w' w).
  { unfold hb_pref2.
    rewrite dom_rel_eqv_dom_rel.
    rewrite <- seqA, (rewrite_trans_seq_cr_r (hb_trans G')).      
    basic_solver 10. }
  specialize (step_hb_dom BSTEP STEP_ WF_G) as HB_DOM.
  assert (JF_CLOS_PREFIX : dom_rel(jf G' ⨾ ⦗hb_pref2 G' w' w⦘) ⊆₁ hb_pref2 G' w' w).
  { unfold hb_pref2.
    rewrite dom_rel_eqv_dom_rel.
    rewrite JF', IH.
    type_solver 9. }
  admit. 

Admitted.

Lemma rf_in_jf (S : ES.t) (X : eventid -> Prop)
      (WF : ES.Wf S)
      (EXEC : Execution.t S X)
      (JF_IN_HB : S.(ES.jf) ⊆ S.(hb)):
  ⦗X⦘ ⨾ S.(ES.rf) ⨾ ⦗X⦘ ⊆ S.(ES.jf).
Proof.
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
  acyclic (⦗X⦘ ⨾ S.(ES.sb) ⨾ ⦗X⦘ ∪ ⦗X⦘ ⨾ S.(ES.rf) ⨾ ⦗X⦘).
Proof.
  rewrite sb_in_hb.
  rewrite (rf_in_jf WF EXEC JF_IN_HB), JF_IN_HB.
  specialize (hb_acyclic S Weakestmo CONS) as HB_ACYCLIC.
  rewrite <- restr_relE, inclusion_restr.
  relsf.
Qed.
  
End DRF.
