Require Import Omega.
From hahn Require Import Hahn.
From PromisingLib Require Import Basic.
From imm Require Import Events Execution
     Traversal TraversalConfig SimTraversal SimTraversalProperties
     Prog ProgToExecution ProgToExecutionProperties Receptiveness
     imm_common imm_s imm_s_hb SimState PromiseLTS
     CertExecution2
     SubExecution CombRelations.
Require Import AuxRel.
Require Import AuxDef.
Require Import LblStep.
Require Import CertRf.
Require Import ImmProperties.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Classical_Prop.

Set Implicit Arguments.
Local Open Scope program_scope.

Section CertGraph.
  Variable prog : Prog.t.
  Variable G  : execution.
  Variable GPROG : program_execution prog G.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable TC': trav_config.
  Variable thread : thread_id.
  Variable state : state.
    
  Notation "'certG'" := state.(ProgToExecution.G).

  Notation "'certE'" := certG.(acts_set).

  Definition certLab : actid -> label :=
    restr_fun certE certG.(lab) G.(lab).

  Notation "'certRmw'" := (certG.(rmw)).

  Notation "'cert_rf'" := (cert_rf G sc TC' thread).

  Notation "'E'" := G.(acts_set).

  Notation "'Tid' t" := (fun x => tid x = t) (at level 1).
  Notation "'NTid' t" := (fun x => tid x <> t) (at level 1).

  Notation "'R'" := (fun a => is_true (is_r G.(lab) a)).
  Notation "'W'" := (fun a => is_true (is_w G.(lab) a)).
  Notation "'F'" := (fun a => is_true (is_f G.(lab) a)).

  Notation "'Rel'" := (fun a => is_true (is_rel G.(lab) a)).

  Notation "'R_ex'" := (fun a => R_ex G.(lab) a).
  
  Notation "'sb'" := (G.(sb)).
  Notation "'rmw'" := G.(rmw).
  Notation "'addr'" := G.(addr).
  Notation "'data'" := G.(data).
  Notation "'ctrl'" := G.(ctrl).
  Notation "'rmw_dep'" := G.(rmw_dep).
  Notation "'rf'" := (G.(rf)).
  Notation "'co'" := (G.(co)).
  
  Notation "'ppo'" := (G.(ppo)).
  Notation "'hb'" := (G.(imm_s_hb.hb)).
  Notation "'vf'" := (furr G sc).

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).
  Notation "'C''"  := (covered TC').
  Notation "'I''"  := (issued TC').

  Notation "'E0'" := (E0 G TC' thread).
  Notation "'D'" := (D G TC' thread).

  Definition cert_dom st := 
    (C ∪₁ (dom_rel (sb^? ⨾ ⦗ I ⦘) ∩₁ NTid thread) ∪₁ acts_set st.(ProgToExecution.G)).  

  Lemma cert_dom_alt st 
    (STCOV : C ∩₁ Tid thread ⊆₁ acts_set st.(ProgToExecution.G)) :
      cert_dom st ≡₁ 
               (C ∪₁ dom_rel (sb^? ⨾ ⦗ I ⦘)) ∩₁ NTid thread ∪₁ 
               acts_set st.(ProgToExecution.G). 
  Proof. 
    unfold cert_dom. 
    split; [|basic_solver 10]. 
    arewrite (C ≡₁ C ∩₁ Tid thread ∪₁ C ∩₁ NTid thread) at 1.
    { rewrite <- set_inter_union_r.
      rewrite tid_set_dec.
      basic_solver. }
    rewrite STCOV. basic_solver 10.
  Qed.

  Record cert_graph :=
    { cslab : eq_dom D certLab G.(lab);
      cuplab_cert : same_lab_u2v_dom certE certG.(lab) G.(lab);
      
      dcertE : certE ≡₁ E0;
      dcertRMW : certRmw ≡ ⦗ certE ⦘ ⨾ rmw;
      
      cert_rfv_clab : cert_rf ⊆ same_val certLab;
      cert_rfl_clab : cert_rf ⊆ same_loc certLab;
      cert_rf_iss_sb : cert_rf ⊆ ⦗ I ⦘ ⨾ cert_rf ∪ sb;
    }.

  Section CertGraphProperties.
    Variable WF : Wf G.
    Variable Wf_sc : wf_sc G sc.
    Variable IMMC : imm_consistent G sc.
    Variable TCCOH : tc_coherent G sc TC.
    Variable TSTEP : isim_trav_step G sc thread TC TC'.

    Lemma isim_trav_step_coherence : tc_coherent G sc TC'.
    Proof. eapply sim_trav_step_coherence; eauto. red. eauto. Qed.
    
    Hint Resolve isim_trav_step_coherence.

    Lemma trstep_thread_prog : IdentMap.In thread prog. 
    Proof. 
      apply sim_trav_step_to_step in TSTEP. 
      destruct TSTEP as [e [T'' ITSTEP]]. desf. 
      assert (E e) as EE.
      { cdes ITSTEP. desf.
        { apply COV. }
        apply ISS. }
      set (BB := EE).
      apply GPROG in BB.
      desf. exfalso.
      cdes ITSTEP. desf.
      { apply NEXT. by eapply init_covered; eauto. }
      apply NISS. by eapply init_issued; eauto. 
    Qed.

    (******************************************************************************)
    (** ** E0 propeties *)
    (******************************************************************************)

    Lemma E0_in_thread_execE st
          (TEH : thread_restricted_execution G thread st.(ProgToExecution.G)) :
      E0 ⊆₁ acts_set st.(ProgToExecution.G).
    Proof. 
      rewrite tr_acts_set; eauto.
      rewrite set_interC.
      apply set_subset_inter; auto.
      rewrite coveredE; eauto.
      rewrite issuedE; eauto.
      rewrite wf_sbE.
      basic_solver.
    Qed.

    Lemma E0_eindex_weak e (CTE : E0 e) (NINITT : thread <> tid_init) : 
      exists index : nat,
        ⟪ EREP : e = ThreadEvent thread index ⟫.
    Proof. 
      ins. destruct CTE as [AA BB].
      destruct e; simpls; rewrite <- AA in *; desf.
      eauto. 
    Qed.

    Lemma E0_eindex st 
          (NINITT : thread <> tid_init)
          (GPC : wf_thread_state thread st)
          (TEH : thread_restricted_execution G thread st.(ProgToExecution.G)) : 
      exists ctindex,
        ⟪ CCLOS :forall index (LT : index < ctindex),
            E0 (ThreadEvent thread index) ⟫ /\
        ⟪ CREP : forall e (CTE : E0 e),
            exists index : nat,
              ⟪ EREP : e = ThreadEvent thread index ⟫ /\
              ⟪ ILT : index < ctindex ⟫ ⟫.
    Proof. 
      assert (E0 ⊆₁ E) as E0_in_E.
      { eapply E0_in_E; eauto. }
      destruct (classic (exists e, E0 e)) as [|NCT].
      2: { exists 0. splits.
           { ins. inv LT. }
           ins. exfalso. apply NCT. eauto. }
      desc.
      assert (acyclic (sb ⨾ ⦗ E0 ⦘)) as AC.
      { arewrite (sb ⨾ ⦗E0⦘ ⊆ sb). apply sb_acyclic. }
      set (doml := filterP E0 G.(acts)).
      assert (forall c, (sb ⨾ ⦗E0⦘)＊ e c -> In c doml) as UU.
      { intros c SCC. apply rtE in SCC. destruct SCC as [SCC|SCC].
        { red in SCC. desf. apply in_filterP_iff. 
          split; auto. eapply E0_in_E. eauto. }
        apply inclusion_ct_seq_eqv_r in SCC. apply seq_eqv_r in SCC.
        apply in_filterP_iff. split; auto; [apply E0_in_E|]; desf. }
      edestruct (last_exists doml AC UU) as [max [MM1 MM2]].
      assert (E0 max) as CTMAX.
      { apply rtE in MM1. destruct MM1 as [MM1|MM1].
        { red in MM1. desf. }
        apply inclusion_ct_seq_eqv_r in MM1. apply seq_eqv_r in MM1. desf. }
      assert (Tid thread max) as CTTID by apply CTMAX.
      destruct max as [l|mthread mindex].
      { simpls. rewrite <- CTTID in *. desf. }
      simpls. rewrite CTTID in *.
      assert (acts_set G (ThreadEvent thread mindex)) as EEM.
      { by apply E0_in_E. }
      exists (1 + mindex). splits.
      { ins. destruct CTMAX as [_ CTMAX].
        split; [by ins|].
        apply le_lt_or_eq in LT. destruct LT as [LT|LT].
        2: { inv LT. }
        assert (acts_set (st.(ProgToExecution.G)) (ThreadEvent thread mindex)) as PP.
        { apply TEH.(tr_acts_set). by split. }
        assert (E (ThreadEvent thread index)) as EEE.
        { apply TEH.(tr_acts_set). eapply acts_rep in PP; eauto. desc.
          eapply GPC.(acts_clos). inv REP. omega. }
        assert (sb (ThreadEvent thread index) (ThreadEvent thread mindex)) as QQQ.
        { red.
          apply seq_eqv_l. split; auto.
          apply seq_eqv_r. split; auto.
          red. split; auto. omega. }
        destruct CTMAX as [AA|[z AA]]; [left|right].
        { apply isim_trav_step_coherence in AA. apply AA. eexists.
          apply seq_eqv_r. split; eauto. }
        exists z. apply seq_eqv_r in AA. destruct AA as [AA1 AA2].
        apply seq_eqv_r. split; auto.
        apply rewrite_trans_seq_cr_cr.
        { apply sb_trans. }
        eexists; split; [|by eauto].
          by apply r_step. }
      ins. set (CTE' := CTE).
      apply E0_eindex_weak in CTE'; auto; desc.
      eexists. splits; eauto.
      destruct (le_gt_dec index mindex) as [LL|LL].
      { by apply le_lt_n_Sm. }
      exfalso.
      eapply MM2. apply seq_eqv_r. split; [|by apply CTE].
      red.
      apply seq_eqv_l. split; auto.
      apply seq_eqv_r. split; auto.
      red. rewrite EREP. 
      split; auto.  
    Qed.

    (******************************************************************************)
    (** ** certLab propeties *)
    (******************************************************************************)

    Lemma cuplab (SCG : cert_graph) :
      same_lab_u2v certLab G.(lab).
    Proof.
      red. red. ins.
      unfold certLab. 
      unfold restr_fun.
      desf.
      { by apply SCG. }
      red. desf.
    Qed.

    (******************************************************************************)
    (** ** cert_rf propeties *)
    (******************************************************************************)

    Lemma cert_rf_w (SCG : cert_graph) : 
      cert_rf ≡ ⦗ W ⦘ ⨾ cert_rf.
    Proof. rewrite cert_rfD; auto. basic_solver. Qed.

    Lemma cert_rf_ntid_iss_sb 
          (SCG : cert_graph)
          (IRELCOV : W ∩₁ Rel ∩₁ I ⊆₁ C) :
      cert_rf ⊆ ⦗ NTid thread ∩₁ I ⦘ ⨾ cert_rf ∪ sb.
    Proof.
      etransitivity.
      { apply cert_rf_ntid_sb; auto. 
        eapply sim_trav_step_rel_covered; eauto. 
        eexists; eauto. }
      sin_rewrite cert_rf_iss_sb; auto. 
      basic_solver 10.
    Qed.

    Lemma cert_rf_cert_dom st
          (SCG : cert_graph)
          (IRELCOV : W ∩₁ Rel ∩₁ I ⊆₁ C) 
          (NINITT : thread <> tid_init) 
          (WFST : wf_thread_state thread st) :
      dom_rel (cert_rf ⨾ ⦗ eq (ThreadEvent thread st.(eindex)) ⦘) ⊆₁ cert_dom st.
    Proof. 
      unfold cert_dom. 
      rewrite cert_rf_codomt. 
      erewrite cert_rf_ntid_iss_sb; eauto.
      rewrite !seq_union_l, dom_union. 
      apply set_subset_union_l. split.
      { basic_solver 10. }
      rewrite sb_tid_init'.
      rewrite !seq_union_l, dom_union. 
      apply set_subset_union_l. split.
      { arewrite (sb ∩ same_tid ⨾ ⦗Tid thread⦘ ≡ ⦗Tid thread⦘ ⨾ sb). 
        { unfolder; splits; ins; splits; desf; auto.  
          { unfold same_tid. 
            edestruct sb_tid_init as [STID | INITx]; eauto.  
            exfalso. apply NINITT.
            by apply is_init_tid in INITx. }
          edestruct sb_tid_init as [STID | INITx]; eauto.  
          exfalso. apply NINITT.
          by apply is_init_tid in INITx. }
        intros x [y HH]. right. 
        apply seq_eqv_lr in HH. 
        destruct HH as [TIDx [SB EQy]].
        destruct x; [intuition|]. 
        unfold tid in TIDx. subst.
        apply acts_clos; auto. 
        unfold Execution.sb, ext_sb in SB.
        apply seq_eqv_lr in SB; desf. }
      rewrite !seqA, seq_eqv.
      intros x [y HH].
      apply seq_eqv_lr in HH.
      destruct HH as [INITx [SB _]].
      do 2 left. 
      eapply init_covered; eauto. 
      split; auto. 
      unfold Execution.sb in SB. 
      apply seq_eqv_lr in SB; desf. 
    Qed.

    (******************************************************************************)
    (** ** deps propeties *)
    (******************************************************************************)

    Lemma dom_addrE_in_D : dom_rel (addr ⨾ ⦗ E0 ⦘) ⊆₁ D.
    Proof.
      unfold CertRf.E0.
      rewrite set_inter_union_r.
      rewrite id_union; relsf; unionL; splits.
      { rewrite (addr_in_sb WF).
        generalize (dom_sb_covered isim_trav_step_coherence).
        unfold CertExecution2.D; basic_solver 21. }
      arewrite (Tid thread ∩₁ dom_rel (sb^? ⨾ ⦗I'⦘) ⊆₁
                      dom_rel (sb^? ⨾ ⦗I'⦘)) by basic_solver.
      rewrite dom_rel_eqv_dom_rel.
      arewrite (⦗I'⦘ ⊆ ⦗W⦘ ⨾ ⦗I'⦘).
      { generalize (issuedW isim_trav_step_coherence); basic_solver. }
      rewrite (dom_l (wf_addrD WF)), !seqA.
      arewrite (⦗R⦘ ⨾ addr ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppo).
      { unfold imm_common.ppo; rewrite <- ct_step; basic_solver 12. }
      unfold CertExecution2.D; basic_solver 21.
    Qed.

    Lemma dom_ctrlE_in_D : dom_rel (ctrl ⨾ ⦗ E0 ⦘) ⊆₁ D.
    Proof.
      unfold CertRf.E0.
      rewrite set_inter_union_r.
      rewrite id_union; relsf; unionL; splits.
      { rewrite (ctrl_in_sb WF).
        generalize (dom_sb_covered isim_trav_step_coherence).
        unfold CertExecution2.D; basic_solver 21. }
      arewrite (Tid thread ∩₁ dom_rel (sb^? ⨾ ⦗I'⦘) ⊆₁
                      dom_rel (sb^? ⨾ ⦗I'⦘)) by basic_solver.
      rewrite dom_rel_eqv_dom_rel.
      arewrite (ctrl ⨾ sb^? ⊆ ctrl).
      { generalize (ctrl_sb WF); basic_solver 21. }
      arewrite (⦗I'⦘ ⊆ ⦗W⦘ ⨾ ⦗I'⦘).
      { generalize (issuedW isim_trav_step_coherence); basic_solver. }
      rewrite (wf_ctrlD WF), !seqA.
      arewrite (⦗R⦘ ⨾ ctrl ⨾ ⦗W⦘ ⊆ ppo).
      { unfold imm_common.ppo; rewrite <- ct_step; basic_solver 12. }
      unfold CertExecution2.D; basic_solver 21.
    Qed.

    Lemma dom_rmw_depE_in_D : dom_rel (rmw_dep ⨾ ⦗ E0 ⦘) ⊆₁ D.
    Proof.
      unfold CertRf.E0.
      rewrite set_inter_union_r.
      rewrite id_union; relsf; unionL; splits.
      { rewrite (rmw_dep_in_sb WF).
        generalize (dom_sb_covered isim_trav_step_coherence).
        unfold CertExecution2.D; basic_solver 21. }
      arewrite (Tid thread ∩₁ dom_rel (sb^? ⨾ ⦗I'⦘) ⊆₁
                      dom_rel (sb^? ⨾ ⦗I'⦘)) by basic_solver.
      rewrite dom_rel_eqv_dom_rel.
      rewrite (wf_rmw_depD WF), !seqA.
      arewrite (⦗I'⦘ ⊆ ⦗W⦘ ⨾ ⦗I'⦘).
      { generalize (issuedW isim_trav_step_coherence); basic_solver. }
      arewrite (⦗R⦘ ⨾ rmw_dep ⨾ ⦗R_ex⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppo).
      2: unfold CertExecution2.D; basic_solver 21.
      unfold imm_common.ppo; hahn_frame.
      case_refl _.
      { by rewrite <- ct_step; basic_solver 12. }
      rewrite ct_begin; rewrite <- inclusion_t_rt, <- ct_step; basic_solver 12.
    Qed.

    Lemma dom_rmwE_in_D : dom_rel (rmw ⨾ ⦗ E0 ⦘) ⊆₁ D.
    Proof.
      unfold CertRf.E0.
      rewrite set_inter_union_r.
      rewrite id_union; relsf; unionL; splits.
      { rewrite (rmw_in_sb WF).
        generalize (dom_sb_covered isim_trav_step_coherence).
        unfold CertExecution2.D; basic_solver 21. }
      arewrite (Tid thread ∩₁ dom_rel (sb^? ⨾ ⦗I'⦘) ⊆₁
                      dom_rel (sb^? ⨾ ⦗I'⦘)) by basic_solver.
      rewrite dom_rel_eqv_dom_rel.
      arewrite (⦗I'⦘ ⊆ ⦗W⦘ ⨾ ⦗I'⦘).
      { generalize (issuedW isim_trav_step_coherence); basic_solver. }
      generalize (rmw_in_ppo WF) (rmw_sb_W_in_ppo WF).
      unfold CertExecution2.D; basic_solver 21.
    Qed.

    Lemma dom_dataD_in_D : dom_rel (data ⨾ ⦗D⦘) ⊆₁ D.
    Proof.
      unfold CertRf.E0.
      unfold CertExecution2.D.
      rewrite !id_union; relsf; unionL; splits.
      { rewrite (data_in_sb WF).
        generalize dom_sb_covered. basic_solver 21. }
      { rewrite (data_in_ppo WF).
        basic_solver 12. }
      { rewrite (data_in_sb WF).
        rewrite (dom_l (@wf_sbE G)) at 1.
        rewrite sb_tid_init' at 1; relsf; unionL; split.
        { unionR left -> left -> left -> right.
          unfold same_tid; unfolder; ins; desf; eauto 20. }
        arewrite (⦗E⦘ ⨾ ⦗fun a : actid => is_init a⦘ ⊆ ⦗D⦘).
        generalize D_init; basic_solver.
        arewrite (dom_rel (⦗D⦘ ⨾ sb ⨾ ⦗E ∩₁ NTid thread⦘) ⊆₁ D) by basic_solver.
        unfold CertExecution2.D; basic_solver 12. }
      { rewrite dom_rel_eqv_dom_rel.
        rewrite crE at 1; relsf; unionL; splits.
        { rewrite (dom_r (wf_dataD WF)), (dom_l (@wf_ppoD G)). type_solver. }
        rewrite (data_in_ppo WF).
        sin_rewrite ppo_rfi_ppo. basic_solver 21. }
      { rewrite (dom_r (wf_dataD WF)), (dom_r (wf_rfiD WF)). type_solver. }
      rewrite (dom_r (wf_dataD WF)), (dom_r (wf_rfeD WF)). type_solver.
    Qed.

  End CertGraphProperties.
End CertGraph. 

Section CertGraphLemmas.

Variable prog : Prog.t.
Variable G  : execution.
Variable GPROG : program_execution prog G.
Variable sc : relation actid.
Variable TC : trav_config.
Variable TC': trav_config.
Variable thread : thread_id.

Notation "'E'" := G.(acts_set).

Notation "'R'" := (fun a => is_true (is_r G.(lab) a)).
Notation "'W'" := (fun a => is_true (is_w G.(lab) a)).
Notation "'F'" := (fun a => is_true (is_f G.(lab) a)).

Notation "'Rel'" := (fun a => is_true (is_rel G.(lab) a)).

Notation "'R_ex'" := (fun a => R_ex G.(lab) a).

Notation "'sb'" := (G.(sb)).
Notation "'rmw'" := G.(rmw).
Notation "'addr'" := G.(addr).
Notation "'data'" := G.(data).
Notation "'ctrl'" := G.(ctrl).
Notation "'rmw_dep'" := G.(rmw_dep).
Notation "'rf'" := (G.(rf)).
Notation "'co'" := (G.(co)).

Notation "'ppo'" := (G.(ppo)).
Notation "'hb'" := (G.(imm_s_hb.hb)).
Notation "'vf'" := (furr G sc).

Notation "'C'"  := (covered TC).
Notation "'I'"  := (issued TC).
Notation "'C''"  := (covered TC').
Notation "'I''"  := (issued TC').

Notation "'E0'" := (E0 G TC' thread). 
Notation "'D'" := (D G TC' thread).

Notation "'Tid' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid' t" := (fun x => tid x <> t) (at level 1).

Variable WF : Wf G.
Variable Wf_sc : wf_sc G sc.
Variable IMMC : imm_consistent G sc.
Variable TCCOH : tc_coherent G sc TC.
Variable TSTEP : isim_trav_step G sc thread TC TC'.

Hint Resolve isim_trav_step_coherence. 

(******************************************************************************)
(** ** cert_graph start lemma *)
(******************************************************************************)

Lemma cert_graph_start 
      (state : Language.Language.state (PromiseLTS.thread_lts thread))
      (NINITT : thread <> tid_init)
      (GPC : wf_thread_state thread state)
      (PROGST : stable_lprog (instrs state))
      (REACHABLE : (step thread)＊ (init (instrs state)) state)
      (SSTATE : sim_state G sim_normal C state)
      (STATECOV : acts_set state.(ProgToExecution.G) ⊆₁ C)
      (RMWCLOS : forall r w (RMW : rmw r w), C r <-> C w)
      (IRELCOV : W ∩₁ Rel ∩₁ I ⊆₁ C) :
  exists state', 
    ⟪ CERTG : cert_graph G sc TC TC' thread state' ⟫ /\
    ⟪ CST_STABLE : stable_state state' ⟫ /\
    ⟪ CST_REACHABLE : (step thread)＊ state state' ⟫.
Proof. 
    cdes SSTATE. cdes SSTATE1.

    assert (wf_thread_state thread state') as GPC'.
    { eapply wf_thread_state_steps; eauto. }

    assert (forall r w, rmw r w -> covered TC' r <-> covered TC' w) as RMWCOV.
    { eapply sim_trav_step_rmw_covered; eauto.
      red. eauto. }

    edestruct E0_eindex; eauto; desf. 
    edestruct steps_middle_set with
      (thread := thread)
      (state0 := state) (state':=state') as [state''].
    3: { eapply E0_in_thread_execE; eauto. }
    all: eauto. 
    { apply set_subset_inter_r. split.
      { etransitivity. 
        { eapply steps_preserve_E; eauto. }
        etransitivity. 
        { eapply TEH.(tr_acts_set). }
        basic_solver. }
      unionR left.
      etransitivity; eauto.
      eapply sim_trav_step_covered_le. red. eauto. }
    { ins.
      eapply rmw_in_thread_restricted_rmw in RMW; eauto.
      split; intros [TT XX]; split.
      1,3: by apply WF.(wf_rmwt) in RMW; rewrite <- TT; red in RMW; desf.
      all: destruct XX as [XX|XX]; [by left; eapply RMWCOV with (r:=r); eauto|right].
      all: destruct XX as [e XX].
      all: apply seq_eqv_r in XX; destruct XX as [SB II].
      all: exists e; apply seq_eqv_r; split; auto.
      2: { apply (wf_rmwi WF) in RMW.
           generalize SB RMW (@sb_trans G). basic_solver. }
      assert (R r) as RR.
      { apply WF.(wf_rmwD) in RMW. destruct_seq RMW as [AAA BBB].
        type_solver. }
      apply (wf_rmwi WF) in RMW.
      destruct SB as [|SB]; subst.
      { eapply issuedW in II; eauto. type_solver. }
      destruct (classic (w = e)) as [|NEQ]; [by left|].
      assert (~ is_init r) as NINIT.
      { intros GG. eapply WF.(init_w) in GG.
        type_solver. }
      edestruct sb_semi_total_l with (y:=w) (z:=e); eauto.
      { apply RMW. }
      exfalso. eapply RMW; eauto. }
    desf. 

    assert (wf_thread_state thread state'') as GPC''.
    { eapply wf_thread_state_steps. apply GPC. auto. }
    
    set (new_rf := cert_rf G sc TC' thread ⨾ ⦗ E0 \₁ D ⦘).
    set (new_rfi := ⦗ Tid thread ⦘ ⨾ new_rf ⨾ ⦗ Tid thread ⦘).
    set (new_rfe := ⦗ NTid thread ⦘ ⨾ new_rf ⨾ ⦗ Tid thread ⦘).
    set (new_rfe_ex := new_rfe ∪ ⦗ set_compl (codom_rel new_rfe) ⦘).

    assert (new_rfi ⊆ cert_rfi G sc TC' thread) as NEWRFI_IN_CERT. 
    { unfold cert_rfi. unfold new_rfi, new_rf. basic_solver. }

    assert (new_rff : functional new_rf⁻¹).
    { arewrite (new_rf ⊆ cert_rf G sc TC' thread).
      apply cert_rff; auto. }
    assert (new_rfif : functional new_rfi⁻¹).
    { arewrite (new_rfi ⊆ new_rf); auto.
      unfold new_rfi; basic_solver. }
    assert (new_rfef : functional new_rfe⁻¹).
    { arewrite (new_rfe ⊆ new_rf); auto.
      unfold new_rfe; basic_solver. }

    assert (tc_coherent G sc TC') as TCCOH'.
    { eapply isim_trav_step_coherence; [ eapply TCCOH | apply TSTEP]. }
    assert (W ∩₁ Rel ∩₁ I' ⊆₁ C') as RELCOV'.
    { eapply sim_trav_step_rel_covered; eauto. red. eauto. }

    assert (new_rfi ≡ ⦗ E0 ⦘ ⨾ new_rfi ⨾ ⦗ E0 ⦘) as NEW_RFIE.
    { split; [|basic_solver].
      etransitivity.
      2: apply doma_helper.
      { unfold new_rfi, new_rf. basic_solver 10. }
      arewrite (new_rfi ⊆ ⦗Tid thread⦘ ⨾ sb). 
      { (*generalize cert_rfi_in_sb.*) 
        etransitivity.
        { apply NEWRFI_IN_CERT. }
        unfold cert_rfi. 
        arewrite (
            cert_rfi G sc TC' thread ⊆ 
            ⦗Tid thread⦘ ⨾ cert_rfi G sc TC' thread ⨾ ⦗Tid thread⦘).
        { unfold cert_rfi. basic_solver. }
        rewrite cert_rfi_in_sb; auto. 
        basic_solver 42. }
      eapply E0_sbprcl; eauto. }
      
    assert (forall r, exists ! w, new_rfe_ex⁻¹ r w) as new_rfe_unique.
    { ins.
      destruct (classic ((codom_rel new_rfe) r)) as [X|X].
      { unfolder in X. 
        destruct X as [w RFE].
        exists w; red; splits.
        unfold new_rfe_ex; basic_solver 12.
        unfold new_rfe_ex; unfolder; ins; desf.
        eapply new_rfef; basic_solver.
        exfalso; eauto. }
      exists r; red; splits.
      unfold new_rfe_ex; basic_solver 12.
      unfold new_rfe_ex; unfolder; ins; desf.
      unfolder in X; exfalso; eauto. }

    assert (exists new_value, forall x, (new_rfe_ex)⁻¹ x (new_value x)) as HH; desc.
    { apply (unique_choice (new_rfe_ex)⁻¹ (new_rfe_unique)). }

    set (get_val (v: option value) :=  match v with | Some v => v | _ => 0 end).
    set (new_val := fun r => get_val (val G.(lab) (new_value r))).

    assert (forall e (IN: acts_set (ProgToExecution.G state'') e),
               lab (ProgToExecution.G state'') e = G.(lab) e) as LST2.
    { ins.
      assert (tid e = thread) as ETT. 
      { eapply acts_rep in IN.
        2: by eapply wf_thread_state_steps; [|by eauto]; eauto.
        desf. }
      erewrite <- steps_preserve_lab; try rewrite ETT; eauto.
      eapply tr_lab; eauto.
      eapply steps_preserve_E; eauto. }

    edestruct steps_old_restrict with (state0:=state'') (state':=state') as [ORMW]; eauto.
    desc. unnw.
    edestruct receptiveness_full with
        (tid:=thread)
        (s_init:=state) (s:=state'')
        (new_val:=new_val)
        (new_rfi:=new_rfi)
        (MOD:=E0 \₁ D) as [pre_cert_state]; eauto.
    { rewrite CACTS. apply NEW_RFIE. }
    { split; [|basic_solver].
      rewrite NEW_RFIE at 1.
      unfolder. intros w r [EEX [RFXY EEY]].
      set (AA := RFXY).
      unfold new_rfi in AA.
      destruct_seq AA as [TX TY].
      unfold new_rf in AA. apply seq_eqv_r in AA. destruct AA as [AA _].
      apply cert_rfD in AA; auto. destruct_seq AA as [WX RY].
      splits; auto; unfold is_w, is_r.
      all: erewrite <- steps_preserve_lab with (state0:=state'') (state':=state'); eauto;
        [ erewrite tr_lab; eauto; eapply E0_in_thread_execE with (TC:=TC); eauto
        | | | by apply CACTS]. 
      1-2: rewrite TX; auto.  
      all: rewrite TY; auto. }
    { rewrite NEWRFI_IN_CERT.
      rewrite cert_rfi_in_sb; auto. 
      unfold Execution.sb. basic_solver. }
    { unfold new_rfi, new_rf. basic_solver. } 
    { rewrite <- CACTS. basic_solver. } 
    { rewrite STATECOV. 
      sin_rewrite sim_trav_step_covered_le.
      2: by red; eauto.
      rewrite <- C_in_D.
      basic_solver. }

    Ltac _ltt thread EE0 TCCOH OC CC CACTS CCD := 
      rewrite OC; rewrite CC;
      rewrite CACTS;
      arewrite_id ⦗Tid thread⦘; arewrite_id ⦗E0⦘ at 1;
      rewrite !seq_id_l;
      (*unfold EE0, thread;*)
      rewrite CCD; [| |apply TCCOH|]; auto;
      basic_solver.
    
    { _ltt thread E0 TCCOH OFAILDEP TEH.(tr_rmw_dep) CACTS dom_rmw_depE_in_D. }
    { _ltt thread E0 TCCOH OADDR TEH.(tr_addr) CACTS dom_addrE_in_D. }
    2: { _ltt thread E0 TCCOH OCTRL TEH.(tr_ctrl) CACTS dom_ctrlE_in_D. }

    { rewrite CACTS.
      arewrite ((E0 \₁ D) ∩₁ E0 ⊆₁ E0 \₁ D) by basic_solver.
      intros e [[EE DE] RE]. red.
      apply DE.
      set (EE':=EE).
      destruct EE' as [TT [AA|AA]].
      { by apply C_in_D. } 
      unfolder in AA. 
      destruct AA as [y [z [[EQx | SB] [EQ Iz]]]]. 
      { rewrite EQx. by apply I_in_D. }
      subst. red. do 2 left. right.
      eexists. eexists. split.
      { by left. }
      apply seq_eqv_r. split; eauto.
      assert (R_ex e) as UU.
      { unfold Events.R_ex. rewrite <- LST2; auto. by apply CACTS. }
      red. apply seq_eqv_l. split.
      { by apply R_ex_in_R. }
      apply seq_eqv_r. split.
      2: by eapply issuedW; eauto.
      apply ct_step. left. right.
      apply seq_eqv_l. split; auto. }

    { rewrite ODATA, CACTS.
      arewrite_id ⦗E0⦘ at 1. rewrite seq_id_l.
      rewrite <- id_inter.
      arewrite (E0 ∩₁ set_compl (E0 \₁ D) ⊆₁ D).
      { unfolder. intros a [AA BB].
        destruct (classic (D a)); auto.
        exfalso. apply BB. desf. }
      rewrite TEH.(tr_data), !seqA. 
      arewrite_id ⦗Tid thread⦘. rewrite !seq_id_l.
      generalize (dom_dataD_in_D). basic_solver 10. }

    desf.

    assert (instrs pre_cert_state = instrs state) as INSTRSS.
    { eapply steps_same_instrs; eauto. }

    edestruct get_stable with (state0:=pre_cert_state) (thread:=thread)
      as [cert_state [CC _]].
    { by rewrite INSTRSS. }
    { eapply transitive_rt; [|by eauto]. by rewrite INSTRSS. }
    desc.
    
    assert (ProgToExecution.G cert_state = ProgToExecution.G pre_cert_state) as SCC.
    { eapply eps_steps_same_G; eauto. }

    assert (acts_set (ProgToExecution.G pre_cert_state) =
            acts_set (ProgToExecution.G state'')) as SS.
    { unfold acts_set. by rewrite RACTS. }

    exists cert_state.
    splits; auto. 
    2 : { eapply transitive_rt; eauto. by apply eps_steps_in_steps. }

    assert (same_lab_u2v (certLab G cert_state) (lab G)) as SU2V.
    { intros e _. unfold certLab.
      unfold restr_fun.
      destruct (excluded_middle_informative
                  (acts_set (ProgToExecution.G cert_state) e))
               as [AA|AA].
      2: { red. desf. }
      rewrite SCC in *.
      eapply same_label_u2v_trans.
      { by apply SAME. }
      rewrite LST2; [by red; desf|].
      red. by rewrite RACTS. }

    assert (eq_dom D (certLab G cert_state) (lab G))
      as CERTLABD.
    { intros e DE. unfold certLab.
      unfold restr_fun.
      destruct (excluded_middle_informative
                  (acts_set (ProgToExecution.G cert_state) e))
               as [CEE|]; auto.
      rewrite SCC in *. rewrite SS in CEE.
      rewrite <- LST2; auto.
      apply same_label_u2v_val; auto.
      apply OLD_VAL. intros [_ ND]. desf. }

    constructor; auto.
    all: try rewrite SCC.
    { red. ins.
      eapply same_label_u2v_trans; eauto.
      assert (tid e = thread) as BB.
      { red in EE. rewrite <- RACTS in EE. by apply CACTS. }
      assert (acts_set (ProgToExecution.G state'') e) as CC.
      { by red; rewrite RACTS. }

      assert (lab (ProgToExecution.G state'') e = G.(lab) e) as AA by (by apply LST2).
      rewrite AA. red. desf. }
    { unfold acts_set. by rewrite <- RACTS. }
    { rewrite <- RRMW, SS. rewrite ORMW, !CACTS.
      rewrite TEH.(tr_rmw), !seqA.
      rewrite seq_eqvC. seq_rewrite <- !id_inter.
      arewrite (E0 ∩₁ Tid thread ≡₁ E0).
      { rewrite set_interC. unfold CertRf.E0. rewrite <- !set_interA. 
          by rewrite set_interK. }
        by erewrite <- E0_rmwsfcl; eauto. }
    { intros w r RF. apply cert_rf_codomE0 in RF.
      destruct_seq_r RF as EER.
      assert (Tid thread r) as TRR by apply EER.
      unfold same_val, val.
      
      destruct (classic (D r)) as [DR|NDR].
      { rewrite CERTLABD with (x:=r); auto.
        assert (rf w r) as RFWR.
        { intros. eapply cert_rf_D_rf with (TC:=TC'); eauto.
          apply seq_eqv_r. do 2 (split; eauto). }
        assert (D w).
        2: { rewrite CERTLABD; auto. apply wf_rfv; auto. }
        eapply rf_E0D_in_D; eauto.
        eexists. apply seq_eqv_r. split; eauto.
        split; [split|]; auto. apply EER. }
      
      unfold certLab at 2.
      set (STE := EER). apply CACTS in STE.
      unfold restr_fun.
      destruct (excluded_middle_informative (acts_set (ProgToExecution.G cert_state) r))
        as [VV|VV].
      2: { exfalso. apply VV. rewrite SCC. red. by rewrite <- RACTS. }
      rewrite SCC.

      set (LL := RF).
      apply cert_rfE in LL; auto. destruct_seq LL as [RE RW].
      apply cert_rfD in LL; auto. destruct_seq LL as [RR WW].

      assert (Tid thread w -> sb w r) as SBWR.
      { intros TTW.
        edestruct same_thread with (x:=r) (y:=w) as [[SB|SB]|SB]; eauto.
        { intros II. eapply init_w in II; eauto.
          clear -WW II. type_solver. }
        { desf. }
        { subst. clear -RR WW. type_solver. }
        exfalso. eapply cert_rf_hb_irr; eauto.
        eexists; split; eauto. by apply sb_in_hb. }

      assert (Tid thread w -> acts_set (ProgToExecution.G cert_state) w) as PP.
      { intros TT. set (AA := TT).
        apply SBWR in AA. rewrite SCC. red. rewrite <- RACTS. apply CACTS.
        eapply E0_sbprcl; eauto. apply seq_eqv_l. split; auto.
        apply seq_eqv_r. split; eauto. }
      
      destruct (classic (codom_rel new_rfi r)) as [DD|DD].
      { set (TT:=DD). destruct TT as [w' TT].
        set (OO := TT). destruct_seq OO as [TTW TTR].
        assert (w' = w); subst.
        { destruct_seq_r OO as QQ. eapply cert_rff; eauto. }
        unfold certLab. unfold restr_fun.
        set (OO' := OO). destruct_seq_r OO' as OOK.
        specialize (PP eq_refl).
        destruct (excluded_middle_informative (acts_set (ProgToExecution.G cert_state) w));
          [|done].
        rewrite SCC.
        symmetry. apply NEW_VAL1. red.
        apply seq_eqv_l. split; auto.
        apply seq_eqv_r. split; auto. }
      
      destruct (classic (Tid thread w)) as [TTW|NTTW].
      { exfalso. apply DD. exists w.
        apply seq_eqv_l. split; auto.
        apply seq_eqv_r. split; auto.
        apply seq_eqv_r. do 2 (split; auto). }

      rewrite CERTLABD.
      2: { red. do 3 left. right. split; auto. }
      
      etransitivity.
      2: { symmetry. apply NEW_VAL2; auto.
           2: by split.
           eapply same_lab_u2v_is_r; eauto. unfold is_r. by rewrite LST2. }
      unfold new_val, get_val, val.
      assert (new_value r = w) as FF.
      2: { rewrite FF; desf. clear -Heq RR. type_solver. }
      assert (new_rfe w r) as RFE.
      { apply seq_eqv_l. split; auto.
        apply seq_eqv_r. split; auto.
        apply seq_eqv_r. repeat (split; auto). }
      specialize (HH r). destruct HH as [HH|HH].
      { eapply new_rfef; eauto. }
      clear -HH RFE. red in HH. desf.
      exfalso. apply HH0. rewrite HH.
      eexists. eauto. }
    { erewrite same_lab_u2v_same_loc; eauto.
      apply cert_rfl. }
    arewrite (cert_rf G sc TC' thread ⊆
                      ⦗issued TC' ∪₁ set_compl (issued TC')⦘ ⨾
                      cert_rf G sc TC' thread) at 1
      by rewrite set_compl_union_id, seq_id_l.
    rewrite id_union, seq_union_l.
    rewrite non_I_cert_rf; auto.
    unionL; [|basic_solver].
    inv TSTEP; simpls. 

    3: assert (tid r = tid w) as TR by (eapply wf_rmwt; eauto).

    all: assert (~ is_init w) as NINITX
        by (intros AA; destruct w; simpls; desf;
            rewrite <- TX in *; desf).
    
    all: rewrite id_union, seq_union_l; unionL; [basic_solver|].
    all: unionR right.
    all: unfolder; intros a b [AA RF]; desf.
    
    3: rewrite TR in RF.
    all: assert (tid b = tid a) as TB
        by (apply cert_rf_codomt in RF; generalize RF; basic_solver).

    all: apply cert_rfD in RF; auto; destruct_seq RF as [WX RY].
    all: apply cert_rfE in RF; auto; destruct_seq RF as [EX EY].
    all: destruct (@same_thread G a b) as [[|SB]|SB]; desf; auto. 
    1,3,5: type_solver.
    all: exfalso.
    all: eapply cert_rf_hb_sc_hb_irr; eauto.
    all: assert (hb b a) as HB by (apply imm_s_hb.sb_in_hb; auto).
    all: repeat (eexists; split; eauto).
Qed.

(******************************************************************************)
(** ** ilbl_step lemmas *)
(******************************************************************************)

Lemma ilbl_step_E0_eindex lbls
        (st st' st'' : Language.Language.state (PromiseLTS.thread_lts thread))
        (WFT : wf_thread_state thread st) 
        (CG : cert_graph G sc TC TC' thread st'')
        (ILBL_STEP : ilbl_step thread lbls st st')
        (CST_REACHABLE : (lbl_step thread)＊ st' st'') : 
  E0 (ThreadEvent thread st.(eindex)).
Proof. 
  eapply dcertE; [apply CG|].
  eapply preserve_event.
  { eapply lbl_steps_in_steps; eauto. }
  edestruct ilbl_step_cases as [l [l' HH]]; eauto. 
  desf; apply ACTS; basic_solver.
Qed.

Lemma ilbl_step_E0_eindex' lbls lbl lbl'
        (st st' st'' : Language.Language.state (PromiseLTS.thread_lts thread))
        (WFT : wf_thread_state thread st) 
        (CG : cert_graph G sc TC TC' thread st'')
        (ILBL_STEP : ilbl_step thread lbls st st')
        (LBLS_EQ : lbls = opt_to_list lbl' ++ [lbl])
        (LBL' : lbl' <> None)
        (CST_REACHABLE : (lbl_step thread)＊ st' st'') : 
  E0 (ThreadEvent thread (1 + st.(eindex))).
Proof. 
  eapply dcertE; [apply CG|].
  eapply preserve_event.
  { eapply lbl_steps_in_steps; eauto. }
  edestruct ilbl_step_cases as [l [l' HH]]; eauto. 
  desf. 
  1-4 : apply opt_to_list_app_singl in LBLS; intuition.
  desf; apply ACTS; basic_solver.
Qed.

(* Lemma ilbl_step_cert_dom_eindex lbls *)
(*         (st st' st'' : Language.Language.state (Promise.thread_lts thread)) *)
(*         (WFT : wf_thread_state thread st)  *)
(*         (CG : cert_graph G sc TC TC' thread st'') *)
(*         (ILBL_STEP : ilbl_step thread lbls st st') *)
(*         (CST_REACHABLE : (lbl_step thread)＊ st' st'') :  *)
(*   cert_dom st' ≡₁ cert_dom st ∪  *)
(*            eq (ThreadEvent thread st.(eindex)) ∪₁ eq (ThreadEvent thread (1 + st.(eindex))) *)
(*   E0 (ThreadEvent thread st.(eindex)). *)

End CertGraphLemmas.
