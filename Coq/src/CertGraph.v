Require Import Omega.
Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution
     Traversal TraversalConfig SimTraversal SimTraversalProperties
     Prog ProgToExecution ProgToExecutionProperties Receptiveness
     imm_common imm_s imm_s_hb SimulationRel
     CertExecution2 CertExecutionMain
     SubExecution CombRelations AuxRel.
Require Import AuxRel AuxDef EventStructure LblStep CertRf.
Require Import Coq.Logic.FunctionalExtensionality Classical_Prop.

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

  Definition certLab (e : actid) : label :=
    if excluded_middle_informative (certE e)
    then certG.(lab) e
    else G.(lab) e.

  Notation "'certRmw'" := (certG.(rmw)).

  Notation "'new_rf'" := (cert_rf G sc TC' thread).

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

  (* Notation "'E0'" := (E0 G TC' thread).  *)
  (* Notation "'D'" := (D G TC' thread). *)
  
  Notation "'E0'" := (Tid_ thread ∩₁ (C' ∪₁ dom_rel (sb^? ⨾ ⦗ I' ⦘))).
  Notation "'D'" := (D G TC' thread).

  Record cert_graph :=
    { cslab : eq_dom ((Tid_ thread) ∩₁ (C' ∪₁ I')) certLab G.(lab);
      cuplab_cert : forall e (EE : certE e),
          same_label_up_to_value (certG.(lab) e) (G.(lab) e);
      
      dcertE : certE ≡₁ E0;
      dcertRMW : certRmw ≡ ⦗ certE ⦘ ⨾ rmw ⨾ ⦗ certE ⦘;
      
      new_rfv : new_rf ⊆ same_val certLab;
      new_rfl : new_rf ⊆ same_loc certLab;
      new_rf_iss_sb : new_rf ⊆ ⦗ I ⦘ ⨾ new_rf ∪ sb;

      oval : eq_dom D (val certLab) (val G.(lab));
    }.

  Section CertGraphProperties.
    Variable WF : Wf G.
    Variable Wf_sc : wf_sc G sc.
    Variable IMMC : imm_consistent G sc.
    Variable TCCOH : tc_coherent G sc TC.
    Variable TSTEP : isim_trav_step G sc thread TC TC'.

    Fact TCCOH' : tc_coherent G sc TC'.
    Proof. 
      eapply sim_trav_step_coherence; red; eauto.
    Qed.

    Hint Resolve TCCOH'. 

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

    (* Lemma E0_eq_certE  *)
    (*       (TEH : thread_restricted_execution G thread certG)  *)
    (*       (CDOM : certE ⊆₁ C) :  *)
    (*   E0 ≡₁ certE. *)
    (* Proof.  *)
    (*   red. split.  *)
    (*   { (* E0_in_e in CertRF ? *) *)
    (*     rewrite tr_acts_set; eauto. *)
    (*     rewrite set_interC. *)
    (*     apply set_subset_inter; auto. *)
    (*     rewrite coveredE; eauto. *)
    (*     rewrite issuedE; eauto. *)
    (*     rewrite wf_sbE. *)
    (*     basic_solver. } *)
    (*   apply set_subset_inter_r. split. *)
    (*   { etransitivity.  *)
    (*     { eapply TEH.(tr_acts_set). }         *)
    (*     basic_solver. } *)
    (*   unionR left. *)
    (*   etransitivity; eauto.   *)
    (*   eapply sim_trav_step_covered_le. red. eauto.  *)
    (* Qed. *)

    Lemma E0_eq_certE 
          (TEH : thread_restricted_execution G thread certG) :
      E0 ⊆₁ certE.
    Proof. 
      rewrite tr_acts_set; eauto.
      rewrite set_interC.
      apply set_subset_inter; auto.
      rewrite coveredE; eauto.
      rewrite issuedE; eauto.
      rewrite wf_sbE.
      basic_solver.
    Qed.

    (* Lemma E0_in_E : E0 ⊆₁ E. *)
    (* Proof.  *)
    (*   rewrite TCCOH'.(coveredE). *)
    (*   rewrite TCCOH'.(issuedE). *)
    (*   rewrite wf_sbE. basic_solver.  *)
    (* Qed. *)

    Lemma E0_eindex_weak e (CTE : E0 e) (NINITT : thread <> tid_init) : 
      exists index : nat,
        ⟪ EREP : e = ThreadEvent thread index ⟫.
    Proof. 
      ins. destruct CTE as [AA BB].
      destruct e; simpls; rewrite <- AA in *; desf.
      eauto. 
    Qed.

    Lemma E0_eindex 
          (NINITT : thread <> tid_init)
          (GPC : wf_thread_state thread state)
          (TEH : thread_restricted_execution G thread certG) : 
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
      assert (Tid_ thread max) as CTTID by apply CTMAX.
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
        assert (certE (ThreadEvent thread mindex)) as PP.
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
        { apply TCCOH' in AA. apply AA. eexists.
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

    Lemma cuplab e (SCG : cert_graph) :
      same_label_up_to_value (certLab e) (G.(lab) e).
    Proof.
      unfold certLab. desf.
      { by apply SCG. }
      red. desf.
    Qed.

    Lemma new_rf_w (SCG : cert_graph) : 
      new_rf ≡ ⦗ W ⦘ ⨾ new_rf.
    Proof. rewrite cert_rfD. basic_solver. Qed.

    Lemma new_rf_ntid_iss_sb 
          (SCG : cert_graph)
          (IRELCOV : W ∩₁ Rel ∩₁ I ⊆₁ C) :
      new_rf ⊆ ⦗ NTid_ thread ∩₁ I ⦘ ⨾ new_rf ∪ sb.
    Proof.
      etransitivity.
      { apply cert_rf_ntid_sb; auto. 
        eapply sim_trav_step_rel_covered; eauto. 
        eexists; eauto. }
      sin_rewrite new_rf_iss_sb; auto. 
      basic_solver 10.
    Qed.

    Lemma dom_addrE_in_D : dom_rel (addr ⨾ ⦗ E0 ⦘) ⊆₁ D.
    Proof.
      rewrite set_inter_union_r.
      rewrite id_union; relsf; unionL; splits.
      { rewrite (addr_in_sb WF).
        generalize (dom_sb_covered TCCOH').
        unfold CertExecution2.D; basic_solver 21. }
      arewrite (Tid_ thread ∩₁ dom_rel (sb^? ⨾ ⦗I'⦘) ⊆₁
                      dom_rel (sb^? ⨾ ⦗I'⦘)) by basic_solver.
      rewrite dom_rel_eqv_dom_rel.
      arewrite (⦗I'⦘ ⊆ ⦗W⦘ ⨾ ⦗I'⦘).
      { generalize (issuedW TCCOH'); basic_solver. }
      rewrite (dom_l (wf_addrD WF)), !seqA.
      arewrite (⦗R⦘ ⨾ addr ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppo).
      { unfold imm_common.ppo; rewrite <- ct_step; basic_solver 12. }
      unfold CertExecution2.D; basic_solver 21.
    Qed.

    Lemma dom_ctrlE_in_D : dom_rel (ctrl ⨾ ⦗ E0 ⦘) ⊆₁ D.
    Proof.
      rewrite set_inter_union_r.
      rewrite id_union; relsf; unionL; splits.
      { rewrite (ctrl_in_sb WF).
        generalize (dom_sb_covered TCCOH').
        unfold CertExecution2.D; basic_solver 21. }
      arewrite (Tid_ thread ∩₁ dom_rel (sb^? ⨾ ⦗I'⦘) ⊆₁
                      dom_rel (sb^? ⨾ ⦗I'⦘)) by basic_solver.
      rewrite dom_rel_eqv_dom_rel.
      arewrite (ctrl ⨾ sb^? ⊆ ctrl).
      { generalize (ctrl_sb WF); basic_solver 21. }
      arewrite (⦗I'⦘ ⊆ ⦗W⦘ ⨾ ⦗I'⦘).
      { generalize (issuedW TCCOH'); basic_solver. }
      rewrite (wf_ctrlD WF), !seqA.
      arewrite (⦗R⦘ ⨾ ctrl ⨾ ⦗W⦘ ⊆ ppo).
      { unfold imm_common.ppo; rewrite <- ct_step; basic_solver 12. }
      unfold CertExecution2.D; basic_solver 21.
    Qed.

    Lemma dom_rmw_depE_in_D : dom_rel (rmw_dep ⨾ ⦗ E0 ⦘) ⊆₁ D.
    Proof.
      rewrite set_inter_union_r.
      rewrite id_union; relsf; unionL; splits.
      { rewrite (rmw_dep_in_sb WF).
        generalize (dom_sb_covered TCCOH').
        unfold CertExecution2.D; basic_solver 21. }
      arewrite (Tid_ thread ∩₁ dom_rel (sb^? ⨾ ⦗I'⦘) ⊆₁
                      dom_rel (sb^? ⨾ ⦗I'⦘)) by basic_solver.
      rewrite dom_rel_eqv_dom_rel.
      rewrite (wf_rmw_depD WF), !seqA.
      arewrite (⦗I'⦘ ⊆ ⦗W⦘ ⨾ ⦗I'⦘).
      { generalize (issuedW TCCOH'); basic_solver. }
      arewrite (⦗R⦘ ⨾ rmw_dep ⨾ ⦗R_ex⦘ ⨾ sb^? ⨾ ⦗W⦘ ⊆ ppo).
      2: unfold CertExecution2.D; basic_solver 21.
      unfold imm_common.ppo; hahn_frame.
      case_refl _.
      { by rewrite <- ct_step; basic_solver 12. }
      rewrite ct_begin; rewrite <- inclusion_t_rt, <- ct_step; basic_solver 12.
    Qed.

    Lemma dom_rmwE_in_D : dom_rel (rmw ⨾ ⦗ E0 ⦘) ⊆₁ D.
    Proof.
      rewrite set_inter_union_r.
      rewrite id_union; relsf; unionL; splits.
      { rewrite (rmw_in_sb WF).
        generalize (dom_sb_covered TCCOH').
        unfold CertExecution2.D; basic_solver 21. }
      arewrite (Tid_ thread ∩₁ dom_rel (sb^? ⨾ ⦗I'⦘) ⊆₁
                      dom_rel (sb^? ⨾ ⦗I'⦘)) by basic_solver.
      rewrite dom_rel_eqv_dom_rel.
      arewrite (⦗I'⦘ ⊆ ⦗W⦘ ⨾ ⦗I'⦘).
      { generalize (issuedW TCCOH'); basic_solver. }
      generalize (rmw_in_ppo WF) (rmw_sb_W_in_ppo WF).
      unfold CertExecution2.D; basic_solver 21.
    Qed.

    Lemma dom_dataD_in_D : dom_rel (data ⨾ ⦗D⦘) ⊆₁ D.
    Proof.
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
        arewrite (dom_rel (⦗D⦘ ⨾ sb ⨾ ⦗E ∩₁ NTid_ thread⦘) ⊆₁ D) by basic_solver.
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

Variable WF : Wf G.
Variable Wf_sc : wf_sc G sc.
Variable IMMC : imm_consistent G sc.
Variable TCCOH : tc_coherent G sc TC.
Variable TSTEP : isim_trav_step G sc thread TC TC'.

Hint Resolve TCCOH'. 

Lemma sim_cert_graph_start 
      (state : Language.Language.state (Promise.thread_lts thread))
      (NINITT : thread <> tid_init)
      (GPC : wf_thread_state thread state)
      (SSTATE : sim_state G sim_normal C state)
      (STATECOV : acts_set state.(ProgToExecution.G) ⊆₁ C) :
  exists state', cert_graph G sc TC TC' thread state'.
Proof. 
    cdes SSTATE. cdes SSTATE1.

    assert (wf_thread_state thread state') as GPC'.
    { eapply wf_thread_state_steps; eauto. }

    assert (forall r w, rmw r w -> covered TC' r <-> covered TC' w) as RMWCOV.
    { eapply sim_trav_step_rmw_covered; eauto.
      { red. eauto. }
      admit. }

    edestruct E0_eindex; eauto; desf. 
    edestruct steps_middle_set with
      (thread := thread)
      (state0 := state) (state':=state') as [state''].
    3: { eapply E0_eq_certE; eauto. }
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
    set (new_rfi := ⦗ Tid_ thread ⦘ ⨾ new_rf ⨾ ⦗ Tid_ thread ⦘).
    set (new_rfe := ⦗ NTid_ thread ⦘ ⨾ new_rf ⨾ ⦗ Tid_ thread ⦘).
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

    edestruct steps_old_restrict with (state0:=state'') (state':=state') as [ORMW]; eauto.
    desc. unnw.
    edestruct receptiveness_full with
        (tid:=thread)
        (s_init:=state) (s:=state'')
        (new_val:=new_val)
        (new_rfi:=new_rfi)
        (MOD:=E0 \₁ D) as [pre_cert_state]; eauto.
    { red. split; [|basic_solver].  
      unfold new_rfi, new_rf.
      rewrite CACTS. 
      arewrite (
          ⦗Tid_ thread⦘ ⨾ (cert_rf G sc TC' thread ⨾ ⦗E0 \₁ D⦘) ⨾ ⦗Tid_ thread⦘ ≡ 
           (cert_rfi G sc TC' thread ⨾ ⦗E0⦘) ⨾ ⦗E0 \₁ D⦘) at 1.
      { unfold cert_rfi. basic_solver 42. }
      arewrite (
          ⦗E0⦘ ⨾ ⦗Tid_ thread⦘ ⨾ cert_rf G sc TC' thread ⨾ ⦗E0 \₁ D⦘ ⨾ ⦗Tid_ thread⦘ ⨾ ⦗E0⦘ ≡
          ⦗E0⦘ ⨾ cert_rfi G sc TC' thread ⨾ ⦗E0⦘ ⨾ ⦗E0 \₁ D⦘). 
      { unfold cert_rfi. basic_solver 42. }
      rewrite <- seqA.
      rewrite cert_rfi_in_E0; eauto.  
      basic_solver 10.  
      admit. }
      
    all: admit. 
    
    (* { red. split; [|basic_solver].  *)
    (*   unfold new_rfi, new_rf.  *)
      
      
    (*   apply cert_rfi_in_E0. *)
    (* { by rewrite CACTS. } *)
    (* { split; [|basic_solver]. *)
    (*   rewrite NEW_RFIE at 1. *)
    (*   unfolder. intros x y [EEX [RFXY EEY]]. *)
    (*   set (AA := RFXY). *)
    (*   unfold new_rfi in AA. *)
    (*   destruct_seq AA as [TX TY]. *)
    (*   unfold new_rf in AA. apply seq_eqv_r in AA. destruct AA as [AA _]. *)
    (*   apply cert_rfD in AA. destruct_seq AA as [WX RY]. *)
    (*   splits; auto; unfold is_w, is_r. *)
    (*   all: erewrite <- steps_preserve_lab with (state0:=state'') (state':=state'); eauto; *)
    (*     [by erewrite tr_lab; eauto | | | by apply CACTS]. *)
    (*   3,4: by rewrite TY; eauto. *)
    (*   all: by rewrite TX; eauto. } *)
    (* { rewrite NEWRFISB. unfold Execution.sb. basic_solver. } *)
    (* { unfold new_rfi, new_rf. basic_solver. } *)
    (* { rewrite <- CACTS. basic_solver. } *)
    (* { rewrite STATECOV. *)
    (*   sin_rewrite sim_trav_step_covered_le. *)
    (*   2: by red; eauto. *)
    (*   rewrite <- C_in_D. *)
    (*   basic_solver. } *)
    

    
  
Admitted.

End CertGraphLemmas.