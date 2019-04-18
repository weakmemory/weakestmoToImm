Require Import Program.Basics Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     SimTraversal SimTraversalProperties
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CombRelations SimTraversal SimulationRel AuxRel.
Require Import AuxRel.
Require Import AuxDef.
Require Import EventStructure.
Require Import Consistency.
Require Import BasicStep.
Require Import CertRf.
Require Import CertGraph.
Require Import EventToAction.
Require Import LblStep.
Require Import SimRelCont.
Require Import ProgES.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelEventToAction.
  Variable S : ES.t.
  Variable G : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Hypothesis WFsc : wf_sc G sc.

  Notation "'SE'" := S.(ES.acts_set).
  Notation "'SEinit'" := S.(ES.acts_init_set).
  Notation "'SEninit'" := S.(ES.acts_ninit_set).

  Notation "'Stid'" := (S.(ES.tid)).
  Notation "'Slab'" := (ES.lab S).
  Notation "'Sloc'" := (loc S.(ES.lab)).

  Notation "'K'" := S.(ES.cont_set).

  Notation "'STid' t" := (fun x => Stid x = t) (at level 1).

  Notation "'SR'" := (fun a => is_true (is_r Slab a)).
  Notation "'SW'" := (fun a => is_true (is_w Slab a)).
  Notation "'SF'" := (fun a => is_true (is_f Slab a)).

  Notation "'SRel'" := (fun a => is_true (is_rel Slab a)).
  Notation "'SAcq'" := (fun a => is_true (is_acq Slab a)).

  Notation "'Ssb'" := (S.(ES.sb)).
  Notation "'Scf'" := (S.(ES.cf)).
  Notation "'Srmw'" := (S.(ES.rmw)).
  Notation "'Sjf'" := (S.(ES.jf)).
  Notation "'Sjfi'" := (S.(ES.jfi)).
  Notation "'Sjfe'" := (S.(ES.jfe)).
  Notation "'Srf'" := (S.(ES.rf)).
  Notation "'Srfi'" := (S.(ES.rfi)).
  Notation "'Srfe'" := (S.(ES.rfe)).
  Notation "'Sco'" := (S.(ES.co)).
  Notation "'Sew'" := (S.(ES.ew)).

  Notation "'Srs'" := (S.(Consistency.rs)).
  Notation "'Srelease'" := (S.(Consistency.release)).
  Notation "'Ssw'" := (S.(Consistency.sw)).
  Notation "'Shb'" := (S.(Consistency.hb)).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).

  Notation "'Glab'" := (Execution.lab G).
  Notation "'Gloc'" := (Events.loc (lab G)).
  Notation "'Gtid'" := (Events.tid).

  Notation "'GTid' t" := (fun x => Gtid x = t) (at level 1).
  Notation "'GNTid' t" := (fun x => Gtid x <> t) (at level 1).

  Notation "'GR'" := (fun a => is_true (is_r Glab a)).
  Notation "'GW'" := (fun a => is_true (is_w Glab a)).
  Notation "'GF'" := (fun a => is_true (is_f Glab a)).

  Notation "'GRel'" := (fun a => is_true (is_rel Glab a)).
  Notation "'GAcq'" := (fun a => is_true (is_acq Glab a)).

  Notation "'Gsb'" := (Execution.sb G).
  Notation "'Grmw'" := (Execution.rmw G).
  Notation "'Grf'" := (Execution.rf G).
  Notation "'Gco'" := (Execution.co G).

  Notation "'Grs'" := (imm_s_hb.rs G).
  Notation "'Grelease'" := (imm_s_hb.release G).
  Notation "'Gsw'" := (imm_s_hb.sw G).
  Notation "'Ghb'" := (imm_s_hb.hb G).
  
  Notation "'Gfurr'" := (furr G sc).

  Notation "'C'" := (covered TC).
  Notation "'I'" := (issued TC).

  Notation "'e2a'" := (e2a S).

  Notation "'thread_syntax' t"  := 
    (Language.syntax (thread_lts t)) (at level 10, only parsing).  

  Notation "'thread_st' t" := 
    (Language.state (thread_lts t)) (at level 10, only parsing).

  Notation "'thread_init_st' t" := 
    (Language.init (thread_lts t)) (at level 10, only parsing).

  Notation "'thread_cont_st' t" :=
    (fun st => existT _ (thread_lts t) st) (at level 10, only parsing).

  Notation "'cont_lang'" :=
    (fun S k => thread_lts (ES.cont_thread S k)) (at level 10, only parsing).

  Notation "'kE' k" := (ES.cont_sb_dom S k) (at level 1, only parsing).
  Notation "'ktid' k" := (ES.cont_thread S k) (at level 1, only parsing).

  Record simrel_e2a := 
    { e2a_GE : e2a □₁ SE ⊆₁ GE;
      e2a_GEinit : GEinit ⊆₁ e2a □₁ SEinit;

      e2a_lab : same_lab_u2v_dom SE Slab (Glab ∘ e2a);

      e2a_rmw : e2a □ Srmw ⊆ Grmw;
      e2a_ew  : e2a □ Sew  ⊆ eq;
      e2a_co  : e2a □ Sco  ⊆ Gco;

      e2a_jf  : e2a □ Sjf  ⊆ Gfurr;
      e2a_jfrmw : e2a □ (Sjf ⨾ Srmw) ⊆ Grf ⨾ Grmw;
    }.

  Section SimRelEventToActionProps. 
    Variable prog : Prog.t.
    Variable GPROG : program_execution prog G.
    Variable PROG_NINIT : ~ (IdentMap.In tid_init prog).
    Variable WF : ES.Wf S.
    Variable SRK : simrel_cont prog S G TC.
    Variable SRE2A : simrel_e2a.

    Lemma e2a_same_Einit : 
      e2a □₁ SEinit ≡₁ GEinit.
    Proof. 
      split. 
      { eapply e2a_Einit; eauto. apply SRE2A. }
      unfold ES.acts_ninit_set, ES.acts_init_set, ES.acts_set. 
      unfolder. intros a [INITa GEa].
      edestruct e2a_GEinit as [e [[INITe SEe] gEQ]].
      
      1-2 : unfolder; eauto.  
      eexists; splits; eauto. 
    Qed.

    Ltac e2a_type t :=
      intros x [y HH]; desf;
      eapply t in HH;
        [|by apply same_lab_u2v_dom_comm; apply SRE2A];
      split; [apply SRE2A.(e2a_GE); red; eexists; split; eauto|]; apply HH.
    
    Lemma e2a_R : e2a □₁ (SE ∩₁ SR) ⊆₁ GE ∩₁ GR.
    Proof. e2a_type same_lab_u2v_dom_is_r. Qed.
    
    Lemma e2a_W : e2a □₁ (SE ∩₁ SW) ⊆₁ GE ∩₁ GW.
    Proof. e2a_type same_lab_u2v_dom_is_w. Qed.

    Lemma e2a_F : e2a □₁ (SE ∩₁ SF) ⊆₁ GE ∩₁ GF.
    Proof. e2a_type same_lab_u2v_dom_is_f. Qed.

    Lemma e2a_Rel : e2a □₁ (SE ∩₁ SRel) ⊆₁ GE ∩₁ GRel.
    Proof. e2a_type same_lab_u2v_dom_is_rel. Qed.

    Lemma e2a_Acq : e2a □₁ (SE ∩₁ SAcq) ⊆₁ GE ∩₁ GAcq.
    Proof. e2a_type same_lab_u2v_dom_is_acq. Qed.

    Lemma e2a_same_loc : 
      e2a □ restr_rel SE (Events.same_loc Slab) ⊆ restr_rel GE (Events.same_loc Glab).
    Proof.
      intros x y HH. red in HH. desf.
      eapply same_lab_u2v_dom_same_loc in HH.
      2: { apply same_lab_u2v_dom_comm. apply SRE2A. }
      red in HH. desf. 
      red. splits.
      apply HH.
      all: by eapply e2a_GE; eauto; eexists; eauto.
    Qed.
    
    Lemma e2a_rf : e2a □ Srf ≡ e2a □ Sjf.
    Proof.
      destruct SRE2A.
      split.
      2: by rewrite ES.jf_in_rf; eauto.
      unfold ES.rf.
      rewrite inclusion_minus_rel.
      unfolder.
      ins. desf.
      eexists. eexists. splits; eauto.
      eapply e2a_ew; auto. 
      eexists. eexists.
      splits.
      { eapply ES.ew_sym; eauto. }
      all: by eauto.
    Qed.

    Lemma e2a_rs : e2a □ Srs ⊆ Grs. 
    Proof. 
      rewrite rs_alt; auto.
      rewrite !collect_rel_seqi.
      rewrite !collect_rel_eqv.
      rewrite !e2a_W; eauto.
      repeat apply seq_mori; eauto with hahn.
      2: { rewrite collect_rel_crt.
           eauto using clos_refl_trans_mori, e2a_jfrmw. }
      rewrite ES.sbE; auto.
      rewrite wf_sbE.
      rewrite <- !restr_relE.
      rewrite <- restr_inter_absorb_r.
      rewrite <- restr_inter_absorb_r 
        with (r':=same_loc S).
      rewrite collect_rel_cr.
      rewrite collect_rel_interi. 
      apply clos_refl_mori, inter_rel_mori. 
      2: by eapply e2a_same_loc; eauto.
      rewrite !restr_relE, <- wf_sbE, <- ES.sbE; auto.
      eapply e2a_sb; eauto; apply SRE2A.
    Qed.

    Lemma e2a_release : e2a □ Srelease ⊆ Grelease.
    Proof. 
      rewrite release_alt; auto.
      rewrite !collect_rel_seqi, !collect_rel_cr, !collect_rel_seqi.
      rewrite !collect_rel_eqv.
      arewrite (SE ∩₁ (SF ∪₁ SW) ⊆₁ SE) by basic_solver.
      rewrite e2a_Rel, e2a_rs, e2a_sb, e2a_F.
      { unfold imm_s_hb.release. basic_solver 10. }
      all: eauto; apply SRE2A.
    Qed.

    Lemma e2a_jfacq : e2a □ Sjf ⨾ (Ssb ⨾ ⦗SF⦘)^? ⨾ ⦗SAcq⦘ ⊆
                      Grf ⨾ (Gsb ⨾ ⦗GF⦘)^? ⨾ ⦗GAcq⦘.
    Proof.
      inv SRE2A.
      arewrite (Ssb ⨾ ⦗SF⦘ ⊆ Ssb ⨾ ⦗SE∩₁SF⦘).
      { rewrite (dom_r WF.(ES.sbE)) at 1. basic_solver 10. }
      arewrite (Sjf ⨾ (Ssb ⨾ ⦗SE ∩₁ SF⦘)^? ⨾ ⦗SAcq⦘ ⊆
                Sjf ⨾ (Ssb ⨾ ⦗SE ∩₁ SF⦘)^? ⨾ ⦗SE∩₁SAcq⦘).
      { rewrite (dom_r WF.(ES.jfE)) at 1. basic_solver 10. }
      (* arewrite (Sjf ⨾ (Ssb ⨾ ⦗SE ∩₁ SF⦘)^? ⨾ ⦗SE ∩₁ SAcq⦘ ⊆ *)
      (*           Sjf ⨾ ⦗DR⦘ ⨾ (Ssb ⨾ ⦗SE ∩₁ SF⦘)^? ⨾ ⦗SE ∩₁ SAcq⦘). *)
      (* 2: { rewrite <- !seqA. *)
      (*      do 2 rewrite collect_rel_seqi. *)
      (*      rewrite e2a_jfDR; auto. *)
      (*      rewrite !collect_rel_cr, !collect_rel_seqi, !collect_rel_eqv. *)
      (*      rewrite e2a_sb; eauto; try apply SRC. *)
      (*      rewrite e2a_F, e2a_Acq; eauto; try apply SRC. *)
      (*      arewrite (GE ∩₁ GF ⊆₁ GF) by basic_solver. *)
      (*      arewrite (GE ∩₁ GAcq ⊆₁ GAcq) by basic_solver. } *)
      (* rewrite crE. rewrite !seq_union_l, !seq_union_r, !seq_id_l. *)
      (* apply union_mori. *)
      (* { rewrite (dom_r WF.(ES.jfD)) at 1. *)
      (*   rewrite !seqA. *)
      (*   arewrite (⦗SR⦘ ⨾ ⦗SE ∩₁ SAcq⦘ ⊆ ⦗SR ∩₁ SE ∩₁ SAcq⦘ ⨾ ⦗SE ∩₁ SAcq⦘) *)
      (*     by basic_solver. *)
      (*   arewrite (SR ∩₁ SE ∩₁ SAcq ⊆₁ DR). *)
      (*   2: done. *)
      (*   unfold SimRelJF.DR. *)
      (*   basic_solver 10. } *)
      (* rewrite (dom_r WF.(ES.jfD)) at 1. *)
      (* rewrite !seqA. *)
      (* arewrite (Ssb ⨾ ⦗SE ∩₁ SF⦘ ⊆ ⦗X ∩₁ e2a ⋄₁ C⦘ ⨾ Ssb ⨾ ⦗SE ∩₁ SF⦘). *)
      (* 2: { arewrite (⦗SR⦘ ⨾ ⦗X ∩₁ e2a ⋄₁ C⦘ ⊆ ⦗DR⦘). *)
      (*      2: done. *)
      (*      unfold SimRelJF.DR. basic_solver 10. } *)
    Admitted.

    Lemma e2a_hb : e2a □ Shb ⊆ Ghb.
    Proof. 
      unfold hb, imm_s_hb.hb.
      rewrite collect_rel_ct.
      apply clos_trans_mori.
      rewrite collect_rel_union.
      apply union_mori.
      { eapply e2a_sb; eauto; apply SRE2A. }
      unfold Consistency.sw.
      rewrite collect_rel_seqi.
      rewrite e2a_release. by rewrite e2a_jfacq.
    Qed.

    Lemma e2a_kE_ninit k (st : thread_st (ktid k))
          (INK : K S (k, thread_cont_st (ktid k) st)) :
      e2a □₁ (kE k \₁ SEinit) ≡₁ acts_set st.(ProgToExecution.G).
    Proof. 
      assert (wf_thread_state (ktid k) st) as WFT.
      { eapply contwf; eauto. }
      ins. 
      symmetry. split.
      { unfold acts_set. intros a ACT.
        eapply acts_rep in ACT; eauto. 
        desf. unfolder. unfold ES.cont_sb_dom.
        edestruct k eqn:kEQ.
        { erewrite continit in LE; eauto; omega. }
        assert (Stid eid <> tid_init) as NINITeid.
        { red. ins. eapply ES.init_tid_K; eauto. }
        erewrite contseqn in LE; eauto. 
        apply lt_n_Sm_le, le_lt_or_eq in LE.
        destruct LE as [LT | EQ]. 
        { edestruct ES.seqn_pred; eauto. 
          { eapply ES.K_inEninit; eauto. }
          desf.
          assert (Stid x <> tid_init) as NINITx.
          { red. ins. congruence. }
          exists x; splits. 
          { unfold ES.cont_sb_dom. unfolder. eauto 10. }
          { unfold ES.acts_init_set. unfolder. intuition. }
          unfold ES.cont_thread, EventToAction.e2a. 
          destruct 
            (excluded_middle_informative (Stid x = tid_init))
            as [TIDi | nTIDi];
          [intuition | congruence]. }
        exists eid; splits.
        { unfold ES.cont_sb_dom. basic_solver 10. }
        { unfold ES.acts_init_set. unfolder. intuition. }
        unfold ES.cont_thread, EventToAction.e2a. 
        destruct 
          (excluded_middle_informative (Stid eid = tid_init))
          as [TIDi | nTIDi];
          [intuition | congruence]. }
      unfolder. intros a [e [[SB NINIT] gEQ]]. 
      edestruct k eqn:kEQ.
      { unfold ES.cont_sb_dom, ES.acts_init_set in *. exfalso. auto. }
      rewrite <- gEQ.
      erewrite e2a_ninit; auto. 
      2 : { unfold ES.acts_ninit_set. 
            unfolder; split; auto. 
            eapply ES.cont_sb_domE; eauto. }
      assert (ES.same_tid S e eid) as STID.
      { unfold ES.cont_sb_dom in SB.
        unfolder in SB. desf.
        apply ES.sb_Einit_Eninit in SB; auto.
        destruct SB as [AA | BB].
        { unfolder in AA. intuition. }
        apply ES.sb_tid; auto. generalize BB. basic_solver. }
      unfold acts_set. eapply acts_clos. 
      { arewrite (Stid e = Stid eid).
        arewrite (Stid eid = ktid (CEvent eid)).
        eapply contwf; eauto. }
      unfold ES.cont_sb_dom in SB.
      unfolder in SB. 
      destruct SB as [y [z [[EQe | SBez] [EQzy EQeid]]]].
      { subst e y z. erewrite contseqn; eauto. }
      subst z y. etransitivity. 
      { eapply ES.seqn_sb_alt; eauto. }
      erewrite contseqn; eauto.
    Qed.

    Lemma e2a_kE k (st : thread_st (ktid k))
          (INK : K S (k, thread_cont_st (ktid k) st)) :
      e2a □₁ kE k ≡₁ GEinit ∪₁ acts_set st.(ProgToExecution.G).
    Proof.
      assert (wf_thread_state (ktid k) st) as WFT.
      { eapply contwf; eauto. }
      ins. 
      erewrite set_union_minus
        with (s := ES.cont_sb_dom S k) (s' := SEinit).
      2 : eapply ES.cont_sb_dom_Einit; eauto.
      rewrite set_unionC, set_collect_union.
      apply set_union_Propere.
      { apply e2a_same_Einit. }
      by apply e2a_kE_ninit.
    Qed.

  End SimRelEventToActionProps. 

End SimRelEventToAction.

Section SimRelEventToActionLemmas.

  Variable prog : Prog.t.
  Variable PROG_NINIT : ~ (IdentMap.In tid_init prog).
  Variable S : ES.t.
  Variable G : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable GPROG : program_execution prog G.
  Variable WF : ES.Wf S.

  Notation "'SE' S" := S.(ES.acts_set) (at level 10).
  Notation "'SEinit' S" := S.(ES.acts_init_set) (at level 10).
  Notation "'SEninit' S" := S.(ES.acts_ninit_set) (at level 10).

  Notation "'Stid' S" := (S.(ES.tid)) (at level 10).
  Notation "'Slab' S" := (S.(ES.lab)) (at level 10).
  Notation "'Sloc' S" := (loc S.(ES.lab)) (at level 10).

  Notation "'K' S" := S.(ES.cont_set) (at level 10).

  Notation "'STid' S" := (fun t e => S.(ES.tid) e = t) (at level 10).

  Notation "'SR' S" := (fun a => is_true (is_r S.(ES.lab) a)) (at level 10).
  Notation "'SW' S" := (fun a => is_true (is_w S.(ES.lab) a)) (at level 10).
  Notation "'SF' S" := (fun a => is_true (is_f S.(ES.lab) a)) (at level 10).

  Notation "'SRel' S" := (fun a => is_true (is_rel S.(ES.lab) a)) (at level 10).

  Notation "'Ssb' S" := (S.(ES.sb)) (at level 10).
  Notation "'Scf' S" := (S.(ES.cf)) (at level 10).
  Notation "'Srmw' S" := (S.(ES.rmw)) (at level 10).
  Notation "'Sjf' S" := (S.(ES.jf)) (at level 10).
  Notation "'Sjfi' S" := (S.(ES.jfi)) (at level 10).
  Notation "'Sjfe' S" := (S.(ES.jfe)) (at level 10).
  Notation "'Srf' S" := (S.(ES.rf)) (at level 10).
  Notation "'Srfi' S" := (S.(ES.rfi)) (at level 10).
  Notation "'Srfe' S" := (S.(ES.rfe)) (at level 10).
  Notation "'Sco' S" := (S.(ES.co)) (at level 10).
  Notation "'Sew' S" := (S.(ES.ew)) (at level 10).

  Notation "'Srs' S" := (S.(Consistency.rs)) (at level 10).
  Notation "'Srelease' S" := (S.(Consistency.release)) (at level 10).
  Notation "'Ssw' S" := (S.(Consistency.sw)) (at level 10).
  Notation "'Shb' S" := (S.(Consistency.hb)) (at level 10).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).

  Notation "'Glab'" := (Execution.lab G).
  Notation "'Gloc'" := (Events.loc (lab G)).
  Notation "'Gtid'" := (Events.tid).

  Notation "'GR'" := (fun a => is_true (is_r Glab a)).
  Notation "'GW'" := (fun a => is_true (is_w Glab a)).
  Notation "'GF'" := (fun a => is_true (is_f Glab a)).

  Notation "'GRel'" := (fun a => is_true (is_rel Glab a)).
  Notation "'GAcq'" := (fun a => is_true (is_acq Glab a)).

  Notation "'GTid' t" := (fun x => Gtid x = t) (at level 1).
  Notation "'GNTid' t" := (fun x => Gtid x <> t) (at level 1).

  Notation "'Gsb'" := (Execution.sb G).
  Notation "'Grmw'" := (Execution.rmw G).
  Notation "'Grf'" := (Execution.rf G).
  Notation "'Gco'" := (Execution.co G).

  Notation "'Grs'" := (imm_s_hb.rs G).
  Notation "'Grelease'" := (imm_s_hb.release G).
  Notation "'Gsw'" := (imm_s_hb.sw G).
  Notation "'Ghb'" := (imm_s_hb.hb G).
  
  Notation "'Gfurr'" := (furr G sc).

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Notation "'thread_syntax' t"  := 
    (Language.syntax (thread_lts t)) (at level 10, only parsing).  

  Notation "'thread_st' t" := 
    (Language.state (thread_lts t)) (at level 10, only parsing).

  Notation "'thread_init_st' t" := 
    (Language.init (thread_lts t)) (at level 10, only parsing).

  Notation "'thread_cont_st' t" :=
    (fun st => existT _ (thread_lts t) st) (at level 10, only parsing).

  Notation "'cont_lang'" :=
    (fun S k => thread_lts (ES.cont_thread S k)) (at level 10, only parsing).

  Notation "'kE' S" := (fun k => ES.cont_sb_dom S k) (at level 1, only parsing).
  Notation "'ktid' S" := (fun k => ES.cont_thread S k) (at level 1, only parsing).
  
  Lemma simrel_e2a_init :
    simrel_e2a (prog_g_es_init prog G) G sc.
  Proof.
    constructor.
    { unfold e2a, prog_g_es_init.
      simpls.
      desf.
      remember
        (flatten
           (map
              (fun e0 : actid =>
                 match e0 with
                 | InitEvent l => [l]
                 | ThreadEvent _ _ => []
                 end) (acts G)))
        as ll.
      unfold Events.loc.
      unfolder. intros x [y [AA BB]].
      unfold ES.init in AA. red in AA. simpls.
      assert (exists b, In (y, b) (indexed_list
                   (map (fun l : location => Astore Xpln Opln l 0) ll)))
        as [b IN].
      { admit. }
      erewrite l2f_in in BB; eauto.
      2: by apply indexed_list_fst_nodup.
  Admitted.

  Lemma basic_step_e2a_e k k' e e' S' 
        (st st' : thread_st (ktid S k))
        (SRK : simrel_cont prog S G TC)
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S') :
    e2a S' e = ThreadEvent (ktid S k) (st.(eindex)).
  Proof. 
    cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (SE S' e) as SEe. 
    { eapply basic_step_acts_set; eauto. basic_solver. }
    unfold e2a. 
    destruct (excluded_middle_informative ((Stid S') e = tid_init)) as [INIT | nINIT]. 
    { exfalso. eapply basic_step_acts_ninit_set_e; eauto.
      unfold ES.acts_init_set. basic_solver. } 
    erewrite basic_step_tid_e; eauto.  
    edestruct k eqn:kEQ. 
    { erewrite basic_step_seqn_kinit. 
      { erewrite continit; eauto. }
      all : subst k; eauto. }
    erewrite basic_step_seqn_kevent with (k := k); eauto. 
    { erewrite contseqn; eauto. }
    all : subst k; eauto. 
  Qed.

  Lemma basic_step_e2a_e' k k' e e' S' 
        (st st' : thread_st (ktid S k))
        (SRK : simrel_cont prog S G TC)
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e (Some e') S S') :
    e2a S' e' = ThreadEvent (ktid S k) (1 + st.(eindex)).
  Proof. 
    cdes BSTEP_.
    assert (basic_step e (Some e') S S') as BSTEP.
    { econstructor; eauto. }
    assert (SE S' e') as SEe'. 
    { eapply basic_step_acts_set; eauto. basic_solver. }
    unfold e2a. 
    destruct (excluded_middle_informative ((Stid S') e' = tid_init)) as [INIT | nINIT]. 
    { exfalso. eapply basic_step_acts_ninit_set_e'; eauto.
      unfold ES.acts_init_set. basic_solver. } 
    erewrite basic_step_tid_e'; eauto.  
    erewrite basic_step_seqn_e'; eauto.
    edestruct k eqn:kEQ.
    { erewrite basic_step_seqn_kinit.
      { erewrite continit; eauto. } 
      all : subst k; eauto. }
    erewrite basic_step_seqn_kevent with (k := k); eauto. 
    { erewrite contseqn; eauto. }
    all : subst k; eauto. 
  Qed.

  Lemma basic_step_cert_dom_ne k k' e e' S' 
        (st st' : thread_st (ktid S k))
        (SRK : simrel_cont prog S G TC)
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S') 
        (STCOV : C ∩₁ GTid (ktid S k) ⊆₁ acts_set st.(ProgToExecution.G)) : 
    ~ (cert_dom G TC (ktid S k) st) (e2a S' e).
  Proof.
    cdes BSTEP_.
    red. intros HH.
    eapply cert_dom_alt in HH; eauto.
    destruct HH as [HA | HB].
    { destruct HA as [_ NTID].
      apply NTID.
      erewrite <- e2a_tid.
      eapply basic_step_tid_e; eauto. }
    erewrite basic_step_e2a_e in HB; eauto. 
    2 : eapply BSTEP_.
    eapply acts_rep in HB.
    2 : eapply SRK; eauto.
    desf. omega.
  Qed.

  Lemma basic_step_cert_dom_ne' k k' e e' S' 
        (st st' : thread_st (ktid S k))
        (SRK : simrel_cont prog S G TC)
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e (Some e') S S') 
        (STCOV : C ∩₁ GTid (ktid S k) ⊆₁ acts_set st.(ProgToExecution.G)) : 
    ~ (cert_dom G TC (ktid S k) st) (e2a S' e').
  Proof.
    cdes BSTEP_.
    red. intros HH.
    eapply cert_dom_alt in HH; eauto.
    destruct HH as [HA | HB].
    { destruct HA as [_ NTID].
      apply NTID.
      erewrite <- e2a_tid.
      eapply basic_step_tid_e'; eauto. }
    erewrite basic_step_e2a_e' in HB; eauto. 
    2 : eapply BSTEP_.
    eapply acts_rep in HB.
    2 : eapply SRK; eauto.
    desf. omega.
  Qed.

  Lemma basic_step_cert_dom k k' e e' S' 
        (st st' : thread_st (ktid S k))
        (SRK : simrel_cont prog S G TC)
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S') : 
    cert_dom G TC (ktid S' k') st' ≡₁ 
             cert_dom G TC (ktid S k) st ∪₁ 
               eq (e2a S' e) ∪₁ eq_opt (option_map (e2a S') e').
  Proof. 
    cdes BSTEP_.   
    assert (basic_step e e' S S') as BSTEP. 
    { econstructor. eauto. }
    unfold cert_dom. 
    erewrite basic_step_cont_thread_k; eauto. 
    rewrite !set_unionA.
    do 2 (eapply set_union_Propere; auto). 
    edestruct lbl_step_cases as [l [l' HH]].
    { eapply SRK. eauto. }
    { apply STEP. }
    destruct HH as [LBLS HH].
    apply opt_to_list_app_singl in LBLS.
    destruct LBLS as [LA LB]. subst l l'. 
    destruct HH as [HA | HB].
    { destruct HA as [_ [ACTS [_ [LBL' _]]]].
      unfold eq_opt, option_map, opt_same_ctor in *.
      destruct e'; [desf|].
      etransitivity; [eapply ACTS|].
      apply set_union_Propere; auto. 
      erewrite basic_step_e2a_e; eauto. 
      basic_solver. }
    destruct HB as [_ [ACTS [_ [LBLS _]]]].
    destruct LBLS as [ordr [ordw [ll [valr [valw [LA LB]]]]]].
    unfold eq_opt, option_map, opt_same_ctor in *.
    destruct e'; [|desf].
    etransitivity; [eapply ACTS|].
    rewrite set_unionA.
    apply set_union_Propere; auto. 
    erewrite basic_step_e2a_e; eauto. 
    erewrite basic_step_e2a_e'; eauto. 
  Qed.

  Lemma basic_step_nupd_cert_dom k k' e S'
        (st st' : thread_st (ktid S k))
        (SRK : simrel_cont prog S G TC)
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e None S S') :
    cert_dom G TC (ktid S' k') st' ≡₁
             cert_dom G TC (ktid S k) st ∪₁ eq (e2a S' e).
  Proof.
    erewrite basic_step_cert_dom; eauto. 
    unfold eq_opt, option_map. basic_solver.
  Qed.

  Lemma basic_step_e2a_E0_e TC' k k' e e' S' 
        (st st' st'' : thread_st (ktid S k))
        (SRK : simrel_cont prog S G TC)
        (CG : cert_graph G sc TC TC' (ktid S k) st'')
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
     E0 G TC' (ktid S k) (e2a S' e).
  Proof. 
    cdes BSTEP_. simpl in BSTEP_.
    erewrite basic_step_e2a_e; eauto using BSTEP_. 
    eapply ilbl_step_E0_eindex; eauto. 
    { eapply SRK. eauto. }
    apply STEP.
  Qed.

  Lemma basic_step_e2a_E0_e' TC' k k' e e' S' 
        (st st' st'' : thread_st (ktid S k))
        (SRK : simrel_cont prog S G TC)
        (CG : cert_graph G sc TC TC' (ktid S k) st'')
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e (Some e') S S') 
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
     E0 G TC' (ktid S k) (e2a S' e').
  Proof. 
    cdes BSTEP_. simpl in BSTEP_.
    erewrite basic_step_e2a_e'; eauto. 
    eapply ilbl_step_E0_eindex'; eauto. 
    { eapply SRK. eauto. }
    { apply STEP. }
    red. ins. by subst lbl'. 
  Qed.

  Lemma basic_step_e2a_GE_e TC' k k' e e' S' 
        (st st' st'' : thread_st (ktid S k))
        (SRK : simrel_cont prog S G TC)
        (CG : cert_graph G sc TC TC' (ktid S k) st'')
        (TCCOH : tc_coherent G sc TC')
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S') 
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :     
    GE (e2a S' e).
  Proof. 
    cdes BSTEP_. 
    eapply E0_in_E; eauto.  
    eapply basic_step_e2a_E0_e; eauto.
  Qed.

  Lemma basic_step_e2a_GE_e' TC' k k' e e' S' 
        (st st' st'' : thread_st (ktid S k))
        (SRK : simrel_cont prog S G TC)
        (CG : cert_graph G sc TC TC' (ktid S k) st'')
        (TCCOH : tc_coherent G sc TC')
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e (Some e') S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
     GE (e2a S' e').
  Proof. 
    cdes BSTEP_.
    eapply E0_in_E; eauto.  
    eapply basic_step_e2a_E0_e'; eauto.
  Qed.

  Lemma basic_step_e2a_GE TC' k k' e e' S' 
        (st st' st'' : thread_st (ktid S k))
        (SRK : simrel_cont prog S G TC)
        (SRE2A : simrel_e2a S G sc)
        (CG : cert_graph G sc TC TC' (ktid S k) st'')
        (TCCOH : tc_coherent G sc TC')
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
     e2a S' □₁ SE S' ⊆₁ GE.
  Proof. 
    cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    rewrite basic_step_acts_set; eauto.  
    rewrite !set_collect_union. 
    rewrite !set_subset_union_l.
    splits. 
    { erewrite set_collect_eq_dom; [eapply SRE2A|].
      eapply basic_step_e2a_eq_dom; eauto. } 
    { rewrite set_collect_eq.
      apply eq_predicate. 
      eapply basic_step_e2a_GE_e; eauto. }
    destruct e' as [e'|]; [|basic_solver]. 
    unfold eq_opt. 
    rewrite set_collect_eq.
    apply eq_predicate. 
    eapply basic_step_e2a_GE_e'; eauto. 
  Qed.

  Lemma basic_step_e2a_lab_e TC' k k' e e' S' 
        (st st' st'' : thread_st (ktid S k))
        (SRK : simrel_cont prog S G TC)
        (CG : cert_graph G sc TC TC' (ktid S k) st'')
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
     Slab S' e = Execution.lab (ProgToExecution.G st'') (e2a S' e).
  Proof. 
    cdes BSTEP_. simpl in BSTEP_.
    assert (Gtid (e2a S' e) = ktid S k) as GTIDe.
    { rewrite <- e2a_tid. erewrite basic_step_tid_e; eauto. }
    assert (wf_thread_state (ktid S k) st') as WFTS. 
    { eapply wf_thread_state_steps.
      { eapply SRK; eauto. }
      eapply ilbl_steps_in_steps.
      do 2 econstructor. eapply STEP. }
    arewrite ((Slab S') e = lbl).
    { rewrite LAB'. unfold upd_opt, opt_ext in *.
      destruct e'; desf. 
      { rewrite updo; [|omega].
          by rewrite upds. }
        by rewrite upds. }
    edestruct lbl_step_cases as [l [l' HH]]. 
    { eapply SRK; eauto. }
    { eapply STEP. }
    destruct HH as [AA BB].
    apply opt_to_list_app_singl in AA.
    destruct AA as [LA LB].
    subst l l'.
    erewrite steps_preserve_lab.    
    { erewrite basic_step_e2a_e.
      2-5 : eauto; apply SRCC.
      destruct BB as [BB | BB].
      { destruct BB as [_ [ACTS [LAB _]]]. 
        rewrite LAB. by rewrite upds. }
      destruct BB as [_ [ACTS [LAB HH]]].
      desf. rewrite LAB.
      unfold upd_opt.
      rewrite updo. 
      { rewrite upds. basic_solver. }
      red. intros HH. inversion HH. omega. }
    { by rewrite GTIDe. }
    { apply ilbl_steps_in_steps. 
      by rewrite GTIDe. }    
    erewrite basic_step_e2a_e.
    2-5 : eauto; apply SRCC.
    desf; apply ACTS; basic_solver.    
  Qed.

  Lemma basic_step_e2a_lab_e' TC' k k' e e' S' 
        (st st' st'' : thread_st (ktid S k))
        (SRK : simrel_cont prog S G TC)
        (CG : cert_graph G sc TC TC' (ktid S k) st'')
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e (Some e') S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
     Slab S' e' = Execution.lab (ProgToExecution.G st'') (e2a S' e').
  Proof. 
    cdes BSTEP_. simpl in BSTEP_.
    assert (Gtid (e2a S' e') = ktid S k) as GTIDe.
    { rewrite <- e2a_tid. erewrite basic_step_tid_e'; eauto. }
    assert (wf_thread_state (ktid S k) st') as WFTS. 
    { eapply wf_thread_state_steps.
      { eapply SRK; eauto. }
      eapply ilbl_steps_in_steps.
      do 2 econstructor. eapply STEP. }
    destruct lbl' as [lbl' | ].
    2 : { by unfold opt_same_ctor in LABEL'. }
    arewrite ((Slab S') e' = lbl').
    { rewrite LAB'. unfold upd_opt, opt_ext in *.
      by rewrite upds. }
    edestruct lbl_step_cases as [l [l' HH]]. 
    { eapply SRK; eauto. }
    { eapply STEP. }
    destruct HH as [AA BB].
    apply opt_to_list_app_singl in AA.
    destruct AA as [LA LB].
    subst l l'.
    destruct BB as [BB | BB]; [desf|].
    erewrite steps_preserve_lab.    
    { erewrite basic_step_e2a_e'.
        2-5 : eauto; apply SRCC.
        destruct BB as [_ [ACTS [LAB HH]]].
        desf. rewrite LAB.
        unfold upd_opt.
        by rewrite upds. }
    { by rewrite GTIDe. }
    { apply ilbl_steps_in_steps. 
      by rewrite GTIDe. }    
    erewrite basic_step_e2a_e'.
    2-5 : eauto; apply SRCC.
    desf; apply ACTS; basic_solver.    
  Qed.

  Lemma basic_step_e2a_certlab_e TC' k k' e e' S' 
        (st st' st'' : thread_st (ktid S k))
        (SRK : simrel_cont prog S G TC)
        (CG : cert_graph G sc TC TC' (ktid S k) st'')
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
     Slab S' e = certLab G st'' (e2a S' e).
  Proof. 
    unfold certLab, restr_fun.
    destruct 
      (excluded_middle_informative (acts_set (ProgToExecution.G st'') (e2a S' e))) 
      as [GCE | nGCE].
    { eapply basic_step_e2a_lab_e; eauto. }
    exfalso. apply nGCE. 
    eapply dcertE; eauto.
    eapply basic_step_e2a_E0_e; eauto. 
  Qed.

  Lemma basic_step_e2a_certlab_e' TC' k k' e e' S' 
        (st st' st'' : thread_st (ktid S k))
        (SRK : simrel_cont prog S G TC)
        (CG : cert_graph G sc TC TC' (ktid S k) st'')
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e (Some e') S S')
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') : 
     Slab S' e' = certLab G st'' (e2a S' e').
  Proof. 
    unfold certLab, restr_fun.
    destruct 
      (excluded_middle_informative (acts_set (ProgToExecution.G st'') (e2a S' e'))) 
      as [GCE | nGCE].
    { eapply basic_step_e2a_lab_e'; eauto. }
    exfalso. apply nGCE. 
    eapply dcertE; eauto.
    eapply basic_step_e2a_E0_e'; eauto. 
  Qed.

  Lemma basic_step_e2a_same_lab_u2v TC' k k' e e' S' 
        (st st' st'' : thread_st (ktid S k))
        (SRK : simrel_cont prog S G TC)
        (SRE2A : simrel_e2a S G sc)
        (CG : cert_graph G sc TC TC' (ktid S k) st'')
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S') 
        (CST_REACHABLE : (lbl_step (ktid S k))＊ st' st'') :
    same_lab_u2v_dom (SE S') (Slab S') (Glab ∘ (e2a S')).
  Proof. 
    cdes BSTEP_. simpl in BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    unfold same_lab_u2v_dom.
    intros x SEx.
    eapply basic_step_acts_set in SEx; eauto.
    destruct SEx as [[SEx | SEx] | SEx].
    { erewrite basic_step_lab_eq_dom; eauto. 
      unfold compose. 
        by erewrite basic_step_e2a_eq_dom; eauto; apply SRE2A. }
    { subst x.
      erewrite basic_step_e2a_lab_e; eauto.
      unfold compose. 
      eapply cuplab_cert; [|eapply dcertE]; eauto.
      eapply basic_step_e2a_E0_e; eauto. }
    destruct e' as [e' | ].
    2 : { exfalso. by unfold eq_opt in SEx. }
    unfold eq_opt in SEx. subst x.
    erewrite basic_step_e2a_lab_e'; eauto.
    unfold compose. 
    eapply cuplab_cert; [|eapply dcertE]; eauto.
    eapply basic_step_e2a_E0_e'; eauto.    
  Qed.

End SimRelEventToActionLemmas.