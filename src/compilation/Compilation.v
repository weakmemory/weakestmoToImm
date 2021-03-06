Require Import Program.Basics.
From hahn Require Import Hahn.
From PromisingLib Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb
     CombRelations SimTraversal TraversalCounting.
Require Import AuxRel.
Require Import AuxDef.
Require Import ImmProperties.
Require Import EventStructure.
Require Import Consistency.
Require Import Step.
Require Import Execution.
Require Import EventToAction.
Require Import SimRelCont.
Require Import SimRelEventToAction.
Require Import SimRel.
Require Import SimRelInit.
Require Import SimRelStep.
Require Import ProgES.
Require Import CertRf.

Set Implicit Arguments.
Local Open Scope program_scope.

Section Compilation.
  Variable prog : stable_prog_type.
  Variable G : execution.
  Variable sc : relation actid.

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

  Notation "'Geco'" := (Execution_eco.eco G).

  Section Extraction.

    Variable S : ES.t.
    Variable TC : trav_config.
    Variable X : eventid -> Prop.
    Variable T : thread_id -> Prop.

    Notation "'SE'" := S.(ES.acts_set).
    Notation "'SEinit'" := S.(ES.acts_init_set).
    Notation "'SEninit'" := S.(ES.acts_ninit_set).
    Notation "'Stid'" := (S.(ES.tid)).
    Notation "'Slab'" := (S.(ES.lab)).
    Notation "'Sloc'" := (loc S.(ES.lab)).
    Notation "'K'" := S.(ES.cont_set).

    Notation "'STid' t" := (fun x => Stid x = t) (at level 1).

    Notation "'SR'" := (fun a => is_true (is_r Slab a)).
    Notation "'SW'" := (fun a => is_true (is_w Slab a)).
    Notation "'SF'" := (fun a => is_true (is_f Slab a)).
    Notation "'SRel'" := (fun a => is_true (is_rel Slab a)).

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

    Notation "'C'"  := (covered TC).
    Notation "'I'"  := (issued TC).

    (* Relation stating that extracted subset `X` is `isomorphic` to execution graph `G`.
     * This definition is actually has nothing to do with `simrel`, 
     * but for historical reasons it's defined here. *)
    Definition simrel_extracted :=
      ⟪ GACTS : GE ≡₁ e2a S □₁ X ⟫ /\
      ⟪ GLAB  : eq_dom X Slab (Glab ∘ e2a S) ⟫ /\
      ⟪ GSB   : Gsb  ≡  e2a S □ (Ssb ∩ X × X) ⟫ /\
      ⟪ GRMW  : Grmw ≡  e2a S □ (Srmw ∩ X × X) ⟫ /\
      ⟪ GRF   : Grf  ≡  e2a S □ (Srf ∩ X × X) ⟫ /\
      ⟪ GCO   : Gco  ≡  e2a S □ (Sco ∩ X × X) ⟫.

    Lemma simrel_extract
          (SRC : simrel_consistent prog S G sc TC X T)
          (* condition that all the events are covered implies that  
           * the traversal configuration `TC` is terminal *)
          (COVinG : GE ⊆₁ C) :
      simrel_extracted.
    Proof.
      assert (ES.Wf S) as SWF.
      { apply SRC. }
      assert (Wf G) as GWF.
      { apply SRC. }
      assert (tc_coherent G sc TC) as TCCOH.
      { apply SRC. }
      assert (Execution.t S X) as EXEC.
      { apply SRC. }
      assert (simrel prog S G sc TC X T) as SRC_.
      { apply SRC. }
      assert (simrel_e2a S G sc) as SRE2A.
      { apply SRC. }

      assert (GE ≡₁ C) as COVG.
      { split; auto. eapply coveredE; eauto. }
      assert (GE ≡₁ C ∪₁ I) as COVISSG.
      { split; auto.
        { rewrite COVG. basic_solver. }
        apply set_subset_union_l. split.
        { eapply coveredE; eauto. }
        eapply issuedE; eauto. }
      assert (GE ≡₁ C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘)) as DCOV.
      { rewrite COVG.
        split; [basic_solver|].
        unionL; auto.
        rewrite issuedE; [|apply SRC].
        rewrite COVG.
        rewrite crE. relsf.
        split; auto.
        eapply dom_sb_covered; eauto. }
      assert (GE ∩₁ GW ≡₁ I) as ISSG.
      { split.
        { rewrite COVG. rewrite set_interC.
          eapply w_covered_issued; eauto. }
        apply set_subset_inter_r. split.
        { eapply issuedE; eauto. }
        eapply issuedW; eauto. }

      constructor; splits.
      3-6: split.

      { rewrite DCOV. symmetry.
        eapply ex_cov_iss; eauto. }

      { eapply eq_dom_more;
          [| | | eapply ex_cov_iss_lab; eauto].
        all : auto.
        rewrite <- COVISSG, DCOV.
        fold (CsbI G TC).
        erewrite <- ex_cov_iss; eauto.
        erewrite set_inter_absorb_r; auto.
        apply set_in_map_collect. }

      { arewrite (Gsb ≡ ⦗C⦘ ⨾ Gsb ⨾ ⦗C⦘).
        { rewrite wf_sbE at 1; auto. by rewrite COVG. }
        rewrite <- restr_cross, restr_relE.
        eapply sb_restr_cov_in_ex; eauto. }

      { rewrite collect_rel_interi.
        erewrite e2a_sb; try apply SRC.
        basic_solver. }

      { arewrite (Grmw ≡ ⦗C⦘ ⨾ Grmw ⨾ ⦗C⦘).
        { rewrite wf_rmwE at 1; auto. by rewrite COVG. }
        rewrite <- restr_cross, restr_relE.
        eapply rmw_restr_cov_in_ex; eauto. }

      { rewrite collect_rel_interi.
        erewrite e2a_rmw; try apply SRC.
        basic_solver. }

      { arewrite (Grf ≡ ⦗GE ∩₁ GW⦘ ⨾ Grf ⨾ ⦗GE⦘).
        { rewrite wf_rfE, wf_rfD; auto. basic_solver. }
        rewrite ISSG, COVG.
        rewrite <- restr_cross, restr_relE.
        eapply iss_rf_cov_in_ex; eauto. }

      { intros x' y' [x [y [[RF [Xx Xy]] [EQx' EQy']]]].
        unfolder. ins. desf.
        eapply jf_cov_in_rf; eauto.
        unfold ES.rf in RF.
        destruct RF as [[z [EW JF]] nCF].
        exists z, y.
        splits; auto.
        { apply seq_eqv_r.
          unfolder; splits; auto.
          apply COVG.
          eapply e2a_GE.
          { apply SRC. }
          eexists; splits; eauto.
          eapply Execution.ex_inE; eauto. }
        symmetry.
        eapply e2a_ew; eauto.
        basic_solver 10. }

      { arewrite (Gco ≡ ⦗GE ∩₁ GW⦘ ⨾ Gco ⨾ ⦗GE ∩₁ GW⦘).
        { rewrite wf_coE, wf_coD at 1; auto. basic_solver. }
        rewrite ISSG.
        rewrite <- restr_cross, restr_relE.
        eapply co_restr_iss_in_ex; eauto. }

      unfolder. ins. desf.
      eapply e2a_co_ncf; eauto.
      unfolder; do 2 eexists; splits; eauto.
      intros CF.
      eapply Execution.ex_ncf.
      { apply SRC. }
      apply seq_eqv_lr; eauto.

    Qed.

  End Extraction.

  Lemma simrel_traversal
        (nInitProg : ~ IdentMap.In tid_init prog)
        (GProg : program_execution (stable_prog_to_prog prog) G)
        (GWF : Execution.Wf G)
        (IMMCONS : imm_consistent G sc)
        (nLocsEmpty : g_locs G <> [])
        (GCLOS : forall t m n (LT : m < n) (NE : GE (ThreadEvent t n)),
            GE (ThreadEvent t m)) :
    let T := (fun t => IdentMap.In t prog) in
    forall TC (TC_STEPS : (sim_trav_step G sc)＊ (init_trav G) TC),
      exists S X,
        ⟪ STEPS : (step Weakestmo)＊ (prog_g_es_init prog G) S ⟫ /\
        ⟪ SRC  : simrel_consistent prog S G sc TC X T ⟫.
  Proof.
    eapply clos_refl_trans_ind_left.
    { exists (prog_g_es_init prog G), (ES.acts_set (prog_g_es_init prog G)).
      splits; auto using rt_refl, simrel_init. }
    intros TC TC' TC_STEPS IH TC_STEP. desc.
    destruct TC_STEP as [thread TC_ISTEP].
    edestruct simrel_step as [X' [S' HH]]; eauto.
    { apply stable_prog_to_prog_in.
      eapply CertGraph.trstep_thread_prog; eauto.
      apply SRC. }
    destruct HH as [STEPS' SRC'].
    red in STEPS', SRC'.
    exists S', X'. splits; auto.
    eapply rt_trans; eauto.
  Qed.

  Theorem compilation_correctness
        (nInitProg : ~ IdentMap.In tid_init prog)
        (GProg : program_execution (stable_prog_to_prog prog) G)
        (GWF : Execution.Wf G)
        (IMMCONS : imm_consistent G sc)
        (nLocsEmpty : g_locs G <> [])
        (GCLOS : forall t m n (LT : m < n) (NE : GE (ThreadEvent t n)),
            GE (ThreadEvent t m)) :
    exists S X,
      ⟪ STEPS : (step Weakestmo)＊ (prog_g_es_init prog G) S ⟫ /\
      ⟪ EXEC  : simrel_extracted S X ⟫.
  Proof.
    edestruct sim_traversal
      as [TC [TC_STEPS GCOV]];
      eauto.
    edestruct simrel_traversal
      as [S [X [STEPS SRC]]];
      eauto.
    red in STEPS, SRC.
    exists S, X.
    splits; auto.
    eapply simrel_extract; eauto.
  Qed.

End Compilation.
