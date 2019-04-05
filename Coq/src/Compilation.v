Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CombRelations SimTraversal SimulationRel AuxRel
     PromiseToimm_s.
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
Require Import SimRelStep.

Set Implicit Arguments.
Local Open Scope program_scope.

Section Compilation.
  Variable prog : Prog.t.
  Variable G : execution.
  Variable sc : relation actid.

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).

  Notation "'Gtid'" := (tid).
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gloc'" := (loc G.(lab)).
  
  Notation "'GTid' t" := (fun x => tid x = t) (at level 1).
  Notation "'GNTid' t" := (fun x => tid x <> t) (at level 1).

  Notation "'GR'" := (fun a => is_true (is_r Glab a)).
  Notation "'GW'" := (fun a => is_true (is_w Glab a)).
  Notation "'GF'" := (fun a => is_true (is_f Glab a)).

  Notation "'GRel'" := (fun a => is_true (is_rel Glab a)).
  
  Notation "'Gsb'" := (G.(sb)).
  Notation "'Grmw'" := G.(rmw).
  Notation "'Grf'" := (G.(rf)).
  Notation "'Gco'" := (G.(co)).

  Notation "'Grs'" := (G.(imm_s_hb.rs)).
  Notation "'Grelease'" := (G.(imm_s_hb.release)).
  Notation "'Ghb'" := (G.(imm_s_hb.hb)).

  Section Extraction.

    Variable S : ES.t.
    Variable TC : trav_config.
    Variable X : eventid -> Prop.
  
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

    Definition simrel_extracted := 
      ⟪ GACTS : GE ≡₁ e2a S □₁ X ⟫ /\
      ⟪ GLAB  : eq_dom X Slab (Glab ∘ e2a S) ⟫ /\
      ⟪ GSB   : Gsb  ≡  e2a S □ (Ssb ∩ X × X) ⟫ /\
      ⟪ GRMW  : Grmw ≡  e2a S □ (Srmw ∩ X × X) ⟫ /\
      ⟪ GRF   : Grf  ≡  e2a S □ (Srf ∩ X × X) ⟫ /\
      ⟪ GCO   : Gco  ≡  e2a S □ (Sco ∩ X × X) ⟫.

    Lemma simrel_extract
          (SRC : simrel_common prog S G sc TC X)
          (COVinG : GE ⊆₁ C) :
      simrel_extracted.
    Proof. 
      assert (ES.Wf S) as SWF.
      { apply SRC. }
      assert (Wf G) as GWF.
      { apply SRC. }
      assert (tc_coherent G sc TC) as TCCOH.
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
      { rewrite DCOV. symmetry. eapply ex_cov_iss; eauto. }
      { eapply eq_dom_more; 
          [| | | eapply ex_cov_iss_lab; eauto].
        all : auto.
        arewrite (e2a S ⋄₁ (C ∪₁ I) ≡₁ e2a S ⋄₁ (C ∪₁ dom_rel (Gsb^? ⨾ ⦗I⦘))).
        { admit. }
        arewrite (e2a S ⋄₁ (C ∪₁ dom_rel (Gsb^? ⨾ ⦗I⦘)) ≡₁ e2a S ⋄₁ (e2a S □₁ X)).
        { admit. }
        split; [|basic_solver].
        rewrite <- set_in_map_collect. done. }
      { split.
        { admit. }
        rewrite collect_rel_interi.
        erewrite e2a_sb; try apply SRC. 
        basic_solver. }
      { split. 
        { arewrite (Grmw ≡ ⦗C⦘ ⨾ Grmw ⨾ ⦗C⦘).
          { rewrite wf_rmwE at 1; auto. by rewrite COVG. }
          rewrite <- restr_cross, restr_relE.
          eapply cov_rmw_cov; eauto. }
        rewrite collect_rel_interi.
        erewrite e2a_rmw; try apply SRC. 
        basic_solver. }
      { split. 
        { arewrite (Grf ≡ ⦗GE ∩₁ GW⦘ ⨾ Grf ⨾ ⦗GE⦘).
        { rewrite wf_rfE, wf_rfD; auto. basic_solver. }
        rewrite ISSG, COVG.
          rewrite <- restr_cross, restr_relE.
          eapply iss_rf_cov; eauto. }
        admit. }
      split. 
      { arewrite (Gco ≡ ⦗GE ∩₁ GW⦘ ⨾ Gco ⨾ ⦗GE ∩₁ GW⦘).
        { rewrite wf_coE, wf_coD at 1; auto. basic_solver. }
        rewrite ISSG.
        rewrite <- restr_cross, restr_relE.
        eapply iss_co_iss; eauto. }
      rewrite collect_rel_interi.
      erewrite e2a_co; try apply SRC. 
      basic_solver.
    Admitted.

  End Extraction.

  Lemma simrel_traversal
        (nInitProg : ~ IdentMap.In tid_init prog)
        (GProg : program_execution prog G)
        (GWF : Execution.Wf G)
        (IMMCONS : imm_consistent G sc) : 
    forall TC (TC_STEPS : (sim_trav_step G sc)＊ (init_trav G) TC), 
      exists S X, 
        ⟪ STEPS : (ESstep.t Weakestmo)＊ (ES.init prog) S ⟫ /\
        ⟪ SRC  : simrel_common prog S G sc TC X ⟫.
  Proof. 
    eapply clos_refl_trans_ind_left.
    { exists (ES.init prog), (ES.acts_set (ES.init prog)).
      splits; auto using rt_refl, simrel_init. }
    intros TC TC' TC_STEPS IH TC_STEP. desc.
    edestruct simrel_step as [X' [S' HH]]; eauto. 
    destruct HH as [STEPS' SRC']. 
    red in STEPS', SRC'.
    exists S', X'. splits; auto.
    eapply rt_trans; eauto.
  Qed.

  Theorem compilation_correctness 
        (nInitProg : ~ IdentMap.In tid_init prog)
        (GProg : program_execution prog G)
        (GWF : Execution.Wf G)
        (IMMCONS : imm_consistent G sc) :
    exists S X,
      ⟪ STEPS : (ESstep.t Weakestmo)＊ (ES.init prog) S ⟫ /\
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