Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CombRelations SimTraversal SimulationRel AuxRel.
Require Import AuxRel.
Require Import AuxDef.
Require Import ImmProperties.
Require Import EventStructure.
Require Import Consistency.
Require Import Execution.
Require Import EventToAction.
Require Import LblStep.
Require Import SimRelCont.
Require Import SimRelEventToAction.
Require Import ProgES.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRel.
  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G : execution.
  Variable sc : relation actid.
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
  Notation "'SNTid' t" := (fun x => Stid x <> t) (at level 1).

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

  Notation "'thread_syntax' tid"  := 
    (Language.syntax (thread_lts tid)) (at level 10, only parsing).  

  Notation "'thread_st' tid" := 
    (Language.state (thread_lts tid)) (at level 10, only parsing).

  Notation "'thread_init_st' tid" := 
    (Language.init (thread_lts tid)) (at level 10, only parsing).
  
  Notation "'thread_cont_st' tid" :=
    (fun st => existT _ (thread_lts tid) st) (at level 10, only parsing).

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

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Notation "'Gfurr'" := (furr G sc).

  Notation "'e2a'" := (e2a S).

  Record simrel_graph := 
    { gprclos : forall thread m n (LT : m < n) (EE : GE (ThreadEvent thread n)),
        GE (ThreadEvent thread m);
      rmwclos : forall r w (RMW : Grmw r w), C r <-> C w;
      irelcov : GW ∩₁ GRel ∩₁ I ⊆₁ C;
    }.

  Record simrel_ :=
    { noinitprog : ~ IdentMap.In tid_init prog ;
      gprog : program_execution prog G ;
      
      gwf   : Execution.Wf G ;
      swf   : ES.Wf S ;
      
      gcons : imm_consistent G sc ;

      tccoh : tc_coherent G sc TC ;

      sr_graph : simrel_graph ;

      sr_exec : Execution.t S X ;
      
      sr_cont : simrel_cont prog S G TC ;

      sr_e2a : simrel_e2a S G sc ;
      
      ex_cov_iss : e2a □₁ X ≡₁ C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘) ;
      
      ex_cov_iss_lab : eq_dom (X ∩₁ e2a ⋄₁ (C ∪₁ I)) Slab (Glab ∘ e2a) ;

      rmw_cov_in_ex : Grmw ⨾ ⦗ C ⦘ ⊆ e2a □ Srmw ⨾ ⦗ X ⦘ ;
      
      jf_cov_in_rf : e2a □ (Sjf ⨾ ⦗X ∩₁ e2a ⋄₁ C⦘) ⊆ Grf ;

      jfe_ex_iss : dom_rel Sjfe ⊆₁ dom_rel (Sew ⨾ ⦗ X ∩₁ e2a ⋄₁ I ⦘) ;
      ew_ex_iss  : dom_rel (Sew \ eq) ⊆₁ dom_rel (Sew ⨾ ⦗ X ∩₁ e2a ⋄₁ I ⦘) ;

      (* rel_ew_ex_iss : dom_rel (Srelease ⨾ Sew ⨾ ⦗ X ⦘) ⊆₁ X ; *)
    }.

  Definition simrel := 
    ⟪ SRC_ : simrel_ ⟫ /\ 
    ⟪ SCONS : @es_consistent S Weakestmo ⟫.
  
  Section SimRelCommonProps. 
    
    Variable SRC_ : simrel_.

    (******************************************************************************)
    (** ** X properties  *)
    (******************************************************************************)

    Lemma ex_iss_inW : 
      X ∩₁ e2a ⋄₁ I ⊆₁ SW.
    Proof.
      unfolder.
      intros x [xX xI].
      unfold is_w.
      erewrite ex_cov_iss_lab; auto.
      { unfold compose.
        eapply issuedW; eauto.
        apply SRC_. }
      basic_solver.
    Qed.

    (******************************************************************************)
    (** ** sb/rmw/jf/ew/co properties  *)
    (******************************************************************************)

    Lemma sb_cov :
      dom_rel (Ssb ⨾ ⦗ e2a ⋄₁ C ⦘) ⊆₁ e2a ⋄₁ C.
    Proof.
      unfold set_map.
      rewrite seq_eqv_r.
      intros x [y [SB Cy]].
      eapply dom_sb_covered; [apply SRC_|].
      unfolder; do 2 eexists; splits; eauto.
      eapply e2a_sb; try apply SRC_.
      basic_solver 10.
    Qed.

    Lemma sb_ex_cov :
      dom_rel (Ssb ⨾ ⦗ X ∩₁ e2a ⋄₁ C ⦘) ⊆₁ X ∩₁ e2a ⋄₁ C.
    Proof.
      rewrite seq_eqv_r.
      intros x [y [SB [Xy Cy]]].
      split.
      { eapply Execution.ex_sb_prcl; [apply SRC_|]. basic_solver 10. }
      eapply sb_cov. basic_solver 10.
    Qed.
    
    Lemma rfe_ex_iss :
      dom_rel Srfe ⊆₁ dom_rel (Sew ⨾ ⦗X ∩₁ e2a ⋄₁ I⦘).
    Proof.
      assert (ES.Wf S) as WFS.
      { apply SRC_. }
      unfold ES.rfe, ES.rf, ES.jfe.
      intros x [y [[[z [EW JF]] CC] NSB]].
      assert (~ Ssb z y) as AA.
      { intros SB. apply CC.
        apply ES.cf_sb_in_cf; auto.
        eexists. split; eauto.
        edestruct ES.ewc; eauto.
        apply ES.ewD in EW; auto.
        apply ES.jfD in JF; auto.
        red. ins. type_solver. }
      edestruct SRC_.(jfe_ex_iss) as [v HH].
      { eexists. split; eauto. }
      destruct_seq_r HH as BB.
      eexists. apply seq_eqv_r. split; [|by eauto].
      generalize WFS.(ES.ew_trans) EW HH. basic_solver.
    Qed.

    Lemma ew_in_ew_ex_iss_ew : 
      Sew ⊆ (Sew ⨾ ⦗X ∩₁ e2a ⋄₁ I⦘ ⨾ Sew)^?.
    Proof. 
      assert (ES.Wf S) as WFS.
      { apply SRC_. }
      rewrite <- seqA.
      intros x y EWxy.
      destruct (classic (x = y)) as [EQ | nEQ].
      { basic_solver. }
      right. edestruct ew_ex_iss as [z HH]; auto.
      { basic_solver. }
      eexists; splits; eauto.
      eapply ES.ew_trans; eauto.
      apply ES.ew_sym; auto.
      generalize HH. basic_solver.
    Qed.

    (******************************************************************************)
    (** ** `e2a □ S.rr ⊆ G.rr`  properties  *)
    (******************************************************************************)

    Lemma ex_Tid t : 
      e2a □₁ (X ∩₁ STid t) ≡₁ (e2a □₁ X) ∩₁ GTid t.
    Proof. 
      unfolder. split. 
      { ins; desf. 
        split; eauto.
        symmetry. apply e2a_tid. }
      ins; desf.
      eexists; splits; eauto.
      apply e2a_tid.
    Qed.

    Lemma ex_NTid t : 
      e2a □₁ (X ∩₁ SNTid t) ≡₁ (e2a □₁ X) ∩₁ GNTid t.
    Proof. 
      unfolder. split. 
      { intros x [y [[Xy NTIDy] EQx]].
        splits; eauto.
        intros TIDx. apply NTIDy.
        subst. apply e2a_tid. }
      intros x [[y [Xy EQx]] NTIDx].
      eexists; splits; eauto.
      intros TIDy. apply NTIDx.
      subst. symmetry. apply e2a_tid.
    Qed.
    
    Lemma e2a_ew_iss : 
      e2a □ (Sew \ eq) ⊆ ⦗ I ⦘. 
    Proof.
      intros x y HH.
      assert (x = y) as EQxy; subst.
      { eapply e2a_ew; [apply SRC_|]. generalize HH. basic_solver 10. }
      split; auto.
      destruct HH as [a [b [EW [EQx EQy]]]]; subst.
      edestruct ew_ex_iss as [x HH]; eauto.
      { eexists; eauto. }
      destruct_seq_r HH as FI.
      red in FI. destruct FI as [y IY]; subst.
      unfolder in IY.
      arewrite (e2a a = e2a x); auto.
      eapply e2a_ew; [apply SRC_|].
      eexists; eauto.
    Qed.

    (******************************************************************************)
    (** ** `G.rr ⊆ e2a □ S.rr` properties  *)
    (******************************************************************************)

    Lemma sb_cov_in_ex : 
      Gsb ⨾ ⦗C⦘ ⊆ e2a □ Ssb ⨾ ⦗X⦘.
    Proof. 
      assert (Wf G) as WFG.
      { apply SRC_. }
      assert (ES.Wf S) as WFS.
      { apply SRC_. }
      assert (tc_coherent G sc TC) as TCCOH.
      { apply SRC_. }
      assert (Execution.t S X) as EXEC.
      { apply SRC_. }
      erewrite dom_rel_helper with (r := Gsb ⨾ ⦗C⦘).
      2 : eapply dom_sb_covered; eauto. 
      rewrite <- restr_relE.
      unfolder.
      intros x y [SB [Cx Cy]].
      assert ((e2a □₁ X) x) as e2aXx.
      { apply ex_cov_iss; auto. basic_solver. }
      assert ((e2a □₁ X) y) as e2aXy.
      { apply ex_cov_iss; auto. basic_solver. }
      destruct e2aXx as [x' [Xx' EQx]].
      destruct e2aXy as [y' [Xy' EQy]].
      do 2 eexists; splits; eauto.
      assert (SEninit y') as nINITy.
      { red. unfolder. split. 
        { eapply Execution.ex_inE; eauto. }
        intros EINITy.
        apply no_sb_to_init in SB.
        apply seq_eqv_r in SB.
        destruct SB as [SB nINITy].
        apply nINITy. 
        eapply e2a_Einit.
        1-3 : apply SRC_.
        basic_solver. }
      set (HH := SB).
      apply sb_tid_init in HH.
      destruct HH as [GTID | INITx].
      { assert (Stid x' = Stid y') as STID.
        { rewrite !e2a_tid. basic_solver. }
        assert (SEninit x') as nINITx.
        { red. unfolder. split. 
          { eapply Execution.ex_inE; eauto. }
          intros [_ TIDx].
          apply nINITy. 
          unfold ES.acts_init_set. split.
          { eapply Execution.ex_inE; eauto. }
          congruence. }
        edestruct ES.same_thread_alt with (x := x') (y := y')
          as [[EQ | [SB' | SB']] | CF]; subst; eauto.
        { exfalso. eapply sb_irr; eauto. }
        { exfalso. eapply sb_irr, sb_trans; eauto. 
          eapply e2a_sb.
          1-4 : apply SRC_.
          basic_solver 10. }
        exfalso. eapply Execution.ex_ncf; eauto.
        apply seq_eqv_lr. splits; [|apply CF|]; eauto. }
      apply ES.sb_init; auto. split; auto.
      subst. eapply e2a_map_Einit. split.
      { eapply Execution.ex_inE; eauto. } 
      split; auto. apply wf_sbE in SB. 
      generalize SB. basic_solver. 
    Qed.

    Lemma sb_restr_cov_in_ex : 
      ⦗C⦘ ⨾ Gsb ⨾ ⦗C⦘ ⊆ e2a □ ⦗X⦘ ⨾ Ssb ⨾ ⦗X⦘.
    Proof.
      assert (Wf G) as WFG.
      { apply SRC_. }
      assert (ES.Wf S) as WFS.
      { apply SRC_. }
      assert (tc_coherent G sc TC) as TCCOH.
      { apply SRC_. }
      assert (Execution.t S X) as EXEC.
      { apply SRC_. }
      erewrite <- dom_rel_helper with (r := Gsb ⨾ ⦗C⦘),
               <- dom_rel_helper with (r := Ssb ⨾ ⦗X⦘).
      { by apply sb_cov_in_ex. }
      { by apply Execution.ex_sb_prcl. }
      eapply dom_sb_covered; eauto. 
    Qed.

    Lemma rmw_restr_cov_in_ex : 
      ⦗C⦘ ⨾ Grmw ⨾ ⦗C⦘ ⊆ e2a □ ⦗X⦘ ⨾ Srmw ⨾ ⦗X⦘.
    Proof. 
      assert (Wf G) as WFG.
      { apply SRC_. }
      assert (ES.Wf S) as WFS.
      { apply SRC_. }
      assert (tc_coherent G sc TC) as TCCOH.
      { apply SRC_. }
      assert (Execution.t S X) as EXEC.
      { apply SRC_. }
      erewrite <- dom_rel_helper with (r := Grmw ⨾ ⦗C⦘),
               <- dom_rel_helper with (r := Srmw ⨾ ⦗X⦘).                                      
      { by apply rmw_cov_in_ex. }
      { rewrite ES.rmwi; auto.
        rewrite immediate_in.
        by apply Execution.ex_sb_prcl. }
      rewrite wf_rmwi; auto.
      rewrite immediate_in.
      eapply dom_sb_covered; eauto. 
    Qed.

    Lemma rf_cov_in_ex : 
      Grf ⨾ ⦗ C ⦘ ⊆ e2a □ Srf ⨾ ⦗ X ⦘.
    Proof. admit. Admitted.

    Lemma iss_rf_cov_in_ex : 
      ⦗I⦘ ⨾ Grf ⨾ ⦗C⦘ ⊆ e2a □ ⦗X⦘ ⨾ Srf ⨾ ⦗X⦘.
    Proof. 
      assert (Wf G) as WFG.
      { apply SRC_. }
      assert (ES.Wf S) as WFS.
      { apply SRC_. }
      assert (tc_coherent G sc TC) as TCCOH.
      { apply SRC_. }
      assert (Execution.t S X) as EXEC.
      { apply SRC_. }
      erewrite <- dom_rel_helper with (r := Grf ⨾ ⦗C⦘).
      2 : eapply dom_rf_covered; eauto.
      rewrite <- restr_relE, seq_eqv_r.
      intros x y [GRF Cy].
      edestruct rf_cov_in_ex
        as [x' [y' [HH [EQx EQy]]]]; auto.
      { basic_solver. }
      apply seq_eqv_r in HH.
      destruct HH as [SRF Xy].
      edestruct Execution.ex_rf_compl
        as [z' HH]; eauto.
      { split; [apply Xy|].
        apply ES.rfD in SRF; auto.
        generalize SRF. basic_solver. }
      apply seq_eqv_l in HH.
      destruct HH as [Xz SRF'].
      unfolder; do 2 eexists; splits; eauto.
      subst x. eapply e2a_ew; [apply SRC_|].
      unfolder; do 2 eexists; splits; eauto.
      apply ES.rf_trf_in_ew; auto.
      basic_solver. 
    Qed.

    Lemma co_restr_iss_in_ex : 
      ⦗ I ⦘ ⨾ Gco ⨾ ⦗ I ⦘ ⊆ e2a □ ⦗ X ⦘ ⨾ Sco ⨾ ⦗ X ⦘.
    Proof. 
      assert (Wf G) as WFG.
      { apply SRC_. }
      assert (ES.Wf S) as WFS.
      { apply SRC_. }
      assert (tc_coherent G sc TC) as TCCOH.
      { apply SRC_. }
      assert (Execution.t S X) as EXEC.
      { apply SRC_. }
      rewrite <- !restr_relE.
      intros x y [GCO [Ix Iy]].
      assert ((e2a □₁ X) x) as e2aXx.
      { apply ex_cov_iss; auto. basic_solver 10. }
      assert ((e2a □₁ X) y) as e2aXy.
      { apply ex_cov_iss; auto. basic_solver 10. }
      destruct e2aXx as [x' [Xx' EQx]].
      destruct e2aXy as [y' [Xy' EQy]].
      assert ((restr_rel SE (same_loc Slab)) x' y') as HH.
      { eapply same_lab_u2v_dom_same_loc.
        { eapply e2a_lab; eauto. apply SRC_. }
        red. unfold compose. splits; auto.
        { red. unfold loc. 
          apply wf_col; auto. 
          congruence. }
        { eapply Execution.ex_inE; eauto. }
        eapply Execution.ex_inE; eauto. }
      destruct HH as [SLOC [SEx' SEy']].
      do 2 eexists; splits; eauto.
      red; splits; auto.
      edestruct Execution.co_total
        as [SCO | SCO].
      1-2 : eauto.      
      { unfolder; splits.
        { apply Xx'. }
        { eapply same_lab_u2v_dom_is_w.
          { eapply e2a_lab; eauto. apply SRC_. }
          split; auto.
          unfold compose, is_w.
          apply wf_coD in GCO; auto.
          generalize GCO. basic_solver. }
        done. }
      { unfolder; splits.
        { apply Xy'. }
        { eapply same_lab_u2v_dom_is_w.
          { eapply e2a_lab; eauto. apply SRC_. }
          split; auto.
          unfold compose, is_w.
          apply wf_coD in GCO; auto.
          generalize GCO. basic_solver. }
        done. }
      { intros NEQ. subst.
        eapply co_irr; eauto. } 
      { done. }
      exfalso. eapply co_irr; eauto.
      eapply co_trans; eauto.
      eapply e2a_co; [apply SRC_|].
      basic_solver 10. 
    Qed.

    (******************************************************************************)
    (** ** rs/release/sw/hb properties  *)
    (******************************************************************************)

    Lemma rel_ew_e2a_iss_cov :
      dom_rel (Srelease ⨾ Sew ⨾ ⦗ e2a ⋄₁ I ⦘) ⊆₁ e2a ⋄₁ C.
    Proof. 
      unfold set_map.
      rewrite seq_eqv_r.
      intros x [z [y [REL [EW Iz]]]].
      eapply dom_release_issued; try apply SRC_.
      unfolder; do 2 eexists; splits; eauto.
      arewrite (e2a z = e2a y).
      { symmetry. eapply e2a_ew; [apply SRC_|]. basic_solver 10. }
      eapply e2a_release; try apply SRC_.
      basic_solver 10.
    Qed.

    Lemma rel_ew_ex_iss_cov :
      dom_rel (Srelease ⨾ Sew ⨾ ⦗ X ∩₁ e2a ⋄₁ I ⦘) ⊆₁ X ∩₁ e2a ⋄₁ C.
    Proof. 
      apply set_subset_inter_r. 
      split; [admit|].
      arewrite (X ∩₁ e2a ⋄₁ I ⊆₁ e2a ⋄₁ I).
      { basic_solver. }
      apply rel_ew_e2a_iss_cov.
    Admitted.

    Lemma rel_in_ex_cov_rel_sb : 
      Srelease ⊆ ⦗ X ∩₁ e2a ⋄₁ C ⦘ ⨾ Srelease ∪ Ssb^?. 
    Proof.
      assert (ES.Wf S) as WFS.
      { apply SRC_. }
      arewrite (Srelease ⊆ ⦗X ∩₁ e2a ⋄₁ C ∪₁ set_compl (X ∩₁ e2a ⋄₁ C)⦘ ⨾ Srelease).
      { rewrite set_compl_union_id. by rewrite seq_id_l. }
      rewrite id_union, seq_union_l. 
      apply union_mori; [done|].
      unfold release at 1, rs. 
      rewrite <- !seqA.
      intros x y [z [HH JFRMW]].
      apply clos_rt_rtn1 in JFRMW.
      induction JFRMW as [|y w [u [JF RMW]]].
      { generalize WFS.(ES.sb_trans) HH. basic_solver 10. }
      apply ES.jfi_union_jfe in JF. destruct JF as [JF|JF].
      { apply WFS.(ES.rmwi) in RMW. red in JF. 
        generalize WFS.(ES.sb_trans) IHJFRMW JF RMW. basic_solver 10. }
      exfalso.
      assert (~ (X ∩₁ e2a ⋄₁ C) x) as CC.
      { generalize HH. basic_solver 10. }
      apply CC. eapply rel_ew_ex_iss_cov; eauto.
      assert (dom_rel (Sew ⨾ ⦗ X ∩₁ e2a ⋄₁ I ⦘) y) as [yy DD].
      { eapply jfe_ex_iss; auto. eexists. eauto. }
      eexists. eexists. split; eauto.
      unfold release, rs. apply clos_rtn1_rt in JFRMW.
      generalize HH JFRMW. basic_solver 40.
    Qed.

    Lemma sw_in_ex_cov_sw_sb : 
      Ssw ⊆ ⦗ X ∩₁ e2a ⋄₁ C ⦘ ⨾ Ssw ∪ Ssb. 
    Proof.
      assert (ES.Wf S) as WFS.
      { apply SRC_. }
      arewrite (Ssw ⊆ ⦗X ∩₁ e2a ⋄₁ C ∪₁ set_compl (X ∩₁ e2a ⋄₁ C)⦘ ⨾ Ssw).
      { rewrite set_compl_union_id. by rewrite seq_id_l. }
      rewrite id_union, seq_union_l. 
      apply union_mori; [done|].
      unfold sw.
      arewrite (⦗set_compl (X ∩₁ e2a ⋄₁ C)⦘ ⨾ Srelease ⨾ Sjf ⊆ Ssb).
      2: { generalize WFS.(ES.sb_trans). basic_solver. }
      rewrite ES.jfi_union_jfe. 
      rewrite !seq_union_r. unionL.
      { rewrite <- seqA.
        erewrite eqv_l_set_compl_eqv_l.
        2 : apply rel_in_ex_cov_rel_sb.
        unfold ES.jfi.
        generalize WFS.(ES.sb_trans). basic_solver. }
      intros x y HH.
      destruct_seq_l HH as DX. 
      exfalso. apply DX.
      destruct HH as [z [REL RFE]].
      eapply rel_ew_ex_iss_cov; eauto.
      assert (dom_rel (Sew ⨾ ⦗X ∩₁ e2a ⋄₁ I⦘) z) as [zz DD].
      { apply jfe_ex_iss; auto. eexists. eauto. }
      eexists. eexists. eauto.
    Qed.

    Lemma hb_in_ex_cov_hb_sb :
      Shb ⊆ ⦗ X ∩₁ e2a ⋄₁ C ⦘ ⨾ Shb ∪ Ssb.
    Proof.
      assert (ES.Wf S) as WFS.
      { apply SRC_. }
      arewrite (Shb ⊆ ⦗X ∩₁ e2a ⋄₁ C ∪₁ set_compl (X ∩₁ e2a ⋄₁ C)⦘ ⨾ Shb).
      { rewrite set_compl_union_id. by rewrite seq_id_l. }
      rewrite id_union, seq_union_l. 
      apply union_mori; [done|].
      intros x y HH. 
      destruct_seq_l HH as DX.
      red in HH. apply clos_trans_tn1 in HH.
      induction HH as [y [|HH]|y z [HH|HH]]; auto.
      { eapply eqv_l_set_compl_eqv_l.
        { apply sw_in_ex_cov_sw_sb. }
        basic_solver. }
      all: eapply ES.sb_trans; eauto.
      eapply eqv_l_set_compl_eqv_l.
      { apply sw_in_ex_cov_sw_sb. }
      apply seq_eqv_l.
      split; auto.
      red. intros CC. apply DX.
      eapply sb_ex_cov. 
      basic_solver 10.
    Qed.

  End SimRelCommonProps.

End SimRel.

Section SimRelLemmas.

  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable X : actid -> eventid.

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

  Notation "'thread_syntax' tid"  := 
    (Language.syntax (thread_lts tid)) (at level 10, only parsing).  

  Notation "'thread_st' tid" := 
    (Language.state (thread_lts tid)) (at level 10, only parsing).

  Notation "'thread_init_st' tid" := 
    (Language.init (thread_lts tid)) (at level 10, only parsing).
  
  Notation "'thread_cont_st' tid" :=
    (fun st => existT _ (thread_lts tid) st) (at level 10, only parsing).

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

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Notation "'Gfurr'" := (furr G sc).

  Lemma simrel_init 
        (nInitProg : ~ IdentMap.In tid_init prog)
        (PExec : program_execution prog G)
        (WF : Execution.Wf G)
        (CONS : imm_consistent G sc) : 
    let Sinit := prog_g_es_init prog G in
    simrel prog Sinit G sc (init_trav G) (ES.acts_set Sinit).
  Proof.
    clear S TC X.
    assert (simrel_e2a (prog_g_es_init prog G) G sc) as HH.
    { by apply simrel_e2a_init. }
    simpls.
    red. splits.
    2: by apply prog_g_es_init_consistent.
    constructor; auto.
    { apply prog_g_es_init_wf. }
    { apply init_trav_coherent; auto. }
    { constructor.
      3: basic_solver. 
      { admit. }
      simpls. ins.
      apply rmw_from_non_init in RMW; auto.
      (* trivial *)
      admit. }
    { constructor.
      { basic_solver. }
      { unfold ES.acts_init_set. basic_solver. }
      { unfold prog_g_es_init, ES.init. basic_solver. }
      { unfold sw, prog_g_es_init, ES.init. basic_solver. }
      { unfold prog_g_es_init, ES.init. basic_solver. }
      { admit. }
      { red. admit. }
      admit. }
    { constructor.
      all: admit. }
    { simpls.
      admit. }
    { (* It should follow from HH. *)
      admit. }
    { simpls. rewrite WF.(rmw_in_sb). rewrite no_sb_to_init.
      basic_solver. }
    { unfold prog_g_es_init, ES.init. basic_solver. }
    { unfold ES.jfe, prog_g_es_init, ES.init. basic_solver. }
    unfold prog_g_es_init, ES.init. basic_solver.
  Admitted.

End SimRelLemmas.
