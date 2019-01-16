Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CombRelations SimTraversal SimulationRel AuxRel.
Require Import AuxRel AuxDef EventStructure Consistency EventToAction LblStep 
         SimRelCont SimRelEventToAction. 

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelSubExec. 
  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.

  Variable a2e : actid -> eventid.
  Variable a2eD : actid -> Prop.

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
  Notation "'Secf'" := (S.(Consistency.ecf)).

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

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Notation "'Gvf'" := (furr G sc).

  Record simrel_subexec :=
    { exec_sb_prcl : dom_rel (Ssb ⨾ ⦗ a2e □₁ a2eD ⦘) ⊆₁ a2e □₁ a2eD;
      exec_ncf : ES.cf_free S (a2e □₁ a2eD);
      exec_rfc : (a2e □₁ a2eD) ∩₁ SR ⊆₁ codom_rel (⦗ a2e □₁ a2eD ⦘ ⨾ Srf);

      exec_jfeI : dom_rel Sjfe ⊆₁ dom_rel (Sew^? ⨾ ⦗ a2e □₁ I ⦘);
      exec_ewI  : dom_rel Sew  ⊆₁ dom_rel (Sew^? ⨾ ⦗ a2e □₁ I ⦘);
      
      exec_rel_iss_cov : dom_rel (Srelease ⨾ Sew^? ⨾ ⦗ a2e □₁ I ⦘) ⊆₁ a2e □₁ C;
    }.

  Section SimRelSubExecProps. 
    Variable GPROG : program_execution prog G.
    Variable PROG_NINIT : ~ (IdentMap.In tid_init prog).

    Variable WF : ES.Wf S.
    Variable TCCOH : tc_coherent G sc TC.
    Variable SRSE : simrel_subexec.

    Lemma exec_rfeI :
      dom_rel Srfe ⊆₁ dom_rel (Sew^? ⨾ ⦗ a2e □₁ I ⦘).
    Proof.
      unfold ES.rfe, ES.rf, ES.jfe.
      rewrite crE at 1.
      rewrite seq_union_l, !minus_union_l, dom_union, seq_id_l.
      unionL.
      { etransitivity; [|by apply SRSE.(exec_jfeI)].
        unfold ES.jfe. basic_solver. }
      intros x [y [[[z [EW JF]] CC] NSB]].
      assert (~ Ssb z y) as AA.
      { intros SB. apply CC.
        apply ES.cf_sb_in_cf; auto.
        eexists. split; eauto.
        apply ES.ewc; auto. }
      edestruct SRSE.(exec_jfeI) as [v HH].
      { eexists. split; eauto. }
      destruct_seq_r HH as BB.
      eexists.  apply seq_eqv_r. split; [|by eauto].
      generalize WF.(ES.ew_trans) EW HH. basic_solver.
    Qed.

    Lemma exec_rel_nCsb : ⦗ set_compl (a2e □₁ C) ⦘ ⨾ Srelease ⊆ Ssb^?.
    Proof.
      unfold release at 1, rs. rewrite <- !seqA.
      intros x y [z [HH RFRMW]].
      apply clos_rt_rtn1 in RFRMW.
      induction RFRMW as [|y w [u [RF RMW]]].
      { generalize WF.(ES.sb_trans) HH. basic_solver 10. }
      apply ES.rfi_union_rfe in RF. destruct RF as [RF|RF].
      { apply WF.(ES.rmwi) in RMW. red in RF. 
        generalize WF.(ES.sb_trans) IHRFRMW RF RMW. basic_solver 10. }
      exfalso.
      assert (~ (a2e □₁ C) x) as CC.
      { generalize HH. basic_solver 10. }
      apply CC. eapply exec_rel_iss_cov; eauto.
      assert (dom_rel (Sew^? ⨾ ⦗ a2e □₁ I ⦘) y) as [yy DD].
      { apply exec_rfeI; auto. eexists. eauto. }
      eexists. eexists. split; eauto.
      unfold release, rs. apply clos_rtn1_rt in RFRMW.
      generalize HH RFRMW. basic_solver 40.
    Qed.

    Lemma exec_rel_in_Crel_sb : Srelease ⊆ ⦗ a2e □₁ C ⦘ ⨾ Srelease ∪ Ssb^?. 
    Proof.
      arewrite (Srelease ⊆ ⦗a2e □₁ C ∪₁ set_compl (a2e □₁ C)⦘ ⨾ Srelease).
      { rewrite set_compl_union_id. by rewrite seq_id_l. }
      rewrite id_union, seq_union_l. apply union_mori; [done|].
      apply exec_rel_nCsb; auto.
    Qed.

    Lemma exec_rel_ewD (CinD : C ⊆₁ a2eD) : 
      dom_rel (Srelease ⨾ Sew^? ⨾ ⦗ a2e □₁ a2eD ⦘) ⊆₁ a2e □₁ a2eD.  
    Proof.
      rewrite crE. rewrite !seq_union_l, !seq_union_r, dom_union, seq_id_l.
      unionL.
      { rewrite exec_rel_in_Crel_sb, CinD.
        generalize exec_sb_prcl. basic_solver 10. }
      arewrite (dom_rel (Srelease ⨾ Sew ⨾ ⦗ a2e □₁ a2eD ⦘) ⊆₁
                dom_rel (Srelease ⨾ Sew^? ⨾ ⦗ a2e □₁ I ⦘)).
      2: { rewrite exec_rel_iss_cov; eauto. by rewrite CinD. }
      rewrite <- seqA.
      intros x [y HH].
      destruct_seq_r HH as HD.
      destruct HH as [z [REL EW]].
      edestruct exec_ewI as [a AA]; eauto.
      { red. eauto. }
      exists a.
      generalize REL AA. basic_solver 10.
    Qed.

    Lemma exec_sw_nCsb : ⦗ set_compl (a2e □₁ C) ⦘ ⨾ Ssw ⊆ Ssb. 
    Proof.
      unfold sw.
      arewrite (⦗set_compl (a2e □₁ C)⦘ ⨾ Srelease ⨾ Srf ⊆ Ssb).
      2: { generalize WF.(ES.sb_trans). basic_solver. }
      rewrite ES.rfi_union_rfe. rewrite !seq_union_r. unionL.
      { sin_rewrite exec_rel_nCsb; auto. unfold ES.rfi.
        generalize WF.(ES.sb_trans). basic_solver. }
      intros x y HH.
      destruct_seq_l HH as DX. exfalso. apply DX.
      destruct HH as [z [REL RFE]].
      eapply exec_rel_iss_cov; eauto.
      assert (dom_rel (Sew^? ⨾ ⦗ a2e □₁ I ⦘) z) as [zz DD].
      { apply exec_rfeI; auto. eexists. eauto. }
      eexists. eexists. eauto.
    Qed.

    Lemma SsbD_in_Gsb 
          (SRE2A : simrel_e2a S G sc)
          (SRA2E : simrel_a2e S a2e a2eD) :
      Ssb ⨾ ⦗ a2e □₁ a2eD ⦘ ⊆ a2e □ Gsb.
    Proof.
      arewrite (Ssb ⨾ ⦗ a2e □₁ a2eD ⦘ ⊆ ⦗ a2e □₁ a2eD ⦘ ⨾ Ssb ⨾ ⦗ a2e □₁ a2eD ⦘). 
      { intros x y HH. apply seq_eqv_l. split; auto.
        eapply exec_sb_prcl; eauto. eexists. eauto. }
      rewrite <- restr_relE.
      rewrite <- collect_rel_fixset. 
      2 : eapply fixset_swap; apply SRA2E.
      rewrite <- collect_rel_compose.
      apply collect_rel_mori; auto.
      rewrite inclusion_restr.
      eapply e2a_sb; eauto. apply SRE2A. 
    Qed.

    Lemma sbC_dom 
          (CinD : C ⊆₁ a2eD) 
          (SRE2A : simrel_e2a S G sc)
          (SRA2E : simrel_a2e S a2e a2eD) :
      dom_rel (Ssb ⨾ ⦗ a2e □₁ C ⦘) ⊆₁ a2e □₁ C.
    Proof.
      rewrite <- seq_eqvK.
      sin_rewrite CinD.
      sin_rewrite SsbD_in_Gsb; auto.
      rewrite <- set_collect_eqv.
      rewrite <- collect_rel_seq_r.
      2: { sin_rewrite CinD. rewrite dom_eqv. apply SRA2E. }
      rewrite sb_covered; eauto.
      basic_solver.
    Qed.

    Lemma sb_nC_nC 
          (CinD : C ⊆₁ a2eD) 
          (SRE2A : simrel_e2a S G sc)
          (SRA2E : simrel_a2e S a2e a2eD) :
      codom_rel (⦗ set_compl (a2e □₁ C) ⦘ ⨾ Ssb) ⊆₁ set_compl (a2e □₁ C).
    Proof.
      intros x [y HH]. destruct_seq_l HH as DX.
      intros DY. apply DX.
      apply sbC_dom; auto. eexists. apply seq_eqv_r. eauto.
    Qed.

    Lemma exec_hb_nCsb 
          (CinD : C ⊆₁ a2eD) 
          (SRE2A : simrel_e2a S G sc)
          (SRA2E : simrel_a2e S a2e a2eD) :
      ⦗ set_compl (a2e □₁ C) ⦘ ⨾ Shb ⊆ Ssb. 
    Proof.
      intros x y HH. destruct_seq_l HH as DX.
      red in HH. apply clos_trans_tn1 in HH.
      induction HH as [y [|HH]|y z [HH|HH]]; auto.
      { apply exec_sw_nCsb; auto. by apply seq_eqv_l. }
      all: eapply ES.sb_trans; eauto.
      apply exec_sw_nCsb; auto. apply seq_eqv_l. split; auto.
      apply sb_nC_nC; auto.
      eexists. apply seq_eqv_l. eauto.
    Qed.

    Lemma exec_hb_in_Chb_sb 
          (CinD : C ⊆₁ a2eD) 
          (SRE2A : simrel_e2a S G sc)
          (SRA2E : simrel_a2e S a2e a2eD) :           
      Shb ⊆ ⦗ a2e □₁ C ⦘ ⨾ Shb ∪ Ssb. 
    Proof.
      arewrite (Shb ⊆ ⦗a2e □₁ C ∪₁ set_compl (a2e □₁ C)⦘ ⨾ Shb).
      { rewrite set_compl_union_id. by rewrite seq_id_l. }
      rewrite id_union, seq_union_l. apply union_mori; [done|].
      apply exec_hb_nCsb; auto.
    Qed.

    Lemma exec_hbD
          (CinD : C ⊆₁ a2eD) 
          (SRE2A : simrel_e2a S G sc)
          (SRA2E : simrel_a2e S a2e a2eD) :           
      dom_rel (Shb ⨾ ⦗ a2e □₁ a2eD ⦘) ⊆₁ a2e □₁ a2eD.  
    Proof.
      rewrite exec_hb_in_Chb_sb; auto.
      rewrite seq_union_l, dom_union. unionL.
      2: by eapply exec_sb_prcl; eauto.
      rewrite CinD. basic_solver.
    Qed.

    Lemma exec_hb_release_ewD 
          (CinD : C ⊆₁ a2eD) 
          (SRE2A : simrel_e2a S G sc)
          (SRA2E : simrel_a2e S a2e a2eD) :
      dom_rel (Shb^? ⨾ Srelease ⨾ Sew^? ⨾ ⦗ a2e □₁ a2eD ⦘) ⊆₁ a2e □₁ a2eD.  
    Proof. 
      rewrite crE with (r := Shb). 
      relsf. split. 
      { by apply exec_rel_ewD. }
      intros x [y [z [HB REL]]].
      eapply exec_hbD; auto. 
      eexists. apply seq_eqv_r. split; eauto.
      apply exec_rel_ewD; auto. basic_solver.
    Qed.

    Lemma himg_necf 
          (CinD : C ⊆₁ a2eD) 
          (SRE2A : simrel_e2a S G sc)
          (SRA2E : simrel_a2e S a2e a2eD) : 
      restr_rel (a2e □₁ a2eD) Secf ⊆ ∅₂.
    Proof. 
      unfold restr_rel, ecf. 
      intros a b [ECF [Hx Hy]].
      destruct ECF as [c [tHB [d [CF HB]]]].
      eapply exec_ncf; eauto. 
      apply restr_relE. unfold restr_rel.
      splits; eauto. 
      { unfolder in tHB; desf. 
        eapply exec_hbD; auto. basic_solver 10. }
      unfolder in HB; desf. 
      eapply exec_hbD; auto. basic_solver 10.
    Qed.

  End SimRelSubExecProps.

End SimRelSubExec.
