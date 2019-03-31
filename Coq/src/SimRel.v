Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CombRelations SimTraversal SimulationRel AuxRel.
Require Import AuxRel AuxDef ImmProperties 
        EventStructure Consistency Execution EventToAction 
        LblStep SimRelCont SimRelEventToAction.

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

  Notation "'e2a'" := (e2a S).

  Record simrel_graph := 
    { gprclos : forall thread m n (LT : m < n) (EE : GE (ThreadEvent thread n)),
        GE (ThreadEvent thread m);
      rmwclos : forall r w (RMW : Grmw r w), C r <-> C w;
      irelcov : GW ∩₁ GRel ∩₁ I ⊆₁ C;
    }.

  Notation "'fdom'" := (C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘)) (only parsing).
  
  Record simrel_common :=
    { noinitprog : ~ IdentMap.In tid_init prog;
      gprog : program_execution prog G;
      
      gwf   : Execution.Wf G;
      swf   : ES.Wf S;
      
      gcons : imm_consistent G sc;
      scons : @es_consistent S Weakestmo;

      tccoh : tc_coherent G sc TC;
      
      sr_cont : simrel_cont prog S G TC;
      sr_graph : simrel_graph;

      sr_e2a : simrel_e2a S G sc;

      sr_exec : Execution.t S X ;
      
      (* initIn : SEinit ⊆₁ e2a ⋄₁ GEinit ; *)

      labCI : eq_dom (X ∩₁ e2a ⋄₁ (C ∪₁ I)) Slab (Glab ∘ e2a);

      rmwC : Grmw ⨾ ⦗ C ⦘ ⊆ e2a □ (Srmw ⨾ ⦗ X ⦘) ;
      rfC  : Grf ⨾ ⦗ C ⦘ ⊆ e2a □ (Srf ⨾ ⦗ X ⦘) ;
      coI  : ⦗ I ⦘ ⨾ Gco ⨾ ⦗ I ⦘ ⊆ e2a □ (⦗ X ⦘ ⨾ Sco ⨾ ⦗ X ⦘) ;

      jfe_ex_iss : dom_rel Sjfe ⊆₁ dom_rel (Sew ⨾ ⦗ X ∩₁ e2a ⋄₁ I ⦘);
      ew_ex_iss  : dom_rel (Sew \ eq) ⊆₁ dom_rel (Sew ⨾ ⦗ X ∩₁ e2a ⋄₁ I ⦘);

      rel_ew_ex_iss : dom_rel (Srelease ⨾ Sew ⨾ ⦗ X ∩₁ e2a ⋄₁ I ⦘) ⊆₁ X ;
    }.
  
  (* Record simrel := *)
  (*   { src : simrel_common; *)
  (*     gE_trav : e2a □₁ SE ⊆₁ fdom; *)
  (*     jfefI  : dom_rel Sjfe ⊆₁ dom_rel (Sew^? ⨾ ⦗ f □₁ I ⦘); *)

  (*     release_issf_cov : dom_rel (Srelease ⨾ Sew^? ⨾ ⦗ f □₁ I ⦘) ⊆₁ f □₁ C; *)
  (*   }. *)

  Section SimRelCommonProps. 
    
    Variable SRC : simrel_common.

    Lemma fdomE : 
      fdom ⊆₁ GE.
    Proof.
      assert (tc_coherent G sc TC) as TCCOH. 
      { apply SRC. }
      erewrite coveredE; eauto.
      erewrite issuedE; eauto.
      rewrite (dom_l G.(wf_sbE)).
      basic_solver.
    Qed.

    Lemma fI_EW : 
      X ∩₁ e2a ⋄₁ I ⊆₁ SW.
    Proof.
      unfolder.
      intros x [xX xI].
      unfold is_w.
      erewrite labCI; auto.
      { unfold compose.
        eapply issuedW; eauto.
        apply SRC. }
      basic_solver.
    Qed.

    (* Lemma e2af_fixI :  *)
    (*   fixset I ((e2a S) ∘ f).  *)
    (* Proof.  *)
    (*   eapply fixset_mori;  *)
    (*     [| eauto | eapply SRC].  *)
    (*   red. basic_solver 10. *)
    (* Qed. *)

    (* Lemma e2a_inj_ffdom :  *)
    (*   inj_dom (f □₁ fdom) (e2a S). *)
    (* Proof. eapply e2a_inj; apply SRC. Qed. *)

    (* Lemma e2a_inj_fC :  *)
    (*   inj_dom (f □₁ C) (e2a S). *)
    (* Proof. *)
    (*   eapply inj_dom_mori; eauto. *)
    (*   2: by apply e2a_inj_ffdom. *)
    (*   red. basic_solver. *)
    (* Qed. *)
    
    Lemma e2a_ew_iss : 
      e2a □ (Sew \ eq)  ⊆ ⦗ I ⦘. 
    Proof.
      intros x y HH.
      assert (x = y) as EQxy; subst.
      { eapply e2a_ew; [apply SRC|]. generalize HH. basic_solver 10. }
      split; auto.
      destruct HH as [a [b [EW [EQx EQy]]]]; subst.
      edestruct ew_ex_iss as [x HH]; eauto.
      { eexists; eauto. }
      destruct_seq_r HH as FI.
      red in FI. destruct FI as [y IY]; subst.
      unfolder in IY.
      arewrite (e2a a = e2a x); auto.
      eapply e2a_ew; [apply SRC|].
      eexists; eauto.
    Qed.

    Lemma ew_in_eq_ew_ex_iss_ew : 
      Sew ⊆ eq ∪ Sew ⨾ ⦗X ∩₁ e2a ⋄₁ I⦘ ⨾ Sew.
    Proof. 
      assert (ES.Wf S) as WFS.
      { apply SRC. }
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

    Lemma rfe_ex_iss :
      dom_rel Srfe ⊆₁ dom_rel (Sew ⨾ ⦗X ∩₁ e2a ⋄₁ I⦘).
    Proof.
      assert (ES.Wf S) as WFS.
      { apply SRC. }
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
      edestruct SRC.(jfe_ex_iss) as [v HH].
      { eexists. split; eauto. }
      destruct_seq_r HH as BB.
      eexists. apply seq_eqv_r. split; [|by eauto].
      generalize WFS.(ES.ew_trans) EW HH. basic_solver.
    Qed.

    Lemma GrmwC_Srmw_fC : 
      ⦗C⦘ ⨾ Grmw ⨾ ⦗C⦘ ⊆ e2a □ (⦗X⦘ ⨾ Srmw ⨾ ⦗X⦘).
    Proof. admit. Admitted.
    (*   rewrite <- restr_relE. *)
    (*   erewrite <- collect_rel_fixset *)
    (*     with (h := e2a S ∘ f). *)
    (*   { rewrite <- collect_rel_compose. *)
    (*     apply collect_rel_mori; auto. *)
    (*     rewrite restr_relE. *)
    (*     rewrite <- seq_eqvK at 2. *)
    (*     rewrite collect_rel_seqi, set_collect_eqv. *)
    (*     apply seq_mori; [done|]. *)
    (*     rewrite <- seqA. *)
    (*     rewrite collect_rel_seqi, set_collect_eqv. *)
    (*     apply seq_mori; [|done]. *)
    (*     by apply fGrmwC. } *)
    (*   eapply fixset_mori; [| auto | apply SRC]. *)
    (*   red. basic_solver. *)
    (* Qed. *)

    Lemma GrfC_Srf_fC : 
      ⦗C⦘ ⨾ Grf ⨾ ⦗C⦘ ⊆ e2a □ (⦗X⦘ ⨾ Srf ⨾ ⦗X⦘).
    Proof. admit. Admitted.
    (*   rewrite <- restr_relE. *)
    (*   erewrite <- collect_rel_fixset *)
    (*     with (h := e2a S ∘ f). *)
    (*   { rewrite <- collect_rel_compose. *)
    (*     apply collect_rel_mori; auto. *)
    (*     rewrite restr_relE. *)
    (*     rewrite <- seq_eqvK at 2. *)
    (*     rewrite collect_rel_seqi, set_collect_eqv. *)
    (*     apply seq_mori; [done|]. *)
    (*     rewrite <- seqA. *)
    (*     rewrite collect_rel_seqi, set_collect_eqv. *)
    (*     apply seq_mori; [|done]. *)
    (*     by apply fGrfC. } *)
    (*   eapply fixset_mori; [| auto | apply SRC]. *)
    (*   red. basic_solver. *)
    (* Qed. *)

    Lemma GcoI_Sco_fI : 
      ⦗I⦘ ⨾ Gco ⨾ ⦗I⦘ ⊆ e2a □ (⦗X⦘ ⨾ Sco ⨾ ⦗X⦘).
    Proof. admit. Admitted.
    (*   rewrite <- restr_relE. *)
    (*   erewrite <- collect_rel_fixset *)
    (*     with (h := e2a S ∘ f). *)
    (*   { rewrite <- collect_rel_compose. *)
    (*     apply collect_rel_mori; auto. *)
    (*     rewrite restr_relE. *)
    (*     rewrite <- seq_eqvK at 1 2. *)
    (*     rewrite !seqA. *)
    (*     rewrite collect_rel_seqi, set_collect_eqv. *)
    (*     apply seq_mori; [done|]. *)
    (*     do 2 rewrite <- seqA. *)
    (*     rewrite collect_rel_seqi, set_collect_eqv. *)
    (*     apply seq_mori; [|done]. *)
    (*     rewrite !seqA. *)
    (*     by apply fGcoI. } *)
    (*   eapply fixset_mori; [| auto | apply SRC]. *)
    (*   red. basic_solver 10. *)
    (* Qed. *)

    Lemma sb_e2a_cov :
      dom_rel (Ssb ⨾ ⦗ e2a ⋄₁ C ⦘) ⊆₁ e2a ⋄₁ C.
    Proof.
      unfold set_map.
      rewrite seq_eqv_r.
      intros x [y [SB Cy]].
      eapply dom_sb_covered; [apply SRC|].
      unfolder; do 2 eexists; splits; eauto.
      eapply e2a_sb; try apply SRC.
      basic_solver 10.
    Qed.

    Lemma sb_ex_cov :
      dom_rel (Ssb ⨾ ⦗ X ∩₁ e2a ⋄₁ C ⦘) ⊆₁ X ∩₁ e2a ⋄₁ C.
    Proof.
      rewrite seq_eqv_r.
      intros x [y [SB [Xy Cy]]].
      split.
      { eapply Execution.ex_sb_prcl; [apply SRC|]. basic_solver 10. }
      eapply sb_e2a_cov. basic_solver 10.
    Qed.

    Lemma rel_ew_e2a_iss_cov :
      dom_rel (Srelease ⨾ Sew ⨾ ⦗ e2a ⋄₁ I ⦘) ⊆₁ e2a ⋄₁ C.
    Proof. 
      unfold set_map.
      rewrite seq_eqv_r.
      intros x [z [y [REL [EW Iz]]]].
      eapply dom_release_issued; try apply SRC.
      unfolder; do 2 eexists; splits; eauto.
      arewrite (e2a z = e2a y).
      { symmetry. eapply e2a_ew; [apply SRC|]. basic_solver 10. }
      eapply e2a_release; try apply SRC.
      basic_solver 10.
    Qed.

    Lemma rel_ew_ex_iss_cov :
      dom_rel (Srelease ⨾ Sew ⨾ ⦗ X ∩₁ e2a ⋄₁ I ⦘) ⊆₁ X ∩₁ e2a ⋄₁ C.
    Proof. 
      apply set_subset_inter_r. 
      split; [apply SRC|].
      arewrite (X ∩₁ e2a ⋄₁ I ⊆₁ e2a ⋄₁ I).
      { basic_solver. }
      apply rel_ew_e2a_iss_cov.
    Qed.

    Lemma rel_in_ex_cov_rel_sb : 
      Srelease ⊆ ⦗ X ∩₁ e2a ⋄₁ C ⦘ ⨾ Srelease ∪ Ssb^?. 
    Proof.
      assert (ES.Wf S) as WFS.
      { apply SRC. }
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

    (* Lemma sb_nfC_nfC : *)
    (*   codom_rel (⦗ set_compl (e2a ⋄₁ C) ⦘ ⨾ Ssb) ⊆₁ set_compl (e2a ⋄₁ C). *)
    (* Proof. *)
    (*   intros x [y HH]. destruct_seq_l HH as DX. *)
    (*   intros DY. apply DX. *)
    (*   apply sbC; auto. eexists. apply seq_eqv_r. eauto. *)
    (* Qed. *)

    (* Lemma rel_nfCsb :  *)
    (*   ⦗ set_compl (f □₁ C) ⦘ ⨾ Srelease ⊆ Ssb^?. *)
    (* Proof. *)
    (*   assert (ES.Wf S) as WFS. *)
    (*   { apply SRC. } *)
    (*   unfold release at 1, rs.  *)
    (*   rewrite <- !seqA. *)
    (*   intros x y [z [HH JFRMW]]. *)
    (*   apply clos_rt_rtn1 in JFRMW. *)
    (*   induction JFRMW as [|y w [u [JF RMW]]]. *)
    (*   { generalize WFS.(ES.sb_trans) HH. basic_solver 10. } *)
    (*   apply ES.jfi_union_jfe in JF. destruct JF as [JF|JF]. *)
    (*   { apply WFS.(ES.rmwi) in RMW. red in JF.  *)
    (*     generalize WFS.(ES.sb_trans) IHJFRMW JF RMW. basic_solver 10. } *)
    (*   exfalso. *)
    (*   assert (~ (f □₁ C) x) as CC. *)
    (*   { generalize HH. basic_solver 10. } *)
    (*   apply CC. eapply rel_fI_fC; eauto. *)
    (*   assert (dom_rel (Sew ⨾ ⦗ f □₁ I ⦘) y) as [yy DD]. *)
    (*   { eapply jfe_fI; auto. eexists. eauto. } *)
    (*   eexists. eexists. split; eauto. *)
    (*   unfold release, rs. apply clos_rtn1_rt in JFRMW. *)
    (*   generalize HH JFRMW. basic_solver 40. *)
    (* Qed. *)

    (* Lemma frel_in_Crel_sb :  *)
    (*   Srelease ⊆ ⦗ f □₁ C ⦘ ⨾ Srelease ∪ Ssb^?.  *)
    (* Proof. *)
    (*   arewrite (Srelease ⊆ ⦗f □₁ C ∪₁ set_compl (f □₁ C)⦘ ⨾ Srelease). *)
    (*   { rewrite set_compl_union_id. by rewrite seq_id_l. } *)
    (*   rewrite id_union, seq_union_l. apply union_mori; [done|]. *)
    (*   apply rel_nfCsb; auto. *)
    (* Qed. *)

    (* Lemma sw_nfCsb :  *)
    (*   ⦗ set_compl (f □₁ C) ⦘ ⨾ Ssw ⊆ Ssb. *)
    (* Proof. *)
    (*   assert (ES.Wf S) as WFS. *)
    (*   { apply SRC. } *)
    (*   unfold sw. *)
    (*   arewrite (⦗set_compl (f □₁ C)⦘ ⨾ Srelease ⨾ Sjf ⊆ Ssb). *)
    (*   2: { generalize WFS.(ES.sb_trans). basic_solver. } *)
    (*   rewrite ES.jfi_union_jfe. rewrite !seq_union_r. unionL. *)
    (*   { sin_rewrite rel_nfCsb; auto. unfold ES.jfi. *)
    (*     generalize WFS.(ES.sb_trans). basic_solver. } *)
    (*   intros x y HH. *)
    (*   destruct_seq_l HH as DX. exfalso. apply DX. *)
    (*   destruct HH as [z [REL RFE]]. *)
    (*   eapply rel_fI_fC; eauto. *)
    (*   assert (dom_rel (Sew ⨾ ⦗ f □₁ I ⦘) z) as [zz DD]. *)
    (*   { apply jfe_fI; auto. eexists. eauto. } *)
    (*   eexists. eexists. eauto. *)
    (* Qed. *)

    Lemma sw_in_ex_cov_sw_sb : 
      Ssw ⊆ ⦗ X ∩₁ e2a ⋄₁ C ⦘ ⨾ Ssw ∪ Ssb. 
    Proof.
      assert (ES.Wf S) as WFS.
      { apply SRC. }
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

    (* Lemma hb_nfCsb : *)
    (*   ⦗ set_compl (f □₁ C) ⦘ ⨾ Shb ⊆ Ssb. *)
    (* Proof. *)
    (*   assert (ES.Wf S) as WFS. *)
    (*   { apply SRC. } *)
    (*   intros x y HH. destruct_seq_l HH as DX. *)
    (*   red in HH. apply clos_trans_tn1 in HH. *)
    (*   induction HH as [y [|HH]|y z [HH|HH]]; auto. *)
    (*   { apply sw_nfCsb; auto. by apply seq_eqv_l. } *)
    (*   all: eapply ES.sb_trans; eauto. *)
    (*   apply sw_nfCsb; auto. apply seq_eqv_l.  *)
    (*   split; auto. *)
    (*   eapply sb_nfC_nfC; try apply SRC. *)
    (*   eexists. apply seq_eqv_l. eauto. *)
    (* Qed. *)

    Lemma hb_in_ex_cov_hb_sb :
      Shb ⊆ ⦗ X ∩₁ e2a ⋄₁ C ⦘ ⨾ Shb ∪ Ssb.
    Proof.
      assert (ES.Wf S) as WFS.
      { apply SRC. }
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

    (* Lemma hb_fdom_in_fdom :  *)
    (*   dom_rel (Shb ⨾ ⦗ f □₁ fdom ⦘) ⊆₁ f □₁ fdom. *)
    (* Proof.  *)
    (*   rewrite hb_in_fChb_sb. *)
    (*   rewrite seq_union_l. *)
    (*   rewrite dom_union. *)
    (*   unionL.  *)
    (*   { rewrite !dom_seq. basic_solver. } *)
    (*   erewrite a2e_sb_prcl; auto. *)
    (*   apply SRC. *)
    (* Qed. *)

    (* Lemma fdom_good_restr :  *)
    (*   good_restriction S (f □₁ fdom). *)
    (* Proof.  *)
    (*   constructor; try apply SRC. *)
    (*   apply hb_fdom_in_fdom. *)
    (* Qed.       *)

    (* Lemma cont_tid_state thread (INP : IdentMap.In thread prog): *)
    (*   exists (state : (thread_lts thread).(Language.state)) c, *)
    (*     ⟪ QQ : K (c, existT _ _ state) ⟫ /\ *)
    (*     ⟪ QTID : thread = ES.cont_thread S c  ⟫ /\ *)
    (*     ⟪ CsbqDOM : e2a □₁ ES.cont_sb_dom S c ⊆₁ covered TC ⟫ /\ *)
    (*     ⟪ SSTATE : @sim_state G sim_normal C thread state ⟫. *)
    (* Proof. *)
    (*   destruct SRC. *)
    (*   destruct (IdentMap.find thread prog) as [lprog|] eqn:AA. *)
    (*   2: { apply IdentMap.Facts.in_find_iff in INP. desf. } *)
    (*   destruct (classic (exists e, pc G TC thread e)) as [[e PC]|NPC]. *)
    (*   2: { edestruct continit as [state]; eauto. *)
    (*        desf. all: admit.  *)
    (*   (* eexists. eexists. *)
    (*        splits; eauto. *)
    (*        { red. ins. *)
    (*          eapply init_covered; eauto. *)
    (*            by apply gEinit. } *)
    (*        red. splits; ins. *)
    (*        2: { symmetry in AA. *)
    (*             eapply GPROG in AA. desf. *)
    (*             cdes AA. exists s. *)
    (*             red. splits; auto. *)
    (*             2: by rewrite PEQ. *)
    (*             admit. } *)
    (*        (* split; intros XX; [|omega]. *) *)
    (*        (* exfalso. apply NPC. clear NPC. *) *)
    (*        admit. *) } *)
    (*   assert (thread <> tid_init) as NTINIT. *)
    (*   { intros HH; subst. by apply SRC. } *)
    (*   assert (thread = Gtid e); subst. *)
    (*   { red in PC. generalize PC. basic_solver. } *)
    (*   assert (C e) as CE by apply PC. *)
    (*   assert (~ dom_rel Grmw e) as NRMW. *)
    (*   { intros [w RMW]. *)
    (*     eapply PC. exists w. *)
    (*     apply seq_eqv_r. split. *)
    (*     { apply rmw_in_sb; auto. } *)
    (*       eapply rmwclos with (r:=e) (w:=w); eauto. } *)
    (*   assert (~ dom_rel Srmw (f e)) as NSRMW. *)
    (*   { intros [w RMW]. *)
    (*     apply NRMW. exists (e2a S w). *)
    (*     eapply e2a_rmw; eauto. *)
    (*     arewrite (e = e2a S (f e)). *)
    (*     { symmetry. admit. (* eapply gffix; eauto. basic_solver. *) } *)
    (*     unfolder. eauto. } *)
    (*   assert (~ GEinit e) as NINIT. *)
    (*   { intros [BB]. unfold is_init in BB. desf. } *)
    (*   assert (~ SEinit (f e)) as NSINIT. *)
    (*   { intros BB. apply NINIT. *)
    (*     eapply finitIncl in BB; eauto.  *)
    (*     red in BB. desf. *)
    (*     assert (y = e); desf. *)
    (*     admit. *)
    (*     (* apply finj; eauto. by left. *) } *)
    (*   eapply ES.event_K in NSRMW; eauto. *)
    (*   destruct NSRMW as [[lang state] KK]. *)
    (*   assert (lang = thread_lts (ES.cont_thread S (CEvent (f e)))); subst. *)
    (*   { eapply contlang; eauto. } *)
    (*   assert (Stid (f e) = Gtid e) as TT. *)
    (*   { arewrite (Stid (f e) = (Stid ∘ f) e). *)
    (*     erewrite a2e_tid; eauto.  *)
    (*     admit. (* basic_solver. *) } *)
    (*   simpls. rewrite TT in KK. *)
    (*   (* eapply contpc in PC; eauto. *) *)
    (*   (* eexists. eexists. *) *)
    (*   (* splits; eauto. *) *)
    (*   (* unfold ES.cont_sb_dom. simpls. *) *)
    (*   (* rewrite set_collect_dom. *) *)
    (*   (* rewrite collect_seq_eqv_r. *) *)
    (*   (* rewrite collect_eq. *) *)
    (*   (* arewrite (g (f e) = e). *) *)
    (*   (* { apply gffix; eauto. basic_solver. } *) *)
    (*   (* rewrite crE. *) *)
    (*   (* rewrite collect_rel_union. *) *)
    (*   (* rewrite seq_union_l. *) *)
    (*   (* rewrite dom_union. *) *)
    (*   (* apply set_subset_union_l. *) *)
    (*   (* split; [basic_solver|]. *) *)
    (*   (* rewrite e2a_sb. *) *)
    (*   (* arewrite (eq e ⊆₁ C). *) *)
    (*   (* { intros x HH. desf. } *) *)
    (*   (* eapply dom_sb_covered; eauto. *) *)
    (*   admit.  *)
    (*   (* apply fimg; auto. *) *)
    (*   (* generalize CE. basic_solver. *) *)
    (* Admitted. *)

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

  Lemma simrel_init 
        (nInitProg : ~ IdentMap.In tid_init prog)
        (PExec : program_execution prog G)
        (WF : Execution.Wf G)
        (CONS : imm_consistent G sc) : 
    let Sinit := ES.init prog in
    simrel_common prog Sinit G sc (init_trav G) (ES.acts_set Sinit).
  Proof. clear S TC X. admit. Admitted.

End SimRelLemmas.
