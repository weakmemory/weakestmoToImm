Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CombRelations SimTraversal SimulationRel AuxRel.
Require Import AuxRel AuxDef ImmProperties 
        EventStructure Consistency EventToAction LblStep 
        CertGraph CertRf SimRelCont SimRelEventToAction.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRel.
  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable f : actid -> eventid.

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

      sr_e2a : simrel_e2a S G;
      sr_a2e_f : simrel_a2e S f (C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘));
      
      flab : eq_dom (C ∪₁ I) (Slab ∘ f) Glab;
      fvis : f □₁ fdom ⊆₁ vis S;
      finitIncl : SEinit ⊆₁ f □₁ GEinit;

      fD_rfc : (f □₁ fdom) ∩₁ SR ⊆₁ codom_rel (⦗ f □₁ fdom ⦘ ⨾ Srf);

      fGrmwC : f □ (Grmw ⨾ ⦗ C ⦘) ⊆ Srmw ;
      fGrfC  : f □ (Grf ⨾ ⦗ C ⦘) ⊆ Srf ;
      fGcoI  : f □ (⦗ I ⦘ ⨾ Gco ⨾ ⦗ I ⦘) ⊆ Sco ;

      jfe_fI : dom_rel Sjfe ⊆₁ dom_rel (Sew ⨾ ⦗ f □₁ I ⦘);
      ew_fI  : dom_rel (Sew \ eq) ⊆₁ dom_rel (Sew ⨾ ⦗ f □₁ I ⦘);

      rel_fI_fC : dom_rel (Srelease ⨾ Sew ⨾ ⦗ f □₁ I ⦘) ⊆₁ f □₁ C;
    }.
  
  Record simrel :=
    { src : simrel_common;
      gE_trav : (e2a S) □₁ SE ⊆₁ fdom;
      jfefI  : dom_rel Sjfe ⊆₁ dom_rel (Sew^? ⨾ ⦗ f □₁ I ⦘);

      release_issf_cov : dom_rel (Srelease ⨾ Sew^? ⨾ ⦗ f □₁ I ⦘) ⊆₁ f □₁ C;
    }.

  Section SimRelCommonProps. 
    
    Variable SRC : simrel_common.

    Lemma fimgInit : 
      SEinit ≡₁ f □₁ GEinit. 
    Proof. admit. Admitted.

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
      f □₁ I ⊆₁ SE ∩₁ SW.
    Proof.
      intros x HH. 
      assert ((f □₁ fdom) x) as fDx.
      { generalize HH. basic_solver 10. }
      assert (SE x) as SEx.
      { eapply a2e_img; [apply SRC|]. done. }
      split; auto. 
      eapply same_lab_u2v_dom_is_w.
      { eapply e2a_lab. apply SRC. }
      split; auto.
      unfold is_w, compose.
      destruct HH as [a [Ia EQx]]. subst x.
      fold (compose (e2a S) f a).
      erewrite a2e_fix; [|apply SRC|].
      { fold (is_w Glab a).
        eapply issuedW; eauto.
        apply SRC. }
      generalize Ia. basic_solver 10.
    Qed.

    Lemma e2af_fixI : 
      fixset I ((e2a S) ∘ f). 
    Proof. 
      eapply fixset_mori; 
        [| eauto | eapply SRC]. 
      red. basic_solver 10.
    Qed.

    Lemma e2a_inj_ffdom : 
      inj_dom (f □₁ fdom) (e2a S).
    Proof. eapply e2a_inj; apply SRC. Qed.

    Lemma e2a_inj_fC : 
      inj_dom (f □₁ C) (e2a S).
    Proof.
      eapply inj_dom_mori; eauto.
      2: by apply e2a_inj_ffdom.
      red. basic_solver.
    Qed.
    
    Lemma e2a_ewI : 
      (e2a S) □ (Sew \ eq)  ⊆ ⦗ I ⦘. 
    Proof.
      intros x y HH.
      assert (x = y) as EQxy; subst.
      { eapply e2a_ew; [apply SRC|]. generalize HH. basic_solver 10. }
      split; auto.
      destruct HH as [a [b [EW [EQx EQy]]]]; subst.
      edestruct ew_fI as [x HH]; eauto.
      { eexists; eauto. }
      destruct_seq_r HH as FI.
      red in FI. destruct FI as [y [IY]]; subst.
      assert (e2a S a = compose (e2a S) f y) as XX.
      2: { rewrite XX. by rewrite e2af_fixI. }
      eapply e2a_ew; [apply SRC|].
      eexists; eauto.
    Qed.

    Lemma ew_in_eq_ew_fI_ew : 
      Sew ⊆ eq ∪ Sew ⨾ ⦗f □₁ I⦘ ⨾ Sew.
    Proof. 
      assert (ES.Wf S) as WFS.
      { apply SRC. }
      rewrite <- seqA.
      intros x y EWxy.
      destruct (classic (x = y)) as [EQ | nEQ].
      { basic_solver. }
      right. edestruct ew_fI as [z HH]; auto.
      { basic_solver. }
      eexists; splits; eauto.
      eapply ES.ew_trans; eauto.
      apply ES.ew_sym; auto.
      generalize HH. basic_solver.
    Qed.

    Lemma rfe_fI :
      dom_rel Srfe ⊆₁ dom_rel (Sew ⨾ ⦗ f □₁ I ⦘).
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
      edestruct SRC.(jfe_fI) as [v HH].
      { eexists. split; eauto. }
      destruct_seq_r HH as BB.
      eexists. apply seq_eqv_r. split; [|by eauto].
      generalize WFS.(ES.ew_trans) EW HH. basic_solver.
    Qed.

    Lemma GrmwC_Srmw_fC : 
      ⦗C⦘ ⨾ Grmw ⨾ ⦗C⦘ ⊆ e2a S □ (⦗f □₁ C⦘ ⨾ Srmw ⨾ ⦗f □₁ C⦘).
    Proof. 
      rewrite <- restr_relE.
      erewrite <- collect_rel_fixset
        with (h := e2a S ∘ f).
      { rewrite <- collect_rel_compose.
        apply collect_rel_mori; auto.
        rewrite restr_relE.
        rewrite <- seq_eqvK at 2.
        rewrite collect_rel_seqi, set_collect_eqv.
        apply seq_mori; [done|].
        rewrite <- seqA.
        rewrite collect_rel_seqi, set_collect_eqv.
        apply seq_mori; [|done].
        by apply fGrmwC. }
      eapply fixset_mori; [| auto | apply SRC].
      red. basic_solver.
    Qed.

    Lemma GrfC_Srf_fC : 
      ⦗C⦘ ⨾ Grf ⨾ ⦗C⦘ ⊆ e2a S □ (⦗f □₁ C⦘ ⨾ Srf ⨾ ⦗f □₁ C⦘).
    Proof. 
      rewrite <- restr_relE.
      erewrite <- collect_rel_fixset
        with (h := e2a S ∘ f).
      { rewrite <- collect_rel_compose.
        apply collect_rel_mori; auto.
        rewrite restr_relE.
        rewrite <- seq_eqvK at 2.
        rewrite collect_rel_seqi, set_collect_eqv.
        apply seq_mori; [done|].
        rewrite <- seqA.
        rewrite collect_rel_seqi, set_collect_eqv.
        apply seq_mori; [|done].
        by apply fGrfC. }
      eapply fixset_mori; [| auto | apply SRC].
      red. basic_solver.
    Qed.

    Lemma GcoI_Sco_fI : 
      ⦗I⦘ ⨾ Gco ⨾ ⦗I⦘ ⊆ e2a S □ (⦗f □₁ I⦘ ⨾ Sco ⨾ ⦗f □₁ I⦘).
    Proof. 
      rewrite <- restr_relE.
      erewrite <- collect_rel_fixset
        with (h := e2a S ∘ f).
      { rewrite <- collect_rel_compose.
        apply collect_rel_mori; auto.
        rewrite restr_relE.
        rewrite <- seq_eqvK at 1 2.
        rewrite !seqA.
        rewrite collect_rel_seqi, set_collect_eqv.
        apply seq_mori; [done|].
        do 2 rewrite <- seqA.
        rewrite collect_rel_seqi, set_collect_eqv.
        apply seq_mori; [|done].
        rewrite !seqA.
        by apply fGcoI. }
      eapply fixset_mori; [| auto | apply SRC].
      red. basic_solver 10.
    Qed.

    Lemma sb_fC :
      dom_rel (Ssb ⨾ ⦗ f □₁ C ⦘) ⊆₁ f □₁ C.
    Proof.
      rewrite <- seq_eqvK.
      arewrite (C ⊆₁ fdom).
      arewrite (Ssb ⨾ ⦗f □₁ fdom⦘ ⊆ f □ (Gsb ⨾ ⦗ fdom ⦘)).
      { eapply SsbD_in_GsbD; apply SRC. }
      rewrite <- set_collect_eqv.
      rewrite <- collect_rel_seq.
      { rewrite seqA.
        arewrite (⦗fdom⦘ ⨾ ⦗C⦘ ⊆ ⦗C⦘).
        rewrite sb_covered; eauto.
        { basic_solver. }
        apply SRC. }
      rewrite codom_seq, codom_eqv, dom_eqv.
      eapply inj_dom_mori; [| done | apply SRC].
      red. basic_solver 6.
    Qed.

    Lemma sb_nfC_nfC :
      codom_rel (⦗ set_compl (f □₁ C) ⦘ ⨾ Ssb) ⊆₁ set_compl (f □₁ C).
    Proof.
      intros x [y HH]. destruct_seq_l HH as DX.
      intros DY. apply DX.
      apply sb_fC; auto. eexists. apply seq_eqv_r. eauto.
    Qed.

    Lemma rel_nfCsb : 
      ⦗ set_compl (f □₁ C) ⦘ ⨾ Srelease ⊆ Ssb^?.
    Proof.
      assert (ES.Wf S) as WFS.
      { apply SRC. }
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
      assert (~ (f □₁ C) x) as CC.
      { generalize HH. basic_solver 10. }
      apply CC. eapply rel_fI_fC; eauto.
      assert (dom_rel (Sew ⨾ ⦗ f □₁ I ⦘) y) as [yy DD].
      { eapply jfe_fI; auto. eexists. eauto. }
      eexists. eexists. split; eauto.
      unfold release, rs. apply clos_rtn1_rt in JFRMW.
      generalize HH JFRMW. basic_solver 40.
    Qed.

    Lemma frel_in_Crel_sb : 
      Srelease ⊆ ⦗ f □₁ C ⦘ ⨾ Srelease ∪ Ssb^?. 
    Proof.
      arewrite (Srelease ⊆ ⦗f □₁ C ∪₁ set_compl (f □₁ C)⦘ ⨾ Srelease).
      { rewrite set_compl_union_id. by rewrite seq_id_l. }
      rewrite id_union, seq_union_l. apply union_mori; [done|].
      apply rel_nfCsb; auto.
    Qed.

    Lemma sw_nfCsb : 
      ⦗ set_compl (f □₁ C) ⦘ ⨾ Ssw ⊆ Ssb.
    Proof.
      assert (ES.Wf S) as WFS.
      { apply SRC. }
      unfold sw.
      arewrite (⦗set_compl (f □₁ C)⦘ ⨾ Srelease ⨾ Sjf ⊆ Ssb).
      2: { generalize WFS.(ES.sb_trans). basic_solver. }
      rewrite ES.jfi_union_jfe. rewrite !seq_union_r. unionL.
      { sin_rewrite rel_nfCsb; auto. unfold ES.jfi.
        generalize WFS.(ES.sb_trans). basic_solver. }
      intros x y HH.
      destruct_seq_l HH as DX. exfalso. apply DX.
      destruct HH as [z [REL RFE]].
      eapply rel_fI_fC; eauto.
      assert (dom_rel (Sew ⨾ ⦗ f □₁ I ⦘) z) as [zz DD].
      { apply jfe_fI; auto. eexists. eauto. }
      eexists. eexists. eauto.
    Qed.

    Lemma sw_in_fCsw_sb : 
      Ssw ⊆ ⦗ f □₁ C ⦘ ⨾ Ssw ∪ Ssb. 
    Proof.
      arewrite (Ssw ⊆ ⦗f □₁ C ∪₁ set_compl (f □₁ C)⦘ ⨾ Ssw).
      { rewrite set_compl_union_id. by rewrite seq_id_l. }
      rewrite id_union, seq_union_l. apply union_mori; [done|].
      apply sw_nfCsb; auto.
    Qed.

    Lemma hb_nfCsb :
      ⦗ set_compl (f □₁ C) ⦘ ⨾ Shb ⊆ Ssb.
    Proof.
      assert (ES.Wf S) as WFS.
      { apply SRC. }
      intros x y HH. destruct_seq_l HH as DX.
      red in HH. apply clos_trans_tn1 in HH.
      induction HH as [y [|HH]|y z [HH|HH]]; auto.
      { apply sw_nfCsb; auto. by apply seq_eqv_l. }
      all: eapply ES.sb_trans; eauto.
      apply sw_nfCsb; auto. apply seq_eqv_l. 
      split; auto.
      eapply sb_nfC_nfC; try apply SRC.
      eexists. apply seq_eqv_l. eauto.
    Qed.

    Lemma hb_in_fChb_sb :
      Shb ⊆ ⦗ f □₁ C ⦘ ⨾ Shb ∪ Ssb.
    Proof.
      arewrite (Shb ⊆ ⦗f □₁ C ∪₁ set_compl (f □₁ C)⦘ ⨾ Shb).
      { rewrite set_compl_union_id. by rewrite seq_id_l. }
      rewrite id_union, seq_union_l. apply union_mori; [done|].
      apply hb_nfCsb; auto.
    Qed.

    Lemma hb_fdom_in_fdom : 
      dom_rel (Shb ⨾ ⦗ f □₁ fdom ⦘) ⊆₁ f □₁ fdom.
    Proof. 
      rewrite hb_in_fChb_sb.
      rewrite seq_union_l.
      rewrite dom_union.
      unionL. 
      { rewrite !dom_seq. basic_solver. }
      erewrite a2e_sb_prcl; auto.
      apply SRC.
    Qed.

    Lemma fdom_good_restr : 
      good_restriction S (f □₁ fdom).
    Proof. 
      constructor; try apply SRC.
      apply hb_fdom_in_fdom.
    Qed.      

    Lemma cont_tid_state thread (INP : IdentMap.In thread prog):
      exists (state : (thread_lts thread).(Language.state)) c,
        ⟪ QQ : K (c, existT _ _ state) ⟫ /\
        ⟪ QTID : thread = ES.cont_thread S c  ⟫ /\
        ⟪ CsbqDOM : (e2a S) □₁ ES.cont_sb_dom S c ⊆₁ covered TC ⟫ /\
        ⟪ SSTATE : @sim_state G sim_normal C thread state ⟫.
    Proof.
      destruct SRC.
      destruct (IdentMap.find thread prog) as [lprog|] eqn:AA.
      2: { apply IdentMap.Facts.in_find_iff in INP. desf. }
      destruct (classic (exists e, pc G TC thread e)) as [[e PC]|NPC].
      2: { edestruct continit as [state]; eauto.
           desf. all: admit. 
      (* eexists. eexists.
           splits; eauto.
           { red. ins.
             eapply init_covered; eauto.
               by apply gEinit. }
           red. splits; ins.
           2: { symmetry in AA.
                eapply GPROG in AA. desf.
                cdes AA. exists s.
                red. splits; auto.
                2: by rewrite PEQ.
                admit. }
           (* split; intros XX; [|omega]. *)
           (* exfalso. apply NPC. clear NPC. *)
           admit. *) }
      assert (thread <> tid_init) as NTINIT.
      { intros HH; subst. by apply SRC. }
      assert (thread = Gtid e); subst.
      { red in PC. generalize PC. basic_solver. }
      assert (C e) as CE by apply PC.
      assert (~ dom_rel Grmw e) as NRMW.
      { intros [w RMW].
        eapply PC. exists w.
        apply seq_eqv_r. split.
        { apply rmw_in_sb; auto. }
          eapply rmwclos with (r:=e) (w:=w); eauto. }
      assert (~ dom_rel Srmw (f e)) as NSRMW.
      { intros [w RMW].
        apply NRMW. exists (e2a S w).
        eapply e2a_rmw; eauto.
        arewrite (e = e2a S (f e)).
        { symmetry. admit. (* eapply gffix; eauto. basic_solver. *) }
        unfolder. eauto. }
      assert (~ GEinit e) as NINIT.
      { intros [BB]. unfold is_init in BB. desf. }
      assert (~ SEinit (f e)) as NSINIT.
      { intros BB. apply NINIT.
        eapply finitIncl in BB; eauto. 
        red in BB. desf.
        assert (y = e); desf.
        admit.
        (* apply finj; eauto. by left. *) }
      eapply ES.event_K in NSRMW; eauto.
      destruct NSRMW as [[lang state] KK].
      assert (lang = thread_lts (ES.cont_thread S (CEvent (f e)))); subst.
      { eapply contlang; eauto. }
      assert (Stid (f e) = Gtid e) as TT.
      { arewrite (Stid (f e) = (Stid ∘ f) e).
        erewrite a2e_tid; eauto. 
        admit. (* basic_solver. *) }
      simpls. rewrite TT in KK.
      (* eapply contpc in PC; eauto. *)
      (* eexists. eexists. *)
      (* splits; eauto. *)
      (* unfold ES.cont_sb_dom. simpls. *)
      (* rewrite set_collect_dom. *)
      (* rewrite collect_seq_eqv_r. *)
      (* rewrite collect_eq. *)
      (* arewrite (g (f e) = e). *)
      (* { apply gffix; eauto. basic_solver. } *)
      (* rewrite crE. *)
      (* rewrite collect_rel_union. *)
      (* rewrite seq_union_l. *)
      (* rewrite dom_union. *)
      (* apply set_subset_union_l. *)
      (* split; [basic_solver|]. *)
      (* rewrite e2a_sb. *)
      (* arewrite (eq e ⊆₁ C). *)
      (* { intros x HH. desf. } *)
      (* eapply dom_sb_covered; eauto. *)
      admit. 
      (* apply fimg; auto. *)
      (* generalize CE. basic_solver. *)
    Admitted.

  End SimRelCommonProps.

End SimRel.

Section SimRelLemmas.

  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable f : actid -> eventid.

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
    simrel_common prog (ES.init prog) G sc (init_trav G) a2e_init.
  Proof. clear S TC f. admit. Admitted.

End SimRelLemmas.
