Require Import Program.Basics Omega.
Require Import Coq.Logic.FunctionalExtensionality Classical_Prop.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb SimulationRel
     CombRelations AuxRel.
Require Import AuxRel AuxDef EventStructure Construction Consistency LblStep
        EventToAction ImmProperties.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRel.
  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G  : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable f  : actid -> eventid.

  Notation "'SE'" := S.(ES.acts_set).
  Notation "'SEinit'" := S.(ES.acts_init_set).
  Notation "'SEninit'" := S.(ES.acts_ninit_set).
  Notation "'Stid'" := (S.(ES.tid)).
  Notation "'Slab'" := (S.(ES.lab)).
  Notation "'Sloc'" := (loc S.(ES.lab)).
  Notation "'K'"  := S.(ES.cont_set).

  Notation "'STid' t" := (fun x => Stid x = t) (at level 1).

  Notation "'Ssb'" := (S.(ES.sb)).
  Notation "'Srmw'" := (S.(ES.rmw)).
  Notation "'Sjf'" := (S.(ES.jf)).
  Notation "'Sjfe'" := (S.(ES.jfe)).
  Notation "'Srf'" := (S.(ES.rf)).
  Notation "'Srfi'" := (S.(ES.rfi)).
  Notation "'Srfe'" := (S.(ES.rfe)).
  Notation "'Sco'" := (S.(ES.co)).
  Notation "'Scf'" := (S.(ES.cf)).
  Notation "'Sew'" := (S.(ES.ew)).

  Notation "'Srs'" := (S.(Consistency.rs)).
  Notation "'Srelease'" := (S.(Consistency.release)).
  Notation "'Ssw'" := (S.(Consistency.sw)).
  Notation "'Shb'" := (S.(Consistency.hb)).

  Notation "'SR'" := (fun a => is_true (is_r Slab a)).
  Notation "'SW'" := (fun a => is_true (is_w Slab a)).
  Notation "'SF'" := (fun a => is_true (is_f Slab a)).
  Notation "'SRel'" := (fun a => is_true (is_rel Slab a)).
  
  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).

  Notation "'Glab'" := (G.(lab)).
  Notation "'Gloc'" := (loc G.(lab)).
  Notation "'Gtid'" := (tid).
  Notation "'Grmw'" := G.(rmw).
  
  Notation "'GTid' t" := (fun x => tid x = t) (at level 1).
  Notation "'GNTid' t" := (fun x => tid x <> t) (at level 1).

  Notation "'GR'" := (fun a => is_true (is_r Glab a)).
  Notation "'GW'" := (fun a => is_true (is_w Glab a)).
  Notation "'GF'" := (fun a => is_true (is_f Glab a)).
  Notation "'GRel'" := (fun a => is_true (is_rel Glab a)).
  
  Notation "'Gsb'" := (G.(sb)).
  Notation "'Grf'" := (G.(rf)).
  Notation "'Gco'" := (G.(co)).

  Notation "'Grs'" := (G.(imm_s_hb.rs)).
  Notation "'Grelease'" := (G.(imm_s_hb.release)).
  Notation "'Ghb'" := (G.(imm_s_hb.hb)).

  Notation "'Gvf'" := (furr G sc).

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Notation "'g'" := (e2a S). 

  Definition pc thread :=
    C ∩₁ GTid thread \₁ dom_rel (Gsb ⨾ ⦗ C ⦘).

  Definition thread_lts (tid : thread_id) : Language.t :=
    @Language.mk
      (list Instr.t) state
      init
      is_terminal
      (ilbl_step tid).

  Notation "'thread_syntax' tid"  := 
    (Language.syntax (thread_lts tid)) (at level 10, only parsing).  

  Notation "'thread_st' tid" := 
    (Language.state (thread_lts tid)) (at level 10, only parsing).

  Notation "'thread_init_st' tid" := 
    (Language.init (thread_lts tid)) (at level 10, only parsing).
  
  Notation "'thread_cont_st' tid" :=
    (fun st => existT _ (thread_lts tid) st) (at level 10, only parsing).

  Record simrel_graph := 
    { gprclos : forall thread m n (LT : m < n) (EE : GE (ThreadEvent thread n)),
          GE (ThreadEvent thread m);
      rmwclos : forall r w (RMW : Grmw r w), C r <-> C w;
      irelcov : GW ∩₁ GRel ∩₁ I ⊆₁ C;
    }.

  Record simrel_cont :=
    { contlang : forall k lang (state : lang.(Language.state))
                        (INK : K (k, existT _ lang state)),
        lang = thread_lts (ES.cont_thread S k);

      contwf : forall k (state : thread_st (ES.cont_thread S k))
                        (INK : K (k, thread_cont_st (ES.cont_thread S k) state)),
          wf_thread_state (ES.cont_thread S k) state;

      contstable : forall k (state : thread_st (ES.cont_thread S k))
                          (INK : K (k, thread_cont_st (ES.cont_thread S k) state)), 
          stable_state (ES.cont_thread S k) state;

      contrun : forall thread (lprog : thread_syntax thread) 
                        (INPROG : IdentMap.find thread prog = Some lprog),
          exists (state : thread_st thread),
            ⟪ INK : K (CInit thread, thread_cont_st thread state) ⟫ /\
            ⟪ INITST : (istep thread [])＊ (thread_init_st thread lprog) state⟫;

      continit : forall thread (state : thread_st thread)
                        (INKi : K (CInit thread, thread_cont_st thread state)),
          state.(eindex) = 0;

      contseqn : forall e (state : thread_st (Stid e))
                        (INKe : K (CEvent e, thread_cont_st (Stid e) state)),
          state.(eindex) = 1 + ES.seqn S e;

      contpc : forall e (state : (thread_st (Gtid e)))
                      (PC : pc (Gtid e) e)
                      (INK : K (CEvent (f e), thread_cont_st (Gtid e) state)),
                @sim_state G sim_normal C (Gtid e) state;
    }.

  Lemma contstateE (SRC : simrel_cont) :
    forall cont thread (state : thread_st thread)
           (INK : K (cont, thread_cont_st thread state)),
      state.(ProgToExecution.G).(acts_set) ≡₁ g □₁ ES.cont_sb_dom S cont.
  Proof.
    
    (* It should follow from `contseqn` *)
  Admitted.
     
  Notation "'fdom'" := (C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘)) (only parsing).

  Record simrel_common :=
    { noinitprog : ~ IdentMap.In tid_init prog;
      gprog : program_execution prog G;
      
      gwf   : Execution.Wf G;
      swf   : ES.Wf S;
      
      gcons : imm_consistent G sc;
      scons : @es_consistent S Weakestmo;

      tccoh : tc_coherent G sc TC;
      
      sr_cont : simrel_cont;
      sr_graph : simrel_graph;

      gE : g □₁ SE ⊆₁ GE;
      gEinit : GEinit ⊆₁ g □₁ SEinit;

      grmw : g □ Srmw ⊆ Grmw;
      gjf  : g □ Sjf  ⊆ Gvf;
      gew  : g □ Sew  ⊆ ⦗I⦘;
      gco  : g □ Sco  ⊆ Gco;
      
      grfrmw : g □ (Srf ⨾ Srmw) ⊆ Grf ⨾ Grmw;

      fco : f □ ⦗ fdom ⦘ ⨾ Gco ⨾ ⦗ fdom ⦘ ⊆ Sco;

      fimgNcf : ES.cf_free S (f □₁ fdom);
      
      complete_fdom :
        (f □₁ fdom) ∩₁ SR ⊆₁ codom_rel (⦗ f □₁ fdom ⦘ ⨾ Srf);

      gffix : fixset fdom (g ∘ f);

      finj : inj_dom_s fdom f;  
      fimg : f □₁ fdom ⊆₁ SE;
      foth : (f □₁ set_compl fdom) ∩₁ SE ≡₁ ∅;
      flab : eq_dom (C ∪₁ I) (Slab ∘ f) Glab;

      glab : same_lab_u2v_dom SE Slab (Glab ∘ g);

      finitIncl : SEinit ⊆₁ f □₁ GEinit;

      vis  : f □₁ fdom ⊆₁ vis S;
    }.
  
  Record simrel :=
    { src : simrel_common;
      gE_trav : g □₁ SE ⊆₁ fdom;
      jfefI  : dom_rel Sjfe ⊆₁ dom_rel (Sew^? ⨾ ⦗ f □₁ I ⦘);

      release_issf_cov : dom_rel (Srelease ⨾ Sew^? ⨾ ⦗ f □₁ I ⦘) ⊆₁ f □₁ C;
    }.

  Section Properties.
    Variable SRC : simrel_common.

    Lemma e2a_same_Einit : 
      e2a S □₁ SEinit ≡₁ GEinit.
    Proof. 
      split; [eapply e2a_Einit; apply SRC|].
      unfolder. intros a [INITa GEa].
      edestruct gEinit as [e [[INITe SEe] gEQ]].
      1-2 : unfolder; eauto.  
      eexists; splits; eauto. 
    Qed.

    Lemma basic_step_e2a_cont_sb_dom e k (st : thread_st (ES.cont_thread S k)) 
          (kE : k = CEvent e)
          (INK : K (k, thread_cont_st (ES.cont_thread S k) st)) :
      g □₁ ES.cont_sb_dom S k ≡₁ dom_rel (⦗ GTid (Stid e) ⦘ ⨾ Gsb^? ⨾ ⦗ eq (g e) ⦘).
    Proof. 
      edestruct SRC. ins.
      assert (SE e) as SEe.
      { subst k. edestruct ES.K_inEninit; eauto. }
      assert (GE (e2a S e)) as GEe.
      { apply gE; auto. unfolder. eauto. }
      assert (wf_thread_state (ES.cont_thread S k) st) as WFT.
      { eapply contwf; eauto. }
      rewrite <- contstateE; eauto. 
      erewrite e2a_ninit in *; auto.
      2,3 : subst k; eapply ES.K_inEninit; eauto. 
      split. 
      { unfold acts_set. intros a ACT.
        eapply acts_rep in ACT; eauto.
        desf. unfolder. unfold ES.cont_thread.
        do 2 eexists; split; eauto.
        exists (ThreadEvent (Stid e) (ES.seqn S e)).
        split; eauto.
        erewrite contseqn in LE; eauto.
        apply lt_n_Sm_le, le_lt_or_eq in LE.
        destruct LE as [LT | EQ]; auto.
        right. unfold sb, ext_sb. apply seq_eqv_lr.
        splits; auto.
        eapply gprclos; eauto. }
      unfolder.
      intros x [y [TIDx [[EQ | SB] EQy]]]; subst y.         
      { subst k x. unfold acts_set. apply acts_clos; auto.
        erewrite contseqn; eauto. }
      destruct x. 
      { exfalso. eapply ES.init_tid_K; eauto.
        do 2 eexists; splits; eauto.
        subst k. unfold ES.cont_thread.
        unfold tid in TIDx. by symmetry. }
      subst k. 
      unfold acts_set. apply acts_clos; auto.
      { unfold tid in TIDx. by rewrite TIDx. }
      unfold sb, ext_sb in SB. apply seq_eqv_lr in SB.
      erewrite contseqn; eauto.
      desf; omega.
    Qed.

    Lemma issuedSbE : dom_rel (Gsb^? ⨾ ⦗I⦘) ⊆₁ GE.
    Proof.
      rewrite (dom_l G.(wf_sbE)).
      rewrite issuedE; [|by apply SRC].
      basic_solver.
    Qed.
    
    Lemma fdomE : fdom ⊆₁ GE.
    Proof.
      destruct SRC.
      erewrite coveredE; eauto.
      apply set_subset_union_l; split; auto.
      apply issuedSbE.
    Qed.

    Lemma fE e (SEE : SE (f e)) : GE e.
    Proof.
      apply fdomE.
      apply NNPP. intros NN.
      eapply SRC.(foth).
      split; eauto.
      red. eexists. splits; eauto.
    Qed.

    Lemma ginjfdom : inj_dom (f □₁ fdom) g.
    Proof. eapply e2a_inj; apply SRC. Qed.

    Lemma ginjfC : inj_dom (f □₁ C) g.
    Proof.
      eapply inj_dom_mori; eauto.
      2: by apply ginjfdom.
      red. basic_solver.
    Qed.

    Lemma grf : g □ Srf ≡ g □ Sjf.
    Proof.
      destruct SRC.
      split.
      2: by rewrite jf_in_rf; eauto.
      unfold ES.rf.
      arewrite (Sew^? ⨾ Sjf \ Scf ⊆ Sew^? ⨾ Sjf).
      rewrite crE.
      rewrite seq_union_l.
      rewrite collect_rel_union.
      apply inclusion_union_l.
      { by rewrite seq_id_l. }
      unfolder.
      ins. desf.
      eexists. eexists. splits; eauto.
      apply SRC.(gew).
      eexists. eexists.
      splits.
      { eapply ES.ew_sym; eauto. }
      all: by eauto.
    Qed.
    
    Lemma sbtot_fdom thread (NINIT : thread <> tid_init) :
      is_total (f □₁ fdom ∩₁ STid thread) Ssb.
    Proof.
      red. ins.
      apply NNPP. intros NN.
      eapply SRC.(fimgNcf).
      apply seq_eqv_l; split.
      { apply IWa. }
      apply seq_eqv_r; split.
      2: { apply IWb. }
      red.
      apply seq_eqv_l; split.
      { unfold ES.acts_ninit_set, ES.acts_init_set, set_minus; splits.
        { apply SRC.(fimg). apply IWa. }
        red. intros [_ INITa].
        edestruct IWa as [_ INITa'].
        desf. }
      apply seq_eqv_r; split.
      { split.
        { red. red in IWa. red in IWb.
          desf. }
        red. intros [AA|[AA|AA]]; desf.
        all: apply NN; auto. }
      unfold ES.acts_ninit_set, ES.acts_init_set, set_minus; splits.
      { apply SRC.(fimg). apply IWb. }
      red. intros [_ INITb].
      edestruct IWb as [_ INITb'].
      desf.
    Qed.

    Ltac g_type t :=
      intros x [y HH]; desf;
      eapply t in HH;
        [|by apply same_lab_u2v_dom_comm; apply SRC];
      split; [apply SRC.(gE); red; eexists; split; eauto|]; apply HH.

    Lemma gW : g □₁ (SE ∩₁ SW) ⊆₁ GE ∩₁ GW.
    Proof. g_type same_lab_u2v_dom_is_w. Qed.

    Lemma gF : g □₁ (SE ∩₁ SF) ⊆₁ GE ∩₁ GF.
    Proof. g_type same_lab_u2v_dom_is_f. Qed.

    Lemma gRel : g □₁ (SE ∩₁ SRel) ⊆₁ GE ∩₁ GRel.
    Proof. g_type same_lab_u2v_dom_is_rel. Qed.
    
    Lemma gsame_loc : g □ restr_rel SE (same_loc Slab) ⊆ restr_rel GE (same_loc Glab).
    Proof.
      intros x y HH. red in HH. desf.
      eapply same_lab_u2v_dom_same_loc in HH.
      2: { apply same_lab_u2v_dom_comm. apply SRC. }
      red in HH. desf. 
      red. splits.
      apply HH.
      all: by apply gE; auto; eexists; eauto.
    Qed.

    Lemma grs : g □ Srs ⊆ Grs. 
    Proof. 
      assert (ES.Wf S) as WF by apply SRC.
      rewrite rs_alt; auto.
      rewrite !collect_rel_seqi.
      rewrite !set_collect_eqv.
      rewrite !gW.
      repeat apply seq_mori; eauto with hahn.
      2: { rewrite collect_rel_crt. auto using clos_refl_trans_mori, grfrmw. }
      rewrite ES.sbE; auto.
      rewrite wf_sbE.
      rewrite <- !restr_relE.
      rewrite <- restr_inter_absorb_r.
      rewrite <- restr_inter_absorb_r with (r':=same_loc Slab).
      rewrite collect_rel_cr.
      rewrite collect_rel_interi. 
      apply clos_refl_mori, inter_rel_mori. 
      { rewrite !restr_relE, <- wf_sbE, <- ES.sbE; auto. 
        eapply e2a_sb; eauto; apply SRC. }
      apply gsame_loc.
    Qed.

    Lemma grelease : g □ Srelease ⊆ Grelease.
    Proof. 
      rewrite release_alt; [|by apply SRC].
      rewrite !collect_rel_seqi, !collect_rel_cr, !collect_rel_seqi.
      rewrite !set_collect_eqv.
      arewrite (SF ∪₁ SW ⊆₁ fun _ => True).
      arewrite (SE ∩₁ (fun _ : eventid => True) ⊆₁ SE) by basic_solver.
      rewrite gRel, grs, e2a_sb, gF.
      { unfold imm_s_hb.release. basic_solver 10. }
      all: eauto; apply SRC.
    Qed.
 
    Lemma flaboth :
          same_lab_u2v_dom fdom (Slab ∘ f) Glab.
    Proof.
      (* TODO. It should follow from glab and definition of g. *)
    Admitted.
    
    Lemma cont_tid_state thread (INP : IdentMap.In thread prog):
      exists (state : (thread_lts thread).(Language.state)) c,
        ⟪ QQ : K (c, existT _ _ state) ⟫ /\
        ⟪ QTID : thread = ES.cont_thread S c  ⟫ /\
        ⟪ CsbqDOM : g □₁ ES.cont_sb_dom S c ⊆₁ covered TC ⟫ /\
        ⟪ SSTATE : @sim_state G sim_normal C thread state ⟫.
    Proof.
      destruct SRC.
      destruct (IdentMap.find thread prog) as [lprog|] eqn:AA.
      2: { apply IdentMap.Facts.in_find_iff in INP. desf. }
      destruct (classic (exists e, pc thread e)) as [[e PC]|NPC].
      2: { edestruct (continit (sr_cont SRC)) as [state]; eauto.
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
          by apply rmwclos with (r:=e) (w:=w). }
      assert (~ dom_rel Srmw (f e)) as NSRMW.
      { intros [w RMW].
        apply NRMW. exists (g w).
        apply SRC.(grmw).
        arewrite (e = g (f e)).
        { symmetry. apply SRC.(gffix). basic_solver. }
        unfolder. eauto. }
      assert (~ GEinit e) as NINIT.
      { intros [BB]. unfold is_init in BB. desf. }
      assert (~ SEinit (f e)) as NSINIT.
      { intros BB. apply NINIT.
        apply SRC.(finitIncl) in BB.
        red in BB. desf.
        assert (y = e); desf.
        apply SRC.(finj); auto. by left. }
      eapply ES.event_K in NSRMW; eauto.
      destruct NSRMW as [[lang state] KK].
      assert (lang = thread_lts (ES.cont_thread S (CEvent (f e)))); subst.
      { eapply contlang; eauto. }
      assert (Stid (f e) = Gtid e) as TT.
      { arewrite (Stid (f e) = (Stid ∘ f) e).
        erewrite a2e_tid; eauto. 
        basic_solver. }
      simpls. rewrite TT in KK.
      eapply contpc in PC; eauto.
      eexists. eexists.
      splits; eauto.
      unfold ES.cont_sb_dom. simpls.
      rewrite set_collect_dom.
      rewrite collect_seq_eqv_r.
      rewrite collect_eq.
      arewrite (g (f e) = e).
      { apply SRC.(gffix). basic_solver. }
      rewrite crE.
      rewrite collect_rel_union.
      rewrite seq_union_l.
      rewrite dom_union.
      apply set_subset_union_l.
      split; [basic_solver|].
      rewrite e2a_sb.
      arewrite (eq e ⊆₁ C).
      { intros x HH. desf. }
      eapply dom_sb_covered; eauto.
      admit. 
      (* apply fimg; auto. *)
      (* generalize CE. basic_solver. *)
    Admitted.

  End Properties.
End SimRel.