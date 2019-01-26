Require Import Program.Basics Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CombRelations SimTraversal SimTraversalProperties SimulationRel AuxRel CertExecution2.
Require Import AuxRel AuxDef EventStructure Consistency EventToAction LblStep 
        CertGraph CertRf ImmProperties 
        SimRelDef SimRelCert SimRelCont SimRelEventToAction SimRelSubExec. 

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelProps.

  Variable prog : Prog.t.

  Variable S : ES.t.

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

  Notation "'g'" := (e2a S). 

  Notation "'thread_syntax' tid"  := 
    (Language.syntax (thread_lts tid)) (at level 10, only parsing).  

  Notation "'thread_st' tid" := 
    (Language.state (thread_lts tid)) (at level 10, only parsing).

  Notation "'thread_init_st' tid" := 
    (Language.init (thread_lts tid)) (at level 10, only parsing).
  
  Notation "'thread_cont_st' tid" :=
    (fun st => existT _ (thread_lts tid) st) (at level 10, only parsing).

  Variable G : execution.

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

  Variable TC : trav_config.

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Variable sc : relation actid.

  Notation "'Gvf'" := (furr G sc).

  Variable f : actid -> eventid.

  Notation "'fdom'" := (C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘)) (only parsing).

  Section SimRelCommonProps. 
    
    Variable SRC : simrel_common prog S G sc TC f. 

    Lemma fimgInit : 
      SEinit ≡₁ f □₁ GEinit. 
    Proof. admit. Admitted.

    Lemma fdomE : fdom ⊆₁ GE.
    Proof.
      assert (tc_coherent G sc TC) as TCCOH. 
      { apply SRC. }
      erewrite coveredE; eauto.
      erewrite issuedE; eauto.
      rewrite (dom_l G.(wf_sbE)).
      basic_solver.
    Qed.

    Lemma gf_fixI : fixset I (g ∘ f). 
    Proof. 
      eapply fixset_mori; 
        [| eauto | eapply SRC]. 
      red. basic_solver 10.
    Qed.

    Lemma ginjfdom : inj_dom (f □₁ fdom) g.
    Proof. eapply e2a_inj; apply SRC. Qed.

    Lemma ginjfC : inj_dom (f □₁ C) g.
    Proof.
      eapply inj_dom_mori; eauto.
      2: by apply ginjfdom.
      red. basic_solver.
    Qed.
    
    Lemma gewI : g □ Sew  ⊆ ⦗ I ⦘. 
    Proof.
      intros x y HH.
      assert (x = y) as EQxy; subst.
      { eapply e2a_ew; eauto. apply SRC. }
      split; auto.
      destruct HH as [a [b [EW [EQx EQy]]]]; subst.
      edestruct exec_ewI as [x HH]; eauto.
      { apply SRC. }
      { eexists; eauto. }
      destruct_seq_r HH as FI.
      red in FI. destruct FI as [y [IY]]; subst.
      destruct HH as [HH|HH]; subst.
      { fold (compose g f y).
        by rewrite gf_fixI. }
      assert (g a = compose g f y) as XX.
      2: { rewrite XX. by rewrite gf_fixI. }
      eapply e2a_ew; [apply SRC|].
      eexists; eauto.
    Qed.

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
        apply NRMW. exists (g w).
        eapply e2a_rmw; eauto.
        arewrite (e = g (f e)).
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

End SimRelProps.