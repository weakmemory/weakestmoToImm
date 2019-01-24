Require Import Program.Basics Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CombRelations SimTraversal SimTraversalProperties SimulationRel AuxRel CertExecution2.
Require Import AuxRel AuxDef EventStructure Consistency EventToAction LblStep 
        CertGraph CertRf ImmProperties 
        SimRelDef SimRelCont SimRelEventToAction SimRelSubExec. 

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

  Section SimRelCertProps. 

    Variable TC': trav_config.

    Notation "'C''"  := (covered TC').
    Notation "'I''"  := (issued TC').

    Variable h : actid -> eventid.

    Variable q : cont_label.

    Notation "'qtid'" := (ES.cont_thread S q) (only parsing).

    (* A state in a continuation related to q in S. *)
    Variable state : ProgToExecution.state.

    (* A state, which is reachable from 'state' and which represents a graph certification. *)
    Variable state' : ProgToExecution.state.

    Notation "'E0'" := (E0 G TC' qtid).

    Notation "'new_rf'" := (cert_rf G sc TC' qtid).
    
    Notation "'contG'" := state.(ProgToExecution.G).
    Notation "'certG'" := state'.(ProgToExecution.G).

    Notation "'contE'" := contG.(acts_set).
    Notation "'certE'" := certG.(acts_set).

    Notation "'certLab'" := (certLab G state').

    Notation "'hdom'" :=  (cert_dom G TC (ES.cont_thread S q) state) (only parsing).

    Lemma C_in_hdom : C ⊆₁ hdom.
    Proof. unfold cert_dom. basic_solver. Qed.

    Lemma GEinit_in_hdom (TCCOH : tc_coherent G sc TC) : 
      GEinit ⊆₁ hdom. 
    Proof. 
      etransitivity; [|apply C_in_hdom].
      eapply init_covered; eauto. 
    Qed.

    Variable SRCC : simrel_cert prog S G sc TC f TC' h q state state'.  

    Lemma wf_cont_state : wf_thread_state (ES.cont_thread S q) state. 
    Proof. 
      edestruct cstate_q_cont. 
      { apply SRCC. }
      eapply contwf; eauto. 
      apply SRCC. desf.
    Qed.

    Lemma htid : eq_dom hdom (Stid ∘ h) Gtid.
    Proof. eapply a2e_tid. eapply SRCC. Qed.

    Lemma himgInit : 
      SEinit ≡₁ h □₁ GEinit. 
    Proof. 
      etransitivity.
      { apply fimgInit. apply SRCC. }
      eapply set_collect_eq_dom.
      admit. 
    Admitted.
    
    Lemma SEinit_in_cont_sb_dom : 
      SEinit ⊆₁ ES.cont_sb_dom S q.
    Proof. 
      eapply ES.cont_sb_dom_Einit; [apply SRCC|].
      edestruct cstate_q_cont; [apply SRCC|].
      desf. apply KK.
    Qed.

    Lemma GEinit_in_e2a_cont_sb_dom : 
      GEinit ⊆₁ e2a S □₁ ES.cont_sb_dom S q. 
    Proof. 
      erewrite <- e2a_same_Einit.
      2-4 : eapply SRCC.
      apply set_collect_mori; auto. 
        by apply SEinit_in_cont_sb_dom.
    Qed.

    Lemma cont_sb_dom_in_hhdom :
      ES.cont_sb_dom S q ⊆₁ h □₁ hdom.
    Proof.
      unfold cert_dom.
      arewrite (ES.cont_sb_dom S q ≡₁ h □₁ (g □₁ ES.cont_sb_dom S q)) at 1.
      { rewrite set_collect_compose.
        apply fixset_set_fixpoint.
        apply SRCC. }
      erewrite set_union_minus with (s := ES.cont_sb_dom S q) (s' := SEinit).
      2 : by apply SEinit_in_cont_sb_dom.
      rewrite !set_collect_union.
      apply set_subset_union_l. split.
      { arewrite (acts_set (ProgToExecution.G state) ≡₁ g □₁ (ES.cont_sb_dom S q \₁ SEinit)).
        2: by eauto with hahn.
        eapply contstateE; eauto.
        1-2: by apply SRCC.
        edestruct cstate_q_cont; [apply SRCC|]. desf. }
      rewrite <- !set_collect_union.
      apply set_collect_mori; auto. 
      rewrite e2a_same_Einit.
      2-4 : eapply SRCC. 
      eapply GEinit_in_hdom; apply SRCC.
    Qed.

    Lemma cfk_hdom : 
      h □₁ hdom ∩₁ ES.cont_cf_dom S q ≡₁ ∅.
    Proof. 
      assert (ES.Wf S) as WFS by apply SRCC.
      edestruct cstate_q_cont as [st [stEQ KK]]; 
        [apply SRCC|].
      red; split; [|basic_solver].
      rewrite cert_dom_alt; [|apply SRCC].
      rewrite !set_collect_union. 
      rewrite set_inter_union_l.
      apply set_subset_union_l; split. 
      { rewrite ES.cont_cf_Tid_; eauto.  
        intros x [HH TIDx]. red.
        destruct HH as [a [DOMa Ha]].
        edestruct DOMa as [CIa NTIDa].
        subst x. apply NTIDa.
        erewrite <- a2e_tid; 
          [eauto | | eapply DOMa]. 
        eapply fixset_mori; 
          [| eauto| eapply SRCC].
        rewrite cert_dom_alt; [|apply SRCC]. 
        red. basic_solver 10. }
      erewrite contstateE;
        [|apply SRCC | apply SRCC | rewrite stEQ; eapply KK].
      arewrite 
        (h □₁ (g □₁ (ES.cont_sb_dom S q \₁ SEinit)) ≡₁ ES.cont_sb_dom S q \₁ SEinit).
      { rewrite set_collect_compose.
        symmetry. eapply fixset_set_fixpoint.
        eapply fixset_mori; eauto; 
          [| eapply hgfix; eapply SRCC].  
        red. basic_solver. }
      rewrite ES.cont_cf_cont_sb; eauto. 
      unfolder. ins. desf. 
    Qed.

    Lemma hdom_sb_dom :
      dom_rel (Gsb ⨾ ⦗ hdom ⦘) ⊆₁ hdom.
    Proof.
      assert (tc_coherent G sc TC) as TCCOH by apply SRCC.
      intros x [y SB].
      destruct_seq_r SB as YY.
      set (ESB := SB).
      destruct_seq ESB as [XE YE].
      destruct YY as [[YY|[YY NTID]]|YY].
      { apply C_in_hdom. eapply dom_sb_covered; eauto.
        eexists. apply seq_eqv_r. eauto. }
      { set (CC := SB). apply sb_tid_init in CC. desf.
        { left. right. split. 2: by rewrite CC.
          generalize (@sb_trans G) SB YY. basic_solver 10. }
        apply C_in_hdom. eapply init_covered; eauto.
        split; auto. }
      destruct (classic (is_init x)) as [NN|NINIT].
      { apply C_in_hdom. eapply init_covered; eauto.
        split; auto. }
      right.
      edestruct cstate_q_cont as [lstate]; [apply SRCC|]. desf.
      assert (wf_thread_state (ES.cont_thread S q) lstate) as WFT.
      { eapply contwf; [by apply SRCC|]. apply KK. }
      eapply acts_rep in YY; eauto. 
      destruct YY as [yin [REP LE]]. 
      rewrite REP in *.
      destruct x; desf.
      red in ESB. desf. 
      apply acts_clos; auto.
      etransitivity; eauto.  
    Qed.

    Lemma hdom_sb_prefix :
      Gsb ⨾ ⦗ hdom ⦘ ≡ ⦗ hdom ⦘ ⨾ Gsb ⨾ ⦗ hdom ⦘.
    Proof.
      split.
      all: intros x y SB.
      2: { destruct_seq_l SB as AA. apply SB. }
      apply seq_eqv_l. split; auto.
      apply hdom_sb_dom; auto. red. eauto.
    Qed.

    Lemma hsb : 
      h □ (Gsb ⨾ ⦗ hdom ⦘) ⊆ Ssb. 
    Proof.
      rewrite hdom_sb_prefix; auto.
      intros x y SB. red in SB. desf.
      destruct_seq SB as [AA BB].
      assert (~ is_init y') as YNINIT.
      { apply no_sb_to_init in SB. by destruct_seq_r SB as YY. }

      apply wf_sbE in SB. destruct_seq SB as [EX EY]. 

      assert (SE (h x')) as HEX.
      { eapply SRCC.(sr_a2e_h). eexists. split; [|by eauto]; eauto. }
      assert (SE (h y')) as HEY.
      { eapply SRCC.(sr_a2e_h). eexists. split; [|by eauto]; eauto. }

      assert (~ SEinit (h y')) as HYNINIT.
      { intros JJ. apply himgInit in JJ; auto.
        unfolder in JJ. desc. apply YNINIT.
        erewrite a2e_inj; eauto; try apply SRCC.
        unfold cert_dom. do 2 left. 
        eapply init_covered; try apply SRCC.
        basic_solver. }

      set (CC := SB). apply sb_tid_init in CC. desf.
      2: { apply ES.sb_init; [by apply SRCC|].
           split. 2: by split.
           apply himgInit; auto. eexists. split; eauto.
           split; auto. }
      assert (~ Scf (h x') (h y')) as NCF.
      { intros JJ.
        eapply exec_ncf. 
        { apply SRCC.(sr_exec_h). }
        apply seq_eqv_l. split; [|apply seq_eqv_r; split; eauto].
        all: by eexists; split; [|by eauto]. }
      edestruct ES.same_thread as [PP _]; [by apply SRCC|].
      specialize (PP (h x') (h y')).

      assert (~ is_init x') as XNINIT.
      { intros XX. apply YNINIT.
        eapply tid_initi; eauto; try by apply SRCC.
        split; auto.
        rewrite <- CC. destruct x'; desf. }
      assert (~ SEinit (h x')) as HXNINIT.
      { intros JJ. apply himgInit in JJ; auto.
        unfolder in JJ. desc. apply XNINIT.
        erewrite a2e_inj; try apply SRCC.(sr_a2e_h); eauto. 
        unfold cert_dom. do 2 left.
        eapply init_covered; try apply SRCC.
        basic_solver. }

      destruct PP as [PP|]; [| |done].
      { apply seq_eqv_l. split.
        2: apply seq_eqv_r; split.
        1,3: by split.
        do 2 (rewrite <- htid in CC; auto). }
      destruct_seq PP as [XX YY].
      red in PP. desf.
      { eapply SRCC.(sr_a2e_h) in PP; eauto. subst. by apply sb_irr in SB. }
      exfalso.
      eapply sb_irr. eapply sb_trans; eauto.
      eapply e2a_sb; eauto; try apply SRCC. 
      do 2 eexists. splits; eauto.
      1 : fold (compose g h y').
      2 : fold (compose g h x').
      all: eapply a2e_fix; [by apply SRCC|]; auto. 
    Qed.

    Lemma hlabCI : 
      eq_dom (C ∪₁ I) (Slab ∘ h) Glab.
    Proof. 
      red. ins. etransitivity.
      { eapply hlab; eauto. basic_solver. }
      eapply cslab; [apply SRCC|]. 
      unfold D. do 4 left.
      (* it should be easy, but it seems there are no suitable lemmas *)
      admit. 
    Admitted.

    Lemma h_rel_ewD : 
      dom_rel (Srelease ⨾ Sew^? ⨾ ⦗ h □₁ hdom ⦘) ⊆₁ h □₁ hdom.  
    Proof.
      eapply exec_rel_ewD; try apply SRCC. 
      unfold cert_dom. basic_solver. 
    Qed.

    Lemma h_hb_in_Chb_sb :
      Shb ⊆ ⦗ h □₁ C ⦘ ⨾ Shb ∪ Ssb. 
    Proof.
      eapply exec_hb_in_Chb_sb; try apply SRCC. 
      unfold cert_dom. basic_solver. 
    Qed.

    Lemma h_hbD :
      dom_rel (Shb ⨾ ⦗ h □₁ hdom ⦘) ⊆₁ h □₁ hdom.  
    Proof.
      eapply exec_hbD; try apply SRCC. 
      unfold cert_dom. basic_solver. 
    Qed.

    Lemma h_hb_release_ewD :
      dom_rel (Shb^? ⨾ Srelease ⨾ Sew^? ⨾ ⦗ h □₁ hdom ⦘) ⊆₁ h □₁ hdom.  
    Proof. 
      eapply exec_hb_release_ewD; try apply SRCC. 
      unfold cert_dom. basic_solver. 
    Qed.

    Lemma h_necfD :
      restr_rel (h □₁ hdom) Secf ⊆ ∅₂.
    Proof. 
      eapply exec_necfD; try apply SRCC. 
      unfold cert_dom. basic_solver. 
    Qed.

  End SimRelCertProps. 

End SimRelProps.