Require Import Program.Basics Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CombRelations SimTraversal SimulationRel AuxRel CertExecution2.
Require Import AuxRel AuxDef EventStructure Consistency EventToAction LblStep 
        CertGraph CertRf ImmProperties SimRelDef.

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

  Section SimRelContProps. 

    Variable WF : ES.Wf S.
    Variable SRC : simrel_cont prog S G TC f.  
  
    Lemma contstateE k (st : thread_st (ES.cont_thread S k))
             (INK : K (k, thread_cont_st (ES.cont_thread S k) st)) :
      acts_set st.(ProgToExecution.G) ≡₁ g □₁ (ES.cont_sb_dom S k \₁ SEinit).
    Proof.
      ins. 
      assert (wf_thread_state (ES.cont_thread S k) st) as WFT.
      { eapply contwf; eauto. }
      ins. split.
      { unfold acts_set. intros a ACT.
        eapply acts_rep in ACT; eauto. 
        desf. unfolder. unfold ES.cont_thread.
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
          { intuition. }
          unfold e2a. 
          destruct 
            (excluded_middle_informative (Stid x = tid_init))
            as [TIDi | nTIDi];
            [intuition | congruence]. }
        exists eid; splits.
        { unfold ES.cont_sb_dom. basic_solver 10. }
        { intuition. }
        unfold e2a. 
        destruct 
          (excluded_middle_informative (Stid eid = tid_init))
          as [TIDi | nTIDi];
          [intuition | congruence]. }
      unfolder. intros a [e [[SB NINIT] gEQ]]. 
      edestruct k eqn:kEQ.
      { unfold ES.cont_sb_dom, ES.acts_init_set in SB.
        destruct SB as [SEe TIDe].
        exfalso. apply NINIT. splits; auto. }
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
          by apply ES.sb_tid. }
      unfold acts_set. eapply acts_clos. 
      { arewrite (Stid e = Stid eid).
        arewrite (Stid eid = ES.cont_thread S (CEvent eid)).
        eapply contwf; eauto. }
      unfold ES.cont_sb_dom in SB.
      unfolder in SB. 
      destruct SB as [y [z [[EQe | SBez] [EQzy EQeid]]]].
      { subst e y z. erewrite contseqn; eauto. }
      subst z y. etransitivity. 
      { eapply ES.seqn_sb_alt; eauto. }
      erewrite contseqn; eauto.
    Qed.

  End SimRelContProps. 

  Section SimRelCommonProps. 
    
    Variable SRC : simrel_common prog S G sc TC f. 

    Lemma e2a_same_Einit : 
      e2a S □₁ SEinit ≡₁ GEinit.
    Proof. 
      split; [eapply e2a_Einit; apply SRC|].
      unfolder. intros a [INITa GEa].
      edestruct gEinit as [e [[INITe SEe] gEQ]].
      1-2 : unfolder; eauto.  
      eexists; splits; eauto. 
    Qed.

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

    Lemma ginjfdom : inj_dom (f □₁ fdom) g.
    Proof. eapply e2a_inj; apply SRC. Qed.

    Lemma ginjfC : inj_dom (f □₁ C) g.
    Proof.
      eapply inj_dom_mori; eauto.
      2: by apply ginjfdom.
      red. basic_solver.
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
    
    Lemma gsame_loc : 
      g □ restr_rel SE (same_loc Slab) ⊆ restr_rel GE (same_loc Glab).
    Proof.
      intros x y HH. red in HH. desf.
      eapply same_lab_u2v_dom_same_loc in HH.
      2: { apply same_lab_u2v_dom_comm. apply SRC. }
      red in HH. desf. 
      red. splits.
      apply HH.
      all: by eapply gE; eauto; eexists; eauto.
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
      eapply gew.
      eexists. eexists.
      splits.
      { eapply ES.ew_sym; eauto. }
      all: by eauto.
    Qed.

    Lemma grs : g □ Srs ⊆ Grs. 
    Proof. 
      assert (ES.Wf S) as WF by apply SRC.
      rewrite rs_alt; auto.
      rewrite !collect_rel_seqi.
      rewrite !set_collect_eqv.
      rewrite !gW.
      repeat apply seq_mori; eauto with hahn.
      2: { rewrite collect_rel_crt. eauto using clos_refl_trans_mori, grfrmw. }
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
        eapply grmw; eauto.
        arewrite (e = g (f e)).
        { symmetry. eapply gffix; eauto. basic_solver. }
        unfolder. eauto. }
      assert (~ GEinit e) as NINIT.
      { intros [BB]. unfold is_init in BB. desf. }
      assert (~ SEinit (f e)) as NSINIT.
      { intros BB. apply NINIT.
        eapply finitIncl in BB; eauto. 
        red in BB. desf.
        assert (y = e); desf.
        apply finj; eauto. by left. }
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
      { apply gffix; eauto. basic_solver. }
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
      edestruct cstate_q_cont; eauto; desf. 
      eapply contwf; eauto. 
      apply SRCC.
    Qed.

    Lemma hdom_alt : 
      hdom ≡₁ (C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘)) ∩₁ GNTid qtid ∪₁ contE. 
    Proof. 
      unfold cert_dom. 
      split; [|basic_solver 10]. 
      arewrite (C ≡₁ C ∩₁ GTid qtid ∪₁ C ∩₁ GNTid qtid) at 1.
      { rewrite <- set_inter_union_r.
        rewrite tid_set_dec.
        basic_solver. }
      erewrite cstate_covered; eauto. 
      basic_solver 10.
    Qed.

    Lemma htid : eq_dom hdom (Stid ∘ h) Gtid.
    Proof. eapply a2e_tid. eapply SRCC. Qed.

    Lemma hgtrip : ⦗ h □₁ hdom ⦘ ⨾ ↑ (h ∘ g) ⊆ eq.
    Proof. 
      unfold seq, eqv_rel, set_collect, img_rel, inclusion, compose.
      intros x y [z [[zEQ [a [DOM xEQ]]] yEQ]].
      rewrite <- xEQ, yEQ, <- zEQ.
      arewrite (a = g x); auto.
      symmetry. rewrite <- xEQ. eapply ghfix; eauto.
    Qed.

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
      destruct SRCC.(cstate_q_cont).
      desf. apply KK.
    Qed.

    Lemma GEinit_in_e2a_cont_sb_dom : 
      GEinit ⊆₁ e2a S □₁ ES.cont_sb_dom S q. 
    Proof. 
      erewrite <- e2a_same_Einit; [|apply SRCC].
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
        edestruct cstate_q_cont; eauto. desf. }
      rewrite <- !set_collect_union.
      apply set_collect_mori; auto. 
      rewrite e2a_same_Einit; [|apply SRCC]. 
      eapply GEinit_in_hdom; apply SRCC.
    Qed.

    Lemma cfk_hdom : 
      h □₁ hdom ∩₁ ES.cont_cf_dom S q ≡₁ ∅.
    Proof. 
      assert (ES.Wf S) as WFS by apply SRCC.
      edestruct cstate_q_cont as [st [stEQ KK]]; eauto.
      red; split; [|basic_solver].
      rewrite hdom_alt.
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
        rewrite hdom_alt. red.
        basic_solver 10. }
      erewrite contstateE; auto; 
        [| apply SRCC | rewrite stEQ; eapply KK].
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

    Lemma cont_sb_dom_dom :
      dom_rel (Ssb ⨾ ⦗ ES.cont_sb_dom S q ⦘) ⊆₁ ES.cont_sb_dom S q.
    Proof.
      assert (ES.Wf S) as WF.
      { apply SRCC. }
      intros x [y SB].
      destruct_seq_r SB as YY. red in YY. desf.
      { exfalso. eapply ES.sb_ninit; eauto.
        apply seq_eqv_r. eauto. }
      red. generalize WF.(ES.sb_trans) YY SB. basic_solver 10.
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
      edestruct cstate_q_cont as [lstate]; eauto. desf.
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
      { eapply himg; eauto. eexists. split; [|by eauto]; eauto. }
      assert (SE (h y')) as HEY.
      { eapply himg; eauto. eexists. split; [|by eauto]; eauto. }

      assert (~ SEinit (h y')) as HYNINIT.
      { intros JJ. apply himgInit in JJ; auto.
        red in JJ. desf. eapply hinj in JJ0; eauto. subst.
        destruct JJ. desf. }

      set (CC := SB). apply sb_tid_init in CC. desf.
      2: { apply ES.sb_init; [by apply SRCC|].
           split. 2: by split.
           apply himgInit; auto. eexists. split; eauto.
           split; auto. }
      assert (~ Scf (h x') (h y')) as NCF.
      { intros JJ.
        eapply SRCC.(himgNcf).
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
        red in JJ. desf. eapply hinj in JJ0; eauto. subst.
        destruct JJ. desf. }
      destruct PP as [PP|]; [| |done].
      { apply seq_eqv_l. split.
        2: apply seq_eqv_r; split.
        1,3: by split.
        do 2 (rewrite <- htid in CC; auto). }
      destruct_seq PP as [XX YY].
      red in PP. desf.
      { eapply hinj in PP; eauto. subst. by apply sb_irr in SB. }
      exfalso.
      eapply sb_irr. eapply sb_trans; eauto.
      eapply e2a_sb; eauto; try apply SRCC. 
      do 2 eexists. splits; eauto.
      1 : fold (compose g h y').
      2 : fold (compose g h x').
      all: eapply ghfix; [by apply SRCC|]; auto. 
    Qed.

    Lemma rfeI :
      dom_rel Srfe ⊆₁ dom_rel (Sew^? ⨾ ⦗ h □₁ I ⦘).
    Proof.
      assert (ES.Wf S) as WF by apply SRCC.
      unfold ES.rfe, ES.rf, ES.jfe.
      rewrite crE at 1.
      rewrite seq_union_l, !minus_union_l, dom_union, seq_id_l.
      unionL.
      { etransitivity; [|by apply SRCC.(jfehI)].
        unfold ES.jfe. basic_solver. }
      intros x [y [[[z [EW JF]] CC] NSB]].
      assert (~ Ssb z y) as AA.
      { intros SB. apply CC.
        apply ES.cf_sb_in_cf; auto.
        eexists. split; eauto.
        apply ES.ewc; auto. }
      edestruct SRCC.(jfehI) as [v HH].
      { eexists. split; eauto. }
      destruct_seq_r HH as BB.
      eexists.  apply seq_eqv_r. split; [|by eauto].
      generalize WF.(ES.ew_trans) EW HH. basic_solver.
    Qed.

    Lemma releaseNCsb : ⦗ set_compl (h □₁ C) ⦘ ⨾ Srelease ⊆ Ssb^?.
    Proof.
      assert (ES.Wf S) as WF by apply SRCC.
      unfold release at 1, rs. rewrite <- !seqA.
      intros x y [z [HH RFRMW]].
      apply clos_rt_rtn1 in RFRMW.
      induction RFRMW as [|y w [u [RF RMW]]].
      { generalize WF.(ES.sb_trans) HH. basic_solver 10. }
      apply ES.rfi_union_rfe in RF. destruct RF as [RF|RF].
      { apply WF.(ES.rmwi) in RMW. red in RF. 
        generalize WF.(ES.sb_trans) IHRFRMW RF RMW. basic_solver 10. }
      exfalso.
      assert (~ (h □₁ C) x) as CC.
      { generalize HH. basic_solver 10. }
      apply CC. eapply release_issh_cov; eauto.
      assert (dom_rel (Sew^? ⨾ ⦗ h □₁ I ⦘) y) as [yy DD].
      { apply rfeI; auto. eexists. eauto. }
      eexists. eexists. split; eauto.
      unfold release, rs. apply clos_rtn1_rt in RFRMW.
      generalize HH RFRMW. basic_solver 40.
    Qed.
    
    Lemma swNCsb : ⦗ set_compl (h □₁ C) ⦘ ⨾ Ssw ⊆ Ssb.
    Proof.
      assert (ES.Wf S) as WF by apply SRCC.
      unfold sw.
      arewrite (⦗set_compl (h □₁ C)⦘ ⨾ Srelease ⨾ Srf ⊆ Ssb).
      2: { generalize WF.(ES.sb_trans). basic_solver. }
      rewrite ES.rfi_union_rfe. rewrite !seq_union_r. unionL.
      { sin_rewrite releaseNCsb; auto. unfold ES.rfi.
        generalize WF.(ES.sb_trans). basic_solver. }
      intros x y HH.
      destruct_seq_l HH as DX. exfalso. apply DX.
      destruct HH as [z [REL RFE]].
      eapply release_issh_cov; eauto.
      assert (dom_rel (Sew^? ⨾ ⦗ h □₁ I ⦘) z) as [zz DD].
      { apply rfeI; auto. eexists. eauto. }
      eexists. eexists. eauto.
    Qed.

    Lemma sb_hdom_dom : dom_rel (Ssb ⨾ ⦗ h □₁ hdom ⦘) ⊆₁ h □₁ hdom.
    Proof. (* TODO: most likely, we need this in simrel_cert. *) Admitted.

    Lemma sb_hdom_in_hsb : Ssb ⨾ ⦗ h □₁ hdom ⦘ ⊆ h □ Gsb.
    Proof.
      assert (inj_dom_s hdom h) as HD by apply SRCC.
      arewrite (Ssb ⨾ ⦗ h □₁ hdom ⦘ ⊆ ⦗ h □₁ hdom ⦘ ;; Ssb ⨾ ⦗ h □₁ hdom ⦘). 
      { intros x y HH. apply seq_eqv_l. split; auto.
        apply sb_hdom_dom; auto. eexists. eauto. }
      rewrite <- restr_relE.
      rewrite <- collect_rel_eqdom_eq. 2: by apply hgtrip.
      rewrite <- collect_rel_compose.
      apply collect_rel_mori; auto.
      rewrite inclusion_restr.
      eapply e2a_sb; apply SRCC.
    Qed.
    
    Lemma sbHC_dom : dom_rel (Ssb ⨾ ⦗ h □₁ C ⦘) ⊆₁ h □₁ C.
    Proof.
      rewrite <- seq_eqvK.
      sin_rewrite C_in_hdom.
      sin_rewrite sb_hdom_in_hsb; auto.
      rewrite <- set_collect_eqv.
      rewrite <- collect_rel_seq_r.
      2: { sin_rewrite C_in_hdom. rewrite dom_eqv.
           apply SRCC. }
      rewrite sb_covered; [|by apply SRCC].
      basic_solver.
    Qed.

    Lemma sbNCNC :
      codom_rel (⦗ set_compl (h □₁ C) ⦘ ⨾ Ssb) ⊆₁ set_compl (h □₁ C).
    Proof.
      intros x [y HH]. destruct_seq_l HH as DX.
      intros DY. apply DX.
      apply sbHC_dom; auto. eexists. apply seq_eqv_r. eauto.
    Qed.

    Lemma hbNCsb : ⦗ set_compl (h □₁ C) ⦘ ⨾ Shb ⊆ Ssb. 
    Proof.
      assert (ES.Wf S) as WF by apply SRCC.
      intros x y HH. destruct_seq_l HH as DX.
      red in HH. apply clos_trans_tn1 in HH.
      induction HH as [y [|HH]|y z [HH|HH]]; auto.
      { apply swNCsb; auto. by apply seq_eqv_l. }
      all: eapply ES.sb_trans; eauto.
      apply swNCsb; auto. apply seq_eqv_l. split; auto.
      apply sbNCNC; auto.
      eexists. apply seq_eqv_l. eauto.
    Qed.

    Lemma hb_in_HChb_sb : Shb ⊆ ⦗ h □₁ C ⦘ ⨾ Shb ∪ Ssb. 
    Proof.
      arewrite (Shb ⊆ ⦗h □₁ C ∪₁ set_compl (h □₁ C)⦘ ⨾ Shb).
      { rewrite set_compl_union_id. by rewrite seq_id_l. }
      rewrite id_union, seq_union_l. apply union_mori; [done|].
      apply hbNCsb; auto.
    Qed.
   
  End SimRelCertProps. 


End SimRelProps.