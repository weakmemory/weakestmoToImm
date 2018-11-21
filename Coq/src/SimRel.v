Require Import Program.Basics Omega.
Require Import Coq.Logic.FunctionalExtensionality Classical_Prop.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb SimulationRel
     CombRelations.
Require Import AuxRel AuxDef EventStructure Construction Consistency LblStep
        ImmProperties.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRel.
  Variable prog : Prog.t.
  Variable PROG_NINIT : ~ (IdentMap.In tid_init prog).
  Variable S : ES.t.
  Variable G  : execution.
  Variable GPROG : program_execution prog G.
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

  Notation "'Stid_' t" := (fun x => Stid x = t) (at level 1).

  Notation "'Ssb'" := (S.(ES.sb)).
  Notation "'Srmw'" := (S.(ES.rmw)).
  Notation "'Sjf'" := (S.(ES.jf)).
  Notation "'Srf'" := (S.(ES.rf)).
  Notation "'Srfi'" := (S.(ES.rfi)).
  Notation "'Srfe'" := (S.(ES.rfe)).
  Notation "'Sco'" := (S.(ES.co)).
  Notation "'Scf'" := (S.(ES.cf)).
  Notation "'Scc'" := (S.(ES.cc)).
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
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gloc'" := (loc G.(lab)).
  Notation "'Gtid'" := (tid).
  Notation "'Grmw'" := G.(rmw).
  
  Notation "'Gtid_' t" := (fun x => tid x = t) (at level 1).
  Notation "'GNtid_' t" := (fun x => tid x <> t) (at level 1).

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


  Definition pc thread :=
    C ∩₁ Gtid_ thread \₁ dom_rel (Gsb ⨾ ⦗ C ⦘).

  Definition thread_lts (tid : thread_id) : Language.t :=
    @Language.mk
      (list Instr.t) state
      init
      is_terminal
      (ilbl_step tid).
  
  Notation "'g'" := (ES.event_to_act S).
  Notation "'g_s'" :=
    (fun e: actid => 
       let thread := Stid e in
       ThreadEvent thread
                   (countNatP (dom_rel (⦗Stid thread⦘ ⨾ sb ⨾ ⦗eq e⦘))
                              (ES.next_act S))).

  Record simrel_cont :=
    { contlang : forall cont lang (state : lang.(Language.state))
                        (INK : K (cont, existT _ lang state)),
        lang = thread_lts (ES.cont_thread S cont);
      
      contstateE : forall cont thread (state : (thread_lts thread).(Language.state))
                        (INK : K (cont, existT _ _ state)), 
          state.(ProgToExecution.G).(acts_set) ≡₁ g □₁ ES.cont_sb_dom S cont;

      contstable : forall cont thread (state : (thread_lts thread).(Language.state))
                        (INK : K (cont, existT _ _ state)), 
          stable_state thread state;

      contwf : forall cont thread (state : (thread_lts thread).(Language.state))
                        (INK : K (cont, existT _ _ state)),
          wf_thread_state thread state;

      continit : forall thread lprog
                        (INPROG : IdentMap.find thread prog = Some lprog),
          exists (state : (thread_lts thread).(Language.state)),
            ⟪ INK : K (CInit thread, existT _ _ state) ⟫ /\
            ⟪ INITST :
                (istep thread [])＊ ((thread_lts thread).(Language.init) lprog)
                                 state⟫;

      contpc : forall e (state : (thread_lts (Gtid e)).(Language.state))
                      (PC : pc (Gtid e) e)
                      (INK : K (CEvent (f e), existT _ _ state)),
                @sim_state G sim_normal C (Gtid e) state;
    }.
  
  Notation "'fdom'" := (C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘)) (only parsing).

  Record simrel_common :=
    { gwf   : Execution.Wf G;
      gprclos : forall thread m n (LT : m < n)
                       (EE : GE (ThreadEvent thread n)),
          GE (ThreadEvent thread m);
      tccoh : tc_coherent G sc TC;
      rmwclos : forall r w (RMW : Grmw r w), C r <-> C w;
      irelcov : GW ∩₁ GRel ∩₁ I ⊆₁ C;
      swf   : ES.Wf S;
      
      gcons : imm_consistent G sc;
      scons : @es_consistent S Weakestmo;
      
      scont : simrel_cont;

      fgtrip : ⦗ fdom ⦘ ⨾ ↑ (g ∘ f) ⊆ eq;

      gE : g □₁ SE ⊆₁ GE;
      grmw : g □ Srmw ⊆ Grmw;
      gjf  : g □ Sjf  ⊆ Gvf;
      gew  : g □ Sew  ⊆ ⦗I⦘;
      gco  : g □ Sco  ⊆ Gco;
      
      grfrmw : g □ (Srf ⨾ Srmw) ⊆ Grf ⨾ Grmw;

      fco : f □ ⦗ fdom ⦘ ⨾ Gco ⨾ ⦗ fdom ⦘ ⊆ Sco;

      fimgNcf : ⦗ f □₁ fdom ⦘ ⨾ Scf ⨾ ⦗ f □₁ fdom ⦘ ≡ ∅₂;
      
      complete_fdom :
        (f □₁ fdom) ∩₁ SR ⊆₁ codom_rel (⦗ f □₁ fdom ⦘ ⨾ Srf);

      finj : inj_dom_s fdom f;  
      fimg : f □₁ fdom ⊆₁ SE;
      foth : (f □₁ set_compl fdom) ∩₁ SE ≡₁ ∅;
      flab : eq_dom (C ∪₁ I) (Slab ∘ f) Glab;
      
      glab : same_lab_up_to_value Slab (Glab ∘ g);

      ftid : eq_dom GE (Stid ∘ f) Gtid;

      finitIncl : S.(ES.acts_init_set) ⊆₁ f □₁ (is_init ∩₁ GE);

      vis  : f □₁ fdom ⊆₁ vis S;

    }.

  Section Properties.
    Variable SRC : simrel_common.

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
      is_total (f □₁ fdom ∩₁ Stid_ thread) Ssb.
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

    Lemma gEinit : g □₁ SEinit ⊆₁ GEinit.
    Proof.
      unfold ES.event_to_act.
      unfolder. ins. desf.
      3: { exfalso. apply n. split; auto. }
      2: { exfalso.
           eapply ES.init_lab in a.
           2: by apply SRC.
           unfold loc in *. desf. }
      split; auto.
      apply SRC.(finitIncl) in a.
      destruct a as [z [[AA BB] CC]].
      desf. destruct z; desf.
      assert (Slab (f (InitEvent l0)) = Glab (InitEvent l0)) as DD.
      { eapply SRC.(flab). left. apply SRC. split; eauto. }
      unfold loc in *. rewrite DD in Heq.
      rewrite wf_init_lab in Heq; [|by apply SRC].
      inv Heq.
    Qed.

    Lemma gEninit : g □₁ SEninit ⊆₁ set_compl is_init.
    Proof. unfold ES.acts_ninit_set, ES.event_to_act. basic_solver. Qed.

    Lemma gext_sb : g □ Ssb ⊆ ext_sb.
    Proof.
      assert (ES.Wf S) as WF by apply SRC.
      rewrite <- WF.(ES.sb_seq_Eninit_r).
      rewrite <- seq_id_l with (r:=Ssb).
      rewrite <- set_compl_union_id with (s:=SEinit).
      rewrite id_union. relsf.
      rewrite !seqA.
      eapply inclusion_union_l.
      { arewrite (⦗SEinit⦘ ⨾ Ssb ⨾ ⦗SEninit⦘ ⊆ SEinit × SEninit).
        { basic_solver. }
        rewrite collect_rel_cross.
        rewrite gEinit, gEninit.
        etransitivity; [|by apply initninit_in_ext_sb].
        basic_solver. }
      rewrite (dom_l WF.(ES.sbE)), !seqA.
      arewrite (⦗set_compl SEinit⦘ ⨾ ⦗SE⦘ ⊆ ⦗SEninit⦘) by basic_solver.
      unfold ES.event_to_act.
      rewrite collect_rel_if_else.
      2,3: unfold ES.acts_ninit_set; basic_solver.
      intros x y HH. red in HH. desf.
      red.
      assert (Stid x' = Stid y') as TT.
      { by apply WF.(ES.sb_tid). }
      rewrite TT.
      splits; auto.
      destruct_seq HH as [AA BB].
      assert (dom_rel (⦗Stid_ (Stid y')⦘ ⨾ Ssb ⨾ ⦗eq y'⦘) x') as CC.
      { eexists. apply seq_eqv_l. split; auto.
        apply seq_eqv_r. eauto. }
      assert (irreflexive Ssb) as UU by (by apply ES.sb_irr).
      apply countNatP_lt with (e:=x'); auto.
      3: by apply AA.
      2: { intros YY. eapply UU. generalize YY. basic_solver. }
      intros z [v PP]. destruct_seq PP as [DD EE]; subst.
      eexists. apply seq_eqv_l. split; auto.
      apply seq_eqv_r. split; [|by eauto].
      eapply ES.sb_trans; eauto.
    Qed.

    Lemma gsb : g □ Ssb ⊆ Gsb.
    Proof.
      rewrite ES.sbE; [|by apply SRC].
      unfold Execution.sb.
        by rewrite !collect_rel_seqi, set_collect_eqv, gext_sb, gE.
    Qed.

    (* TODO: it may not follow from the simulation relation. *)
    Lemma fsb : f □ (Gsb ⨾ ⦗ fdom ⦘) ⊆ Ssb. 
    Proof.
      unfold collect_rel, inclusion.
      ins. desf.
    Admitted.
    
    Ltac g_type t H :=
      unfolder; ins; desf; erewrite t in H; [|by apply SRC]; inv H.

    Lemma gW : g □₁ SW ⊆₁ GW.
    Proof. g_type same_label_is_w H. Qed.

    Lemma gF : g □₁ SF ⊆₁ GF.
    Proof. g_type same_label_is_f H. Qed.

    Lemma gRel : g □₁ SRel ⊆₁ GRel.
    Proof. g_type same_label_is_rel H. Qed.
    
    Lemma gsame_loc : g □ same_loc Slab ⊆ same_loc Glab.
    Proof. g_type same_label_same_loc H. Qed.

    Lemma grs : g □ Srs ⊆ Grs. 
    Proof. 
      unfold rs, imm_s_hb.rs. 
      rewrite !collect_rel_seqi.
      rewrite !set_collect_eqv.
      arewrite (SE ∩₁ SW ⊆₁ SW) by basic_solver.
      rewrite !gW.
      repeat apply seq_mori; eauto with hahn.
      2: { rewrite collect_rel_crt. auto using clos_refl_trans_mori, grfrmw. }
      rewrite collect_rel_cr.
      rewrite collect_rel_interi. 
      apply clos_refl_mori, inter_rel_mori. 
      { apply gsb. }
      apply gsame_loc.
    Qed.

    Lemma grelease : g □ Srelease ⊆ Grelease.
    Proof. 
      unfold release, imm_s_hb.release. 
      rewrite !collect_rel_seqi, !collect_rel_cr, !collect_rel_seqi. 
      rewrite !set_collect_eqv.
        by rewrite gRel, grs, gsb, gF.
    Qed.
 
    Lemma gtid e : Stid e = Gtid (g e).
    Proof.
      assert (SEinit e -> Stid e = tid_init) as HH.
      { admit. }
      unfold ES.event_to_act. desf; simpls.
      all: by apply HH.
    Admitted.

    Lemma gtid_ thread : g □₁ Stid_ thread ⊆₁ Gtid_ thread.
    Proof. generalize gtid. basic_solver. Qed.

    Lemma flaboth :
          same_lab_up_to_value (Slab ∘ f) Glab.
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
      2: { edestruct (continit (scont SRC)) as [state]; eauto.
           desf.
           eexists. eexists.
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
           admit. }
      assert (thread <> tid_init) as NTINIT.
      { intros HH; subst. by apply PROG_NINIT. }
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
        { apply SRC.(fgtrip). apply seq_eqv_l.
            by split; [left|]. }
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
      { rewrite <- SRC.(ftid); auto.
        eapply coveredE; eauto. }
      simpls. rewrite TT in KK.
      eapply contpc in PC; eauto.
      eexists. eexists.
      splits; eauto.
      unfold ES.cont_sb_dom. simpls.
      rewrite set_collect_dom.
      rewrite collect_seq_eqv_r.
      rewrite collect_eq.
      arewrite (g (f e) = e).
      { symmetry. apply SRC.(fgtrip).
        apply seq_eqv_l. by split; [left|]. }
      rewrite crE.
      rewrite collect_rel_union.
      rewrite seq_union_l.
      rewrite dom_union.
      apply set_subset_union_l.
      split; [basic_solver|].
      rewrite gsb.
      arewrite (eq e ⊆₁ C).
      { intros x HH. desf. }
      eapply dom_sb_covered; eauto.
      apply fimg; auto.
      generalize CE. basic_solver.
    Admitted.

    Lemma ginjfdom : inj_dom (f □₁ fdom) g.
    Proof. 
      red. intros x y [x' [AA BB]] [y' [CC DD]] HH. subst.
      assert (g (f x') = x' /\ g (f y') = y') as [FF GG].
      { split.
        all: symmetry; apply SRC.(fgtrip); apply seq_eqv_l.
        all: by split; auto; red. }
      rewrite FF in *. rewrite GG in *. by subst.
    Qed.

    Lemma ginjfC : inj_dom (f □₁ C) g.
    Proof.
      eapply inj_dom_mori; eauto.
      2: by apply ginjfdom.
      red. basic_solver.
    Qed.
    
    Lemma dom_release_iss : 
        dom_rel (Srelease ⨾ Sew^? ⨾ ⦗ f □₁ I ⦘) ⊆₁ f □₁ C.
    Proof. 
      eapply set_collect_subset.
      { (* TODO: it doesn't hold :( *)
        admit. }
      rewrite set_collect_dom, !collect_rel_seqi, 
        set_collect_eqv, !set_collect_compose.
      arewrite ((g ∘ f) □₁ I ≡₁ I).
      { symmetry. 
        eapply fixset_set_fixpoint.
        eapply fixset_mori with (x:=fdom). 
        { unfold flip; basic_solver 10. }
        { eauto. }
        apply fixset_img_rel.
        eapply SRC.(fgtrip). }
      arewrite ((g ∘ f) □₁ C ≡₁ C).
      { symmetry. 
        eapply fixset_set_fixpoint.
        eapply fixset_mori with (x:=fdom). 
        { unfold flip; basic_solver 10. }
        { eauto. }
        apply fixset_img_rel.
        eapply SRC.(fgtrip). }
      rewrite grelease. 
      rewrite collect_rel_cr.
      rewrite gew; auto. 
      arewrite (⦗I⦘^? ⨾ ⦗I⦘ ≡ ⦗I⦘) by basic_solver.
      eapply dom_release_issued; apply SRC.  
    Admitted.  

    Lemma hbNCsb : ⦗SE \₁ f □₁ C⦘ ⨾ Shb ⊆ Ssb. 
    Proof. 
      admit. 
      (* assert (ES.Wf S) as SWF by apply SRC.  *)
      (* unfold hb, set_minus.  *)
      (* rewrite seq_eqv_l. *)
      (* red. *)
      (* intros x y [[Ex NCx] HBxy]. *)
      (* induction HBxy as [x y STEPxy | x y z HBxy IHxy HByz IHyz].  *)
      (* { destruct STEPxy as [SBxy | SWxy]; auto.  *)
      (*   exfalso.  *)
      (*   apply NCx. *)
      (*   apply swC in SWxy. *)
      (*   unfold seq, eqv_rel in SWxy. *)
      (*   desf. } *)
      (* specialize (IHxy Ex NCx). *)
      (* assert (SE y) as Ey.  *)
      (* { eapply ES.sbE in IHxy; auto.  *)
      (*   unfold seq, eqv_rel in IHxy. *)
      (*   desf. } *)
      (* assert (~ (f □₁ C) y) as NCy. *)
      (* { admit. } *)
      (* specialize (IHyz Ey NCy). *)
      (* eapply ES.sb_trans; eauto.  *)
    Admitted.  

  End Properties.
End SimRel.