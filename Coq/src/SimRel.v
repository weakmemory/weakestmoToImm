Require Import Program.Basics Omega.
Require Import Coq.Logic.FunctionalExtensionality Classical_Prop.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_hb SimulationRel
     CombRelations.
Require Import AuxRel AuxDef EventStructure Construction Consistency Vf.

Set Implicit Arguments.

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
  Notation "'K'"  := S.(ES.cont_set).
  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gtid'" := (tid).
  Notation "'Gsb'" := (G.(sb)).
  Notation "'Ghb'" := (G.(imm_hb.hb)).
  Notation "'Grf'" := (G.(rf)).
  Notation "'Gvf'" := (G.(Gvf)).
  Notation "'Gco'" := (G.(co)).
  Notation "'Grmw'" := (G.(rmw)).
  Notation "'Stid'" := (S.(ES.tid)).
  Notation "'Slab'" := (S.(ES.lab)).
  Notation "'Sloc'" := (loc S.(ES.lab)).
  Notation "'Ssb'" := (S.(ES.sb)).
  Notation "'Srf'" := (S.(ES.rf)).
  Notation "'Sco'" := (S.(ES.co)).
  Notation "'Scf'" := (S.(ES.cf)).
  Notation "'Sew'" := (S.(ES.ew)).
  Notation "'Sjf'" := (S.(ES.jf)).
  Notation "'Srmw'" := (S.(ES.rmw)).
  Notation "'Svf'" := (Svf S Weakestmo).
  Notation "'Gtid_' t" := (fun x => tid x = t) (at level 1).
  Notation "'Stid_' t" := (fun x => Stid x = t) (at level 1).

  Notation "'GR'" := (fun a => is_true (is_r Glab a)).
  Notation "'SR'" := (fun a => is_true (is_r Slab a)).

  Definition pc thread :=
    C ∩₁ Gtid_ thread \₁ dom_rel (Gsb ⨾ ⦗ C ⦘).

  Definition thread_lts (tid : thread_id) : Language.t :=
    @Language.mk
      (list Instr.t) state
      init
      is_terminal
      (istep tid).

  Record simrel_cont :=
    { contlang : forall cont lang (state : lang.(Language.state))
                        (INK : K (cont, existT _ lang state)),
        lang = thread_lts (ES.cont_thread S cont);

      continit : forall thread lprog
                        (INPROG : IdentMap.find thread prog = Some lprog),
          exists (state : (thread_lts thread).(Language.state)),
            ⟪ INK : K (CInit thread, existT _ _ state) ⟫ /\
            ⟪ INITST : state = (thread_lts thread).(Language.init) lprog ⟫;

      contpc : forall e (state : (thread_lts (Gtid e)).(Language.state))
                      (PC : pc (Gtid e) e)
                      (INK : K (CEvent (f e), existT _ _ state)),
                @sim_state G sim_normal C (Gtid e) state;
    }.
  
  Definition event_to_act (e : eventid) : actid :=
    if excluded_middle_informative (SEinit e)
    then
      match Sloc e with
      | Some l => InitEvent l
      | _      => InitEvent BinNums.xH
      end
    else
      let thread := Stid e in
      ThreadEvent thread
                  (countNatP (dom_rel (⦗ Stid_ thread ⦘⨾ Ssb ⨾ ⦗ eq e ⦘))
                             S.(ES.next_act)).
  Notation "'g'" := (event_to_act).
  Notation "'fdom'" := (C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘)) (only parsing).

  Record simrel :=
    { gwf   : Execution.Wf G;
      gprclos : forall thread m n (LT : m < n)
                       (EE : GE (ThreadEvent thread n)),
          GE (ThreadEvent thread m);
      tccoh : tc_coherent G sc TC;
      rmwclos : forall r w (RMW : Grmw r w), C r <-> C w;
      swf   : ES.Wf S;
      scons : @es_consistent S Weakestmo;
      
      scont : simrel_cont;

      fgtrip : ⦗ fdom ⦘ ⨾ ↑ (compose g f) ⊆ eq;
      gew  : g □ Sew  ⊆ eq;
      gco  : g □ Sco  ⊆ Gco;
      gjf  : g □ Sjf  ⊆ Gvf;
      grmw : g □ Srmw ⊆ Grmw;

      fco : f □ ⦗ fdom ⦘ ⨾ Gco ⨾ ⦗ fdom ⦘ ⊆ Sco;

      cimgNcf : ⦗ f □₁ fdom ⦘ ⨾ Scf ⨾ ⦗ f □₁ fdom ⦘ ≡ ∅₂;
      
      complete_fdom :
        (f □₁ fdom) ∩₁ SR ⊆₁ codom_rel (⦗ f □₁ fdom ⦘ ⨾ Srf);

      finj : inj_dom fdom f;  
      fimg : f □₁ fdom ⊆₁ SE;
      foth : (f □₁ set_compl fdom) ∩₁ SE ≡₁ ∅;
      flab : forall e (CI : (C ∪₁ I) e),
          Slab e.(f) = Glab e;
      
      glab : forall e,
          same_label_up_to_value (Slab e) (Glab (g e));

      (* To be able to show that `ftid` holds after a simulation step,
         we use Logic.FunctionalExtensionality. *)
      ftid : compose Stid f = Gtid;

      finitIncl : S.(ES.acts_init_set) ⊆₁ f □₁ (is_init ∩₁ GE);

      vis  : f □₁ fdom ⊆₁ vis S;

      (* sbF : f □ Gsb ⨾ ⦗ C ⦘ ⊆ Ssb; *)
      (* sbPrcl : Ssb ⨾ ⦗ f □₁ C ⦘ ⊆ ⦗ f □₁ C ⦘ ⨾ Ssb; *)
    }.

  Record forward_pair (e : actid) (e' : eventid) :=
    { fp_tcstep : trav_step G sc TC (mkTC (C ∪₁ eq e) I);
      fp_inGE   : GE e;
      fp_inSE   : SE e'; 
      fp_tidEq  : Stid e' = Gtid e;
      fp_labEq  : Slab e' = Glab e;
      fp_covsb  : Ssb ⨾ ⦗ eq e' ⦘ ⊆ ⦗ f □₁ C ⦘ ⨾ Ssb;
      fp_sbEq   : upd f e e' □ (Gsb ⨾ ⦗ eq e ⦘) ≡ Ssb ⨾ ⦗ eq e' ⦘;
      fp_imgrf  : upd f e e' □ (Grf ⨾ ⦗ eq e ⦘) ⊆ Srf;
    }.

  Section Properties.
    Variable SRC : simrel.

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

    Lemma finE e (SEE : SE (f e)) : GE e.
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
      autounfold with unfolderDb.
      ins. desf.
      eexists. eexists. splits; eauto.
      apply SRC.(gew).
      eexists. eexists.
      splits.
      { eapply ES.ew_sym; eauto. }
      all: by eauto.
    Qed.
    
    Lemma sbtot_fdom thread :
      is_total (f □₁ fdom ∩₁ Stid_ thread) Ssb.
    Proof.
      red. ins.
      apply NNPP. intros NN.
      eapply SRC.(cimgNcf).
      apply seq_eqv_l; split.
      { apply IWa. }
      apply seq_eqv_r; split.
      2: { apply IWb. }
      red.
      apply seq_eqv_l; split.
      { apply SRC.(fimg). apply IWa. }
      apply seq_eqv_r; split.
      2: { apply SRC.(fimg). apply IWb. }
      split.
      { red. red in IWa. red in IWb.
        desf. }
      red. intros [[AA|AA]|AA]; desf.
      all: apply NN; auto.
    Qed.

    Lemma gE : g □₁ SE ⊆₁ GE.
    Proof.
      (* TODO. It should follow from definition of g. *)
    Admitted.

    Lemma gsb : g □ Ssb ⊆ Gsb.
    Proof.
      (* TODO. It should follow from definition of g. *)
    Admitted.

    Lemma flaboth e :
          same_label_up_to_value (Slab e.(f)) (Glab e).
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
           { red. ins. red in H. desf. }
           red. splits; ins.
           2: { symmetry in AA.
                eapply GPROG in AA. desf.
                cdes AA. exists s.
                red. splits; auto.
                  by rewrite PEQ. }
           split; intros XX; [|omega].
           exfalso. apply NPC. clear NPC.
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
        autounfold with unfolderDb. eauto. }
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
      { by rewrite <- SRC.(ftid). }
      simpls. rewrite TT in KK.
      eapply contpc in PC; eauto.
      eexists. eexists.
      splits; eauto.
      unfold ES.cont_sb_dom. simpls.
      arewrite (Stid_ (Stid (f e)) ⊆₁ fun _ => True).
      rewrite set_inter_full_l.
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
   Admitted.

  End Properties.
End SimRel.