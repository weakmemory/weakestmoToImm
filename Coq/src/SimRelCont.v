Require Import Program.Basics Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CombRelations SimTraversal SimulationRel AuxRel.
Require Import AuxRel AuxDef EventStructure Consistency BasicStep EventToAction LblStep.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelCont.
  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.

  Notation "'SE'" := S.(ES.acts_set).
  Notation "'SEinit'" := S.(ES.acts_init_set).
  Notation "'SEninit'" := S.(ES.acts_ninit_set).

  Notation "'Stid'" := (S.(ES.tid)).
  Notation "'Slab'" := (S.(ES.lab)).
  Notation "'Sloc'" := (loc S.(ES.lab)).

  Notation "'K'" := S.(ES.cont_set).

  Notation "'STid' t" := (fun x => Stid x = t) (at level 1).

  Notation "'Ssb'" := (S.(ES.sb)).
  Notation "'Scf'" := (S.(ES.cf)).
  Notation "'Srmw'" := (S.(ES.rmw)).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).

  Notation "'Gtid'" := (tid).
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gloc'" := (loc G.(lab)).
  
  Notation "'GTid' t" := (fun x => tid x = t) (at level 1).
  Notation "'GNTid' t" := (fun x => tid x <> t) (at level 1).

  Notation "'Gsb'" := (G.(sb)).
  Notation "'Grmw'" := (G.(rmw)).

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

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).
        
  Definition pc thread :=
    C ∩₁ GTid thread \₁ dom_rel (Gsb ⨾ ⦗ C ⦘).

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

      contpc : forall e (state : (thread_st (Stid e)))
                      (PC : pc (Stid e) (e2a S e))
                      (INK : K (CEvent e, thread_cont_st (Stid e) state)),
          @sim_state G sim_normal C (Stid e) state;
    }.

  Section SimRelContProps. 
    Variable WF : ES.Wf S.
    Variable SRC : simrel_cont.

    Lemma contstateE k (st : thread_st (ES.cont_thread S k))
          (INK : K (k, thread_cont_st (ES.cont_thread S k) st)) :
      acts_set st.(ProgToExecution.G) ≡₁ (e2a S) □₁ (ES.cont_sb_dom S k \₁ SEinit).
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
          apply ES.sb_tid; auto. generalize BB. basic_solver. }
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

End SimRelCont.

Section SimRelContLemmas. 
  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G  : execution.
  Variable GPROG : program_execution prog G.
  Variable TC : trav_config.
  Variable WF : ES.Wf S.
  Variable SRK : simrel_cont prog S G TC.
  
  Notation "'SE' S" := S.(ES.acts_set) (at level 10).
  Notation "'SEinit' S" := S.(ES.acts_init_set) (at level 10).
  Notation "'SEninit' S" := S.(ES.acts_ninit_set) (at level 10).
  Notation "'Stid' S" := (S.(ES.tid)) (at level 10).
  Notation "'Slab' S" := S.(ES.lab) (at level 10).
  Notation "'Sloc' S" := (loc S.(ES.lab)) (at level 10).

  Notation "'K' S" := (S.(ES.cont_set)) (at level 10).

  Notation "'Stid_' t" := (fun x => Stid x = t) (at level 1).

  Notation "'Ssb' S" := S.(ES.sb) (at level 10).
  Notation "'Srmw' S" := S.(ES.rmw) (at level 10).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).

  Notation "'Glab'" := (G.(lab)).
  Notation "'Gtid'" := (tid).

  Notation "'Gtid_' t" := (fun x => tid x = t) (at level 1).
  Notation "'GNtid_' t" := (fun x => tid x <> t) (at level 1).

  Notation "'Gsb'" := (G.(sb)).
  Notation "'Grmw'" := G.(rmw).

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Notation "'thread_syntax' tid"  := 
    (Language.syntax (thread_lts tid)) (at level 10, only parsing).  

  Notation "'thread_st' tid" := 
    (Language.state (thread_lts tid)) (at level 10, only parsing).

  Notation "'thread_init_st' tid" := 
    (Language.init (thread_lts tid)) (at level 10, only parsing).

  Notation "'thread_cont_st' tid" :=
    (fun st => existT _ (thread_lts tid) st) (at level 10, only parsing).

  Notation "'cont_lang'" :=
    (fun S k => thread_lts (ES.cont_thread S k)) (at level 10, only parsing).

  Lemma basic_step_simrel_cont k k' e e' S'
        (st st' : thread_st (ES.cont_thread S k))
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e e' S S')
        (STCOV : C ∩₁ Gtid_ (ES.cont_thread S k) ⊆₁ acts_set st.(ProgToExecution.G)) : 
    simrel_cont prog S' G TC.
  Proof. 
    cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor; eauto. }

    assert (Stid S' (opt_ext e e') = ES.cont_thread S k) as TIDee.
    { edestruct e'; simpl;
        [eapply ESBasicStep.basic_step_tid_e' | eapply ESBasicStep.basic_step_tid_e];
        eauto. }

    assert (st'.(eindex) = 1 + ES.seqn S' (opt_ext e e')) as ST_IDX. 
    { edestruct lbl_step_cases as [l [l' HH]]; eauto.
      { eapply contwf; eauto. }
      { apply STEP. }
      edestruct HH as [EE _].
      apply opt_to_list_app_singl in EE.
      destruct EE as [eqLBL eqLBL'].
      edestruct e'; simpl; unfold opt_ext.
      { destruct HH as [_ [HH | HH]]. 
        { destruct HH as [_ [_ [_ [LBL _]]]].
          subst l'. rewrite LBL in LABEL'. exfalso. auto. } 
        destruct HH as [IDX _]. 
        erewrite IDX. simpl. 
        erewrite ESBasicStep.basic_step_seqn_e'; eauto.
        arewrite (eindex st = ES.seqn S' e); [|omega].
        edestruct k. 
        { erewrite continit; eauto.
          erewrite ESBasicStep.basic_step_seqn_kinit; eauto. }
        erewrite contseqn; eauto.
        erewrite <- ESBasicStep.basic_step_seqn_kevent; eauto. }
      destruct HH as [_ [HH | HH]]. 
      { destruct HH as [IDX _]. 
        erewrite IDX. simpl. 
        edestruct k. 
        { erewrite continit; eauto.
          erewrite ESBasicStep.basic_step_seqn_kinit; eauto. }
        erewrite contseqn; eauto.
        erewrite <- ESBasicStep.basic_step_seqn_kevent; eauto. }
      destruct HH as [_ [_ [_ HH]]].
      destruct HH as [ordr [ordw [loc [valr [vaw [_ LBL]]]]]].
      subst l'. rewrite LBL in LABEL'. exfalso. auto. }

    split.

    (* contlang *)
    { intros kk lang st'' INK.  
      eapply ESBasicStep.basic_step_cont_set in INK; eauto.
      unfold set_union in INK. destruct INK as [HA | HB]. 
      { erewrite ESBasicStep.basic_step_cont_thread; eauto.
          by eapply SRK in HA. }
      inversion HB.
      rewrite <- KCE.
      erewrite ESBasicStep.basic_step_cont_thread_k with (k' := k').
      all : eauto. }

    (* contwf *)
    { intros kk st'' KK. 
      eapply ESBasicStep.basic_step_cont_set in KK; eauto.
      unfold set_union in KK. 
      destruct KK as [KK | KK].
      { erewrite ESBasicStep.basic_step_cont_thread; eauto.
        apply SRK.
        erewrite <- ESBasicStep.basic_step_cont_thread; eauto. }
      assert (kk = CEvent (opt_ext e e')) as kkEQ.
      { by inversion KK. }
      rewrite <- kkEQ in *.
      assert (ES.cont_thread S' kk = (ES.cont_thread S k)) as Hkk.
      { by rewrite kkEQ. }
      rewrite Hkk in *.
      inversion KK as [HH].
      apply inj_pair2 in HH. 
      rewrite <- HH.
      eapply wf_thread_state_steps.
      { eapply SRK; eauto. }
      eapply ilbl_steps_in_steps.
      do 2 econstructor. 
      eapply STEP. }

    (* contstable *)
    { intros kk st'' KK. 
      eapply ESBasicStep.basic_step_cont_set in KK; eauto.
      unfold set_union in KK. 
      destruct KK as [KK | KK].
      { erewrite ESBasicStep.basic_step_cont_thread; eauto.
        apply SRK.
        erewrite <- ESBasicStep.basic_step_cont_thread; eauto. }
      assert (kk = CEvent (opt_ext e e')) as kkEQ.
      { by inversion KK. }
      rewrite <- kkEQ in *.
      assert (ES.cont_thread S' kk = (ES.cont_thread S k)) as Hkk.
      { by rewrite kkEQ. }
      rewrite Hkk in *. 
      inversion KK as [HH].
      apply inj_pair2 in HH. 
      rewrite <- HH.
      simpls. 
      unfold ilbl_step in STEP.
      apply seqA in STEP.
      apply seq_eqv_r in STEP.
      desf. }

    (* contrun *)
    { intros thread lprog INP.
      edestruct SRK.(contrun) as [st'' [Kinit ISTEP]]; eauto.    
      eexists; split; eauto.
      eapply ESBasicStep.basic_step_cont_set; eauto.
      left. eauto. }

    (* contseqn *)
    { intros thread st'' KK. 
      eapply ESBasicStep.basic_step_cont_set in KK; eauto.
      unfold set_union in KK. 
      destruct KK as [KK | KK].
      { by eapply SRK. }
      exfalso. inversion KK. }
    { intros x st'' KK. 
      eapply ESBasicStep.basic_step_cont_set in KK; eauto.
      unfold set_union in KK. 
      destruct KK as [KK | KK].
      { assert (SE S x) as SEx.
        { eapply ES.K_inEninit; eauto. }
        erewrite ESBasicStep.basic_step_seqn_eq_dom; eauto.
        eapply SRK. erewrite <- ESBasicStep.basic_step_tid_eq_dom; eauto. }
      assert (x = opt_ext e e') as xEQ.
      { by inversion KK. }
      rewrite xEQ, TIDee in KK. 
      inversion KK as [HST].
      apply inj_pair2 in HST.
      congruence. }

    (* contpc *)
    intros x st'' PC KK. 
    eapply ESBasicStep.basic_step_cont_set in KK; eauto.
    unfold set_union in KK. 
    destruct KK as [KK | KK].
    { assert (Stid S' x = Stid S x) as EQtid. 
      { eapply ESBasicStep.basic_step_tid_eq_dom; eauto.  
        eapply ES.K_inEninit; eauto. } 
      assert (e2a S' x = e2a S x) as EQe2a. 
      { eapply basic_step_e2a_eq_dom; eauto.  
        eapply ES.K_inEninit; eauto. } 
      rewrite EQtid, EQe2a in *. 
      eapply contpc; eauto. }
    exfalso. 
    assert (x = opt_ext e e') as xEQ.
    { by inversion KK. }
    rewrite xEQ in KK. 
    rewrite TIDee in KK. 
    inversion KK as [HST].
    apply inj_pair2 in HST. 
    assert (e2a S' x = ThreadEvent ((Stid S') x) (ES.seqn S' x)) as EQe2a.
    { unfold e2a. 
      destruct 
        (excluded_middle_informative ((Stid S') x = tid_init)) 
        as [INIT | TE]; auto. 
      exfalso. eapply ES.init_tid_K; eauto. 
      do 2 eexists; splits; eauto. congruence. }
    rewrite EQe2a in PC. 
    unfold pc in PC.
    destruct PC as [CTIDx nDOMx].
    rewrite xEQ, TIDee in CTIDx.
    apply STCOV in CTIDx.
    eapply acts_rep in CTIDx.
    2 : { eapply contwf; eauto. }
    assert (st.(eindex) < st'.(eindex)) as IDX_LE. 
    { edestruct lbl_step_cases as [l [l' HH]]; eauto.
      { eapply contwf; eauto. }
      { apply STEP. }
      desf; omega. }
    desf. omega. 
  Qed.

End SimRelContLemmas.