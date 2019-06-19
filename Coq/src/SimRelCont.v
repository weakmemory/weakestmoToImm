Require Import Program.Basics Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CombRelations SimTraversal SimulationRel AuxRel.
Require Import AuxRel.
Require Import AuxDef.
Require Import EventStructure.
Require Import Consistency.
Require Import BasicStep.
Require Import EventToAction.
Require Import LblStep.
Require Import ProgES.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelCont.
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

  Notation "'K'" := (ES.cont_set S) (at level 1).

  Notation "'STid' t" := (fun x => Stid x = t) (at level 1).

  Notation "'Ssb'" := (S.(ES.sb)).
  Notation "'Scf'" := (S.(ES.cf)).
  Notation "'Srmw'" := (S.(ES.rmw)).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).

  Notation "'Glab'" := (lab G).
  Notation "'Gloc'" := (Events.loc (lab G)).
  Notation "'Gtid'" := (Events.tid).
  
  Notation "'GTid' t" := (fun x => Gtid x = t) (at level 1).
  Notation "'GNTid' t" := (fun x => Gtid x <> t) (at level 1).

  Notation "'Gsb'" := (Execution.sb G).
  Notation "'Grmw'" := (Execution.rmw G).

  Notation "'thread_syntax' t"  := 
    (Language.syntax (thread_lts t)) (at level 10, only parsing).  

  Notation "'thread_st' t" := 
    (Language.state (thread_lts t)) (at level 10, only parsing).

  Notation "'thread_init_st' t" := 
    (Language.init (thread_lts t)) (at level 10, only parsing).
  
  Notation "'thread_cont_st' t" :=
    (fun st => existT _ (thread_lts t) st) (at level 10, only parsing).

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
          stable_state state;

      contrun : forall thread (lprog : thread_syntax thread) 
                       (INPROG : IdentMap.find thread prog = Some lprog),
          exists (state : thread_st thread),
            ⟪ INK : K (CInit thread, thread_cont_st thread state) ⟫ /\
            ⟪ INITST : (istep thread [])＊ (thread_init_st thread lprog) state⟫;

      contreach :
        forall k (state : thread_st (ES.cont_thread S k))
               (lprog : thread_syntax (ES.cont_thread S k)) 
               (INPROG : IdentMap.find (ES.cont_thread S k) prog =
                         Some lprog)
               (INK : K (k, thread_cont_st (ES.cont_thread S k) state)),
          (step (ES.cont_thread S k))＊
            (thread_init_st (ES.cont_thread S k) lprog)
            state;

      continit : forall thread (state : thread_st thread)
                        (INKi : K (CInit thread, thread_cont_st thread state)),
          state.(eindex) = 0;

      contseqn : forall e (state : thread_st (Stid e))
                        (INKe : K (CEvent e, thread_cont_st (Stid e) state)),
          state.(eindex) = 1 + ES.seqn S e;

      (* contpc : forall e (state : thread_st (Stid e)) *)
      (*                 (XE : X e) *)
      (*                 (PC : pc (Stid e) (e2a S e)) *)
      (*                 (INK : K S (CEvent e, thread_cont_st (Stid e) state)), *)
      (*     @sim_state G sim_normal C (Stid e) state; *)

      (* continitstate : *)
      (*   forall thread (state : thread_st thread) *)
      (*          (CEMP : C ∩₁ GTid thread ⊆₁ ∅) *)
      (*          (INK : K S (CInit thread, thread_cont_st thread state)), *)
      (*     @sim_state G sim_normal C thread state; *)
      
      contsimstate :
        forall thread (lprog : thread_syntax thread) 
               (INPROG : IdentMap.find thread prog = Some lprog),
          exists k (state : thread_st (ES.cont_thread S k)),
            ⟪ THK   : thread = ES.cont_thread S k ⟫ /\
            ⟪ INK   : K (k, thread_cont_st (ES.cont_thread S k) state) ⟫ /\
            ⟪ INX   : ES.cont_sb_dom S k ≡₁
                       SEinit ∪₁
                       X ∩₁ STid (ES.cont_thread S k) ∩₁ e2a S ⋄₁ C ⟫ /\
            ⟪ SIMST : @sim_state G sim_normal C (ES.cont_thread S k) state ⟫;
    }.

End SimRelCont.

Section SimRelContLemmas. 
  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G  : execution.
  Variable GPROG : program_execution prog G.
  Variable TC : trav_config.
  Variable X : eventid -> Prop.
  Variable WF : ES.Wf S.
  Variable SRK : simrel_cont prog S G TC X.
  
  Notation "'SE' S" := S.(ES.acts_set) (at level 10).
  Notation "'SEinit' S" := S.(ES.acts_init_set) (at level 10).
  Notation "'SEninit' S" := S.(ES.acts_ninit_set) (at level 10).
  Notation "'Stid' S" := (S.(ES.tid)) (at level 10).
  Notation "'Slab' S" := S.(ES.lab) (at level 10).
  Notation "'Sloc' S" := (loc S.(ES.lab)) (at level 10).

  Notation "'K' S" := (S.(ES.cont_set)) (at level 10).

  Notation "'Ssb' S" := S.(ES.sb) (at level 10).
  Notation "'Srmw' S" := S.(ES.rmw) (at level 10).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).

  Notation "'Glab'" := (lab G).
  Notation "'Gloc'" := (Events.loc (lab G)).
  Notation "'Gtid'" := (Events.tid).

  Notation "'GTid_' t" := (fun x => Gtid x = t) (at level 1).
  Notation "'GNTid_' t" := (fun x => Gtid x <> t) (at level 1).

  Notation "'Gsb'" := (Execution.sb G).
  Notation "'Grmw'" := (Execution.rmw G).

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Notation "'thread_syntax' t"  := 
    (Language.syntax (thread_lts t)) (at level 10, only parsing).  

  Notation "'thread_st' t" := 
    (Language.state (thread_lts t)) (at level 10, only parsing).

  Notation "'thread_init_st' t" := 
    (Language.init (thread_lts t)) (at level 10, only parsing).

  Notation "'thread_cont_st' t" :=
    (fun st => existT _ (thread_lts t) st) (at level 10, only parsing).

  Notation "'cont_lang'" :=
    (fun S k => thread_lts (ES.cont_thread S k)) (at level 10, only parsing).

  Notation "'STid'" := (fun S t x => ES.tid S x = t) (at level 1).
  
  Lemma kstate_instrs k (state : thread_st (ES.cont_thread S k))
        (lprog : thread_syntax (ES.cont_thread S k))
        (INPROG : IdentMap.find (ES.cont_thread S k) prog = Some lprog)
        (INK : K S (k, thread_cont_st (ES.cont_thread S k) state)) :
    lprog = instrs state.
  Proof.
    eapply contreach in INK; eauto.
    apply steps_same_instrs in INK. simpls.
  Qed.

  Lemma basic_step_simrel_cont k k' e e' S'
        (st st' : thread_st (ES.cont_thread S k))
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S')
        (XE : X ⊆₁ SE S) :
        (* (STCOV : C ∩₁ GTid_ (ES.cont_thread S k) ⊆₁ acts_set st.(ProgToExecution.G)) :  *)
    simrel_cont prog S' G TC X.
  Proof. 
    cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }

    assert (Stid S' (opt_ext e e') = ES.cont_thread S k) as TIDee.
    { edestruct e'; simpl;
        [eapply basic_step_tid_e' | eapply basic_step_tid_e];
        eauto. }

    assert (st'.(eindex) = 1 + ES.seqn S' (opt_ext e e')) as ST_IDX. 
    { edestruct ilbl_step_cases as [l [l' HH]]; eauto.
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
        erewrite basic_step_seqn_e'; eauto.
        arewrite (eindex st = ES.seqn S' e); [|omega].
        edestruct k. 
        { erewrite continit; eauto.
          erewrite basic_step_seqn_kinit; eauto. }
        erewrite contseqn; eauto.
        erewrite <- basic_step_seqn_kevent; eauto. }
      destruct HH as [_ [HH | HH]]. 
      2: by desf.
      destruct HH as [IDX _]. 
      erewrite IDX. simpl. 
      edestruct k. 
      { erewrite continit; eauto.
        erewrite basic_step_seqn_kinit; eauto. }
      erewrite contseqn; eauto.
      erewrite <- basic_step_seqn_kevent; eauto. }

    split.

    (* contlang *)
    { intros kk lang st'' INK.  
      eapply basic_step_cont_set in INK; eauto.
      unfold set_union in INK. destruct INK as [HA | HB]. 
      { erewrite basic_step_cont_thread; eauto.
          by eapply SRK in HA. }
      inversion HB.
      rewrite <- KCE.
      erewrite basic_step_cont_thread_k with (k' := k').
      all : eauto. }

    (* contwf *)
    { intros kk st'' KK. 
      eapply basic_step_cont_set in KK; eauto.
      unfold set_union in KK. 
      destruct KK as [KK | KK].
      { erewrite basic_step_cont_thread; eauto.
        apply SRK.
        erewrite <- basic_step_cont_thread; eauto. }
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
      eapply lbl_steps_in_steps.
      do 2 econstructor. 
      eapply STEP. }

    (* contstable *)
    { intros kk st'' KK. 
      eapply basic_step_cont_set in KK; eauto.
      unfold set_union in KK. 
      destruct KK as [KK | KK].
      { eapply SRK.
        erewrite <- basic_step_cont_thread; eauto. }
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
      eapply basic_step_cont_set; eauto.
      left. eauto. }

    (* contreach *)
    { ins. red in INK. rewrite CONT' in INK.
      apply in_inv in INK. destruct INK as [INK|INK].
      2: { assert (ES.cont_thread S' k0 = ES.cont_thread S k0) as HH.
           { eapply basic_step_cont_thread; eauto. }
           rewrite HH in *.
           eapply contreach; eauto. }
      assert (k0 = k') as YY by inv INK; rewrite YY in *.
      assert (ES.cont_thread S' k' = ES.cont_thread S k) as BB.
      { eapply basic_step_cont_thread_k; eauto. }
      rewrite BB in *.
      assert (state = st'); subst.
      { apply pair_inj in INK. destruct INK as [AA INK]; subst.
        inv INK. }
      apply rt_rt. exists st. split.
      { eapply contreach; eauto. }
      apply inclusion_t_rt.
      eapply ilbl_step_in_steps; eauto. }

    (* contseqn *)
    { intros thread st'' KK. 
      eapply basic_step_cont_set in KK; eauto.
      unfold set_union in KK. 
      destruct KK as [KK | KK].
      { by eapply SRK. }
      exfalso. inversion KK. }
    { intros x st'' KK. 
      eapply basic_step_cont_set in KK; eauto.
      unfold set_union in KK. 
      destruct KK as [KK | KK].
      { assert (SE S x) as SEx.
        { eapply ES.K_inEninit; eauto. }
        erewrite basic_step_seqn_eq_dom; eauto.
        eapply SRK. erewrite <- basic_step_tid_eq_dom; eauto. }
      assert (x = opt_ext e e') as xEQ.
      { by inversion KK. }
      rewrite xEQ, TIDee in KK. 
      inversion KK as [HST].
      apply inj_pair2 in HST.
      congruence. }

    ins.
    edestruct contsimstate as [ok]; eauto. desf.
    exists ok. exists state.
    arewrite (ES.cont_thread S' ok = ES.cont_thread S ok).
    { eapply basic_step_cont_thread; eauto. }
    splits; auto.
    { eapply basic_step_cont_set; eauto. by left. }
    arewrite (ES.cont_sb_dom S' ok ≡₁ ES.cont_sb_dom S ok).
    { eapply basic_step_cont_sb_dom_eq; eauto. }
    rewrite INX.
    apply set_union_Propere.
    { symmetry. eapply basic_step_acts_init_set; eauto. }
    arewrite (X ∩₁ (STid S' (ES.cont_thread S ok)) ≡₁
              X ∩₁ (STid S  (ES.cont_thread S ok))).
    { unfolder. split; intros x [XX BB]; desf; splits; auto.
      all: rewrite <- BB.
      symmetry.
      all: eapply basic_step_tid_eq_dom; eauto. }
    rewrite set_interC with (s:=X).
    rewrite !set_interA.
    arewrite (X ∩₁ e2a S' ⋄₁ C ≡₁ X ∩₁ e2a S ⋄₁ C).
    2: done.
    unfolder. split; ins; desf; splits; auto.
    { erewrite <- basic_step_e2a_eq_dom; eauto. }
    erewrite basic_step_e2a_eq_dom; eauto. 
  Qed.

End SimRelContLemmas.
