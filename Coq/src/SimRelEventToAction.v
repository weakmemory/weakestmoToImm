Require Import Program.Basics Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     SimTraversal SimTraversalProperties
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CombRelations SimTraversal SimulationRel AuxRel.
Require Import AuxRel AuxDef EventStructure Consistency BasicStep 
        CertRf CertGraph EventToAction LblStep SimRelCont.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelEventToAction.
  Variable S : ES.t.
  Variable G : execution.
  Variable sc : relation actid.

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
  
  Notation "'Gvf'" := (furr G sc).

  Notation "'e2a'" := (e2a S).

  Record simrel_e2a := 
    { e2a_GE : e2a □₁ SE ⊆₁ GE;
      e2a_GEinit : GEinit ⊆₁ e2a □₁ SEinit;

      e2a_lab : same_lab_u2v_dom SE Slab (Glab ∘ e2a);

      e2a_rmw : e2a □ Srmw ⊆ Grmw;
      e2a_jf  : e2a □ Sjf  ⊆ Gvf;
      e2a_ew  : e2a □ Sew  ⊆ eq;
      e2a_co  : e2a □ Sco  ⊆ Gco;
      
      e2a_jfrmw : e2a □ (Sjf ⨾ Srmw) ⊆ Grf ⨾ Grmw;
    }.

  Record simrel_a2e (a2e : actid -> eventid) (a2eD : actid -> Prop) := 
    { a2e_inj : inj_dom a2eD a2e;
      a2e_img : a2e □₁ a2eD ⊆₁ SE;
      a2e_fix : fixset a2eD (e2a ∘ a2e);
      (* Do we really need this ? *)
      (* a2e_oth : (a2e □₁ set_compl aD) ∩₁ SE ≡₁ ∅; *)
    }. 

  Section SimRelEventToActionProps. 
    Variable prog : Prog.t.
    Variable GPROG : program_execution prog G.
    Variable PROG_NINIT : ~ (IdentMap.In tid_init prog).
    Variable WF : ES.Wf S.
    Variable SRE2A : simrel_e2a.

    Lemma e2a_same_Einit : 
      e2a □₁ SEinit ≡₁ GEinit.
    Proof. 
      split. 
      { eapply e2a_Einit; eauto. apply SRE2A. }
      unfold ES.acts_ninit_set, ES.acts_init_set, ES.acts_set. 
      unfolder. intros a [INITa GEa].
      edestruct e2a_GEinit as [e [[INITe SEe] gEQ]].
      
      1-2 : unfolder; eauto.  
      eexists; splits; eauto. 
    Qed.

    Ltac e2a_type t :=
      intros x [y HH]; desf;
      eapply t in HH;
        [|by apply same_lab_u2v_dom_comm; apply SRE2A];
      split; [apply SRE2A.(e2a_GE); red; eexists; split; eauto|]; apply HH.
    
    Lemma e2a_R : e2a □₁ (SE ∩₁ SR) ⊆₁ GE ∩₁ GR.
    Proof. e2a_type same_lab_u2v_dom_is_r. Qed.
    
    Lemma e2a_W : e2a □₁ (SE ∩₁ SW) ⊆₁ GE ∩₁ GW.
    Proof. e2a_type same_lab_u2v_dom_is_w. Qed.

    Lemma e2a_F : e2a □₁ (SE ∩₁ SF) ⊆₁ GE ∩₁ GF.
    Proof. e2a_type same_lab_u2v_dom_is_f. Qed.

    Lemma e2a_Rel : e2a □₁ (SE ∩₁ SRel) ⊆₁ GE ∩₁ GRel.
    Proof. e2a_type same_lab_u2v_dom_is_rel. Qed.

    Lemma e2a_same_loc : 
      e2a □ restr_rel SE (same_loc Slab) ⊆ restr_rel GE (same_loc Glab).
    Proof.
      intros x y HH. red in HH. desf.
      eapply same_lab_u2v_dom_same_loc in HH.
      2: { apply same_lab_u2v_dom_comm. apply SRE2A. }
      red in HH. desf. 
      red. splits.
      apply HH.
      all: by eapply e2a_GE; eauto; eexists; eauto.
    Qed.
    
    Lemma e2a_rf (CONS : @es_consistent S Weakestmo) : 
      e2a □ Srf ≡ e2a □ Sjf.
    Proof.
      destruct SRE2A.
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
      eapply e2a_ew; auto. 
      eexists. eexists.
      splits.
      { eapply ES.ew_sym; eauto. }
      all: by eauto.
    Qed.

    Lemma e2a_rs : e2a □ Srs ⊆ Grs. 
    Proof. 
      rewrite rs_alt; auto.
      rewrite !collect_rel_seqi.
      rewrite !set_collect_eqv.
      rewrite !e2a_W.
      repeat apply seq_mori; eauto with hahn.
      2: { rewrite collect_rel_crt. eauto using clos_refl_trans_mori, e2a_jfrmw. }
      rewrite ES.sbE; auto.
      rewrite wf_sbE.
      rewrite <- !restr_relE.
      rewrite <- restr_inter_absorb_r.
      rewrite <- restr_inter_absorb_r with (r':=same_loc Slab).
      rewrite collect_rel_cr.
      rewrite collect_rel_interi. 
      apply clos_refl_mori, inter_rel_mori. 
      { rewrite !restr_relE, <- wf_sbE, <- ES.sbE; auto. 
        eapply e2a_sb; eauto; apply SRE2A. }
      apply e2a_same_loc.
    Qed.

    Lemma e2a_release : e2a □ Srelease ⊆ Grelease.
    Proof. 
      rewrite release_alt; auto.
      rewrite !collect_rel_seqi, !collect_rel_cr, !collect_rel_seqi.
      rewrite !set_collect_eqv.
      arewrite (SF ∪₁ SW ⊆₁ fun _ => True).
      arewrite (SE ∩₁ (fun _ : eventid => True) ⊆₁ SE) by basic_solver.
      rewrite e2a_Rel, e2a_rs, e2a_sb, e2a_F.
      { unfold imm_s_hb.release. basic_solver 10. }
      all: eauto; apply SRE2A.
    Qed.

  End SimRelEventToActionProps. 

End SimRelEventToAction.

Section SimRelEventToActionLemmas.

  Variable prog : Prog.t.
  Variable PROG_NINIT : ~ (IdentMap.In tid_init prog).
  Variable S : ES.t.
  Variable G : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable GPROG : program_execution prog G.
  Variable WF : ES.Wf S.

  Notation "'SE' S" := S.(ES.acts_set) (at level 10).
  Notation "'SEinit' S" := S.(ES.acts_init_set) (at level 10).
  Notation "'SEninit' S" := S.(ES.acts_ninit_set) (at level 10).

  Notation "'Stid' S" := (S.(ES.tid)) (at level 10).
  Notation "'Slab' S" := (S.(ES.lab)) (at level 10).
  Notation "'Sloc' S" := (loc S.(ES.lab)) (at level 10).

  Notation "'K' S" := S.(ES.cont_set) (at level 10).

  Notation "'STid' S" := (fun t e => S.(ES.tid) e = t) (at level 10).

  Notation "'SR' S" := (fun a => is_true (is_r S.(ES.lab) a)) (at level 10).
  Notation "'SW' S" := (fun a => is_true (is_w S.(ES.lab) a)) (at level 10).
  Notation "'SF' S" := (fun a => is_true (is_f S.(ES.lab) a)) (at level 10).

  Notation "'SRel' S" := (fun a => is_true (is_rel S.(ES.lab) a)) (at level 10).

  Notation "'Ssb' S" := (S.(ES.sb)) (at level 10).
  Notation "'Scf' S" := (S.(ES.cf)) (at level 10).
  Notation "'Srmw' S" := (S.(ES.rmw)) (at level 10).
  Notation "'Sjf' S" := (S.(ES.jf)) (at level 10).
  Notation "'Sjfi' S" := (S.(ES.jfi)) (at level 10).
  Notation "'Sjfe' S" := (S.(ES.jfe)) (at level 10).
  Notation "'Srf' S" := (S.(ES.rf)) (at level 10).
  Notation "'Srfi' S" := (S.(ES.rfi)) (at level 10).
  Notation "'Srfe' S" := (S.(ES.rfe)) (at level 10).
  Notation "'Sco' S" := (S.(ES.co)) (at level 10).
  Notation "'Sew' S" := (S.(ES.ew)) (at level 10).

  Notation "'Srs' S" := (S.(Consistency.rs)) (at level 10).
  Notation "'Srelease' S" := (S.(Consistency.release)) (at level 10).
  Notation "'Ssw' S" := (S.(Consistency.sw)) (at level 10).
  Notation "'Shb' S" := (S.(Consistency.hb)) (at level 10).

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
  
  Notation "'Gvf'" := (furr G sc).

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

  Lemma basic_step_e2a_e k k' e e' S' 
        (st st' : thread_st (ES.cont_thread S k))
        (SRK : simrel_cont prog S G TC)
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e e' S S') :
    e2a S' e = ThreadEvent (ES.cont_thread S k) (st.(eindex)).
  Proof. 
    cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (SE S' e) as SEe. 
    { eapply ESBasicStep.basic_step_acts_set; eauto. basic_solver. }
    unfold e2a. 
    destruct (excluded_middle_informative ((Stid S') e = tid_init)) as [INIT | nINIT]. 
    { exfalso. eapply ESBasicStep.basic_step_acts_ninit_set_e; eauto.
      unfold ES.acts_init_set. basic_solver. } 
    erewrite ESBasicStep.basic_step_tid_e; eauto.  
    edestruct k eqn:kEQ. 
    { erewrite ESBasicStep.basic_step_seqn_kinit. 
      { erewrite continit; eauto. }
      all : subst k; eauto. }
    erewrite ESBasicStep.basic_step_seqn_kevent with (k := k); eauto. 
    { erewrite contseqn; eauto. }
    all : subst k; eauto. 
  Qed.

  Lemma basic_step_e2a_e' k k' e e' S' 
        (st st' : thread_st (ES.cont_thread S k))
        (SRK : simrel_cont prog S G TC)
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e (Some e') S S') :
    e2a S' e' = ThreadEvent (ES.cont_thread S k) (1 + st.(eindex)).
  Proof. 
    cdes BSTEP_.
    assert (ESBasicStep.t e (Some e') S S') as BSTEP.
    { econstructor; eauto. }
    assert (SE S' e') as SEe'. 
    { eapply ESBasicStep.basic_step_acts_set; eauto. basic_solver. }
    unfold e2a. 
    destruct (excluded_middle_informative ((Stid S') e' = tid_init)) as [INIT | nINIT]. 
    { exfalso. eapply ESBasicStep.basic_step_acts_ninit_set_e'; eauto.
      unfold ES.acts_init_set. basic_solver. } 
    erewrite ESBasicStep.basic_step_tid_e'; eauto.  
    erewrite ESBasicStep.basic_step_seqn_e'; eauto.
    edestruct k eqn:kEQ.
    { erewrite ESBasicStep.basic_step_seqn_kinit.
      { erewrite continit; eauto. } 
      all : subst k; eauto. }
    erewrite ESBasicStep.basic_step_seqn_kevent with (k := k); eauto. 
    { erewrite contseqn; eauto. }
    all : subst k; eauto. 
  Qed.

  Lemma basic_step_cert_dom_ne k k' e e' S' 
        (st st' : thread_st (ES.cont_thread S k))
        (SRK : simrel_cont prog S G TC)
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e e' S S') 
        (STCOV : C ∩₁ GTid (ES.cont_thread S k) ⊆₁ acts_set st.(ProgToExecution.G)) : 
    ~ (cert_dom G TC (ES.cont_thread S k) st) (e2a S' e).
  Proof.
    cdes BSTEP_.
    red. intros HH.
    eapply cert_dom_alt in HH; eauto.
    destruct HH as [HA | HB].
    { destruct HA as [_ NTID].
      apply NTID.
      erewrite <- e2a_tid.
      eapply ESBasicStep.basic_step_tid_e; eauto. }
    erewrite basic_step_e2a_e in HB; eauto. 
    2 : eapply BSTEP_.
    eapply acts_rep in HB.
    2 : eapply SRK; eauto.
    desf. omega.
  Qed.

  Lemma basic_step_cert_dom_ne' k k' e e' S' 
        (st st' : thread_st (ES.cont_thread S k))
        (SRK : simrel_cont prog S G TC)
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e (Some e') S S') 
        (STCOV : C ∩₁ GTid (ES.cont_thread S k) ⊆₁ acts_set st.(ProgToExecution.G)) : 
    ~ (cert_dom G TC (ES.cont_thread S k) st) (e2a S' e').
  Proof.
    cdes BSTEP_.
    red. intros HH.
    eapply cert_dom_alt in HH; eauto.
    destruct HH as [HA | HB].
    { destruct HA as [_ NTID].
      apply NTID.
      erewrite <- e2a_tid.
      eapply ESBasicStep.basic_step_tid_e'; eauto. }
    erewrite basic_step_e2a_e' in HB; eauto. 
    2 : eapply BSTEP_.
    eapply acts_rep in HB.
    2 : eapply SRK; eauto.
    desf. omega.
  Qed.

  Lemma basic_step_cert_dom k k' e e' S' 
        (st st' : thread_st (ES.cont_thread S k))
        (SRK : simrel_cont prog S G TC)
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e e' S S') : 
    cert_dom G TC (ES.cont_thread S' k') st' ≡₁ 
             cert_dom G TC (ES.cont_thread S k) st ∪₁ 
               eq (e2a S' e) ∪₁ eq_opt (option_map (e2a S') e').
  Proof. 
    cdes BSTEP_.   
    assert (ESBasicStep.t e e' S S') as BSTEP. 
    { econstructor. eauto. }
    unfold cert_dom. 
    erewrite ESBasicStep.basic_step_cont_thread_k; eauto. 
    rewrite !set_unionA.
    do 2 (eapply set_union_Propere; auto). 
    edestruct lbl_step_cases as [l [l' HH]].
    { eapply SRK. eauto. }
    { apply STEP. }
    destruct HH as [LBLS HH].
    apply opt_to_list_app_singl in LBLS.
    destruct LBLS as [LA LB]. subst l l'. 
    destruct HH as [HA | HB].
    { destruct HA as [_ [ACTS [_ [LBL' _]]]].
      unfold eq_opt, option_map, opt_same_ctor in *.
      destruct e'; [desf|].
      etransitivity; [eapply ACTS|].
      apply set_union_Propere; auto. 
      erewrite basic_step_e2a_e; eauto. 
      basic_solver. }
    destruct HB as [_ [ACTS [_ [LBLS _]]]].
    destruct LBLS as [ordr [ordw [loc [valr [valw [LA LB]]]]]].
    unfold eq_opt, option_map, opt_same_ctor in *.
    destruct e'; [|desf].
    etransitivity; [eapply ACTS|].
    rewrite set_unionA.
    apply set_union_Propere; auto. 
    erewrite basic_step_e2a_e; eauto. 
    erewrite basic_step_e2a_e'; eauto. 
  Qed.

  Lemma basic_step_nupd_cert_dom k k' e S'
        (st st' : thread_st (ES.cont_thread S k))
        (SRK : simrel_cont prog S G TC)
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e None S S') :
    cert_dom G TC (ES.cont_thread S' k') st' ≡₁
             cert_dom G TC (ES.cont_thread S k) st ∪₁ eq (e2a S' e).
  Proof.
    erewrite basic_step_cert_dom; eauto. 
    unfold eq_opt, option_map. basic_solver.
  Qed.

  Lemma basic_step_e2a_E0_e TC' k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRK : simrel_cont prog S G TC)
        (CG : cert_graph G sc TC TC' (ES.cont_thread S k) st'')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
     E0 G TC' (ES.cont_thread S k) (e2a S' e).
  Proof. 
    cdes BSTEP_. simpl in BSTEP_.
    erewrite basic_step_e2a_e; eauto using BSTEP_. 
    eapply ilbl_step_E0_eindex; eauto. 
    { eapply SRK. eauto. }
    apply STEP.
  Qed.

  Lemma basic_step_e2a_E0_e' TC' k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRK : simrel_cont prog S G TC)
        (CG : cert_graph G sc TC TC' (ES.cont_thread S k) st'')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e (Some e') S S') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :
     E0 G TC' (ES.cont_thread S k) (e2a S' e').
  Proof. 
    cdes BSTEP_. simpl in BSTEP_.
    erewrite basic_step_e2a_e'; eauto. 
    eapply ilbl_step_E0_eindex'; eauto. 
    { eapply SRK. eauto. }
    { apply STEP. }
    red. ins. by subst lbl'. 
  Qed.

  Lemma basic_step_e2a_GE_e TC' k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRK : simrel_cont prog S G TC)
        (CG : cert_graph G sc TC TC' (ES.cont_thread S k) st'')
        (TCCOH : tc_coherent G sc TC')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e e' S S') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :     
    GE (e2a S' e).
  Proof. 
    cdes BSTEP_. 
    eapply E0_in_E; eauto.  
    eapply basic_step_e2a_E0_e; eauto.
  Qed.

  Lemma basic_step_e2a_GE_e' TC' k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRK : simrel_cont prog S G TC)
        (CG : cert_graph G sc TC TC' (ES.cont_thread S k) st'')
        (TCCOH : tc_coherent G sc TC')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e (Some e') S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
     GE (e2a S' e').
  Proof. 
    cdes BSTEP_.
    eapply E0_in_E; eauto.  
    eapply basic_step_e2a_E0_e'; eauto.
  Qed.

  Lemma basic_step_e2a_GE TC' k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRK : simrel_cont prog S G TC)
        (SRE2A : simrel_e2a S G sc)
        (CG : cert_graph G sc TC TC' (ES.cont_thread S k) st'')
        (TCCOH : tc_coherent G sc TC')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
     e2a S' □₁ SE S' ⊆₁ GE.
  Proof. 
    cdes BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor; eauto. }
    rewrite ESBasicStep.basic_step_acts_set; eauto.  
    rewrite !set_collect_union. 
    rewrite !set_subset_union_l.
    splits. 
    { erewrite set_collect_eq_dom; [eapply SRE2A|].
      eapply basic_step_e2a_eq_dom; eauto. } 
    { rewrite set_collect_eq.
      apply eq_predicate. 
      eapply basic_step_e2a_GE_e; eauto. }
    destruct e' as [e'|]; [|basic_solver]. 
    unfold eq_opt. 
    rewrite set_collect_eq.
    apply eq_predicate. 
    eapply basic_step_e2a_GE_e'; eauto. 
  Qed.

  Lemma basic_step_e2a_lab_e TC' k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRK : simrel_cont prog S G TC)
        (CG : cert_graph G sc TC TC' (ES.cont_thread S k) st'')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
     Slab S' e = lab (ProgToExecution.G st'') (e2a S' e).
  Proof. 
    cdes BSTEP_. simpl in BSTEP_.
    assert (Gtid (e2a S' e) = ES.cont_thread S k) as GTIDe.
    { rewrite <- e2a_tid. erewrite ESBasicStep.basic_step_tid_e; eauto. }
    assert (wf_thread_state (ES.cont_thread S k) st') as WFTS. 
    { eapply wf_thread_state_steps.
      { eapply SRK; eauto. }
      eapply ilbl_steps_in_steps.
      do 2 econstructor. eapply STEP. }
    arewrite ((Slab S') e = lbl).
    { rewrite LAB'. unfold upd_opt, opt_ext in *.
      destruct e'; desf. 
      { rewrite updo; [|omega].
          by rewrite upds. }
        by rewrite upds. }
    edestruct lbl_step_cases as [l [l' HH]]. 
    { eapply SRK; eauto. }
    { eapply STEP. }
    destruct HH as [AA BB].
    apply opt_to_list_app_singl in AA.
    destruct AA as [LA LB].
    subst l l'.
    erewrite steps_preserve_lab.    
    { erewrite basic_step_e2a_e.
      2-5 : eauto; apply SRCC.
      destruct BB as [BB | BB].
      { destruct BB as [_ [ACTS [LAB _]]]. 
        rewrite LAB. by rewrite upds. }
      destruct BB as [_ [ACTS [LAB HH]]].
      desf. rewrite LAB.
      unfold upd_opt.
      rewrite updo. 
      { rewrite upds. basic_solver. }
      red. intros HH. inversion HH. omega. }
    { by rewrite GTIDe. }
    { apply ilbl_steps_in_steps. 
      by rewrite GTIDe. }    
    erewrite basic_step_e2a_e.
    2-5 : eauto; apply SRCC.
    desf; apply ACTS; basic_solver.    
  Qed.

  Lemma basic_step_e2a_lab_e' TC' k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRK : simrel_cont prog S G TC)
        (CG : cert_graph G sc TC TC' (ES.cont_thread S k) st'')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e (Some e') S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
     Slab S' e' = lab (ProgToExecution.G st'') (e2a S' e').
  Proof. 
    cdes BSTEP_. simpl in BSTEP_.
    assert (Gtid (e2a S' e') = ES.cont_thread S k) as GTIDe.
    { rewrite <- e2a_tid. erewrite ESBasicStep.basic_step_tid_e'; eauto. }
    assert (wf_thread_state (ES.cont_thread S k) st') as WFTS. 
    { eapply wf_thread_state_steps.
      { eapply SRK; eauto. }
      eapply ilbl_steps_in_steps.
      do 2 econstructor. eapply STEP. }
    destruct lbl' as [lbl' | ].
    2 : { by unfold opt_same_ctor in LABEL'. }
    arewrite ((Slab S') e' = lbl').
    { rewrite LAB'. unfold upd_opt, opt_ext in *.
      by rewrite upds. }
    edestruct lbl_step_cases as [l [l' HH]]. 
    { eapply SRK; eauto. }
    { eapply STEP. }
    destruct HH as [AA BB].
    apply opt_to_list_app_singl in AA.
    destruct AA as [LA LB].
    subst l l'.
    destruct BB as [BB | BB]; [desf|].
    erewrite steps_preserve_lab.    
    { erewrite basic_step_e2a_e'.
        2-5 : eauto; apply SRCC.
        destruct BB as [_ [ACTS [LAB HH]]].
        desf. rewrite LAB.
        unfold upd_opt.
        by rewrite upds. }
    { by rewrite GTIDe. }
    { apply ilbl_steps_in_steps. 
      by rewrite GTIDe. }    
    erewrite basic_step_e2a_e'.
    2-5 : eauto; apply SRCC.
    desf; apply ACTS; basic_solver.    
  Qed.

  Lemma basic_step_e2a_certlab_e TC' k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRK : simrel_cont prog S G TC)
        (CG : cert_graph G sc TC TC' (ES.cont_thread S k) st'')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e e' S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
     Slab S' e = certLab G st'' (e2a S' e).
  Proof. 
    unfold certLab.
    destruct 
      (excluded_middle_informative (acts_set (ProgToExecution.G st'') (e2a S' e))) 
      as [GCE | nGCE].
    { eapply basic_step_e2a_lab_e; eauto. }
    exfalso. apply nGCE. 
    eapply dcertE; eauto.
    eapply basic_step_e2a_E0_e; eauto. 
  Qed.

  Lemma basic_step_e2a_certlab_e' TC' k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRK : simrel_cont prog S G TC)
        (CG : cert_graph G sc TC TC' (ES.cont_thread S k) st'')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e (Some e') S S')
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
     Slab S' e' = certLab G st'' (e2a S' e').
  Proof. 
    unfold certLab.
    destruct 
      (excluded_middle_informative (acts_set (ProgToExecution.G st'') (e2a S' e'))) 
      as [GCE | nGCE].
    { eapply basic_step_e2a_lab_e'; eauto. }
    exfalso. apply nGCE. 
    eapply dcertE; eauto.
    eapply basic_step_e2a_E0_e'; eauto. 
  Qed.

  Lemma basic_step_e2a_same_lab_u2v TC' k k' e e' S' 
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRK : simrel_cont prog S G TC)
        (SRE2A : simrel_e2a S G sc)
        (CG : cert_graph G sc TC TC' (ES.cont_thread S k) st'')
        (BSTEP_ : ESBasicStep.t_ (cont_lang S k) k k' st st' e e' S S') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') :
    same_lab_u2v_dom (SE S') (Slab S') (Glab ∘ (e2a S')).
  Proof. 
    cdes BSTEP_. simpl in BSTEP_.
    assert (ESBasicStep.t e e' S S') as BSTEP.
    { econstructor; eauto. }
    unfold same_lab_u2v_dom.
    intros x SEx.
    eapply ESBasicStep.basic_step_acts_set in SEx; eauto.
    destruct SEx as [[SEx | SEx] | SEx].
    { erewrite ESBasicStep.basic_step_lab_eq_dom; eauto. 
      unfold compose. 
        by erewrite basic_step_e2a_eq_dom; eauto; apply SRE2A. }
    { subst x.
      erewrite basic_step_e2a_lab_e; eauto.
      unfold compose. 
      eapply cuplab_cert; [|eapply dcertE]; eauto.
      eapply basic_step_e2a_E0_e; eauto. }
    destruct e' as [e' | ].
    2 : { exfalso. by unfold eq_opt in SEx. }
    unfold eq_opt in SEx. subst x.
    erewrite basic_step_e2a_lab_e'; eauto.
    unfold compose. 
    eapply cuplab_cert; [|eapply dcertE]; eauto.
    eapply basic_step_e2a_E0_e'; eauto.    
  Qed.

  Lemma simrel_a2e_set_equiv a2e a2eD a2eD' (EQ : a2eD ≡₁ a2eD') : 
    simrel_a2e S a2e a2eD <-> simrel_a2e S a2e a2eD'.
  Proof. 
    split; [symmetry in EQ|].
    all: intros HH; inv HH; constructor;
      [ eapply inj_dom_more; eauto 
      | erewrite set_collect_more; eauto
      | eapply fixset_more; eauto ].
  Qed.

  Lemma basic_step_simrel_a2e_preserved e e' S' a2e a2eD
        (SRA2E : simrel_a2e S a2e a2eD)
        (BSTEP : ESBasicStep.t e e' S S') : 
    simrel_a2e S' a2e a2eD.
  Proof. 
    constructor.
    { apply SRA2E. }
    { etransitivity.
      { apply SRA2E. }
      eapply ESBasicStep.basic_step_acts_set_mon; eauto. }
    eapply fixset_eq_dom.
    2 : apply SRA2E.
    unfolder. unfold compose. 
    ins. eapply basic_step_e2a_eq_dom; eauto.
    apply SRA2E. basic_solver.
  Qed.

End SimRelEventToActionLemmas.