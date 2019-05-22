Require Import Omega.
From hahn Require Import Hahn.
From imm Require Import Events Execution
     Traversal TraversalConfig SimTraversal SimTraversalProperties
     Prog ProgToExecution ProgToExecutionProperties Receptiveness
     imm_common imm_s imm_s_hb SimulationRel
     CertExecution2 CertExecutionMain
     SubExecution CombRelations AuxRel.
Require Import AuxRel.
Require Import AuxDef.
Require Import EventStructure.
Require Import Execution.
Require Import BasicStep.
Require Import Step.
Require Import StepWf.
Require Import Consistency.
Require Import LblStep.
Require Import CertRf.
Require Import CertGraph.
Require Import EventToAction.
Require Import ImmProperties.
Require Import SimRelCont.
Require Import SimRelEventToAction.
Require Import SimRel.
Require Import SimRelCert.
Require Import SimRelCertBasicStep.
Require Import SimRelCertStep.
Require Import SimRelCertStepCoh.
Require Import ProgES.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelStep.

  Variable prog : stable_prog_type.
  Variable G : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable TC' : trav_config.
  Variable X : eventid -> Prop.

  Notation "'SE' S" := S.(ES.acts_set) (at level 10).
  Notation "'SEinit' S" := S.(ES.acts_init_set) (at level 10).
  Notation "'SEninit' S" := S.(ES.acts_ninit_set) (at level 10).
  Notation "'Stid' S" := (S.(ES.tid)) (at level 10).
  Notation "'Slab' S" := S.(ES.lab) (at level 10).
  Notation "'Sloc' S" := (loc S.(ES.lab)) (at level 10).

  Notation "'Ssb' S" := S.(ES.sb) (at level 10).
  Notation "'Srmw' S" := S.(ES.rmw) (at level 10).
  Notation "'Sew' S" := S.(ES.ew) (at level 10).
  Notation "'Sjf' S" := S.(ES.jf) (at level 10).
  Notation "'Srf' S" := S.(ES.rf) (at level 10).
  Notation "'Sco' S" := S.(ES.co) (at level 10).
  Notation "'Scf' S" := S.(ES.cf) (at level 10).

  Notation "'Sjfe' S" := S.(ES.jfe) (at level 10).
  Notation "'Srfe' S" := S.(ES.rfe) (at level 10).
  Notation "'Scoe' S" := S.(ES.coe) (at level 10).
  Notation "'Sjfi' S" := S.(ES.jfi) (at level 10).
  Notation "'Srfi' S" := S.(ES.rfi) (at level 10).
  Notation "'Scoi' S" := S.(ES.coi) (at level 10).

  Notation "'Scc' S" := S.(cc) (at level 10).
  Notation "'Ssw' S" := S.(sw) (at level 10).
  Notation "'Shb' S" := S.(hb) (at level 10).
  Notation "'Secf' S" := (S.(Consistency.ecf)) (at level 10).
  Notation "'Seco' S" := (Consistency.eco S Weakestmo) (at level 10).

  Notation "'SR' S" := (fun a => is_true (is_r S.(ES.lab) a)) (at level 10).
  Notation "'SW' S" := (fun a => is_true (is_w S.(ES.lab) a)) (at level 10).
  Notation "'SF' S" := (fun a => is_true (is_f S.(ES.lab) a)) (at level 10).

  Notation "'SPln' S" := (fun a => is_true (is_only_pln S.(ES.lab) a)) (at level 10).
  Notation "'SRlx' S" := (fun a => is_true (is_rlx S.(ES.lab) a)) (at level 10).
  Notation "'SRel' S" := (fun a => is_true (is_rel S.(ES.lab) a)) (at level 10).
  Notation "'SAcq' S" := (fun a => is_true (is_acq S.(ES.lab) a)) (at level 10).
  Notation "'SAcqrel' S" := (fun a => is_true (is_acqrel S.(ES.lab) a)) (at level 10).
  Notation "'SSc' S" := (fun a => is_true (is_sc S.(ES.lab) a)) (at level 10).

  Notation "'K' S" := (S.(ES.cont_set)) (at level 10).

  Notation "'Stid_' S" := (fun t x => Stid S x = t) (at level 1).
  Notation "'SNTid_' S" := (fun t x => Stid S x <> t) (at level 1).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).

  Notation "'Glab'" := (Execution.lab G).
  Notation "'Gloc'" := (Events.loc (lab G)).
  Notation "'Gtid'" := (Events.tid).

  Notation "'GTid' t" := (fun x => Gtid x = t) (at level 1).
  Notation "'GNTid' t" := (fun x => Gtid x <> t) (at level 1).

  Notation "'GR'" := (fun a => is_true (is_r Glab a)).
  Notation "'GW'" := (fun a => is_true (is_w Glab a)).
  Notation "'GF'" := (fun a => is_true (is_f Glab a)).

  Notation "'GRel'" := (fun a => is_true (is_rel Glab a)).
  Notation "'GAcq'" := (fun a => is_true (is_acq Glab a)).

  Notation "'Gsb'" := (Execution.sb G).
  Notation "'Grmw'" := (Execution.rmw G).
  Notation "'Grf'" := (Execution.rf G).
  Notation "'Gco'" := (Execution.co G).

  Notation "'Grs'" := (imm_s_hb.rs G).
  Notation "'Grelease'" := (imm_s_hb.release G).
  Notation "'Gsw'" := (imm_s_hb.sw G).
  Notation "'Ghb'" := (imm_s_hb.hb G).

  Notation "'Gfurr'" := (furr G sc).
  Notation "'Gvf' t" := (vf G sc TC' t) (at level 10, only parsing).

  Notation "'Geco'" := (Execution_eco.eco G).

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).
  Notation "'C''"  := (covered TC').
  Notation "'I''"  := (issued TC').

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

  Notation "'kE' S" := (fun k => ES.cont_sb_dom S k) (at level 1, only parsing).
  Notation "'ktid' S" := (fun k => ES.cont_thread S k) (at level 1, only parsing).

  Notation "'certX' S" := (fun k => (X ∩₁ SNTid_ S (ktid S k)) ∪₁ (kE S k)) (at level 1, only parsing).
  
  Lemma simrel_cert_graph_start thread S 
        (NINITT : thread <> tid_init)
        (SRC : simrel prog S G sc TC X) 
        (TC_STEP : isim_trav_step G sc thread TC TC') : 
    exists k st st',
      ⟪ kTID : thread = ktid S k ⟫ /\
      ⟪ XkTIDCOV : kE S k ≡₁ X ∩₁ Stid_ S (ktid S k) ∩₁ e2a S ⋄₁ C ⟫ /\
      ⟪ CERTG : cert_graph G sc TC TC' thread st' ⟫ /\
      ⟪ CERT_ST : simrel_cstate S k st st' ⟫.
  Proof.
    cdes SRC.
    assert (ES.Wf S) as WFS by apply SRC.
    assert (Wf G) as WF by apply SRC.

    pose proof TC_STEP as HH. 
    eapply trstep_thread_prog in HH; try apply SRC.
    apply Basic.IdentMap.Facts.in_find_iff in HH.
    destruct (Basic.IdentMap.find thread (stable_prog_to_prog prog))
      as [lprog|] eqn:AA; desf.
    
    (* TODO: make it a separate lemma. *)
    assert
      (exists k (state : Language.state (thread_lts thread)),
          ⟪ INK : K S (k, thread_cont_st thread state) ⟫ /\
          ⟪ THK : thread = ES.cont_thread S k ⟫ /\
          ⟪ EST : state.(ProgToExecution.G).(acts_set) ≡₁
                  C ∩₁ GTid thread ⟫ /\
          ((exists thread,
               << KREP : k = CInit thread >> /\
               << CEMP : C ∩₁ GTid thread ≡₁ ∅ >>) \/
           (exists e,
               << KREP : k = CEvent e >> /\
               << EPC  : pc G TC thread (e2a S e) >>))
      ).
    { destruct (classic (exists x, (C ∩₁ GTid thread) x)) as [[x [CX TX]]|NN].
      2: { exists (CInit thread).
           edestruct contrun as [st]; try apply SRC; eauto. 
           desf.
           eexists. splits; eauto.
           2: { left. eexists. splits; eauto.
                generalize NN. basic_solver. }
           etransitivity.
           { eapply steps_empty_same_E; eauto. }
           arewrite (C ∩₁ GTid thread ≡₁ ∅).
           { generalize NN. basic_solver. }
           simpls. }
      edestruct exists_pc as [xpc XPC]; eauto; try apply SRC.
      assert ((e2a S □₁ X) xpc) as EE.
      { eapply ex_cov_iss; eauto. left. apply XPC. }
      red in EE. desf.
      assert (Gtid x = Stid S y) as TT.
      { rewrite e2a_tid. red in XPC. generalize XPC. basic_solver. }
      rewrite TT in XPC.
      edestruct ES.event_K with (e:=y) as [c INKC]; try apply SRC.
      { split.
        { eapply Execution.ex_inE; eauto. apply SRC. }
        intros [CC BB].
        rewrite <- TT in BB. desf. }
      { intros [z RMW].
        apply XPC. exists (e2a S z).
        assert (Grmw (e2a S y) (e2a S z)) as GRMW.
        { eapply e2a_rmw; try apply SRC.
          red. eauto. }
        apply seq_eqv_r. split.
        { apply rmw_in_sb; auto. }
        eapply (rmwclos _ _ _ GRMW).
          by apply XPC. }
      destruct c as [lang state].
      set (BB := INKC).
      eapply contlang in BB; try apply SRC.
      desf.
      exists (CEvent y). exists state.
      splits; eauto.
      { arewrite (Gtid x = ES.cont_thread S (CEvent y)). eauto. }
      2: { right. eexists. split; eauto. by rewrite TT. }
      (* TODO: generalize to a lemma *)
      set (WFTS:=INKC).
      eapply contwf in WFTS; try apply SRC.
      simpls. rewrite <- TT in WFTS.
      set (SS:=INKC).
      eapply contpc in SS; try apply SRC; auto.
      split.
      { intros e CC.
        set (DD:=CC).
        eapply acts_rep in DD; eauto. desf.
        split; auto.
        cdes SS. rewrite TT. by apply PCOV. }
      intros e [CC ET].
      destruct e; simpls; desf.
      { by rewrite ET in NINITT. }
      cdes SS. rewrite TT in CC. apply PCOV in CC.
      apply acts_clos; auto. }

    desc.
    assert (lprog = instrs state) as UU.
    { rewrite THK in *. eapply kstate_instrs; eauto; try apply SRC. }

    edestruct cert_graph_start with (state0:=state) as [state']; eauto.
    1,2,3,4: by apply SRC.
    { rewrite THK. eapply contwf; try apply SRC. desf. }
    { rewrite <- UU. 
      unfold stable_prog_to_prog in *.
      rewrite Basic.IdentMap.Facts.map_o in AA.
      unfold option_map in *. clear UU. desf.
      destruct s. simpls. }
    { rewrite <- UU.
      rewrite THK in *.
      eapply contreach; eauto. apply SRC. }
    { desf.
      2: { eapply contpc; eauto. apply SRC. }
      eapply continitstate; simpls; eauto; try apply SRC.
      simpls. apply CEMP. }
    { rewrite EST. basic_solver. }
    all: try by apply SRC.
    desc.
    do 3 eexists.
    splits; eauto.
    2: { constructor; eauto.
         { red. eexists. splits; eauto.
           rewrite <- THK. eauto. }
         rewrite <- THK.
         apply steps_stable_lbl_steps.
         apply seq_eqv_l. split.
         { eapply contstable; try apply SRC; eauto.
           rewrite <- THK. eauto. }
         apply seq_eqv_r. by split. }
    desf; simpls.
    { (* TODO: it's wrong! *) admit. }
    (* TODO: it's wrong! *)
    admit.
  Admitted.
  
  Lemma simrel_cert_start k S 
        (st st' : thread_st (ktid S k))
        (SRC : simrel prog S G sc TC X) 
        (TC_ISTEP : isim_trav_step G sc (ktid S k) TC TC') 
        (XkTIDCOV : kE S k ≡₁ X ∩₁ Stid_ S (ktid S k) ∩₁ e2a S ⋄₁ C)
        (CERTG : cert_graph G sc TC TC' (ktid S k) st')
        (CERT_ST : simrel_cstate S k st st') :
    simrel_cert prog S G sc TC TC' X k st st'.
  Proof. 
    assert (tc_coherent G sc TC') as TCCOH'.
    { eapply sim_trav_step_coherence; try apply SRC.
      red. eauto. }
    constructor; auto.
    (* ex_ktid_cov : X ∩₁ STid ktid ∩₁ e2a ⋄₁ C ⊆₁ kE *)
    { apply XkTIDCOV. }
    (* cov_in_ex : e2a ⋄₁ C ∩₁ kE ⊆₁ X *)
    { rewrite XkTIDCOV. basic_solver. }
    (* kE_lab : eq_dom (kE \₁ SEinit) Slab (certG.(lab) ∘ e2a) *)
    { intros x [kEx nINITx].
      erewrite ex_cov_iss_lab; try apply SRC.
      2 : { apply XkTIDCOV in kEx. 
            generalize kEx. basic_solver. }
      unfold Basics.compose. 
      erewrite <- cslab; eauto.
      { unfold certLab.
        erewrite restr_fun_fst; auto.
        edestruct cstate_cont as [sta HH]; 
          eauto; desf.
        eapply steps_preserve_E; eauto.
        { eapply contwf; eauto. apply SRC. }
        { apply ilbl_steps_in_steps, CERT_ST. }
        eapply e2a_kE_ninit; auto; try apply SRC.
        basic_solver. }
      red. do 4 left.
      simpl in XkTIDCOV.
      apply XkTIDCOV in kEx.
      destruct kEx as [[_ _] Cx].
      eapply sim_trav_step_covered_le in Cx.
      2 : eexists; eauto.
      basic_solver. }
    (* jf_in_cert_rf : e2a □ (Sjf ⨾ ⦗kE⦘) ⊆ cert_rf G sc TC' ktid *)
    { rewrite XkTIDCOV.
      rewrite <- seq_eqvK.
      rewrite <- seqA, collect_rel_seqi.
      arewrite (X ∩₁ Tid_ S (ES.cont_thread S k) ∩₁ e2a S ⋄₁ C ⊆₁
                X ∩₁ e2a S ⋄₁ C) at 1 by basic_solver.
      rewrite jf_cov_in_rf; [|by apply SRC].
      rewrite collect_rel_eqv.
      rewrite set_collect_inter.
      2: { (* TODO: remove an extra argument of set_collect_inter in Hahn *) 
        ins. repeat constructor. }
      rewrite collect_map_in_set. 
      arewrite (X ∩₁ Tid_ S (ES.cont_thread S k) ⊆₁
                Tid_ S (ES.cont_thread S k)) by basic_solver.
      rewrite e2a_Tid.
      arewrite (C ⊆₁ C').
      { eapply sim_trav_step_covered_le.
        red. eauto. }
      by apply rf_C_in_cert_rf; try apply SRC. }
    (* ex_cont_iss : X ∩₁ e2a ⋄₁ (contE ∩₁ I) ⊆₁ dom_rel (Sew ⨾ ⦗ kE ⦘) ; *)
    arewrite (X ∩₁ e2a S ⋄₁ (acts_set (ProgToExecution.G st) ∩₁ I) ⊆₁ 
              X ∩₁ SW S ∩₁ Stid_ S (ktid S k) ∩₁ e2a S ⋄₁ C).
    { edestruct cstate_cont as [sta HH]; 
        eauto; desf.
      rewrite <- e2a_kE_ninit; try apply SRC; eauto.
      rewrite XkTIDCOV.
      unfolder. ins. desf. splits; auto; try congruence.
      { eapply ex_iss_inW; [apply SRC|]. basic_solver. }
      arewrite (Stid S x = Stid S y); auto.
      rewrite !e2a_tid. congruence. }
    rewrite XkTIDCOV.
    rewrite seq_eqv_r.
    unfolder. ins. desf. 
    exists x; splits; auto.
    apply ES.ew_refl; [apply SRC|].
    unfolder; splits; auto.
    eapply Execution.ex_inE; eauto.
    apply SRC.
  Qed.

  Lemma ew_ex_iss_in_cert_ex_iss k S 
        (st : thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st) :  
    dom_rel (Sew S ⨾ ⦗X ∩₁ e2a S ⋄₁ I⦘) ⊆₁ 
    dom_rel (Sew S ⨾ ⦗certX S k ∩₁ e2a S ⋄₁ I⦘).
  Proof. 
    assert (ES.Wf S) as WFS by apply SRCC.      
    assert (Execution.t S X) as EXEC by apply SRCC.
    rewrite !seq_eqv_r. 
    intros x [y [EW [Xy Iy]]].
    assert (Stid S x = Stid S y) as STID.
    { apply ES.ew_tid; auto. }
    edestruct ex_iss_cert_ex
      as [z HH]; eauto.
    { unfolder; splits; eauto.
      eapply ex_in_certD; eauto.
      basic_solver. }
    apply seq_eqv_r in HH. 
    destruct HH as [EW' [CERTXz Iz]].
    eexists.
    unfold set_inter. splits.
    2,3: eauto.
    eapply ES.ew_trans; eauto. 
  Qed.

  Lemma cert_ex_rf_compl k S 
        (st : thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st) : 
    certX S k ∩₁ SR S ⊆₁ codom_rel (⦗certX S k⦘ ⨾ Srf S).
  Proof. 
    assert (ES.Wf S) as WFS by apply SRCC.      
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (es_consistent S) as CONS by apply SRCC.
    assert (simrel_ prog S G sc TC X) as SR_ by apply SRCC.
    edestruct cstate_cont as [st_ [stEQ KK]]; 
      [apply SRCC|].
    red in stEQ, KK. subst st_.
    rewrite set_inter_union_l.
    rewrite set_subset_union_l. split.
    2 : eapply kE_rf_compl; eauto.
    intros x [[Xx nTIDx] Rx].
    edestruct Execution.ex_rf_compl
      as [y HH]; eauto.
    { basic_solver. }
    apply seq_eqv_l in HH.
    destruct HH as [Xy RF].
    eapply ES.set_split_Tid 
      with (S := S) (t := ktid S k) in Xy.
    destruct Xy as [[Xy TIDy] | [Xy nTIDy]].
    2 : basic_solver 10.
    assert (SEninit S y) as nINITy.
    { red. split.
      { eapply Execution.ex_inE; eauto. }
      intros [_ INITy].
      eapply ktid_ninit; eauto.
      congruence. }
    assert (Srfe S y x) as RFE.
    { unfold ES.rfe. split; auto.
      intros SB.
      apply nTIDx.
      rewrite <- TIDy.
      symmetry.
      eapply ES.sb_tid; auto.
      basic_solver. }
    edestruct rfe_ex_iss
      as [z HH]; eauto.
    { eexists; eauto. }
    edestruct ew_ex_iss_in_cert_ex_iss
      as [z' HH']; eauto.
    { basic_solver. }
    apply seq_eqv_r in HH'.
    destruct HH' as [EW [CERTXz' Iz']].
    exists z'.
    apply seq_eqv_l.
    split; auto.
    apply ES.rfe_in_rf.
    eapply ew_rfe_in_rfe; eauto.
    eexists; splits; eauto.
    apply ES.ew_sym; auto. 
  Qed.

  Lemma simrel_cert_vis k S
        (st : thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st) :
    certX S k ⊆₁ vis S.
  Proof. 
    assert (ES.Wf S) as WFS by apply SRCC.      
    assert (Execution.t S X) as EXEC by apply SRCC.
    assert (es_consistent S) as CONS by apply SRCC.
    assert (simrel_ prog S G sc TC X) as SR_ by apply SRCC.
    edestruct cstate_cont as [st_ [stEQ KK]]; 
      [apply SRCC|].
    red in stEQ, KK. subst st_.
    simpl.
    intros x [[Xx nTIDx] | kSBx].
    { eapply ex_cov_ntid_vis; eauto. basic_solver. }
    red. splits. 
    { eapply kE_inE; eauto. }
    rewrite seq_eqv_r.
    intros y z [CC EQz]. subst z.
    assert 
      ((dom_rel (Sew S ⨾ ⦗certX S k ∩₁ e2a S ⋄₁ I⦘)) y)
      as EWCERTX.
    { eapply ew_ex_iss_in_cert_ex_iss; eauto.
      eapply jfe_ex_iss; eauto.
      apply dom_cc_jfe.
      basic_solver. }
    destruct EWCERTX as [z HH].
    apply seq_eqv_r in HH.
    destruct HH as [EW CERTXz].
    eexists; splits; eauto.
    destruct CERTXz as [[[Xz nTIDz] | kSBz] Iz].
    { eapply ES.cont_sb_tid in kSBx; eauto.
      destruct kSBx as [INITx | TIDx].
      { exfalso. 
        apply cc_ninit in CC.
        destruct CC as [_ nINITx].
        by apply nINITx. }
      exfalso. apply nTIDz.
      etransitivity.
      { symmetry; apply ES.ew_tid; eauto. }
      etransitivity. 
      { apply cc_tid; eauto. }
      done. } 
    edestruct ES.cont_sb_dom_cross
      as [[INITz INITx] | HH]; eauto.
    { basic_solver. }
    exfalso. 
    apply cc_ninit in CC.
    destruct CC as [_ nINITx].
    by apply nINITx.
  Qed.

  Lemma simrel_cert_end k S 
        (st : thread_st (ktid S k))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st) :
    simrel prog S G sc TC' (certX S k).
  Proof. 
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (Execution.t S X) as EXEC.
    { apply SRCC. }
    assert (simrel_ prog S G sc TC X) as SR_.
    { apply SRCC. }
    edestruct cstate_cont as [stx [EQ KK]]; 
      [apply SRCC|].
    red in EQ, KK. subst stx.
    constructor; [|apply SRCC].
    constructor; try apply SRCC.
    { eapply tccoh'; eauto. }
    { constructor.
      { apply SRCC. }
      { eapply sim_trav_step_rmw_covered;
          try apply SRCC.
        eexists. apply SRCC. }
      eapply sim_trav_step_rel_covered;
        try apply SRCC.
      eexists. apply SRCC. }
    (* sr_exec : Execution.t S certX *)
    { constructor.
      { eapply cert_ex_inE; eauto. }
      { eapply init_in_cert_ex; eauto. }
      { eapply cert_ex_sb_prcl; eauto. }
      { eapply cert_ex_sw_prcl; eauto. }
      { admit. }
      { eapply cert_ex_rf_compl; eauto. }
      { eapply cert_ex_ncf; eauto. }
      eapply simrel_cert_vis; eauto. }
    (* sr_cont : simrel_cont (stable_prog_to_prog prog) S G TC' *)
    { econstructor; try apply SRCC.
      all: admit. }
    (* ex_cov_iss : e2a □₁ certX ≡₁ C' ∪₁ dom_rel (Gsb^? ⨾ ⦗ I' ⦘) *)
    { rewrite cert_ex_certD; eauto. 
      rewrite cert_dom_cov_sb_iss; eauto. }
    (* ex_cov_iss_lab : eq_dom (certX ∩₁ e2a ⋄₁ (C' ∪₁ I')) Slab (Glab ∘ e2a) *)
    { eapply cert_ex_cov_iss_lab; apply SRCC. }
    (* rmw_cov_in_ex : Grmw ⨾ ⦗ C' ⦘ ⊆ e2a □ Srmw ⨾ ⦗ certX ⦘ *)
    { admit. }
    (* jf_cov_in_rf : e2a □ (Sjf ⨾ ⦗certX ∩₁ e2a ⋄₁ C'⦘) ⊆ Grf *)
    { rewrite set_inter_union_l, id_union. relsf.
      apply inclusion_union_l. 
      { rewrite isim_trav_step_new_covered_tid; try apply SRCC.
        rewrite seq_eqv_r.
        unfolder. ins. desf.
        { eapply jf_cov_in_rf; eauto. basic_solver 10. }
        exfalso. rewrite e2a_tid in *. auto. }
      arewrite (kE S k ∩₁ e2a S ⋄₁ C' ⊆₁ 
                   SEinit S ∪₁ kE S k ∩₁ e2a S ⋄₁ (GTid (ktid S k) ∩₁ C')).
      { unfolder. 
        intros x [kSBx Cx].
        set (HH := kSBx).
        eapply ES.cont_sb_tid in HH; eauto.
        edestruct HH as [INITx | TIDx].
        { by left. }
        right; splits; auto.
        by rewrite <- e2a_tid. }
      rewrite id_union. relsf.
      apply inclusion_union_l. 
      { rewrite ES.jf_nEinit; auto.
        basic_solver. }
      rewrite id_inter, <- seqA.
      rewrite collect_rel_seqi.
      rewrite jf_in_cert_rf; eauto.
      rewrite collect_rel_eqv. 
      rewrite collect_map_in_set.
      arewrite (C' ⊆₁ D G TC' (ktid S k)).
      { unfold D. basic_solver 10. }
      erewrite cert_rf_D_rf; try done. 
      1,2: apply SRCC.
      eapply tccoh'; eauto. }
    (* jfe_ex_iss : dom_rel Sjfe ⊆₁ dom_rel (Sew ⨾ ⦗ certX ∩₁ e2a ⋄₁ I ⦘) *)
    { etransitivity.
      { eapply jfe_ex_iss; eauto. }
      rewrite ew_ex_iss_in_cert_ex_iss; eauto.
      erewrite sim_trav_step_issued_le; eauto. 
      eexists; apply SRCC. }
    (* ew_ex_iss : dom_rel (Sew \ eq) ⊆₁ dom_rel (Sew ⨾ ⦗ certX ∩₁ e2a ⋄₁ I ⦘) *)
    { etransitivity.
      { eapply ew_ex_iss; eauto. }
      rewrite ew_ex_iss_in_cert_ex_iss; eauto.
      erewrite sim_trav_step_issued_le; eauto. 
      eexists; apply SRCC. }
    (* rel_ew_ex_iss : dom_rel (Srelease ⨾ Sew ⨾ ⦗ certX ∩₁ e2a ⋄₁ I  ⦘) ⊆₁ certX *)
    intros x HH.
    eapply rel_ew_cert_ex; eauto.
    generalize HH. basic_solver 10.
  Admitted.

  Lemma simrel_step_helper k S
        (st st''' : thread_st (ktid S k))
        (SRC : simrel prog S G sc TC X)
        (TC_ISTEP : isim_trav_step G sc (ktid S k) TC TC')
        (XkTIDCOV : kE S k ≡₁ X ∩₁ Stid_ S (ktid S k) ∩₁ e2a S ⋄₁ C)
        (CERTG : cert_graph G sc TC TC' (ktid S k) st''')
        (CERT_ST : simrel_cstate S k st st''') 
        (LBL_STEPS : (lbl_step (ktid S k))＊ st st''') :
    (fun st' => exists k' S',
      ⟪ kTID : ktid S' k' = ktid S k ⟫ /\
      ⟪ STEPS : (step Weakestmo)＊ S S' ⟫ /\
      ⟪ SRCC  : simrel_cert prog S' G sc TC TC' X k' st' st''' ⟫) st'''.
  Proof.
    eapply clos_refl_trans_ind_step_left.
    { exists k, S. splits; auto.
      { apply rt_refl. }
      eapply simrel_cert_start; eauto. }
    { eapply LBL_STEPS. }
    intros st' st'' HH. desc.
    intros LBL_STEP LBL_STEPS'.
    edestruct simrel_cert_lbl_step
      as [k'' [S'' HH]]; 
      eauto; desc.
    { rewrite kTID. apply LBL_STEP. }
    { rewrite kTID. apply LBL_STEPS'. }
    exists k'', S''. splits; auto.
    { congruence. }
    eapply rt_trans; eauto.
    destruct ESSTEP as [EQ | ESSTEP].
    { subst. by apply rt_refl. }
    by apply rt_step.
  Qed.
  
  Lemma simrel_step S 
        (SRC : simrel prog S G sc TC X) 
        (TRAV_STEP : sim_trav_step G sc TC TC') :
    exists X' S', 
      ⟪ STEPS : (step Weakestmo)＊ S S' ⟫ /\      
      ⟪ SRC' : simrel prog S' G sc TC' X' ⟫.
  Proof. 
    unfold sim_trav_step in TRAV_STEP. desc.
    edestruct simrel_cert_graph_start
      as [k [st [st' HH]]]; 
      eauto; desc. 
    { eapply isim_trav_step_thread_ninit; eauto.
      all: try apply SRC.
      apply stable_prog_to_prog_no_init.
      apply SRC. }
    edestruct simrel_step_helper
      as [k' [S' HH]]; 
      subst; eauto; desc.
    { by destruct CERT_ST. }
    exists (certX S' k'), S'.
    splits; auto.
    eapply simrel_cert_end; eauto.
  Qed.
  
End SimRelStep.