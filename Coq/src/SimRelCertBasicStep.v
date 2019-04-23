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
Require Import BasicStep.
Require Import Consistency.
Require Import Execution.
Require Import LblStep.
Require Import CertRf.
Require Import CertGraph.
Require Import EventToAction.
Require Import ImmProperties.
Require Import SimRelCont.
Require Import SimRelEventToAction.
Require Import SimRel.
Require Import SimRelCert.
Require Import ProgES.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelCertBasicStep.

  Variable prog : Prog.t.
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
  Notation "'Secf'" := (S.(Consistency.ecf)).

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

  Notation "'STid_' S" := (fun t x => Stid S x = t) (at level 1).
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

  (* Definition upd_a2e a2e e e' S' :=  *)
  (*   upd_opt (upd a2e (e2a S' e) e) (option_map (e2a S') e') e'. *)

  (* Lemma basic_step_simrel_updh_cert_dom_eq_dom k k' e e' S S'  *)
  (*       (st st' st'': thread_st (ES.cont_thread S k)) *)
  (*       (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') *)
  (*       (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S') :  *)
  (*   eq_dom (cert_dom G TC (ES.cont_thread S k) st) (upd_a2e h e e' S') h. *)
  (* Proof.  *)
  (*   red. ins. unfold upd_a2e. *)
  (*   rewrite updo_opt; auto. *)
  (*   { rewrite updo; auto.  *)
  (*     red. ins. subst.  *)
  (*     eapply basic_step_cert_dom_ne; *)
  (*       try apply SRCC; eauto. } *)
  (*   { unfold eq_opt, option_map.  *)
  (*     destruct e'; try done. *)
  (*     red; ins; subst. *)
  (*     eapply basic_step_cert_dom_ne'; *)
  (*       try apply SRCC; eauto. } *)
  (*   apply option_map_same_ctor. *)
  (* Qed. *)

  (* Lemma basic_step_simrel_updh_e k k' e e' S S'  *)
  (*       (st st' st'': thread_st (ES.cont_thread S k)) *)
  (*       (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') *)
  (*       (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S') :  *)
  (*   (upd_a2e h e e' S') (e2a S' e) = e. *)
  (* Proof.  *)
  (*   unfold upd_a2e.  *)
  (*   rewrite updo_opt. *)
  (*   { by rewrite upds. } *)
  (*   { unfold eq_opt. *)
  (*     destruct e' as [e'|]; simpl; red; ins. *)
  (*     erewrite basic_step_e2a_e with (e := e) in H; eauto. *)
  (*     2-5 : apply SRCC. *)
  (*     erewrite basic_step_e2a_e' in H; eauto. *)
  (*     2-5 : apply SRCC. *)
  (*     inv H. omega. } *)
  (*   apply option_map_same_ctor. *)
  (* Qed. *)

  (* Lemma basic_step_simrel_updh_e' k k' e e' S S'  *)
  (*       (st st' st'': thread_st (ES.cont_thread S k)) *)
  (*       (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') *)
  (*       (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S') :  *)
  (*   option_map (upd_a2e h e e' S') (option_map (e2a S') e') = e'. *)
  (* Proof. *)
  (*   destruct e' as [e'|]; auto. *)
  (*   unfold upd_a2e, option_map, upd_opt. *)
  (*   by rewrite upds. *)
  (* Qed. *)

  Lemma simrel_cert_basic_step_cert_ex k k' e e' S S' 
        (st st' st'': thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S') : 
    certX S' k' ≡₁ certX S k ∪₁ eq e ∪₁ eq_opt e'.  
  Proof. 
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    assert (basic_step e e' S S') as BSTEP.
    { econstructor. eauto. }
    simpl. do 2 rewrite set_unionA.
    apply set_union_Propere.
    { (* TODO : separate lemma *)
      split. 
      { intros x [Xx NTIDx]. 
        split; auto.
        intros TIDx. apply NTIDx.
        erewrite basic_step_tid_eq_dom; eauto.
        2 : { eapply Execution.ex_inE; eauto. apply SRCC. }
        rewrite TIDx. symmetry.
        eapply basic_step_cont_thread_k; eauto. }
      intros x [Xx NTIDx]. 
      split; auto.
      intros TIDx. apply NTIDx.
      erewrite <- basic_step_tid_eq_dom; eauto.
      2 : { eapply Execution.ex_inE; eauto. apply SRCC. }
      rewrite TIDx. 
      eapply basic_step_cont_thread_k; eauto. }
    rewrite <- set_unionA.
    eapply basic_step_cont_sb_dom; eauto.
  Qed.
    
  (* Lemma basic_step_simrel_a2e k k' e e' S S'  *)
  (*       (st st' st'': thread_st (ES.cont_thread S k)) *)
  (*       (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') *)
  (*       (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S') :  *)
  (*   simrel_a2e S' (upd_a2e h e e' S') (cert_dom G TC (ES.cont_thread S' k') st').  *)
  (* Proof.  *)
  (*   cdes BSTEP_.  *)
  (*   assert (ES.Wf S) as WFS. *)
  (*   { apply SRCC. } *)
  (*   assert (basic_step e e' S S') as BSTEP. *)
  (*   { econstructor. eauto. } *)
  (*   assert (h □₁ cert_dom G TC (ES.cont_thread S k) st ⊆₁ SE S)  *)
  (*     as hCertE. *)
  (*   { eapply a2e_img. apply SRCC. } *)

  (*   constructor. *)
    
  (*   (* a2e_inj *) *)
  (*   { eapply inj_dom_more. *)
  (*     { eapply basic_step_cert_dom; eauto; apply SRCC. } *)
  (*     all : eauto. *)
  (*     rewrite set_unionA. *)
  (*     eapply inj_dom_union.  *)
  (*     { red. ins.  *)
  (*       erewrite !basic_step_simrel_updh_cert_dom_eq_dom  *)
  (*         in EQ; eauto. *)
  (*       eapply a2e_inj; eauto. apply SRCC. } *)
  (*     { apply inj_dom_union.  *)
  (*       { apply inj_dom_eq. } *)
  (*       { apply inj_dom_eq_opt. } *)
  (*       rewrite set_collect_eq, set_collect_eq_opt. *)
  (*       erewrite basic_step_simrel_updh_e; eauto. *)
  (*       erewrite basic_step_simrel_updh_e'; eauto. *)
  (*       step_solver. } *)
  (*     erewrite set_collect_eq_dom. *)
  (*     2 : eapply basic_step_simrel_updh_cert_dom_eq_dom; eauto. *)
  (*     rewrite set_collect_union. *)
  (*     rewrite set_collect_eq, set_collect_eq_opt. *)
  (*     erewrite basic_step_simrel_updh_e; eauto. *)
  (*     erewrite basic_step_simrel_updh_e'; eauto. *)
  (*     red. ins. destruct IN' as [IN' | IN']. *)
  (*     { eapply basic_step_acts_set_ne; eauto. *)
  (*       subst. eapply a2e_img; eauto. apply SRCC. } *)
  (*     unfold eq_opt, option_map, upd_opt in IN'. *)
  (*     destruct e' as [e'|]; auto.  *)
  (*     eapply basic_step_acts_set_ne'; eauto. *)
  (*     subst. eapply a2e_img; eauto. apply SRCC. } *)
        
  (*   (* a2e_img *) *)
  (*   { erewrite basic_step_simrel_updh_cert_dom; eauto. *)
  (*     rewrite a2e_img; try apply SRCC. *)
  (*     erewrite basic_step_acts_set *)
  (*       with (S' := S'); eauto. } *)

  (*   (* a2e_fix *) *)
  (*   { eapply fixset_more. *)
  (*     { eapply basic_step_cert_dom; eauto; apply SRCC. } *)
  (*     all : eauto. *)
  (*     rewrite !fixset_union. splits.  *)
  (*     { eapply fixset_eq_dom. *)
  (*       { unfold eq_dom, compose.  *)
  (*         intros x DOM. *)
  (*         erewrite basic_step_simrel_updh_cert_dom_eq_dom; eauto. *)
  (*         erewrite basic_step_e2a_eq_dom; eauto. *)
  (*         { by fold (compose (e2a S) h x). } *)
  (*         apply SRCC.(sr_a2e_h). *)
  (*         basic_solver. } *)
  (*       apply SRCC. } *)
  (*     { unfold eq_dom, compose.  *)
  (*       intros x DOM. subst x.  *)
  (*       erewrite basic_step_simrel_updh_e; eauto. } *)
  (*     unfold upd_a2e, eq_opt, option_map, upd_opt.  *)
  (*     red. ins. destruct e'; [|by exfalso]. *)
  (*     unfold compose. subst x. by rewrite upds. } *)

  (*   (* a2e_sb_prcl : dom_rel (Ssb ⨾ ⦗ a2e □₁ a2eD ⦘) ⊆₁ a2e □₁ a2eD *) *)
  (*   { erewrite basic_step_simrel_updh_cert_dom; eauto. *)
  (*     rewrite !id_union, !seq_union_r, !dom_union. *)
  (*     unionL. splits. *)
  (*     { rewrite <- seq_eqvK. *)
  (*       rewrite hCertE at 1. *)
  (*       seq_rewrite basic_step_sbE;  *)
  (*         eauto; try apply SRCC. *)
  (*       etransitivity; [apply SRCC|]. *)
  (*       basic_solver 5. } *)
  (*     { rewrite basic_step_sbe; eauto. *)
  (*       rewrite dom_cross; [|red; basic_solver]. *)
  (*       rewrite cont_sb_dom_in_hhdom; eauto. *)
  (*       basic_solver 5. } *)
  (*     rewrite basic_step_sbe'; eauto. *)
  (*     destruct e' as [e'|]; [|basic_solver]. *)
  (*     rewrite dom_cross; [|red; basic_solver].  *)
  (*     rewrite cont_sb_dom_in_hhdom; eauto. *)
  (*     basic_solver 5. } *)
    
  (*   (* a2e_ncf : ES.cf_free S (a2e □₁ a2eD) *) *)
  (*   red.  *)
  (*   erewrite basic_step_simrel_updh_cert_dom; eauto. *)
  (*   erewrite basic_step_cf;  *)
  (*     eauto; try apply SRCC. *)
  (*   unfold cf_delta. *)
  (*   rewrite !csE, !transp_cross, !id_union.  *)
  (*   relsf. unionL. *)
  (*   { apply SRCC. } *)
  (*   all : try by ( *)
  (*     try rewrite hCertE; *)
  (*     step_solver *)
  (*   ). *)
  (*   all : rewrite !seq_eqv_cross_r, !seq_eqv_cross_l. *)
  (*   all : erewrite cfk_hdom; eauto.  *)
  (*   all : basic_solver. *)

  (* Qed. *)

  (* Lemma basic_step_nupd_simrel_a2e k k' e S S'  *)
  (*       (st st' st'': thread_st (ES.cont_thread S k)) *)
  (*       (SRCC : simrel_cert prog S G sc TC TC' f h k st st'') *)
  (*       (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e None S S') :  *)
  (*   let h' := upd h (e2a S' e) e in *)
  (*   simrel_a2e S' h' (cert_dom G TC (ES.cont_thread S' k') st').  *)
  (* Proof. *)
  (*   edestruct basic_step_simrel_a2e; eauto. *)
  (*   unfold upd_opt, option_map in *.  *)
  (*   constructor; auto. *)
  (* Qed. *)

  Lemma simrel_cert_basic_step_cstate k k' e e' S S'
        (st st' st'': thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    simrel_cstate S' k' st' st''. 
  Proof. 
    cdes BSTEP_. 
    constructor.
    (* cstate_stable : stable_state (ES.cont_thread S' k') st'' *)
    { eapply cstate_stable. apply SRCC. }
    (* cstate_q_cont : Kstate (k', st'); *)
    { red. exists st'. split; auto. 
      eapply basic_step_cont_set; eauto.
      erewrite basic_step_cont_thread_k with (S' := S'); eauto.
      subst. basic_solver. }
    (* cstate_reachable : (step (ES.cont_thread S' k'))＊ st' st'' *)
    admit. 
  Admitted.

  Lemma simrel_cert_basic_step_e2a_eqr k k' e e' S S' r r' r''
        (st st' st'' : thread_st (ES.cont_thread S k))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (BSTEP_ : basic_step_ (cont_lang S k) k k' st st' e e' S S') 
        (restrE : r ≡ ⦗ SE S ⦘ ⨾ r ⨾ ⦗ SE S ⦘)
        (rEQ : r' ≡ r) 
        (rIN : (e2a S) □ r ⊆ r'') : 
    (e2a S') □ r' ⊆ r''.
  Proof. 
    assert (basic_step e e' S S') as BSTEP.
    { econstructor. eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    rewrite rEQ, restrE, <- restr_relE. 
    rewrite collect_rel_restr_eq_dom. 
    2 : eapply basic_step_e2a_eq_dom; eauto. 
    rewrite restr_relE, <- restrE; eauto. 
  Qed.

  Lemma simrel_cert_basic_step_hb_sb_delta_dom k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (BSTEP_ : basic_step_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    dom_rel ((Shb S)^? ⨾ (sb_delta S k e e')) ⊆₁ certX S k ∪₁ eq e. 
  Proof. 
    cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    repeat autounfold with ESStepDb.
    arewrite (
        ES.cont_sb_dom S k × eq e ∪ (ES.cont_sb_dom S k ∪₁ eq e) × eq_opt e' ≡
                       ES.cont_sb_dom S k × (eq e ∪₁ eq_opt e') ∪ eq e × eq_opt e'
      ) by basic_solver.
    relsf. splits.
    { intros x [y [z [[EQxy | HB] [certD _]]]].
      { basic_solver. }
      left. eapply cert_ex_hb_prcl; eauto. basic_solver 10. }
    rewrite crE, seq_union_l, seq_id_l, dom_union. 
    unionL. splits.
    { basic_solver. }
    etransitivity; [| apply set_subset_empty_l]. 
    step_solver. 
  Qed.

  Lemma simrel_cert_basic_step_hb_rel_jf_sb_delta_dom k k' e e' S S'
        (st st' st'': (thread_st (ES.cont_thread S k)))
        (SRCC : simrel_cert prog S G sc TC TC' X k st st'')
        (BSTEP_ : basic_step_ (thread_lts (ES.cont_thread S k)) k k' st st' e e' S S') 
        (CST_REACHABLE : (lbl_step (ES.cont_thread S k))＊ st' st'') : 
    dom_rel ((Shb S)^? ⨾ release S ⨾ Sjf S ⨾ sb_delta S k e e') ⊆₁ certX S k. 
  Proof. 
    cdes BSTEP_.
    assert (basic_step e e' S S') as BSTEP.
    { econstructor; eauto. }
    assert (ES.Wf S) as WFS.
    { apply SRCC. }
    repeat autounfold with ESStepDb.
    arewrite (
        ES.cont_sb_dom S k × eq e ∪ (ES.cont_sb_dom S k ∪₁ eq e) × eq_opt e' ≡
                       ES.cont_sb_dom S k × (eq e ∪₁ eq_opt e') ∪ eq e × eq_opt e'
      ) by basic_solver.
    relsf. splits.
    { rewrite <- seqA.
      intros x [y [z [HA HB]]].
      eapply hb_rel_ew_cert_ex; eauto.
      edestruct jf_kE_in_ew_cert_ex as [a Ha]; eauto.
      { generalize HB. basic_solver 10. }
      eexists. apply seqA. 
      eexists; splits; eauto. }
    etransitivity; [| apply set_subset_empty_l]. 
    step_solver. 
  Qed.

End SimRelCertBasicStep.
