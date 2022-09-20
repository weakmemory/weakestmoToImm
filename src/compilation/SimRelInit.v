Require Import Lia.
Require Import Program.Basics.
From hahn Require Import Hahn.
From PromisingLib Require Import Basic Language.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb
     CombRelations SimTraversal.
Require Import AuxRel.
Require Import AuxDef.
Require Import ImmProperties.
Require Import EventStructure.
Require Import Consistency.
Require Import Execution.
Require Import EventToAction.
Require Import LblStep.
Require Import SimRelCont.
Require Import SimRelEventToAction.
Require Import ProgES.
Require Import SimRel.

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelInit.

  Variable prog : stable_prog_type.
  Variable S : ES.t.
  Variable G : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable X : actid -> eventid.

  Notation "'SE'" := ES.acts_set.
  Notation "'SEinit'" := ES.acts_init_set.
  Notation "'SEninit'" := ES.acts_ninit_set.
  Notation "'Stid'" := ES.tid.
  Notation "'Slab'" := ES.lab.
  Notation "'Sloc' S" := (loc S.(ES.lab)) (at level 1).
  Notation "'K'" := ES.cont_set.

  Notation "'STid' S t" := (fun x => Stid S x = t) (at level 1).

  Notation "'SR'" := (fun a => is_true (is_r Slab a)).
  Notation "'SW'" := (fun a => is_true (is_w Slab a)).
  Notation "'SF'" := (fun a => is_true (is_f Slab a)).
  Notation "'SRel'" := (fun a => is_true (is_rel Slab a)).

  Notation "'Ssb'" := ES.sb.
  Notation "'Scf'" := ES.cf.
  Notation "'Srmw'" := ES.rmw.
  Notation "'Sjf'" := ES.jf.
  Notation "'Sjfi'" := ES.jfi.
  Notation "'Sjfe'" := ES.jfe.
  Notation "'Srf'" := ES.rf.
  Notation "'Srfi'" := ES.rfi.
  Notation "'Srfe'" := ES.rfe.
  Notation "'Sco'" := ES.co.
  Notation "'Sew'" := ES.ew.

  Notation "'Srs'" := Consistency.rs.
  Notation "'Srelease'" := Consistency.release.
  Notation "'Ssw'" := Consistency.sw.
  Notation "'Shb'" := Consistency.hb.

  Notation "'thread_syntax' tid"  :=
    (Language.syntax (thread_lts tid)) (at level 10, only parsing).

  Notation "'thread_st' tid" :=
    (Language.state (thread_lts tid)) (at level 10, only parsing).

  Notation "'thread_init_st' tid" :=
    (Language.init (thread_lts tid)) (at level 10, only parsing).

  Notation "'thread_cont_st' tid" :=
    (fun st => existT _ (thread_lts tid) st) (at level 10, only parsing).

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

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Notation "'Gfurr'" := (furr G sc).

  Lemma simrel_init
        (nInitProg : ~ IdentMap.In tid_init prog)
        (PExec : program_execution (stable_prog_to_prog prog) G)
        (WF : Execution.Wf G)
        (CONS : imm_consistent G sc)
        (nLocsEmpty : g_locs G <> [])
        (GCLOS : forall tid m n (LT : m < n) (NE : GE (ThreadEvent tid n)),
            GE (ThreadEvent tid m)) :
    let Sinit := prog_g_es_init prog G in
    simrel_consistent prog Sinit G sc
                      (init_trav G)
                      (ES.acts_set Sinit)
                      (fun t => IdentMap.In t prog).
  Proof.
    clear S TC X.
    assert (simrel_e2a (prog_g_es_init prog G) G sc) as HH.
    { by apply simrel_e2a_init. }
    simpls.
    red. splits.
    2: by apply prog_g_es_init_consistent.
    constructor; auto.
    { apply prog_g_es_init_wf; auto. }
    { apply init_trav_coherent; auto. }
    { constructor; eauto.
      2: basic_solver.
      simpls. ins.
      split.
      { apply rmw_from_non_init in RMW; auto.
        generalize RMW. basic_solver. }
      apply WF.(rmw_in_sb) in RMW.
      apply no_sb_to_init in RMW.
      generalize RMW. basic_solver. }
    { constructor.
      all: unfold ES.cf_free, vis, cc, ES.acts_init_set.
      all: autorewrite with prog_g_es_init_db; auto.
      all: try basic_solver.
      { rewrite prog_g_es_init_w at 1. type_solver. }
      unfolder. ins. splits; auto.
      unfold cc.
      ins. desf.
      exfalso.
      eapply prog_g_es_init_cf; eauto. }
    { constructor.
      all: try by (ins;
                   match goal with
                   | H : ES.cont_set _ _ |- _ =>
                     apply prog_g_es_init_K in H; desf
                   end).
      5: { ins. apply prog_g_es_init_K in INKi; desf.
           erewrite steps_same_eindex; eauto.
           { by unfold init. }
           apply wf_thread_state_init. }
      { ins. red in INK.
        rewrite prog_g_es_init_alt in *.
        unfold ES.init, prog_init_K, ES.cont_thread in *.
        simpls.
        apply in_map_iff in INK. desf. }
      { ins. apply prog_g_es_init_K in INK. desf.
        eapply wf_thread_state_steps.
        2: { simpls. apply eps_steps_in_steps. eauto. }
        apply wf_thread_state_init. }
      { ins.
        assert (exists xst,
                   IdentMap.find thread prog = Some xst /\
                   lprog = projT1 xst) as [xst [XST]];
          subst.
        { unfold stable_prog_to_prog in *.
          rewrite IdentMap.Facts.map_o in INPROG.
          unfold option_map in *. desf.
          eauto. }
        unfold prog_g_es_init, ES.init, prog_init_K, ES.cont_thread,
        ES.cont_set in *.
        simpls.
        eexists. splits.
        { apply in_map_iff.
          exists (thread, xst). splits. simpls.
            by apply IdentMap.elements_correct. }
        destruct xst as [lprog BB]. simpls.
        pose (AA :=
                @proj2_sig
                  _ _
                  (get_stable thread (init lprog) BB
                              (rt_refl state (step thread) (init lprog)))).
        red in AA. desf. }
      ins.
      apply eps_steps_in_steps.
      unfold prog_g_es_init, ES.init, prog_init_K, ES.cont_thread,
      ES.cont_set in *.
      simpls.
      apply in_map_iff in INK.
      destruct INK as [xst [INK REP]].
      apply pair_inj in INK. destruct INK as [AA INK].
      rewrite <- AA in *.
      inv INK.
      destruct xst as [thread [xprog BB]]. simpls.
      assert (xprog = lprog); subst.
      { clear -REP INPROG.
        apply IdentMap.elements_complete in REP.
        unfold stable_prog_to_prog in *.
        rewrite IdentMap.Facts.map_o in INPROG.
        unfold option_map in *. desf. }
      pose (AA :=
              @proj2_sig
                _ _
                (get_stable thread (init lprog) BB
                            (rt_refl state (step thread) (init lprog)))).
      red in AA. desf. }
    { unfold contsimstate.
      ins.
      unfold stable_prog_to_prog in INPROG.
      rewrite IdentMap.Facts.map_o in INPROG.
      unfold option_map in *. desf.
      match goal with
      | H : IdentMap.find _ _ = Some _ |- _ => rename H into INP
      end.
      destruct s as [lprog BB].
      pose (AA :=
              @proj2_sig
                _ _
                (get_stable thread (init lprog) BB
                            (rt_refl state (step thread) (init lprog)))).
      assert
        (K (prog_g_es_init prog G)
           (CInit thread,
            existT _
              (thread_lts thread)
              (proj1_sig
                 (get_stable thread (init lprog) BB
                             (rt_refl state (step thread) (init lprog))))))
          as INK.
      { unfold prog_g_es_init, ES.init, prog_init_K, ES.cont_thread,
        ES.cont_set in *.
        simpls.
        apply in_map_iff.
        eexists. splits.
        2: { apply IdentMap.elements_correct; eauto. }
        done. }

      exists (CInit thread). eexists.
      splits; eauto.
      { arewrite
          ((fun _ : eventid =>
              tid_init = ES.cont_thread (prog_g_es_init prog G)
                                        (CInit thread)) ≡₁ ∅).
        2: basic_solver.
        split; [|basic_solver].
        unfolder. ins. apply nInitProg.
        apply IdentMap.Facts.in_find_iff. desf.
        destruct (IdentMap.find tid_init prog); desf. }
      red in AA. desf.
      red. splits; ins.
      { erewrite steps_same_eindex; eauto.
        2: by eapply wf_thread_state_init.
        simpls.
        split; [|lia].
        unfold is_init. basic_solver. }

      unfold prog_g_es_init, ES.init, prog_init_K, ES.cont_thread,
      ES.cont_set in *. simpls.
      apply in_map_iff in INK.
      destruct INK as [[tid [lprog' BB']] [INK REP]].
      apply pair_inj in INK. destruct INK as [AA INK].
      assert (tid = thread) as TT by inv AA.
      rewrite TT in *.
      inv INK. desf.
      apply RegMap.elements_complete in REP.
      cdes PExec.
      edestruct (PExec1 thread lprog) as [pe [CC DD]].
      { unfold stable_prog_to_prog.
        rewrite IdentMap.Facts.map_o. unfold option_map.
        desf. }
      cdes CC.
      exists s.
      red. splits.
      2,3: by desf.
      eapply steps_to_eps_steps_steps; eauto.
        by apply terminal_stable. }
    { simpls.
      arewrite (GEinit ∪₁ dom_rel (Gsb^? ⨾ ⦗GEinit⦘) ≡₁ GEinit).
      { rewrite (no_sb_to_init G). basic_solver. }
      split.
      2: { rewrite prog_g_es_init_init. apply HH. }
      apply set_subset_inter_r. splits.
      2: by apply HH.
      unfold e2a. unfolder. ins. desf. }
    { unfold prog_g_es_init, prog_l_es_init, ES.init. basic_solver. }
    { eapply eq_dom_mori; eauto.
      2: by apply prog_g_es_init_same_lab.
      red. basic_solver. }
    { simpls. rewrite WF.(rmw_in_sb). rewrite no_sb_to_init.
      basic_solver. }
    { unfold prog_g_es_init, ES.init. basic_solver. }
    { unfold prog_g_es_init, ES.init. basic_solver. }
    { unfold prog_g_es_init, ES.init. basic_solver. }
    { unfold prog_g_es_init, ES.init. basic_solver. }
    { unfold ES.jfe, prog_g_es_init, ES.init. basic_solver. }
    { rewrite prog_g_es_init_alt. unfold ES.init. basic_solver. }
    unfold release.
    arewrite (is_rel (ES.lab (prog_g_es_init prog G)) ⊆₁ ∅).
    2: basic_solver 20.
    unfolder. ins.
    pose proof (prog_g_es_init_lab prog G x) as AA.
    unfold prog_g_es_init, ES.init, is_rel, Events.mod, mode_le in *. simpls.
    desf.
  Qed.

End SimRelInit.
