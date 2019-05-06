Require Import Omega Setoid Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Prog Execution ProgToExecution AuxRel.
Require Import AuxDef.
Require Import AuxRel.
Require Import EventStructure.
Require Import LblStep.
Require Import ProgLoc.
Require Import Consistency.
Require Import EventToAction.

Set Implicit Arguments.
Local Open Scope program_scope.

Definition thread_lts (t : thread_id) : Language.t :=
  @Language.mk
    (list Instr.t) state
    init
    is_terminal
    (ilbl_step t).

Definition prog_init_threads (prog : Prog.t) :
  IdentMap.t {lang : Language.t & Language.state lang} :=
  IdentMap.mapi
    (fun tid (linstr : list Instr.t) =>
       existT _ (thread_lts tid) (ProgToExecution.init linstr))
    prog.

Definition stable_prog_type := IdentMap.t { linstr & stable_lprog linstr }.
Definition stable_prog_to_prog (prog : stable_prog_type) : Prog.t :=
  (IdentMap.map (fun x => projT1 x) prog).

Lemma stable_prog_to_prog_no_init prog
      (PROG_NINIT : ~ IdentMap.In tid_init prog) :
  ~ IdentMap.In tid_init (stable_prog_to_prog prog).
Proof.
  unfold stable_prog_to_prog.
  intros HH.
  apply RegMap.Facts.map_in_iff in HH. intuition.
Qed.

Definition prog_init_K
           (prog : stable_prog_type) :
  list (cont_label * {lang : Language.t & Language.state lang}) :=
  map
    (fun tidc =>
       let tid    := fst tidc in
       let linstr := projT1 (snd tidc) in
       let STBL   := projT2 (snd tidc) in
       let st'    := proj1_sig (get_stable
                                  tid (init linstr) STBL
                                  (rt_refl _ _ (init linstr))) in
       (CInit tid, existT _ (thread_lts tid) st'))
    (RegMap.elements prog).
 
Definition prog_es_init (prog : stable_prog_type) :=
  ES.init (prog_locs (stable_prog_to_prog prog))
          (prog_init_K prog).

Definition g_locs (G : execution) :=
  undup (flatten (map (fun e =>
                         match e with
                         | InitEvent l => [l]
                         | _ => []
                         end)
                      (acts G))).

Definition prog_g_es_init prog (G : execution) :=
  ES.init (g_locs G) (prog_init_K prog).

Lemma prog_g_es_init_ninit G prog :
  ES.acts_ninit_set (prog_g_es_init prog G) ≡₁ ∅.
Proof.
  split; [|basic_solver].
  red. unfold prog_g_es_init, ES.init. intros x HH. 
  apply HH. red. split; auto.
  apply HH.
Qed.

Lemma prog_g_es_init_sb G prog :
  ES.sb (prog_g_es_init prog G) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfold prog_g_es_init, ES.init. simpls.
Qed.

Lemma prog_g_es_init_jf G prog :
  ES.jf (prog_g_es_init prog G) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfold prog_g_es_init, ES.init. simpls.
Qed.

Lemma prog_g_es_init_sw G prog :
  sw (prog_g_es_init prog G) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfold sw. rewrite prog_g_es_init_jf. basic_solver.
Qed.

Lemma prog_g_es_init_hb G prog :
  hb (prog_g_es_init prog G) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfold hb.
  rewrite prog_g_es_init_sw, prog_g_es_init_sb.
  rewrite ct_no_step; basic_solver.
Qed.

Lemma prog_g_es_init_cf G prog :
  ES.cf (prog_g_es_init prog G) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfold ES.cf. rewrite prog_g_es_init_ninit. basic_solver.
Qed.

Hint Rewrite prog_g_es_init_ninit
     prog_g_es_init_sb
     prog_g_es_init_jf
     prog_g_es_init_sw
     prog_g_es_init_hb
     prog_g_es_init_cf
  : prog_g_es_init_db.

Lemma prog_g_es_init_consistent G prog :
  @es_consistent (prog_g_es_init prog G) Weakestmo.
Proof.
  constructor; unfold ecf, ES.jfe, icf.
  all: autorewrite with prog_g_es_init_db; auto.
  all: basic_solver.
Qed.

Lemma prog_g_es_init_act_in prog G
      e (ACT : ES.acts_set (prog_g_es_init prog G) e) :
  exists l,
    In (e, init_write l)
       (indexed_list
          (map init_write (g_locs G))).
Proof.
  ins.
  assert
    (exists b,
        In (e, b) (indexed_list
                     (map init_write (g_locs G))))
    as [b IN].
  { apply indexed_list_range. desf. }

  assert (In b (map init_write (g_locs G)))
    as BIN.
  { clear -IN.
    apply In_map_snd in IN.
    rewrite <- indexed_list_map_snd; eauto. }

  apply in_map_iff in BIN. destruct BIN as [l [LB INL]].
  rewrite <- LB in *. simpls. desf.
  eauto.
Qed.

Lemma prog_g_es_init_act_lab prog G
      e (ACT : ES.acts_set (prog_g_es_init prog G) e) :
  exists l, ES.lab (prog_g_es_init prog G) e = Astore Xpln Opln l 0.
Proof.
  apply prog_g_es_init_act_in in ACT. destruct ACT as [l LL].
  exists l. unfold ES.lab, prog_g_es_init, ES.init.
  apply l2f_in; desf.
  apply indexed_list_fst_nodup.
Qed.

Lemma prog_g_es_init_w G prog :
  ES.acts_set (prog_g_es_init prog G) ≡₁
  ES.acts_set (prog_g_es_init prog G) ∩₁
  (fun a => is_true (is_w (ES.lab (prog_g_es_init prog G)) a)).
Proof.
  split; [|basic_solver].
  unfolder. intros. split; auto. 
  unfold is_w.
  apply prog_g_es_init_act_lab in H. desf.
Qed.

Lemma prog_g_es_seqn G prog x : ES.seqn (prog_g_es_init prog G) x = 0.
Proof.
  unfold ES.seqn. autorewrite with prog_g_es_init_db; eauto.
  relsf.
  apply countNatP_empty.
Qed.

Lemma prog_g_es_init_init G prog :
  ES.acts_set (prog_g_es_init prog G) ≡₁
  ES.acts_init_set (prog_g_es_init prog G).
Proof. unfold ES.acts_init_set. simpls. basic_solver. Qed.
  
Lemma prog_g_es_init_wf G prog (nInitProg : ~ IdentMap.In tid_init prog) :
  ES.Wf (prog_g_es_init prog G).
Proof.
  assert
    (NoDup (map init_write (g_locs G)))
    as NNDD.
  { apply nodup_map.
    2: { ins. intros HH. inv HH. }
    unfold g_locs. apply nodup_undup. }
  constructor.
  all: autorewrite with prog_g_es_init_db; auto.
  all: simpls.
  all: try basic_solver.
  { ins. red. exists b.
    splits; auto.
    red. split; auto. }
  { intros e [AA BB]. 
    eapply prog_g_es_init_act_lab; eauto. }
  { red. ins.
    destruct SX as [SX _]. apply prog_g_es_init_act_in in SX.
    destruct SY as [SY _]. apply prog_g_es_init_act_in in SY.
    desf.
    assert (l0 = l); subst.
    { unfold loc, init_write in *.
      erewrite l2f_in in EQ; eauto.
      2: by apply indexed_list_fst_nodup.
      erewrite l2f_in in EQ; eauto.
      2: by apply indexed_list_fst_nodup.
      desf. }
    eapply indexed_list_snd_nodup; eauto. }
  { red. basic_solver. }
  { unfolder. ins. eexists.
    splits; eauto.
    2: by red.
    apply prog_g_es_seqn. }
  { rewrite prog_g_es_init_w. type_solver. }
  { intros ol a b [[EA _] WA] [[EB _] WB].
    set (CA := EA). apply prog_g_es_init_act_in in CA. desf.
    set (CB := EB). apply prog_g_es_init_act_in in CB. desf.
    assert (l0 = l); subst.
    { unfold loc, init_write in *.
      erewrite l2f_in in WB; eauto.
      2: by apply indexed_list_fst_nodup.
      erewrite l2f_in in WB; eauto.
      2: by apply indexed_list_fst_nodup.
      desf. }
    unfolder. ins. exfalso. apply nEW. splits; auto.
    clear -CA CB NNDD.
    eapply indexed_list_snd_nodup; eauto. }
  { split; [|basic_solver].
    unfolder. ins. desf. splits; auto.
    all: eapply prog_g_es_init_w; eauto.
    Unshelve. all: auto. }
  { intros HH. desf.
    unfold prog_g_es_init, ES.init, ES.cont_thread, ES.cont_set in *. 
    simpls.
    unfold prog_init_K in KK.
    apply in_map_iff in KK.
    desf. destruct x as [tid k]; simpls; desf.
    apply RegMap.elements_complete in KK0.
    apply nInitProg.
    apply RegMap.Facts.in_find_iff.
    rewrite KK0. desf. }
  { unfold prog_g_es_init, ES.init, ES.cont_thread, ES.cont_set in *. 
    simpls.
    unfold prog_init_K in *.
    ins.
    apply in_map_iff in CK. apply in_map_iff in CK'.
    desf.
    destruct x. destruct x0.
    apply RegMap.elements_complete in CK0.
    apply RegMap.elements_complete in CK'0.
    simpls; desf. }
  { ins. by apply prog_g_es_init_ninit in EE. }
  ins. exfalso.
  red in inK.
  unfold prog_g_es_init, ES.init in *. simpls.
  unfold prog_init_K in *.
  apply in_map_iff in inK. desf.
Qed.

Lemma prog_g_es_init_same_lab prog G (WF : Wf G) :
  eq_dom (ES.acts_set (prog_g_es_init prog G))
         (ES.lab (prog_g_es_init prog G))
         (Execution.lab G ∘ e2a (prog_g_es_init prog G)).
Proof.
  red. ins.
  unfold compose.
  apply prog_g_es_init_act_in in SX. desf.

  unfold prog_g_es_init, e2a, ES.init, ES.acts_set in *; simpls; desf.
  unfold Events.loc.
  erewrite l2f_in; [|by apply indexed_list_fst_nodup|by eauto].
  simpls. rewrite wf_init_lab; auto.
Qed.

Lemma prog_g_es_init_K prog G k state
      (INK : ES.cont_set
               (prog_g_es_init prog G)
               (k, existT
                     Language.state
                     (thread_lts (ES.cont_thread (prog_g_es_init prog G)
                                                 k))
                     state)) :
  exists thread,
    ⟪ KTID  : k = CInit thread ⟫ /\
    ⟪ STEPS : (istep thread [])＊ (init (instrs state)) state ⟫ /\
    ⟪ STBL  : stable_state state ⟫.
Proof.
  assert (forall A B (c : A) (a b : B)
                 (OO : (c, a) = (c, b)), a = b) as OO.
  { ins. inv OO. }
  ins. red in INK.
  unfold prog_g_es_init, ES.init, prog_init_K, ES.cont_thread in *.
  simpls.
  apply in_map_iff in INK. desc. inv INK.
  destruct x. simpls. desf.
  apply OO in INK.
  inv INK.
  destruct s; simpls.
  eexists; splits; eauto.
  all: pose (AA :=
               @proj2_sig 
                 _ _ 
                 (get_stable t (init x) s
                             (rt_refl state (step t) (init x)))).
  arewrite
    (instrs
       (proj1_sig
          (get_stable t (init x) s (rt_refl state (step t) (init x)))) =
     instrs (init x)).
  all: red in AA; desf.
  eapply steps_same_instrs; eauto.
  apply eps_steps_in_steps. eauto.
Qed.