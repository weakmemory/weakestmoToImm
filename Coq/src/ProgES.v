Require Import Omega Setoid Program.Basics.
From hahn Require Import Hahn.
From PromisingLib Require Import Basic Language.
From imm Require Import Events Prog Execution ProgToExecution.
Require Import AuxDef.
Require Import AuxRel.
Require Import EventStructure.
Require Import LblStep.
Require Import ProgLoc.
Require Import Consistency.
Require Import EventToAction.

Set Implicit Arguments.
Local Open Scope program_scope.

Definition thread_lts (t : thread_id) : Language.t (list label) :=
  @Language.mk (list label)
    (list Instr.t) state
    init
    is_terminal
    (ilbl_step t).

Definition prog_init_threads (prog : Prog.t) :
  IdentMap.t {lang : Language.t (list label) & Language.state lang} :=
  IdentMap.mapi
    (fun tid (linstr : list Instr.t) =>
       existT _ (thread_lts tid) (ProgToExecution.init linstr))
    prog.

Definition stable_prog_type := IdentMap.t { linstr & stable_lprog linstr }.
Definition stable_prog_to_prog (prog : stable_prog_type) : Prog.t :=
  (IdentMap.map (fun x => projT1 x) prog).

Lemma stable_prog_to_prog_in prog thread :
  IdentMap.In thread (stable_prog_to_prog prog) <-> IdentMap.In thread prog. 
Proof. 
  unfold stable_prog_to_prog. 
  eapply RegMap.Facts.map_in_iff.
Qed.

Lemma stable_prog_to_prog_no_init prog
      (PROG_NINIT : ~ IdentMap.In tid_init prog) :
  ~ IdentMap.In tid_init (stable_prog_to_prog prog).
Proof. by rewrite stable_prog_to_prog_in. Qed.

Definition prog_init_K
           (prog : stable_prog_type) :
  list (cont_label * {lang : Language.t (list label) & Language.state lang}) :=
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

Definition prog_l_es_init (prog : stable_prog_type) (locs : list location) :=
  ES.init (undup locs) (prog_init_K prog).

Definition prog_es_init (prog : stable_prog_type) :=
  prog_l_es_init prog (prog_locs (stable_prog_to_prog prog)).


Lemma prog_es_init_alt (prog : stable_prog_type) :
  prog_es_init prog = ES.init
                        (prog_locs (stable_prog_to_prog prog))
                        (prog_init_K prog).
Proof.
  unfold prog_es_init, prog_l_es_init, prog_locs.
  rewrite undup_nodup; eauto.
  apply NoDup_nodup.
Qed.

Definition g_locs (G : execution) :=
  undup (flatten (map (fun e =>
                         match e with
                         | InitEvent l => [l]
                         | _ => []
                         end)
                      (acts G))).

Definition prog_g_es_init prog (G : execution) :=
  prog_l_es_init prog (g_locs G).

Lemma prog_g_es_init_alt prog (G : execution) :
  prog_g_es_init prog G = ES.init (g_locs G) (prog_init_K prog).
Proof.
  unfold prog_g_es_init, prog_l_es_init, g_locs.
  rewrite undup_nodup; auto.
Qed.

Lemma prog_l_es_init_ninit locs prog :
  ES.acts_ninit_set (prog_l_es_init prog locs) ≡₁ ∅.
Proof.
  split; [|basic_solver].
  red. unfold prog_l_es_init, ES.init. intros x HH.
  apply HH. red. split; auto.
  apply HH.
Qed.

Lemma prog_g_es_init_ninit G prog :
  ES.acts_ninit_set (prog_g_es_init prog G) ≡₁ ∅.
Proof. apply prog_l_es_init_ninit. Qed.

Lemma prog_l_es_init_sb locs prog :
  ES.sb (prog_l_es_init prog locs) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfold prog_l_es_init, ES.init. simpls.
Qed.

Lemma prog_g_es_init_sb G prog :
  ES.sb (prog_g_es_init prog G) ≡ ∅₂.
Proof. apply prog_l_es_init_sb. Qed.

Lemma prog_l_es_init_jf locs prog :
  ES.jf (prog_l_es_init prog locs) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfold prog_l_es_init, ES.init. simpls.
Qed.

Lemma prog_g_es_init_jf G prog :
  ES.jf (prog_g_es_init prog G) ≡ ∅₂.
Proof. apply prog_l_es_init_jf. Qed.

Lemma prog_l_es_init_sw locs prog :
  sw (prog_l_es_init prog locs) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfold sw. rewrite prog_l_es_init_jf. basic_solver.
Qed.

Lemma prog_g_es_init_sw G prog :
  sw (prog_g_es_init prog G) ≡ ∅₂.
Proof. apply prog_l_es_init_sw. Qed.

Lemma prog_l_es_init_hb locs prog :
  hb (prog_l_es_init prog locs) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfold hb.
  rewrite prog_l_es_init_sw, prog_l_es_init_sb.
  rewrite ct_no_step; basic_solver.
Qed.

Lemma prog_g_es_init_hb G prog :
  hb (prog_g_es_init prog G) ≡ ∅₂.
Proof. apply prog_l_es_init_hb. Qed.

Lemma prog_l_es_init_cf locs prog :
  ES.cf (prog_l_es_init prog locs) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfold ES.cf. rewrite prog_l_es_init_ninit. basic_solver.
Qed.

Lemma prog_g_es_init_cf G prog :
  ES.cf (prog_g_es_init prog G) ≡ ∅₂.
Proof. apply prog_l_es_init_cf. Qed.

Lemma prog_l_es_init_psc_f locs prog :
  psc_f (prog_l_es_init prog locs) Weakestmo ≡ ∅₂.
Proof.
  unfold psc_f.
  rewrite prog_l_es_init_hb.
  basic_solver.
Qed.

Lemma prog_l_es_init_scb locs prog :
  scb (prog_l_es_init prog locs) ≡ ∅₂.
Proof.
  unfold scb.
  unfold ES.fr, ES.rf.
  rewrite prog_l_es_init_sb.
  rewrite prog_l_es_init_hb.
  rewrite prog_l_es_init_jf.
  basic_solver.
Qed.

Lemma prog_l_es_init_psc_base locs prog :
  psc_base (prog_l_es_init prog locs) ≡ ∅₂.
Proof.
  unfold psc_base.
  rewrite prog_l_es_init_scb.
  basic_solver.
Qed.

Lemma prog_l_es_init_rmw locs prog :
  ES.rmw (prog_l_es_init prog locs) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfold prog_l_es_init, ES.init. simpls.
Qed.

Hint Rewrite prog_g_es_init_ninit
     prog_g_es_init_sb
     prog_g_es_init_jf
     prog_g_es_init_sw
     prog_g_es_init_hb
     prog_g_es_init_cf
  : prog_g_es_init_db.

Hint Rewrite prog_l_es_init_ninit
     prog_l_es_init_sb
     prog_l_es_init_jf
     prog_l_es_init_sw
     prog_l_es_init_hb
     prog_l_es_init_cf
     prog_l_es_init_psc_f
     prog_l_es_init_psc_base
     prog_l_es_init_rmw
  : prog_l_es_init_db.

Lemma prog_l_es_init_consistent locs prog :
  @es_consistent (prog_l_es_init prog locs) Weakestmo.
Proof.
  constructor; unfold ecf, ES.jfe, ES.icf.
  all: autorewrite with prog_l_es_init_db; auto.
  7: apply acyclic_disj.
  all: basic_solver.
Qed.

Lemma prog_g_es_init_consistent G prog :
  @es_consistent (prog_g_es_init prog G) Weakestmo.
Proof. apply prog_l_es_init_consistent. Qed.

Lemma prog_es_init_consistent prog :
  @es_consistent (prog_es_init prog) Weakestmo.
Proof. apply prog_l_es_init_consistent. Qed.

Lemma prog_l_es_init_act_in prog locs
      e (ACT : ES.acts_set (prog_l_es_init prog locs) e) :
  exists l,
    In (e, init_write l)
       (indexed_list
          (map init_write (undup locs))).
Proof.
  ins.
  assert
    (exists b,
        In (e, b) (indexed_list
                     (map init_write (undup locs))))
    as [b IN].
  { apply indexed_list_range. desf. }

  assert (In b (map init_write (undup locs)))
    as BIN.
  { clear -IN.
    apply In_map_snd in IN.
    rewrite <- indexed_list_map_snd; eauto. }

  apply in_map_iff in BIN. destruct BIN as [l [LB INL]].
  rewrite <- LB in *. simpls. desf.
  eauto.
Qed.

Lemma prog_g_es_init_act_in prog G
      e (ACT : ES.acts_set (prog_g_es_init prog G) e) :
  exists l,
    In (e, init_write l)
       (indexed_list
          (map init_write (g_locs G))).
Proof.
  apply prog_l_es_init_act_in in ACT.
  unfold g_locs in *.
  rewrite undup_nodup in ACT; auto.
Qed.

Lemma prog_l_es_init_act_lab prog locs
      e (ACT : ES.acts_set (prog_l_es_init prog locs) e) :
  exists l, ES.lab (prog_l_es_init prog locs) e = Astore Xpln Opln l 0.
Proof.
  apply prog_l_es_init_act_in in ACT. destruct ACT as [l LL].
  exists l. unfold ES.lab, prog_g_es_init, ES.init.
  apply l2f_in; desf.
  apply indexed_list_fst_nodup.
Qed.

Lemma prog_g_es_init_act_lab prog G
      e (ACT : ES.acts_set (prog_g_es_init prog G) e) :
  exists l, ES.lab (prog_g_es_init prog G) e = Astore Xpln Opln l 0.
Proof. by apply prog_l_es_init_act_lab. Qed.

Lemma prog_l_es_init_w locs prog :
  ES.acts_set (prog_l_es_init prog locs) ≡₁
  ES.acts_set (prog_l_es_init prog locs) ∩₁
  (fun a => is_true (is_w (ES.lab (prog_l_es_init prog locs)) a)).
Proof.
  split; [|basic_solver].
  unfolder. intros. split; auto.
  unfold is_w.
  apply prog_l_es_init_act_lab in H. desf.
Qed.

Lemma prog_g_es_init_w G prog :
  ES.acts_set (prog_g_es_init prog G) ≡₁
  ES.acts_set (prog_g_es_init prog G) ∩₁
  (fun a => is_true (is_w (ES.lab (prog_g_es_init prog G)) a)).
Proof. apply prog_l_es_init_w. Qed.

Lemma prog_l_es_seqn locs prog x : ES.seqn (prog_l_es_init prog locs) x = 0.
Proof.
  unfold ES.seqn. autorewrite with prog_l_es_init_db; eauto.
  relsf.
  apply countNatP_empty.
Qed.

Lemma prog_g_es_seqn G prog x : ES.seqn (prog_g_es_init prog G) x = 0.
Proof. apply prog_l_es_seqn. Qed.

Lemma prog_l_es_init_init locs prog :
  ES.acts_set (prog_l_es_init prog locs) ≡₁
  ES.acts_init_set (prog_l_es_init prog locs).
Proof. unfold ES.acts_init_set. simpls. basic_solver. Qed.

Lemma prog_es_init_init prog :
  ES.acts_set (prog_es_init prog) ≡₁
  ES.acts_init_set (prog_es_init prog).
Proof. apply prog_l_es_init_init. Qed.

Lemma prog_g_es_init_init G prog :
  ES.acts_set (prog_g_es_init prog G) ≡₁
  ES.acts_init_set (prog_g_es_init prog G).
Proof. apply prog_l_es_init_init. Qed.

(* TODO : move to a more suitable place  *)
Lemma length_nempty {A : Type} (l : list A) (nEmpty : l <> []) :
  0 < length l.
Proof.
  unfold length.
  destruct l.
  { intuition. }
  apply Nat.lt_0_succ.
Qed.

Lemma prog_l_es_init_nempty locs prog
      (nInitProg : ~ IdentMap.In tid_init prog)
      (nLocsEmpty : locs <> []) :
  ~ ES.acts_init_set (prog_l_es_init prog locs) ≡₁ ∅.
Proof.
  intros HH. eapply HH.
  apply prog_l_es_init_init.
  unfold ES.acts_set.
  unfold prog_l_es_init, ES.init.
  simpls.
  erewrite map_length.
  eapply length_nempty.
  by apply undup_nonnil.
Qed.

Lemma prog_g_es_init_nempty G prog
      (nInitProg : ~ IdentMap.In tid_init prog)
      (nLocsEmpty : g_locs G <> []) :
  ~ ES.acts_init_set (prog_g_es_init prog G) ≡₁ ∅.
Proof. by apply prog_l_es_init_nempty. Qed.

Lemma prog_l_es_init_wf locs prog
      (nInitProg : ~ IdentMap.In tid_init prog)
      (nLocsEmpty : locs <> []) :
  ES.Wf (prog_l_es_init prog locs).
Proof.
  assert
    (NoDup (map init_write (undup locs)))
    as NNDD.
  { apply nodup_map.
    2: { ins. intros HH. inv HH. }
    unfold g_locs. apply nodup_undup. }
  constructor.
  all: autorewrite with prog_l_es_init_db; auto.
  all: simpls.
  all: try basic_solver.
  { ins. red. exists b.
    splits; auto.
    red. split; auto. }
  { intros e [AA BB].
    eapply prog_l_es_init_act_lab; eauto. }
  { red. ins.
    destruct SX as [SX _]. apply prog_l_es_init_act_in in SX.
    destruct SY as [SY _]. apply prog_l_es_init_act_in in SY.
    desf.
    assert (l0 = l); subst.
    { unfold loc, init_write in *.
      erewrite l2f_in in EQ; eauto.
      2: by apply indexed_list_fst_nodup.
      erewrite l2f_in in EQ; eauto.
      2: by apply indexed_list_fst_nodup.
      desf. }
    eapply indexed_list_snd_nodup; eauto. }
  { apply prog_l_es_init_nempty; eauto. }
  { red. basic_solver. }
  { unfolder. ins. eexists.
    splits; eauto.
    2: by red.
    apply prog_l_es_seqn. }
  { rewrite prog_l_es_init_w. type_solver. }
  { intros ol a b [[EA _] WA] [[EB _] WB].
    set (CA := EA). apply prog_l_es_init_act_in in CA. desf.
    set (CB := EB). apply prog_l_es_init_act_in in CB. desf.
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
    all: eapply prog_l_es_init_w; eauto.
    Unshelve. all: auto. }
  { intros HH. desf.
    unfold prog_l_es_init, ES.init, ES.cont_thread, ES.cont_set in *.
    simpls.
    unfold prog_init_K in KK.
    apply in_map_iff in KK.
    desf. destruct x as [tid k]; simpls; desf.
    apply RegMap.elements_complete in KK0.
    apply nInitProg.
    apply RegMap.Facts.in_find_iff.
    rewrite KK0. desf. }
  { intros HH. desf. inv RMW. }
  { unfold prog_l_es_init, ES.init, ES.cont_thread, ES.cont_set in *.
    simpls.
    unfold prog_init_K in *.
    ins.
    apply in_map_iff in CK. apply in_map_iff in CK'.
    desf.
    destruct x. destruct x0.
    apply RegMap.elements_complete in CK0.
    apply RegMap.elements_complete in CK'0.
    simpls; desf. }
  { ins. by apply prog_l_es_init_ninit in EE. }
  { ins. exfalso.
    red in inK.
    unfold prog_g_es_init, ES.init in *. simpls.
    unfold prog_init_K in *.
    apply in_map_iff in inK. desf. }
  ins. exfalso.
  unfold ES.cont_adjacent
    in ADJ.
  desc.
  unfold ES.cont_set,
         ES.cont,
         prog_g_es_init,
         prog_init_K
    in KK'.
  simpl in KK'.
  apply in_map_iff in KK'.
  destruct KK' as [HA [HB HC]].
  inversion HB. congruence.
Qed.

Lemma prog_g_es_init_wf G prog
      (nInitProg : ~ IdentMap.In tid_init prog)
      (nLocsEmpty : g_locs G <> []) :
  ES.Wf (prog_g_es_init prog G).
Proof. by apply prog_l_es_init_wf. Qed.

Lemma prog_es_init_wf prog
      (nInitProg : ~ IdentMap.In tid_init prog)
      (nLocsEmpty : prog_locs (stable_prog_to_prog prog) <> []) :
  ES.Wf (prog_es_init prog).
Proof. by apply prog_l_es_init_wf. Qed.

Lemma prog_g_es_init_same_lab prog G (WF : Wf G) :
  eq_dom (ES.acts_set (prog_g_es_init prog G))
         (ES.lab (prog_g_es_init prog G))
         (Execution.lab G ∘ e2a (prog_g_es_init prog G)).
Proof.
  red. ins.
  arewrite (undup (g_locs G) = g_locs G).
  { unfold g_locs. rewrite undup_nodup; auto. }
  unfold compose.

  apply prog_g_es_init_act_in in DX. desf.
  rewrite prog_g_es_init_alt.
  unfold e2a, ES.init, ES.acts_set in *; simpls; desf.
  unfold Events.loc.
  erewrite l2f_in; [|by apply indexed_list_fst_nodup|by eauto].
  simpls. rewrite wf_init_lab; auto.
Qed.

Lemma prog_l_es_init_K prog locs k state
      (INK : ES.cont_set
               (prog_l_es_init prog locs)
               (k, existT _
                     (thread_lts (ES.cont_thread (prog_l_es_init prog locs)
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
  unfold prog_l_es_init, ES.init, prog_init_K, ES.cont_thread in *.
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

Lemma prog_g_es_init_K prog G k state
      (INK : ES.cont_set
               (prog_g_es_init prog G)
               (k, existT _
                     (thread_lts (ES.cont_thread (prog_g_es_init prog G)
                                                 k))
                     state)) :
  exists thread,
    ⟪ KTID  : k = CInit thread ⟫ /\
    ⟪ STEPS : (istep thread [])＊ (init (instrs state)) state ⟫ /\
    ⟪ STBL  : stable_state state ⟫.
Proof. by apply prog_l_es_init_K. Qed.

Lemma prog_l_es_init_lab prog locs e :
  << ELAB : ES.lab (prog_l_es_init prog locs) e = Afence Orlx >> \/
  exists l,
  << ELAB : ES.lab (prog_l_es_init prog locs) e = init_write l >>.
Proof.
  unfold prog_l_es_init, ES.init. simpls.
  unnw.
  edestruct @l2f_v with (A:=nat)
                        (l:=indexed_list (map init_write (undup locs)))
                        (a:=e)
                        (DEC:=Nat.eq_dec).
  { apply indexed_list_fst_nodup. }

  2: { desf. left. eauto. }
  desf. right.
  generalize dependent e.
  unfold indexed_list in *.
  remember 0 as n. clear Heqn.
  generalize dependent n.
  induction (undup locs); simpls.
  ins. desf; eauto.
Qed.

Lemma prog_g_es_init_lab prog G e :
  << ELAB : ES.lab (prog_g_es_init prog G) e = Afence Orlx >> \/
  exists l,
  << ELAB : ES.lab (prog_g_es_init prog G) e = init_write l >>.
Proof. apply prog_l_es_init_lab. Qed.

(* TODO : move to a more suitable place  *)
Lemma traverse_map_indexed_list {A B} (f : A -> B) l :
  indexed_list (map f l) =
  map (fun p : nat * A => let (a, b) := p in (a, f b))
      (indexed_list l).
Proof.
  unfold indexed_list in *.
  remember 0 as n. clear Heqn.
  generalize dependent n.
  induction l; simpls.
  congruence.
Qed.

Lemma prog_l_es_init_init_loc prog locs :
  (fun l => In l locs) ≡₁ ES.init_loc (prog_l_es_init prog locs).
Proof.
  split.
  { intros l L_IN.
    apply in_undup_iff in L_IN.
    specialize (indexed_list_in_exists l (undup locs) L_IN) as [e Foo].
    exists e. splits.
    { apply prog_l_es_init_init.
      unfold prog_l_es_init, ES.init.
      unfold ES.acts_set, ES.next_act. rewrite length_map.
      apply indexed_list_range. eauto. }
    unfold prog_l_es_init, ES.init. simpl.
    unfold Events.loc.
    arewrite ((list_to_fun
                 Nat.eq_dec
                 (Afence Orlx)
                 (indexed_list (map init_write (undup locs)))) e =
              init_write l); [|done].
    apply l2f_in.
    { apply indexed_list_fst_nodup. }
    rewrite traverse_map_indexed_list.
    eapply in_map with
        (f := (fun p : nat * location => let (a, b) := p in (a, init_write b))) in Foo.
    auto. }
  intros l [a HH]. desf.
  unfold prog_l_es_init, ES.init, ES.lab in LOCA.
  specialize (l2f_codom (indexed_list (map init_write (undup locs)))
                        a
                        (Afence Orlx) Nat.eq_dec) as RR.
  desf; unfold loc in LOCA; desf.
  all: rewrite traverse_map_indexed_list in RR;
    apply in_map_iff in RR; desf.
  apply In_map_snd in RR0.
  rewrite indexed_list_map_snd in RR0.
  by apply in_undup_iff.
Qed.

Lemma prog_g_init_init_loc prog G :
  (fun l => In l (g_locs G)) ≡₁ ES.init_loc (prog_g_es_init prog G).
Proof. by apply prog_l_es_init_init_loc. Qed.

Lemma prog_es_init_init_loc prog :
  (fun l => In l (prog_locs (stable_prog_to_prog prog))) ≡₁ ES.init_loc (prog_es_init prog).
Proof. by apply prog_l_es_init_init_loc. Qed.
