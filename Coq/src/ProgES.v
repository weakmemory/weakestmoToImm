Require Import Omega Setoid Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Prog Execution ProgToExecution.
Require Import AuxDef.
Require Import AuxRel.
Require Import EventStructure.
Require Import LblStep.
Require Import ProgLoc.
Require Import Consistency.

Set Implicit Arguments.

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

Definition prog_init_K (prog : Prog.t) :=
  map
    (fun tidc =>
       (CInit (fst tidc), (snd tidc)))
    (RegMap.elements
       (prog_init_threads prog)).

Definition prog_es_init (prog : Prog.t) :=
  ES.init (prog_locs prog) (prog_init_K prog).

Definition g_locs (G : execution) :=
  undup (flatten (map (fun e =>
                         match e with
                         | InitEvent l => [l]
                         | _ => []
                         end)
                      (acts G))).

Definition prog_g_es_init (prog : Prog.t) (G : execution) :=
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
    In (e, Astore Xpln Opln l 0)
       (indexed_list
          (map (fun l : location => Astore Xpln Opln l 0)
               (g_locs G))).
Proof.
  ins.
  assert
    (exists b,
        In (e, b) (indexed_list
                     (map (fun l : location => Astore Xpln Opln l 0)
                          (g_locs G))))
    as [b IN].
  { apply indexed_list_range. desf. }

  assert (In b (map (fun l : location => Astore Xpln Opln l 0) (g_locs G)))
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
  
Lemma prog_g_es_init_wf G prog :
  ES.Wf (prog_g_es_init prog G).
Proof.
  assert
    (NoDup (map (fun l0 : location => Astore Xpln Opln l0 0) (g_locs G)))
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
    { unfold loc in *.
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
    { unfold loc in *.
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
    all: eapply prog_g_es_init_w; eauto. }
  1-4: admit.
Unshelve. all: auto.
Admitted.
