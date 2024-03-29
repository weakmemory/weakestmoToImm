Require Import Program.Basics Lia.
From hahn Require Import Hahn.
From PromisingLib Require Import Basic Language.
From imm Require Import Events Execution Prog ProgToExecution ProgToExecutionProperties
     CombRelations.
Require Import AuxRel.
Require Import AuxDef.
Require Import EventStructure.
Require Import Consistency.
Require Import BasicStep.
Require Import ImmProperties.

Set Implicit Arguments.
Local Open Scope program_scope.

Section EventToAction.

  Variable S : ES.t.
  Hypothesis WF : ES.Wf S.
  Variable G : execution.

  Notation "'SE'" := S.(ES.acts_set).
  Notation "'SEinit'" := S.(ES.acts_init_set).
  Notation "'SEninit'" := S.(ES.acts_ninit_set).
  Notation "'Stid'" := (S.(ES.tid)).
  Notation "'Slab'" := (S.(ES.lab)).
  Notation "'Sloc'" := (Events.loc (ES.lab S)).
  Notation "'K'"  := S.(ES.cont_set).

  Notation "'STid' t" := (fun x => Stid x = t) (at level 1).
  Notation "'SNTid' t" := (fun x => Stid x <> t) (at level 1).

  Notation "'Ssb'" := (S.(ES.sb)).
  Notation "'Scf'" := (S.(ES.cf)).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).
  Notation "'Glab'" := (lab G).
  Notation "'Gloc'" := (Events.loc (lab G)).
  Notation "'Gtid'" := (Events.tid).

  Notation "'GTid' t" := (fun x => Gtid x = t) (at level 1).
  Notation "'GNTid' t" := (fun x => Gtid x <> t) (at level 1).

  Notation "'Gsb'" := (Execution.sb G).

  Definition e2a (e : eventid) : actid :=
    if excluded_middle_informative (Stid e = tid_init)
    then
      InitEvent (opt_ext BinNums.xH (Sloc e))
    else
      ThreadEvent (Stid e) (ES.seqn S e).

  (******************************************************************************)
  (** ** e2a general properties *)
  (******************************************************************************)

  Lemma e2a_init e (EINITe : SEinit e) :
    e2a e = InitEvent (opt_ext BinNums.xH (Sloc e)).
  Proof.
    unfold ES.acts_ninit_set, ES.acts_init_set in EINITe.
    destruct EINITe as [SEe STIDe].
    unfold e2a.
    destruct
      (excluded_middle_informative (Stid e = tid_init));
      [auto | congruence].
  Qed.

  Lemma e2a_init_loc e (EINITe : SEinit e) :
    exists l,
      ⟪ SLOC : Sloc e = Some l⟫ /\
      ⟪ E2Ai : e2a e = InitEvent l⟫.
  Proof.
    edestruct ES.init_lab as [l SLAB]; eauto.
    exists l.
    assert (Sloc e = Some l) as SLOC.
    { unfold Events.loc. by rewrite SLAB. }
    splits; auto.
    rewrite e2a_init; auto.
    unfold opt_ext. by rewrite SLOC.
  Qed.

  Lemma e2a_ninit e (ENINITe : SEninit e) :
    e2a e = ThreadEvent (Stid e) (ES.seqn S e).
  Proof.
    unfold ES.acts_ninit_set, ES.acts_init_set in ENINITe.
    destruct ENINITe as [SEe HH].
    unfold e2a.
    destruct (excluded_middle_informative (Stid e = tid_init)); [|auto].
    exfalso. apply HH. by unfolder.
  Qed.

  (******************************************************************************)
  (** ** e2a tid properties *)
  (******************************************************************************)

  Lemma e2a_tid e :
    Stid e = Gtid (e2a e).
  Proof.
    unfold e2a.
    destruct (excluded_middle_informative (Stid e = tid_init)).
    1 : destruct (Sloc e).
    all : by unfold Events.tid.
  Qed.

  Lemma e2a_Tid thread :
    e2a □₁ STid thread ⊆₁ GTid thread.
  Proof. unfolder. ins. desf. symmetry. apply e2a_tid. Qed.

  Lemma e2a_NTid thread :
    e2a □₁ SNTid thread ⊆₁ GNTid thread.
  Proof.
    unfolder.
    intros x [y [NTIDy EQx]].
    intros TIDx. apply NTIDy.
    subst. apply e2a_tid.
  Qed.

  Lemma e2a_Einit
        (EE : e2a □₁ SE ⊆₁ GE):
    e2a □₁ SEinit ⊆₁ GEinit.
  Proof.
    red. unfolder.
    intros e [e' [[Ee TIDe] E2A]].
    split; [|by apply EE; basic_solver].
    unfold e2a in E2A.
    desf.
  Qed.

  Lemma e2a_Eninit
        (EE : e2a □₁ SE ⊆₁ GE) :
    e2a □₁ SEninit ⊆₁ GEninit.
  Proof.
    unfold ES.acts_ninit_set, ES.acts_init_set, ES.acts_set.
    unfold e2a. unfolder.
    ins; split; desf; auto.
    { exfalso; auto. }
    apply EE. unfolder.
    eexists; split; eauto.
    unfold e2a.
    destruct
      (excluded_middle_informative (Stid y = tid_init));
      auto.
    by exfalso.
  Qed.

  Lemma e2a_map_Einit :
    SE ∩₁ e2a ⋄₁ GEinit ⊆₁ SEinit.
  Proof.
    intros x [SEx [INITx GEx]].
    split; auto.
    unfold is_init, EventToAction.e2a in INITx.
    destruct
      (excluded_middle_informative (Stid x = tid_init));
      done.
  Qed.

  (******************************************************************************)
  (** ** e2a sb properties *)
  (******************************************************************************)

  Lemma e2a_ext_sb_restr (X : eventid -> Prop)
        (XE : X ⊆₁ SE):
    e2a □ restr_rel X Ssb ⊆ ext_sb.
  Proof.
    rewrite WF.(ES.sb_Einit_Eninit).
    unfolder.
    intros a1 a2 [e1 [e2 HH]].
    destruct HH as [[SSB [Xe1 Xe2]] [EQ1 EQ2]].
    unfold e2a in EQ1, EQ2.
    destruct (excluded_middle_informative (ES.tid S e1 = tid_init));
      destruct (excluded_middle_informative (ES.tid S e2 = tid_init)).
    1, 3:
      unfold ES.acts_ninit_set, ES.acts_init_set in *;
      unfolder in *; desf; basic_solver.
    { subst. basic_solver. }
    subst. simpls.
    desf.
    { exfalso. apply n, SSB. }
    assert (SAME_TID : ES.same_tid S e1 e2).
    { apply WF.(ES.sb_tid). basic_solver. }
    split; auto.
    by apply ES.seqn_sb_alt.
  Qed.

  Lemma e2a_ext_sb :
    e2a □ Ssb ⊆ ext_sb.
  Proof.
    rewrite <- e2a_ext_sb_restr; eauto.
    rewrite WF.(ES.sbE) at 1.
    by rewrite restr_relE.
  Qed.

  Lemma e2a_sb
        (EE : e2a □₁ SE ⊆₁ GE) :
    e2a □ Ssb ⊆ Gsb.
  Proof.
    rewrite WF.(ES.sbE).
    unfold Execution.sb.
      by rewrite !collect_rel_seqi, collect_rel_eqv, e2a_ext_sb, EE.
  Qed.

  (******************************************************************************)
  (** ** e2a cf properties *)
  (******************************************************************************)

  Lemma e2a_eq_in_cf x y (Ex : SE x) (Ey : SE y) :
    e2a x = e2a y -> x = y \/ Scf x y.
  Proof.
    intros EQ.
    apply ES.acts_set_split in Ex.
    destruct Ex as [INITx | nINITx].
    { edestruct e2a_init_loc as [l HH];
        eauto; desc.
      assert (SEinit y) as INITy.
      { destruct (e2a y) as [l' | HH] eqn:Heqy;
          [|congruence].
        unfold e2a in Heqy.
        destruct
          (excluded_middle_informative (Stid y = tid_init));
          [|congruence].
        unfold ES.acts_init_set.
        basic_solver. }
      edestruct e2a_init_loc as [l' HH];
        eauto; desc.
      left. eapply WF.(ES.init_uniq); auto.
      congruence. }
    erewrite e2a_ninit in EQ; auto.
    assert (SEninit y) as nINITy.
    { destruct (e2a y) as [l' | HH] eqn:Heqy;
        [congruence|].
      unfold e2a in Heqy.
      destruct
        (excluded_middle_informative (Stid y = tid_init));
        [congruence|].
      unfold ES.acts_ninit_set, ES.acts_init_set.
      split; auto.
      intros [_ INIT]; auto. }
    erewrite e2a_ninit in EQ; auto.
    inversion EQ as [[TIDeq SEQNeq]].
    destruct (classic (x = y)) as [EQxy | nEQxy].
    { basic_solver. }
    right.
    edestruct ES.same_thread_alt
      with (x := x) (y := y) as [SB | CF]; eauto.
    { apply nINITx. }
    exfalso.
    destruct SB as [EQ' | [SB | tSB]]; auto.
    { apply ES.seqn_sb_alt in SB; auto. lia. }
    unfold transp in tSB.
    apply ES.seqn_sb_alt in tSB; auto; [lia|].
    red. congruence.
  Qed.

  Lemma e2a_inj X (XinSE : X ⊆₁ SE) (CFF : ES.cf_free S X) :
    inj_dom X e2a.
  Proof.
    unfolder. ins.

    destruct
      (excluded_middle_informative (Stid x = tid_init),
       excluded_middle_informative (Stid y = tid_init))
    as [[INITx | nINITx]  [INITy | nINITy]].
    { assert (SEinit x) as EINITx.
      { unfold ES.acts_init_set, set_inter.
        split; auto. }
      assert (SEinit y) as EINITy.
      { unfold ES.acts_init_set, set_inter.
        split; auto. }
      edestruct e2a_init_loc as [lx [SLOCx GEx]]; auto.
      { apply EINITx. }
      edestruct e2a_init_loc as [ly [SLOCy GEy]]; auto.
      { apply EINITy. }
      eapply WF.(ES.init_uniq); auto; congruence. }
    all: unfold e2a in *; desf.
    eapply ES.seqn_inj.
    { eauto. }
    { eapply set_inter_Proper.
      { unfold ES.acts_ninit_set.
        eapply set_minus_mori; [eapply XinSE|].
        unfold flip. eauto. }
      eapply set_subset_refl. }
    { eapply ES.cf_free_mori; try apply CFF; auto.
      red. basic_solver. }
    assert (~ SEinit x) as nEINITx.
    { unfold ES.acts_init_set, set_inter.
      red. intros [_ HH]. auto. }
    assert (~ SEinit y) as nEINITy.
    { unfold ES.acts_init_set, set_inter.
      red. intros [_ HH]. auto. }
    1,3: basic_solver.
    unfolder; splits; auto.
    red. intros [_ HH]. auto.
  Qed.

  Lemma e2a_inj_init :
    inj_dom SEinit e2a.
  Proof.
    eapply e2a_inj; auto.
    { unfold ES.acts_init_set. basic_solver. }
    apply ES.ncfEinit.
  Qed.

  Lemma e2a_cont_sb_dom_inj k a b lang (st : Language.state lang)
        (KE : K (k, existT _ lang st))
        (ACTS : e2a □₁ SE ⊆₁ acts_set G)
        (AIN : ES.cont_sb_dom S k a)
        (BIN : ES.cont_sb_dom S k b)
        (EQ  : e2a a = e2a b) :
    a = b.
  Proof.
    assert (SE a) as EA.
    { eapply ES.cont_sb_domE; eauto. }
    assert (SE b) as EB.
    { eapply ES.cont_sb_domE; eauto. }
    red in AIN. red in BIN. desf.
    { eapply e2a_inj_init; eauto. }
    assert (a = b \/ (Ssb a b \/ Ssb b a)) as AA.
    2: { destruct AA as [|AA]; auto.
         exfalso. desf.
         all: eapply sb_irr with (G:=G); eapply e2a_sb; eauto.
         1,2: by red; eauto. }
    destruct (classic (SEinit a)) as [AINIT|ANINIT].
    { destruct (classic (SEinit b)) as [BINIT|BNINIT].
      { left. eapply e2a_inj_init; eauto. }
      right. left. apply WF.(ES.sb_Einit_Eninit). left.
      repeat (split; auto). }
    destruct (classic (SEinit b)) as [BINIT|BNINIT].
    { right. right. apply WF.(ES.sb_Einit_Eninit). left.
      repeat (split; auto). }
    destruct (classic (a = b)) as [|NEQ]; [by left|right].
    unfolder in AIN. unfolder in BIN. desf; auto.
    eapply WF.(ES.sb_tot); auto.
    { eapply ES.K_inEninit; eauto. }
    all: unfolder; splits; eauto.
  Qed.

End EventToAction.

Section EventToActionLemmas.

  Variable prog : Prog.t.
  Variable PROG_NINIT : ~ (IdentMap.In tid_init prog).

  Variable S : ES.t.
  Variable G : execution.
  Variable GPROG : program_execution prog G.

  Variable WF : ES.Wf S.

  Notation "'SE' S" := S.(ES.acts_set) (at level 10).
  Notation "'SEinit' S" := S.(ES.acts_init_set) (at level 10).
  Notation "'SEninit' S" := S.(ES.acts_ninit_set) (at level 10).

  Notation "'Stid' S" := (S.(ES.tid)) (at level 10).
  Notation "'Slab' S" := (S.(ES.lab)) (at level 10).
  Notation "'Sloc' S" := (Events.loc S.(ES.lab)) (at level 10).

  Notation "'K' S" := S.(ES.cont_set) (at level 10).

  Notation "'STid' S" := (fun t e => S.(ES.tid) e = t) (at level 10).

  Notation "'Ssb' S" := (S.(ES.sb)) (at level 10).
  Notation "'Scf' S" := (S.(ES.cf)) (at level 10).
  Notation "'Srmw' S" := (S.(ES.rmw)) (at level 10).

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

  Lemma basic_step_e2a_eq_dom e e' S'
        (BSTEP : basic_step e e' S S') :
    eq_dom (SE S) (e2a S') (e2a S).
  Proof.
    cdes BSTEP; cdes BSTEP_.
    red. intros x. ins.
    unfold e2a.
    assert (Stid S' x = tid_init <-> Stid S x = tid_init) as AA.
    { red; split; ins;
        [ erewrite <- basic_step_tid_eq_dom
        | erewrite basic_step_tid_eq_dom
        ]; eauto. }
    assert ((Sloc S') x = (Sloc S) x) as BB.
    { eapply basic_step_loc_eq_dom; eauto. }
    unfold opt_ext; desf; try by (exfalso; intuition).
    assert ((Stid S') x = (Stid S) x) as CC.
    { eapply basic_step_tid_eq_dom; eauto. }
    assert (ES.seqn S' x = ES.seqn S x) as DD.
    { eapply basic_step_seqn_eq_dom; eauto. }
    congruence.
  Qed.

  Lemma basic_step_e2a_set_collect_eq_dom e e' S' s
        (BSTEP : basic_step e e' S S')
        (inE : s ⊆₁ SE S) :
    e2a S' □₁ s ≡₁ e2a S □₁ s.
  Proof.
    eapply set_collect_eq_dom.
    rewrite inE.
    eapply basic_step_e2a_eq_dom; eauto.
  Qed.

  Lemma basic_step_e2a_collect_rel_eq_dom e e' S' r
        (BSTEP : basic_step e e' S S')
        (restrE : r ≡ ⦗ SE S ⦘ ⨾ r ⨾ ⦗ SE S ⦘) :
    e2a S' □ r ≡ e2a S □ r.
  Proof.
    rewrite restrE, <- restr_relE.
    eapply collect_rel_restr_eq_dom.
    eapply basic_step_e2a_eq_dom; eauto.
  Qed.

  Lemma basic_step_e2a_set_map_inter_old e e' S' s s'
        (BSTEP : basic_step e e' S S')
        (inE : s ⊆₁ SE S) :
    s ∩₁ (e2a S' ⋄₁ s') ≡₁ s ∩₁ (e2a S ⋄₁ s').
  Proof.
    unfolder. split.
    { intros x [Sx S'x].
      splits; auto.
      erewrite <- basic_step_e2a_eq_dom; eauto. }
    intros x [Sx S'x].
    splits; auto.
    erewrite basic_step_e2a_eq_dom; eauto.
  Qed.

  Lemma basic_step_e2a_map_rel_inter_restr e e' S' r r'
        (BSTEP : basic_step e e' S S') :
    restr_rel (SE S) r ∩ (e2a S' ⋄ r') ≡ restr_rel (SE S) r ∩ (e2a S ⋄ r').
  Proof.
    unfolder. split.
    { intros x y [[Rxy [Ex Ey]] R'xy].
      splits; auto.
      erewrite <- basic_step_e2a_eq_dom; eauto.
      erewrite <- basic_step_e2a_eq_dom; eauto. }
    intros x y [[Rxy [Ex Ey]] R'xy].
    splits; auto.
    erewrite basic_step_e2a_eq_dom; eauto.
    erewrite basic_step_e2a_eq_dom with (S' := S'); eauto.
  Qed.

  Lemma basic_step_e2a_map_rel_inter_old e e' S' r r'
        (BSTEP : basic_step e e' S S')
        (restrE : r ≡ ⦗ SE S ⦘ ⨾ r ⨾ ⦗ SE S ⦘) :
    r ∩ (e2a S' ⋄ r') ≡ r ∩ (e2a S ⋄ r').
  Proof.
    rewrite restrE.
    rewrite <- restr_relE.
    eapply basic_step_e2a_map_rel_inter_restr; eauto.
  Qed.

End EventToActionLemmas.
