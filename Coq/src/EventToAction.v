Require Import Program.Basics Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution Prog ProgToExecution ProgToExecutionProperties
     CombRelations AuxRel.
Require Import AuxRel.
Require Import AuxDef.
Require Import EventStructure.
Require Import Consistency.
Require Import BasicStep.
Require Import ImmProperties.

Set Implicit Arguments.
Local Open Scope program_scope.

Section EventToAction.

  Variable prog : Prog.t.
  Variable PROG_NINIT : ~ (IdentMap.In tid_init prog).

  Variable S : ES.t.
  Variable G : execution.
  Variable GPROG : program_execution prog G.
  
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

  Lemma e2a_init_loc (WF : ES.Wf S) e (EINITe : SEinit e) : 
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
        (EE : e2a □₁ SE ⊆₁ GE) :
    e2a □₁ SEinit ⊆₁ GEinit.
  Proof.
    red. unfolder.
    intros e [e' [[Ee TIDe] E2A]].
    assert (GE e) as GEe by (apply EE; basic_solver). 
    split; auto.
    eapply tid_initi; eauto. 
    red; split; auto.
    subst e. by erewrite <- e2a_tid. 
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

  Lemma e2a_ext_sb 
        (EE : e2a □₁ SE ⊆₁ GE) 
        (WF : ES.Wf S) :
    e2a □ Ssb ⊆ ext_sb.
  Proof.
    rewrite WF.(ES.sb_Einit_Eninit). 
    rewrite <- WF.(ES.sb_seq_Eninit_l).
    relsf. unionL.
    { rewrite e2a_Einit, e2a_Eninit; auto.
      etransitivity; [|by apply initninit_in_ext_sb].
      basic_solver. }
    unfold e2a.
    rewrite collect_rel_if_else.
    2,3 : 
      rewrite WF.(ES.sb_seq_Eninit_l);
      unfold ES.acts_ninit_set, ES.acts_init_set, ES.acts_set; 
      basic_solver.
    intros x y HH. red in HH. desf. red.
    assert (Stid x' = Stid y') as TT.
    { apply WF.(ES.sb_tid). generalize HH. basic_solver. }
    rewrite TT.
    splits; auto.
    eapply ES.seqn_sb_alt; auto.
    apply seq_eqv_l in HH; desf. 
  Qed.

  Lemma e2a_sb 
        (EE : e2a □₁ SE ⊆₁ GE) 
        (WF : ES.Wf S) : 
    e2a □ Ssb ⊆ Gsb.
  Proof.
    rewrite ES.sbE; [|by apply WF].
    unfold Execution.sb.
      by rewrite !collect_rel_seqi, collect_rel_eqv, e2a_ext_sb, EE.
  Qed.

  (******************************************************************************)
  (** ** e2a is injective on non-conflicting events *)
  (******************************************************************************)

  (* Lemma e2a_ncf_eq (WF : ES.Wf S) x y (nCF : ~ Scf x y) (EQ : e2a x = e2a y) :  *)
  (*   x = y. *)
  (* Proof.  *)

  Lemma e2a_inj (WF : ES.Wf S) X (XinSE : X ⊆₁ SE) (CFF : ES.cf_free S X) : 
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
      edestruct e2a_init_loc as [lx [SLOCx GEx]]; 
        [auto | apply EINITx |].
      edestruct e2a_init_loc as [ly [SLOCy GEy]]; 
        [auto | apply EINITy |].
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

  Lemma e2a_inj_init (WF : ES.Wf S) : 
    inj_dom SEinit e2a. 
  Proof. 
    eapply e2a_inj; auto.
    { unfold ES.acts_init_set. basic_solver. }
    apply ES.ncfEinit.
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