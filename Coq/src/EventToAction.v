Require Import Program.Basics Omega.
Require Import Coq.Logic.FunctionalExtensionality Classical_Prop.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution Prog ProgToExecution ProgToExecutionProperties
     CombRelations AuxRel.
Require Import AuxRel AuxDef EventStructure Consistency ImmProperties.

Set Implicit Arguments.
Local Open Scope program_scope.

Section EventToAction.

  Variable prog : Prog.t.
  Variable PROG_NINIT : ~ (IdentMap.In tid_init prog).

  Variable S : ES.t.
  Variable G  : execution.
  Variable GPROG : program_execution prog G.

  
  Notation "'SE'" := S.(ES.acts_set).
  Notation "'SEinit'" := S.(ES.acts_init_set).
  Notation "'SEninit'" := S.(ES.acts_ninit_set).
  Notation "'Stid'" := (S.(ES.tid)).
  Notation "'STid' t" := (fun x => Stid x = t) (at level 1).
  Notation "'Slab'" := (S.(ES.lab)).
  Notation "'Sloc'" := (loc S.(ES.lab)).
  Notation "'K'"  := S.(ES.cont_set).

  Notation "'Ssb'" := (S.(ES.sb)).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gloc'" := (loc G.(lab)).
  Notation "'Gtid'" := (tid).
  Notation "'GTid' t" := (fun x => tid x = t) (at level 1).

  Notation "'Gsb'" := (G.(sb)).

  Definition e2a (e : eventid) : actid :=
    if excluded_middle_informative (Stid e = tid_init)
    then 
      InitEvent (opt_ext BinNums.xH (Sloc e))
    else
      ThreadEvent (Stid e) (ES.seqn S e).

  (******************************************************************************)
  (** ** e2a general properties *)
  (******************************************************************************)

  Lemma e2a_init (WF : ES.Wf S) e (EINITe : SEinit e) : 
    exists l, 
      ⟪ SLOC : Sloc e = Some l⟫ /\
      ⟪ E2Ai : e2a e = InitEvent l⟫. 
  Proof. 
    edestruct ES.init_lab as [l SLAB]; eauto. 
    exists l. 
    assert (Sloc e = Some l) as SLOC. 
    { unfold loc. by rewrite SLAB. }
    splits; auto. 
    unfold ES.acts_init_set in EINITe.
    destruct EINITe as [_ TIDIe].
    unfold e2a. 
    destruct (excluded_middle_informative (Stid e = tid_init)); 
      [|congruence]. 
    unfold opt_ext. by rewrite SLOC. 
  Qed.

  Lemma e2a_ninit (WF : ES.Wf S) e (ENINITe : SEninit e) : 
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
    all : by unfold tid.
  Qed.

  Lemma e2a_Tid thread : 
    e2a □₁ STid thread ⊆₁ GTid thread.
  Proof. unfolder. ins. desf. symmetry. apply e2a_tid. Qed.

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
    unfold e2a, ES.acts_ninit_set. unfolder. 
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


  (******************************************************************************)
  (** ** e2a sb properties *)
  (******************************************************************************)

  Lemma e2a_ext_sb 
        (EE : e2a □₁ SE ⊆₁ GE) 
        (WF : ES.Wf S) :
    e2a □ Ssb ⊆ ext_sb.
  Proof.
    rewrite WF.(ES.sb_Einit_Eninit). relsf.
    unionL.
    { rewrite e2a_Einit, e2a_Eninit; auto.
      etransitivity; [|by apply initninit_in_ext_sb].
      basic_solver. }
    unfold e2a.
    rewrite collect_rel_if_else.
    2,3: unfold ES.acts_ninit_set; basic_solver.
    intros x y HH. red in HH. desf. red.
    assert (Stid x' = Stid y') as TT.
    { by apply WF.(ES.sb_tid). }
    rewrite TT.
    splits; auto.
    eapply ES.seqn_sb_alt; auto.
    apply seq_eqv_lr in HH; desf. 
  Qed.

  Lemma e2a_sb 
        (EE : e2a □₁ SE ⊆₁ GE) 
        (WF : ES.Wf S) : 
    e2a □ Ssb ⊆ Gsb.
  Proof.
    rewrite ES.sbE; [|by apply WF].
    unfold Execution.sb.
      by rewrite !collect_rel_seqi, set_collect_eqv, e2a_ext_sb, EE.
  Qed.

  (******************************************************************************)
  (** ** e2a is injective on non-conflicting events *)
  (******************************************************************************)

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
      edestruct e2a_init as [lx [SLOCx GEx]]; 
        [auto | apply EINITx |].
      edestruct e2a_init as [ly [SLOCy GEy]]; 
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
    { eapply ES.cf_free_subset; [|by apply CFF]. 
      basic_solver. }
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

  (******************************************************************************)
  (** ** a2e properties (for an arbitary a2e mapping) *)
  (******************************************************************************)

  Variable a2e : actid -> eventid.
  Variable aD : actid -> Prop.
  
  (* Stid e = Gtid (e2a e). *)

  Lemma a2e_tid 
        (FIX : fixset aD (e2a ∘ a2e)) : 
    eq_dom aD (Stid ∘ a2e) Gtid.
  Proof. 
    unfolder in *. unfold compose in *. 
    ins. specialize (FIX x SX).
    rewrite <- FIX, <- e2a_tid.
    congruence.
  Qed.

  Lemma a2e_same_lab_u2v
        (SLAB : same_lab_u2v_dom SE Slab (Glab ∘ e2a))
        (aDE : a2e □₁ aD ⊆₁ SE)
        (FIX : fixset aD (e2a ∘ a2e)) :
    same_lab_u2v_dom aD (Slab ∘ a2e) Glab.
  Proof. 
    unfolder in *. unfold compose in *. 
    unfold same_lab_u2v_dom in *. (*, same_label_u2v.*)
    ins. specialize (FIX e EE).
    rewrite <- FIX at 2.
    eapply SLAB.
    eapply aDE.
    eauto. 
  Qed.

End EventToAction.