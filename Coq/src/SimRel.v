From hahn Require Import Hahn.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecutionProperties.
Require Import AuxRel AuxDef EventStructure Construction Consistency.
Require Import Coq.Logic.FunctionalExtensionality.

Section SimRel.
  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G  : execution.
  Variable GPROG : program_execution prog G.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable f  : actid -> EventId.t.

  Notation "'SE'" := S.(ES.acts_set).
  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).
  Notation "'GE'" := G.(acts_set).
  Notation "'Gtid'" := (tid).
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gsb'" := (G.(sb)).
  Notation "'Grf'" := (G.(rf)).
  Notation "'Gco'" := (G.(co)).
  Notation "'Stid'" := (EventId.tid).
  Notation "'Slab'" := (EventId.lab).
  Notation "'Ssb'" := (S.(ES.sb)).
  Notation "'Srf'" := (S.(ES.rf)).
  Notation "'Sco'" := (S.(ES.co)).
  Notation "'Scf'" := (S.(ES.cf)).

  (* TODO. Should state smth about `execs` used in Construction.v.
     Probably, in terms of a program. *)
  Record simrel_common :=
    { tccoh : tc_coherent G sc TC;
      (*fdef  : forall e (COV : C e),
        f e = act_to_event G e; *)
      finj  : inj_dom (C ∪₁ I) f;  
      tidEq : forall e (CpoI : (C ∪₁ dom_rel (Gsb ;; <| I |>)) e),
        Stid e.(f) = Gtid e;
      labEq : forall e (CI : (C ∪₁ I) e),
        Slab e.(f) = Glab e;
      foth  : (f ∘₁ set_compl (C ∪₁ I)) ∩₁ SE ≡₁ ∅;
      sbPrcl : Ssb ⨾ ⦗ f ∘₁ C ⦘ ⊆ ⦗ f ∘₁ C ⦘ ⨾ Ssb;
      sbF : f ∘ ⦗ C ⦘ ⨾ Gsb ⨾ ⦗ C ⦘ ≡
            ⦗ f ∘₁ C ⦘ ⨾ Ssb ⨾ ⦗ f ∘₁ C ⦘;
      cimgNcf : ⦗ f ∘₁ C ⦘ ⨾ Scf ⨾ ⦗ f ∘₁ C ⦘ ≡ ∅₂;
      imgrf : f ∘ ⦗ I ⦘ ⨾ Grf ⨾ ⦗ C ⦘ ≡
              ⦗ f ∘₁ I ⦘ ⨾ Srf  ⨾ ⦗ f ∘₁ C ⦘;
      imgco : f ∘ ⦗ I ⦘ ⨾ Gco ⨾ ⦗ I ⦘ ⊆
              ⦗ f ∘₁ I ⦘ ⨾ Sco  ⨾ ⦗ f ∘₁ I ⦘;
    }.
  
  Implicit Type SRC : simrel_common.

  Lemma finE SRC e (SEE : SE (f e)) : GE e.
  Proof.
    destruct (classic (GE e)) as [|NGE]; auto.
    exfalso.
    eapply foth; auto.
    split; eauto.
    autounfold with unfolderDb.
    eexists. split; eauto.
    intros [AA|AA]; apply NGE.
    2: eapply issuedE; eauto.
    eapply coveredE; eauto.
    all: apply SRC.
  Qed.

  Record simrel :=
    { comm : simrel_common;
      vis  : f ∘₁ (C ∪₁ dom_rel (Gsb^? ;; <| I |>)) ⊆₁ vis S;
    }.
  
  Record forward_pair (e : actid) (e' : EventId.t) :=
    { fp_tcstep : trav_step G sc TC (mkTC (C ∪₁ eq e) I);
      fp_inGE   : GE e;
      fp_inSE   : SE e'; 
      fp_tidEq  : Stid e' = Gtid e;
      fp_labEq  : Slab e' = Glab e;
      fp_covsb  : Ssb ⨾ ⦗ eq e' ⦘ ⊆ ⦗ f ∘₁ C ⦘ ⨾ Ssb;
      fp_sbEq   : upd f e e' ∘ (Gsb ;; <| eq e |>) ≡ Ssb ;; <| eq e' |>;
      fp_imgrf  : upd f e e' ∘ (Grf ⨾ ⦗ eq e ⦘) ⊆ Srf;
    }.
End SimRel.

Lemma simstep_forward S G sc TC f e e'
      (SRC : simrel_common S G sc TC f)
      (FP  : forward_pair S G sc TC f e e') :
  exists f',
    simrel_common S G sc (mkTC (covered TC ∪₁ eq e) (issued TC)) f'.
Proof.
  exists (upd f e e').

  (* extract (NEXT e) and (COVERABLE e) from fp_tcstep *)
  edestruct fp_tcstep as [a ST]; eauto.
  red in ST. desf; simpls.
  2 : { exfalso. apply NISS. apply ISSEQ. by right. }
  destruct (classic (a = e)) as [|NEQ]; subst.
  2: { destruct COVEQ as [CC CC'].
       specialize (CC a).
       destruct (CC' a); auto; desf.
         by right. }

  assert (~ is_init e) as NINITE.
  { destruct SRC. destruct FP.
    intros HH. apply NEXT.
    eapply init_covered; eauto.
    desf. }

  assert (sb G ;; <| eq e |> ⊆ <| covered TC |> ;; sb G) as EPrclCOV.
  { admit. } 

  assert ((upd f e e') ∘₁ (covered TC) ≡₁ f ∘₁ (covered TC)) as FupdCOV.
  { by rewrite set_collect_updo. } 

  assert ((upd f e e') ∘₁ (issued TC) ≡₁ f ∘₁ (issued TC)) as FupdISS.
  { admit. } 
  
  assert (issued TC e -> f e = e') as NN.
  { admit. }

  assert (issued TC e -> upd f e e' = f) as YY.
  { intros II. apply NN in II.
    apply functional_extensionality.
    ins.
    destruct (classic (x = e)) as [|NEQ]; subst.
    { by rewrite upds. }
      by rewrite updo. }
  
  assert (((upd f e e') ∘₁ set_compl (covered TC ∪₁ eq e ∪₁ issued TC))
            ∩₁ S.(ES.acts_set) ≡₁ ∅)
    as FOTH.
  { split; [|basic_solver].
    destruct (classic (issued TC e)) as [ISS|NISS].
    { rewrite YY; auto.
      rewrite set_unionA.
      arewrite (eq e ∪₁ issued TC ≡₁ issued TC).
      2: by apply SRC.
      generalize ISS. basic_solver. }
    rewrite set_collect_updo.
    2: { intros HH. apply HH. basic_solver. }
    arewrite (set_compl (covered TC ∪₁ eq e ∪₁ issued TC) ⊆₁
              set_compl (covered TC ∪₁ issued TC)).
    2: by apply SRC.
    apply set_subset_compl. basic_solver. }

  assert (eq_dom (covered TC) (upd f e e') f) as FupdEQCOV.
  { admit. } 

  assert (eq_dom (issued TC) (upd f e e') f) as FupdEQISS.
  { admit. } 
  
  assert (forall a (COVa: covered TC a)
                 (Fimga: S.(ES.acts_set) (f a))
                 (tidEQ: EventId.same_tid (f a) e'),
       S.(ES.sb) (f a) e')
  as FCOVimgEsb.
  { ins.
    destruct FP. destruct SRC.
    assert (tid e = tid a) as Hsametid.
    { rewrite <- fp_tidEq0. 
      rewrite <- (tidEq0 a); auto. 
      autounfold with unfolderDb. auto. }
    assert (sb G a e) as GpoYE.
    { apply (same_thread G e a) in Hsametid; desf.
      autounfold with unfolderDb in Hsametid; desf.
      exfalso. apply NEXT. 
      assert (tc_coherent G sc TC) as TRCOH. 
      { admit. }
      apply (dom_sb_covered TRCOH).
      autounfold with unfolderDb.
      eexists. eexists. eauto. 
      admit. }
      (* apply finE0. auto. } *)
    unfold same_relation in fp_sbEq0. desf.
    repeat rewrite seq_eqv_r in fp_sbEq0.
    apply fp_sbEq0.
    unfold collect_rel. eexists. eexists. splits; eauto.
    apply upds. } 
  
  assert (inj_dom (covered TC ∪₁ eq e ∪₁ issued TC) (upd f e e'))
    as FINJ.
  { 
    (* destruct (classic (issued TC e)) as [ISS|NISS]. *)
    (* { admit. } *)
    (* red. ins. *)
    (* unfold set_union in *. desf. *)
    (* { admit. } *)
    (* { rewrite upds in *. *)
    (*   destruct (classic (x = y)) as [|NEQ]; auto. *)
    (*   rewrite updo in *; auto. *)

    (*   admit. } *)
    admit.
  }

  destruct FP.
  set (SRC' := SRC).
  destruct SRC'.
  
  constructor; ins.
  (* finE *)
  { admit. } 
  (* tidEq *)
  { admit. }
  (* labEq *)
  { unfold set_union in *.
    desf.
    { rewrite updo.
      { basic_solver. }
      intros HH. desf. }
    { by rewrite upds. }
    destruct (classic (e = e0)) as [|NEQ]; subst.
    { by rewrite upds. }
    rewrite updo; auto. }
  (* sbPrcl *)
  { rewrite set_collect_union.
    rewrite set_collect_updo; auto.
    rewrite set_collect_eq.
    rewrite upds.
    rewrite id_union.
    rewrite seq_union_r.
    rewrite seq_union_l.
    apply inclusion_union_l.
    { rewrite sbPrcl; eauto. by unionR left. } 
    by apply inclusion_union_r1_search. }
  (* sbF *)
  { repeat rewrite <- restr_relE.
    rewrite set_collect_union.
    repeat rewrite restr_set_union.
    rewrite set_collect_eq. rewrite upds.
    rewrite restr_irrefl_eq; [|by apply Execution.sb_irr].
    rewrite restr_irrefl_eq; [|by apply ES.sb_irr].
    arewrite_false (<| eq e |> ;; sb G ;; <| covered TC |>).
    { autounfold with unfolderDb. splits; ins; eauto. 
      destruct H as [z Hz]. desf.
      admit.
    }
    arewrite_false (<| eq e' |> ;; S.(ES.sb) ;; <| upd f e e' ∘₁ covered TC |>).
    { admit. }
    repeat rewrite union_false_r.
    rewrite collect_rel_union.

    apply union_more.
    { rewrite (collect_rel_restr_eq_dom (sb G) FupdEQCOV). 
      rewrite FupdCOV. 
      repeat rewrite restr_relE.
      apply sbF0. }
    { rewrite collect_rel_seq_l. 
      repeat rewrite set_collect_eqv.
      repeat rewrite FupdCOV.
      assert (upd f e e' ∘ (sb G) ;; <| eq e |> ≡ S.(ES.sb) ;; <| eq e' |> ) as FupdGsbE.
      { admit. } 
      rewrite FupdGsbE.
      reflexivity.
      (* inj_dom (s ∪ s') f => inj_dom s f *)
      admit. } }
  (* cimgNcf *)
  { split; [|basic_solver].
    rewrite set_collect_union.
    rewrite set_collect_eq. rewrite upds.
    rewrite set_collect_updo; auto.
    rewrite id_union.
    repeat rewrite seq_union_r.
    repeat rewrite seq_union_l.
    unionL.
    { apply SRC. }
    { autounfold with unfolderDb. 
      ins. desf. apply H7.
      right.
      apply FCOVimgEsb; auto.
      symmetry. auto. }
    {  autounfold with unfolderDb.
       ins. desf. apply H6.
       left. right.
       apply FCOVimgEsb; auto. }
    rewrite <- restr_relE. 
    erewrite restr_irrefl_eq.
    { basic_solver. }
    apply ES.cf_irr. }
  (* imgrf *)
  { rewrite set_collect_union.
    repeat rewrite id_union.
    repeat rewrite seq_union_r. 
    rewrite collect_rel_union.
    rewrite FupdCOV. 
    rewrite FupdISS. 
    apply union_more.
    { rewrite collect_rel_eq_dom; eauto. }
    rewrite set_collect_eq.
    rewrite upds.
    rewrite wf_rfD; [|admit].
    rewrite ES.rfD; [|admit].
    admit. }
  admit.
Admitted.

(* Lemma 2 from notes. *)
Lemma simstep_exists_forward execs S G TC f
      (SRC : simrel_common S G TC f) :
  exists e (e' : EventId.t) S' f',
    ⟪ EST : ESstep.t Weakestmo execs S S' ⟫ /\
    ⟪ SRC : simrel_common S' G (mkTC (covered TC ∪₁ eq e) (issued TC)) f' ⟫.
Proof. Admitted.

