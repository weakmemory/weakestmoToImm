From hahn Require Import Hahn.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecutionProperties.
Require Import AuxRel AuxDef EventStructure Construction Consistency.
Require Import Coq.Logic.FunctionalExtensionality Classical_Prop.

Set Implicit Arguments.

Section SimRelAlt.
  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G  : execution.
  Variable GPROG : program_execution prog G.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable f  : actid -> EventId.t.

  Notation "'SE'" := S.(ES.acts_set).
  Notation "'GE'" := G.(acts_set).
  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gsb'" := (G.(sb)).
  Notation "'Grf'" := (G.(rf)).
  Notation "'Gco'" := (G.(co)).
  Notation "'Slab'" := (EventId.lab).
  Notation "'Ssb'" := (S.(ES.sb)).
  Notation "'Srf'" := (S.(ES.rf)).
  Notation "'Sco'" := (S.(ES.co)).
  Notation "'Scf'" := (S.(ES.cf)).
  Notation "'Gtid_' t" := (fun x => tid x = t) (at level 1).
  Notation "'Stid_' t" := (fun x => EventId.tid x = t) (at level 1).

  Definition pc thread :=
    f ∘₁ C ∩₁ Stid_ thread \₁ dom_rel (Ssb ;; <| f ∘₁ C |>).

  Record simrel (P : thread_id -> Prop) :=
    { gwf   : Execution.Wf G;
      gprclos : forall thread m n (LT : m < n)
                       (EE : GE (ThreadEvent thread n)),
          GE (ThreadEvent thread m);
      tccoh : tc_coherent G sc TC;
      swf   : ES.Wf S;
      scons : es_consistent S Weakestmo;

      finj : inj_dom (C ∪₁ I) f;  
      fimg : f ∘₁ (C ∪₁ I) ⊆₁ SE;
      foth : (f ∘₁ set_compl (C ∪₁ I)) ∩₁ SE ≡₁ ∅;
      flab : forall e (CI : (C ∪₁ I) e),
        Slab e.(f) = Glab e;
      ftid : forall e, EventId.tid (f e) = tid e;
      fdef : forall e (COV : C e),
          f e = act_to_event G e;
      finitIncl : S.(ES.acts_init_set) ⊆₁ f ∘₁ (is_init ∩₁ GE);
      
      sbtot_cov : forall thread,
          is_total (f ∘₁ C ∩₁ Stid_ thread) Ssb;

      sbtot_ci : forall thread (NP : ~ P thread),
          is_total (f ∘₁ (C ∪₁ I) ∩₁ Stid_ thread) Ssb;
      
      (* sbF : f ∘ ⦗ C ⦘ ⨾ Gsb ⨾ ⦗ C ⦘ ≡ *)
      (*       ⦗ f ∘₁ C ⦘ ⨾ Ssb ⨾ ⦗ f ∘₁ C ⦘; *)
      (* cimgNcf : ⦗ f ∘₁ C ⦘ ⨾ Scf ⨾ ⦗ f ∘₁ C ⦘ ≡ ∅₂; *)
      (* imgrf : f ∘ ⦗ I ⦘ ⨾ Grf ⨾ ⦗ C ⦘ ≡ *)
      (*         ⦗ f ∘₁ I ⦘ ⨾ Srf  ⨾ ⦗ f ∘₁ C ⦘; *)
      (* imgco : f ∘ ⦗ I ⦘ ⨾ Gco ⨾ ⦗ I ⦘ ⊆ *)
      (*         ⦗ f ∘₁ I ⦘ ⨾ Sco  ⨾ ⦗ f ∘₁ I ⦘; *)
    }.

  Section SRCprop.
    Variable P : thread_id -> Prop.
    Variable SRC : simrel P.
    
    Lemma finit : S.(ES.acts_init_set) ≡₁ f ∘₁ (is_init ∩₁ GE).
    Proof.
      set (SRC' := SRC).
      destruct SRC'.
      split; [eapply finitIncl; eauto|].
      unfold ES.acts_init_set.
      apply set_subset_inter_r; split.
      { rewrite init_covered; eauto.
          by arewrite (C ⊆₁ C ∪₁ I). }
      unfold is_init.
      intros x [y [[AA CC] BB]]; desf.
      rewrite SRC.(fdef).
      2: { eapply init_covered; eauto. by split. }
      simpls.
      constructor; auto.
      eexists. simpls.
      rewrite wf_init_lab; auto.
    Qed.

    Lemma finitC : S.(ES.acts_init_set) ⊆₁ f ∘₁ C.
    Proof. rewrite finit. erewrite init_covered; eauto. apply SRC. Qed.

    Lemma sbPrcl : Ssb ⨾ ⦗ f ∘₁ C ⦘ ⊆ ⦗ f ∘₁ C ⦘ ⨾ Ssb.
    Proof.
      arewrite (Ssb ⊆ <| f ∘₁ C ∪₁ set_compl (f ∘₁ C) |> ;; Ssb) at 1.
      { arewrite (f ∘₁ C ∪₁ set_compl (f ∘₁ C) ≡₁ fun _ => True).
        2: by relsf.
        split; [basic_solver|].
        intros x _. apply classic. }
      rewrite id_union. rewrite seq_union_l.
      arewrite_false (⦗set_compl (f ∘₁ C)⦘ ⨾ Ssb ⨾ ⦗f ∘₁ C⦘).
      2: { arewrite_id ⦗f ∘₁ C⦘ at 2. relsf. }
      unfold ES.sb.
      rewrite seq_union_l. rewrite seq_union_r.
      rewrite seq_eqv_cross.
      rewrite finitC.
      rewrite set_compl_inter_id.
      rewrite cross_false_l.
      apply inclusion_union_l; [done|].
      red. intros x y HH.
      destruct_seq HH as [XX YY].
      destruct YY as [z [COVZ ZZ]]; subst.
      erewrite fdef in *; eauto.
      apply XX.
      apply seq_eqv_r in HH. destruct HH as [HH SEE].
      assert (dom_rel (EventId.ext_sb ⨾ ⦗eq (act_to_event G z)⦘) x) as AA.
      { eexists. apply seq_eqv_r. eauto. }
      apply act_to_event_ext_sb_dom in AA.
      desf. desf.
      assert (C (ThreadEvent thread m)) as MM.
      2: { red. eexists. by split; [|eapply fdef; eauto]. }
      destruct SRC.
      eapply dom_sb_covered; eauto.
      eexists. apply seq_eqv_r. split; eauto.
      assert (GE (ThreadEvent thread index)) as EE.
      { eapply coveredE; eauto. }
      red. apply seq_eqv_l. split.
      { eapply SRC.(gprclos); eauto. }
      apply seq_eqv_r. splits; auto.
      red. by splits.
    Qed.
  End SRCprop.
  
  (* TODO: Continue from here *)

  Record simrel :=
    { comm : simrel_common;
      vis  : f ∘₁ (C ∪₁ dom_rel (Gsb^? ;; <| I |>)) ⊆₁ vis S;
    }.
  
  Record forward_pair (e : actid) (e' : EventId.t) :=
    { fp_tcstep : trav_step G sc TC (mkTC (C ∪₁ eq e) I);
      fp_labEq : Slab e' = Glab e;
      fp_covsb : Ssb ⨾ ⦗ eq e' ⦘ ⊆ ⦗ f ∘₁ C ⦘ ⨾ Ssb; 
      fp_imgrf : upd f e e' ∘ (Grf ⨾ ⦗ eq e ⦘) ⊆ Srf;
    }.
End SimRel.

Lemma simstep_forward S G sc TC f e e'
      (SRC : simrel_common S G TC f)
      (FP  : forward_pair S G sc TC f e e') :
  exists f',
    simrel_common S G (mkTC (covered TC ∪₁ eq e) (issued TC)) f'.
Proof.
  assert (~ covered TC e) as NCOV.
  { intros COV.
    edestruct fp_tcstep as [a ST]; eauto.
    red in ST. desf; simpls.
    { assert ((covered TC ∪₁ eq e) a ) as HH.
      { apply COVEQ. by right. }
      unfold set_union in *. desf. }
    apply NISS. apply ISSEQ. by right. }

  assert ((upd f e e') ∘₁ (covered TC) ≡₁ f ∘₁ (covered TC)) as FupdCOV.
  { by rewrite set_collect_updo. } 
  
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

  exists (upd f e e').
  constructor; ins.
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
    rewrite restr_irrefl_eq; [|by apply sb_irr].
    arewrite_false (<| eq e |> ;; sb G ;; <| covered TC |>).
    { autounfold with unfolderDb. splits; ins; eauto. 
      destruct H as [z Hz]. desf.
      admit.
    }
    arewrite_false (<| eq e' |> ;; S.(ES.sb) ;; <| upd f e e' ∘₁ covered TC |>).
    { admit. }
    repeat rewrite union_false_r.
    rewrite collect_rel_union.
    assert (eq_dom (covered TC) (upd f e e') f) as FupdEQCOV.
    { admit. } 
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
      ins. destruct H. desf.
      apply H7.
      right.
      admit. 
    }
    3: { autounfold with unfolderDb.
         ins. desf. apply H3.
         basic_solver. }
    all: admit. }
  { admit. }
Admitted.


(* Lemma 2 from notes. *)
Lemma simstep_exists_forward execs S G TC f
      (SRC : simrel_common S G TC f) :
  exists e (e' : EventId.t) S' f',
    ⟪ EST : ESstep.t Weakestmo execs S S' ⟫ /\
    ⟪ SRC : simrel_common S' G (mkTC (covered TC ∪₁ eq e) (issued TC)) f' ⟫.
Proof. Admitted.

End SimRelAlt.
