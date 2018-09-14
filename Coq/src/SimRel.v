From hahn Require Import Hahn.
From imm Require Import Events Execution TraversalConfig Traversal.
Require Import AuxDef AuxRel EventStructure.

Section SimRel.
  Variable S : ES.t.
  Variable G  : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable f  : actid -> EventId.t.

  Notation "'C'" := (covered TC).
  Notation "'I'" := (issued TC).
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gsb'" := (G.(sb)).
  Notation "'Grf'" := (G.(rf)).
  Notation "'Gco'" := (G.(co)).
  Notation "'Slab'" := (EventId.lab).
  Notation "'Ssb'" := (S.(ES.sb)).
  Notation "'Srf'" := (S.(ES.rf)).
  Notation "'Sco'" := (S.(ES.co)).
  Notation "'Scf'" := (S.(ES.cf)).

  (* TODO. Probably, we need the following condition:
             s is injective on C ∪₁ I
   *)
  Record simrel_common :=
    { labEq : forall e (CI : (C ∪₁ I) e),
        Slab e.(f) = Glab e;
      sbPrcl : Ssb ;; <| f ∘₁ C |> ⊆ <| f ∘₁ C |> ;; Ssb;
      sbF : f ∘ (<| C |> ;; Gsb ;; <| C |>) ≡
            <| f ∘₁ C |> ;; Ssb ;; <| f ∘₁ C |>;
      cimgNcf : <| f ∘₁ C |> ;; Scf ;; <| f ∘₁ C |> ≡ ∅₂;
      imgrf : f ∘ (<| I |> ;; Grf ;; <| C |>) ≡
              <| f ∘₁ I |> ;; Srf  ;; <| f ∘₁ C |>;
      imgco : f ∘ (<| I |> ;; Gco ;; <| I |>) ⊆
              <| f ∘₁ I |> ;; Sco  ;; <| f ∘₁ I |>;
    }.
  
  Record forward_pair (e : actid) (e' : EventId.t) :=
    { fp_tcstep : trav_step G sc TC (mkTC (C ∪₁ eq e) I);
      fp_labEq : Slab e' = Glab e;
      fp_covsb : Ssb ;; <| eq e' |> ⊆ (f ∘ <| C |>) ;; Ssb; 
      fp_imgrf : upd f e e' ∘ (Grf ;; <| eq e |>) ⊆ Srf;
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
  { admit. } 

  destruct FP.
  set (SRC' := SRC).
  destruct SRC'.
  exists (upd f e e').
  constructor; ins.
  (* labEq *)
  { unfold set_union in *.
    desf.
    { rewrite updo.
      2: { intros HH. desf. }
      basic_solver. }
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
    apply inclusion_union_r1_search.
    rewrite <- set_collect_eqv.
    apply fp_covsb0. }
  (* sbF *)
  { repeat rewrite collect_rel_seq.
    {
      repeat rewrite set_collect_eqv.
      repeat rewrite set_collect_union.
      repeat rewrite eqv_rel_union.
      repeat rewrite seq_union_l.
      repeat rewrite seq_union_r.
      split.
      { unionL.
        { apply inclusion_union_r. left. apply inclusion_union_r. left.
          repeat rewrite <- set_collect_eqv.   
          repeat rewrite <- collect_rel_seq.
          
          rewrite <- (set_collect_restr G.(sb) FupdCOV).
          rewrite <- restr_relE.
          assert (H: set_collect_restr FupdCOV). as Hh. 
          rewrite <- (set_collect_restr FupdCOV).
        }
      }
    }
  }
  { }
    admit. }
  { admit. }
  { split; [|basic_solver].
    rewrite set_collect_union.
    rewrite set_collect_eq. rewrite upds.
    rewrite set_collect_updo; auto.
    rewrite id_union.
    repeat rewrite seq_union_r.
    repeat rewrite seq_union_l.
    unionL.
    { apply SRC. }
    3: { autounfold with unfolderDb.
         ins. desf. apply H3.
         basic_solver. }
    all: admit. }
  { admit. }
 
Admitted.
