From hahn Require Import Hahn.
From imm Require Import Events Execution TraversalConfig Traversal.
Require Import AuxRel EventStructure.

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
  
  (* TODO. Probably, add condition F.2. *) 
  Record forward_pair (e : actid) (e' : EventId.t) :=
    { fp_tcstep : trav_step G sc TC (mkTC (C ∪₁ eq e) I);
      fp_labEq : Slab e' = Glab e;
      fp_imgrf : upd f e e' ∘ (Grf ;; <| eq e |>) ⊆ Srf;
    }.
End SimRel.