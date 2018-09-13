From hahn Require Import Hahn.
From imm Require Import Events Execution TraversalConfig.
Require Import AuxRel EventStructure.

Section SimRel.
  Variable S : ES.t.
  Variable G  : execution.
  Variable TC : trav_config.
  Variable f  : actid -> EventId.t.
  
  Notation "'C'" := (covered TC).
  Notation "'I'" := (issued TC).
  Notation "'Gsb'" := (G.(sb)).
  Notation "'Grf'" := (G.(rf)).
  Notation "'Gco'" := (G.(co)).
  Notation "'Ssb'" := (S.(ES.sb)).
  Notation "'Srf'" := (S.(ES.rf)).
  Notation "'Sco'" := (S.(ES.co)).
  Notation "'Scf'" := (S.(ES.cf)).

  (* TODO. Probably, we need the following condition:
             s is injective on C ∪₁ I
   *)
  Record simrel_common :=
    { labEq : forall e (CI : (C ∪₁ I) e),
        EventId.lab e.(f) = G.(lab) e;
      sbPrcl : Ssb ;; <| f ∘₁ C |> ⊆ <| f ∘₁ C |> ;; Ssb;
      sbF : f ∘ (<| C |> ;; Gsb ;; <| C |>) ≡
            <| f ∘₁ C |> ;; Ssb ;; <| f ∘₁ C |>;
      cimgNcf : <| f ∘₁ C |> ;; Scf ;; <| f ∘₁ C |> ≡ ∅₂;
      imgrf : f ∘ (<| I |> ;; Grf ;; <| C |>) ≡ Srf;
      imgco : f ∘ (<| I |> ;; Gco ;; <| I |>) ⊆ Sco;
    }.
End SimRel.