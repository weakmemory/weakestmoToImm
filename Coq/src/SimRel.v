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

  Record simrel_common :=
    { labEq : forall e (CI : (C ∪₁ I) e),
        EventId.lab e.(f) = G.(lab) e;
      sbPrcl : S.(ES.sb) ;; <| f ∘₁ C |> ⊆ <| f ∘₁ C |> ;; S.(ES.sb);
      sbF : f ∘ (<| C |> ;; G.(sb) ;; <| C |>) ≡
              <| f ∘₁ C |> ;; S.(ES.sb) ;; <| f ∘₁ C |>;
      cimgNcf : <| f ∘₁ C |> ;; S.(ES.cf) ;; <| f ∘₁ C |> ≡ ∅₂;


      (* TODO. Probably, we need the following condition:
             s is injective on C ∪₁ I *)
    }.
End SimRel.