From hahn Require Import Hahn.
From imm Require Import Events Execution TraversalConfig.
Require Import AuxRel EventStructure.

Section SimRel.
  Variable EG : ES.t.
  Variable G  : execution.
  Variable TC : trav_config.
  Variable s  : actid -> EventId.t.
  
  Notation "'C'" := (covered TC).
  Notation "'I'" := (issued TC).

  Record simrel_common :=
    { labEq : forall e (CI : (C ∪₁ I) e),
        EventId.lab e.(s) = G.(lab) e;
      sbPrcl : EG.(ES.sb) ;; <| s ∘₁ C |> ⊆ <| s ∘₁ C |> ;; EG.(ES.sb);
      (* sbS :  *)

      (* TODO. Probably, we need the following condition:
             s is injective on C ∪₁ I *)
    }.
End SimRel.