From hahn Require Import Hahn.
From imm Require Import Execution Events.
Require Import EventStructure.
Require Import Consistency.
Require Import AuxRel.

Section Extraction.

Variable G : execution.
Variable S : ES.t.

Notation "'SE'" := S.(ES.acts_set).
Notation "'Slab'" := EventId.lab.
Notation "'Ssb'" := S.(ES.sb).
Notation "'Srmw'" := S.(ES.rmw).
Notation "'Sew'" := S.(ES.ew).
Notation "'Srf'" := S.(ES.rf).
Notation "'Sco'" := S.(ES.co).
Notation "'Scf'" := S.(ES.cf).

Notation "'GE'" := G.(acts_set).
Notation "'Glab'" := G.(lab).
Notation "'Gsb'" := G.(sb).
Notation "'Grf'" := G.(rf).
Notation "'Gco'" := G.(co).
Notation "'Grmw'" := G.(rmw).
Notation "'Gdata'" := G.(data).
Notation "'Gaddr'" := G.(addr).
Notation "'Gctrl'" := G.(ctrl).


Definition extracted : Prop :=
  exists f : actid -> EventId.t, 
    << EVIS    : f ∘₁ GE ⊆₁ vis S >> /\
    << ENCF    : <| f ∘₁ GE |> ;; Scf ;; <| f ∘₁ GE |> ≡ ∅₂ >> /\
    << ESBPRCL : Ssb ;; <| f ∘₁ GE |> ⊆ f ∘ (GE × GE) >> /\
    << ESBMAX  : 
      <| f ∘₁ GE |> ;; Ssb ;; <| SE \₁ (f ∘₁ GE) |> ⊆ <| f ∘₁ GE |> ;; Ssb ;; <| f ∘₁ GE |> ;; Scf 
    >> /\
    << ESB     : f ∘ Gsb  ≡ <| f ∘₁ GE |> ;; Ssb  ;; <| f ∘₁ GE |> >> /\
    << ERMW    : f ∘ Grmw ≡ <| f ∘₁ GE |> ;; Srmw ;; <| f ∘₁ GE |> >> /\
    << ERF     : f ∘ Grf  ≡ <| f ∘₁ GE |> ;; Srf  ;; <| f ∘₁ GE |> >> /\                          
    << ECO     : f ∘ Gco  ≡ <| f ∘₁ GE |> ;; Sco  ;; <| f ∘₁ GE |> >>.              
  
End Extraction.