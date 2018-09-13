From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events.
Require Import AuxRel EventStructure.

Inductive model := weakest | weakestmo.

Section Consistency.

Variable EG : ES.t.

Notation "'E'" := EG.(ES.acts_set).
Notation "'E_init'" := EG.(ES.acts_init_set).
Notation "'lab'" := EventId.lab.
Notation "'sb'" := EG.(ES.sb).
Notation "'rmw'" := EG.(ES.rmw).
Notation "'ew'" := EG.(ES.ew).
Notation "'jf'" := EG.(ES.jf).
Notation "'rf'" := EG.(ES.rf).
Notation "'co'" := EG.(ES.co).
Notation "'cf'" := EG.(ES.cf).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).

Notation "'Pln'" := (is_only_pln lab).
Notation "'Rlx'" := (is_rlx lab).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).
Notation "'Sc'" := (is_sc lab).

Definition vis :=
  codom_rel (cf ∩ (sb ∪ jf)⁺ ∩ (ew ;; sb ⁼)).

Definition hb : relation EventId.t := fun x y => True. (* TODO: define *)
Definition eco (m : model) : relation EventId.t := fun x y => True. (* TODO: define *)

Record es_consistent m :=
  { visC : jf ⊆ sb ∪ vis × E;
    cfC  : jf ∩ cf ≡ ∅₂;
    hbC  : (hb ;; jf⁻¹) ∩ cf ≡ ∅₂;
    cohC : irreflexive (hb ;; eco m);
  }.

End Consistency.