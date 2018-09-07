From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events.
Require Import AuxRel EventStructure.

Inductive model := weakest | weakestmo.

Section Consistency.

Variable ES : event_structure.

Definition acts_set := fun x => In x ES.(acts).
Definition acts_init_set := fun x => In x ES.(acts_init).

Notation "'E'" := acts_set.
Notation "'E_init'" := acts_init_set.
Notation "'lab'" := ES.(lab).
Notation "'sb'" := ES.(sb).
Notation "'rmw'" := ES.(rmw).
Notation "'ew'" := ES.(ew).
Notation "'rf'" := ES.(rf).
Notation "'co'" := ES.(co).
Notation "'cf'" := ES.(cf).

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
  codom_rel (cf ∩ (sb ∪ rf)⁺ ∩ (ew ;; sb ⁼)).

Definition hb : relation eventid := fun x y => True. (* TODO: define *)
Definition eco (m : model) : relation eventid := fun x y => True. (* TODO: define *)

Record es_consistent m :=
  { visC : rf ⊆ sb ∪ vis × E;
    cfC  : rf ∩ cf ≡ ∅₂;
    hbC  : (hb ;; rf⁻¹) ∩ cf ≡ ∅₂;
    cohC : irreflexive (hb ;; eco m);
  }.

End Consistency.