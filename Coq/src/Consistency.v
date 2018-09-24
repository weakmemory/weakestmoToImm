From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events.
Require Import AuxRel EventStructure.

Inductive model := Weakest | Weakestmo.

Section Consistency.

Variable S : ES.t.

Notation "'E'" := S.(ES.acts_set).
Notation "'E_init'" := S.(ES.acts_init_set).
Notation "'lab'" := S.(ES.lab).
Notation "'sb'" := S.(ES.sb).
Notation "'rmw'" := S.(ES.rmw).
Notation "'ew'" := S.(ES.ew).
Notation "'jf'" := S.(ES.jf).
Notation "'rf'" := S.(ES.rf).
Notation "'co'" := S.(ES.co).
Notation "'cf'" := S.(ES.cf).

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
  codom_rel (cf ∩ (sb ∪ jf)⁺ ∩ (ew ⨾ sb ⁼)).

Definition sw : relation event_id := fun x y => True. (* TODO: define *)

Definition hb : relation event_id := (sb ∪ sw)⁺.

Definition co_strong : relation event_id :=
  ⦗ W ⦘ ⨾ hb ⨾ ⦗ W ⦘ ∩ same_loc.

Definition mco (m : model) : relation event_id :=
  match m with
  | Weakest   => co_strong 
  | Weakestmo => co
  end.

Definition fr : relation event_id := rf⁻¹ ⨾ co \ cf^?.

Definition mfr (m : model) : relation event_id :=
  (rf⁻¹ ⨾ mco m) \ cf^?.

Definition eco (m : model) : relation event_id :=
  (rf ∪ (mco m) ∪ (mfr m))⁺.

Record es_consistent m :=
  { esc_vis : jf ⊆ sb ∪ vis × E;
    esc_hb  : (hb ⨾ jf⁻¹) ∩ cf ≡ ∅₂;
    esc_coh : irreflexive (hb ⨾ (eco m)^?);
  }.

End Consistency.