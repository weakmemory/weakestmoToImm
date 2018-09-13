From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events.
Require Import AuxRel EventStructure.

Inductive model := weakest | weakestmo.

Section Consistency.

Variable S : ES.t.

Notation "'E'" := S.(ES.acts_set).
Notation "'E_init'" := S.(ES.acts_init_set).
Notation "'lab'" := EventId.lab.
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
  codom_rel (cf ∩ (sb ∪ jf)⁺ ∩ (ew ;; sb ⁼)).

Definition sw : relation EventId.t := fun x y => True. (* TODO: define *)

Definition hb : relation EventId.t := (sb ∪ sw)⁺.

Definition co_strong : relation EventId.t :=
  <| W |> ;; hb ;; <| W |> ∩ same_loc.

Definition mco (m : model) : relation EventId.t :=
  match m with
  | weakest   => co
  | weakestmo => co_strong 
  end.

Definition fr : relation EventId.t := rf⁻¹ ;; co \ cf^?.

Definition mfr (m : model) : relation EventId.t :=
  (rf⁻¹ ;; mco m) \ cf^?.

Definition eco (m : model) : relation EventId.t :=
  (rf ∪ (mco m) ∪ (mfr m))⁺.

Record es_consistent m :=
  { esc_vis : jf ⊆ sb ∪ vis × E;
    esc_cf  : jf ∩ cf ≡ ∅₂;
    esc_hb  : (hb ;; jf⁻¹) ∩ cf ≡ ∅₂;
    esc_coh : irreflexive (hb ;; (eco m)^?);
  }.

End Consistency.