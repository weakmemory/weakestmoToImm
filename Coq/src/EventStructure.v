From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events.
Require Import AuxRel.

Definition eventid := Ident.t.

(** Definition of an execution *)
Record event_structure :=
  { acts : list eventid;
    acts_init : list eventid;
    tid  : eventid -> thread_id;
    lab  : eventid -> label;
    sb   : eventid -> eventid -> Prop ;
    rmw  : eventid -> eventid -> Prop ;
    rf : eventid -> eventid -> Prop ;
    co : eventid -> eventid -> Prop ;
    ew : eventid -> eventid -> Prop ;
  }.

Section EventStructure.

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

Definition cf := (sb⁻¹ ;; <| E_init |> ;; sb) \ sb ⁼.

Hint Unfold cf : unfolderDb. 

Lemma cf_irr : irreflexive cf.
Proof. basic_solver. Qed.

Record Wf :=
  { initD : E_init ⊆₁ E;
    init_lab : forall e (INIT : E_init e), exists l, lab e = Astore Xpln Opln l 0 ;
    sbE : sb ≡ ⦗E⦘ ⨾ sb ⨾ ⦗E⦘ ;
    rmwD : rmw ≡ ⦗R⦘ ⨾ rmw ⨾ ⦗W⦘ ;
    rmwl : rmw ⊆ same_loc ;
    rmwi : rmw ⊆ immediate sb ;
    rfE : rf ≡ ⦗E⦘ ⨾ rf ⨾ ⦗E⦘ ;
    rfD : rf ≡ ⦗W⦘ ⨾ rf ⨾ ⦗R⦘ ;
    rfl : rf ⊆ same_loc ;
    rfv : funeq val rf ;
    rff : functional rf⁻¹ ;
    coE : co ≡ ⦗E⦘ ⨾ co ⨾ ⦗E⦘ ;
    coD : co ≡ ⦗W⦘ ⨾ co ⨾ ⦗W⦘ ;
    col : co ⊆ same_loc ;
    co_trans : transitive co ;
    co_total : forall ol, is_total (E ∩₁ W ∩₁ (fun x => loc x = ol)) co ;
    co_irr : irreflexive co ;
    ewE : ew ≡ ⦗E⦘ ⨾ ew ⨾ ⦗E⦘ ;
    ewD : ew ≡ ⦗W⦘ ⨾ ew ⨾ ⦗R⦘ ;
    ewl : ew ⊆ same_loc ;
    ewv : funeq val ew ;
    ewc : ew ⊆ cf ;
    ew_trans : transitive ew ;
    ew_sym : symmetric ew ;
  }.

Implicit Type WF : Wf.

Lemma ew_irr WF : irreflexive ew.
Proof. generalize cf_irr (ewc WF). basic_solver. Qed.

End EventStructure.