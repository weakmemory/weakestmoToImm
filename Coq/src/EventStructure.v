From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events.
Require Import AuxRel.

Definition compl_rel {A} (r : relation A) := fun a b => ~ r a b.

Module EventId.
Record t :=
  mk {
      thread : thread_id;
      lbl    : label;
      prefix : list label;
    }.
Definition path e := e.(lbl) :: e.(prefix).

Definition ext_sb (a b : EventId.t) : Prop :=
  exists l, b.(path) = l ++ a.(path).

Definition ext_cf :=
   compl_rel ext_sb ∩ compl_rel ext_sb⁻¹.
End EventId.

Module Language.
Record t :=
  mk { syntax : Type;
       state : Type;
       init : syntax -> state;
       is_terminal : state -> Prop;
       step : list label -> state -> state -> Prop
     }.
End Language.

Module ES.
Record t :=
  mk { acts : list EventId.t;
       acts_init : list EventId.t;
       next_act : EventId.t;
       tid  : EventId.t -> thread_id;
       rmw  : EventId.t -> EventId.t -> Prop ;
       rf : EventId.t -> EventId.t -> Prop ;
       co : EventId.t -> EventId.t -> Prop ;
       ew : EventId.t -> EventId.t -> Prop ;
     }.

Definition acts_set ES := fun x => In x ES.(acts).
Definition acts_init_set ES := fun x => In x ES.(acts_init).
End ES.

(* Module Continuation. *)
(* Record t := *)
(*   mk { lang     : Language.t; *)
(*        state    : lang.(Language.state); *)
(*        thread   : thread_id; (* replace with one field of type "thread_id + eventid" "*) *)
(*        prev_act : option EventId.t; *)
(*      }. *)
(* End Continuation. *)

Section EventStructure.

Variable EG : ES.t.

Notation "'Einit'" := EG.(ES.acts_init_set).
(* Notation "'next_act'" := EG.(next_act). *)
Notation "'lab'" := EG.(lab).
Notation "'sb'" := EG.(sb).
Notation "'rmw'" := EG.(rmw).
Notation "'ew'" := EG.(ew).
Notation "'rf'" := EG.(rf).
Notation "'co'" := EG.(co).

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


Record Wf :=
  { initD : Einit ⊆₁ E;
    init_lab : forall e (INIT : Einit e), exists l, lab e = Astore Xpln Opln l 0 ;
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
    next_act_lt : forall e (EE : E e), lt e next_act;

    conts_prev_ninit : forall c (CC : K c) e (PA : c.(Continuation.prev_act) = Some e),
        ~ Einit e;
    conts_prevE : forall c (CC : K c) e (PA : c.(Continuation.prev_act) = Some e), E e;

    conts_uniq_prev : forall c c' (CC : K c) (CC' : K c') e
                            (PA : c.(Continuation.prev_act) = Some e),
        c = c' \/
        c.(Continuation.prev_act) <> c'.(Continuation.prev_act);
    conts_uniq_tid : forall c c' (CC : K c) (CC' : K c')
                            (PA  : c .(Continuation.prev_act) = None)
                            (PA' : c'.(Continuation.prev_act) = None),
        c = c' \/
        c.(Continuation.thread) <> c'.(Continuation.thread);
    conts_exists : forall e (EE : E e) (NINIT : ~ Einit e),
        exists c,
          << CC : K c >> /\
          << PA : c.(Continuation.prev_act) = Some e >>;
  }.

Implicit Type WF : Wf.

Lemma ew_irr WF : irreflexive ew.
Proof. generalize cf_irr (ewc WF). basic_solver. Qed.

End EventStructure.