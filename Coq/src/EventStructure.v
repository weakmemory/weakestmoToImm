From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events.
Require Import AuxRel.

Definition eventid := nat.

Module Language.
Record t :=
  mk { syntax : Type;
       state : Type;
       init : syntax -> state;
       is_terminal : state -> Prop;
       step : list label -> state -> state -> Prop
     }.
End Language.

Module Continuation.
Record t :=
  { lang     : Language.t;
    state    : lang.(Language.state);
    thread   : thread_id;
    prev_act : option eventid;
  }.
End Continuation.

Record event_structure :=
  { acts : list eventid;
    acts_init : list eventid;
    next_act : eventid;
    tid  : eventid -> thread_id;
    lab  : eventid -> label;
    sb   : eventid -> eventid -> Prop ;
    rmw  : eventid -> eventid -> Prop ;
    rf : eventid -> eventid -> Prop ;
    co : eventid -> eventid -> Prop ;
    ew : eventid -> eventid -> Prop ;
    cons : list Continuation.t;
  }.

Section EventStructure.

Variable ES : event_structure.

Definition acts_set := fun x => In x ES.(acts).
Definition acts_init_set := fun x => In x ES.(acts_init).
Definition cons_set := fun x => In x ES.(cons).

Notation "'E'" := acts_set.
Notation "'Einit'" := acts_init_set.
Notation "'K'" := cons_set.
Notation "'next_act'" := ES.(next_act).
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

Definition cf := (sb⁻¹ ;; <| Einit |> ;; sb) \ sb ⁼.

Hint Unfold cf : unfolderDb. 

Lemma cf_irr : irreflexive cf.
Proof. basic_solver. Qed.

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

    cons_prev_ninit : forall c (CC : K c) e (PA : c.(Continuation.prev_act) = Some e),
        ~ Einit e;
    cons_prevE : forall c (CC : K c) e (PA : c.(Continuation.prev_act) = Some e), E e;

    cons_uniq_prev : forall c c' (CC : K c) (CC' : K c') e
                            (PA : c.(Continuation.prev_act) = Some e),
        c = c' \/
        c.(Continuation.prev_act) <> c'.(Continuation.prev_act);
    cons_uniq_tid : forall c c' (CC : K c) (CC' : K c')
                            (PA  : c .(Continuation.prev_act) = None)
                            (PA' : c'.(Continuation.prev_act) = None),
        c = c' \/
        c.(Continuation.thread) <> c'.(Continuation.thread);
  }.

Implicit Type WF : Wf.

Lemma ew_irr WF : irreflexive ew.
Proof. generalize cf_irr (ewc WF). basic_solver. Qed.

End EventStructure.