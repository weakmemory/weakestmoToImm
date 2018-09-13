Require Import Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events.
Require Import AuxRel.

Export ListNotations.

Definition compl_rel {A} (r : relation A) := fun a b => ~ r a b.

Module EventId.
Record t :=
  mk {
      tid    : thread_id;
      lab    : label;
      prefix : list label;
    }.
Definition path e := e.(lab) :: e.(prefix).

Definition ext_sb (a b : EventId.t) : Prop :=
  exists hd tl,
    b.(path) = (hd :: tl) ++ a.(path).

Definition init_tid := xH.

Record init (e : EventId.t) :=
  { itid : e.(tid) = init_tid ;
    ilab : exists l, e.(lab) = Astore Xpln Opln l 0;
    ipre : e.(prefix) = [];
  }.
End EventId.

Hint Unfold EventId.path EventId.ext_sb
     EventId.init_tid : unfolderDb.

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
       rmw  : EventId.t -> EventId.t -> Prop ;
       rf : EventId.t -> EventId.t -> Prop ;
       co : EventId.t -> EventId.t -> Prop ;
       ew : EventId.t -> EventId.t -> Prop ;
     }.

Definition acts_set ES := fun x => In x ES.(acts).
Definition acts_init_set  ES := ES.(acts_set) ∩₁ EventId.init.
Definition acts_ninit_set ES := ES.(acts_set) \₁ EventId.init.

Definition sb ES := ES.(acts_init_set) × ES.(acts_ninit_set) ∪
                    EventId.ext_sb ;; <| ES.(acts_set) |>.
Definition cf ES := <| ES.(acts_set) |> ;;
                    compl_rel (ES.(sb)^? ∪ ES.(sb)⁻¹) ;;
                    <| ES.(acts_set) |>.
End ES.

Hint Unfold ES.acts_set ES.acts_init_set ES.acts_ninit_set
     ES.sb ES.cf : unfolderDb.

Section EventStructure.

Variable EG : ES.t.

Notation "'E'"     := EG.(ES.acts_set).
Notation "'Einit'" := EG.(ES.acts_init_set).
Notation "'sb'" := EG.(ES.sb).
Notation "'rmw'" := EG.(ES.rmw).
Notation "'ew'" := EG.(ES.ew).
Notation "'rf'" := EG.(ES.rf).
Notation "'co'" := EG.(ES.co).
Notation "'lab'" := EventId.lab.
Notation "'cf'" := EG.(ES.cf).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
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
  { init_tidI : forall e (EE : E e) (ITID : e.(EventId.tid) = EventId.init_tid),
      Einit e;
    initL : forall l, (exists b, E b /\ loc b = Some l) ->
                      exists a, Einit a /\ loc a = Some l ;
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
    co_total :
      forall ol ws (WS : ws ⊆₁ E ∩₁ W ∩₁ (fun x => loc x = ol))
             (NCF : <| ws |> ;; cf ;; <| ws |> ≡ ∅₂),
        is_total ws co;
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

Lemma sb_irr : irreflexive sb.
Proof.
  repeat autounfold with unfolderDb.
  ins. desf.
  generalize H. clear H.
  set (ll := EventId.prefix x).
  intros HH.
  assert (length ll = length tl + 1 + length ll) as LL.
  2: omega.
  rewrite HH at 1. rewrite length_app. simpls. omega.
Qed.

Lemma cf_irr : irreflexive cf.
Proof. basic_solver. Qed.

Lemma ew_irr WF : irreflexive ew.
Proof. generalize cf_irr (ewc WF). basic_solver. Qed.

End EventStructure.