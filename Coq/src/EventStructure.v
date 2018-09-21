Require Import Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events.
Require Import AuxRel.

Set Implicit Arguments.
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
  << STID : tid a = tid b >> /\
  << REPR : exists hd tl,
      b.(path) = (hd :: tl) ++ a.(path) >>.

Definition init_tid := xH.

Record init (e : EventId.t) :=
  { itid : e.(tid) = init_tid ;
    ilab : exists l, e.(lab) = Astore Xpln Opln l 0;
    ipre : e.(prefix) = [];
  }.

Definition same_tid := fun x y => tid x = tid y.

Lemma ext_sb_trans : transitive ext_sb.
Proof.
  red. unfold ext_sb.
  ins; desf.
  splits.
  { etransitivity; eauto. }
  rewrite REPR0 in REPR.
  rewrite REPR.
  exists hd. exists (tl ++ hd0 :: tl0).
    by rewrite <- app_assoc.
Qed.
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
       jf : EventId.t -> EventId.t -> Prop ;
       co : EventId.t -> EventId.t -> Prop ;
       ew : EventId.t -> EventId.t -> Prop ;
     }.

Definition acts_set ES := fun x => In x ES.(acts).
Definition acts_init_set  ES := ES.(acts_set) ∩₁ EventId.init.
Definition acts_ninit_set ES := ES.(acts_set) \₁ EventId.init.

Definition sb ES := ES.(acts_init_set) × ES.(acts_ninit_set) ∪
                    EventId.ext_sb ⨾ ⦗ ES.(acts_set) ⦘.
Definition cf ES := ⦗ ES.(acts_set) ⦘ ⨾
                    (EventId.same_tid ∩ compl_rel (ES.(sb)^? ∪ ES.(sb)⁻¹)) ⨾
                    ⦗ ES.(acts_set) ⦘.
Definition rf ES := ES.(ew)^? ⨾ ES.(jf) \ ES.(cf).

Hint Unfold ES.acts_set ES.acts_init_set ES.acts_ninit_set
     ES.sb ES.cf : unfolderDb.

Section EventStructure.

Variable EG : ES.t.

Notation "'E'"     := EG.(ES.acts_set).
Notation "'Einit'" := EG.(ES.acts_init_set).
Notation "'sb'" := EG.(ES.sb).
Notation "'rmw'" := EG.(ES.rmw).
Notation "'ew'" := EG.(ES.ew).
Notation "'jf'" := EG.(ES.jf).
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
    jfE : jf ≡ ⦗E⦘ ⨾ jf ⨾ ⦗E⦘ ;
    jfD : jf ≡ ⦗W⦘ ⨾ jf ⨾ ⦗R⦘ ;
    jfl : jf ⊆ same_loc ;
    jfv : funeq val jf ;
    jff : functional jf⁻¹ ;
    coE : co ≡ ⦗E⦘ ⨾ co ⨾ ⦗E⦘ ;
    coD : co ≡ ⦗W⦘ ⨾ co ⨾ ⦗W⦘ ;
    col : co ⊆ same_loc ;
    co_trans : transitive co ;
    co_total :
      forall ol ws (WS : ws ⊆₁ E ∩₁ W ∩₁ (fun x => loc x = ol))
             (NCF : ⦗ ws ⦘ ⨾ cf ⨾ ⦗ ws ⦘ ≡ ∅₂),
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
  generalize H0. clear H0.
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

Lemma rfE WF : rf ≡ ⦗E⦘ ⨾ rf ⨾ ⦗E⦘.
Proof.
  unfold ES.rf.
  arewrite (ew^? ⨾ jf ≡ ⦗E⦘ ⨾ ew^? ⨾ jf ⨾ ⦗E⦘) at 1.
  2: { assert (⦗E⦘ ⨾ ew^? ⨾ jf ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ (ew^? ⨾ jf) ⨾ ⦗E⦘) as HH
         by basic_solver. rewrite HH.
         by rewrite <- minus_eqv_rel_helper. }
  rewrite crE.
  rewrite !seq_union_l.
  rewrite !seq_union_r.
  relsf.
  apply union_more.
  { apply WF.(jfE). }
  rewrite WF.(ewE).
  rewrite WF.(jfE).
  rewrite !seqA.
  relsf.
Qed.

Lemma rfD WF : rf ≡ ⦗W⦘ ⨾ rf ⨾ ⦗R⦘.
Proof.
  unfold ES.rf.
  arewrite (ew^? ⨾ jf ≡ ⦗W⦘ ⨾ ew^? ⨾ jf ⨾ ⦗R⦘) at 1.
  2: { assert (⦗W⦘ ⨾ ew^? ⨾ jf ⨾ ⦗R⦘ ≡ ⦗W⦘ ⨾ (ew^? ⨾ jf) ⨾ ⦗R⦘) as HH
         by basic_solver. rewrite HH.
         by rewrite <- minus_eqv_rel_helper. }
  rewrite crE.
  rewrite !seq_union_l.
  rewrite !seq_union_r.
  relsf.
  apply union_more.
  { apply WF.(jfD). }
  rewrite WF.(ewD).
  rewrite WF.(jfD).
  rewrite !seqA.
  relsf.
Qed.
    
Lemma rfl WF : rf ⊆ same_loc.
Proof.
  unfold ES.rf.
  rewrite inclusion_minus_rel.
  rewrite WF.(jfl).
  rewrite WF.(ewl).
  generalize same_loc_trans.
  basic_solver.
Qed.

Lemma rfv WF : funeq val rf.
Proof.
  unfold ES.rf.
  apply funeq_minus.
  generalize WF.(jfv) WF.(ewv) funeq_seq.
  basic_solver.
Qed.

End EventStructure.
End ES.