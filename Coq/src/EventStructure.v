Require Import Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events.
Require Import AuxRel.

Set Implicit Arguments.
Export ListNotations.

Definition compl_rel {A} (r : relation A) := fun a b => ~ r a b.

Definition event_id := Ident.t.
Definition tid_init := xH.

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

Inductive cont_label :=
| CInit  (tid : thread_id)
| CEvent (eid : event_id).

Record t :=
  mk { acts : list event_id;
       lab  : event_id -> label; 
       tid  : event_id -> thread_id;
       sb   : event_id -> event_id -> Prop ;
       rmw  : event_id -> event_id -> Prop ;
       jf   : event_id -> event_id -> Prop ;
       co   : event_id -> event_id -> Prop ;
       ew   : event_id -> event_id -> Prop ;

       lang : Language.t;
       cont : list (cont_label * lang.(Language.state));
     }.

Definition acts_set ES := fun x => In x ES.(acts).
Definition acts_init_set  ES := ES.(acts_set)
                                     ∩₁ (fun x => ES.(tid) x = tid_init).
Definition acts_ninit_set ES := ES.(acts_set) \₁ ES.(acts_init_set).
Definition cont_set ES := fun x => In x ES.(cont).

Definition same_tid ES := fun x y => ES.(tid) x = ES.(tid) y.

Definition cf ES := ⦗ ES.(acts_set) ⦘ ⨾
                    (ES.(same_tid) ∩ compl_rel (ES.(sb)^? ∪ ES.(sb)⁻¹)) ⨾
                    ⦗ ES.(acts_set) ⦘.
Definition rf ES := ES.(ew)^? ⨾ ES.(jf) \ ES.(cf).

Hint Unfold ES.acts_set ES.acts_init_set ES.cf : unfolderDb.

Section EventStructure.

Variable EG : ES.t.

Notation "'E'"      := EG.(ES.acts_set).
Notation "'Einit'"  := EG.(ES.acts_init_set).
Notation "'Eninit'" := EG.(ES.acts_ninit_set).
Notation "'tid'"   := EG.(ES.tid).
Notation "'sb'"    := EG.(ES.sb).
Notation "'rmw'"   := EG.(ES.rmw).
Notation "'ew'"    := EG.(ES.ew).
Notation "'jf'"    := EG.(ES.jf).
Notation "'rf'"    := EG.(ES.rf).
Notation "'co'"    := EG.(ES.co).
Notation "'lab'"   := EG.(ES.lab).
Notation "'cf'"    := EG.(ES.cf).
Notation "'K'"     := EG.(ES.cont_set).
Notation "'lang'"  := EG.(ES.lang).

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
  { initL : forall l, (exists b, E b /\ loc b = Some l) ->
                      exists a, Einit a /\ loc a = Some l ;
    init_lab : forall e (INIT : Einit e),
        exists l, lab l = Astore Xpln Opln l 0 ;
    sbE : sb ≡ ⦗E⦘ ⨾ sb ⨾ ⦗E⦘ ;
    sb_irr   : irreflexive sb;
    sb_trans : transitive sb;
    sb_init  : Einit × Eninit ⊆ sb;
    rmwD : rmw ≡ ⦗R⦘ ⨾ rmw ⨾ ⦗W⦘ ;
    rmwl : rmw ⊆ same_loc ;
    rmwi : rmw ⊆ immediate sb ;
    jfE : jf ≡ ⦗E⦘ ⨾ jf ⨾ ⦗E⦘ ;
    jfD : jf ≡ ⦗W⦘ ⨾ jf ⨾ ⦗R⦘ ;
    jfl : jf ⊆ same_loc ;
    jfv : funeq val jf ;
    jff : functional jf⁻¹ ;
    jf_complete : E ∩₁ R ⊆₁ codom_rel jf;
    jf_not_cf : jf ∩ cf ≡ ∅₂;

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

    term_def_K : forall state (TERM : lang.(Language.is_terminal) state),
        ~ (exists lbl state', lang.(Language.step) lbl state state');
    init_tid_K : ~ (exists c, K (CInit tid_init, c));
    unique_K : forall c c' (CK : K c) (CK' : K c') (FF : fst c = fst c'),
        snd c = snd c';
    event_K  : forall e (NINIT : ~ Einit e) (NRMW : ~ dom_rel rmw e),
        exists c, K (CEvent e, c);
  }.

Implicit Type WF : Wf.

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

Lemma jf_in_rf WF : jf ⊆ rf.
Proof.
  unfold ES.rf.
  generalize WF.(jf_not_cf).
  basic_solver.
Qed.

Lemma rf_complete WF : E ∩₁ R ⊆₁ codom_rel rf.
Proof. rewrite <- WF.(jf_in_rf). apply WF. Qed.

End EventStructure.
End ES.