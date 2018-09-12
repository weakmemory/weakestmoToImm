From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events ProgToExecution Execution.
Require Import AuxRel EventStructure Consistency.

Export ListNotations.

Definition opt_to_list {A} (a : option A) : list A :=
  match a with
  | None => []
  | Some a => [a]
  end.

Definition same_val {A} (lab : A -> label) : relation A :=
  (fun x y => val lab x = val lab y).

Fixpoint act_to_event_helper (G : execution) (tid : thread_id)
           (n : nat) : label * list label :=
  let e := ThreadEvent tid n in
  let lbl := G.(lab) e in
  match n with
  | 0 => (lbl, [])
  | S n =>
    let (hd, tl) := act_to_event_helper G tid n in
    (lbl, hd :: tl)
  end.

Definition act_to_event (G : execution) (e : actid) : EventId.t :=
  let lbl := G.(lab) e in
  match e with
  | InitEvent   _   => EventId.mk e.(tid) lbl []
  | ThreadEvent t n =>
    let (hd, tl) := act_to_event_helper G t n in
    EventId.mk t hd tl
  end.

Module ESstep.
  
Notation "'R'" := (fun a => is_true (is_r EventId.lab a)).
Notation "'W'" := (fun a => is_true (is_w EventId.lab a)).
Notation "'F'" := (fun a => is_true (is_f EventId.lab a)).
Notation "'same_loc'" := (same_loc EventId.lab).
Notation "'same_val'" := (same_val EventId.lab).

Definition t_basic
           (execs : state -> Prop)
           (event  : EventId.t)
           (event' : option EventId.t)
           (s s' : ES.t) : Prop :=
  let thread := event.(EventId.tid) in
  let event_list := opt_to_list event' ++ [event] in
  let label_list := map EventId.lab event_list in
  let rmw_edge a b :=
      << EQA : eq a event >> /\
      << EQB : In b (opt_to_list event') >>
  in
  << TRE  : exists state state',
      let new_act  := (ThreadEvent thread state.(eindex)) in
      let new_act' := (ThreadEvent thread (1 + state.(eindex))) in
      << SS    : execs state  >> /\
      << SS'   : execs state' >> /\
      << ISTEP : istep thread label_list state state' >> /\
      << EREP1 : event = act_to_event state'.(G) new_act >> /\
      << EREP2 :
        match event' with
        | None => True
        | Some event' => event' = act_to_event state'.(G) new_act'
        end >>
  >> /\
  << EVN  : ~ s.(ES.acts_set) event >> /\
  << PRCL : s'.(ES.sb) ≡ <| s'.(ES.acts_set) |> ;; s'.(ES.sb) >> /\
  << REP  : s' = ES.mk (event_list ++ s.(ES.acts))
                       (rmw_edge ∪ s.(ES.rmw))
                       s.(ES.rf) s.(ES.co) s.(ES.ew)
  >>.
  
Definition add_rf (r : EventId.t) (s s' : ES.t) : Prop :=
  << RR : R r >> /\
  exists w,
    << EW   : s.(ES.acts_set) w >> /\
    << WW   : W w >> /\
    << LOC  : same_loc w r >> /\
    << VAL  : same_val w r >> /\
    << REPR :
      s' = ES.mk s.(ES.acts) s.(ES.rmw)
                 (singl_rel w r ∪ s.(ES.rf))
                 s.(ES.co) s.(ES.ew)
    >>.

Definition add_ew (w : EventId.t) (s s' : ES.t) : Prop :=
  << WW : W w >> /\
  exists (ws : EventId.t -> Prop),
    << WWS   : ws ⊆₁ W >> /\
    << LOCWS : ws ⊆₁ same_loc w >> /\
    << VALWS : ws ⊆₁ same_val w >> /\
    << CFWS  : ws ⊆₁ s.(ES.cf) w >> /\
    << REPR :
      s' = ES.mk s.(ES.acts) s.(ES.rmw)
                 s.(ES.rf) s.(ES.co)
                 (ws × eq w ∪ eq w × ws ∪ s.(ES.ew))
    >>.

Definition add_co (w : EventId.t) (s s' : ES.t) : Prop :=
  let A := s.(ES.acts_set) ∩₁ W ∩₁ (same_loc w) \₁ (s.(ES.cf)^? w) in
  << WW : W w >> /\
  exists (ws : EventId.t -> Prop),
    << WWS : ws ⊆₁ A >> /\
    << REPR :
      s' = ES.mk s.(ES.acts) s.(ES.rmw)
                 s.(ES.rf)
                 (ws × eq w ∪ eq w × (A \₁ ws) ∪ s.(ES.co))
                 s.(ES.ew)
    >>.

Inductive t_ (execs : state -> Prop) (s s' : ES.t) : Prop :=
| t_fence  e  (FF : F e) (BS : t_basic execs e None s s')
| t_load   e s1          (BS : t_basic execs e None s s1)
           (RF : add_rf e s1 s')
| t_store  e s1 s2       (BS : t_basic execs e None s s1)
           (EW : add_ew e s1 s2)
           (CO : add_co e s2 s')
| t_update e e' s1 s2 s3 (BS : t_basic execs e (Some e') s s1)
           (RF : add_rf e  s1 s2)
           (EW : add_ew e' s2 s3)
           (CO : add_co e' s3 s').

Definition t (m : model) (execs : state -> Prop) (s s' : ES.t) : Prop :=
  << TT  : t_ execs s s' >> /\
  << CON : es_consistent s' m >>.
End ESstep.