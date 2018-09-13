From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events ProgToExecution Execution.
Require Import AuxRel AuxDef EventStructure Consistency.

Export ListNotations.

Module ESstep.
  
Notation "'R'" := (fun a => is_true (is_r EventId.lab a)).
Notation "'W'" := (fun a => is_true (is_w EventId.lab a)).
Notation "'F'" := (fun a => is_true (is_f EventId.lab a)).
Notation "'same_loc'" := (same_loc EventId.lab).
Notation "'same_val'" := (same_val EventId.lab).

Definition t_basic
           (execs : thread_id -> state -> Prop)
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
      << SS    : execs thread state  >> /\
      << SS'   : execs thread state' >> /\
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
                       s.(ES.jf) s.(ES.co) s.(ES.ew)
  >>.
  
Definition add_jf (r : EventId.t) (s s' : ES.t) : Prop :=
  << RR : R r >> /\
  exists w,
    << EW   : s.(ES.acts_set) w >> /\
    << WW   : W w >> /\
    << LOC  : same_loc w r >> /\
    << VAL  : same_val w r >> /\
    << REPR :
      s' = ES.mk s.(ES.acts) s.(ES.rmw)
                 (singl_rel w r ∪ s.(ES.jf))
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
                 s.(ES.jf) s.(ES.co)
                 (ws × eq w ∪ eq w × ws ∪ s.(ES.ew))
    >>.

Definition add_co (w : EventId.t) (s s' : ES.t) : Prop :=
  let A := s.(ES.acts_set) ∩₁ W ∩₁ (same_loc w) \₁ (s.(ES.cf)^? w) in
  << WW : W w >> /\
  exists (ws : EventId.t -> Prop),
    << WWS : ws ⊆₁ A >> /\
    << REPR :
      s' = ES.mk s.(ES.acts) s.(ES.rmw)
                 s.(ES.jf)
                 (ws × eq w ∪ eq w × (A \₁ ws) ∪ s.(ES.co))
                 s.(ES.ew)
    >>.

Inductive t_ (execs : thread_id -> state -> Prop) (s s' : ES.t) : Prop :=
| t_fence  e  (FF : F e) (BS : t_basic execs e None s s')
| t_load   e s1          (BS : t_basic execs e None s s1)
           (JF : add_jf e s1 s')
| t_store  e s1 s2       (BS : t_basic execs e None s s1)
           (EW : add_ew e s1 s2)
           (CO : add_co e s2 s')
| t_update e e' s1 s2 s3 (BS : t_basic execs e (Some e') s s1)
           (JF : add_jf e  s1 s2)
           (EW : add_ew e' s2 s3)
           (CO : add_co e' s3 s').

Definition t (m : model) (execs : thread_id -> state -> Prop) (s s' : ES.t) : Prop :=
  << TT  : t_ execs s s' >> /\
  << CON : es_consistent s' m >>.
End ESstep.