From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events ProgToExecution.
Require Import AuxRel EventStructure Consistency.

Export ListNotations.

Definition opt_to_list {A} (a : option A) : list A :=
  match a with
  | None => []
  | Some a => [a]
  end.

Definition same_val {A} (lab : A -> label) : relation A :=
  (fun x y => val lab x = val lab y).

Module ESstep.
  
Notation "'R'" := (fun a => is_true (is_r EventId.lab a)).
Notation "'W'" := (fun a => is_true (is_w EventId.lab a)).
Notation "'F'" := (fun a => is_true (is_f EventId.lab a)).
Notation "'same_loc'" := (same_loc EventId.lab).
Notation "'same_val'" := (same_val EventId.lab).

Definition t_basic
           (event  : EventId.t)
           (event' : option EventId.t)
           (s s' : ES.t) : Prop :=
  let event_list := opt_to_list event' ++ [event] in
  let label_list := map EventId.lab event_list in
  let rmw_edge a b :=
      << EQA : eq a event >> /\
      << EQB : In b (opt_to_list event') >>
  in
  << TRE  : exists state state',
      << ISTEP : istep event.(EventId.tid) label_list state state' >> /\
      (* TODO: compilation of *)
      << FF : False >>
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

Inductive t_ (s s' : ES.t) : Prop :=
| t_fence  e             (BS : t_basic e None s s')
          (FF : is_f EventId.lab e)
| t_load   e s1          (BS : t_basic e None s s1)
          (RF : add_rf e s1 s')
| t_store  e s1 s2       (BS : t_basic e None s s1)
          (EW : add_ew e s1 s2)
          (CO : add_co e s2 s')
| t_update e e' s1 s2 s3 (BS : t_basic e (Some e') s s1)
           (RF : add_rf e s1 s2)
           (EW : add_ew e' s2 s3)
           (CO : add_co e' s3 s').

Definition t (m : model) (s s' : ES.t) : Prop :=
  << TT  : t_ s s' >> /\
  << CON : es_consistent s' m >>.
End ESstep.

Definition last_error {A} (l : list A) : option A :=
  match l with
  | [] => None
  | h::t => Some (last t h)
  end.

(* Definition add_cont (k : Continuation.t) (s : ES.t) : ES.t := *)
(*   {| acts := s.(acts); *)
(*      acts_init := s.(acts_init); *)
(*      next_act := s.(next_act); *)
(*      tid := s.(tid); *)
(*      lab := s.(lab); *)
(*      sb := s.(sb); *)
(*      rmw := s.(rmw); *)
(*      rf := s.(rf); *)
(*      co := s.(co); *)
(*      ew := s.(ew); *)
(*      conts := k :: s.(conts); *)
(*   |}. *)

Definition cstep_ (labs : list label) (s s' : ES.t) (k : Continuation.t) : Prop :=
  let thread := k.(Continuation.thread) in
  let lang   := k.(Continuation.lang)   in
  let state  := k.(Continuation.state)  in
  let prev_acts :=
      match k.(Continuation.prev_act) with
      | Some e => eq e
      | None   => s.(acts_init_set)
      end
  in
  << INK : In k s.(conts) >> /\
  exists (state' : lang.(Language.state)),
    let new_cont :=
        Continuation.mk lang state' thread
                        (match labs with
                         | [] => None
                         | _ => Some (length labs + s.(next_act))
                         end) in
    << LSTEP : lang.(Language.step) labs state state' >> /\
    << SES   :
      s' = {| acts := s.(acts);
              acts_init := s.(acts_init);
              next_act := length labs + s.(next_act);
              tid := s.(tid);
              lab := s.(lab);
              sb := s.(sb);
              rmw := s.(rmw);
              rf := s.(rf);
              co := s.(co);
              ew := s.(ew);
              conts := new_cont :: s.(conts); |} >>.
      

    match labs with
    | []    =>
      s' = {| acts := s.(acts);
              acts_init := s.(acts_init);
              next_act := s.(next_act);
              tid := s.(tid);
              lab := s.(lab);
              sb := s.(sb);
              rmw := s.(rmw);
              rf := s.(rf);
              co := s.(co);
              ew := s.(ew);
              conts := (new_cont None) :: s.(conts);
           |}
    | [lbl] =>
      s' = {| acts := s.(acts);
              acts_init := s.(acts_init);
              next_act := 1 + s.(next_act);
              tid := s.(tid);
              lab := mupd s.(lab) s.(next_act) lbl;
              sb := s.(sb);
              rmw := s.(rmw);
              rf := s.(rf);
              co := s.(co);
              ew := s.(ew);
              conts := (new_cont (Some s.(next_act))) :: s.(conts);
           |}
    | _     => False
    end.

Definition cstep (labs : list label) (s s' : ES.t) : Prop :=
  exists (k : Continuation.t), cstep_ labs s s' k.

Inductive step (s s' : ES.t) : Prop :=
| False.