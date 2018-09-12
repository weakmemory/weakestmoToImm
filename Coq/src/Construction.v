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

Module ESstep.

Definition t_basic (es : state -> Prop) 
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

(* TODO *) 
Inductive t (m : model) : relation ES.t :=
| t_fence  x : t m x x
| t_load   x : t m x x
| t_store  x : t m x x
| t_update x : t m x x.

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