From hahn Require Import Hahn.
From imm Require Import Events Execution.
From promising Require Import Basic.
Require Import EventStructure.

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