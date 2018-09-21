Require Import Omega.
From hahn Require Import Hahn.
From imm Require Import Events Execution.
From promising Require Import Basic.
Require Import EventStructure.

Tactic Notation "destruct_seq" constr(x)
       "as" "[" ident(y) ident(z) "]" :=
  apply seq_eqv_l in x; destruct x as [y x];
  apply seq_eqv_r in x; destruct x as [x z].

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

Lemma act_to_event_ext_sb_S G thread y :
  EventId.ext_sb (act_to_event G (ThreadEvent thread y))
    (act_to_event G (ThreadEvent thread (S y))).
Proof.
  unfold act_to_event.
  red. splits; desf.
  eexists. exists [].
  unfold EventId.path. simpls.
  rewrite Heq0 in *. clear Heq0.
  inv Heq.
Qed.

Lemma act_to_event_ext_sb_lt G thread x y (LT : x < y) :
  EventId.ext_sb (act_to_event G (ThreadEvent thread x))
    (act_to_event G (ThreadEvent thread y)).
Proof.
  generalize dependent x.
  induction y; ins; inv LT.
  { apply act_to_event_ext_sb_S. }
  eapply EventId.ext_sb_trans.
  { by apply IHy. }
  apply act_to_event_ext_sb_S.
Qed.

Lemma act_to_event_prefix_length G thread m :
  length (EventId.prefix (act_to_event G (ThreadEvent thread m))) = m.
Proof. induction m; simpls; desf. Qed.

Lemma act_to_event_ext_sb_dom (G : execution) y :
  dom_rel (EventId.ext_sb ;; <| eq (act_to_event G y) |>) ≡₁
  (match y with
   | InitEvent _ => ∅
   | ThreadEvent thread n =>
     fun x =>
       exists m,
         << LTMN : m < n >> /\
         << REPX : x = act_to_event G (ThreadEvent thread m) >>
   end).
Proof.
  desf.
  { split; [|basic_solver].
    intros x [y HH].
    apply seq_eqv_r in HH. destruct HH as [HH]; desf.
    simpls. cdes HH. destruct tl; desf. }
  split.
  2: { intros x [y]; desf.
       red. eexists.
       apply seq_eqv_r. split; [|done].
         by apply act_to_event_ext_sb_lt. }
  intros x [y HH].
  apply seq_eqv_r in HH; desf.
  cdes HH. destruct x.
  exists (length (prefix)).
  unfold EventId.path in *.
  assert (index =
          length (EventId.prefix (act_to_event G (ThreadEvent thread index)))
         ) as XX.
  { symmetry. apply act_to_event_prefix_length. }
  simpls.
  destruct (act_to_event_helper G thread index) eqn:AA.
  simpls. subst.
  splits; inv REPR.
  { rewrite app_length. simpls. omega. }
  clear REPR. clear HH.
  generalize dependent prefix.
  generalize dependent lab.
  generalize dependent hd.
  induction tl; ins.
  { destruct (act_to_event_helper G thread (length prefix)) eqn:BB.
    inv AA. }
  destruct (act_to_event_helper G thread (length (tl ++ lab :: prefix)))
  eqn:BB.
  inv AA. clear AA.
    by apply IHtl in BB.
Qed.