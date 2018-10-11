Require Import Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events ProgToExecution Execution.
Require Import AuxRel AuxDef EventStructure Consistency.

Export ListNotations.

Module ESstep.

Notation "'R' S" := (fun a => is_true (is_r S.(ES.lab) a)) (at level 10).
Notation "'W' S" := (fun a => is_true (is_w S.(ES.lab) a)) (at level 10).
Notation "'F' S" := (fun a => is_true (is_f S.(ES.lab) a)) (at level 10).
Notation "'same_loc' S" := (same_loc S.(ES.lab)) (at level 10).
Notation "'same_val' S" := (same_val S.(ES.lab)) (at level 10).
Notation "'K' S" := (S.(ES.cont_set)) (at level 10).

Definition t_basic
           (event  : eventid)
           (event' : option eventid)
           (S S' : ES.t) : Prop :=
  ⟪ EVENT  : event = S.(ES.next_act) ⟫ /\
  ⟪ EVENT' :
    exists next_shift,
      ⟪ NEXT_SHIFT :
        match event' with
        | None => next_shift = 1
        | Some _ =>
          next_shift = 2 /\
          ⟪ EVENT' : event' = Some (1 + event) ⟫
        end
      ⟫ /\
      ⟪ NEXT_ACT :
          S'.(ES.next_act) = next_shift + S.(ES.next_act) ⟫
  ⟫ /\
  exists cont lang (state state' : lang.(Language.state))
         label label',
    let label_list := opt_to_list label' ++ [label] in
    let thread := ES.cont_thread S cont in
    let set_event' : eventid -> Prop :=
        match event' with
        | None => ∅
        | Some event'' => eq event''
        end
    in
    ⟪ CONT  : K S (cont, existT _ lang state) ⟫ /\
    ⟪ CONT' :
      let event'' :=
          match event' with
          | None => event
          | Some event'' => event''
          end
      in
      S'.(ES.cont) = (CEvent event'', existT _ lang state') :: S.(ES.cont)
    ⟫ /\
    ⟪ STEP : lang.(Language.step) label_list state state' ⟫ /\
    ⟪ LABEL' :
      match event', label' with
      | None, None
      | Some _, Some _ => True
      | _, _ => False
      end
    ⟫ /\
    ⟪ LAB' :
      let lab' := upd S.(ES.lab) event label in
      S'.(ES.lab) =
      match event', label' with
      | Some event'', Some label'' => upd lab' event'' label''
      | _, _ => lab'
      end
    ⟫ /\
    ⟪ TID' :
      let tid' := upd S.(ES.tid) event thread in
      S'.(ES.tid) =
      match event' with
      | Some event'' => upd tid' event'' thread
      | None => tid'
      end
    ⟫ /\
    ⟪ SB' :
      let prev_set :=
          match cont with
          | CInit thread => S.(ES.acts_init_set)
          | CEvent event_prev => dom_rel (S.(ES.sb)^? ⨾ ⦗ eq event_prev ⦘)
          end
      in
      S'.(ES.sb) ≡ S.(ES.sb) ∪ prev_set × eq event ∪
                             (prev_set ∪₁ eq event) × set_event' ⟫ /\
    ⟪ RMW' : S'.(ES.rmw) ≡ S.(ES.rmw) ∪ eq event × set_event' ⟫.
  
Definition add_jf (r : eventid) (S S' : ES.t) : Prop :=
  ⟪ RR : R S' r ⟫ /\
  exists w,
    ⟪ EW  : S.(ES.acts_set) w ⟫ /\
    ⟪ WW  : W S' w ⟫ /\
    ⟪ LOC : same_loc S' w r ⟫ /\
    ⟪ VAL : same_val S' w r ⟫ /\
    ⟪ JF' : S'.(ES.jf) ≡ S.(ES.jf) ∪ singl_rel w r ⟫.

Definition add_ew (w : eventid) (S S' : ES.t) : Prop :=
  ⟪ WW : W S' w ⟫ /\
  exists (ws : eventid -> Prop),
    ⟪ WWS   : ws ⊆₁ W S ⟫ /\
    ⟪ LOCWS : ws ⊆₁ same_loc S w ⟫ /\
    ⟪ VALWS : ws ⊆₁ same_val S w ⟫ /\
    ⟪ CFWS  : ws ⊆₁ S.(ES.cf) w ⟫ /\
    ⟪ REPR :
      S'.(ES.ew) ≡ S.(ES.ew) ∪ ws × eq w ∪ eq w × ws ⟫.

Definition add_co (w : eventid) (S S' : ES.t) : Prop :=
  let A := S.(ES.acts_set) ∩₁ W S ∩₁ (same_loc S w) \₁ (S.(ES.cf)^? w) in
  ⟪ WW : W S' w ⟫ /\
  exists (ws : eventid -> Prop),
    ⟪ WWS : ws ⊆₁ A ⟫ /\
    ⟪ REPR :
      S'.(ES.co) ≡ S.(ES.co) ∪ S.(ES.ew) ∪ ws × eq w ∪ eq w × (A \₁ ws) ⟫.

Inductive t_ (S S' : ES.t) : Prop :=
| t_fence  e    (BS  : t_basic e None S S')
                (FF  : F S' e)
                (JF' : S'.(ES.jf) ≡ S.(ES.jf))
                (EW' : S'.(ES.ew) ≡ S.(ES.ew))
                (CO' : S'.(ES.co) ≡ S.(ES.co))
| t_load   e    (BS  : t_basic e None S S')
                (AJF : add_jf e S S')
                (EW' : S'.(ES.ew) ≡ S.(ES.ew))
                (CO' : S'.(ES.co) ≡ S.(ES.co))
| t_store  e    (BS  : t_basic e None S S')
                (JF' : S'.(ES.jf) ≡ S.(ES.jf))
                (AEW : add_ew e S S')
                (ACO : add_co e S S')
| t_update e e' (BS  : t_basic e (Some e') S S')
                (AJF : add_jf e  S S')
                (AEW : add_ew e' S S')
                (ACO : add_co e' S S').

Definition t (m : model) (S S' : ES.t) : Prop :=
  ⟪ TT  : t_ S S' ⟫ /\
  ⟪ CON : @es_consistent S' m ⟫.

Lemma basic_step_acts_set 
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BASIC_STEP : t_basic e e' S S') :
  S'.(ES.acts_set) ≡₁ S.(ES.acts_set) ∪₁ eq e ∪₁ eq_opt e'.
Proof. 
  cdes BASIC_STEP. 
  edestruct e';
    desf; 
    unfold ES.acts_set; 
    rewrite NEXT_ACT;
    autounfold with unfolderDb;
    splits; unfold set_subset; intros; by omega.
Qed.

Lemma basic_step_acts_set_mon
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BASIC_STEP : t_basic e e' S S') :
  S.(ES.acts_set) ⊆₁ S'.(ES.acts_set).
Proof. 
  edestruct basic_step_acts_set as [INCL_L INCL_R]; eauto. 
  do 2 (apply set_subset_union_l in INCL_R; desf). 
Qed.

Lemma basic_step_tid_eq_dom
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e e' S S') :
  eq_dom S.(ES.acts_set) S.(ES.tid) S'.(ES.tid).
Proof. 
  unfold eq_dom. ins. 
  unfold ES.acts_set in SX.
  cdes BSTEP. 
  rewrite TID'.
  desf; rewrite updo; try rewrite updo; desf; omega. 
Qed.

Lemma basic_step_same_tid
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e e' S S') :
  restr_rel S.(ES.acts_set) S.(ES.same_tid) ≡ restr_rel S.(ES.acts_set) S'.(ES.same_tid).
Proof. 
  autounfold with unfolderDb. 
  unfold ES.same_tid.
  splits; ins; desf; splits; auto;
    [erewrite <- basic_step_tid_eq_dom | erewrite basic_step_tid_eq_dom];
    eauto;
    rewrite H;
    [|symmetry];
    eapply basic_step_tid_eq_dom; eauto. 
Qed.

Lemma basic_step_sb_mon
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e e' S S') :
  S.(ES.sb) ⊆ S'.(ES.sb).
Proof.
  cdes BSTEP.
  desf; rewrite SB'; basic_solver. 
Qed.

Lemma basic_step_cf_mon 
      (e  : eventid)
      (e' : option eventid)
      (S S' : ES.t) 
      (BSTEP : t_basic e e' S S') :
  S.(ES.cf) ⊆ S'.(ES.cf).
Proof.
  edestruct basic_step_same_tid as [STIDL STIDR]; [by apply BSTEP|].
  unfold ES.cf.
  cdes BSTEP. 
  rewrite SB'. 
  rewrite (basic_step_acts_set e e' S S'); [| apply BSTEP].
  unfold eq_opt. 
  repeat rewrite <- restr_relE.
  repeat rewrite restr_inter.
  rewrite STIDL. 
  autounfold with unfolderDb.
  ins; desf; splits; auto; 
    unfold not; ins; desf; auto; omega. 
Qed.

Lemma step_jf_mon S S' (STEP_: t_ S S') :
  S.(ES.jf) ⊆ S'.(ES.jf).
Proof. 
  destruct STEP_; try (by rewrite JF'; apply inclusion_refl2); 
    cdes AJF; rewrite JF'; basic_solver.  
Qed.

Lemma step_ew_mon S S' (STEP_: t_ S S') :
  S.(ES.ew) ⊆ S'.(ES.ew).
Proof. 
  destruct STEP_; try (by rewrite EW');
    cdes AEW; rewrite REPR; basic_solver. 
Qed.

Lemma step_jfe_mon S S' (STEP_: t_ S S') (wfE: ES.Wf S) :
  S.(ES.jfe) ⊆ S'.(ES.jfe).
Proof. 
  unfold ES.jfe.
  edestruct STEP_; 
    cdes BS; 
    rewrite SB';
    try (cdes AJF);
    rewrite JF';
    rewrite wfE.(ES.jfE).
  1,3:
    autounfold with unfolderDb;
    ins; desf; splits;
    try (by eexists; splits; eauto);
    unfold not; ins; desf; omega.
  all:
    autounfold with unfolderDb;
    ins; desf; splits;
    try (by left; eexists; splits; eauto);
    unfold not; ins; desf; omega.
Qed.

Lemma step_cc_mon S S' (STEP_: t_ S S') (wfE: ES.Wf S) :
  S.(ES.cc) ⊆ S'.(ES.cc).
Proof.
  unfold ES.cc. 
  apply inclusion_inter_mon.
  { edestruct STEP_; eapply basic_step_cf_mon; apply BS. } 
  apply inclusion_seq_mon.
  { by eapply step_jfe_mon. }
  apply inclusion_seq_mon.
  { unfold inclusion. ins. eapply clos_refl_trans_mon.
    { apply H. }
    apply inclusion_union_mon.
    { edestruct STEP_; eapply basic_step_sb_mon; apply BS. }
    by eapply step_jf_mon. } 
  apply inclusion_seq_mon. 
  { by eapply step_jfe_mon. }
  apply clos_refl_mori. 
  edestruct STEP_; eapply basic_step_sb_mon; apply BS. 
Qed.
      
Lemma step_vis_mon S S' (STEP_: t_ S S') (wfE: ES.Wf S) :
  vis S ⊆₁ vis S'.
Proof.
  unfold vis. 
  apply codom_rel_mori. 
  apply inclusion_inter_mon.
  { by apply step_cc_mon. }
  apply inclusion_seq_mon.
  { by apply step_ew_mon. }
  apply eq_class_mori.
  edestruct STEP_; eapply basic_step_sb_mon; apply BS.
Qed.

Lemma step_event_to_act S S' (STEP_: t_ S S') (wfE: ES.Wf S) : 
  eq_dom (ES.acts_set S) (ES.event_to_act S) (ES.event_to_act S').
Proof.
Admitted. 

End ESstep.