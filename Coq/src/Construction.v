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

Definition cont_thread S (cont : ES.cont_label) : thread_id :=
  match cont with
  | ES.CInit thread => thread
  | ES.CEvent e => S.(ES.tid) e
  end.

Definition t_basic
           (event  : event_id)
           (event' : option event_id)
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
    let thread := cont_thread S cont in
    let set_event' : event_id -> Prop :=
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
      S'.(ES.cont) = (ES.CEvent event'', existT _ lang state') :: S.(ES.cont)
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
          | ES.CInit thread => S.(ES.acts_init_set)
          | ES.CEvent event_prev => dom_rel (S.(ES.sb)^? ⨾ ⦗ eq event_prev ⦘)
          end
      in
      S'.(ES.sb) ≡ S.(ES.sb) ∪ prev_set × eq event ∪
                             (prev_set ∪₁ eq event) × set_event' ⟫ /\
    ⟪ RMW' : S'.(ES.rmw) ≡ S.(ES.rmw) ∪ eq event × set_event' ⟫.
  
Definition add_jf (r : event_id) (S S' : ES.t) : Prop :=
  ⟪ RR : R S' r ⟫ /\
  exists w,
    ⟪ EW  : S.(ES.acts_set) w ⟫ /\
    ⟪ WW  : W S' w ⟫ /\
    ⟪ LOC : same_loc S' w r ⟫ /\
    ⟪ VAL : same_val S' w r ⟫ /\
    ⟪ JF' : S'.(ES.jf) ≡ S.(ES.jf) ∪ singl_rel w r ⟫.

Definition add_ew (w : event_id) (S S' : ES.t) : Prop :=
  ⟪ WW : W S w ⟫ /\
  exists (ws : event_id -> Prop),
    ⟪ WWS   : ws ⊆₁ W S ⟫ /\
    ⟪ LOCWS : ws ⊆₁ same_loc S w ⟫ /\
    ⟪ VALWS : ws ⊆₁ same_val S w ⟫ /\
    ⟪ CFWS  : ws ⊆₁ S.(ES.cf) w ⟫ /\
    ⟪ REPR :
      S'.(ES.ew) ≡ S'.(ES.ew) ∪ ws × eq w ∪ eq w × ws ⟫.

Definition add_co (w : event_id) (S S' : ES.t) : Prop :=
  let A := S.(ES.acts_set) ∩₁ W S ∩₁ (same_loc S w) \₁ (S.(ES.cf)^? w) in
  ⟪ WW : W S w ⟫ /\
  exists (ws : event_id -> Prop),
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
                (JF' : add_jf e S S')
                (EW' : S'.(ES.ew) ≡ S.(ES.ew))
                (CO' : S'.(ES.co) ≡ S.(ES.co))
| t_store  e    (BS  : t_basic e None S S')
                (JF' : S'.(ES.jf) ≡ S.(ES.jf))
                (EW' : add_ew e S S')
                (CO' : add_co e S S')
| t_update e e' (BS  : t_basic e (Some e') S S')
                (JF' : add_jf e  S S')
                (EW' : add_ew e' S S')
                (CO' : add_co e' S S').

Definition t (m : model) (S S' : ES.t) : Prop :=
  ⟪ TT  : t_ S S' ⟫ /\
  ⟪ CON : @es_consistent S' m ⟫.
End ESstep.