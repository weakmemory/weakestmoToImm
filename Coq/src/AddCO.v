From hahn Require Import Hahn.
From imm Require Import Events AuxRel. 
Require Import AuxRel.
Require Import AuxDef.
Require Import EventStructure.
Require Import Consistency.
Require Import BasicStep.
Require Import AddEW.

Set Implicit Arguments.

Notation "'E' S" := S.(ES.acts_set) (at level 10).
Notation "'Einit' S"  := S.(ES.acts_init_set) (at level 10).
Notation "'Eninit' S" := S.(ES.acts_ninit_set) (at level 10).

Notation "'tid' S" := S.(ES.tid) (at level 10).
Notation "'lab' S" := S.(ES.lab) (at level 10).
Notation "'mod' S" := (Events.mod S.(ES.lab)) (at level 10).
Notation "'loc' S" := (Events.loc S.(ES.lab)) (at level 10).
Notation "'val' S" := (Events.val S.(ES.lab)) (at level 10).

Notation "'sb' S" := S.(ES.sb) (at level 10).
Notation "'rmw' S" := S.(ES.rmw) (at level 10).
Notation "'ew' S" := S.(ES.ew) (at level 10).
Notation "'jf' S" := S.(ES.jf) (at level 10).
Notation "'rf' S" := S.(ES.rf) (at level 10).
Notation "'co' S" := S.(ES.co) (at level 10).
Notation "'cf' S" := S.(ES.cf) (at level 10).

Notation "'jfe' S" := S.(ES.jfe) (at level 10).
Notation "'rfe' S" := S.(ES.rfe) (at level 10).
Notation "'coe' S" := S.(ES.coe) (at level 10).
Notation "'jfi' S" := S.(ES.jfi) (at level 10).
Notation "'rfi' S" := S.(ES.rfi) (at level 10).
Notation "'coi' S" := S.(ES.coi) (at level 10).

Notation "'R' S" := (fun a => is_true (is_r S.(ES.lab) a)) (at level 10).
Notation "'W' S" := (fun a => is_true (is_w S.(ES.lab) a)) (at level 10).
Notation "'F' S" := (fun a => is_true (is_f S.(ES.lab) a)) (at level 10).

Notation "'RW' S" := (R S ∪₁ W S) (at level 10).
Notation "'FR' S" := (F S ∪₁ R S) (at level 10).
Notation "'FW' S" := (F S ∪₁ W S) (at level 10).

Notation "'Pln' S" := (fun a => is_true (is_only_pln S.(ES.lab) a)) (at level 10).
Notation "'Rlx' S" := (fun a => is_true (is_rlx S.(ES.lab) a)) (at level 10).
Notation "'Rel' S" := (fun a => is_true (is_rel S.(ES.lab) a)) (at level 10).
Notation "'Acq' S" := (fun a => is_true (is_acq S.(ES.lab) a)) (at level 10).
Notation "'Acqrel' S" := (fun a => is_true (is_acqrel S.(ES.lab) a)) (at level 10).
Notation "'Sc' S" := (fun a => is_true (is_sc S.(ES.lab) a)) (at level 10).

(* Notation "'same_mod' S" := (same_mod S.(ES.lab)) (at level 10). *)
(* Notation "'same_loc' S" := (same_loc S.(ES.lab)) (at level 10). *)
(* Notation "'same_val' S" := (same_val S.(ES.lab)) (at level 10). *)

Notation "'K' S" := (S.(ES.cont_set)) (at level 10).

Notation "'Tid' S" := (fun t e => S.(ES.tid) e = t) (at level 9).
Notation "'Mod_' S" := (fun m x => mod S x = m) (at level 9).
Notation "'Loc_' S" := (fun l x => loc S x = l) (at level 9).
Notation "'Val_' S" := (fun v e => val S e = v) (at level 9).

Definition ws_compl ews ws S := 
  codom_rel (⦗ews ∪₁ ws⦘ ⨾ co S) \₁ (ews ∪₁ ws).

Definition co_delta ews ws w' S : relation eventid := 
  ws × eq w' ∪ eq w' × ws_compl ews ws S.

Hint Unfold ws_compl co_delta : ESStepDb.

Definition add_co ews ws w' S S' : Prop := 
  ⟪ wE' : E S' w' ⟫ /\
  ⟪ wW' : W S' w' ⟫ /\
  ⟪ wsE : ws ⊆₁ E S ⟫ /\
  ⟪ wsW : ws ⊆₁ W S ⟫ /\
  ⟪ wsLOC : ws ⊆₁ same_loc S' w' ⟫ /\
  ⟪ ws_ews : ws ∩₁ ews ⊆₁ ∅ ⟫ /\
  ⟪ wsEinit : (Einit S ∩₁ Loc_ S (loc S' w')) ⊆₁ ws ⟫ /\
  ⟪ wsCOEWprcl : dom_rel ((co S)^? ⨾ (ew S)^? ⨾ ⦗ws⦘) ⊆₁ ws ⟫ /\
  ⟪ ewsCOprcl : dom_rel (co S ⨾ ⦗ews⦘) ⊆₁ ws ⟫ /\
  ⟪ ewsCOprcl : dom_rel (co S ⨾ ⦗ews⦘) ⊆₁ ws ⟫ /\
  (* ⟪ wsNCF : ws ⊆₁ dom_rel ((co S)^? ⨾ (ew S)^? ⨾ ⦗set_compl (cf S' w')⦘) ⟫ /\ *)
  ⟪ CO' : co S' ≡ co S ∪ co_delta ews ws w' S ⟫.

(******************************************************************************)
(** ** ews, ws, ws_compl lemmas *)
(******************************************************************************)

Lemma add_co_ws_co_prcl ews ws w' S S'
      (wf : ES.Wf S) 
      (ACO : add_co ews ws w' S S') : 
  dom_rel (co S ⨾ ⦗ws⦘) ⊆₁ ws.
Proof. cdes ACO. generalize wsCOEWprcl. basic_solver 10. Qed.

Lemma add_co_ws_ew_prcl ews ws w' S S'
      (wf : ES.Wf S) 
      (ACO : add_co ews ws w' S S') : 
  dom_rel (ew S ⨾ ⦗ws⦘) ⊆₁ ws.
Proof. cdes ACO. generalize wsCOEWprcl. basic_solver 10. Qed.

Lemma add_co_ws_ew_fwcl ews ws w' S S'
      (wf : ES.Wf S) 
      (ACO : add_co ews ws w' S S') : 
  codom_rel (⦗ws⦘ ⨾ ew S) ⊆₁ ws.
Proof. 
  cdes ACO. 
  intros x [y [z [[EQz WS] EW]]]. subst z.
  apply ES.ew_sym in EW; auto.
  eapply add_co_ws_ew_prcl; eauto.
  basic_solver 10.
Qed.

Lemma add_co_ws_co_ew_prcl ews ws w' S S'
      (wf : ES.Wf S) 
      (ACO : add_co ews ws w' S S') : 
  dom_rel (co S ⨾ ew S ⨾ ⦗ws⦘) ⊆₁ ws.
Proof. cdes ACO. generalize wsCOEWprcl. basic_solver 10. Qed.

Lemma add_co_ws_complE ews ws S 
      (wf : ES.Wf S) : 
  ws_compl ews ws S ⊆₁ E S.
Proof. 
  unfold ws_compl.
  rewrite ES.coE; auto.
  basic_solver.
Qed.

Lemma add_co_ws_complW ews ws S 
      (wf : ES.Wf S) : 
  ws_compl ews ws S ⊆₁ W S.
Proof. 
  unfold ws_compl.
  rewrite ES.coD; auto.
  basic_solver.
Qed.

Lemma add_co_ws_compl_loc ews ws w' e e' S S'
      (wf : ES.Wf S) 
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S')
      (ACO : add_co ews ws w' S S') : 
  ws_compl ews ws S ⊆₁ same_loc S' w'.
Proof. 
  cdes AEW; cdes ACO.
  unfold ws_compl.
  rewrite ES.coE; auto.
  rewrite ewsLOC at 1.
  rewrite wsLOC at 1.
  rewrite ES.col; auto.
  rewrite set_unionK.
  intros x [[y HH] _].
  unfolder in HH. desc.
  etransitivity; eauto.
  arewrite (loc S' y = loc S y).
  { erewrite basic_step_loc_eq_dom; eauto. }
  arewrite (loc S' x = loc S x).
  { erewrite basic_step_loc_eq_dom; eauto. }
  done. 
Qed.

Lemma add_co_wsEWLoc ews ws w' e e' S S'
      (wf : ES.Wf S) 
      (BSTEP : basic_step e e' S S') 
      (ACO : add_co ews ws w' S S') : 
  ws ⊆₁ (E S) ∩₁ (W S) ∩₁ (Loc_ S (loc S' w')).
Proof. 
  cdes ACO.
  intros x xWS.
  unfolder; splits; auto.
  etransitivity.
  { symmetry. eapply basic_step_loc_eq_dom; eauto. }
  symmetry. by apply wsLOC in xWS.
Qed.

Lemma add_co_ws_complEWLoc ews ws w' e e' S S'
      (wf : ES.Wf S) 
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S')
      (ACO : add_co ews ws w' S S') : 
  ws_compl ews ws S ⊆₁ (E S) ∩₁ (W S) ∩₁ (Loc_ S (loc S' w')).
Proof. 
  cdes ACO.
  intros x xWS.
  unfolder; splits; auto.
  { eapply add_co_ws_complE; eauto. }
  { eapply add_co_ws_complW; eauto. }
  etransitivity.
  { symmetry. eapply basic_step_loc_eq_dom; eauto. 
    eapply add_co_ws_complE; eauto. }
  symmetry. eapply add_co_ws_compl_loc in xWS; eauto. 
Qed.

Lemma add_co_ws_compl_co_fwcl ews ws w' S S'
      (wf : ES.Wf S) 
      (ACO : add_co ews ws w' S S') : 
  codom_rel (⦗ws_compl ews ws S⦘ ⨾ co S) ⊆₁ ws_compl ews ws S.
Proof. 
  cdes ACO. 
  unfold ws_compl. 
  intros y [x [z [[EQz HH] CO]]]. subst z.
  destruct HH as [[z [z' [[EQz' EWWS] COzx]]] nEWWS]. subst z'.
  red. splits.
  { do 2 eexists. splits. 
    { red. eauto using EWWS. }
    eapply ES.co_trans; eauto. }
  intros EWWSy. apply nEWWS.
  generalize wsCOEWprcl ewsCOprcl EWWSy CO.
  basic_solver 10.
Qed.

Lemma add_co_ws_compl_ew_fwcl ews ws w' S S'
      (wf : ES.Wf S) 
      (AEW : add_ew ews w' S S')
      (ACO : add_co ews ws w' S S') : 
  codom_rel (⦗ws_compl ews ws S⦘ ⨾ ew S) ⊆₁ ws_compl ews ws S.
Proof. 
  cdes AEW; cdes ACO. 
  unfold ws_compl. 
  intros y [x [z [[EQz HH] EW]]]. subst z.
  destruct HH as [[z [z' [[EQz' EWWS] COzx]]] nEWWS]. subst z'.
  red. splits.
  { do 2 eexists. splits. 
    { red. eauto using EWWS. }
    eapply ES.co_ew_in_co; eauto. 
    basic_solver. }
  intros EWWSy. apply nEWWS.
  generalize wsCOEWprcl ewsCOprcl EWWSy ewsEWprcl EW.
  basic_solver 10.
Qed.

Lemma add_co_ws_inter_ws_compl_false ews ws w' S S'
      (wf : ES.Wf S) 
      (ACO : add_co ews ws w' S S') : 
  ws ∩₁ ws_compl ews ws S ⊆₁ ∅.
Proof. unfold ws_compl. basic_solver. Qed.

Lemma add_co_ews_inter_ws_compl_false ews ws w' S S'
      (wf : ES.Wf S) 
      (ACO : add_co ews ws w' S S') : 
  ews ∩₁ ws_compl ews ws S ⊆₁ ∅.
Proof. unfold ws_compl. basic_solver. Qed.

Lemma add_co_ws_cross_ws_compl_in_co ews ws w' e e' S S'
      (wf : ES.Wf S) 
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S')
      (ACO : add_co ews ws w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') : 
  ws × ws_compl ews ws S ⊆ co S.
Proof. 
  cdes AEW; cdes ACO.
  intros x y [xWS yWS].
  destruct 
    (excluded_middle_informative (ew S x y))
    as [EW | nEW].
  { exfalso.
    destruct yWS as [HH nEWWS].
    eapply nEWWS.
    right. eapply add_co_ws_ew_fwcl; eauto. 
    basic_solver 10. }
  edestruct ES.co_total; eauto.
  { eapply add_co_wsEWLoc; eauto. }
  { eapply add_co_ws_complEWLoc; eauto. }
  exfalso. 
  destruct yWS as [HH nEWWS].
  apply nEWWS.
  right. eapply add_co_ws_co_prcl; eauto.
  basic_solver 10. 
Qed.

Lemma add_co_ws_cross_ews_in_ew_compl ews ws w' e e' S S'
      (wf : ES.Wf S)
      (BSTEP : basic_step e e' S S')
      (AEW : add_ew ews w' S S')
      (ACO : add_co ews ws w' S S')
      (wEE' : (eq e ∪₁ eq_opt e') w') :
  ws × ews ⊆ compl_rel (ew S).
Proof.
  cdes AEW; cdes ACO.
  intros x y [xWS yEWS].
  assert (~ ews x) as xnEWS.
  { red. ins. eapply ws_ews; eauto. basic_solver. }
  intros EW. eapply ws_ews; eauto.
  split; [|eauto].
  eapply add_co_ws_ew_fwcl; eauto.
  basic_solver 10.
Qed.

Lemma add_co_ews_cross_ws_compl_in_ew_compl ews ws w' e e' S S'
      (wf : ES.Wf S) 
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S')
      (ACO : add_co ews ws w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') : 
  ews × ws_compl ews ws S ⊆ compl_rel (ew S).
Proof. 
  cdes AEW; cdes ACO.
  intros x y [xEWS yWSC].
  assert (~ ews y) as ynEWS.
  { red. ins. eapply add_co_ews_inter_ws_compl_false; eauto. basic_solver. }
  intros EW. eapply add_co_ews_inter_ws_compl_false; eauto.
  split; [|eauto].
  eapply add_ew_ews_ew_fwcl; eauto.
  basic_solver 10.
Qed.

Lemma add_co_ws_cross_ews_in_co ews ws w' e e' S S'
      (wf : ES.Wf S) 
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S')
      (ACO : add_co ews ws w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') : 
  ws × ews ⊆ co S.
Proof. 
  cdes AEW; cdes ACO.
  intros x y [xWS yEWS].
  assert (~ ew S x y) as nEW.
  { eapply add_co_ws_cross_ews_in_ew_compl; eauto. basic_solver. }
  edestruct ES.co_total as [COxy | COyx]; eauto.
  { eapply add_co_wsEWLoc; eauto. }
  { eapply add_ew_ewsEWLoc; eauto. }
  exfalso. eapply ws_ews.
  split; [|eauto].
  eapply add_co_ws_co_prcl; eauto.
  basic_solver 10.
Qed.

Lemma add_co_ews_cross_ws_compl_in_co ews ws w' e e' S S'
      (wf : ES.Wf S) 
      (BSTEP : basic_step e e' S S') 
      (AEW : add_ew ews w' S S')
      (ACO : add_co ews ws w' S S') 
      (wEE' : (eq e ∪₁ eq_opt e') w') : 
  ews × ws_compl ews ws S ⊆ co S.
Proof. 
  cdes AEW; cdes ACO.
  intros x y [xEWS yWSC].
  assert (~ ew S x y) as nEW.
  { eapply add_co_ews_cross_ws_compl_in_ew_compl; eauto. basic_solver. }
  set (yWSC' := yWSC).
  destruct yWSC' as [[z [z' [[EQz' HA] CO]]] HB]. subst z'.
  destruct HA as [zEWS | zWS].
  { apply ES.ew_co_in_co; auto.
    eexists; splits; eauto. 
    apply ewsEW. basic_solver. }
  edestruct ES.co_total as [COxy | COyx]; eauto.
  { eapply add_ew_ewsEWLoc; eauto. }
  { eapply add_co_ws_complEWLoc; eauto. }
  exfalso. eapply HB.
  right. apply ewsCOprcl. basic_solver 10.
Qed.

Lemma add_co_ews_co_codom ews ws w' S S'
      (wf : ES.Wf S) 
      (AEW : add_ew ews w' S S')
      (ACO : add_co ews ws w' S S') : 
  codom_rel (⦗ews⦘ ⨾ co S) ⊆₁ ws_compl ews ws S. 
Proof. 
  cdes AEW; cdes ACO.
  unfold ws_compl.
  intros x [y [z [[EQz EWS] CO]]]. subst z.
  unfolder; splits; eauto 10.
  intros [EW | WS].
  { eapply ES.ew_co; eauto.
    split; eauto.
    eapply ewsEW. 
    basic_solver. }
  eapply ws_ews. split; [|eauto].
  eapply add_co_ws_co_prcl; eauto. basic_solver 10. 
Qed.

Lemma add_co_ews_co_ws_empty ews ws w' S S'
      (wf : ES.Wf S) 
      (AEW : add_ew ews w' S S')
      (ACO : add_co ews ws w' S S') : 
  ⦗ews⦘ ⨾ co S ⨾ ⦗ws⦘ ⊆ ∅₂.
Proof. 
  cdes AEW; cdes ACO.
  rewrite <- seqA.
  intros x y [z [HA [EQz WSy]]]. subst z.
  eapply add_co_ws_inter_ws_compl_false; eauto.
  split; eauto.
  eapply add_co_ews_co_codom; eauto.
  basic_solver.
Qed.

(******************************************************************************)
(** ** co_delta lemmas *)
(******************************************************************************)

Lemma add_co_co_delta_dom ews ws w' e e' S S'
      (BSTEP : basic_step e e' S S') 
      (ACO : add_co ews ws w' S S') 
      (wf : ES.Wf S) 
      (wEE' : (eq e ∪₁ eq_opt e') w') : 
  dom_rel (co_delta ews ws w' S) ⊆₁ ws ∪₁ eq w'.
Proof. unfold co_delta. basic_solver. Qed.

Lemma add_co_co_delta_codom ews ws w' e e' S S'
      (BSTEP : basic_step e e' S S') 
      (ACO : add_co ews ws w' S S') 
      (wf : ES.Wf S) 
      (wEE' : (eq e ∪₁ eq_opt e') w') : 
  codom_rel (co_delta ews ws w' S) ⊆₁ ws_compl ews ws S ∪₁ eq w'.
Proof. unfold co_delta. basic_solver. Qed.

Lemma add_co_co_deltaEl ews ws w' e e' S S'
      (BSTEP : basic_step e e' S S') 
      (ACO : add_co ews ws w' S S') 
      (wf : ES.Wf S) 
      (wEE' : (eq e ∪₁ eq_opt e') w') : 
  co_delta ews ws w' S ⨾ ⦗E S⦘ ≡ eq w' × ws_compl ews ws S.
Proof. 
  cdes ACO; cdes BSTEP; cdes BSTEP_.
  unfold co_delta. relsf.
  arewrite_false (ws × eq w' ⨾ ⦗E S⦘).
  { unfolder in wEE'; desf; step_solver. }
  relsf. split; [basic_solver|].
  unfolder. ins. desf. splits; auto.
  eapply add_co_ws_complE; eauto.
Qed.  

Lemma add_co_co_deltaEr ews ws w' e e' S S'
      (BSTEP : basic_step e e' S S') 
      (ACO : add_co ews ws w' S S') 
      (wf : ES.Wf S) 
      (wEE' : (eq e ∪₁ eq_opt e') w') : 
  ⦗E S⦘ ⨾ co_delta ews ws w' S ≡ ws × eq w'.
Proof. 
  cdes ACO; cdes BSTEP; cdes BSTEP_.
  unfold co_delta. relsf.
  arewrite_false (⦗E S⦘ ⨾ eq w' × ws_compl ews ws S). 
  { unfolder in wEE'; desf; step_solver. }
  basic_solver 10.
Qed.  
