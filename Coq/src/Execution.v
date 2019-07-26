From hahn Require Import Hahn.
From imm Require Import Events AuxRel.
(* TODO : get rid of dependency on Step, move corresponding lemmas to Step.v *)
Require Import AuxDef.
Require Import AuxRel.
Require Import EventStructure.
Require Import Consistency.

Module Execution.

Section Execution.

Variable S : ES.t.

Notation "'E'" := S.(ES.acts_set).
Notation "'Einit'" := S.(ES.acts_init_set).
Notation "'Eninit'" := S.(ES.acts_ninit_set).

Notation "'lab'" := S.(ES.lab).

Notation "'sb'" := S.(ES.sb).
Notation "'rmw'" := S.(ES.rmw).
Notation "'ew'" := S.(ES.ew).
Notation "'jf'" := S.(ES.jf).
Notation "'rf'" := S.(ES.rf).
Notation "'fr'" := S.(ES.fr).
Notation "'co'" := S.(ES.co).
Notation "'cf'" := S.(ES.cf).

Notation "'sw'" := S.(sw).
Notation "'hb'" := S.(hb).

Notation "'jfe'" := S.(ES.jfe).
Notation "'rfe'" := S.(ES.rfe).
Notation "'coe'" := S.(ES.coe).
Notation "'jfi'" := S.(ES.jfi).
Notation "'rfi'" := S.(ES.rfi).
Notation "'coi'" := S.(ES.coi).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'mod'" := (mod lab).

Notation "'same_tid'" := S.(ES.same_tid).
Notation "'same_lab'" := S.(ES.same_lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).

Notation "'Loc_' l" := (fun x => loc x = l) (at level 1).

Notation "'Pln'" := (fun a => is_true (is_only_pln S.(ES.lab) a)) (at level 10).
Notation "'Rlx'" := (fun a => is_true (is_rlx S.(ES.lab) a)) (at level 10).
Notation "'Rel'" := (fun a => is_true (is_rel S.(ES.lab) a)) (at level 10).
Notation "'Acq'" := (fun a => is_true (is_acq S.(ES.lab) a)) (at level 10).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel S.(ES.lab) a)) (at level 10).
Notation "'Sc'" := (fun a => is_true (is_sc S.(ES.lab) a)) (at level 10).

Record t (X : eventid -> Prop) :=
  mk { ex_inE : X ⊆₁ E ;
       init_in_ex : Einit ⊆₁ X ;

       ex_sb_prcl : dom_rel (sb ⨾ ⦗X⦘) ⊆₁ X ;
       ex_sw_prcl : dom_rel (sw ⨾ ⦗X⦘) ⊆₁ X ;
       
       ex_rmw_fwcl : codom_rel (⦗X⦘ ⨾ rmw) ⊆₁ X ;

       ex_rf_compl : X ∩₁ R ⊆₁ codom_rel (⦗X⦘ ⨾ rf) ;
       
       ex_ncf : ES.cf_free S X ; 

       ex_vis : X ⊆₁ vis S ;
     }.

Lemma co_total (WF : ES.Wf S) X (exec : t X) : 
  forall ol, is_total (X ∩₁ W ∩₁ Loc_ ol) co. 
Proof. 
  red. ins. 
  unfolder in IWa.
  unfolder in IWb.
  desc.
  edestruct ES.co_total; eauto.
  { unfolder; splits; eauto. 
    eapply ex_inE; eauto. }
  { unfolder; splits; eauto. 
    eapply ex_inE; eauto. }
  intros EW.
  apply ES.ewc in EW; auto.
  destruct EW as [EQ | CF]; auto.
  eapply ex_ncf; eauto.
  basic_solver.
Qed.

Lemma hb_prcl X (exec : t X) : 
  dom_rel (hb ⨾ ⦗X⦘) ⊆₁ X.
Proof. 
  rewrite seq_eqv_r.
  intros x [y [HB yX]].
  induction HB as [x y [SB | SW] | ]; auto.
  { apply ex_sb_prcl; auto. basic_solver 10. }
  apply ex_sw_prcl; auto. basic_solver 10. 
Qed.


Section ExecutionRels.

  Variable X : eventid -> Prop.
  Variable EXEC : t X.

  Definition ex_Einit := Einit.
  Definition ex_Eninit := Eninit ∩₁ X.

  Definition ex_rmw := restr_rel X rmw.
  Definition ex_sb := restr_rel X sb.
  Definition ex_jf := restr_rel X jf.
  Definition ex_co := restr_rel X co.
  Definition ex_ew := restr_rel X ew.

  Definition ex_same_tid := restr_rel X same_tid.
  Definition ex_cf := ⦗ex_Eninit⦘ ⨾ (ex_same_tid \ ex_sb⁼) ⨾ ⦗ex_Eninit⦘.
  Definition ex_rf := ex_ew ⨾ ex_jf \ ex_cf.
  Definition ex_fr := ex_rf⁻¹ ⨾ ex_co.
  Definition ex_rs := ⦗X ∩₁ W⦘ ⨾ (ex_sb ∩ same_loc)^? ⨾ ⦗W⦘ ⨾ (ex_jf ⨾ ex_rmw)＊.
  Definition ex_release := ⦗Rel⦘ ⨾ (⦗F⦘ ⨾ ex_sb)^? ⨾ ex_rs.
  Definition ex_sw := ex_release ⨾ ex_jf ⨾ (ex_sb ⨾ ⦗F⦘)^? ⨾ ⦗Acq⦘.
  Definition ex_hb := (ex_sb ∪ ex_sw)⁺.

  Definition ex_jfe := ex_jf \ ex_sb.
  Definition ex_rfe := ex_rf \ ex_sb.
  Definition ex_coe := ex_co \ ex_sb.

  Definition ex_jfi := ex_jf ∩ ex_sb.
  Definition ex_rfi := ex_rf ∩ ex_sb.
  Definition ex_coi := ex_co ∩ ex_sb.

End ExecutionRels.

End Execution.
End Execution.
