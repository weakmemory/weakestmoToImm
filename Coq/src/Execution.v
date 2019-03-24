From hahn Require Import Hahn.
From imm Require Import Events AuxRel.
(* TODO : get rid of dependency on Step, move corresponding lemmas to Step.v *)
Require Import AuxDef AuxRel EventStructure Consistency BasicStep Step.

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

Notation "'Pln'" := (fun a => is_true (is_only_pln S.(ES.lab) a)) (at level 10).
Notation "'Rlx'" := (fun a => is_true (is_rlx S.(ES.lab) a)) (at level 10).
Notation "'Rel'" := (fun a => is_true (is_rel S.(ES.lab) a)) (at level 10).
Notation "'Acq'" := (fun a => is_true (is_acq S.(ES.lab) a)) (at level 10).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel S.(ES.lab) a)) (at level 10).
Notation "'Sc'" := (fun a => is_true (is_sc S.(ES.lab) a)) (at level 10).

Record t (X : eventid -> Prop) :=
  mk { Ex_inE : X ⊆₁ E ;
       init_inEx : Einit ⊆₁ X ;

       Ex_sb_prcl : dom_rel (sb ⨾ ⦗X⦘) ⊆₁ X ;
       Ex_sw_prcl : dom_rel (sw ⨾ ⦗X⦘) ⊆₁ X ;
       
       Ex_rmw_fwcl : codom_rel (⦗X⦘ ⨾ rmw) ⊆₁ X ;

       Ex_rf_compl : X ∩₁ R ⊆₁ codom_rel (⦗X⦘ ⨾ rf) ;
       
       Ex_ncf : ES.cf_free S X ; 

       Ex_vis : X ⊆₁ vis S ;
     }.

Lemma hb_prcl X (exec : t X) : 
  dom_rel (hb ⨾ ⦗X⦘) ⊆₁ X.
Proof. 
  rewrite seq_eqv_r.
  intros x [y [HB yX]].
  induction HB as [x y [SB | SW] | ]; auto.
  { apply Ex_sb_prcl; auto. basic_solver 10. }
  apply Ex_sw_prcl; auto. basic_solver 10. 
Qed.

End Execution.

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

Notation "'same_mod' S" := (same_mod S.(ES.lab)) (at level 10).
Notation "'same_loc' S" := (same_loc S.(ES.lab)) (at level 10).
Notation "'same_val' S" := (same_val S.(ES.lab)) (at level 10).

Notation "'K' S" := (S.(ES.cont_set)) (at level 10).

Notation "'Tid' S" := (fun t e => S.(ES.tid) e = t) (at level 9).
Notation "'Mod_' S" := (fun m x => mod S x = m) (at level 9).
Notation "'Loc_' S" := (fun l x => loc S x = l) (at level 9).
Notation "'Val_' S" := (fun v e => val S e = v) (at level 9).

Lemma step_preserves X e e' S S' 
      (WF : ES.Wf S)
      (EXEC : t S X) 
      (BSTEP : ESBasicStep.t e e' S S')
      (STEP : ESstep.t_ e e' S S') :
  t S' X.
Proof.       
  cdes BSTEP; cdes BSTEP_.
  constructor.
  { etransitivity; [apply EXEC |].
    eapply ESBasicStep.basic_step_acts_set_mon; eauto. }
  { erewrite ESBasicStep.basic_step_acts_init_set; eauto. apply EXEC. } 
  { rewrite SB'. 
    relsf. splits.
    { apply EXEC. }
    arewrite (X ⊆₁ E S) by apply Ex_inE; auto.
    erewrite ESBasicStep.basic_step_sb_deltaE; eauto. 
    basic_solver. }
  { (* TODO: add a corresponding lemma  *)
    arewrite (sw S' ≡ sw S ∪ ESstep.sw_delta S S' k e e').
    { destruct STEP as [FSTEP | [LSTEP | [SSTEP | USTEP]]].
      { cdes FSTEP. erewrite ESstep.step_same_jf_sw; eauto.
        eapply ESBasicStep.basic_step_nupd_rmw; subst; eauto. }
      { cdes LSTEP. erewrite ESstep.step_add_jf_sw; eauto.
        subst. basic_solver. }
      { cdes SSTEP. erewrite ESstep.step_same_jf_sw; eauto.
        eapply ESBasicStep.basic_step_nupd_rmw; subst; eauto. }
      cdes USTEP. erewrite ESstep.step_add_jf_sw; eauto.
      cdes AEW. type_solver. }
    relsf. splits.
    { apply EXEC. }
    arewrite (X ⊆₁ E S) by apply Ex_inE; auto.
    erewrite ESstep.basic_step_sw_deltaE; eauto. 
    basic_solver. }
  { admit. }
  { admit. }
  { red. 
    rewrite <- set_interK with (s := X).
    rewrite id_inter.
    arewrite (X ⊆₁ E S) at 2 by apply Ex_inE; auto. 
    arewrite (X ⊆₁ E S) at 2 by apply Ex_inE; auto. 
    arewrite (⦗E S⦘ ⨾ cf S' ⨾ ⦗E S⦘ ≡ cf S).
    { rewrite <- restr_relE. erewrite ESBasicStep.basic_step_cf_restr; eauto. }
    apply EXEC. }
  etransitivity.
  { eapply Ex_vis; eauto. }
  eapply ESstep.step_vis_mon; eauto. 
Admitted.

End Execution.