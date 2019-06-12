From hahn Require Import Hahn.
From imm Require Import Events AuxRel Prog ProgToExecutionProperties.
(* TODO : get rid of dependency on Step, move corresponding lemmas to Step.v *)
Require Import AuxDef.
Require Import AuxRel.
Require Import EventStructure.
Require Import Consistency.
Require Import Execution.


Module Races.
  
Section Races.


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

Definition one {A : Type} (X : A -> Prop) a b := X a \/ X b. 

Definition race (X : eventid -> Prop) :=
  dom_rel ((X × X) \ (hb⁼ ∪ cf) ∩ same_loc ∩ one W). (* hb should be hbc11? *)

Definition RLX_race_free (X : eventid -> Prop) :=
  race X ⊆₁ (Rel ∩₁ W) ∪₁ (Acq ∩₁ R). 
       
Definition RA_race_free (X : eventid -> Prop) :=
  race X ⊆₁ Sc.

End Races.
End Races.

Definition program_execution P X := exists S : ES.t,
    ⟪ steps : (step Weakestmo)＊ (prog_es_init P) S ⟫ /\
    ⟪ exec : Execution.t S X ⟫. 
                                             
                                            
   ⟪ STEPS : (step Weakestmo)＊ (prog_g_es_init prog G) S ⟫ /\
      
Definition RLX_race_free_program (P : Prog.t) :=
  forall X : eventid -> Prop, 
Lemma DRF_rlx (P : Prog.t)
              (r11_cons: forall X : eventid -> Prop, program_execution P X) : False
             ((step Weakestmo)＊ ES.)
Proof.

Qed.
 

Lemma rf_in_jf (S : ES.t) (X : eventid -> Prop)
      (wf : ES.Wf S)
      (exec : Execution.t S X)
      (p : S.(ES.jf) ⊆ S.(hb)):
  (⦗X⦘ ⨾ S.(ES.rf) ⨾ ⦗X⦘) ⊆ S.(ES.jf).
Proof. unfold "⊆". intros. SearchAbout eqv_rel "⨾".
       unfold eqv_rel in H. unfold "⨾" in H.


       destruct H. destruct H. destruct H. subst. destruct H0.
       destruct H. destruct H0. subst.

       unfold ES.rf in H.
       unfold "⨾" in H.  repeat destruct H. rewrite p in H. 


       repeat destruct H0. destruct H. destruct H0. subst. destruct H. destruct H0.
  unfold ES.rf. SearchAbout .
