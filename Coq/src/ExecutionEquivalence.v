Require Import Program.Basics.

From hahn Require Import Hahn.
From imm Require Import Events Prog Execution RC11.
Require Import AuxRel.
Require Import EventStructure.
Require Import Execution.
Require Import ProgES.
Require Import EventToAction.
Require Import AuxDef.
Require Import Logic.FinFun.
Require Import Omega.
Require Import Consistency.
Require Import ExecutionToG.
Require Import SC.

Local Open Scope program_scope.

Section ExecutionEquivalence.

Variable G G' : execution.

Notation "'E'" := G.(acts_set).
Notation "'Einit'" := (is_init ∩₁ E).
Notation "'Eninit'" := ((set_compl is_init) ∩₁ E).

Notation "'lab'" := (Execution.lab G).
Notation "'loc'" := (Events.loc (lab G)).
Notation "'tid'" := (Events.tid).

Notation "'Tid' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid' t" := (fun x => tid x <> t) (at level 1).
Notation "'Loc_' l" := (fun x => loc x = l) (at level 1).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).

Notation "'Gsame_loc'" := (same_loc lab).

Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).

Notation "'sb'" := (Execution.sb G).
Notation "'rmw'" := (Execution.rmw G).
Notation "'rf'" := (Execution.rf G).
Notation "'fr'" := (Execution.fr G).
Notation "'co'" := (Execution.co G).
Notation "'eco'" := (Execution_eco.eco G).

Notation "'rs'" := (imm_s_hb.rs G).
Notation "'release'" := (imm_s_hb.release G).
Notation "'sw'" := (imm_s_hb.sw G).
Notation "'hb'" := (imm_s_hb.hb G).

Notation "'psc_f'" := (imm_s.psc_f G).
Notation "'scb'" :=  (imm_s.scb G).
Notation "'psc_base'" := (imm_s.psc_base G).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).




Notation "'E''" := G'.(acts_set).
Notation "'Einit''" := (is_init ∩₁ E').
Notation "'Eninit''" := ((set_compl is_init) ∩₁ E').

Notation "'lab''" := (Execution.lab G').
Notation "'loc''" := (Events.loc (lab G')).
Notation "'tid''" := (Events.tid).

Notation "'Tid'' t" := (fun x => tid' x = t) (at level 1).
Notation "'NTid'' t" := (fun x => tid' x <> t) (at level 1).
Notation "'Loc_'' l" := (fun x => loc' x = l) (at level 1).

Notation "'R''" := (fun a => is_true (is_r lab' a)).
Notation "'R_ex''" := (fun a => is_true (R_ex lab' a)).
Notation "'W''" := (fun a => is_true (is_w lab' a)).
Notation "'F''" := (fun a => is_true (is_f lab' a)).

Notation "'Gsame_loc''" := (same_loc lab').

Notation "'Rel''" := (fun a => is_true (is_rel lab' a)).
Notation "'Acq''" := (fun a => is_true (is_acq lab' a)).

Notation "'sb''" := (Execution.sb G').
Notation "'rmw''" := (Execution.rmw G').
Notation "'rf''" := (Execution.rf G').
Notation "'fr''" := (Execution.fr G').
Notation "'co''" := (Execution.co G').
Notation "'eco''" := (Execution_eco.eco G').

Notation "'rs''" := (imm_s_hb.rs G').
Notation "'release''" := (imm_s_hb.release G').
Notation "'sw''" := (imm_s_hb.sw G').
Notation "'hb''" := (imm_s_hb.hb G').

Notation "'psc_f''" := (imm_s.psc_f G').
Notation "'scb''" :=  (imm_s.scb G').
Notation "'psc_base''" := (imm_s.psc_base G').
Notation "'Sc''" := (fun a => is_true (is_sc lab' a)).

Definition X_EQUIV :=
  ⟪ ACTS : E ≡₁ E' ⟫ /\
  ⟪ LAB  : eq_dom E lab lab' ⟫ /\
  ⟪ SB   : sb  ≡  sb' ⟫ /\
  ⟪ RMW  : rmw ≡ rmw' ⟫ /\
  ⟪ RF   : rf  ≡ rf' ⟫ /\
  ⟪ CO   : co  ≡ co' ⟫.

Variable EQUIV : X_EQUIV.

Lemma lab_set_x_equiv
      (p : forall {A}, (A -> label) -> A -> Prop)
      (p_lab : label -> Prop)
      (EQ : forall {A} (sup : A -> label) a, (p sup a) = (p_lab (sup a))) :
  E ∩₁ (fun a => p lab a) ≡₁ E' ∩₁ (fun a => p lab' a).
Proof.
  cdes EQUIV.
  unfolder.
  split.
  all: intros x [Ex HH].
  all: splits; [by apply ACTS|].
  all: assert (LAB_EQ : lab' x = lab x).
  1,3: by rewrite LAB; auto; apply ACTS.
  all: rewrite EQ; rewrite EQ in HH.
  { by rewrite LAB_EQ. }
    by rewrite <- LAB_EQ.
Qed.

Lemma lab_rel_x_equiv
      (p : forall {A}, (A -> label) -> A -> A -> Prop)
      (p_lab : label -> label -> Prop)
      (EQ : forall {A} (sup : A -> label) a b, (p sup a b) = (p_lab (sup a) (sup b))) :
  restr_rel E (fun a b => p lab a b) ≡ restr_rel E' (fun a b => p lab' a b).
Proof.
  cdes EQUIV.
  unfolder.
  split.
  all: intros x y [HH [Ex Ey]].
  all: splits; [| by apply ACTS | by apply ACTS].
  all: assert (LAB_EQx : lab' x = lab x).
  1,3: by rewrite LAB; auto; apply ACTS.
  all: assert (LAB_EQy : lab' y = lab y).
  1,3: by rewrite LAB; auto; apply ACTS.
  all: rewrite EQ; rewrite EQ in HH.
  { by rewrite LAB_EQx, LAB_EQy. }
  by rewrite <- LAB_EQx, <- LAB_EQy.
Qed.

Lemma R_x_equiv :
  E ∩₁ R ≡₁ E' ∩₁ R'.
Proof.
  set (f := fun x => match x with
                  | Aload _ _ _ _ => true
                  | _ => false end).
  erewrite lab_set_x_equiv
    with (p := is_r) (p_lab := f); eauto.
Qed.

Lemma W_x_equiv :
  E ∩₁ W ≡₁ E' ∩₁ W'.
Proof.
  set (f := fun x => match x with
                  | Astore _ _ _ _ => true
                  | _ => false end).
  erewrite lab_set_x_equiv
    with (p := is_w) (p_lab := f); eauto.
Qed.

Lemma F_x_equiv :
  E ∩₁ F ≡₁ E' ∩₁ F'.
Proof.
  set (f := fun x => match x with
                  | Afence _ => true
                  | _ => false end).
  erewrite lab_set_x_equiv
    with (p := is_f) (p_lab := f); eauto.
Qed.

Lemma Acq_x_equiv :
 E ∩₁ Acq ≡₁ E' ∩₁ Acq'.
Proof.
  set (f := fun x => let m :=
                      match x with
                      | Aload  _ o _ _ => o
                      | Astore _ o _ _ => o
                      | Afence o => o
                      end
                  in mode_le Oacq m).
  erewrite lab_set_x_equiv
    with (p := is_acq) (p_lab := f); eauto.
Qed.

Lemma Rel_x_equiv :
 E ∩₁ Rel ≡₁ E' ∩₁ Rel'.
Proof.
  set (f := fun x => let m :=
                      match x with
                      | Aload  _ o _ _ => o
                      | Astore _ o _ _ => o
                      | Afence o => o
                      end
                  in mode_le Orel m).
  erewrite lab_set_x_equiv
    with (p := is_rel) (p_lab := f); eauto.
Qed.

Lemma Sc_x_equiv :
      E ∩₁ Sc ≡₁ E' ∩₁ Sc'.
Proof.
  set (f := fun x => let m :=
                      match x with
                      | Aload  _ o _ _ => o
                      | Astore _ o _ _ => o
                      | Afence o => o
                      end
                  in mode_le Osc m).
  erewrite lab_set_x_equiv
    with (p := is_sc) (p_lab := f); eauto.
Qed.

Lemma same_loc_x_equiv :
  restr_rel E Gsame_loc ≡ restr_rel E' Gsame_loc'.
Proof.
  set (loc_l := fun (l : label) =>
                  match l with
                  | Aload _ _ l _ | Astore _ _ l _ => Some l
                  | Afence _ => None
                  end).
  set (f := fun (l1 : label) (l2 : label) => loc_l l1 = loc_l l2).
  erewrite lab_rel_x_equiv with (p_lab := f); eauto.
Qed.

Lemma rs_x_equiv
      (WF : Wf G)
      (WF' : Wf G') :
  rs ⨾ ⦗E⦘ ≡ rs' ⨾ ⦗E'⦘.
Proof.
  cdes EQUIV.
  unfold imm_s_hb.rs.
  arewrite (sb ∩ Gsame_loc ≡ sb ∩ restr_rel E Gsame_loc).
  2 : arewrite (sb' ∩ Gsame_loc' ≡ sb' ∩ restr_rel E' Gsame_loc').
  1,2 : rewrite wf_sbE, restr_relE; basic_solver.
  specialize prcl_fwcl_swap with (s := E) as HH.
  specialize prcl_fwcl_swap with (s := E') as HH'.
  rewrite HH, HH'.
  2,4 : apply prcl_rt; rewrite wf_rfE; basic_solver.
  2,3 : apply fwcl_rt; rewrite wf_rmwE; basic_solver.
  arewrite (⦗W⦘ ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ ⦗E ∩₁ W⦘) by basic_solver.
  arewrite (⦗W'⦘ ⨾ ⦗E'⦘ ≡ ⦗E'⦘ ⨾ ⦗E' ∩₁ W'⦘) by basic_solver.
  seq_rewrite HH.
  seq_rewrite HH'.
  2,4 : apply prcl_cr; rewrite wf_sbE; basic_solver.
  2,3 : apply fwcl_cr; basic_solver.
  rewrite !seqA.
  arewrite (⦗W⦘ ⨾ ⦗E⦘ ≡ ⦗E ∩₁ W⦘) by basic_solver.
  arewrite (⦗W'⦘ ⨾ ⦗E'⦘ ≡ ⦗E' ∩₁ W'⦘) by basic_solver.
  by rewrite SB, W_x_equiv, same_loc_x_equiv, RMW, RF.
Qed.

Lemma release_x_equiv
      (WF : Wf G)
      (WF' : Wf G') :
  release ⨾ ⦗E⦘ ≡ release' ⨾ ⦗E'⦘.
Proof.
  unfold imm_s_hb.release.
  rewrite !seqA.
  rewrite !rsE_alt_restr; auto.
  rewrite !restr_relE.

  specialize prcl_fwcl_swap with (s := E)
                                 (r := (⦗F⦘ ⨾ sb)^?) as HH.
  specialize prcl_fwcl_swap with (s := E')
                                 (r := (⦗F'⦘ ⨾ sb')^?)as HH'.
  seq_rewrite HH.
  seq_rewrite HH'.
  2,4: apply prcl_cr.
  4,5: apply fwcl_cr.
  2-5: rewrite wf_sbE; basic_solver.
  rewrite (dom_l G.(wf_sbE)).
  rewrite (dom_l G'.(wf_sbE)).
  rewrite !seqA.
  arewrite (⦗Rel⦘ ⨾ ⦗E⦘ ≡ ⦗E ∩₁ Rel⦘) by basic_solver.
  arewrite (⦗Rel'⦘ ⨾ ⦗E'⦘ ≡ ⦗E' ∩₁ Rel'⦘) by basic_solver.
  arewrite (⦗F⦘ ⨾ ⦗E⦘ ≡ ⦗E ∩₁ F⦘) by basic_solver.
  arewrite (⦗F'⦘ ⨾ ⦗E'⦘ ≡ ⦗E' ∩₁ F'⦘) by basic_solver.
  cdes EQUIV.
    by rewrite Rel_x_equiv, F_x_equiv, rs_x_equiv, SB.
Qed.

Lemma sw_x_equiv
      (WF : Wf G)
      (WF' : Wf G') :
  sw ≡ sw'.
Proof.
  cdes EQUIV.
  unfold imm_s_hb.sw.
  rewrite WF.(wf_rfE), WF'.(wf_rfE).
  rewrite !seqA.
  specialize prcl_fwcl_swap with (s := E) (r := (sb ⨾ ⦗F⦘)^?) as HH.
  specialize prcl_fwcl_swap with (s := E') (r := (sb' ⨾ ⦗F'⦘)^?) as HH'.
  seq_rewrite <- HH.
  seq_rewrite <- HH'.
  2,4: apply prcl_cr.
  4,5: apply fwcl_cr.
  2-5: rewrite wf_sbE; basic_solver.
  rewrite (dom_r G.(wf_sbE)), (dom_r G'.(wf_sbE)).
  rewrite !seqA.
  rewrite <- !id_inter.
  seq_rewrite release_x_equiv; auto.
  by rewrite RF, SB, F_x_equiv, Acq_x_equiv, seqA.
Qed.

Lemma hb_x_equiv
      (WF : Wf G)
      (WF' : Wf G') :
  hb ≡ hb'.
Proof.
  cdes EQUIV.
  unfold imm_s_hb.hb.
  by rewrite SB, sw_x_equiv.
Qed.

Lemma fr_x_equiv :
  fr ≡ fr'.
Proof.
  cdes EQUIV.
  unfold Execution.fr.
  by rewrite !RF, !CO.
Qed.

Lemma eco_x_equiv :
  eco ≡ eco'.
Proof.
  cdes EQUIV.
  unfold Execution_eco.eco.
  by rewrite !RF, !CO, fr_x_equiv.
Qed.


Lemma scb_x_equiv
      (WF : Wf G)
      (WF' : Wf G') :
  scb ≡ scb'.
Proof.
  cdes EQUIV.
  unfold imm_s.scb.
  rewrite G.(wf_sbE), G'.(wf_sbE).
  rewrite <- !restr_relE.
  rewrite <- !restr_minus_alt, !restr_minus.
  arewrite (hb ∩ Gsame_loc ≡ hb ∩ restr_rel E Gsame_loc).
  { rewrite imm_s_hb.wf_hbE; basic_solver. }
  arewrite (hb' ∩ Gsame_loc' ≡ hb' ∩ restr_rel E' Gsame_loc').
  { rewrite imm_s_hb.wf_hbE; basic_solver. }
  by rewrite same_loc_x_equiv, ACTS, SB, hb_x_equiv, CO, fr_x_equiv.
Qed.

Lemma psc_base_x_equiv
      (WF : Wf G)
      (WF' : Wf G') :
  psc_base ≡ psc_base'.
Proof.
  unfold imm_s.psc_base.
  rewrite (scbE G WF), (scbE G' WF'), !seqA.
  specialize prcl_fwcl_swap with (s := E) (r := (⦗F⦘ ⨾ hb)^?) as HH.
  specialize prcl_fwcl_swap with (s := E') (r := (⦗F'⦘ ⨾ hb')^?) as HH'.
  seq_rewrite HH.
  seq_rewrite HH'.
  2,4: apply prcl_cr.
  4,5: apply fwcl_cr.
  2-5: rewrite imm_s_hb.wf_hbE; basic_solver.
  clear HH HH'.
  specialize prcl_fwcl_swap with (s := E) (r := (hb ⨾ ⦗F⦘)^?) as HH.
  specialize prcl_fwcl_swap with (s := E') (r := (hb' ⨾ ⦗F'⦘)^?) as HH'.
  seq_rewrite <- HH.
  seq_rewrite <- HH'.
  2,4: apply prcl_cr.
  4,5: apply fwcl_cr.
  2-5: rewrite imm_s_hb.wf_hbE; basic_solver.
  rewrite WF.(imm_s_hb.wf_hbE).
  rewrite WF'.(imm_s_hb.wf_hbE).
  rewrite !seqA.
  arewrite (⦗Sc⦘ ⨾ ⦗E⦘ ≡ ⦗E ∩₁ Sc⦘) by basic_solver.
  arewrite (⦗Sc'⦘ ⨾ ⦗E'⦘ ≡ ⦗E' ∩₁ Sc'⦘) by basic_solver.
  arewrite (⦗F⦘ ⨾ ⦗E⦘ ≡ ⦗E ∩₁ F⦘) by basic_solver.
  arewrite (⦗F'⦘ ⨾ ⦗E'⦘ ≡ ⦗E' ∩₁ F'⦘) by basic_solver.
  seq_rewrite <- !id_inter.
  cdes EQUIV.
  by rewrite Sc_x_equiv, F_x_equiv, scb_x_equiv, hb_x_equiv, ACTS.
Qed.

Lemma psc_f_x_equiv
      (WF : Wf G)
      (WF' : Wf G') :
  psc_f ≡ psc_f'.
Proof.
  unfold imm_s.psc_f.
  rewrite WF.(imm_s_hb.wf_hbE) at 1.
  rewrite WF'.(imm_s_hb.wf_hbE) at 1.
  rewrite !seqA.
  specialize prcl_fwcl_swap with (s := E) (r := (eco ⨾ hb)^?) as HH.
  specialize prcl_fwcl_swap with (s := E') (r := (eco' ⨾ hb')^?) as HH'.
  seq_rewrite <- HH.
  seq_rewrite <- HH'.
  2,4: apply prcl_cr.
  4,5: apply fwcl_cr.
  2-5: rewrite imm_s_hb.wf_hbE, Execution_eco.wf_ecoE; basic_solver.
  rewrite !seqA.
  arewrite (⦗E⦘ ⨾ ⦗F ∩₁ Sc⦘ ≡ ⦗E ∩₁ F ∩₁ (E ∩₁ Sc)⦘) by basic_solver.
  arewrite (⦗F ∩₁ Sc⦘ ⨾ ⦗E⦘ ≡ ⦗E ∩₁ F ∩₁ (E ∩₁ Sc)⦘) by basic_solver.
  arewrite (⦗F' ∩₁ Sc'⦘ ⨾ ⦗E'⦘ ≡ ⦗E' ∩₁ F' ∩₁ (E' ∩₁ Sc')⦘) by basic_solver.
  arewrite (⦗E'⦘ ⨾ ⦗F' ∩₁ Sc'⦘ ≡ ⦗E' ∩₁ F' ∩₁ (E' ∩₁ Sc')⦘) by basic_solver.
  by rewrite !F_x_equiv, Sc_x_equiv, hb_x_equiv, eco_x_equiv.
Qed.

Lemma complete_x_equiv
      (COMPLETE : complete G) :
  complete G'.
Proof.
  cdes EQUIV.
  red. rewrite <- R_x_equiv, <- RF.
  apply COMPLETE.
Qed.

Lemma coherence_x_equiv
      (WF : Wf G)
      (WF' : Wf G')
      (COHERENCE : imm_s_hb.coherence G) :
  imm_s_hb.coherence G'.
Proof.
  red.
  by rewrite <- hb_x_equiv, <- eco_x_equiv.
Qed.

Lemma rmw_atomicity_x_equiv
      (RMW_AT : rmw_atomicity G) :
  rmw_atomicity G'.
Proof.
  cdes EQUIV.
  red.
  rewrite <- RMW, <- SB, <- CO, <- fr_x_equiv.
  apply RMW_AT.
Qed.

Lemma psc_acyclic_x_equiv
      (WF : Wf G)
      (WF' : Wf G')
      (PSC_ACYCLIC : acyclic (psc_f ∪ psc_base)) :
  acyclic (psc_f' ∪ psc_base').
Proof. by rewrite <- psc_base_x_equiv, <- psc_f_x_equiv. Qed.


Lemma sb_rf_acyclic_x_equiv
      (SB_RF_ACYCLIC : acyclic (sb ∪ rf)) :
  acyclic (sb' ∪ rf').
Proof. cdes EQUIV. by rewrite <- SB, <- RF. Qed.

Lemma rc11_x_equiv
      (WF : Wf G)
      (WF' : Wf G')
      (RC11 : rc11_consistent G) :
  rc11_consistent G'.
Proof.
  red. splits.
  { apply complete_x_equiv, RC11. }
  { by apply coherence_x_equiv, RC11. }
  { apply rmw_atomicity_x_equiv, RC11. }
  { by apply psc_acyclic_x_equiv, RC11. }
  apply sb_rf_acyclic_x_equiv, RC11.
Qed.

Lemma sc_x_equiv
      (WF : Wf G)
      (WF' : Wf G')
      (SC : sc_consistent G) :
  sc_consistent G'.
Proof.
  red. splits.
  { apply complete_x_equiv, SC. }
  { apply rmw_atomicity_x_equiv, SC. }
  cdes EQUIV.
  rewrite <- SB, <- RF, <- CO, <- fr_x_equiv.
  apply SC.
Qed.

End ExecutionEquivalence.


Lemma X_EQUIV_eqivalence : equivalence execution X_EQUIV.
Proof.
  constructor.
  { unfold X_EQUIV. basic_solver. }
  { red. intros G1 G2 G3 EQ12 EQ23.
    cdes EQ12. cdes EQ23. red. splits.
    2: { unfolder in *. ins. desf. rewrite LAB; auto. }
    all: unfolder in *; basic_solver. }
  red. intros G1 G2 EQ.
  cdes EQ. red. splits.
  2: { rewrite <- ACTS. unfolder. ins. by rewrite LAB. }
  all: unfolder in *; basic_solver.
Qed.
