Require Import Classical Peano_dec Setoid PArith.
From hahn Require Import Hahn.
From imm Require Import AuxRel
     Events Execution Execution_eco imm_s_hb imm_s imm_common
     CombRelations CombRelationsMore
     TraversalConfig Traversal SimTraversal.
Require Import AuxRel AuxDef.

Set Implicit Arguments.

Section Properties.

Variable G : execution.
Variable WF : Wf G.
Variable sc : relation actid.
Variable CON : imm_consistent G sc.

Variable TC : trav_config.
Variable TCCOH : tc_coherent G sc TC.

Notation "'C'" := (covered TC).
Notation "'I'" := (issued TC).

Notation "'E'" := G.(acts_set).
Notation "'sb'" := G.(sb).
Notation "'rf'" := G.(rf).
Notation "'co'" := G.(co).
Notation "'rmw'" := G.(rmw).
Notation "'data'" := G.(data).
Notation "'addr'" := G.(addr).
Notation "'ctrl'" := G.(ctrl).

Notation "'fr'" := G.(fr).
Notation "'coe'" := G.(coe).
Notation "'coi'" := G.(coi).
Notation "'deps'" := G.(deps).
Notation "'rfi'" := G.(rfi).
Notation "'rfe'" := G.(rfe).
Notation "'detour'" := G.(detour).
Notation "'hb'" := G.(hb).
Notation "'sw'" := G.(sw).

Notation "'lab'" := G.(lab).
(* Notation "'loc'" := (loc lab). *)
(* Notation "'val'" := (val lab). *)
(* Notation "'mod'" := (mod lab). *)
(* Notation "'same_loc'" := (same_loc lab). *)

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).

Notation "'Pln'" := (fun a => is_true (is_only_pln lab a)).
Notation "'Rlx'" := (fun a => is_true (is_rlx lab a)).
Notation "'Rel'" := (fun a => is_true (is_rel lab a)).
Notation "'Acq'" := (fun a => is_true (is_acq lab a)).
Notation "'Acqrel'" := (fun a => is_true (is_acqrel lab a)).
Notation "'Acq/Rel'" := (fun a => is_true (is_ra lab a)).
Notation "'Sc'" := (fun a => is_true (is_sc lab a)).

Notation "'Loc_' l" := (fun x => loc lab x = Some l) (at level 1).
Notation "'W_ex'" := G.(W_ex).
Notation "'W_ex_acq'" := (W_ex ∩₁ (fun a => is_true (is_xacq lab a))).

Variable RELCOV : W ∩₁ Rel ∩₁ I ⊆₁ C.

Lemma sw_in_Csw_sb : restr_rel (dom_rel (sb^? ;; <| I |>)) sw ⊆ <| C |> ;; sw ∪ sb.
Proof.
  rewrite restr_relE.
  arewrite (sw ⊆ <| C ∪₁ set_compl C |> ;; sw) at 1.
  { rewrite set_compl_union_id. by rewrite seq_id_l. }
  rewrite id_union. relsf.
  apply union_mori; [basic_solver|].
  unfold imm_s_hb.sw.
  arewrite ((sb ;; ⦗F⦘)^? ⊆ sb ;; ⦗F⦘ ∪ <| fun _ => True |>) by basic_solver.
  rewrite !seq_union_l, !seq_union_r.
  unionL.
  { rewrite !seqA.
    seq_rewrite <- !id_inter. rewrite <- !set_interA.
    arewrite (sb ⨾ ⦗F ∩₁ Acq ∩₁ dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆
              <| C |> ;; sb ⨾ ⦗F ∩₁ Acq ∩₁ dom_rel (sb^? ⨾ ⦗I⦘)⦘).
    { unfolder. ins. desf; splits; auto.
      2,4: by do 2 eexists; splits; eauto.
      2: eapply TCCOH.(dom_sb_covered).
      2: eexists; apply seq_eqv_r; split; eauto.
      all: match goal with H : I _ |- _ => apply TCCOH in H; apply H end.
      all: eexists; apply seq_eqv_r; split; eauto.
      { apply sb_to_f_in_fwbob. apply seq_eqv_r. split; [|split]; auto.
        mode_solver. }
      apply sb_from_f_in_fwbob. apply seq_eqv_l. split; [split|]; auto.
      mode_solver. }
    sin_rewrite release_rf_covered; eauto.
    basic_solver. }
  rewrite seq_id_l.
  arewrite (rf ⊆ <| I ∪₁ set_compl I|> ;; rf).
  { rewrite set_compl_union_id. basic_solver. }
  rewrite id_union. relsf.
  unionL.
  { sin_rewrite release_issued; eauto. basic_solver. }
  rewrite rfi_union_rfe. relsf.
  unionL.
  2: { arewrite (⦗set_compl I⦘ ⨾ rfe ⨾ ⦗Acq⦘ ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆ ∅₂).
       2: basic_solver.
       seq_rewrite <- !id_inter.
       unfolder. ins. desf.
       { match goal with H : I _ |- _ => apply TCCOH.(issuedW) in H end.
         match goal with H : rfe _ _ |- _ =>
                         apply wf_rfeD in H; auto; (destruct_seq H as [XX YY])
         end.
         type_solver. }
       match goal with H : ~ (I _) |- _ => apply H end.
       apply TCCOH.(dom_rfe_acq_sb_issued).
       eexists. eexists. split; eauto.
       apply seq_eqv_l. split; [split|]; auto.
       2: { apply seq_eqv_r. split; eauto. }
       match goal with H : rfe _ _ |- _ =>
                       apply wf_rfeD in H; auto; (destruct_seq H as [XX YY]); auto
       end. }
  unfold release, rs. rewrite !seqA.
  arewrite ((⦗F⦘ ⨾ sb)^? ⊆ ⦗F⦘ ⨾ sb ∪ <| fun _ => True |>)
    by basic_solver.
  rewrite !seq_union_l, !seq_union_r.
  unionL.
  { rewrite !seqA. seq_rewrite <- !id_inter.
    arewrite (dom_rel (sb^? ⨾ ⦗I⦘) ∩₁ set_compl C ∩₁ Rel ∩₁ F ⊆₁ ∅).
    2: by relsf.
    unfolder. ins. desf.
    { match goal with H : I _ |- _ => apply TCCOH.(issuedW) in H end.
      type_solver. }
    match goal with H : ~ (C _) |- _ => apply H end.
    apply TCCOH.(dom_F_sb_issued).
    eexists. apply seq_eqv_l. split; [split; auto|].
    { mode_solver. }
    apply seq_eqv_r. split; eauto. }
  rewrite seq_id_l.

  arewrite (⦗set_compl C⦘ ⨾ ⦗Rel⦘ ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc lab)^? ⨾ ⦗W⦘ ⊆
            ⦗set_compl C⦘ ⨾ ⦗Rel⦘ ⨾ ⦗W⦘ ⨾ (sb ∩ same_loc lab)^? ⨾ ⦗W⦘ ⨾ ⦗set_compl I⦘).
  { unfolder. ins. desf; splits; auto; intros AA.
    all: match goal with H : ~ (C _) |- _ => apply H end.
    { apply RELCOV. split; [split|]; auto. }
    apply TCCOH in AA.
    apply AA. eexists. apply seq_eqv_r. split; eauto.
    apply sb_from_w_rel_in_fwbob.
    apply seq_eqv_l; split; [split|]; auto.
    apply seq_eqv_r; split; [split|]; auto. }
  arewrite (⦗set_compl C⦘ ⨾ ⦗Rel⦘ ⨾ ⦗W⦘ ⊆ ⦗set_compl C ∩₁ Rel ∩₁ W⦘).
  { seq_rewrite <- !id_inter. by rewrite set_interA. }
  arewrite (⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⨾ ⦗set_compl C ∩₁ Rel ∩₁ W⦘ ⨾
               (sb ∩ same_loc lab)^? ⨾ ⦗W⦘ ⊆
            ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⨾ ⦗set_compl C ∩₁ Rel ∩₁ W⦘ ⨾
               (sb ∩ same_loc lab)^? ⨾ ⦗W⦘ ;;
               <| codom_rel  (⦗set_compl C ∩₁ Rel ∩₁ W⦘ ⨾ (sb ∩ same_loc lab)^? ⨾ ⦗W⦘) |>)
    by basic_solver 40.
  arewrite (rfi ⨾ ⦗Acq⦘ ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘ ⊆
            <| dom_rel (rfi ⨾ ⦗Acq⦘ ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘) |> ;;
              rfi ⨾ ⦗Acq⦘ ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘)
    by basic_solver 40.
  arewrite (⦗codom_rel (⦗set_compl C ∩₁ Rel ∩₁ W⦘ ⨾ (sb ∩ same_loc lab)^? ⨾ ⦗W⦘)⦘ ⨾
               ⦗set_compl I⦘ ⨾ (rf ⨾ rmw)＊ ⨾ ⦗set_compl I⦘ ⨾
               ⦗dom_rel (rfi ⨾ ⦗Acq⦘ ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘)⦘ ⊆
            ⦗codom_rel (⦗set_compl C ∩₁ Rel ∩₁ W⦘ ⨾ (sb ∩ same_loc lab)^? ⨾ ⦗W⦘)⦘ ⨾
               ⦗set_compl I⦘ ⨾ (rfi ⨾ rmw ;; <| set_compl I |>)＊ ⨾ ⦗set_compl I⦘ ⨾
               ⦗dom_rel (rfi ⨾ ⦗Acq⦘ ⨾ ⦗dom_rel (sb^? ⨾ ⦗I⦘)⦘)⦘).
  2: { unfold Execution.rfi. rewrite rmw_in_sb; auto.
       arewrite (rf ∩ sb ⨾ sb ⨾ ⦗set_compl I⦘ ⊆ sb).
       { generalize (@sb_trans G). basic_solver. }
       rewrite rt_of_trans. 2: apply (@sb_trans G).
       generalize (@sb_trans G). basic_solver. }
  intros x y HH.
  apply seq_eqv_l in HH. destruct HH as [CODOM HH].
  apply seq_eqv_l in HH. destruct HH as [CIX HH].
  destruct HH as [v [HH DOM]].
  apply seq_eqv_l in DOM. destruct DOM as [CIV [XX DOM]]; subst.
  do 2 (apply seq_eqv_l; split; auto).
  apply seqA.
  do 2 (apply seq_eqv_r; split; auto).
  apply rtE in HH. destruct HH as [HH|HH].
  { inv HH. apply rt_refl. }
  apply inclusion_t_rt.
  induction HH.
  2: { apply ct_ct. eexists. split; eauto.
       specialize (IHHH1 CODOM CIX).
       apply IHHH2.
       2: { eapply codom_eqv1. exists x.
            apply inclusion_ct_seq_eqv_r. eauto. }
       destruct DOM as [v DOM]. destruct_seq DOM as [WV WX].
       exists v.
       apply seq_eqv_l. split; auto.
       apply seq_eqv_r. split.
       all: admit. }

  arewrite (⦗set_compl C ∩₁ Rel ∩₁ W⦘ ⨾ (sb ∩ same_loc lab)^? ⨾
               ⦗W⦘ ⨾ ⦗set_compl I⦘ ⨾ (rf ⨾ rmw)＊ ⊆
          ⦗set_compl C ∩₁ Rel ∩₁ W⦘ ⨾ (sb ∩ same_loc lab)^? ⨾
               ⦗W⦘ ⨾ ⦗set_compl I⦘ ⨾ (rfi ⨾ rmw ;; <| set_compl I |>)＊).
  2: { unfold Execution.rfi. rewrite rmw_in_sb; auto.
       arewrite (rf ∩ sb ⨾ sb ⨾ ⦗set_compl I⦘ ⊆ sb).
       { generalize (@sb_trans G). basic_solver. }
       rewrite rt_of_trans. 2: apply (@sb_trans G).
       generalize (@sb_trans G). basic_solver. }
  assert (<| codom_rel (⦗set_compl C ∩₁ Rel ∩₁ W⦘ ⨾ (sb ∩ same_loc lab)^? ⨾ ⦗W⦘) |> ⨾
                  ⦗set_compl I⦘ ⨾ (rf ⨾ rmw)＊ ⊆
          <| codom_rel (⦗set_compl C ∩₁ Rel ∩₁ W⦘ ⨾ (sb ∩ same_loc lab)^? ⨾ ⦗W⦘) |> ⨾
                  ⦗set_compl I⦘ ⨾ ((rfi ⨾ rmw) ⨾ ⦗set_compl I⦘)＊) as XX.
  2: { arewrite (⦗set_compl C ∩₁ Rel ∩₁ W⦘ ⨾ (sb ∩ same_loc lab)^? ⨾ ⦗W⦘ ⨾
                 ⦗set_compl I⦘ ⨾ (rf ⨾ rmw)＊ ⊆
                 ⦗set_compl C ∩₁ Rel ∩₁ W⦘ ⨾ (sb ∩ same_loc lab)^? ⨾ ⦗W⦘ ⨾
                 ⦗codom_rel (⦗set_compl C ∩₁ Rel ∩₁ W⦘ ⨾ (sb ∩ same_loc lab)^? ⨾ ⦗W⦘)⦘ ⨾
                 ⦗set_compl I⦘ ⨾ (rf ⨾ rmw)＊) by basic_solver 40.
       rewrite XX. basic_solver 40. }

  apply ct_step.
  match goal with H : (rf ⨾ rmw) _ _ |- _ => destruct H as [v [RF RMW]] end.
  apply rfi_union_rfe in RF. destruct RF as [RF|RF].
Admitted.


End Properties.