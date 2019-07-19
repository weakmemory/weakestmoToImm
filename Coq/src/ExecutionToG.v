Require Import Program.Basics.

From hahn Require Import Hahn.
From imm Require Import Events AuxRel Prog Execution.
Require Import AuxRel.
Require Import EventStructure.
Require Import Execution.
Require Import ProgES.
Require Import EventToAction.
Require Import AuxDef.
Require Import Logic.FinFun.
Require Import Omega.

Local Open Scope program_scope.

Section ExecutionToGraph. 
  
Variable S : ES.t.
Variable X : eventid -> Prop.
Variable G : execution.
  

Notation "'GE'" := G.(acts_set).
Notation "'GEinit'" := (is_init ∩₁ GE).
Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).

Notation "'Glab'" := (Execution.lab G).
Notation "'Gloc'" := (Events.loc (lab G)).
Notation "'Gtid'" := (Events.tid).

Notation "'GTid' t" := (fun x => Gtid x = t) (at level 1).
Notation "'GNTid' t" := (fun x => Gtid x <> t) (at level 1).

Notation "'GR'" := (fun a => is_true (is_r Glab a)).
Notation "'GW'" := (fun a => is_true (is_w Glab a)).
Notation "'GF'" := (fun a => is_true (is_f Glab a)).

Notation "'GRel'" := (fun a => is_true (is_rel Glab a)).
Notation "'GAcq'" := (fun a => is_true (is_acq Glab a)).

Notation "'Gsb'" := (Execution.sb G).
Notation "'Grmw'" := (Execution.rmw G).
Notation "'Grf'" := (Execution.rf G).
Notation "'Gco'" := (Execution.co G).

Notation "'Grs'" := (imm_s_hb.rs G).
Notation "'Grelease'" := (imm_s_hb.release G).
Notation "'Gsw'" := (imm_s_hb.sw G).
Notation "'Ghb'" := (imm_s_hb.hb G).

Notation "'SE'" := S.(ES.acts_set).
Notation "'SEinit'" := S.(ES.acts_init_set).
Notation "'SEninit'" := S.(ES.acts_ninit_set).
Notation "'Stid'" := (S.(ES.tid)).
Notation "'Slab'" := (S.(ES.lab)).
Notation "'Sloc'" := (loc S.(ES.lab)).
Notation "'K'" := S.(ES.cont_set).

Notation "'STid' t" := (fun x => Stid x = t) (at level 1).

Notation "'SR'" := (fun a => is_true (is_r Slab a)).
Notation "'SW'" := (fun a => is_true (is_w Slab a)).
Notation "'SF'" := (fun a => is_true (is_f Slab a)).
Notation "'SRel'" := (fun a => is_true (is_rel Slab a)).

Notation "'Ssb'" := (S.(ES.sb)).
Notation "'Scf'" := (S.(ES.cf)).
Notation "'Srmw'" := (S.(ES.rmw)).
Notation "'Sjf'" := (S.(ES.jf)).
Notation "'Sjfi'" := (S.(ES.jfi)).
Notation "'Sjfe'" := (S.(ES.jfe)).
Notation "'Srf'" := (S.(ES.rf)).
Notation "'Srfi'" := (S.(ES.rfi)).
Notation "'Srfe'" := (S.(ES.rfe)).
Notation "'Sco'" := (S.(ES.co)).
Notation "'Sew'" := (S.(ES.ew)).

Notation "'Srs'" := (S.(Consistency.rs)).
Notation "'Srelease'" := (S.(Consistency.release)).
Notation "'Ssw'" := (S.(Consistency.sw)).
Notation "'Shb'" := (S.(Consistency.hb)).

Definition X2G :=
  ⟪ GACTS : GE ≡₁ e2a S □₁ X ⟫ /\
  ⟪ GLAB  : eq_dom X Slab (Glab ∘ e2a S) ⟫ /\
  ⟪ GSB   : Gsb  ≡  e2a S □ restr_rel X Ssb ⟫ /\
  ⟪ GRMW  : Grmw ≡  e2a S □ restr_rel X Srmw ⟫ /\
  ⟪ GRF   : Grf  ≡  e2a S □ restr_rel X Srf ⟫ /\
  ⟪ GCO   : Gco  ≡  e2a S □ restr_rel X Sco ⟫.

Definition eventid_list :=
  filterP X (first_nat_list (ES.next_act S)).

Definition a2e : actid -> eventid :=
  let e_list := eventid_list in
  let a_list := map (e2a S) e_list in
  list_to_fun (fun x y => excluded_middle_informative (x = y)) 
              (ES.next_act S)
              (combine a_list e_list).

Definition x2g : execution :=
  {| acts := map (e2a S) eventid_list;
     lab := Slab ∘ a2e;
     rmw := a2e ⋄ Srmw;
     data := fun x y => False;
     addr := fun x y => False;
     ctrl := fun x y => False;
     rmw_dep := fun x y => False;
     rf :=  a2e ⋄ Srf;
     co :=  a2e ⋄ Sco 
  |}.

Lemma a2e_e2a
      (WF : ES.Wf S)
      (EXEC : Execution.t S X) :
  eq_dom X (a2e ∘ (e2a S)) id.
Proof.
  red. ins.
  unfold id, "∘".
  apply l2f_in.
  { arewrite (forall {A B} (l : list (A * B)), map fst l = fst (split l)).
    { ins. specialize (split_as_map l). intro HH. by rewrite HH. }
    rewrite combine_split_l; [|by rewrite map_length].
    apply Injective_map_NoDup_dom with (P := X).
    { destruct EXEC. by apply e2a_inj. }  
    { apply ForallE. intros y HH. apply in_filterP_iff in HH. desf. }
    apply nodup_filterP, nodup_first_nat_list. }
  assert (X_IN : In x eventid_list).
  { apply in_filterP_iff. split; auto.
    destruct EXEC. rewrite ES.E_alt in ex_inE.
    basic_solver. }
  eapply In_nth in X_IN. desf.
  arewrite ((e2a S x, x) =
            (nth n
                 (combine (map (e2a S) eventid_list) eventid_list)
                 (e2a S x, x))).
  { rewrite combine_nth; [|by rewrite map_length].
    by rewrite map_nth, X_IN0. }
  eapply nth_In.
  rewrite length_combine, map_length.
  apply Nat.min_glb_iff.
  omega. 
Qed. 

Lemma e2a_a2e
      (WF : ES.Wf S)
      (EXEC : Execution.t S X) :
      eq_dom (e2a S □₁ X) (e2a S ∘ a2e) id.
Proof.
  unfold acts_set.
  red. intros a Ga.
  unfold id, "∘".
  unfold "□₁" in Ga.
  desf.
  arewrite (a2e (e2a S y) = y) by apply a2e_e2a.
Qed.

Lemma a2e_dom 
      (WF : ES.Wf S)
      (EXEC : Execution.t S X):
  a2e ⋄₁ SE ≡₁ e2a S □₁ X.
Proof.
  split.
  { intros a IN_S.
    apply ES.E_alt in IN_S.
    rewrite first_nat_list_In_alt in IN_S.
    unfold a2e in IN_S.
    simpls.
    unfold a2e in IN_S.
    destruct (l2f_codom
                (combine (map (e2a S) eventid_list) eventid_list) a
                (ES.next_act S)
                (fun x y : actid => excluded_middle_informative (x = y)))
      as [HH|]; [|omega].
    apply in_combine_l in HH.
    apply in_map_iff in HH. desf.
    apply in_filterP_iff in HH0. desf.
    basic_solver. }
  intros a IN_IM.
  destruct IN_IM as [e [Xe HH]].
  rewrite <- HH.
  eapply Execution.ex_inE in Xe as Ee; eauto.
  unfolder.
  arewrite (a2e (e2a S e) = e) by apply a2e_e2a.
Qed. 

Lemma X2G_acts_transfer
      (WF : ES.Wf S)
      (EXEC : Execution.t S X) :
  acts_set x2g ≡₁ e2a S □₁ X.
Proof.
  unfold acts_set. simpls. 
  unfold eventid_list.
  unfolder. splits; intros x HH.
  { apply in_map_iff in HH.
    destruct HH as [y [e2a_y_x IN_y]]. exists y.
    apply in_filterP_iff in IN_y.
    basic_solver. }
  apply in_map_iff.
  destruct HH as [y [Xy e2a_y_x]]. exists y.
  rewrite in_filterP_iff.
  splits; auto.
  apply ES.E_alt.
  destruct EXEC. auto.
Qed.

Lemma X2G_rel_transfer r
      (WF : ES.Wf S)
      (EXEC : Execution.t S X)
      (rE : r ≡ ⦗SE⦘ ⨾ r ⨾ ⦗SE⦘) :
  a2e ⋄ r ≡ e2a S □ restr_rel X r.
Proof.
  unfold "□", "≡", "⊆". split.
  { intros a1 a2 HH.
    assert (IM_a1 : (e2a S □₁ X) a1).
    2: assert (IM_a2 : (e2a S □₁ X) a2). 
    1, 2: eapply a2e_dom; apply rE in HH; auto.
    1, 2: by unfolder in *; basic_solver.
    unfold "□₁" in IM_a1. desf. exists y.
    unfold "□₁" in IM_a2. desf. exists y0.
    unfold restr_rel.
    splits; auto. 
    arewrite (y = a2e (e2a S y)).
    2: arewrite (y0 = a2e (e2a S y0)).
    1, 2: by symmetry; apply a2e_e2a.
    auto. }
  intros a1 a2 [e1 [e2 [[RMW [Xe1 Xe2]] [eq1 eq2]]]].
  rewrite <- eq1, <- eq2.
  unfolder.
  arewrite (a2e (e2a S e1) = e1) by apply a2e_e2a.
  arewrite (a2e (e2a S e2) = e2) by apply a2e_e2a.
Qed.

Lemma X2G_sb_transfer 
      (WF : ES.Wf S)
      (EXEC : Execution.t S X) :
  sb x2g ≡ e2a S □ restr_rel X (Ssb).
Proof.
  unfold sb.
  rewrite X2G_acts_transfer; auto.
  split.
  { rewrite <- restr_eqv_def.
    unfolder. 
    intros a1 a2 [ESB [[e1 [Xe1 eq2]] [e2 [Xe2 eq1]]]]. 
    exists e1, e2. splits; auto.
    unfold e2a in eq1, eq2. 
    destruct (excluded_middle_informative (Stid e1 = tid_init));
      destruct (excluded_middle_informative (Stid e2 = tid_init)).
    1, 3:  basic_solver.
    { apply ES.sb_init; auto.
      eapply Execution.ex_inE in Xe1; eauto.
      eapply Execution.ex_inE in Xe2; eauto.
      unfold ES.acts_ninit_set, ES.acts_init_set.
      unfolder. intuition. }
    unfold ext_sb in ESB. subst.
    destruct ESB as [SAME_TID LT].
    eapply Execution.ex_inE in Xe1 as Ee1; eauto.
    specialize (ES.seqn_lt_cont_cf_dom WF) as HH.
    specialize (HH e1 e2 Ee1 SAME_TID LT). 
    simpls.
    destruct HH as [HH | HH].
    { exfalso.
      destruct EXEC.
      eapply ex_ncf with (x := e2) (y := e1).
      unfolder in HH. basic_solver. }
    unfolder in HH.
    basic_solver. }
  rewrite restr_relE.
  rewrite !collect_rel_seqi, collect_rel_eqv.
  by rewrite e2a_ext_sb.
Qed.

Lemma e2a_lab_pred p
      (WF : ES.Wf S)
      (x2g : X2G) :
   e2a S □₁ (X ∩₁ (p ∘ Slab)) ≡₁ GE ∩₁ (p ∘ Glab).
Proof.
  split.
  { cdes x2g. clear x2g.
    unfolder. unfold "∘".
    intros x HH. desf.
    arewrite (Glab (e2a S y) = Slab y); auto.
    { specialize (GLAB y HH).
      basic_solver . }
    split; auto.
    apply GACTS. basic_solver. }
  cdes x2g. clear x2g.
  unfolder. unfold "∘".
  intros x [GEx px].
  apply GACTS in GEx.
  unfold "□₁" in GEx. desf.
  exists y. splits; auto.
  by arewrite (Slab y = Glab (e2a S y)).
Qed.

Lemma X2G_R
      (WF : ES.Wf S)
      (X2G : X2G) :
  GE ∩₁ GR ≡₁ e2a S □₁ (X ∩₁ SR).
Proof.
  Definition is_r_lab lab :=
    match lab with
    | Aload _ _ _ _ => True
    | _ => False
    end.
  specialize (e2a_lab_pred is_r_lab WF X2G).
  arewrite (is_r_lab ∘ Slab ≡₁ SR).
  2: arewrite (is_r_lab ∘ Glab ≡₁ GR).
  1, 2: unfold compose, is_r_lab, is_r;
    basic_solver. by symmetry.
Qed.

Lemma X2G_complete
      (WF : ES.Wf S)
      (EXEC : Execution.t S X)
      (X2G : X2G):
  Execution.complete G.
Proof.
  red.
  rewrite <- set_interK with (s := GE), set_interA.
  cdes X2G.
  rewrite GACTS at 1.
  rewrite GRF.
  rewrite X2G_R; auto.
  rewrite <- set_collect_inter_inj.
  2 : { arewrite ((X ∪₁ X ∩₁ SR) ≡₁ X) by basic_solver.
        destruct EXEC. apply e2a_inj; basic_solver. }
  rewrite <- set_interA, set_interK.
  rewrite <- set_collect_codom.
  apply set_subset_collect.
  rewrite restr_relE.
  destruct EXEC.
  rewrite <- set_interK with (s := X) at 1.
  rewrite set_interA, ex_rf_compl.
  basic_solver.
Qed.  

End ExecutionToGraph. 

Lemma x2g_X2G S X
      (WF : ES.Wf S)
      (EXEC : Execution.t S X) :
  X2G S X (x2g S X).
Proof.
  red. splits.
  { by apply X2G_acts_transfer. }
  { simpls.
    unfolder.
    unfold eq_dom. ins.
    rewrite Combinators.compose_assoc.
    unfold "∘" at 1. by rewrite a2e_e2a. }
  { by apply X2G_sb_transfer. }
  all: apply X2G_rel_transfer; auto.
  { by apply ES.rmwE. }
  { by apply ES.rfE. }
  by apply ES.coE. 
Qed.







