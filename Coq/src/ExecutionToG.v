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
Require Import Consistency.

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
Notation "'GLoc_' l" := (fun x => Gloc x = l) (at level 1).

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
Notation "'SLoc_' l" := (fun x => Sloc x = l) (at level 1).

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

Notation "'Move' r" := (e2a S □ restr_rel X r) (at level 1).

Definition X2G :=
  ⟪ GACTS : GE ≡₁ e2a S □₁ X ⟫ /\
  ⟪ GLAB  : eq_dom X Slab (Glab ∘ e2a S) ⟫ /\
  ⟪ GSB   : Gsb  ≡  Move Ssb ⟫ /\
  ⟪ GRMW  : Grmw ≡  Move Srmw ⟫ /\
  ⟪ GRF   : Grf  ≡  Move Srf ⟫ /\
  ⟪ GCO   : Gco  ≡  Move Sco ⟫.

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
  a2e ⋄ r ≡ Move r.
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
  sb x2g ≡ Move Ssb.
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
      (X2G : X2G) :
   e2a S □₁ (X ∩₁ (p ∘ Slab)) ≡₁ GE ∩₁ (p ∘ Glab).
Proof.
  cdes X2G. 
  unfolder. unfold "∘".
  split.
  { intros x HH. desf.
    arewrite (Glab (e2a S y) = Slab y). 
    { specialize (GLAB y HH).
      basic_solver. }
    split; auto.
    apply GACTS. basic_solver. }
  intros x [GEx px].
  apply GACTS in GEx.
  unfold "□₁" in GEx. desf.
  exists y. splits; auto.
  by arewrite (Slab y = Glab (e2a S y)).
Qed.

Lemma X2G_lab {B}
      (p : forall {A}, (A -> label) -> A -> B)
      (p_lab : label -> B)
      (EQ : forall {A} (sup : A -> label), p sup = p_lab ∘ sup) 
      (WF : ES.Wf S)
      (X2G : X2G) :
  eq_dom X (p Slab) (p Glab ∘ e2a S).
Proof.
  cdes X2G.
  rewrite !EQ.
  unfolder. unfold "∘".
  intros.
  by rewrite GLAB.
Qed.

Lemma X2G_lab_set_transfer
      (p : forall {A}, (A -> label) -> A -> Prop)
      (p_lab : label -> Prop)
      (EQ : forall {A} (sup : A -> label) a, (p sup a) = (p_lab (sup a)))
      (WF : ES.Wf S)
      (X2G : X2G) :
 e2a S □₁ (X ∩₁ (fun a => p Slab a)) ≡₁
 GE ∩₁ (fun a => p Glab a).
Proof.
  cdes X2G. 
  unfolder. unfold "∘".
  split.
  { intros x HH. desf.
    split.
    { apply GACTS. basic_solver. }
    rewrite EQ.
    arewrite (Glab (e2a S y) = Slab y). 
    { specialize (GLAB y HH).
      basic_solver . }
    by rewrite EQ in HH1. }
  intros x [GEx px].
  apply GACTS in GEx.
  unfold "□₁" in GEx. desf.
  exists y. splits; auto.
  rewrite EQ in *.
  by arewrite (Slab y = Glab (e2a S y)).
Qed.

Lemma X2G_lab_rel_transfer
      (p : forall {A}, (A -> label) -> A -> A -> Prop)
      (p_lab : label -> label -> Prop)
      (EQ : forall {A} (sup : A -> label) a b, (p sup a b) = (p_lab (sup a) (sup b)))
      (WF : ES.Wf S)
      (X2G : X2G) :
  Move (fun a b => p Slab a b) ≡
       restr_rel GE (fun a b => p Glab a b).
Proof.
  cdes X2G.
  unfolder.
  split.
  { ins. desf.
    rewrite EQ in *.
    unfold "∘" in GLAB.
    rewrite <- !GLAB; auto.
    splits; auto.
    1, 2: apply GACTS; basic_solver. }
  intros a1 a2 [P12 [Ga1 Ga2]].
  apply GACTS in Ga1. unfolder in Ga1.
  apply GACTS in Ga2. unfolder in Ga2.
  destruct Ga1 as [e1 [Xe1 eq1]].
  destruct Ga2 as [e2 [Xe2 eq2]].
  exists e1, e2.
  splits; auto.
  rewrite EQ in *.
  unfold "∘" in GLAB.
  rewrite !GLAB; basic_solver.
Qed.

Lemma X2G_R
      (WF : ES.Wf S)
      (X2G : X2G) :
  GE ∩₁ GR ≡₁ e2a S □₁ (X ∩₁ SR).
Proof.
  set (f := fun x => match x with
                  | Aload _ _ _ _ => true
                  | _ => false end).
  erewrite X2G_lab_set_transfer
    with (p := is_r) (p_lab := f); eauto.
Qed.

Lemma X2G_W
      (WF : ES.Wf S)
      (X2G : X2G) :
  GE ∩₁ GW ≡₁ e2a S □₁ (X ∩₁ SW).
Proof.
  set (f := fun x => match x with
                  | Astore _ _ _ _ => true
                  | _ => false end).
  erewrite X2G_lab_set_transfer
    with (p := is_w) (p_lab := f); eauto.
Qed.

Lemma X2G_loc_ loc
      (WF : ES.Wf S)
      (X2G : X2G) :
  GE ∩₁ GLoc_ loc ≡₁ e2a S □₁ (X ∩₁ SLoc_ loc).
Proof.
  set (f := fun x => match x with
                  | Aload _ _ l _ | Astore _ _ l _ => Some l = loc
                  | Afence _ => None = loc end).
  erewrite X2G_lab_set_transfer
    with (p := fun A s x => Events.loc s x = loc) (p_lab := f); eauto.
  ins.  unfold Events.loc. desf.
Qed.

Lemma move_codom r :
  codom_rel Move r ⊆₁ e2a S □₁ (X ∩₁ codom_rel r). 
Proof.
  basic_solver 7. 
Qed.

Lemma move_dom r :
  dom_rel Move r ⊆₁ e2a S □₁ (X ∩₁ dom_rel r). 
Proof.
  basic_solver 7.
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

From imm Require Import Events Prog RC11.

    
Lemma X2G_rmw_atomicity
      (WF : ES.Wf S)
      (CONS : es_consistent (m := Weakestmo) S)
      (EXEC : Execution.t S X)
      (X2G : X2G):
  rmw_atomicity G.
Proof.
Admitted.


Lemma X2G_sw_trans
      (WF : ES.Wf S)
      (CONS : es_consistent (m := Weakestmo) S)
      (EXEC : Execution.t S X)
      (X2G : X2G):
  e2a S □ restr_rel X (Ssw) ⊆ Gsw.
Proof.
  rewrite restr_relE.
  rewrite imm_s_hb.wf_swE; eauto.
  
  unfold sw.
  rewrite ES.jf_in_rf; auto.
Admitted.
  
Lemma X2G_hb_trans
      (WF : ES.Wf S)
      (CONS : es_consistent (m := Weakestmo) S)
      (EXEC : Execution.t S X)
      (X2G : X2G):
  e2a S □ restr_rel X (Shb) ⊆ Ghb.
Proof.
  unfold hb.
  unfold imm_s_hb.hb.
Admitted.
  
Lemma X2G_cohernce
      (WF : ES.Wf S)
      (CONS : es_consistent (m := Weakestmo) S)
      (EXEC : Execution.t S X)
      (X2G :  X2G):
  imm_s_hb.coherence G.
Proof.
Admitted.

Lemma X2G_acyclic_psc
      (WF : ES.Wf S)
      (CONS : es_consistent (m := Weakestmo) S)
      (EXEC : Execution.t S X)
      (X2G : X2G) :
  acyclic (imm_s.psc_f G ∪ imm_s.psc_base G).
Proof.
Admitted.


Lemma X2G_same_loc r
      (WF : ES.Wf S)
      (X2G : X2G)
      (SL :  r ⊆ same_loc Slab) :
  Move r ⊆ same_loc Glab.
Proof.
  cdes X2G.
  rewrite SL. 
  set (loc_l := fun (l : label) =>
                  match l with
                  | Aload _ _ l _ | Astore _ _ l _ => Some l
                  | Afence _ => None
                  end).
  set (f := fun (l1 : label) (l2 : label) => loc_l l1 = loc_l l2).
  erewrite X2G_lab_rel_transfer with (p_lab := f); eauto.
  basic_solver.
Qed. 

Lemma X2G_E r dom codom 
      (IN_DOM : dom_rel r ⊆₁ dom)
      (IN_CODOM : codom_rel r ⊆₁ codom)
      (X2G : X2G) :
  Move r ≡ ⦗e2a S □₁ (X ∩₁ dom)⦘ ⨾ Move r ⨾ ⦗e2a S □₁ (X ∩₁ codom)⦘. 
Proof.
  eapply dom_codom_rel_helper; eauto. 
  { rewrite move_dom. by rewrite IN_DOM. }
  rewrite move_codom. by rewrite IN_CODOM.
Qed.

Lemma is_total_restr' {A} dom (r : relation A) : 
  is_total dom (restr_rel dom r) -> is_total dom r.
Proof. apply  is_total_mori; basic_solver. Qed.
  
End ExecutionToGraph. 

Lemma x2g_X2G {S X}
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

Lemma immediate_restr {A} (r : relation A) (s : A -> Prop) :
      restr_rel s (immediate r) ⊆ immediate (restr_rel s r).
Proof. basic_solver. Qed. 

Lemma immediate_collect {A B} (r : relation A) (f : A -> B) : 
  immediate (f □ r) ⊆ f □ (immediate r).
Proof. basic_solver 15. Qed. 
  
Lemma immediate_collect_inj {A B} (r : relation A) (f : A -> B) s
      (INJ : inj_dom s f) :
      f □ (immediate (restr_rel s r)) ≡ immediate (f □ (restr_rel s r)).
Proof.
  split; [|by apply immediate_collect].
  split; rename x into b1, y into b2, H into FIb12.
  { destruct FIb12 as [a1 [a2 [IRa12 [eq1 eq2]]]].
    exists a1, a2.
    splits; auto. by apply immediate_in. }
  intros b3 Fb13 Fb32.
  destruct Fb13 as [a1 [a3 [ra13 [eq11 eq33]]]].
  destruct Fb32 as [a3' [a2 [ra32 [eq33' eq22]]]].
  assert (a3 = a3').
  { cdes ra32. cdes ra13.
    apply INJ; basic_solver. }
  subst.
  cdes FIb12.
  cdes FIb0.
  apply FIb4 with (c := a3').
  { unfolder in FIb3. unfolder in ra13.
    apply INJ in FIb1; basic_solver. }
  unfolder in FIb3. unfolder in ra32.
  apply INJ in FIb2; basic_solver.
Qed.

Lemma transp_collect_rel {A B} (f : A -> B) r :
  f □ r⁻¹ ≡  (f □ r)⁻¹.
Proof. basic_solver 10. Qed.

Lemma transp_restr_rel {A} X (r : relation A) :
  restr_rel X r⁻¹ ≡ (restr_rel X r)⁻¹.
Proof. basic_solver. Qed.

Lemma functional_collect_rel_inj {A B} X (f : A -> B) r
      (INJ : inj_dom X f) :
  functional (f □ (restr_rel X r)) <-> functional (restr_rel X r). 
Proof.
  split; [basic_solver 15|].
  unfolder.
  intros P b1 b2 b3 [a1 [a2 [pr1 [eq1 eq2]]]]
         [a1' [a2' [pr1' [eq1' eq2']]]].
  subst.
  assert (a2 = a2'); [|congruence].
  assert (a1 = a1'); [|by eapply P; eauto; desf].
  apply INJ; desf.
Qed.

Lemma transitive_collect_rel_inj {A B} X (f : A -> B) r
      (INJ : inj_dom X f) :
  transitive (f □ restr_rel X r) <-> transitive (restr_rel X r).
Proof. 
  split.
  { unfolder.
    intros HH a1 a2 a3 R12 R23.
    specialize (HH (f a1) (f a2) (f a3)).
    destruct HH as [a1' HH]. 
    { exists a1, a2. desf. }
    { exists a2, a3. desf. }
    destruct HH as [a3' HH].
    assert (a1 = a1'); [apply INJ; by desf|].
    assert (a3 = a3'); [apply INJ; by desf|].
    basic_solver. }
  unfolder. 
  intros HH b1 b2 b3 [a1 [a2 P]] [a2' [a3 PP]].
  assert (a2' = a2); [apply INJ; by desf|].
  exists a1, a3.
  split; [|by desf].
  eapply HH with (y := a2); basic_solver.
Qed.

Lemma total_collect_rel {A B} X (f : A -> B) r :
  is_total X r -> is_total (f □₁ X) (f □ r).
Proof.
  unfolder.
  intros HH b1 [a1 P1] b2 [a2 P2] NEQ.
  desf.
  assert (a1 <> a2) as NEQ' by congruence.
  specialize (HH a1 P1 a2 P2 NEQ').
  desf.
  { left. eauto. }
  right. eauto.
Qed.

Lemma collect_rel_irr_inj {A B} X r (f : A -> B)
      (INJ : inj_dom X f) :
  irreflexive (f □ (restr_rel X r)) <-> irreflexive (restr_rel X r).
Proof.
  split; [by apply collect_rel_irr|].
  unfolder. ins. desf. rename H2 into EQ.
  apply INJ in EQ; eauto.
  basic_solver.
Qed.

Lemma x2g_wf {S X}
      (WF : ES.Wf S)
      (EXEC : Execution.t S X) : 
  Wf (x2g S X).
Proof.
  specialize (x2g_X2G WF EXEC) as X2G.
  cdes X2G.
  assert (INJ : inj_dom X (e2a S)).
  { destruct EXEC. by apply e2a_inj. }
  constructor.
  all: try basic_solver.
  { intros a1 a2 P.
    destruct P as [Ga1 [Ga2 [NEQ [SAME_TID NINIT_a1]]]].
    apply GACTS in Ga1.
    apply GACTS in Ga2. 
    unfold "□₁" in Ga1, Ga2. desf.
    rename y0 into e1, y into e2.
    assert (SAME_TID' : ES.same_tid S e1 e2).
    { destruct (excluded_middle_informative ((ES.tid S) e1 = tid_init)).
      { exfalso; apply NINIT_a1; unfold e2a; desf. } 
      destruct (excluded_middle_informative ((ES.tid S) e2 = tid_init)).
      all: unfold e2a in SAME_TID; desf. }
    assert (HH : (ES.sb S)⁼ e2 e1 \/ ES.cf S e2 e1).
    { eapply Execution.ex_inE in Ga1; eauto.
      eapply Execution.ex_inE in Ga2; eauto.
      apply ES.same_thread_alt; auto.
      split; auto.
      intro HH. apply NINIT_a1.
      unfold ES.acts_init_set in HH.
      unfolder in HH. unfold e2a. desf. }
    desf.
    2: { exfalso. eapply Execution.ex_ncf; eauto. basic_solver. }
    destruct HH as [EQ | SB]; auto.
    assert (FOO : ES.seqn S e2 <> ES.seqn S e1).
    { destruct SB.
      1: assert (ES.seqn S e2 < ES.seqn S e1); [|omega].
      2: assert (ES.seqn S e1 < ES.seqn S e2); [|omega].
      1: apply ES.same_tid_sym in SAME_TID'. 
      all: by apply ES.seqn_sb_alt. }
    destruct (excluded_middle_informative ((ES.tid S) e1 = tid_init)).
    { exfalso; apply NINIT_a1; unfold e2a; desf. } 
    destruct (excluded_middle_informative ((ES.tid S) e2 = tid_init)).
    all : unfold e2a; desf; simpls; auto. 
    arewrite (0 = ES.seqn S e2); auto.
    eapply Execution.ex_inE in Ga2; eauto.
      by rewrite ES.seqn_init. }
  { admit. }
  { rewrite GRMW.
    apply X2G_same_loc; auto.
    by apply ES.rmwl. }
  { rewrite GRMW.
    rewrite ES.rmwi; auto.
    rewrite immediate_restr.
    rewrite immediate_collect_inj; auto.
    by rewrite <- GSB. }
  { rewrite GACTS, GRF.
    apply dom_codom_rel_helper; basic_solver. }
  { rewrite GRF.
    rewrite <- dom_codom_rel_helper; auto.
    { rewrite move_dom.
      rewrite ES.rfD, !dom_seq, dom_eqv; auto.
      rewrite <- X2G_W; eauto. basic_solver. }
    rewrite move_codom.
    rewrite ES.rfD, !codom_seq, codom_eqv; auto.
    rewrite <- X2G_R; eauto. basic_solver. }
  { rewrite GRF.
    apply X2G_same_loc; auto.
    by apply ES.rfl. }
  { rewrite GRF.
    unfolder. intros a1 a2 RF.
    desf. 
    set (f := fun l => match l with
                    | Aload _ _ _ v | Astore _ _ _ v => Some v
                    | Afence _ => None
                    end).
    specialize (X2G_lab S X (x2g S X) val f) as e.
    unfold "∘" in e.
    erewrite <- !e; eauto.
    by apply ES.rfv. }
  { rewrite GRF.
    rewrite <- transp_collect_rel.
    rewrite <- transp_restr_rel.
    apply functional_collect_rel_inj; auto.
    destruct EXEC.
    by apply ES.trf_funcional_in_cf_free. }
  { rewrite GACTS, GCO.
    apply dom_codom_rel_helper; basic_solver. }
  { rewrite GCO.
    rewrite <- dom_codom_rel_helper; auto.
    { rewrite move_dom.
      rewrite ES.coD, !dom_seq, dom_eqv; auto.
      rewrite <- X2G_W; eauto. basic_solver. }
    rewrite move_codom.
    rewrite ES.coD, !codom_seq, codom_eqv; auto.
    rewrite <- X2G_W; eauto. basic_solver. }
  { rewrite GCO.
    apply X2G_same_loc; auto.
    by apply ES.col. }
  { rewrite GCO.
    rewrite transitive_collect_rel_inj; auto.
    apply transitive_restr.
    by apply ES.co_trans. }
  { intro.
    rewrite set_interC with (s := acts_set _).  
    rewrite <- set_interK with (s := acts_set (x2g S X)).
    rewrite !set_interA.
    rewrite X2G_loc_; eauto.
    rewrite <- !set_interA.
    rewrite set_interC with (s' := acts_set (x2g S X)).
    rewrite X2G_W; eauto.

    rewrite GCO.
    rewrite <- !set_collect_inter_inj; [|basic_solver].
    apply total_collect_rel.
    rewrite <- !set_interA.
    rewrite set_interC with (s' := X).
    rewrite <- set_interA, set_interK.
    eapply is_total_mori with
        (x0 := restr_rel (X ∩₁ (fun a : eventid => is_w (ES.lab S) a)
                            ∩₁ (fun x : eventid => loc (ES.lab S) x = ol)) (ES.co S)).
    { apply set_subset_refl2. }
    { basic_solver. } 
    apply is_total_restr.
    by apply Execution.co_total. }
  { rewrite GCO.
    rewrite collect_rel_irr_inj; auto.
    specialize ES.co_irr. basic_solver. }
  { intros l [a [Ea LOC]].
    apply GACTS in Ea.
    destruct Ea as [e [Xe EQ]].
    assert (LOC' : loc (ES.lab S) e = Some l).
    { rewrite <- EQ in LOC.    
      unfold "∘" in GLAB.
      rewrite <- LOC.
      unfold loc.
      erewrite GLAB; eauto. }
    eapply Execution.ex_inE in Xe as Ee; eauto.
    specialize (ES.initL WF Ee LOC') as INIT_l.
    subst.
    apply GACTS.
    cdes INIT_l.
    exists a.
    eapply Execution.init_in_ex in EINA as Xa; eauto.  
    split; auto.
    unfold ES.acts_init_set in EINA. 
    unfolder in EINA.
    unfold e2a. rewrite LOCA. desf. }
  intro.
  unfold x2g. simpl.
  
Admitted.
