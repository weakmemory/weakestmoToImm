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

Section ActionToEvent.

Lemma nodup_first_nat_list : forall n : nat, NoDup (first_nat_list n).
Proof.
  induction n.
  { apply NoDup_nil. }
  apply NoDup_cons; auto.
  rewrite first_nat_list_In_alt.
  omega. 
Qed.
  
Definition eventid_list S (X : eventid -> Prop) :=
  filterP X (first_nat_list (ES.next_act S)).
  
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

Definition a2e : actid -> eventid :=
  let e_list := eventid_list S X in
  let a_list := map (e2a S) e_list in
  list_to_fun (fun x y => excluded_middle_informative (x = y)) 
              (ES.next_act S)
              (combine a_list e_list).

Lemma split_as_map {A B} (l : list (A * B)) :
  split l = (map fst l, map snd l).
Proof.
  generalize dependent l.
  induction l; [done|].
  simpls.
  rewrite IHl.
  basic_solver.
Qed.

Lemma combine_split_l {A B} (lA : list A) (lB : list B)
      (LEQ : length lA <= length lB) :
  fst (split (combine lA lB)) = lA.
Proof.
  generalize dependent lB.
  generalize dependent lA.
  induction lA; [done|].
  intros.
  destruct lB.
  { simpls. omega. }
  simpls. desf.
  arewrite (l = lA); auto.
  rewrite <- (IHlA lB); [|omega].
  unfold fst. basic_solver.
Qed.

Lemma Injective_map_NoDup_dom {A B} (P : A -> Prop) (f : A -> B) (l : list A)
      (IJ : inj_dom P f)
      (PL : Forall P l)
      (NO_DUP: NoDup l) :
  NoDup (map f l).
Proof.
  generalize dependent NO_DUP.
  induction 1 as [|x l SX N IH]; simpls;
    constructor; apply Forall_cons in PL; desf; auto.
  rewrite in_map_iff. intros (y & E & Y). apply IJ in E.
  { now subst. }
  { eapply Forall_forall; eauto. }
  auto.
Qed.

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
  assert (X_IN : In x (eventid_list S X)).
  { apply in_filterP_iff. split; auto.
    destruct EXEC. rewrite ES.E_alt in ex_inE.
    basic_solver. }
  eapply In_nth in X_IN. desf.
  arewrite ((e2a S x, x) =
               (nth n (combine
                         (map (e2a S) (eventid_list S X))
                         (eventid_list S X))
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
  
Lemma e2a_lab_pred p (WF : ES.Wf S) (x2g : X2G) :
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
    
End ActionToEvent.

Section ExecutionToGraph.

Definition X2G_fun (S : ES.t) (X : eventid -> Prop) : execution :=
  {| acts := map (e2a S) (eventid_list S X);
     lab := S.(ES.lab) ∘ (a2e S X);
     rmw :=  fun e1 e2 => S.(ES.rmw) (a2e S X e1) (a2e S X e2);
     data := fun x y => False;
     addr := fun x y => False;
     ctrl := fun x y => False;
     rmw_dep := fun x y => False;
     rf :=  fun e1 e2 => S.(ES.rf) (a2e S X e1) (a2e S X e2);
     co :=  fun e1 e2 => S.(ES.co) (a2e S X e1) (a2e S X e2)
  |}.



