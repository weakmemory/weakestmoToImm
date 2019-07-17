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

Section ExecutionToG.
    
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


Definition upd_with_list_fun {A B} (f : A -> B) (g : A -> B) (l : list A) :=
  fold_left (fun f x => upd f x (g x)) l f. 

Lemma upd_with_list_fun_unfold {A B} (f : A -> B) g x xs:
  upd_with_list_fun f g (x :: xs) = upd_with_list_fun (upd f x (g x)) g xs.
Proof.
  basic_solver.
Qed. 
  
Lemma upd_with_list_fun_not_in {A B} (f : A -> B) g l a
      (N_IN : ~ In a l) :
  upd_with_list_fun f g l a = f a.
Proof.
  remember f as f'.
  assert (HH : f a = f' a) by congruence.
  rewrite <- HH. clear Heqf'.
  generalize dependent f'.
  generalize dependent f.
  generalize dependent l.
  induction l; auto.
  intuition.
  rewrite upd_with_list_fun_unfold.
  apply H.
  rewrite HH.
  symmetry.
  apply updo.
  basic_solver.
Qed.
  
Lemma upd_with_list_fun_in {A B} (f : A -> B) g l a
      (NO_DUP : NoDup l)
      (IN : In a l) :
  upd_with_list_fun f g l a = g a. 
Proof.
  generalize dependent f.
  generalize dependent l.
  induction l; [done|].
  intuition.
  apply NoDup_cons_iff in NO_DUP. desf.
  rewrite upd_with_list_fun_unfold.
  cdes IN. desf.
  { rewrite upd_with_list_fun_not_in; auto.
    apply upds. }
  apply IHl; auto.
Qed.

Definition a2e : actid -> eventid :=
  let e_list := nat_filter X (ES.next_act S) in
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

Lemma a2e_e2a : eq_dom X (a2e ∘ (e2a S)) id.
Proof.
  red. ins.
  unfold id, "∘".
  unfold a2e.
  apply l2f_in.
  { arewrite (forall {A B} (l : list (A * B)), map fst l = fst (split l)).
    { ins. specialize (split_as_map l). ins. rewrite H. auto. }
    rewrite combine_split_l.
    2: { rewrite map_length. auto. }
    apply Injective_map_NoDup.
    2: { unfold nat_filter. }
    
    

    unfold upd_with_lists, upd_with_list.
  
Lemma e2a_lab_pred p (x2g : X2G) :
   e2a S □₁ (X ∩₁ (p ∘ Slab)) ⊆₁ p ∘ Glab .
Proof.
  cdes x2g. clear x2g.
  unfolder. unfold "∘".
  intros x HH. desf.
  arewrite (Glab (e2a S y) = Slab y); auto.
  specialize (GLAB y HH).
  basic_solver.
Qed.
    
    
End ExecutionToG.





Definition X2G_fun (S : ES.t) (X : eventid -> Prop) : execution :=
  {| acts := map (e2a S) (nat_filter X (ES.next_act S));
     lab := fun x => Afence Orlx;
     rmw := fun x y => False;
     data := fun x y => False;
     addr := fun x y => False;
     ctrl := fun x y => False;
     rmw_dep := fun x y => False;
     rf := fun x y => False;
     co := fun x y => False
  |}.



