Require Import Omega.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events.
Require Import AuxDef AuxRel.

Set Implicit Arguments.
Export ListNotations.

Definition eventid := nat.
(* TODO: move to IMM Events.v *)
Definition tid_init := xH.

Module Language.
Record t :=
  mk { syntax : Type;
       state : Type;
       init : syntax -> state;
       is_terminal : state -> Prop;
       step : list label -> state -> state -> Prop
     }.
End Language.

Inductive cont_label :=
| CInit  (tid : thread_id)
| CEvent (eid : eventid).

Module ES.

Record t :=
  mk { next_act : eventid;
       lab  : eventid -> label; 
       tid  : eventid -> thread_id;
       sb   : eventid -> eventid -> Prop ;
       rmw  : eventid -> eventid -> Prop ;
       jf   : eventid -> eventid -> Prop ;
       co   : eventid -> eventid -> Prop ;
       ew   : eventid -> eventid -> Prop ;
       cont : list (cont_label *
                    { lang : Language.t &
                      lang.(Language.state) });
     }.

Definition acts_set (ES : t) := fun x => x < ES.(next_act).
Definition acts_init_set (ES : t) :=
  ES.(acts_set) ∩₁ (fun x => ES.(tid) x = tid_init).
Definition acts_ninit_set (ES : t) := ES.(acts_set) \₁ ES.(acts_init_set).
Definition cont_set (ES : t) := fun x => In x ES.(cont).

Definition same_tid (ES : t) := fun x y => ES.(tid) x = ES.(tid) y.

Definition jfe (ES : t) := ES.(jf) \ ES.(sb).
Definition coe (ES : t) := ES.(co) \ ES.(sb).
Definition jfi (ES : t) := ES.(jf) ∩ ES.(sb).
Definition coi (ES : t) := ES.(co) ∩ ES.(sb).

Definition cf (ES : t) :=
  ⦗ ES.(acts_ninit_set) ⦘ ⨾ (ES.(same_tid) \ (ES.(sb)⁼)) ⨾ ⦗ ES.(acts_ninit_set) ⦘.

Definition cc (ES : t) := 
  ES.(cf) ∩ (ES.(jfe) ⨾ (ES.(sb) ∪ ES.(jf))＊ ⨾ ES.(jfe) ⨾ ES.(sb)^?). 

Definition rf (ES : t) := ES.(ew)^? ⨾ ES.(jf) \ ES.(cf).

Definition rfe (ES : t) := ES.(rf) \ ES.(same_tid).
Definition rfi (ES : t) := ES.(rf) ∩ ES.(same_tid).

Definition fr (ES : t) := ES.(rf)⁻¹ ⨾ ES.(co).

Definition cont_thread S (cont : cont_label) : thread_id :=
  match cont with
  | CInit thread => thread
  | CEvent e => S.(ES.tid) e
  end.

Definition cont_lab S (cont : cont_label) : option label := 
  match cont with
  | CInit thread => None
  | CEvent e => Some (S.(ES.lab) e)
  end.

Definition cont_sb_dom S c :=
  match c with
  | CInit  _ => S.(ES.acts_init_set)
  | CEvent e => dom_rel (S.(sb)^? ⨾ ⦗ eq e ⦘)
  end.

Definition cont_sb_codom S c := 
  match c with
  | CInit _ => (fun x => tid S x = (cont_thread S c))
  | CEvent e => (fun x => tid S x = (cont_thread S c)) ∩₁ codom_rel (⦗ eq e ⦘ ⨾ sb S)
  end.

Definition cont_cf_dom S c :=
  match c with
  | CInit  i => fun x => ES.acts_set S x /\ S.(tid) x = i 
  | CEvent e => dom_rel (cf S ⨾ ⦗ eq e ⦘) ∪₁ codom_rel (⦗ eq e ⦘ ⨾ sb S)
  end.

Hint Unfold ES.acts_set ES.acts_init_set ES.cf : unfolderDb.

Section EventStructure.

Variable S : ES.t.

Notation "'E'"      := S.(ES.acts_set).
Notation "'Einit'"  := S.(ES.acts_init_set).
Notation "'Eninit'" := S.(ES.acts_ninit_set).
Notation "'tid'"   := S.(ES.tid).
Notation "'sb'"    := S.(ES.sb).
Notation "'rmw'"   := S.(ES.rmw).
Notation "'ew'"    := S.(ES.ew).
Notation "'jf'"    := S.(ES.jf).
Notation "'rf'"    := S.(ES.rf).
Notation "'fr'"    := S.(ES.fr).
Notation "'co'"    := S.(ES.co).
Notation "'lab'"   := S.(ES.lab).
Notation "'cf'"    := S.(ES.cf).
Notation "'K'"     := S.(ES.cont_set).

Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).
Notation "'same_loc'" := (same_loc lab).

Notation "'Tid' t" := (fun x => tid x = t) (at level 1).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).

Notation "'Pln'" := (is_only_pln lab).
Notation "'Rlx'" := (is_rlx lab).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).
Notation "'Sc'" := (is_sc lab).

Definition event_to_act (e : eventid) : actid :=
    if excluded_middle_informative (Einit e)
    then
      match loc e with
      | Some l => InitEvent l
      | _      => InitEvent BinNums.xH
      end
    else
      let thread := tid e in
      ThreadEvent thread
                  (countNatP (dom_rel (⦗ Tid thread ⦘⨾ sb ⨾ ⦗ eq e ⦘))
                             (next_act S)).

Record Wf :=
  { (* initI : exists a, Einit a; *)
    initL : forall l, (exists b, E b /\ loc b = Some l) ->
                      exists a, Einit a /\ loc a = Some l ;
    init_lab : forall e (INIT : Einit e),
        exists l, lab e = Astore Xpln Opln l 0 ;
    
    sbE : sb ≡ ⦗E⦘ ⨾ sb ⨾ ⦗E⦘ ;
    sb_init : Einit × Eninit ⊆ sb;
    sb_ninit : sb ⨾ ⦗Einit⦘ ≡ ∅₂;
    sb_tid : ⦗Eninit⦘ ⨾ sb ⨾ ⦗Eninit⦘ ⊆ same_tid S;
    sb_irr   : irreflexive sb;
    sb_trans : transitive sb;

    rmwD : rmw ≡ ⦗R⦘ ⨾ rmw ⨾ ⦗W⦘ ;
    rmwl : rmw ⊆ same_loc ;
    rmwi : rmw ⊆ immediate sb ;

    jfE : jf ≡ ⦗E⦘ ⨾ jf ⨾ ⦗E⦘ ;
    jfD : jf ≡ ⦗W⦘ ⨾ jf ⨾ ⦗R⦘ ;
    jfl : jf ⊆ same_loc ;
    jfv : funeq val jf ;
    jff : functional jf⁻¹ ;
    jf_complete : E ∩₁ R ⊆₁ codom_rel jf;

    coE : co ≡ ⦗E⦘ ⨾ co ⨾ ⦗E⦘ ;
    coD : co ≡ ⦗W⦘ ⨾ co ⨾ ⦗W⦘ ;
    col : co ⊆ same_loc ;
    co_trans : transitive co ;
    co_total :
      forall ol ws (WS : ws ⊆₁ E ∩₁ W ∩₁ (fun x => loc x = ol))
             (NCF : ⦗ ws ⦘ ⨾ cf ⨾ ⦗ ws ⦘ ≡ ∅₂),
        is_total ws co;
    co_irr : irreflexive co ;

    ewE : ew ≡ ⦗E⦘ ⨾ ew ⨾ ⦗E⦘ ;
    ewD : ew ≡ ⦗W⦘ ⨾ ew ⨾ ⦗R⦘ ;
    ewl : ew ⊆ same_loc ;
    ewv : funeq val ew ;
    ewc : ew ⊆ cf ;
    ew_trans : transitive ew ;
    ew_sym : symmetric ew ;

    ew_co_in_co : ew ⨾ co ⊆ co;

    (* term_def_K : forall state (TERM : lang.(Language.is_terminal) state), *)
    (*     ~ (exists lbl state', lang.(Language.step) lbl state state'); *)
    init_tid_K : ~ (exists c k, K (k, c) /\ cont_thread S k = tid_init);
    unique_K : forall c c' (CK : K c) (CK' : K c') (FF : fst c = fst c'),
        snd c = snd c';
    event_K  : forall e (EE: E e) (NINIT : ~ Einit e) (NRMW : ~ dom_rel rmw e),
        exists c, K (CEvent e, c);
    K_inEninit : forall e c (inK: K (CEvent e, c)), Eninit e;  
  }.

Implicit Type WF : Wf.

Lemma acts_set_split : E ≡₁ Einit ∪₁ Eninit.
Proof.
  unfold ES.acts_init_set, ES.acts_ninit_set.
  rewrite set_unionC.
  eapply set_union_minus.
  basic_solver.
Qed.

Lemma acts_ninit_set_incl : Eninit ⊆₁ E. 
Proof. 
  unfold ES.acts_ninit_set.
  basic_solver.
Qed.

Lemma same_tid_refl : reflexive (same_tid S).
Proof. unfold same_tid. basic_solver. Qed.

Lemma same_tid_sym : symmetric (same_tid S). 
Proof. unfold same_tid. basic_solver. Qed.

Lemma same_tid_trans : transitive (same_tid S). 
Proof. unfold same_tid, transitive. ins. by rewrite H. Qed.

Lemma sb_Einit_Eninit WF : sb ≡ Einit × Eninit ∪ ⦗Eninit⦘ ⨾ sb ⨾ ⦗Eninit⦘. 
Proof. 
  unfold same_relation; split.
  { rewrite sbE at 1; auto.
    rewrite <- restr_relE.
    rewrite acts_set_split.
    rewrite restr_set_union. 
    rewrite !restr_relE.
    rewrite sb_ninit; eauto.
    basic_solver. }
  apply inclusion_union_l.
  { by apply sb_init. }
  basic_solver.
Qed.

Lemma sb_seq_Eninit_l WF : ⦗Eninit⦘ ⨾ sb ≡ ⦗Eninit⦘ ⨾ sb ⨾ ⦗Eninit⦘.  
Proof.
  rewrite sb_Einit_Eninit; auto.
  basic_solver 42.
Qed.

Lemma sb_seq_Eninit_r WF : sb ⨾ ⦗Eninit⦘ ≡ sb.  
Proof.
  unfold same_relation; splits.
  { basic_solver. }
  rewrite sb_Einit_Eninit; auto.
  apply inclusion_union_l; basic_solver. 
Qed.

Lemma cf_same_tid : cf ⊆ same_tid S.
Proof. unfold ES.cf. basic_solver. Qed.

Lemma cfE : cf ≡ ⦗E⦘ ⨾ cf ⨾ ⦗E⦘.
Proof. unfold ES.cf, ES.acts_ninit_set. basic_solver. Qed. 

Lemma cfEninit : cf ≡ ⦗Eninit⦘ ⨾ cf ⨾ ⦗Eninit⦘.
Proof. unfold ES.cf. basic_solver. Qed.

Lemma ncfEinit_l : ⦗Einit⦘ ⨾ cf ≡ ∅₂.
Proof. 
  unfold ES.cf, ES.acts_ninit_set.
  basic_solver.
Qed.

Lemma ncfEinit_r : cf ⨾ ⦗Einit⦘ ≡ ∅₂.
Proof. 
  unfold ES.cf, ES.acts_ninit_set.
  basic_solver.
Qed.

Lemma ncfEinit_lr : ⦗Einit⦘ ⨾ cf ⨾ ⦗Einit⦘ ≡ ∅₂.
Proof. 
  unfold ES.cf, ES.acts_ninit_set.
  basic_solver.
Qed.

Lemma cf_irr : irreflexive cf.
Proof. basic_solver. Qed.

Lemma cf_sym : symmetric cf.
Proof. 
  unfold ES.cf, symmetric.
  ins. 
  apply restr_relE. 
  apply restr_relE in H. 
  generalize dependent H.
  generalize dependent y.
  generalize dependent x.
  fold (symmetric (restr_rel Eninit (same_tid S \ sb⁼))).
  apply restr_sym. 
  apply minus_sym; [by apply same_tid_sym | by apply crs_sym].
Qed.

Lemma same_thread WF : ⦗Eninit⦘ ⨾ same_tid S ⨾ ⦗Eninit⦘ ≡ ⦗Eninit⦘ ⨾ sb⁼ ⨾ ⦗Eninit⦘ ∪ cf.
Proof.
  unfold ES.cf.
  rewrite <- !restr_relE.
  rewrite restr_minus.
  rewrite unionC.
  rewrite <- union_minus; auto.
  rewrite crsE.
  rewrite !restr_union.
  rewrite unionA.
  apply inclusion_union_l.
  { basic_solver. } 
  rewrite <- restr_union, <- csE.
  rewrite <- cs_restr.
  rewrite <- (unionK (restr_rel Eninit (same_tid S))).
  assert (symmetric (restr_rel Eninit (same_tid S))) as SYM. 
  { apply restr_sym. apply same_tid_sym. }
  rewrite <- (transp_sym SYM) at 2. 
  rewrite <- csE.
  apply clos_sym_mori.
  rewrite <- (set_interK Eninit) at 1.
  rewrite <- restr_restr.
  apply restr_rel_mori; auto.
  rewrite restr_relE.
  apply (sb_tid WF).
Qed.  

Lemma n_sb_cf x y (Ex : E x) (Ey : E y) : ~ (sb x y /\ cf x y).
Proof. 
  red. intros [SB CF].
  destruct 
    (excluded_middle_informative (Einit x), excluded_middle_informative (Einit y)) 
    as [[INITx | nINITx]  [INITy | nINITy]].
  { eapply ncfEinit_lr.
    eapply seq_eqv_lr.
    splits; [|by apply CF|]; auto. }
  { eapply ncfEinit_l.
    eapply seq_eqv_l.
    splits; eauto. }
  { eapply ncfEinit_r.
    eapply seq_eqv_r.
    splits; eauto. }
  assert (Eninit x) as EnINITx.
  { unfold ES.acts_ninit_set.
    basic_solver. }
  assert (Eninit y) as EnINITy.
  { unfold ES.acts_ninit_set.
    basic_solver. }
  unfold ES.cf in CF.
  assert ((same_tid S \ sb⁼) x y) as HH.
  { unfolder in CF; desf. }
  unfold minus_rel in HH.
  destruct HH as [STID nSBcrs].
  apply nSBcrs.
  unfold clos_refl_sym; auto.
Qed.

Lemma ew_irr WF : irreflexive ew.
Proof. generalize cf_irr (ewc WF). basic_solver. Qed.

Lemma rmwE WF : rmw ≡ ⦗E⦘ ⨾ rmw ⨾ ⦗E⦘.
Proof.
split; [|basic_solver].
arewrite (rmw ⊆ rmw ∩ rmw) at 1.
rewrite (rmwi WF) at 1.
arewrite (immediate sb ⊆ sb).
rewrite (sbE WF).
basic_solver.
Qed.

Lemma rfE WF : rf ≡ ⦗E⦘ ⨾ rf ⨾ ⦗E⦘.
Proof.
  unfold ES.rf.
  arewrite (ew^? ⨾ jf ≡ ⦗E⦘ ⨾ ew^? ⨾ jf ⨾ ⦗E⦘) at 1.
  2: { assert (⦗E⦘ ⨾ ew^? ⨾ jf ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ (ew^? ⨾ jf) ⨾ ⦗E⦘) as HH
         by basic_solver. rewrite HH.
         by rewrite <- minus_eqv_rel_helper. }
  rewrite crE.
  rewrite !seq_union_l.
  rewrite !seq_union_r.
  relsf.
  apply union_more.
  { apply WF.(jfE). }
  rewrite WF.(ewE).
  rewrite WF.(jfE).
  rewrite !seqA.
  relsf.
Qed.

Lemma rfD WF : rf ≡ ⦗W⦘ ⨾ rf ⨾ ⦗R⦘.
Proof.
  unfold ES.rf.
  arewrite (ew^? ⨾ jf ≡ ⦗W⦘ ⨾ ew^? ⨾ jf ⨾ ⦗R⦘) at 1.
  2: { assert (⦗W⦘ ⨾ ew^? ⨾ jf ⨾ ⦗R⦘ ≡ ⦗W⦘ ⨾ (ew^? ⨾ jf) ⨾ ⦗R⦘) as HH
         by basic_solver. rewrite HH.
         by rewrite <- minus_eqv_rel_helper. }
  rewrite crE.
  rewrite !seq_union_l.
  rewrite !seq_union_r.
  relsf.
  apply union_more.
  { apply WF.(jfD). }
  rewrite WF.(ewD).
  rewrite WF.(jfD).
  rewrite !seqA.
  relsf.
Qed.
    
Lemma rfl WF : rf ⊆ same_loc.
Proof.
  unfold ES.rf.
  rewrite inclusion_minus_rel.
  rewrite WF.(jfl).
  rewrite WF.(ewl).
  generalize same_loc_trans.
  basic_solver.
Qed.

Lemma rfv WF : funeq val rf.
Proof.
  unfold ES.rf.
  apply funeq_minus.
  generalize WF.(jfv) WF.(ewv) funeq_seq.
  basic_solver.
Qed.

Lemma frE WF : fr ≡ ⦗E⦘ ⨾ fr ⨾ ⦗E⦘.
Proof.
  unfold ES.fr. rewrite WF.(rfE).
  rewrite WF.(coE).
  basic_solver 10.
Qed.

Lemma frD WF : fr ≡ ⦗R⦘ ⨾ fr ⨾ ⦗W⦘.
Proof.
  unfold ES.fr. rewrite WF.(rfD).
  rewrite WF.(coD).
  basic_solver 10.
Qed.

Lemma rfrf_in_ew WF : rf ⨾ rf⁻¹ ⊆ ew^?.
Proof.
  unfold ES.rf. intros x y [z [[[p [HH DD]] BB] [[q [AA EE]] CC]]].
  assert (p = q); subst.
  { eapply jff; eauto. }
  generalize WF.(ew_trans) WF.(ew_sym) HH AA.
  basic_solver 10.
Qed.

Lemma rffr_in_co WF : rf ⨾ fr ⊆ co.
Proof.
  intros x y [z [HH [p [AA BB]]]].
  edestruct rfrf_in_ew; eauto.
  { exists z. split; [apply HH|apply AA]. }
  { desf. }
  apply WF.(ew_co_in_co). eexists. eauto.
Qed.

Lemma frco_in_fr WF : fr ⨾ co ⊆ fr.
Proof.
  intros x y [z [[p [AA BB]] HH]].
  red. eexists. splits; eauto.
  eapply WF.(co_trans); eauto.
Qed.

(******************************************************************************)
(** ** Continuation properites *)
(******************************************************************************)

Lemma cont_sb_domE k lang st WF (KK : K (k, existT _ lang st)) : 
  cont_sb_dom S k ⊆₁ E.
Proof. 
  unfolder. 
  unfold cont_sb_dom.
  ins; desf.
  { unfold acts_init_set, set_inter in H; desf. }
  unfolder in H; desf.
  { eapply WF.(K_inEninit). apply KK. }
  apply WF.(sbE) in H.
  unfolder in H; desf.
Qed.

Lemma cont_cf_domEninit k lang st WF (KK : K (k, existT _ lang st)) : 
  cont_cf_dom S k ⊆₁ Eninit.
Proof. 
  unfolder. 
  unfold cont_cf_dom.
  ins; desf.
  { unfold acts_ninit_set, acts_init_set, set_minus; splits; desf. 
    red. intros [_ EINITx]. 
    apply init_tid_K; auto.
    do 2 eexists; eauto. }
  unfold dom_rel, codom_rel, seq, eqv_rel, set_union in H; desf.
  { apply cfEninit in H.
    unfold seq, eqv_rel in H; desf. }
  apply sb_seq_Eninit_r in H0; auto. 
  unfold seq, eqv_rel in H0; desf.
Qed.

Lemma cont_cf_tid k lang st WF e
      (KK : K (k, existT _ lang st)) 
      (cfKe: cont_cf_dom S k e) : 
  tid e = cont_thread S k.
Proof. 
  assert (Eninit e) as NINITe.
  { eapply cont_cf_domEninit; eauto. }
  unfold cont_thread, cont_cf_dom in *.
  edestruct k eqn:EQk.
  { desf. }
  assert (Eninit eid) as NINITeid.
  { eapply K_inEninit; eauto. }
  unfolder in cfKe; desf.
  fold (ES.same_tid S e z).
  apply same_tid_sym.
  eapply sb_tid; eauto.
  unfolder. 
  eexists; splits; eauto. 
Qed.

Lemma cont_cf_cont_sb k lang st WF (KK : K (k, existT _ lang st)) : 
  cont_cf_dom S k ≡₁ (E ∩₁ Tid (cont_thread S k)) \₁ cont_sb_dom S k. 
Proof. 
  unfold cont_thread, cont_sb_dom, cont_cf_dom. 
  unfold ES.acts_init_set.
  unfold set_inter, set_minus, set_equiv, set_subset.
  edestruct k eqn:EQk. 
  { splits; ins; splits; desf. 
    red; ins; desf.
    eapply init_tid_K; eauto. }
  assert (Eninit eid) as ENIeid.
  { eapply K_inEninit; eauto. }
  assert (E eid) as Eeid. 
  { eapply K_inEninit; eauto. }
  splits. 
  { intros x [CFx | SBx].
    { unfold dom_rel, seq, eqv_rel, clos_refl in *; desf.
      assert (E x) as Ex. 
      { apply cfE in CFx. 
        unfold seq, eqv_rel in CFx. 
        desf. } 
      splits; desf. 
      { by eapply cf_same_tid. }
      red; ins; desf. 
      { eapply cf_irr; eauto. } 
      eapply n_sb_cf; [apply Ex | apply Eeid | eauto]. }
    unfold dom_rel, codom_rel, seq, eqv_rel, clos_refl in *. 
    destruct SBx as [a [b [[EQab EQeid] SBx]]].
    rewrite <- EQab, <- EQeid in *.
    assert (E x) as Ex. 
    { apply sbE in SBx; auto.  
      unfold seq, eqv_rel in SBx. 
      desf. } 
    assert ((⦗Eninit⦘ ⨾ sb ⨾ ⦗Eninit⦘) eid x) as SBNIx.
    { eapply sb_seq_Eninit_l; auto.
      unfold seq, eqv_rel; eauto.  } 
    splits; auto. 
    { symmetry; eapply sb_tid; auto. }
    red. ins. desf. 
    { eapply sb_irr; eauto. }
    eapply sb_irr, sb_trans; eauto. }
  intros x [[Ex STID] NSBDOM].
  assert (Eninit x) as ENIx.
  { unfold ES.acts_ninit_set, ES.acts_init_set in *. 
    unfold set_inter, set_minus in *.
    splits; auto. 
    red; splits; auto. 
    apply ENIeid; splits; auto; desf; congruence. }
  destruct (excluded_middle_informative (cf x eid)) as [CF | nCF].
  { left. basic_solver 10. } 
  unfold dom_rel, codom_rel, seq, eqv_rel, clos_refl in *.   
  right. do 2 exists eid.
  splits; auto.
  assert ((⦗Eninit⦘ ⨾ same_tid S ⨾ ⦗Eninit⦘) x eid) as STIDNI.
  { unfold seq, eqv_rel. 
    eexists x; splits; auto.  
    eexists eid; splits; auto. } 
  eapply same_thread in STIDNI; auto. 
  destruct STIDNI as [SBx | CFx].
  { unfold seq, eqv_rel, clos_refl_sym in SBx.
    destruct SBx as [z [[EQz _] HH]].
    destruct HH as [z' [[REFL | [SBx | SBx]] [EQeid _]]];
    rewrite <- EQz, EQeid in *; auto. 
    all: exfalso; apply NSBDOM; do 2 exists eid; auto. }
  exfalso; auto. 
Qed.      

End EventStructure.
End ES.