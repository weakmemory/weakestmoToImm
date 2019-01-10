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

Definition acts_set (S : t) := fun x => x < S.(next_act).
Definition acts_init_set (S : t) :=
  S.(acts_set) ∩₁ (fun x => S.(tid) x = tid_init).
Definition acts_ninit_set (S : t) := S.(acts_set) \₁ S.(acts_init_set).

Definition cont_set (S : t) := fun x => In x S.(cont).

Definition same_tid (S : t) := fun x y => S.(tid) x = S.(tid) y.
Definition same_lab (S : t) := fun x y => S.(lab) x = S.(lab) y.

Definition jfe (S : t) := S.(jf) \ S.(sb).
Definition coe (S : t) := S.(co) \ S.(sb).
Definition jfi (S : t) := S.(jf) ∩ S.(sb).
Definition coi (S : t) := S.(co) ∩ S.(sb).

Definition cf (S : t) :=
  ⦗ S.(acts_ninit_set) ⦘ ⨾ (S.(same_tid) \ (S.(sb)⁼)) ⨾ ⦗ S.(acts_ninit_set) ⦘.

Definition cf_free (S : t) X := ⦗ X ⦘ ⨾ cf S ⨾ ⦗ X ⦘ ⊆ ∅₂. 

Definition rf (S : t) := S.(ew)^? ⨾ S.(jf) \ S.(cf).

Definition rfe (S : t) := S.(rf) \ S.(sb).
Definition rfi (S : t) := S.(rf) ∩ S.(sb).

Lemma rfi_union_rfe (S : t) : S.(rf) ≡ S.(rfi) ∪ S.(rfe).
Proof.
  unfold rfe, rfi. split; [|by eauto with hahn].
  unfolder. ins. destruct (classic (sb S x y)) as [AA|AA].
  all: generalize H AA; basic_solver.
Qed.

Definition fr (S : t) := S.(rf)⁻¹ ⨾ S.(co).

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
  | CInit  i => ES.acts_set S ∩₁ (fun x => S.(tid) x = i) 
  | CEvent e => dom_rel (cf S ⨾ ⦗ eq e ⦘) ∪₁ codom_rel (⦗ eq e ⦘ ⨾ sb S)
  end.

Hint Unfold ES.acts_set ES.acts_init_set ES.cf : unfolderDb.

Section EventStructure.

Variable S : ES.t.

Notation "'E'"      := S.(ES.acts_set).
Notation "'Einit'"  := S.(ES.acts_init_set).
Notation "'Eninit'" := S.(ES.acts_ninit_set).

Notation "'tid'" := S.(ES.tid).
Notation "'lab'" := S.(ES.lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).

Notation "'same_tid'" := (same_tid S).
Notation "'same_loc'" := (same_loc lab).

Notation "'Tid' t" := (fun x => tid x = t) (at level 1).

Notation "'sb'"    := S.(ES.sb).
Notation "'rmw'"   := S.(ES.rmw).
Notation "'ew'"    := S.(ES.ew).
Notation "'jf'"    := S.(ES.jf).
Notation "'jfi'"    := S.(ES.jfi).
Notation "'jfe'"    := S.(ES.jfe).
Notation "'rf'"    := S.(ES.rf).
Notation "'fr'"    := S.(ES.fr).
Notation "'co'"    := S.(ES.co).
Notation "'cf'"    := S.(ES.cf).

Notation "'K'"     := S.(ES.cont_set).

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

Definition seqn (e : eventid) : nat := 
  countNatP (dom_rel (⦗ Tid (tid e) ⦘ ⨾ sb ⨾ ⦗ eq e ⦘)) (next_act S).

Record Wf :=
  { initL : forall l, (exists b, E b /\ loc b = Some l) ->
                      exists a, Einit a /\ loc a = Some l ;
    init_lab : forall e (INIT : Einit e),
        exists l, lab e = Astore Xpln Opln l 0 ;
    init_uniq : inj_dom Einit loc;
    
    sbE : sb ≡ ⦗E⦘ ⨾ sb ⨾ ⦗E⦘ ;
    sb_init : Einit × Eninit ⊆ sb;
    sb_ninit : sb ⨾ ⦗Einit⦘ ≡ ∅₂;
    sb_tid : ⦗Eninit⦘ ⨾ sb ⨾ ⦗Eninit⦘ ⊆ same_tid;

    sb_irr     : irreflexive sb;
    sb_trans   : transitive sb;
    sb_prcl    : prefix_clos (sb ∩ same_tid);

    (* TODO: It might be more convenient to state it like this:
      ` forall X (NCF : cf_free S X), 
          is_total (E ∩₁ X) (sb ∩ same_tid); `
     *)
    sb_ncf_tot :
      forall X (inclE : X ⊆₁ E) (NCF : cf_free S X), 
        is_total X (sb ∩ same_tid); 

    seqn_after_null : E ⊆₁ codom_rel (<| fun x => seqn x = 0 |> ;; (sb^? ∩ same_tid));

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
    event_K  : forall e (EE: Eninit e) (NRMW : ~ dom_rel rmw e),
        exists c, K (CEvent e, c);
    K_inEninit : forall e c (inK: K (CEvent e, c)), Eninit e;  
  }.

Implicit Type WF : Wf.

(******************************************************************************)
(** ** acts_set properties *)
(******************************************************************************)

Lemma acts_set_split : E ≡₁ Einit ∪₁ Eninit.
Proof.
  unfold ES.acts_init_set, ES.acts_ninit_set.
  rewrite set_unionC.
  eapply set_union_minus.
  basic_solver.
Qed.

Lemma acts_ninit_set_incl : Eninit ⊆₁ E. 
Proof. unfold ES.acts_ninit_set. basic_solver. Qed.

(******************************************************************************)
(** ** same_tid properites *)
(******************************************************************************)

Lemma same_tid_refl : reflexive same_tid.
Proof. unfold ES.same_tid. basic_solver. Qed.

Lemma same_tid_sym : symmetric same_tid. 
Proof. unfold ES.same_tid. basic_solver. Qed.

Lemma same_tid_trans : transitive same_tid. 
Proof. unfold ES.same_tid, transitive. ins. by rewrite H. Qed.

(******************************************************************************)
(** ** sb properties *)
(******************************************************************************)

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
Proof. rewrite sb_Einit_Eninit; auto. basic_solver 42. Qed.

Lemma sb_seq_Eninit_r WF : sb ⨾ ⦗Eninit⦘ ≡ sb.  
Proof.
  unfold same_relation; splits.
  { basic_solver. }
  rewrite sb_Einit_Eninit; auto.
  apply inclusion_union_l; basic_solver. 
Qed.

(******************************************************************************)
(** ** cf properties *)
(******************************************************************************)

Lemma cfE : cf ≡ ⦗E⦘ ⨾ cf ⨾ ⦗E⦘.
Proof. unfold ES.cf, ES.acts_ninit_set. basic_solver. Qed. 

Lemma cfEninit : cf ≡ ⦗Eninit⦘ ⨾ cf ⨾ ⦗Eninit⦘.
Proof. unfold ES.cf. basic_solver. Qed.

Lemma cf_same_tid : cf ⊆ same_tid.
Proof. unfold ES.cf. basic_solver. Qed.

Lemma ncfEinit_l : ⦗Einit⦘ ⨾ cf ≡ ∅₂.
Proof. unfold ES.cf, ES.acts_ninit_set. basic_solver. Qed.

Lemma ncfEinit_r : cf ⨾ ⦗Einit⦘ ≡ ∅₂.
Proof. unfold ES.cf, ES.acts_ninit_set. basic_solver. Qed.

Lemma ncfEinit : ⦗Einit⦘ ⨾ cf ⨾ ⦗Einit⦘ ≡ ∅₂.
Proof. unfold ES.cf, ES.acts_ninit_set. basic_solver. Qed.

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
  fold (symmetric (restr_rel Eninit (same_tid \ sb⁼))).
  apply restr_sym. 
  apply minus_sym; [by apply same_tid_sym | by apply crs_sym].
Qed.

(******************************************************************************)
(** ** sb/cf properties *)
(******************************************************************************)

Lemma same_thread WF : ⦗Eninit⦘ ⨾ same_tid ⨾ ⦗Eninit⦘ ≡ ⦗Eninit⦘ ⨾ sb⁼ ⨾ ⦗Eninit⦘ ∪ cf.
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
  rewrite <- (unionK (restr_rel Eninit same_tid)).
  assert (symmetric (restr_rel Eninit same_tid)) as SYM. 
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

Lemma same_thread_cf_free WF X (CFF : cf_free S X) : 
  ⦗Eninit ∩₁ X⦘ ⨾ same_tid ⨾ ⦗Eninit ∩₁ X⦘ ≡ ⦗Eninit ∩₁ X⦘ ⨾ sb⁼ ⨾ ⦗Eninit ∩₁ X⦘.
Proof.
  rewrite set_interC with (s := Eninit) at 1 3.
  rewrite !AuxRel.id_inter, !seqA.
  rewrite <- !seqA with (r1 := ⦗Eninit⦘).
  rewrite <- !seqA with (r3 := ⦗X⦘).
  rewrite !seqA with (r1 := ⦗Eninit⦘).
  rewrite same_thread; auto. 
  relsf. rewrite !seqA.
  arewrite (⦗X⦘ ⨾ cf ⨾ ⦗X⦘ ≡ ∅₂).
  { red; split; [by apply CFF | basic_solver]. }
  basic_solver 42.
Qed.

Lemma n_sb_cf x y (Ex : E x) (Ey : E y) : ~ (sb x y /\ cf x y).
Proof. 
  red. intros [SB CF].
  destruct 
    (excluded_middle_informative (Einit x), excluded_middle_informative (Einit y)) 
    as [[INITx | nINITx]  [INITy | nINITy]].
  { eapply ncfEinit.
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
  assert ((same_tid \ sb⁼) x y) as HH.
  { unfolder in CF; desf. }
  unfold minus_rel in HH.
  destruct HH as [STID nSBcrs].
  apply nSBcrs.
  unfold clos_refl_sym; auto.
Qed.

Lemma cf_sb_in_cf WF : cf ⨾ sb ⊆ cf.
Proof.
  intros x y [z [CF SB]].
  red. red in CF.
  destruct_seq CF as [AA BB].
  apply seq_eqv_l. split; auto.
  apply WF.(sbE) in SB. destruct_seq SB as [EZ EY].
  assert (Eninit y) as CC.
  { red. split; auto.
    intros DD. eapply WF.(sb_ninit).
    apply seq_eqv_r. split; eauto. }
  apply seq_eqv_r. split; [split|]; auto.
  { etransitivity; [by apply CF|].
    apply sb_tid; auto.
    apply seq_eqv_l. split; auto.
    apply seq_eqv_r. split; auto. }
  intros DD. apply CF.
  red in DD. desf.
  { generalize SB. basic_solver. }
  { assert (same_tid x y) as STIDxy.
    { eapply WF.(sb_tid). basic_solver. }
    assert (same_tid z y) as STIDzy.
    { eapply WF.(sb_tid). basic_solver. }
    assert ((sb ∩ same_tid)⁼ x z).
    { eapply WF.(sb_prcl); unfold inter_rel; eauto. }
    unfolder in *. 
    basic_solver. }
  assert (sb z x) as UU by (eapply sb_trans; eauto).
  generalize UU. basic_solver.
Qed.

(******************************************************************************)
(** ** cf_free properties *)
(******************************************************************************)

Lemma cf_free_subset X X' (SUBS : X' ⊆₁ X) : 
  cf_free S X -> cf_free S X'.
Proof. unfold cf_free; basic_solver 42. Qed.

Lemma cf_free_eq X X' (EQ : X' ≡₁ X) : 
  cf_free S X <-> cf_free S X'.
Proof. destruct EQ; unfold cf_free; split; basic_solver 42. Qed.

(******************************************************************************)
(** ** rmw properties *)
(******************************************************************************)

Lemma rmwE WF : rmw ≡ ⦗E⦘ ⨾ rmw ⨾ ⦗E⦘.
Proof.
  split; [|basic_solver].
  arewrite (rmw ⊆ rmw ∩ rmw) at 1.
  rewrite (rmwi WF) at 1.
  arewrite (immediate sb ⊆ sb).
  rewrite (sbE WF).
  basic_solver.
Qed.

(******************************************************************************)
(** ** ew properties *)
(******************************************************************************)

Lemma ew_irr WF : irreflexive ew.
Proof. generalize cf_irr (ewc WF). basic_solver. Qed.

(******************************************************************************)
(** ** jf properties *)
(******************************************************************************)

Lemma jfiE WF : jfi ≡ ⦗E⦘ ⨾ jfi ⨾ ⦗E⦘.
Proof. unfold ES.jfi. rewrite WF.(jfE). basic_solver. Qed.

Lemma jfeE WF : jfe ≡ ⦗E⦘ ⨾ jfe ⨾ ⦗E⦘.
Proof. unfold ES.jfe. rewrite WF.(jfE). basic_solver. Qed.

Lemma jfiD WF : jfi ≡ ⦗W⦘ ⨾ jfi ⨾ ⦗R⦘.
Proof. unfold ES.jfi. rewrite WF.(jfD). basic_solver. Qed.

Lemma jfeD WF : jfe ≡ ⦗W⦘ ⨾ jfe ⨾ ⦗R⦘.
Proof. unfold ES.jfe. rewrite WF.(jfD). basic_solver. Qed.

(******************************************************************************)
(** ** rf properties *)
(******************************************************************************)

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

(******************************************************************************)
(** ** fr properties *)
(******************************************************************************)

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


(******************************************************************************)
(** ** rf/fr properties *)
(******************************************************************************)

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
(** ** continuation properites *)
(******************************************************************************)

Lemma K_inE e lang st WF (KK : K (CEvent e, existT _ lang st)) : E e.
Proof. 
  apply K_inEninit in KK; auto.  
  unfold ES.acts_ninit_set, set_minus in KK.
  desf.
Qed.

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

Lemma cont_sb_dom_Einit k lang st WF (KK : K (k, existT _ lang st)) : 
  Einit ⊆₁ cont_sb_dom S k.
Proof. 
  unfold cont_sb_dom.
  unfolder. 
  ins; desf.
  exists eid, eid; splits; auto. 
  right. apply sb_Einit_Eninit; auto. 
  unfold ES.acts_init_set. unfolder.
  left; split; auto.   
  eapply K_inEninit; eauto. 
Qed.  

Lemma cont_sb_prcl k lang st WF (KK : K (k, existT _ lang st)) : 
  sb ⨾ ⦗ cont_sb_dom S k ⦘ ⊆ ⦗ cont_sb_dom S k ⦘ ⨾ sb.
Proof.
  unfold cont_sb_dom. 
  intros x y HH. 
  apply seq_eqv_r in HH.
  destruct HH as [SB CONTy].
  destruct k. 
  { exfalso. eapply sb_ninit; auto. 
    apply seq_eqv_r. eauto. }
  unfolder in CONTy. desf.
  { unfolder; splits; eauto. }
  unfolder; splits; eauto.
  eexists; splits; [|auto].
  right. eapply sb_trans; eauto. 
Qed.

Lemma cont_sb_nfrwd e k lang st WF 
      (KE : k = CEvent e) 
      (KK : K (k, existT _ lang st)) : 
  codom_rel (⦗ eq e ⦘ ⨾ sb) ⊆₁ set_compl (cont_sb_dom S k).
Proof. 
  unfold cont_sb_dom.   
  unfolder; desf. 
  intros x [e' [EQe SB]].
  subst e'. 
  red. ins. desf.
  { eapply sb_irr; eauto. } 
  eapply sb_irr; [|eapply sb_trans]; eauto. 
Qed.

Lemma cont_cf_domE k lang st WF (KK : K (k, existT _ lang st)) : 
  cont_cf_dom S k ⊆₁ E.
Proof. 
  unfold cont_cf_dom. 
  destruct k; [basic_solver|].
  apply set_subset_union_l. split.
  { rewrite cfE. basic_solver. }
  rewrite sbE; auto. basic_solver.
Qed.

Lemma cont_cf_domEninit k lang st WF (KK : K (k, existT _ lang st)) : 
  cont_cf_dom S k ⊆₁ Eninit.
Proof. 
  unfolder. 
  unfold cont_cf_dom.
  ins; desf.
  { destruct H as [Ex Tidx].
    unfold acts_ninit_set, acts_init_set, set_minus; splits; desf.
    red. intros [_ EINITx]. 
    apply init_tid_K; auto.
    do 2 eexists; splits; eauto. }
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
  { destruct cfKe as [Ee TIDe]. desf. }
  assert (Eninit eid) as NINITeid.
  { eapply K_inEninit; eauto. }
  unfolder in cfKe; desf.
  fold (ES.same_tid S e z).
  apply same_tid_sym.
  eapply sb_tid; eauto.
  unfolder. 
  eexists; splits; eauto. 
Qed.

Lemma cont_cf_Tid_ k lang st WF 
      (KK : K (k, existT _ lang st)) :
  cont_cf_dom S k ⊆₁ Tid (cont_thread S k).
Proof. red. ins. eapply cont_cf_tid; eauto. Qed.

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
  assert ((⦗Eninit⦘ ⨾ same_tid ⨾ ⦗Eninit⦘) x eid) as STIDNI.
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

(******************************************************************************)
(** ** seqn properites *)
(******************************************************************************)

Lemma seqn_sb WF : seqn □ (sb ∩ same_tid) ⊆ Nat.lt.
Proof. 
  unfolder. unfold seqn, Nat.lt.
  intros a b [x [y [[SB STID] [SEQx SEQy]]]].
  rewrite <- SEQx, <- SEQy. 
  apply countNatP_lt with (e:=x); auto.
  { intros z [v PP]. destruct_seq PP as [DD EE]; subst.
    eexists. apply seq_eqv_l. split; auto.
    { congruence. }
    apply seq_eqv_r. split; [|by eauto].
    eapply sb_trans; eauto. }
  { red; unfolder; ins; desf.
    eapply sb_irr; eauto. }
  { red; unfolder; eauto 10. }
  apply sbE, seq_eqv_lr in SB; desf. 
Qed.  

Lemma seqn_sb_alt WF x y (STID : same_tid x y) (SB : sb x y) : 
  seqn x < seqn y. 
Proof. eapply seqn_sb; unfolder; eauto 50. Qed.

(* Lemma countNatP_select (s : nat -> Prop) n i j (LT : i < j) (HH : countNatP s n = j) :  *)
(*   exists x, ⟪ IN : s' ⊆₁ s ⟫ /\ ⟪ CNTX : countNatP s' n = i ⟫. *)
(* Proof. admit. Admitted. *)

Lemma seqn_init WF y (Ey : Einit y) : seqn y = 0.
Proof.
  unfold seqn.
  arewrite (⦗Tid (tid y)⦘ ⨾ sb ⨾ ⦗eq y⦘ ≡ ∅₂).
  2: { rels. apply countNatP_empty. }
  split; [|basic_solver].
  arewrite (eq y ⊆₁ Einit) by (intros x HH; desf).
  rewrite sb_ninit; auto.
  rels.
Qed.

Lemma seqn_immsb WF x y 
      (STID : same_tid x y)
      (IMMSB : immediate sb x y) :
  seqn y = 1 + seqn x.
Proof. 
  unfold seqn.
  arewrite (⦗Tid (tid x)⦘ ⨾ sb ⨾ ⦗eq x⦘ ≡ (sb ∩ same_tid) ⨾ ⦗eq x⦘).
  { basic_solver. }
  arewrite (⦗Tid (tid y)⦘ ⨾ sb ⨾ ⦗eq y⦘ ≡ (sb ∩ same_tid) ⨾ ⦗eq y⦘).
  { basic_solver. }
  assert (immediate (sb ∩ same_tid) x y) as IMMSB_STID. 
  { apply immediateE. 
    unfolder. 
    splits; auto. 
    { by apply immediate_in. }
    apply immediateE in IMMSB.
    unfolder in IMMSB.
    red. ins. 
    apply IMMSB.
    basic_solver. }
  erewrite trans_prcl_immediate_seqr_split with (y := y). 
  all: eauto using inter_trans, sb_trans, same_tid_trans, sb_prcl. 
  rewrite dom_cross.
  2: { red. basic_solver. }
  rewrite countNatP_union.
  { eapply Nat.add_wd; auto. 
    eapply countNatP_eq.
    apply immediate_in, sbE, seq_eqv_lr in IMMSB; desf. } 
  unfolder; ins; desf. 
  eapply sb_irr; eauto.  
Qed.

Lemma seqn_inj WF X thread (XinTID : X ⊆₁ Eninit ∩₁ Tid thread) (CFF : cf_free S X) : 
  inj_dom X seqn. 
Proof. 
  intros x y Xx Xy EQ.
  assert (Eninit x /\ tid x = thread) as HA. 
  { apply XinTID in Xx. unfold set_inter in Xx. desf. }
  assert (Eninit y /\ tid y = thread) as HB. 
  { apply XinTID in Xy. unfold set_inter in Xy. desf. }
  assert (same_tid x y) as STID by desf. 
  assert ((⦗Eninit ∩₁ X⦘ ⨾ same_tid ⨾ ⦗Eninit ∩₁ X⦘) x y) as HH.
  { unfolder; splits; desf. }
  apply same_thread_cf_free in HH; auto. 
  apply seq_eqv_lr in HH.
  destruct HH as [_ [SB _]].
  unfold clos_refl_sym in SB; desf.
  { assert (seqn x < seqn y) as HH; [|omega]. 
    eapply seqn_sb_alt; eauto. }
  assert (seqn y < seqn x) as HH; [|omega]. 
  eapply seqn_sb_alt; eauto.
Qed.

Lemma E_alt : E ≡₁ fun x => List.In x (first_nat_list S.(next_act)).
Proof. red; split; red; apply first_nat_list_In_alt. Qed.

Lemma sb_well_founded WF : well_founded sb.
Proof.
  apply fsupp_well_founded.
  3: by apply WF.(sb_trans).
  2: by apply WF.(sb_irr).
  red. ins.
  eexists. intros. apply E_alt.
  apply WF.(sbE) in REL. by destruct_seq_l REL as XX.
Qed.

Lemma sb_transp_well_founded WF : well_founded sb⁻¹.
Proof.
  apply fsupp_well_founded.
  3: { apply transitive_transp. by apply WF.(sb_trans). }
  2: { red. intros x HH. red in HH. eapply WF.(sb_irr); eauto. }
  red. ins.
  eexists. intros. apply E_alt.
  apply WF.(sbE) in REL. by destruct_seq REL as [YY XX].
Qed.

Lemma sb_dom_cf_free WF y : cf_free S (dom_rel (sb ⨾ ⦗eq y⦘)).
Proof.
  red. unfolder. ins; desf.
  apply H7.
  destruct (classic (z1 = y0)) as [|NEQ]; subst.
  { by left. }
  right.
  (* PROBLEM: to prove it, one needs to use sb_ncf_tot,
     which requires the statement we are working on.
     
     A possible solution is to move the statement to Wf and
     prove sb_ncf_tot as a lemma using sb_dom_cf_free
     (and probably smth else). *)

  (* edestruct WF.(sb_ncf_tot) with (X := dom_rel (sb ;; <| eq y2 |>)) *)
  (*   as [AA|AA]. *)
  (* 5: by eauto. *)
  (* { rewrite WF.(sbE). basic_solver. } *)
Admitted.

Lemma sb_imm_split_r WF : sb ≡ sb^? ;; immediate sb.
Proof.
  split.
  2: { generalize WF.(sb_trans). basic_solver. }
  intros x y SB.
  assert (exists z, immediate sb z y) as [z IMM].
  { edestruct wf_imm_succ as [w [HH AA]].
    { by apply sb_transp_well_founded. }
    { eauto. }
    eexists. split.
    { apply HH. }
    intros. eapply AA; red; eauto. }
  eexists. split; [|by eauto].
  destruct (classic (x = z)) as [|NEQ]; subst.
  { by constructor. }
  edestruct WF.(sb_ncf_tot) with (X := dom_rel (sb ;; <| eq y |>))
    as [AA|AA].
  5: by eauto.
  { rewrite WF.(sbE). basic_solver. }
  { apply sb_dom_cf_free. }
  { eexists. apply seq_eqv_r. split; eauto. }
  { eexists. apply seq_eqv_r. split; eauto. apply IMM. }
  { generalize AA. basic_solver. }
  exfalso. eapply IMM; eauto. apply AA.
Qed.

Lemma seqn_pred WF y i (Ey : E y) (LT : i < seqn y) : 
  exists x, 
    ⟪ SBxy : sb x y ⟫ /\ 
    ⟪ STIDxy : same_tid x y ⟫ /\ 
    ⟪ SEQNx : seqn x = i ⟫. 
Proof.
  (* set (EE := Ey). *)
  (* apply WF.(seqn_after_null) in EE. *)
  (* destruct EE as [z EE]. destruct_seq_l EE as Z0. destruct EE as [[|SB] TT]; subst. *)
  (* { omega. } *)



  (* unfold seqn. *)

  (* remember (seqn y) as SY. *)
  (* generalize dependent y. *)
  (* induction SY. *)
  (* { inv LT. } *)
  (* inversion LT; subst. *)
  (* unfold seqn in LT. *)

admit. Admitted.

End EventStructure.
End ES.