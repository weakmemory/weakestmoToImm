Require Import Omega Setoid Program.Basics.
From hahn Require Import Hahn.
From imm Require Import Events.
Require Import AuxDef.
Require Import AuxRel.

Set Implicit Arguments.

Definition eventid := nat.

Inductive cont_label :=
| CInit  (tid : thread_id)
| CEvent (eid : eventid).

Module Language.
Record t :=
  mk { syntax : Type;
       state : Type;
       init : syntax -> state;
       is_terminal : state -> Prop;
       step : list label -> state -> state -> Prop
     }.
End Language.

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

Definition rf (S : t) := S.(ew) ⨾ S.(jf) \ S.(cf).

Definition rfe (S : t) := S.(rf) \ S.(sb).
Definition rfi (S : t) := S.(rf) ∩ S.(sb).

Lemma jfi_union_jfe (S : t) : S.(jf) ≡ S.(jfi) ∪ S.(jfe).
Proof.
  unfold jfe, jfi. split; [|by eauto with hahn].
  unfolder. ins. destruct (classic (sb S x y)) as [AA|AA].
  all: generalize H AA; basic_solver.
Qed.

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

(* An initial event structure. *)
Definition init loc_list conts :=
  let loc_labs :=
      map (fun l => Astore Xpln Opln l 0) loc_list 
  in
  {| next_act := length loc_labs ;
     lab  := list_to_fun Nat.eq_dec
                         (Afence Orlx)
                         (indexed_list loc_labs); 
     tid  := fun _ => tid_init ;
     sb   := ∅₂ ;
     rmw  := ∅₂ ;
     jf   := ∅₂ ;
     co   := ∅₂ ;
     ew   := ∅₂ ;
     cont := conts ;
  |}.

(******************************************************************************)
(** ** cf_free morphisms *)
(******************************************************************************)

Add Parametric Morphism : cf_free with signature
  eq ==> set_subset --> impl as cf_free_mori.
Proof. 
  intros S s s' SUBS.
  unfold cf_free.
  red. by rewrite SUBS.
Qed.

Add Parametric Morphism : cf_free with signature
  eq ==> set_equiv ==> iff as cf_free_more.
Proof. 
  intros S s s' EQV.
  unfold cf_free.
  by rewrite EQV.
Qed.

Section EventStructure.

Variable S : ES.t.

Notation "'E'"      := S.(ES.acts_set).
Notation "'Einit'"  := S.(ES.acts_init_set).
Notation "'Eninit'" := S.(ES.acts_ninit_set).

Notation "'tid'" := S.(ES.tid).
Notation "'lab'" := S.(ES.lab).
Notation "'loc'" := (loc lab).
Notation "'val'" := (val lab).

Notation "'same_lab'" := (same_lab S).
Notation "'same_tid'" := (same_tid S).
Notation "'same_loc'" := (same_loc lab).
Notation "'same_val'" := (same_val lab).

Notation "'Tid_' t" := (fun x => tid x = t) (at level 1).
Notation "'NTid_' t" := (fun x => tid x <> t) (at level 1).
Notation "'Loc_' l" := (fun x => loc x = l) (at level 1).

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
  countNatP (dom_rel (sb ∩ same_tid ⨾ ⦗ eq e ⦘)) (next_act S).

Definition init_loc l :=
      exists a,
        << EINA : Einit a >> /\
        << LOCA : loc a = Some l >>.

Record Wf :=
  { initL : forall l b (EB : E b) (LB : loc b = Some l),
      init_loc l ;
    
    init_lab : forall e (INIT : Einit e),
      exists l, lab e = Astore Xpln Opln l 0 ;
    init_uniq : inj_dom Einit loc ;
    
    sbE : sb ≡ ⦗E⦘ ⨾ sb ⨾ ⦗E⦘ ;
    sb_init : Einit × Eninit ⊆ sb;
    sb_ninit : sb ⨾ ⦗Einit⦘ ≡ ∅₂;
    sb_tid : ⦗Eninit⦘ ⨾ sb ⊆ same_tid;

    sb_irr     : irreflexive sb;
    sb_trans   : transitive sb;
    sb_prcl    : downward_total (sb ∩ same_tid);

    sb_tot : forall e (EE : E e),
        is_total (dom_rel (sb ⨾ ⦗ eq e ⦘) \₁ Einit) sb; 

    seqn_after_null : E ⊆₁ codom_rel (⦗ fun x => seqn x = 0 ⦘ ⨾ (sb^? ∩ same_tid));

    rmwD : rmw ≡ ⦗R⦘ ⨾ rmw ⨾ ⦗W⦘ ;
    rmwl : rmw ⊆ same_loc ;
    rmwi : rmw ⊆ immediate sb ;

    jfE : jf ≡ ⦗E⦘ ⨾ jf ⨾ ⦗E⦘ ;
    jfD : jf ≡ ⦗W⦘ ⨾ jf ⨾ ⦗R⦘ ;
    jfl : jf ⊆ same_loc ;
    jfv : funeq val jf ;
    jff : functional jf⁻¹ ;
    jf_complete : E ∩₁ R ⊆₁ codom_rel jf;
    jf_ncf : jf ∩ cf ≡ ∅₂; 

    coE : co ≡ ⦗E⦘ ⨾ co ⨾ ⦗E⦘ ;
    coD : co ≡ ⦗W⦘ ⨾ co ⨾ ⦗W⦘ ;
    col : co ⊆ same_loc ;
    co_init : ⦗Einit⦘ ⨾ same_loc ⨾ ⦗E ∩₁ W⦘ ⊆ co ;
    co_irr : irreflexive co ;
    co_trans : transitive co ;
    co_total : 
      forall ol a b 
             (aW : (E ∩₁ W ∩₁ Loc_ ol) a) 
             (bW : (E ∩₁ W ∩₁ Loc_ ol) b) 
             (nEW : ~ ew a b),
        co a b \/ co b a ;

    ewE : ew ≡ ⦗E⦘ ⨾ ew ⨾ ⦗E⦘ ;
    ewD : ew ≡ ⦗W⦘ ⨾ ew ⨾ ⦗W⦘ ;
    ewm : ew ⊆ (Rlx × Rlx)^? ;
    ewl : ew ⊆ same_loc ;
    ewv : ew ⊆ same_val ;
    ewc : ew ⊆ cf^? ; 
    ew_refl : ⦗E ∩₁ W⦘ ⊆ ew ;
    ew_sym : symmetric ew ;
    ew_trans : transitive ew ;

    ew_co : ew ∩ co ≡ ∅₂ ;
    ew_co_in_co : ew ⨾ co ⊆ co ;
    co_ew_in_co : co ⨾ ew ⊆ co ;

    (* term_def_K : forall state (TERM : lang.(Language.is_terminal) state), *)
    (*     ~ (exists lbl state', lang.(Language.step) lbl state state'); *)
    init_tid_K :
      ~ (exists c k,
            ⟪ KK  : K (k, c) ⟫ /\
            ⟪ CTK : cont_thread S k = tid_init ⟫);
    unique_K : forall c c' (CK : K c) (CK' : K c') (FF : fst c = fst c'),
        snd c = snd c';
    event_K  : forall e (EE: Eninit e) (NRMW : ~ dom_rel rmw e),
        exists c, ⟪ KC : K (CEvent e, c) ⟫;
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

Lemma acts_init_set_inW WF : Einit ⊆₁ W.
Proof. 
  intros x INIT.
  apply init_lab in INIT; auto.
  desf. unfold is_w. by rewrite INIT.
Qed.

Lemma acts_ninit_set_incl : Eninit ⊆₁ E. 
Proof. unfold ES.acts_ninit_set. basic_solver. Qed.

Lemma Tid_compl_NTid t : Tid_ t ∪₁ NTid_ t ≡₁ ⊤₁. 
Proof. 
  unfolder. split; [done|]. ins.
  destruct (classic (tid x = t)); auto.
Qed.

Lemma set_split_Tid X t : X ≡₁ X ∩₁ Tid_ t ∪₁ X ∩₁ NTid_ t.
Proof. apply set_split, Tid_compl_NTid. Qed.

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

Lemma Tid_sb_prcl WF t : 
  dom_rel (sb ⨾ ⦗Tid_ t⦘) ⊆₁ Einit ∪₁ Tid_ t.
Proof. 
  rewrite seq_eqv_r.
  intros x [y [SB TID]].
  assert (E x) as Ex.
  { apply sbE in SB; auto. 
    generalize SB. basic_solver. }
  apply acts_set_split in Ex.
  destruct Ex as [Init | nInit]; [by left|].
  right. erewrite sb_tid; eauto. basic_solver. 
Qed.

Lemma Tid_sb_fwcl WF t (nInit : t <> tid_init) : 
  codom_rel (⦗Tid_ t⦘ ⨾ sb) ⊆₁ Tid_ t.
Proof. 
  rewrite seq_eqv_l.
  intros y [x [TID SB]].
  subst t. symmetry. 
  erewrite sb_tid; eauto.
  apply seq_eqv_l. 
  split; auto.
  unfold acts_ninit_set, acts_init_set.
  unfolder; split; auto. 
  { apply sbE in SB; auto. 
    generalize SB. basic_solver. }
  by intros [_ TID]. 
Qed.

Lemma NTid_sb_prcl WF t : 
  dom_rel (sb ⨾ ⦗NTid_ t⦘) ⊆₁ Einit ∪₁ NTid_ t.
Proof. 
  rewrite seq_eqv_r.
  intros x [y [SB nTID]].
  assert (E x) as Ex.
  { apply sbE in SB; auto. 
    generalize SB. basic_solver. }
  apply acts_set_split in Ex.
  destruct Ex as [Init | nInit]; [by left|].
  right. erewrite sb_tid; eauto. basic_solver. 
Qed.

Lemma NTid_sb_fwcl WF t : 
  codom_rel (⦗NTid_ t \₁ Einit⦘ ⨾ sb) ⊆₁ NTid_ t.
Proof. 
  rewrite seq_eqv_l.
  intros y [x [[nTID nInit] SB]].
  intros TID. apply nTID.  
  subst t. 
  erewrite sb_tid; eauto.
  apply seq_eqv_l. 
  split; auto.
  unfold acts_ninit_set, acts_init_set.
  unfolder; split; auto. 
  apply sbE in SB; auto. 
  generalize SB. basic_solver.
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
Proof. unfold ES.cf. basic_solver. Qed.

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
  rewrite <- (transp_sym_equiv SYM) at 2. 
  rewrite <- csE.
  apply clos_sym_mori.
  rewrite <- (set_interK Eninit) at 1.
  rewrite <- restr_restr.
  apply restr_rel_mori; auto.
  rewrite restr_relE.
  rewrite <- seqA. rewrite WF.(sb_tid).
  basic_solver.
Qed.  

Lemma same_thread_alt WF x y 
      (Enix : Eninit x) 
      (Eniy : Eninit y) 
      (EQtid : tid x = tid y) :
  sb⁼ x y \/ cf x y. 
Proof. 
  edestruct same_thread as [HH _]; auto.
  assert ((⦗Eninit⦘ ⨾ same_tid ⨾ ⦗Eninit⦘) x y) as STID.
  { basic_solver. }
  specialize (HH x y STID).
  generalize HH. basic_solver 10.
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

Lemma n_sb_cf WF x y : ~ (sb x y /\ cf x y).
Proof. 
  red. intros [SB CF].
  assert (E x) as Ex.
  { apply sbE, seq_eqv_lr in SB; auto. desf. }
  assert (E y) as Ey.
  { apply sbE, seq_eqv_lr in SB; auto. desf. }
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
    apply seq_eqv_l. split; auto. }
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

Lemma ew_eqvW WF ws (inEW : ws ⊆₁ E ∩₁ W) : ws ⊆₁ dom_rel (ew ⨾ ⦗ws⦘).
Proof. 
  intros x WW. 
  exists x, x. 
  unfolder; splits; eauto.
  eapply ew_refl; auto.
  apply inEW in WW.
  generalize WW. 
  basic_solver 10.
Qed.

Lemma ew_domW WF r (domEW : dom_rel r ⊆₁ E ∩₁ W) : r ⊆ ew ⨾ r.
Proof. 
  intros x y RR. 
  eexists x. 
  splits; auto.
  eapply ew_refl; auto.
  specialize (domEW x).
  assert ((E ∩₁ W) x) as EWx.
  { apply domEW. basic_solver. }
  generalize EWx. basic_solver 10.
Qed.

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

Lemma jf_eq WF : jf ∩ eq ⊆ ∅₂.
Proof. rewrite jfD; auto. type_solver. Qed.

Lemma jf_nEinit WF : jf ⨾ ⦗Einit⦘ ⊆ ∅₂.
Proof. rewrite jfD, acts_init_set_inW; auto. type_solver. Qed.

Lemma jf_nEinit_alt WF : jf ⊆ Einit × Eninit ∪ Eninit × Eninit. 
Proof. 
  rewrite jfE; auto.
  rewrite acts_set_split.
  rewrite id_union. relsf.
  rewrite jf_nEinit; auto.
  basic_solver.
Qed.

Lemma jf_same_tid WF : jf ∩ same_tid ≡ jf ∩ (⦗Eninit⦘ ⨾ same_tid ⨾ ⦗Eninit⦘). 
Proof.
  erewrite <- inter_absorb_r
    with (r := jf) at 1.
  2 : eapply jf_nEinit_alt; auto.
  rewrite !inter_union_r, !inter_union_l.
  arewrite_false (jf ∩ Einit × Eninit ∩ same_tid).
  { unfold acts_ninit_set, acts_init_set, ES.same_tid.
    unfolder. ins. desf. exfalso. 
    eapply H3. split; auto.
    congruence. }
  basic_solver 6.
Qed.

Lemma jf_in_ew_jf WF : jf ⊆ ew ⨾ jf.
Proof.
  intros x y JF.
  unfolder; eexists; splits; eauto. 
  eapply ew_refl; auto.
  unfolder; splits; auto.
  { apply jfE in JF; auto. 
    generalize JF. basic_solver. }
  apply jfD in JF; auto. 
  generalize JF. basic_solver. 
Qed.

Lemma jf_in_rf WF : jf ⊆ rf.
Proof.
  unfold ES.rf.
  intros x y JF.
  split.
  { apply jf_in_ew_jf; auto. }
  red. ins. 
  eapply jf_ncf; auto.
  split; eauto.
Qed.

(******************************************************************************)
(** ** rf properties *)
(******************************************************************************)

Lemma rfE WF : rf ≡ ⦗E⦘ ⨾ rf ⨾ ⦗E⦘.
Proof.
  unfold ES.rf.
  arewrite (ew ⨾ jf ≡ ⦗E⦘ ⨾ ew ⨾ jf ⨾ ⦗E⦘) at 1.
  2: { assert (⦗E⦘ ⨾ ew ⨾ jf ⨾ ⦗E⦘ ≡ ⦗E⦘ ⨾ (ew ⨾ jf) ⨾ ⦗E⦘) as HH
         by basic_solver. rewrite HH.
         by rewrite <- minus_eqv_rel_helper. }
  relsf.
  rewrite WF.(ewE).
  rewrite WF.(jfE).
  rewrite !seqA.
  relsf.
Qed.

Lemma rfD WF : rf ≡ ⦗W⦘ ⨾ rf ⨾ ⦗R⦘.
Proof.
  unfold ES.rf.
  arewrite (ew ⨾ jf ≡ ⦗W⦘ ⨾ ew ⨾ jf ⨾ ⦗R⦘) at 1.
  2: { assert (⦗W⦘ ⨾ ew ⨾ jf ⨾ ⦗R⦘ ≡ ⦗W⦘ ⨾ (ew ⨾ jf) ⨾ ⦗R⦘) as HH
         by basic_solver. rewrite HH.
         by rewrite <- minus_eqv_rel_helper. }
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

Lemma rf_complete WF : E ∩₁ R ⊆₁ codom_rel rf.
Proof. rewrite <- jf_in_rf; apply WF. Qed.

Lemma rf_trf_in_ew WF : rf ⨾ rf⁻¹ ⊆ ew. 
Proof. 
  unfold ES.rf.
  rewrite transp_minus, transp_seq.
  rewrite !inclusion_minus_rel.
  rewrite !seqA.
  arewrite (jf ⨾ jf⁻¹ ⊆ ⦗⊤₁⦘).
  { (* TODO : introduce corresponding lemma *)
    arewrite (jf ≡ ((jf)⁻¹)⁻¹).
    rewrite <- functional_alt.
    apply WF. }
  rewrite transp_sym_equiv.
  { rewrite seq_id_l. 
    rewrite transitiveI.
    apply WF. }
  apply WF.
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
(** ** co properites *)
(******************************************************************************)

(* Lemma co_total WF ol ww  *)
(*       (WS : ww ⊆₁ E ∩₁ W ∩₁ Loc_ ol)  *)
(*       (nCF : cf_free S ww) : *)
(*   is_total ww co. *)
(* Proof.  *)
(*   red. ins.  *)
(*   eapply co_connex; auto. *)
(*   generalize nCF. unfold cf_free. *)
(*   basic_solver 10. *)
(* Qed. *)

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

Lemma cont_sb_tid k lang st WF (KK : K (k, existT _ lang st)) : 
  cont_sb_dom S k ⊆₁ Einit ∪₁ Tid_ (cont_thread S k).
Proof. 
  unfold cont_thread, cont_sb_dom.
  destruct k.
  { basic_solver. }
  rewrite sb_Einit_Eninit; auto.
  sin_rewrite sb_tid; auto.
  basic_solver.
Qed.

Lemma cont_sb_prcl k lang st WF (KK : K (k, existT _ lang st)) : 
  dom_rel (sb ⨾ ⦗ cont_sb_dom S k ⦘) ⊆₁ cont_sb_dom S k.
Proof. 
  intros x [y SB].
  destruct_seq_r SB as YY. red in YY. desf.
  { exfalso. eapply sb_ninit; eauto.
    apply seq_eqv_r. eauto. }
  red. generalize WF.(sb_trans) YY SB. basic_solver 10.
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
  unfold ES.cf in cfKe.
  unfolder in cfKe; desf.
  fold (ES.same_tid S e z).
  apply same_tid_sym.
  eapply sb_tid; eauto.
  unfolder. 
  eexists; splits; eauto. 
Qed.

Lemma cont_cf_Tid_ k lang st WF 
      (KK : K (k, existT _ lang st)) :
  cont_cf_dom S k ⊆₁ Tid_ (cont_thread S k).
Proof. red. ins. eapply cont_cf_tid; eauto. Qed.

Lemma cont_cf_cont_sb k lang st WF (KK : K (k, existT _ lang st)) : 
  cont_cf_dom S k ≡₁ (E ∩₁ Tid_ (cont_thread S k)) \₁ cont_sb_dom S k. 
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
      eapply n_sb_cf; eauto. }
    unfold dom_rel, codom_rel, seq, eqv_rel, clos_refl in *. 
    destruct SBx as [a [b [[EQab EQeid] SBx]]].
    rewrite <- EQab, <- EQeid in *.
    assert (E x) as Ex. 
    { apply sbE in SBx; auto.  
      unfold seq, eqv_rel in SBx. 
      desf. } 
    assert ((⦗Eninit⦘ ⨾ sb) eid x) as SBNIx.
    { apply seq_eqv_l. split; auto. } 
    splits; auto. 
    { symmetry; apply sb_tid; auto. }
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

Lemma cont_sb_cont_cf_inter_false k lang st WF (KK : K (k, existT _ lang st)) : 
  cont_sb_dom S k ∩₁ cont_cf_dom S k ⊆₁ ∅.
Proof. erewrite cont_cf_cont_sb; eauto. basic_solver. Qed.

Lemma cont_thread_sb_cf k lang st WF (KK : K (k, existT _ lang st)) : 
  (E ∩₁ Tid_ (cont_thread S k)) ≡₁ (cont_sb_dom S k \₁ Einit) ∪₁ cont_cf_dom S k. 
Proof. 
  rewrite set_unionC.
  erewrite cont_cf_cont_sb; eauto.
  arewrite 
    (E ∩₁ Tid_ (cont_thread S k) \₁ cont_sb_dom S k ≡₁ 
     E ∩₁ Tid_ (cont_thread S k) \₁ (cont_sb_dom S k \₁ Einit)).
  { rewrite set_minus_minus_r.
    arewrite (E ∩₁ Tid_ (cont_thread S k) ∩₁ Einit ≡₁ ∅).
    { split; [|done].
      unfold ES.acts_init_set.
      unfolder. ins. desc.
      eapply init_tid_K; eauto.
      do 2 eexists. splits; eauto. 
      congruence. }
    basic_solver. }
  apply set_union_minus.
  red. intros x [KSB NINIT]. split. 
  { eapply cont_sb_domE; eauto. }
  unfold cont_thread, cont_sb_dom in *. 
  destruct k.
  { exfalso. auto. }
  unfolder in KSB. desf.
  apply sb_Einit_Eninit in KSB; auto.
  unfold union in KSB; desf.
  { destruct KSB as [INIT _]. exfalso. auto. }
  eapply sb_tid; auto.
  apply seq_eqv_lr in KSB. 
  basic_solver.
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
  { intros z [v [u [[SB' STID'] EQx]]].
    unfolder in EQx; desc; subst.
    eexists. apply seq_eqv_r.
    split; eauto. split.
    { eapply sb_trans; eauto. }
    eapply same_tid_trans; eauto. }
  { red; unfolder; ins; desf.
    eapply sb_irr; eauto. }
  { red; unfolder; eauto 10. }
  apply sbE, seq_eqv_lr in SB; desf. 
Qed.  

Lemma seqn_sb_alt WF x y (STID : same_tid x y) (SB : sb x y) : 
  seqn x < seqn y. 
Proof. eapply seqn_sb; unfolder; eauto 50. Qed.

Lemma seqn_init WF y (Ey : Einit y) : seqn y = 0.
Proof.
  unfold seqn.
  arewrite (sb ∩ same_tid ⨾ ⦗eq y⦘ ≡ ∅₂).
  2: { rels. apply countNatP_empty. }
  split; [|basic_solver].
  arewrite (eq y ⊆₁ Einit) by (intros x HH; desf).
  rewrite <- lib.AuxRel.seq_eqv_inter_lr. 
  rewrite sb_ninit; auto. rels.
Qed.

Lemma seqn_immsb WF x y 
      (STID : same_tid x y)
      (IMMSB : immediate sb x y) :
  seqn y = 1 + seqn x.
Proof. 
  unfold seqn.
  assert (immediate (sb ∩ same_tid) x y) as IMMSB_STID. 
  { eapply immediate_inter. red; split; auto. }
  erewrite trans_prcl_immediate_seqr_split with (y := y). 
  all: eauto using inter_trans, sb_trans, same_tid_trans, sb_prcl. 
  rewrite dom_cross; [|red; basic_solver].
  rewrite countNatP_union.
  { apply immediate_in, sbE, seq_eqv_lr in IMMSB; desf.
    eapply Nat.add_wd; auto. 
    by eapply countNatP_eq. } 
  unfolder; ins; desf. 
  eapply sb_irr; eauto.  
Qed.

Lemma seqn_inj WF X thread (XinTID : X ⊆₁ Eninit ∩₁ Tid_ thread) (CFF : cf_free S X) : 
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

Lemma sb_dom_cf_free WF x : cf_free S (dom_rel (sb ⨾ ⦗eq x⦘)).
Proof.
  red. unfolder. ins. desf. 
  eapply n_sb_cf; splits; eauto.
  eapply cf_sb_in_cf; auto.
  eexists; splits.
  { eapply cf_sym; eauto. }
  done.
Qed.

Lemma sb_imm_split_r WF : sb ≡ sb^? ⨾ immediate sb.
Proof.
  split.
  2: { generalize WF.(sb_trans). basic_solver. }
  intros x y SB.
  destruct (classic (exists w, sb x w /\ sb w y))
    as [[p [SBL SBR]]|NN].
  2: { exists x. split; [by constructor|].
       split; auto. ins.
       apply NN. eexists. eauto. }
  assert (exists z, immediate sb z y) as [z IMM].
  { edestruct wf_imm_succ as [w [HH AA]].
    { by apply sb_transp_well_founded. }
    { eauto. }
    eexists. split.
    { apply HH. }
    intros. eapply AA; red; eauto. }
  eexists. split; [|by eauto].
  destruct (classic (p = z)) as [|NEQ]; subst.
  { by constructor. }

  assert (E p) as EP.
  { apply WF.(sbE) in SBR. generalize SBR. basic_solver. }
  assert (~ Einit p) as NIP.
  { intros HH. eapply WF.(sb_ninit).
    apply seq_eqv_r. eauto. }

  assert (~ Einit z) as NIZ.
  { intros HH. eapply IMM.
    2: by apply SBR.
    apply sb_init; auto. repeat (split; auto). }
  
  edestruct WF.(sb_tot) with (e := y) as [AA|AA].
  4: by eauto.
  { apply WF.(sbE) in SB. generalize SB. basic_solver. }
  1,2: split; [eexists; apply seq_eqv_r; eauto|]; auto.
  { by split; eauto; apply IMM. }
  { right. eapply WF.(sb_trans); eauto. }
  exfalso.
  eapply IMM; eauto.
Qed.

Lemma sb_clos_imm_split WF : sb ≡ (immediate sb)⁺.
Proof.
  eapply ct_imm1.
  { apply WF.(sb_irr). }
  { apply WF.(sb_trans). }
  rewrite (dom_l WF.(sbE)).
  rewrite dom_seq, dom_eqv, E_alt.
  reflexivity.
Qed.

Lemma seqn_after_null_imm WF y (EE : Eninit y) :
  exists x,
    ⟪ EX   : Eninit x ⟫ /\
    ⟪ SEQX : seqn x = 0 ⟫ /\
    ⟪ IMM  : (immediate sb) ^^ (seqn y) x y ⟫.
Proof.
  remember (seqn y) as n.
  generalize dependent y.
  induction n.
  { ins. exists y. splits; auto. done. }
  ins.
  destruct EE as [EE NIY].
  set (EI := EE).
  apply seqn_after_null in EI; auto.
  destruct EI as [x EI]. destruct_seq_l EI as SX.
  destruct EI as [[|SB] AA]; subst.
  { rewrite SX in *. desf. }
  apply WF.(sb_imm_split_r) in SB.
  destruct SB as [z [[|SB] IMM]]; subst.
  { set (BB := IMM).
    apply WF.(seqn_immsb) in BB; auto.
    rewrite SX in *. rewrite <- Heqn in *.
    inv BB. simpls.
    exists z. splits; auto.
    2: { generalize IMM. basic_solver. }
    split.
    { destruct IMM as [IMM _]. apply WF.(sbE) in IMM.
      generalize IMM. basic_solver. }
    intros [EZ EI].
    apply NIY. red. split; auto.
      by rewrite <- AA. }
  assert (Eninit z) as NIZ.
  { apply WF.(sb_Einit_Eninit) in SB.
    generalize SB. basic_solver. }
  assert (same_tid z y) as ST.
  { apply WF.(sb_tid). apply seq_eqv_l. split; auto.
    apply IMM. }
  set (BB := IMM).
  apply WF.(seqn_immsb) in BB; auto.
  rewrite <- Heqn in *. inv BB.
  specialize_full IHn; eauto.
  desf. exists x0. splits; eauto.
  eexists. splits; eauto.
Qed.

Lemma seqn_pred_imm WF n y (EE : Eninit y)
      (SS : seqn y = 1 + n) :
  exists x,
    ⟪ EX   : Eninit x ⟫ /\
    ⟪ SEQX : seqn x = n ⟫ /\
    ⟪ IMM  : immediate sb x y ⟫.
Proof.
  edestruct seqn_after_null_imm; eauto. desf.
  rewrite SS in IMM. simpls.
  destruct IMM as [z [IMMs IMM]].
  assert (Eninit z) as BB.
  { destruct n; simpls.
    { red in IMMs. desf. }
    assert (sb x z) as CC.
    { assert ((immediate sb) ^^ n ⨾ immediate sb ⊆ sb) as DD.
      2: by apply DD.
      rewrite pow_rt, <- ct_end. by apply sb_clos_imm_split. }
    apply WF.(sb_seq_Eninit_r) in CC.
    generalize CC. basic_solver. }
  assert (same_tid z y) as AA.
  { apply WF.(sb_tid). apply seq_eqv_l.
    split; auto. apply IMM. }
  exists z. splits; eauto.
  assert (seqn y = 1 + seqn z) as HH.
  2: { rewrite SS in HH. inv HH. }
  apply seqn_immsb; auto.
Qed.

Lemma seqn_pred_imm_i WF i n y (EE : Eninit y)
      (SS : seqn y = i + n) :
  exists x,
    ⟪ EX   : Eninit x ⟫ /\
    ⟪ SEQX : seqn x = n ⟫ /\
    ⟪ IMM  : (immediate sb) ^^ i x y ⟫.
Proof.
  generalize dependent n.
  generalize dependent y.
  induction i.
  { ins. exists y. splits; auto. done. }
  ins.
  edestruct seqn_pred_imm; eauto. desf.
  eapply IHi in SEQX; eauto. desf.
  exists x0. splits; eauto.
  eexists. eauto.
Qed.

Lemma seqn_pred WF y n (Ey : E y) (LT : n < seqn y) : 
  exists x, 
    ⟪ SBxy : sb x y ⟫ /\ 
    ⟪ SEQNx : seqn x = n ⟫ /\
    ⟪ STIDxy : same_tid x y ⟫.
Proof.
  assert (exists i, seqn y = i + n) as [i HH].
  { exists (seqn y - n). omega. }
  apply seqn_pred_imm_i in HH; auto.
  2: { split; auto. intros EI. apply WF.(seqn_init) in EI.
       rewrite EI in LT. omega. }
  desf.
  assert (sb^? x y) as YY.
  { apply pow_rt in IMM. apply rtE in IMM.
    destruct IMM as [IMM|IMM]; [left|right].
    { apply IMM. }
    apply sb_clos_imm_split; auto. }
  destruct YY as [|YY]; subst.
  { omega. }
  exists x. splits; auto.
  apply WF.(sb_tid).
  apply seq_eqv_l. split; auto.
Qed.

Lemma seqn_E WF x (NN : seqn x > 0) : E x.
Proof.
  unfold seqn in *.
  destruct (classic (exists y, (sb ∩ same_tid) y x)) as [[y [SB _]]|HH].
  { apply WF.(sbE) in SB. by destruct_seq SB as [AA BB]. }
  assert (dom_rel (sb ∩ same_tid ⨾ ⦗eq x⦘) ≡₁ ∅) as AA.
  { split; [|basic_solver].
    generalize HH. basic_solver. }
  rewrite AA in NN.
  rewrite countNatP_empty in NN.
  omega.
Qed.

Lemma seqn_Eninit WF x (NN : seqn x > 0) : Eninit x.
Proof.
  split.
  { by apply seqn_E. }
  intros AA. apply seqn_init in AA; auto.
  omega.
Qed.

Lemma seqn_lt_cont_cf_dom WF eid x 
      (EE : E eid)
      (EQtid : tid eid = tid x)
      (LTseqn : seqn eid < seqn x) : 
  cont_cf_dom S (CEvent eid) x.
Proof.
  red.
  destruct (classic (sb eid x)) as [SB|NSB].
  { right. eexists. apply seq_eqv_l. split; eauto. }
  left. eexists. apply seq_eqv_r. split; eauto.
  red.
  assert (seqn x > 0) as SS by omega.
  assert (Eninit x) as EX by (by apply seqn_Eninit).
  assert (Eninit eid) as ENE.
  { split; auto.
    intros AA.
    apply EX. red. split.
    { apply EX. }
    rewrite <- EQtid. apply AA. }
  assert (same_tid x eid) as AA by (by red).
  apply seq_eqv_l. split; auto.
  apply seq_eqv_r. split; auto.
  split; auto.
  intros SB. red in SB. desf.
  { omega. }
  apply seqn_sb_alt in SB; auto.
  omega.
Qed.

End EventStructure.
End ES.
