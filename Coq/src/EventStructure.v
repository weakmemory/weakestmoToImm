Require Import Omega Setoid Program.Basics.
From PromisingLib Require Import Language.
From hahn Require Import Hahn.
From imm Require Import AuxDef Events.
Require Import AuxDef.
Require Import AuxRel.

Set Implicit Arguments.

Definition eventid := nat.

Inductive cont_label :=
| CInit  (tid : thread_id)
| CEvent (eid : eventid).

Definition init_write l := Astore Xpln Opln l 0.

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
                    { lang : Language.t (list label) &
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

(* immediate conflict *)
Definition icf (S : t) :=
  (* In the case of event structure with the empty set 
   * of initial events this definition is incorrect. 
   * In order to check that, consider two 
   * conflicting `first` events in some thread --- 
   * they are not in the immediate conflict 
   * according to this definition.
   * However we found the alternative definition 
   * (as given in the paper) hard to work with.
   * Thus the (temproary) solution is to keep this definition
   * and add the constraint `~ Einit ≡₁ ∅` to the Well-formdness predicate.
   * Techinacally, there are event structures with empty set of initial events.
   * Their corresponding programs should consist of `fences` only.
   * However, in this case these event structures are trivial 
   * in the sense that their only behaviour is that
   * consisting of the set of initial writes (which is empty).
   *)
  cf S ∩ (immediate (sb S)⁻¹ ⨾ immediate (sb S)).
  (* cf S \ ((sb S) ⁻¹ ⨾ (cf S) ∪ (cf S) ⨾ (sb S)). *)

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

Definition cont_last S k :=
  match k with
  | CInit  i => ES.acts_init_set S
  | CEvent e => eq e
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

Definition cont_icf_dom S c := 
  codom_rel (⦗cont_last S c⦘ ⨾ immediate (sb S) ⨾ ⦗fun x => tid S x = cont_thread S c⦘).

Definition cont_adjacent S k k' e e' := 
  ⟪ kREP' : k' = CEvent (opt_ext e e') ⟫ /\ 
  ⟪ kEQTID : ES.cont_thread S k = ES.cont_thread S k' ⟫ /\
  ⟪ nINITe : ES.acts_ninit_set S e ⟫ /\
  ⟪ nRMWde : e' = None -> ~ dom_rel (rmw S) e ⟫ /\
  ⟪ RMWe : eq e × eq_opt e' ⊆ ES.rmw S ⟫ /\
  ⟪ kSBDOM : ES.cont_sb_dom S k ≡₁ dom_rel (ES.sb S ⨾ ⦗eq e⦘) ⟫.

(* An initial event structure. *)
Definition init loc_list conts :=
  let loc_labs := map init_write loc_list in
  let acts := (fun e => e < length loc_labs) in
  {| next_act := length loc_labs ;
     lab  := list_to_fun Nat.eq_dec
                         (Afence Orlx)
                         (indexed_list loc_labs); 
     tid  := fun _ => tid_init ;
     sb   := ∅₂ ;
     rmw  := ∅₂ ;
     jf   := ∅₂ ;
     co   := ∅₂ ;
     ew   := ⦗ acts ⦘ ;
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
Notation "'jfi'"   := S.(ES.jfi).
Notation "'jfe'"   := S.(ES.jfe).
Notation "'rf'"    := S.(ES.rf).
Notation "'rfi'"   := S.(ES.rfi).
Notation "'rfe'"   := S.(ES.rfe).
Notation "'fr'"    := S.(ES.fr).
Notation "'co'"    := S.(ES.co).
Notation "'cf'"    := S.(ES.cf).
Notation "'icf'"    := S.(ES.icf).

Notation "'K'"     := S.(ES.cont_set).

Notation "'R'" := (fun a => is_true (is_r lab a)).
Notation "'W'" := (fun a => is_true (is_w lab a)).
Notation "'F'" := (fun a => is_true (is_f lab a)).
Notation "'RW'" := (R ∪₁ W).
Notation "'FR'" := (F ∪₁ R).
Notation "'FW'" := (F ∪₁ W).
Notation "'R_ex'" := (fun a => is_true (R_ex lab a)).

Notation "'Pln'" := (is_only_pln lab).
Notation "'ORlx'" := (is_only_rlx lab).
Notation "'Rlx'" := (is_rlx lab).
Notation "'Rel'" := (is_rel lab).
Notation "'Acq'" := (is_acq lab).
Notation "'Acqrel'" := (is_acqrel lab).
Notation "'Sc'" := (is_sc lab).

Definition seqn (e : eventid) : nat := 
  countNatP (dom_rel (sb ∩ same_tid ⨾ ⦗ eq e ⦘)) (next_act S).

Definition init_loc l :=
      exists a,
        ⟪ EINA : Einit a ⟫ /\
        ⟪ LOCA : loc a = Some l ⟫.

Record Wf :=
  { initL : forall l b (EB : E b) (LB : loc b = Some l),
      init_loc l ;
    
    init_lab : forall e (INIT : Einit e),
      exists l, lab e = init_write l ;
    init_uniq : inj_dom Einit loc ;
    (* see the comment about `icf` above *)
    init_nempty : ~ Einit ≡₁ ∅ ; 
    
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

    rmwD : rmw ≡ ⦗R_ex⦘ ⨾ rmw ⨾ ⦗W⦘ ;
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
    co_init : ⦗Einit⦘ ⨾ same_loc ⨾ ⦗Eninit ∩₁ W⦘ ⊆ co ;
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
    ewm : ew ⊆ (set_compl Rel × set_compl Rel)^? ;
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

    rmw_K :
      ~ (exists c e,
            ⟪ KK  : K (CEvent e, c) ⟫ /\
            ⟪ RMW : dom_rel rmw e ⟫);

    unique_K : forall c c' (CK : K c) (CK' : K c') (FF : fst c = fst c'),
        snd c = snd c';

    event_K  : forall e (EE: Eninit e) (NRMW : ~ dom_rel rmw e),
        exists c, ⟪ KC : K (CEvent e, c) ⟫;

    K_inEninit : forall e c (inK: K (CEvent e, c)), Eninit e;

    K_adj : forall lang st st' k k' e e' 
                   (KK : K (k , existT _ lang st )) 
                   (KK': K (k', existT _ lang st')) 
                   (ADJ : cont_adjacent S k k' e e'),
        exists lbl lbl', 
          ⟪ LBL  : lbl  = lab e ⟫ /\
          ⟪ LBL' : lbl' = option_map lab e' ⟫ /\
          ⟪ STEP : (Language.step lang) (opt_to_list lbl' ++ [lbl]) st st' ⟫ 
  }.

Implicit Type WF : Wf.

(******************************************************************************)
(** ** acts_set properties *)
(******************************************************************************)

Lemma E_alt : E ≡₁ fun x => List.In x (first_nat_list S.(next_act)).
Proof. red; split; red; apply first_nat_list_In_alt. Qed.

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

Lemma exists_acts_init WF : exists e, Einit e. 
Proof. 
  destruct (classic (exists e, Einit e)); auto.
  exfalso. apply init_nempty; auto.
  split; [|done].
  intros e INITe.
  red. apply H.
  eauto.
Qed.

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

Lemma sb_codom_ninit WF : codom_rel sb ⊆₁ Eninit. 
Proof. rewrite <- sb_seq_Eninit_r; auto. basic_solver. Qed.  

Lemma sb_clos_imm_split WF : sb ≡ (immediate sb)⁺.
Proof.
  eapply ct_imm1.
  { apply WF.(sb_irr). }
  { apply WF.(sb_trans). }
  rewrite (dom_l WF.(sbE)).
  rewrite dom_seq, dom_eqv, E_alt.
  reflexivity.
Qed.

Lemma sb_imm_split_r WF : sb ≡ sb^? ⨾ immediate sb.
Proof.
  split.
  2: { generalize WF.(sb_trans). basic_solver. }
  rewrite sb_clos_imm_split at 1; auto.
  rewrite ct_end.
  apply seq_mori; [|done].
  rewrite immediate_in.
  apply rt_of_trans. by apply sb_trans.
Qed.

Lemma sb_imm_split_l WF : sb ≡ immediate sb ⨾ sb^?.
Proof.
  split.
  2: { generalize WF.(sb_trans). basic_solver. }
  rewrite sb_clos_imm_split at 1; auto.
  rewrite ct_begin.
  apply seq_mori; [done|].
  rewrite immediate_in.
  apply rt_of_trans. by apply sb_trans.
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

Lemma immediate_tsb_functional WF x y z 
      (nINITy  : Eninit y)
      (IMMtSB  : immediate (sb)⁻¹ x y)
      (IMMtSB' : immediate (sb)⁻¹ x z) : 
  y = z.
Proof. 
  destruct IMMtSB  as [SB  nSB ].
  destruct IMMtSB' as [SB' nSB'].
  unfold transp in *.
  assert (Eninit z) as nINITz.
  { red. split.
    { apply sbE in SB'; auto.
      generalize SB'. basic_solver. }
    intros INITz.
    eapply (nSB' y); auto.
    apply sb_init; auto.
    basic_solver. }
  edestruct sb_prcl 
    as [EQ | HH]; eauto.
  { split; eauto.
    eapply sb_tid; auto.
    basic_solver. }
  { split; eauto.
    eapply sb_tid; auto.
    basic_solver. }
  destruct HH as [[HH _] | [HH _]].
  { exfalso. eapply nSB; eauto. }
  exfalso. eapply (nSB' y); auto.
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
(** ** icf properties *)
(******************************************************************************)

Lemma icfE : icf ≡ ⦗E⦘ ⨾ icf ⨾ ⦗E⦘.
Proof. unfold ES.icf. rewrite cfE. basic_solver 20. Qed.

Lemma icfEninit : icf ≡ ⦗Eninit⦘ ⨾ icf ⨾ ⦗Eninit⦘.
Proof. unfold ES.icf. rewrite cfEninit. basic_solver 20. Qed.

Lemma icf_same_tid : icf ⊆ same_tid.
Proof. unfold ES.icf. rewrite cf_same_tid. basic_solver. Qed.

Lemma icfEinit_l : ⦗Einit⦘ ⨾ icf ≡ ∅₂.
Proof. unfold ES.icf. generalize ncfEinit_l. basic_solver. Qed.

Lemma icfEinit_r : icf ⨾ ⦗Einit⦘ ≡ ∅₂.
Proof. unfold ES.icf. generalize ncfEinit_r. basic_solver. Qed.

Lemma icfEinit : ⦗Einit⦘ ⨾ cf ⨾ ⦗Einit⦘ ≡ ∅₂.
Proof. unfold ES.icf. generalize ncfEinit. basic_solver. Qed.

Lemma icf_irr : irreflexive icf.
Proof. unfold ES.icf. generalize cf_irr. basic_solver. Qed.

Lemma icf_sym : symmetric icf.
Proof. 
  unfold ES.icf.
  apply inter_sym.
  { apply cf_sym. }
  intros x y [z [IMMSB IMMSB']].
  exists z. split.
  { apply immediate_transp 
      with (r := sb). 
    apply IMMSB'. }
  apply immediate_transp 
      with (r := sb) in IMMSB. 
  apply IMMSB.
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
      (Ex : E x)
      (Eniy : Eninit y) 
      (EQtid : tid x = tid y) :
  sb⁼ x y \/ cf x y. 
Proof.
  apply acts_set_split in Ex.
  destruct Ex as [INITx | nINITx].
  { left. right. left. 
    apply sb_init; auto.
    basic_solver. }
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
  rewrite !id_inter, !seqA.
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
  unfolder. auto.
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
  unfolder in DD. desf.
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

Lemma sb_dom_cf_free WF x : cf_free S (dom_rel (sb ⨾ ⦗eq x⦘)).
Proof.
  red. unfolder. ins. desf. 
  eapply n_sb_cf; splits; eauto.
  eapply cf_sb_in_cf; auto.
  eexists; splits.
  { eapply cf_sym; eauto. }
  done.
Qed.

Lemma imm_tsb_imm_sb_in_cf WF :
  ((immediate sb)⁻¹ ⨾ immediate sb) ∩ same_tid ⊆ cf^?.
Proof.
  unfolder. ins. desf.
  destruct (classic (x = y)) as [|NEQ]; [by left|right].
  red.
  assert (Eninit x) as EX.
  { apply WF.(sb_seq_Eninit_r) in H.
      by destruct_seq_r H as AA. }
  assert (Eninit y) as EY.
  { apply WF.(sb_seq_Eninit_r) in H1.
      by destruct_seq_r H1 as AA. }
  apply seq_eqv_lr. splits; auto.
  split; auto.
  intros [|[HH|HH]]; desf.
  { by apply H2 with (c:=x). }
    by apply H3 with (c:=y).
Qed.

Lemma imm_tsb_imm_sb_in_icf WF :
  ((immediate sb)⁻¹ ⨾ immediate sb) ∩ same_tid ⊆ icf^?.
Proof.
  intros x y [[z [tIMMSB IMMSB]] STID].
  assert (cf^? x y) as CF.
  { apply WF.(imm_tsb_imm_sb_in_cf).
    basic_solver 10. }
  red. destruct CF as [|CF]; auto.
  right.
  unfold ES.icf.
  split; auto.
  exists z; splits; auto.
  by apply immediate_transp
    with (r := sb).
Qed.

Lemma sb_same_tid_alt WF :
  ⦗Eninit⦘ ⨾ sb ≡ sb ∩ same_tid.
Proof.
  split.
  { specialize (sb_tid WF). basic_solver. }
  rewrite sb_Einit_Eninit at 1; auto.
  rewrite inter_union_l.
  apply inclusion_union_l.
  { arewrite (Einit × Eninit ∩ same_tid ⊆ ∅₂); [|done].
    unfold ES.acts_ninit_set, "\₁", ES.acts_init_set, ES.same_tid, "~".
    unfolder. ins. desf. apply H2.
    split; auto.
    rewrite H3 in H0.
    auto. }
  basic_solver.
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

Lemma rmw_in_sb WF : rmw ⊆ sb.
Proof. rewrite WF.(rmwi). eauto with hahn. Qed.

Lemma rmwEninit WF : rmw ≡ ⦗Eninit⦘ ⨾ rmw ⨾ ⦗Eninit⦘.
Proof.
  split; [|basic_solver].
  rewrite WF.(rmwE).
  rewrite (dom_l WF.(rmwD)).
  unfolder. ins. desf.
  splits; auto.
  { split; auto. intros AA.
    apply WF.(init_lab) in AA.
    desf. unfold init_write in *.
    type_solver. }
  apply WF.(rmw_in_sb) in H0.
  apply WF.(sb_seq_Eninit_r) in H0.
    by destruct_seq_r H0 as AA.
Qed.

Lemma rmwt WF : rmw ⊆ same_tid.
Proof.
  rewrite WF.(rmwEninit).
  rewrite <- WF.(sb_tid).
  rewrite WF.(rmw_in_sb).
  basic_solver.
Qed.

Lemma rmwf WF : functional rmw⁻¹.
Proof.
  arewrite (rmw ⊆ immediate sb ∩ same_tid).
  { apply (inclusion_inter_r WF.(rmwi) WF.(rmwt)). }
  rewrite immediate_inter.
  by apply dwt_imm_f, sb_prcl.
Qed.

Lemma rmw_dom_ninit WF : dom_rel rmw ⊆₁ Eninit. 
Proof. rewrite rmwEninit; auto. basic_solver. Qed.

Lemma rmw_codom_ninit WF : codom_rel rmw ⊆₁ Eninit. 
Proof. 
  rewrite rmw_in_sb; auto.
  apply sb_codom_ninit; auto.
Qed.

Lemma rmw_codom_ndom WF : codom_rel rmw ⊆₁ set_compl (dom_rel rmw).
Proof. 
  intros y [x RMW] [z RMW'].
  apply WF.(rmwD) in RMW.
  apply WF.(rmwD) in RMW'.
  unfolder in *. type_solver.
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

Lemma jfi_in_sb WF : jfi ⊆ sb.
Proof. unfold ES.jfi. basic_solver. Qed.

(******************************************************************************)
(** ** co properties *)
(******************************************************************************)

Lemma co_codom_ninit WF : codom_rel co ⊆₁ Eninit.
Proof. 
  intros y [x CO].
  assert (E x) as Ex.
  { apply coE in CO; auto.
    generalize CO. basic_solver. }
  assert (E y) as Ey.
  { apply coE in CO; auto.
    generalize CO. basic_solver. }

  apply acts_set_split 
    in Ey.
  destruct Ey 
    as [INITy | nINITy]; auto.

  apply acts_set_split 
    in Ex.
  destruct Ex 
    as [INITx | nINITx]; auto.

  { exfalso. 
    assert (x = y) as EQ; subst.
    { eapply init_uniq; auto.
      eapply col; auto. }
    eapply co_irr; eauto. }

  exfalso. 
  eapply co_irr, co_trans; eauto.
  eapply co_init; auto.
  apply seq_eqv_lr. 
  unfold set_inter.
  splits; auto.
  { red; erewrite <- col; auto. }
  apply coD in CO; auto.
  generalize CO. basic_solver.
Qed.

Lemma coEninit WF : co ⨾ ⦗Eninit⦘ ≡ co.
Proof. 
  split; [basic_solver|].
  rewrite seq_eqv_r.
  unfolder; ins; desc.
  split; auto.
  eapply co_codom_ninit; auto.
  basic_solver.
Qed.

(******************************************************************************)
(** ** ew properties *)
(******************************************************************************)

Lemma ew_tid WF : ew ⊆ same_tid.
Proof. 
  rewrite ewc; auto.
  unfold ES.same_tid, ES.cf.
  basic_solver 10.
Qed.  

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

Lemma ewEninit WF : ew ⊆ (Eninit × Eninit)^?.
Proof. 
  rewrite ewc; auto.
  apply clos_refl_mori.
  rewrite cfEninit.
  basic_solver.
Qed.

(******************************************************************************)
(** ** ew/co properties *)
(******************************************************************************)

Lemma ew_co_eq_co WF : ew ⨾ co ≡ co.
Proof.
  split; [apply ew_co_in_co|]; auto.
  rewrite <- ew_refl; auto.
  rewrite coE, coD; auto.
  basic_solver.
Qed.

Lemma co_ew_eq_co WF : co ⨾ ew ≡ co.
Proof. 
  split; [apply co_ew_in_co|]; auto.
  rewrite <- ew_refl; auto.
  rewrite coE, coD; auto.
  basic_solver.
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

Lemma jf_tjf_in_top WF : jf ⨾ jf⁻¹ ⊆ ⦗⊤₁⦘.
Proof.
  arewrite (jf ≡ ((jf)⁻¹)⁻¹).
  rewrite <- functional_alt.
  apply WF.
Qed.

Lemma rf_trf_in_ew WF : rf ⨾ rf⁻¹ ⊆ ew. 
Proof. 
  unfold ES.rf.
  rewrite transp_minus, transp_seq.
  rewrite !inclusion_minus_rel.
  rewrite !seqA.
  sin_rewrite WF.(jf_tjf_in_top).
  rewrite transp_sym_equiv.
  { rewrite seq_id_l. 
    rewrite transitiveI.
    apply WF. }
  apply WF.
Qed.

Lemma rfi_in_rf : rfi ⊆ rf. 
Proof. unfold ES.rfi. basic_solver. Qed.

Lemma rfe_in_rf : rfe ⊆ rf. 
Proof. unfold ES.rfe. basic_solver. Qed.

Lemma rfe_in_ew_jfe WF : rfe ⊆ ew ⨾ jfe. 
Proof. 
  unfold ES.rfe, ES.rf, ES.jfe.
  intros x y [[[z [EW JF]] nCF] nSB].
  unfolder; eexists; splits; eauto.
  intros SB.
  apply ewc in EW; auto.
  destruct EW as [EQ | CF].
  { subst; auto. }
  apply nCF.
  eapply cf_sb_in_cf; auto.
  basic_solver. 
Qed.

Lemma ncf_rff X WF
      (NCF : cf_free S X) :
  functional ((restr_rel X rf)⁻¹).
Proof.
  intros y x z rf_xy rf_zy. 
  destruct rf_xy as [rf_xy [Xy Xx]].
  destruct rf_zy as [rf_zy [Xz _]].
  assert (EW : ew x z).
  { apply rf_trf_in_ew; basic_solver. }
  apply ewc in EW; auto.
  destruct EW; auto.
  unfold cf_free in NCF. unfolder in NCF.
  exfalso. eapply NCF. eauto.
Qed.
  

Lemma jf_prcl_rf_compl {A} WF
      (AE : A ⊆₁ E)
      (JF_PRCL : prcl jf A):
  A ∩₁ R ⊆₁ codom_rel (⦗A⦘ ⨾ rf).
Proof.
  arewrite (A ∩₁ R ≡₁ A ∩₁ (E ∩₁ R)) by basic_solver.
  rewrite WF.(jf_complete).
  rewrite set_interC, <- codom_eqv1.
  rewrite (dom_rel_helper JF_PRCL).
  rewrite jf_in_rf; auto.
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

Lemma fr_alt WF : fr ≡ jf⁻¹ ⨾ co.
Proof. 
  unfold ES.fr. split.
  2 : by rewrite jf_in_rf. 
  unfold ES.rf.
  rewrite inclusion_minus_rel.
  rewrite transp_seq.
  rewrite transp_sym_equiv
    with (r := ew).
  2 : apply WF.
  rewrite seqA.
  by rewrite ew_co_in_co. 
Qed.

(******************************************************************************)
(** ** rf/fr/co properties *)
(******************************************************************************)

Lemma rffr_in_co WF : rf ⨾ fr ⊆ co.
Proof.
  intros x y [z [HH [z' [AA BB]]]].
  apply ew_co_in_co; auto.
  eexists; split; eauto.
  eapply rf_trf_in_ew; eauto.
  basic_solver.
Qed.

Lemma frco_in_fr WF : fr ⨾ co ⊆ fr.
Proof.
  intros x y [z [[p [AA BB]] HH]].
  red. eexists. splits; eauto.
  eapply WF.(co_trans); eauto.
Qed.

Lemma co_rf_alt WF : co ⨾ rf ≡ co ⨾ jf.
Proof. 
  unfold ES.rf. 
  unfolder; split; ins; desf.
  { eexists; splits; [|eauto].
    eapply co_ew_in_co; eauto.
    basic_solver. }
  eexists; splits; eauto.
  { eexists; splits; eauto.
    eapply ew_refl; auto.
    unfolder; splits; auto.
    { apply coE in H; auto. 
      generalize H. basic_solver. }
    apply coD in H; auto. 
    generalize H. basic_solver. }
  intros CF.
  eapply jf_ncf; eauto.
  basic_solver.
Qed.

(******************************************************************************)
(** ** co properites *)
(******************************************************************************)



(******************************************************************************)
(** ** sc properites *)
(******************************************************************************)

Lemma sc_in_rel :
  Sc ⊆₁ Rel.
Proof.
  unfold is_sc, is_rel.
  basic_solver.
Qed.

Lemma sc_in_acq :
  Sc ⊆₁ Acq.
Proof.
  unfold is_sc, is_acq.
  basic_solver.
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

(******************************************************************************)
(** ** cont_sb properites *)
(******************************************************************************)

Lemma exists_cont_sb_dom WF k : 
  exists e, cont_sb_dom S k e. 
Proof. 
  unfold cont_sb_dom.
  destruct k.
  { apply exists_acts_init; eauto. }
  exists eid. basic_solver 10.
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

Lemma cont_sb_cf_free k lang st WF 
      (KK : K (k, existT _ lang st)) : 
  cf_free S (cont_sb_dom S k).
Proof. 
  red. 
  unfold cont_sb_dom.
  destruct k.
  { eapply ncfEinit. }
  rewrite crE. relsf.
  rewrite id_union. relsf.
  rewrite seq_eqv_r with (r := sb).
  rewrite !seq_eqv_lr.
  unfold dom_rel.
  unionL.
  { intros x y HH. desf.
    eapply cf_irr; eauto. }
  { intros x y HH. desf.
    eapply n_sb_cf; eauto. }
  { intros x y HH. desf.
    eapply n_sb_cf; splits; eauto. 
    by apply cf_sym. }
  intros x y HH. desf.
  eapply sb_dom_cf_free; auto.
  apply seq_eqv_lr.
  splits; eauto; basic_solver 10.
Qed.

Lemma cont_sb_dom_cf k lang st WF 
      (KK : K (k, existT _ lang st)) :  
  dom_rel (cf ⨾ ⦗cont_sb_dom S k⦘) ⊆₁ set_compl (cont_sb_dom S k).
Proof. 
  intros x [y CF] kSBx.
  destruct_seq_r CF as kSBy.
  eapply cont_sb_cf_free; eauto.
  basic_solver. 
Qed.

Lemma cont_sb_dom_icf k lang st WF 
      (KK : K (k, existT _ lang st)) :  
  dom_rel (icf ⨾ ⦗cont_sb_dom S k⦘) ⊆₁ set_compl (cont_sb_dom S k).
Proof. 
  intros x [y ICF] kSBx.
  destruct_seq_r ICF as kSBy.
  destruct ICF as [CF _].
  eapply cont_sb_cf_free; eauto.
  basic_solver. 
Qed.

Lemma cont_sb_dom_cross k lang st WF 
      (KK : K (k, existT _ lang st)) :  
  cont_sb_dom S k × cont_sb_dom S k ⊆ Einit × Einit ∪ sb⁼.
Proof.
  unfold cont_sb_dom.
  destruct k as [|e]. 
  { basic_solver. }
  rewrite crE. relsf.
  rewrite seq_eqv_r.
  intros x y [[EQe | HA] [EQe' | HB]].
  { basic_solver. }
  { generalize HB. basic_solver. }
  { generalize HA. basic_solver. }
  destruct HA as [z  [SB  EQz ]].
  destruct HB as [z' [SB' EQz']].
  subst z z'.
  apply sb_Einit_Eninit in SB; auto.
  apply sb_Einit_Eninit in SB'; auto.
  destruct SB  as [[INITx _] | HA];
  destruct SB' as [[INITy _] | HB].
  { basic_solver. }
  { unfolder. right. right. left.
    apply sb_init; auto.
    generalize INITx, HB. basic_solver. }
  { unfolder. right. right. right.
    apply sb_init; auto.
    generalize INITy, HA. basic_solver. }
  assert (sb x e) as SB.
  { generalize HA. basic_solver. }
  assert (sb y e) as SB'.
  { generalize HB. basic_solver. }
  assert (same_tid x e) as STID.
  { eapply sb_tid; auto.
    generalize HA. basic_solver. }
  assert (same_tid y e) as STID'.
  { eapply sb_tid; auto.
    generalize HB. basic_solver. }
  right. 
  edestruct sb_prcl as [EQ | HH]; auto.
  { unfolder; splits; [apply SB |]; eauto. }
  { unfolder; splits; [apply SB'|]; eauto. }
  { basic_solver. }
  generalize HH. basic_solver.
Qed.  

(******************************************************************************)
(** ** cont_last properites *)
(******************************************************************************)

Lemma exists_cont_last WF k : 
  exists e, cont_last S k e. 
Proof. 
  unfold cont_last.
  destruct k.
  { eapply exists_acts_init; eauto. }
  exists eid; eauto.
Qed.

Lemma cont_last_in_cont_sb WF k : 
  cont_last S k ⊆₁ cont_sb_dom S k. 
Proof. 
  unfold cont_sb_dom, cont_last.
  destruct k as [|e]; auto.
  basic_solver.
Qed.

Lemma sb_cont_last_in_cont_sb_dom WF k : 
  dom_rel (sb ⨾ ⦗cont_last S k⦘) ⊆₁ cont_sb_dom S k. 
Proof. 
  unfold cont_sb_dom, cont_last.
  destruct k as [|e].
  { rewrite sb_ninit; auto. basic_solver. }
  basic_solver.
Qed.

Lemma cont_sb_dom_alt WF k : 
  cont_sb_dom S k ≡₁ dom_rel ((sb)^? ⨾ ⦗cont_last S k⦘). 
Proof. 
  split. 
  { unfold cont_sb_dom, cont_last.
    destruct k; basic_solver. }
  rewrite crE. relsf. split.
  { by apply cont_last_in_cont_sb. }
    by apply sb_cont_last_in_cont_sb_dom.
Qed.

Lemma cont_sb_dom_alt_imm WF lang k st e
      (KK : K (k, existT _ lang st))   
      (IMMSB : codom_rel (⦗cont_last S k⦘ ⨾ immediate sb) e) :
  cont_sb_dom S k ≡₁ dom_rel (sb ⨾ ⦗eq e⦘).
Proof.
  unfold cont_sb_dom, cont_last in *.
  assert (Eninit e) as nINITe.
  { apply sb_codom_ninit; auto.
    generalize IMMSB. basic_solver. }
  destruct IMMSB as [y HH].
  apply seq_eqv_l in HH.
  destruct HH as [kSBy IMMSB].
  destruct k eqn:Heq.
  { split.
    { rewrite sb_Einit_Eninit at 1; auto.
      basic_solver 10. }
    rewrite seq_eqv_r.
    intros z' [z'' [SB EQz'']]. subst z''.
    assert (E z') as Ez'.
    { apply sbE in SB; auto.
      generalize SB. basic_solver. }
    apply acts_set_split in Ez'.
    destruct Ez' as [INITz' | nINITz']; auto.
    exfalso. eapply IMMSB; eauto.
    apply sb_Einit_Eninit; auto.
    basic_solver. }
  subst eid. split.
  { unfolder. ins. desf.
    { eexists; splits; eauto.
      apply IMMSB. }
    exists e; split; eauto.
    eapply sb_trans; eauto.
    apply IMMSB. }
  assert (E y) as Ey.
  { eapply K_inEninit; eauto. } 
  assert (Eninit y) as nINITy.
  { eapply K_inEninit; eauto. }
  rewrite sb_imm_split_r at 1; auto.
  rewrite seqA.
  rewrite !seq_eqv_r.
  rewrite crE. relsf. split.
  { intros x [y' [IMMSB' EQy']]. subst y'.
    exists y; splits; auto.
    left. symmetry.
    eapply immediate_tsb_functional; auto.
    { apply immediate_transp with (r := sb).
      red. apply IMMSB. }
  by apply immediate_transp with (r := sb). }
  intros x [e' [y' [SB [IMMSB' EQy']]]]. subst e'.
  exists y; split; auto; right.
  arewrite (y = y'); auto.
  eapply immediate_tsb_functional; auto.
  { apply immediate_transp with (r := sb).
    red. apply IMMSB. }
  by apply immediate_transp with (r := sb).
Qed.

Lemma cont_last_alt WF k : 
  cont_last S k ≡₁ cont_sb_dom S k \₁ dom_rel (sb ⨾ ⦗cont_sb_dom S k⦘).
Proof. 
  unfold cont_sb_dom, cont_last.
  destruct k.
  { rewrite sb_ninit; auto. 
    rewrite dom_empty. 
    basic_solver. }
  rewrite crE, seq_union_l, seq_id_l. 
  rewrite dom_union, !dom_eqv.
  rewrite id_union, seq_union_r, dom_union.
  rewrite !set_minus_union_l, !set_minus_union_r.
  rewrite set_minusK. relsf. 
  split; [|basic_solver].
  rewrite seq_eqv_r. unfolder.
  intros x EQx. subst x.
  splits; auto.
  { intros HH. desf.
    eapply sb_irr; eauto. }
  intros HH. desf.
  eapply sb_irr; eauto.
  eapply sb_trans; eauto.
Qed.    

(******************************************************************************)
(** ** cont_cf properites *)
(******************************************************************************)

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
(** ** cont_adjacent properites *)
(******************************************************************************)

Lemma cont_adjacent_rmw WF k k' e e' 
      (ADJ : cont_adjacent S k k' e (Some e')) :
  rmw e e'.
Proof. 
  unfold cont_adjacent in ADJ; desc. 
  apply RMWe. basic_solver.
Qed.

Lemma cont_adjacent_ninit_e WF k k' e e' 
      (ADJ : cont_adjacent S k k' e e') :
  Eninit e.
Proof. by unfold cont_adjacent in ADJ; desc. Qed.

Lemma cont_adjacent_ninit_e' WF k k' e e' 
      (ADJ : cont_adjacent S k k' e (Some e')) :
  Eninit e'.
Proof. 
  pose proof (cont_adjacent_rmw WF ADJ) as RMW.
  apply rmwEninit in RMW; auto.
  generalize RMW. basic_solver. 
Qed.

Lemma cont_adjacent_tid_e WF k k' e e' 
      (ADJ : cont_adjacent S k k' e e') :
  tid e = ES.cont_thread S k.
Proof. 
  unfold cont_adjacent in ADJ; desc.
  rewrite kEQTID. subst k'.
  unfold ES.cont_thread, opt_ext in *.
  destruct e' as [e'|]; auto.
  apply rmwt; auto.
  apply RMWe. basic_solver. 
Qed.

Lemma cont_adjacent_tid_e' WF k k' e e' 
      (ADJ : cont_adjacent S k k' e (Some e')) :
  tid e' = ES.cont_thread S k.
Proof. 
  unfold cont_adjacent in ADJ; desc.
  rewrite kEQTID. subst k'.
  unfold ES.cont_thread, opt_ext in *; auto.
Qed.

Lemma cont_adjacent_cont_last_sb_imm WF k k' e e' 
      (ADJ : cont_adjacent S k k' e e') :
  codom_rel (⦗cont_last S k⦘ ⨾ immediate sb) e.
Proof. 
  edestruct exists_cont_last
    with (k := k) as [x kLAST]; eauto.
  exists x.
  apply seq_eqv_l.
  split; auto.
  cdes ADJ. split.
  { destruct kSBDOM as [kSBDOM _].
    eapply cont_last_in_cont_sb 
      in kLAST; auto.
    specialize (kSBDOM x kLAST).
    generalize kSBDOM. basic_solver. }
  intros y SB SB'.
  eapply cont_last_alt; eauto.
  exists y. 
  apply seq_eqv_r.
  split; auto.
  apply kSBDOM.
  basic_solver 10.
Qed.

Lemma cont_adjacent_con_last_sb_imm_alt WF x k k' e e' 
      (kLASTx : cont_last S k x)
      (ADJ : cont_adjacent S k k' e e') :
  immediate sb x e.
Proof. 
  assert (Eninit e) as nINITe.
  { eapply cont_adjacent_ninit_e; eauto. }
  edestruct cont_adjacent_cont_last_sb_imm
    as [y IMMSB]; eauto.
  destruct_seq_l IMMSB as kLASTy.
  unfold cont_last in *.
  destruct k; [|congruence].
  split.
  { apply sb_init; auto. basic_solver. }
  intros z SB SB'.
  eapply IMMSB; eauto.
  apply sb_init; auto. 
  split; auto.
  apply sb_codom_ninit; auto.
  basic_solver.
Qed.

Lemma cont_adjacent_sb_imm WF k k' e e' 
      (ADJ : cont_adjacent S k k' e e') :
  eq e × eq_opt e' ⊆ immediate sb.
Proof. 
  cdes ADJ.
  rewrite RMWe.
  by apply rmwi. 
Qed.

Lemma cont_adjacent_nsb_dom_e WF lang st k k' e e' 
      (KK : K (k, existT _ lang st))   
      (ADJ : cont_adjacent S k k' e e') :
  ~ cont_sb_dom S k e.
Proof. 
  intros kSBe.
  edestruct exists_cont_last 
    with (k := k) as [x kLAST]; auto.
  eapply cont_sb_dom_alt_imm 
    with (e := e) in kSBe; eauto.
  { destruct kSBe as [y SB].
    destruct_seq_r SB as EQe. 
    subst y.
    eapply sb_irr; eauto. }
  exists x. 
  apply seq_eqv_l; splits; auto. 
  eapply cont_adjacent_con_last_sb_imm_alt; eauto.
Qed.

Lemma cont_adjacent_nsb_dom_e' WF lang st k k' e e' 
      (KK : K (k, existT _ lang st))   
      (ADJ : cont_adjacent S k k' e (Some e')) :
  ~ cont_sb_dom S k e'.
Proof. 
  intros kSBe'.
  edestruct exists_cont_last 
    with (k := k) as [x kLAST]; auto.
  eapply cont_sb_dom_alt_imm 
    with (e := e) in kSBe'; eauto.
  { destruct kSBe' as [y SB].
    destruct_seq_r SB as EQe. 
    subst y.
    eapply sb_irr; eauto. 
    eapply sb_trans; eauto.
    eapply cont_adjacent_sb_imm; eauto.
    basic_solver. }
  exists x. 
  apply seq_eqv_l; splits; auto. 
  eapply cont_adjacent_con_last_sb_imm_alt; eauto.
Qed.  

Lemma cont_adjacent_sb_dom WF k k' e e'
      (ADJ : cont_adjacent S k k' e e') :
  ES.cont_sb_dom S k' ≡₁ ES.cont_sb_dom S k ∪₁ eq e ∪₁ eq_opt e'.
Proof. 
  red in ADJ. desc. subst k'.
  unfold ES.cont_sb_dom at 1.
  unfold opt_ext, eq_opt in *.
  destruct e' as [e'|].

  { assert (rmw e e') as RMW.
    { generalize RMWe. basic_solver. }
    rewrite crE. relsf.
    rewrite set_unionC.
    apply set_union_Propere; auto.
    arewrite (dom_rel (sb ⨾ ⦗eq e'⦘) ≡₁ 
                      dom_rel (sb^? ⨾ ⦗eq e⦘)).
    { split.
      { rewrite sb_imm_split_r at 1; auto. 
        rewrite !seqA, !seq_eqv_r.
        intros x [y [z [SB [IMMSB EQy]]]].
        subst y. exists z. 
        splits; auto.
        eapply immediate_tsb_functional; eauto.
        { apply immediate_transp with (r := sb). red.
          eapply rmwi; eauto. }
        apply immediate_transp with (r := sb). by red. }
      rewrite crE. relsf. 
      rewrite !seq_eqv_r. splits.
      { unfolder. ins. desf.
        eexists; splits; eauto.
        apply rmw_in_sb; auto. }
      unfolder. ins. desf.
      exists e'; splits; eauto.
      eapply sb_trans; eauto.
      apply rmw_in_sb; auto. }
    rewrite crE. relsf.
    rewrite set_unionC.
    apply set_union_Propere; auto.
      by rewrite kSBDOM. }

  rewrite crE. relsf.
  rewrite set_unionC.
  apply set_union_Propere; auto.
    by rewrite kSBDOM.
Qed.

Lemma cont_adjacent_sb_dom_mon WF k k' e e'
      (ADJ : cont_adjacent S k k' e e') :
  ES.cont_sb_dom S k ⊆₁ ES.cont_sb_dom S k'.
Proof. 
  erewrite cont_adjacent_sb_dom 
    with (k' := k'); eauto.
  basic_solver.
Qed.

Lemma cont_adjacent_inK' WF st k k' e e'
      (KK : K (k, st)) 
      (ADJ : cont_adjacent S k k' e e') :
  exists st', K (k', st').
Proof. 
  cdes ADJ.
  rewrite kREP'.
  eapply event_K; auto.
  { unfold opt_ext. 
    destruct e' as [e'|]; auto.
    apply rmw_codom_ninit; auto.
    eexists. apply RMWe.
    basic_solver. }
  unfold opt_ext, eq_opt in *.
  unfolder in RMWe.
  intros [x RMW].
  destruct e' as [e'|].
  { eapply rmw_codom_ndom with (x := e'); eauto.
    all: basic_solver. }
  apply nRMWde; auto. 
  basic_solver.
Qed.

(******************************************************************************)
(** ** cont_icf_dom properites *)
(******************************************************************************)

Lemma cont_icf_domE WF k : 
  cont_icf_dom S k ⊆₁ E. 
Proof.
  unfold cont_icf_dom.
  rewrite sbE; auto. 
  basic_solver.
Qed.

Lemma cont_icf_domEnint WF k : 
  cont_icf_dom S k ⊆₁ Eninit. 
Proof.
  unfold cont_icf_dom.
  rewrite sb_Einit_Eninit; auto.
  basic_solver.
Qed.

Lemma cont_icf_cont_cf WF k :
  cont_icf_dom S k ⊆₁ cont_cf_dom S k. 
Proof.
  rewrite <- set_interK 
    with (s := cont_icf_dom S k).
  rewrite cont_icf_domE at 1; auto.
  unfold cont_icf_dom, cont_cf_dom.
  destruct k; basic_solver.
Qed.

Lemma cont_sb_cont_icf_inter_false WF lang k st
      (KK : K (k, existT _ lang st)) :
  cont_sb_dom S k ∩₁ cont_icf_dom S k ⊆₁ ∅.
Proof. 
  rewrite cont_icf_cont_cf; auto.
  rewrite cont_sb_cont_cf_inter_false; eauto.
Qed.

Lemma cont_sb_dom_sb_cont_icf WF lang k st e
      (KK : K (k, existT _ lang st))   
      (kICFe : cont_icf_dom S k e) :
  cont_sb_dom S k ≡₁ dom_rel (sb ⨾ ⦗eq e⦘).
Proof.   
  unfold cont_icf_dom in kICFe.
  erewrite cont_sb_dom_alt_imm; eauto.
  generalize kICFe. basic_solver 10.
Qed.

Lemma cont_icf_dom_cont_adjacent WF lang k st e
      (KK : K (k, existT _ lang st)) 
      (kICFe : cont_icf_dom S k e) :
  exists k' e', cont_adjacent S k k' e e'.
Proof.
  destruct kICFe as [x HA].
  apply seq_eqv_lr in HA.
  destruct HA as [kSBLx [SBIMM TIDe]].
  assert (Eninit e) as nINITe.
  { eapply sb_codom_ninit; auto. 
    generalize SBIMM. basic_solver. }
  destruct 
    (classic (exists e', rmw e e'))
    as [[e' RMW] | nRMW].
  { edestruct event_K 
      with (e := e') 
      as [st' KK']; auto.
    { apply rmw_codom_ninit; auto.
      basic_solver. }
    { eapply rmw_codom_ndom; auto.
      basic_solver. }
    red in KK'.
    exists (CEvent e'), (Some e').
    constructor; splits; auto.
    { rewrite <- TIDe.
      unfold cont_thread.
      apply rmwt; auto. }
    { basic_solver. }
    { basic_solver. }
    eapply cont_sb_dom_alt_imm; eauto.
    basic_solver 10. }
  edestruct event_K 
    with (e := e) 
    as [st' KK']; auto.
  red in KK'.
  exists (CEvent e), None.
  constructor; splits; auto.
  { basic_solver. }
  eapply cont_sb_dom_alt_imm; eauto.
  basic_solver 10.
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
  generalize WF.(sb_ninit). basic_solver.
Qed.

Lemma seqn_immsb_init WF x y 
      (INITx : Einit x)
      (IMMSB : immediate sb x y) :
  seqn y = 0.
Proof. 
  unfold seqn.
  arewrite 
    (dom_rel (sb ∩ same_tid ⨾ ⦗eq y⦘) ≡₁ ∅).
  { split; try done.
    rewrite seq_eqv_r.
    intros z [z' [[SB STID] EQb]].
    subst z'. red.
    eapply IMMSB; eauto.
    apply sb_init; auto.
    split; auto.
    split.
    { apply sbE in SB; auto.
      generalize SB. basic_solver. }
    intros [_ TIDz].
    assert (Eninit y) as nINITy.
    { apply sb_codom_ninit; auto.
      eexists. apply IMMSB. }
    apply nINITy. 
    split; auto.
    { apply sbE in SB; auto.
      generalize SB. basic_solver. }
    congruence. }
  by rewrite countNatP_empty.
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
  unfolder in SB; desf.
  { assert (seqn x < seqn y) as HH; [|omega]. 
    eapply seqn_sb_alt; eauto. }
  assert (seqn y < seqn x) as HH; [|omega]. 
  eapply seqn_sb_alt; eauto.
Qed.

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
  intros SB. unfolder in SB. desf.
  { omega. }
  apply seqn_sb_alt in SB; auto.
  omega.
Qed.

Lemma seqn_eq_imm_sb WF x y z 
      (* (SB : sb x y) *)
      (Ey : E y)
      (nCF : ~ cf x y)
      (IMMSB : immediate sb x z)
      (EQtid : tid y = tid z)
      (EQseqn : seqn y = seqn z) :
  immediate sb x y. 
Proof.
  assert (E x) as Ex.
  { destruct IMMSB as [SB _].
    apply sbE in SB; auto.
    generalize SB. basic_solver. }
  assert (Eninit z) as nINITz.
  { apply sb_codom_ninit; auto.
    generalize IMMSB. basic_solver. }
  assert (E z) as Ez.
  { apply nINITz. }
  assert (Eninit y) as nINITy.
  { split; auto.
    intros [_ INITy].
    apply nINITz.
    split; auto; congruence. } 
  assert (sb x y) as SB.
  { apply acts_set_split in Ex.
    destruct Ex as [INITx | nINITx].
    { apply sb_init; auto. basic_solver. }
    assert (same_tid x y) as STID.
    { red. etransitivity.
      { apply sb_tid; auto.
        apply seq_eqv_l; split; auto.
        apply IMMSB. }
      congruence. }
    edestruct same_thread_alt
      with (x := x) (y := y) as [SB | CF]; eauto. 
    { apply nINITx. }
    { destruct SB as [EQ | [SB | SB]]; auto.
      { subst y. exfalso.
        assert (seqn x < seqn z) 
          as SEQLT; [|omega].
        apply seqn_sb_alt; auto.
        apply IMMSB. }
      red in SB. exfalso.
      assert (seqn y < seqn x) 
          as SEQLT.
      { apply seqn_sb_alt; auto. by symmetry. }
      assert (seqn x < seqn z) 
          as SEQLT'; [|omega].
      apply seqn_sb_alt; auto. 
      { unfold ES.same_tid in *. congruence. }
      apply IMMSB. }
    exfalso. auto. }

  split; auto.
  intros z' SB' SB''.
  assert (Eninit z') as nINITz'.
  { apply sb_codom_ninit; auto. basic_solver. }
  assert (seqn z' < seqn y) as SEQNLT.
  { apply seqn_sb_alt; auto. 
    apply sb_tid; auto. basic_solver. }
  apply acts_set_split in Ex.
  destruct Ex as [INITx | nINITx].
  { erewrite seqn_immsb_init 
      with (y := z) in EQseqn; eauto.
    omega. }
  assert (seqn x < seqn z') as SEQNLT'.
  { apply seqn_sb_alt; auto. 
    apply sb_tid; auto. basic_solver. }
  erewrite seqn_immsb 
    with (x := x) (y := z) in EQseqn; eauto; try omega.
  apply sb_tid; auto. 
  apply seq_eqv_l. 
  split; auto.
  apply IMMSB.
Qed.      

Lemma same_sb_dom_same_k k k' lst lst' WF
      (INK   : ES.cont_set S (k, lst))
      (INK'  : ES.cont_set S (k', lst'))
      (TEQ   : ES.cont_thread S k = ES.cont_thread S k')
      (SBDEQ : ES.cont_sb_dom S k ≡₁ ES.cont_sb_dom S k') :
  k = k'.
Proof.
  destruct k; simpls.
  all: destruct k'; simpls; desf.

  1,2: exfalso.
  1,2: eapply WF.(K_inEninit); eauto.
  1,2: apply SBDEQ; basic_solver 10.
  
  assert (dom_rel (sb^? ⨾ ⦗eq eid⦘) eid0) as AA.
  { apply SBDEQ. basic_solver 10. }
  assert (dom_rel (sb^? ⨾ ⦗eq eid0⦘) eid) as BB.
  { apply SBDEQ. basic_solver 10. }
  unfolder in AA. unfolder in BB. desf.
  exfalso.
  eapply WF.(sb_irr).
  eapply WF.(sb_trans); eauto.
Qed.

End EventStructure.
End ES.

