From hahn Require Import Hahn.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecutionProperties imm_hb.
Require Import AuxRel AuxDef EventStructure Construction Consistency.
Require Import Coq.Logic.FunctionalExtensionality Classical_Prop.

Set Implicit Arguments.

Section SimRel.
  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G  : execution.
  Variable GPROG : program_execution prog G.
  Variable sc : relation actid.
  Variable TC : trav_config.
  Variable f  : actid -> eventid.

  Notation "'SE'" := S.(ES.acts_set).
  Notation "'GE'" := G.(acts_set).
  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gtid'" := (tid).
  Notation "'Gsb'" := (G.(sb)).
  Notation "'Ghb'" := (G.(imm_hb.hb)).
  Notation "'Grf'" := (G.(rf)).
  Notation "'Gco'" := (G.(co)).
  Notation "'Stid'" := (S.(ES.tid)).
  Notation "'Slab'" := (S.(ES.lab)).
  Notation "'Ssb'" := (S.(ES.sb)).
  Notation "'Srf'" := (S.(ES.rf)).
  Notation "'Sco'" := (S.(ES.co)).
  Notation "'Scf'" := (S.(ES.cf)).
  Notation "'Gtid_' t" := (fun x => tid x = t) (at level 1).
  Notation "'Stid_' t" := (fun x => Stid x = t) (at level 1).

  Notation "'GR'" := (fun a => is_true (is_r Glab a)).

  Definition pc thread :=
    f ∘₁ C ∩₁ Stid_ thread \₁ dom_rel (Ssb ⨾ ⦗ f ∘₁ C ⦘).

  

  Record simrel_common (P : thread_id -> Prop) :=
    { gwf   : Execution.Wf G;
      gprclos : forall thread m n (LT : m < n)
                       (EE : GE (ThreadEvent thread n)),
          GE (ThreadEvent thread m);
      tccoh : tc_coherent G sc TC;
      swf   : ES.Wf S;
      scons : @es_consistent S Weakestmo;

      (*fdef  : forall e (COV : C e),
        f e = act_to_event G e; *)
      finj : inj_dom (C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘)) f;  
      fimg : f ∘₁ (C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘)) ⊆₁ SE;
      foth : (f ∘₁ set_compl (C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘))) ∩₁ SE ≡₁ ∅;
      flab : forall e (CI : (C ∪₁ I) e),
          Slab e.(f) = Glab e;
      ftid : forall e, Stid (f e) = Gtid e;
      finitIncl : S.(ES.acts_init_set) ⊆₁ f ∘₁ (is_init ∩₁ GE);

      sbtot_cov : forall thread,
          is_total (f ∘₁ C ∩₁ Stid_ thread) Ssb;

      sbtot_ci : forall thread (NP : ~ P thread),
          is_total (f ∘₁ (C ∪₁ I) ∩₁ Stid_ thread) Ssb;

      sbPrcl : Ssb ⨾ ⦗ f ∘₁ C ⦘ ⊆ ⦗ f ∘₁ C ⦘ ⨾ Ssb;
      sbF : f ∘ ⦗ C ⦘ ⨾ Gsb ⨾ ⦗ C ⦘ ≡
            ⦗ f ∘₁ C ⦘ ⨾ Ssb ⨾ ⦗ f ∘₁ C ⦘;
      cimgNcf : ⦗ f ∘₁ C ⦘ ⨾ Scf ⨾ ⦗ f ∘₁ C ⦘ ≡ ∅₂;
      imgrf : f ∘ ⦗ I ⦘ ⨾ Grf ⨾ ⦗ C ⦘ ≡
              ⦗ f ∘₁ I ⦘ ⨾ Srf  ⨾ ⦗ f ∘₁ C ⦘;
      imgco : f ∘ ⦗ I ⦘ ⨾ Gco ⨾ ⦗ I ⦘ ⊆
              ⦗ f ∘₁ I ⦘ ⨾ Sco  ⨾ ⦗ f ∘₁ I ⦘;
      
      (* Highly likely, we need that *)
      (* or it should be deducable from SimRelAlt and (WF S) *)
      (* ⦗ f ∘₁ I ⦘ ⨾ Sew ⨾ ⦗ f ∘₁ I ⦘ ⊆ f ∘ ⦗ I ⦘ *)
    }.

  Record simrel :=
    { comm : simrel_common ∅;
      vis  : f ∘₁ (C ∪₁ dom_rel (Gsb^? ⨾ ⦗ I ⦘)) ⊆₁ vis S;
    }.
  
  Record forward_pair (e : actid) (e' : eventid) :=
    { fp_tcstep : trav_step G sc TC (mkTC (C ∪₁ eq e) I);
      fp_inGE   : GE e;
      fp_inSE   : SE e'; 
      fp_tidEq  : Stid e' = Gtid e;
      fp_labEq  : Slab e' = Glab e;
      fp_covsb  : Ssb ⨾ ⦗ eq e' ⦘ ⊆ ⦗ f ∘₁ C ⦘ ⨾ Ssb;
      fp_sbEq   : upd f e e' ∘ (Gsb ⨾ ⦗ eq e ⦘) ≡ Ssb ⨾ ⦗ eq e' ⦘;
      fp_imgrf  : upd f e e' ∘ (Grf ⨾ ⦗ eq e ⦘) ⊆ Srf;
    }.

  Section Properties.
    Variable P : thread_id -> Prop.
    Variable SRC : simrel_common P.

    Lemma finE e (SEE : SE (f e)) : GE e.
    Proof.
      destruct (classic (GE e)) as [|NGE]; auto.
      exfalso.
      eapply foth; eauto.
      split; eauto.
      autounfold with unfolderDb.
      eexists. split; eauto.
      intros [AA|AA]; apply NGE.
      2: eapply issuedE; eauto.
      eapply coveredE; eauto.
      all: apply SRC.
    Qed.
  End Properties.

  (* Section SRCprop. *)
  (*   Variable P : thread_id -> Prop. *)
  (*   Variable SRC : simrel P. *)
    
  (*   Lemma finit : S.(ES.acts_init_set) ≡₁ f ∘₁ (is_init ∩₁ GE). *)
  (*   Proof. *)
  (*     set (SRC' := SRC). *)
  (*     destruct SRC'. *)
  (*     split; [eapply finitIncl; eauto|]. *)
  (*     unfold ES.acts_init_set. *)
  (*     apply set_subset_inter_r; split. *)
  (*     { rewrite init_covered; eauto. *)
  (*         by arewrite (C ⊆₁ C ∪₁ I). } *)
  (*     unfold is_init. *)
  (*     intros x [y [[AA CC] BB]]; desf. *)
  (*     rewrite SRC.(fdef). *)
  (*     2: { eapply init_covered; eauto. by split. } *)
  (*     simpls. *)
  (*     constructor; auto. *)
  (*     eexists. simpls. *)
  (*     rewrite wf_init_lab; auto. *)
  (*   Qed. *)

  (*   Lemma finitC : S.(ES.acts_init_set) ⊆₁ f ∘₁ C. *)
  (*   Proof. rewrite finit. erewrite init_covered; eauto. apply SRC. Qed. *)

  (*   Lemma sbPrcl : Ssb ⨾ ⦗ f ∘₁ C ⦘ ⊆ ⦗ f ∘₁ C ⦘ ⨾ Ssb. *)
  (*   Proof. *)
  (*     arewrite (Ssb ⊆ ⦗ f ∘₁ C ∪₁ set_compl (f ∘₁ C) ⦘ ⨾ Ssb) at 1. *)
  (*     { arewrite (f ∘₁ C ∪₁ set_compl (f ∘₁ C) ≡₁ fun _ => True). *)
  (*       2: by relsf. *)
  (*       split; [basic_solver|]. *)
  (*       intros x _. apply classic. } *)
  (*     rewrite id_union. rewrite seq_union_l. *)
  (*     arewrite_false (⦗set_compl (f ∘₁ C)⦘ ⨾ Ssb ⨾ ⦗f ∘₁ C⦘). *)
  (*     2: { arewrite_id ⦗f ∘₁ C⦘ at 2. relsf. } *)
  (*     unfold ES.sb. *)
  (*     rewrite seq_union_l. rewrite seq_union_r. *)
  (*     rewrite seq_eqv_cross. *)
  (*     rewrite finitC. *)
  (*     rewrite set_compl_inter_id. *)
  (*     rewrite cross_false_l. *)
  (*     apply inclusion_union_l; [done|]. *)
  (*     red. intros x y HH. *)
  (*     destruct_seq HH as [XX YY]. *)
  (*     destruct YY as [z [COVZ ZZ]]; subst. *)
  (*     erewrite fdef in *; eauto. *)
  (*     apply XX. *)
  (*     apply seq_eqv_r in HH. destruct HH as [HH SEE]. *)
  (*     assert (dom_rel (EventId.ext_sb ⨾ ⦗eq (act_to_event G z)⦘) x) as AA. *)
  (*     { eexists. apply seq_eqv_r. eauto. } *)
  (*     apply act_to_event_ext_sb_dom in AA. *)
  (*     desf. desf. *)
  (*     assert (C (ThreadEvent thread m)) as MM. *)
  (*     2: { red. eexists. by split; [|eapply fdef; eauto]. } *)
  (*     destruct SRC. *)
  (*     eapply dom_sb_covered; eauto. *)
  (*     eexists. apply seq_eqv_r. split; eauto. *)
  (*     assert (GE (ThreadEvent thread index)) as EE. *)
  (*     { eapply coveredE; eauto. } *)
  (*     red. apply seq_eqv_l. split. *)
  (*     { eapply SRC.(gprclos); eauto. } *)
  (*     apply seq_eqv_r. splits; auto. *)
  (*     red. by splits. *)
  (*   Qed. *)
  (* End SRCprop. *)
End SimRel.