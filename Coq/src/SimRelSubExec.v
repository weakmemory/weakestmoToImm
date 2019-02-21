Require Import Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Execution TraversalConfig Traversal
     Prog ProgToExecution ProgToExecutionProperties imm_s imm_s_hb 
     CombRelations SimTraversal SimulationRel AuxRel.
Require Import AuxRel AuxDef EventStructure Consistency EventToAction LblStep 
         SimRelCont SimRelEventToAction. 

Set Implicit Arguments.
Local Open Scope program_scope.

Section SimRelSubExec. 
  Variable prog : Prog.t.
  Variable S : ES.t.
  Variable G : execution.
  Variable sc : relation actid.
  Variable TC : trav_config.

  Variable a2e : actid -> eventid.
  Variable a2eD : actid -> Prop.

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
  Notation "'Secf'" := (S.(Consistency.ecf)).

  Notation "'thread_syntax' tid"  := 
    (Language.syntax (thread_lts tid)) (at level 10, only parsing).  

  Notation "'thread_st' tid" := 
    (Language.state (thread_lts tid)) (at level 10, only parsing).

  Notation "'thread_init_st' tid" := 
    (Language.init (thread_lts tid)) (at level 10, only parsing).
  
  Notation "'thread_cont_st' tid" :=
    (fun st => existT _ (thread_lts tid) st) (at level 10, only parsing).

  Notation "'GE'" := G.(acts_set).
  Notation "'GEinit'" := (is_init ∩₁ GE).
  Notation "'GEninit'" := ((set_compl is_init) ∩₁ GE).

  Notation "'Gtid'" := (tid).
  Notation "'Glab'" := (G.(lab)).
  Notation "'Gloc'" := (loc G.(lab)).
  
  Notation "'GTid' t" := (fun x => tid x = t) (at level 1).
  Notation "'GNTid' t" := (fun x => tid x <> t) (at level 1).

  Notation "'GR'" := (fun a => is_true (is_r Glab a)).
  Notation "'GW'" := (fun a => is_true (is_w Glab a)).
  Notation "'GF'" := (fun a => is_true (is_f Glab a)).

  Notation "'GRel'" := (fun a => is_true (is_rel Glab a)).
  
  Notation "'Gsb'" := (G.(sb)).
  Notation "'Grmw'" := G.(rmw).
  Notation "'Grf'" := (G.(rf)).
  Notation "'Gco'" := (G.(co)).

  Notation "'Grs'" := (G.(imm_s_hb.rs)).
  Notation "'Grelease'" := (G.(imm_s_hb.release)).
  Notation "'Ghb'" := (G.(imm_s_hb.hb)).

  Notation "'C'"  := (covered TC).
  Notation "'I'"  := (issued TC).

  Notation "'Gvf'" := (furr G sc).

  Record simrel_subexec :=
    { exec_sb_prcl : dom_rel (Ssb ⨾ ⦗ a2e □₁ a2eD ⦘) ⊆₁ a2e □₁ a2eD;
      exec_ncf : ES.cf_free S (a2e □₁ a2eD);
      exec_rfc : (a2e □₁ a2eD) ∩₁ SR ⊆₁ codom_rel (⦗ a2e □₁ a2eD ⦘ ⨾ Srf);
    }.

  Section SimRelSubExecProps. 
    Variable GPROG : program_execution prog G.
    Variable PROG_NINIT : ~ (IdentMap.In tid_init prog).

    Variable WF : ES.Wf S.
    Variable TCCOH : tc_coherent G sc TC.
    Variable SRSE : simrel_subexec.

    Lemma SsbD_in_GsbD
          (SRE2A : simrel_e2a S G sc)
          (SRA2E : simrel_a2e S a2e a2eD) :
      Ssb ⨾ ⦗ a2e □₁ a2eD ⦘ ⊆ a2e □ (Gsb ⨾ ⦗ a2eD ⦘).
    Proof.
      erewrite dom_rel_helper with (r := Ssb ⨾ ⦗a2e □₁ a2eD⦘).
      2 : by apply exec_sb_prcl.
      rewrite <- restr_relE.
      rewrite <- collect_rel_fixset.
      2 : eapply fixset_swap; apply SRA2E.
      rewrite <- collect_rel_compose.
      apply collect_rel_mori; auto.
      rewrite restr_relE.
      rewrite <- seq_eqvK at 2.
      rewrite <- !seqA.
      rewrite seqA with (r1 := ⦗a2e □₁ a2eD⦘).
      rewrite collect_rel_seqi.
      rewrite <- restr_relE.
      rewrite inclusion_restr.
      rewrite set_collect_eqv, set_collect_compose.
      rewrite <- fixset_set_fixpoint.
      2 : eapply a2e_fix; apply SRA2E.
      apply seq_mori; [|done].
      eapply e2a_sb; eauto. apply SRE2A.
    Qed.

    Lemma SsbD_in_Gsb
          (SRE2A : simrel_e2a S G sc)
          (SRA2E : simrel_a2e S a2e a2eD) :
      Ssb ⨾ ⦗ a2e □₁ a2eD ⦘ ⊆ a2e □ Gsb.
    Proof.
      etransitivity.
      { by apply SsbD_in_GsbD. }
      basic_solver 10.
    Qed.

    Lemma sbC_dom
          (CinD : C ⊆₁ a2eD)
          (SRE2A : simrel_e2a S G sc)
          (SRA2E : simrel_a2e S a2e a2eD) :
      dom_rel (Ssb ⨾ ⦗ a2e □₁ C ⦘) ⊆₁ a2e □₁ C.
    Proof.
      rewrite <- seq_eqvK.
      sin_rewrite CinD.
      sin_rewrite SsbD_in_GsbD; auto.
      rewrite <- set_collect_eqv.
      rewrite <- collect_rel_seq.
      { rewrite seqA.
        arewrite (⦗a2eD⦘ ⨾ ⦗C⦘ ⊆ ⦗C⦘).
        rewrite sb_covered; eauto. basic_solver. }
      rewrite codom_seq, codom_eqv, dom_eqv.
      eapply inj_dom_mori; [| done |].
      { red. rewrite CinD. rewrite set_unionK. auto. }
      apply SRA2E.
    Qed.

    Lemma sb_nC_nC
          (CinD : C ⊆₁ a2eD)
          (SRE2A : simrel_e2a S G sc)
          (SRA2E : simrel_a2e S a2e a2eD) :
      codom_rel (⦗ set_compl (a2e □₁ C) ⦘ ⨾ Ssb) ⊆₁ set_compl (a2e □₁ C).
    Proof.
      intros x [y HH]. destruct_seq_l HH as DX.
      intros DY. apply DX.
      apply sbC_dom; auto. eexists. apply seq_eqv_r. eauto.
    Qed.

    

    

    (* Lemma exec_hbD *)
    (*       (CinD : C ⊆₁ a2eD)  *)
    (*       (SRE2A : simrel_e2a S G sc) *)
    (*       (SRA2E : simrel_a2e S a2e a2eD) :            *)
    (*   dom_rel (Shb ⨾ ⦗ a2e □₁ a2eD ⦘) ⊆₁ a2e □₁ a2eD.   *)
    (* Proof. *)
    (*   rewrite exec_hb_in_Chb_sb; auto. *)
    (*   rewrite seq_union_l, dom_union. unionL. *)
    (*   2: by eapply exec_sb_prcl; eauto. *)
    (*   rewrite CinD. basic_solver. *)
    (* Qed. *)

    (* Lemma exec_hb_release_ewD  *)
    (*       (CinD : C ⊆₁ a2eD)  *)
    (*       (SRE2A : simrel_e2a S G sc) *)
    (*       (SRA2E : simrel_a2e S a2e a2eD) : *)
    (*   dom_rel (Shb^? ⨾ Srelease ⨾ Sew^? ⨾ ⦗ a2e □₁ a2eD ⦘) ⊆₁ a2e □₁ a2eD.   *)
    (* Proof.  *)
    (*   rewrite crE with (r := Shb).  *)
    (*   relsf. split.  *)
    (*   { by apply exec_rel_ewD. } *)
    (*   intros x [y [z [HB REL]]]. *)
    (*   eapply exec_hbD; auto.  *)
    (*   eexists. apply seq_eqv_r. split; eauto. *)
    (*   apply exec_rel_ewD; auto. basic_solver. *)
    (* Qed. *)

    (* Lemma exec_necfD  *)
    (*       (CinD : C ⊆₁ a2eD)  *)
    (*       (SRE2A : simrel_e2a S G sc) *)
    (*       (SRA2E : simrel_a2e S a2e a2eD) :  *)
    (*   restr_rel (a2e □₁ a2eD) Secf ⊆ ∅₂. *)
    (* Proof.  *)
    (*   unfold restr_rel, ecf.  *)
    (*   intros a b [ECF [Hx Hy]]. *)
    (*   destruct ECF as [c [tHB [d [CF HB]]]]. *)
    (*   eapply exec_ncf; eauto.  *)
    (*   apply restr_relE. unfold restr_rel. *)
    (*   splits; eauto.  *)
    (*   { unfolder in tHB; desf.  *)
    (*     eapply exec_hbD; auto. basic_solver 10. } *)
    (*   unfolder in HB; desf.  *)
    (*   eapply exec_hbD; auto. basic_solver 10. *)
    (* Qed. *)

  End SimRelSubExecProps.

End SimRelSubExec.
