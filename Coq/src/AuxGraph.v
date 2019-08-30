Require Import Program.Basics.

From hahn Require Import Hahn.
From imm Require Import Events Prog Execution RC11.

Require Import AuxRel.

Set Implicit Arguments.

Section AuxGraph.

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
Notation "'GR_ex'" := (fun a => is_true (R_ex Glab a)).
Notation "'GW'" := (fun a => is_true (is_w Glab a)).
Notation "'GF'" := (fun a => is_true (is_f Glab a)).

Notation "'GRel'" := (fun a => is_true (is_rel Glab a)).
Notation "'GAcq'" := (fun a => is_true (is_acq Glab a)).

Notation "'Gsb'" := (Execution.sb G).
Notation "'Grmw'" := (Execution.rmw G).
Notation "'Grf'" := (Execution.rf G).
Notation "'Gfr'" := (Execution.fr G).
Notation "'Gco'" := (Execution.co G).
Notation "'Geco'" := (Execution_eco.eco G).

Notation "'Grs'" := (imm_s_hb.rs G).
Notation "'Grelease'" := (imm_s_hb.release G).
Notation "'Gsw'" := (imm_s_hb.sw G).
Notation "'Ghb'" := (imm_s_hb.hb G).

Notation "'Gpsc_f'" := (imm_s.psc_f G).
Notation "'Gscb'" :=  (imm_s.scb G).
Notation "'Gpsc_base'" := (imm_s.psc_base G).
Notation "'GSc'" := (fun a => is_true (is_sc Glab a)).

Lemma scbE
      (WF : Wf G) :
  Gscb ≡ ⦗GE⦘ ⨾ Gscb ⨾ ⦗GE⦘.
Proof.
  unfold imm_s.scb.
  rewrite wf_sbE, imm_s_hb.wf_hbE, wf_coE, wf_frE; auto.
  basic_solver 30.
Qed.

Lemma rsE_alt
      (WF_G : Wf G) :
  Grs ⨾ ⦗GE⦘ ≡ ⦗GW ∩₁ GE⦘ ⨾ (Gsb ∩ same_loc Glab)^? ⨾ ⦗GW ∩₁ GE⦘ ⨾ (Grf ⨾ Grmw)＊.
Proof.
  unfold imm_s_hb.rs.
  rewrite !seqA.
  arewrite ((Grf ⨾ Grmw)＊ ⨾ ⦗GE⦘ ≡ ⦗GE⦘ ⨾ (Grf ⨾ Grmw)＊).
  { rewrite rtE.
    rewrite !seq_union_l, !seq_union_r.
    apply union_more; [basic_solver|].
    rewrite (dom_l WF_G.(wf_rfE)), !seqA. 
    rewrite ct_seq_eqv_l at 1.
    rewrite (dom_r WF_G.(wf_rmwE)), <- !seqA. 
    rewrite ct_seq_eqv_r at 2.
      by rewrite seqA. }
  arewrite (⦗GW⦘ ⨾ ⦗GE⦘ ≡ ⦗GE⦘ ⨾ ⦗GW ∩₁ GE⦘).
  { basic_solver. }
  arewrite ((Gsb ∩ same_loc Glab)^? ⨾ ⦗GE⦘ ≡ ⦗GE⦘ ⨾ (Gsb ∩ same_loc Glab)^?). 
  { rewrite crE.
    rewrite !seq_union_l, !seq_union_r.
    apply union_more; [basic_solver|].
    rewrite wf_sbE.
    basic_solver. }
  rewrite <- seqA, <- id_inter. done.
Qed.


Lemma rsE_alt_swap
      (WF_G : Wf G) :
  Grs ⨾ ⦗GE⦘ ≡ ⦗GE⦘ ⨾ Grs.
Proof.
 rewrite WF_G.(imm_s_hb.wf_rsE).
 rewrite !seq_union_l, !seq_union_r.
 apply union_more; basic_solver.
Qed.

Lemma rsE_alt_restr
      (WF_G : Wf G) :
  Grs ⨾ ⦗GE⦘ ≡ restr_rel GE Grs.
Proof.
  rewrite restr_relE, <- seqA, <- rsE_alt_swap; auto.
  basic_solver.
Qed.

End AuxGraph.
