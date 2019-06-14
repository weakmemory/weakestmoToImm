Require Import Program.Basics.

From hahn Require Import Hahn.
From imm Require Import Events AuxRel Prog Execution.
Require Import AuxRel.
Require Import EventStructure.
Require Import Execution.
Require Import ProgES.
Require Import EventToAction.

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
  ⟪ GSB   : Gsb  ≡  e2a S □ (Ssb ∩ X × X) ⟫ /\
  ⟪ GRMW  : Grmw ≡  e2a S □ (Srmw ∩ X × X) ⟫ /\
  ⟪ GRF   : Grf  ≡  e2a S □ (Srf ∩ X × X) ⟫ /\
  ⟪ GCO   : Gco  ≡  e2a S □ (Sco ∩ X × X) ⟫.

End ExecutionToG.
