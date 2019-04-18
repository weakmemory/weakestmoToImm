Require Import Omega Setoid Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Prog Execution ProgToExecution.
Require Import AuxDef.
Require Import AuxRel.
Require Import EventStructure.
Require Import LblStep.
Require Import ProgLoc.
Require Import Consistency.

Set Implicit Arguments.

Definition thread_lts (t : thread_id) : Language.t :=
  @Language.mk
    (list Instr.t) state
    init
    is_terminal
    (ilbl_step t).

Definition prog_init_threads (prog : Prog.t) :
  IdentMap.t {lang : Language.t & Language.state lang} :=
  IdentMap.mapi
    (fun tid (linstr : list Instr.t) =>
       existT _ (thread_lts tid) (ProgToExecution.init linstr))
    prog.

Definition prog_init_K (prog : Prog.t) :=
  map
    (fun tidc =>
       (CInit (fst tidc), (snd tidc)))
    (RegMap.elements
       (prog_init_threads prog)).

Definition prog_es_init (prog : Prog.t) :=
  ES.init (prog_locs prog) (prog_init_K prog).

Definition prog_g_es_init (prog : Prog.t) (G : execution) :=
  let glocs :=
      flatten
        (map (fun e =>
                match e with
                | InitEvent l => [l]
                | _ => []
                end)
             (acts G))
  in
  ES.init glocs (prog_init_K prog).

Lemma prog_g_es_init_ninit G prog :
  ES.acts_ninit_set (prog_g_es_init prog G) ≡₁ ∅.
Proof.
  split; [|basic_solver].
  red. unfold prog_g_es_init, ES.init. intros x HH. 
  apply HH. red. split; auto.
  apply HH.
Qed.

Lemma prog_g_es_init_sb G prog :
  ES.sb (prog_g_es_init prog G) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfold prog_g_es_init, ES.init. simpls.
Qed.

Lemma prog_g_es_init_jf G prog :
  ES.jf (prog_g_es_init prog G) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfold prog_g_es_init, ES.init. simpls.
Qed.

Lemma prog_g_es_init_sw G prog :
  sw (prog_g_es_init prog G) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfold sw. rewrite prog_g_es_init_jf. basic_solver.
Qed.

Lemma prog_g_es_init_hb G prog :
  hb (prog_g_es_init prog G) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfold hb.
  rewrite prog_g_es_init_sw, prog_g_es_init_sb.
  rewrite ct_no_step; basic_solver.
Qed.

Lemma prog_g_es_init_cf G prog :
  ES.cf (prog_g_es_init prog G) ≡ ∅₂.
Proof.
  split; [|basic_solver].
  unfold ES.cf. rewrite prog_g_es_init_ninit. basic_solver.
Qed.

Hint Rewrite prog_g_es_init_ninit
     prog_g_es_init_sb
     prog_g_es_init_jf
     prog_g_es_init_sw
     prog_g_es_init_hb
     prog_g_es_init_cf
  : prog_es_init_db.

Lemma prog_g_es_init_consistent G prog :
  @es_consistent (prog_g_es_init prog G) Weakestmo.
Proof.
  constructor; unfold ecf, ES.jfe, icf.
  all: autorewrite with prog_es_init_db; auto.
  all: basic_solver.
Qed.

Lemma prog_g_es_init_wf G prog :
  ES.Wf (prog_g_es_init prog G).
Proof.
  constructor.
  all: autorewrite with prog_es_init_db; auto.
  all: simpls.
  all: try basic_solver.
Admitted.
