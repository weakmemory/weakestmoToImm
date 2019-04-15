Require Import Omega Setoid Program.Basics.
From hahn Require Import Hahn.
From promising Require Import Basic.
From imm Require Import Events Prog ProgToExecution.
Require Import AuxDef.
Require Import AuxRel.
Require Import EventStructure.
Require Import LblStep.
Require Import ProgLoc.

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
  let loc_labs :=
      map (fun l => Astore Xpln Opln l 0) (prog_locs prog)
  in
  ES.init loc_labs (prog_init_K prog).