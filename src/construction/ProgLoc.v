Require Import PArith.BinPos.
From hahn Require Import Hahn.
From imm Require Import Events Prog.
From PromisingLib Require Import Basic.

Set Implicit Arguments.

Definition lexpr_locs (le : Instr.lexpr) : list location :=
  match le with
  | Instr.lexpr_loc l => l :: nil
  | Instr.lexpr_choice _ l1 l2 => l1 :: l2 :: nil
  end.

Definition instr_locs (instr : Instr.t) : list location :=
  match instr with
  | Instr.load   _ _ le
  | Instr.store  _ le _
  | Instr.update _ _ _ _ _ le => lexpr_locs le

  | Instr.assign _ _ 
  | Instr.fence _
  | Instr.ifgoto _ _ => nil
  end.

Definition linstr_locs (linstr : list Instr.t) : list location :=
  flatten (map instr_locs linstr).

Definition prog_locs (prog : Prog.t) : list location :=
  nodup positive_eq_dec
        (flatten
           (map
              (fun tlist =>
                 linstr_locs (snd tlist))
              (IdentMap.Properties.to_list prog))).