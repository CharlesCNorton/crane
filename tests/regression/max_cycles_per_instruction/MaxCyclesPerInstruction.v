(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: modeled instruction cycle counts never exceed 24. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module MaxCyclesPerInstruction.

Inductive instr : Type :=
| NOP
| ADD
| WRM
| FIM
| JMS
| JCNTaken
| JCNNotTaken
| ISZTaken
| ISZZero.

Definition cycles (i : instr) : nat :=
  match i with
  | NOP | ADD | WRM | JCNNotTaken | ISZZero => 8
  | FIM | JCNTaken | ISZTaken => 16
  | JMS => 24
  end.

Definition all_instrs : list instr :=
  [NOP; ADD; WRM; FIM; JMS; JCNTaken; JCNNotTaken; ISZTaken; ISZZero].

Definition t : bool := forallb (fun i => Nat.leb (cycles i) 24) all_instrs.

End MaxCyclesPerInstruction.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "max_cycles_per_instruction" MaxCyclesPerInstruction.
