(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: get_reg_pair reconstructs a byte from two adjacent registers. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module GetRegPairFromRegs.

Record state : Type := mkState { regs : list nat }.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.

Definition get_reg_pair (s : state) (r : nat) : nat :=
  let base := r - r mod 2 in
  get_reg s base * 16 + get_reg s (base + 1).

Definition sample : state := mkState [0; 0; 10; 11; 0; 0].
Definition t : bool := Nat.eqb (get_reg_pair sample 2) 171.

End GetRegPairFromRegs.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "get_reg_pair_from_regs" GetRegPairFromRegs.
