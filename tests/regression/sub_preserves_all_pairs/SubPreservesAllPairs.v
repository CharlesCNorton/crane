(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: SUB does not disturb register pairs. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module SubPreservesAllPairs.

Record state : Type := mkState {
  regs : list nat;
  acc : nat
}.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.
Definition nibble_of_nat (n : nat) : nat := n mod 16.
Definition get_reg_pair (s : state) (r : nat) : nat :=
  let base := r - r mod 2 in
  get_reg s base * 16 + get_reg s (base + 1).

Definition execute_sub (s : state) (r : nat) : state :=
  mkState (regs s) (nibble_of_nat (acc s + 16 - get_reg s r)).

Definition sample : state := mkState [2; 9; 4; 7; 8; 1] 13.
Definition t : bool :=
  Nat.eqb (get_reg_pair (execute_sub sample 4) 2) (get_reg_pair sample 2).

End SubPreservesAllPairs.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "sub_preserves_all_pairs" SubPreservesAllPairs.
