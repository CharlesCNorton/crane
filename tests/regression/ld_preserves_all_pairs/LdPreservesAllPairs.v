(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: LD does not disturb register pairs. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module LdPreservesAllPairs.

Record state : Type := mkState {
  regs : list nat;
  acc : nat
}.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.
Definition get_reg_pair (s : state) (r : nat) : nat :=
  let base := r - r mod 2 in
  get_reg s base * 16 + get_reg s (base + 1).

Definition execute_ld (s : state) (r : nat) : state :=
  mkState (regs s) (get_reg s r).

Definition sample : state := mkState [2; 9; 4; 7; 8; 1] 13.
Definition t : bool :=
  Nat.eqb (get_reg_pair (execute_ld sample 4) 2) (get_reg_pair sample 2).

End LdPreservesAllPairs.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "ld_preserves_all_pairs" LdPreservesAllPairs.
