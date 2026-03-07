(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: an even register indexes the same pair as its successor. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module EvenRegSamePairAsSuccessor.

Record state : Type := mkState { regs : list nat }.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.

Definition get_reg_pair (s : state) (r : nat) : nat :=
  let base := r - r mod 2 in
  get_reg s base * 16 + get_reg s (base + 1).

Definition sample : state := mkState [0; 0; 10; 11; 0; 0].
Definition t : bool := Nat.eqb (get_reg_pair sample 2) (get_reg_pair sample 3).

End EvenRegSamePairAsSuccessor.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "even_reg_same_pair_as_successor" EvenRegSamePairAsSuccessor.
