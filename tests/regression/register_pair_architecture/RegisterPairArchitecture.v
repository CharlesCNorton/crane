(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: each register index maps to one of the eight register pairs. *)

From Stdlib Require Import List Nat Bool Arith.PeanoNat.
Import ListNotations.

Module RegisterPairArchitecture.

Definition pair_index (r : nat) : nat := r / 2.

Definition pair_property (r : nat) : bool :=
  let p := pair_index r in
  andb (Nat.ltb p 8)
       (orb (Nat.eqb r (2 * p))
            (Nat.eqb r (2 * p + 1))).

Definition regs : list nat := seq 0 16.

Definition t : bool := forallb pair_property regs.

End RegisterPairArchitecture.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "register_pair_architecture" RegisterPairArchitecture.
