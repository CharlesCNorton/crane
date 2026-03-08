(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: setting PROM parameters preserves ROM length. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module SetPromPreservesRomLength.

Record state : Type := mkState {
  rom : list nat;
  prom_addr : nat;
  prom_data : nat;
  prom_enable : bool
}.

Definition set_prom_params (s : state) (addr data : nat) (enable : bool) : state :=
  mkState (rom s) addr data enable.

Definition sample : state := mkState [10; 11; 12; 13] 0 0 false.
Definition t : bool :=
  Nat.eqb
    (length (rom (set_prom_params sample 12 99 true)))
    (length (rom sample)).

End SetPromPreservesRomLength.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "set_prom_preserves_rom_length" SetPromPreservesRomLength.
