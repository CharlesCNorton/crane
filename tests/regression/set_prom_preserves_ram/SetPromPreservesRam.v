(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: setting PROM parameters leaves RAM unchanged. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module SetPromPreservesRam.

Fixpoint nat_list_eqb (xs ys : list nat) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Nat.eqb x y && nat_list_eqb xs' ys'
  | _, _ => false
  end.

Record state : Type := mkState {
  regs : list nat;
  ram_sys : list nat;
  prom_addr : nat;
  prom_data : nat;
  prom_enable : bool
}.

Definition set_prom_params (s : state) (addr data : nat) (enable : bool) : state :=
  mkState (regs s) (ram_sys s) addr data enable.

Definition sample : state := mkState [1; 2; 3] [9; 8; 7] 0 0 false.
Definition t : bool :=
  nat_list_eqb (ram_sys (set_prom_params sample 12 99 true)) (ram_sys sample).

End SetPromPreservesRam.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "set_prom_preserves_ram" SetPromPreservesRam.
