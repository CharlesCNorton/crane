(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: set_prom then WPM preserves RAM invariants. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module SetPromThenWpmPreservesRamForall.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record state : Type := mkState {
  ram_sys : list nat;
  rom : list nat;
  prom_addr : nat;
  prom_data : nat;
  prom_enable : bool
}.

Definition set_prom_params (s : state) (addr data : nat) (enable : bool) : state :=
  mkState (ram_sys s) (rom s) addr data enable.

Definition execute_wpm (s : state) : state :=
  let new_rom := if prom_enable s
                 then update_nth (prom_addr s) (prom_data s) (rom s)
                 else rom s in
  mkState (ram_sys s) new_rom (prom_addr s) (prom_data s) (prom_enable s).

Definition sample : state := mkState [1; 2; 3] [10; 11; 12] 0 0 false.
Definition t : Prop :=
  Forall (fun x => x < 8)
         (ram_sys (execute_wpm (set_prom_params sample 1 99 true))).

End SetPromThenWpmPreservesRamForall.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "set_prom_then_wpm_preserves_ram_forall" SetPromThenWpmPreservesRamForall.
