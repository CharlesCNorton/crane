(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: enabled WPM writes prom_data at prom_addr. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module WpmUpdatesRomAtAddr.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record state : Type := mkState {
  rom : list nat;
  prom_addr : nat;
  prom_data : nat;
  prom_enable : bool
}.

Definition execute_wpm (s : state) : state :=
  let new_rom := if prom_enable s
                 then update_nth (prom_addr s) (prom_data s) (rom s)
                 else rom s in
  mkState new_rom (prom_addr s) (prom_data s) (prom_enable s).

Definition sample : state := mkState [10; 11; 12; 13] 2 99 true.
Definition t : bool := Nat.eqb (nth 2 (rom (execute_wpm sample)) 0) 99.

End WpmUpdatesRomAtAddr.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "wpm_updates_rom_at_addr" WpmUpdatesRomAtAddr.
