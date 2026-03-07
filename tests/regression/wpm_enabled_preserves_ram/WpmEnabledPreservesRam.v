(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: WPM leaves RAM unchanged when enabled. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module WpmEnabledPreservesRam.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Fixpoint nat_list_eqb (xs ys : list nat) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Nat.eqb x y && nat_list_eqb xs' ys'
  | _, _ => false
  end.

Record state : Type := mkState {
  ram_sys : list nat;
  rom : list nat;
  prom_addr : nat;
  prom_data : nat;
  prom_enable : bool
}.

Definition execute_wpm (s : state) : state :=
  let new_rom := if prom_enable s
                 then update_nth (prom_addr s) (prom_data s) (rom s)
                 else rom s in
  mkState (ram_sys s) new_rom (prom_addr s) (prom_data s) (prom_enable s).

Definition sample : state := mkState [5; 6; 7] [10; 11; 12] 1 99 true.
Definition t : bool :=
  nat_list_eqb (ram_sys (execute_wpm sample)) (ram_sys sample).

End WpmEnabledPreservesRam.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "wpm_enabled_preserves_ram" WpmEnabledPreservesRam.
