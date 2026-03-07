(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: WPM leaves registers unchanged when enabled. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module WpmEnabledPreservesRegs.

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
  regs : list nat;
  rom : list nat;
  prom_addr : nat;
  prom_data : nat;
  prom_enable : bool
}.

Definition execute_wpm (s : state) : state :=
  let new_rom := if prom_enable s
                 then update_nth (prom_addr s) (prom_data s) (rom s)
                 else rom s in
  mkState (regs s) new_rom (prom_addr s) (prom_data s) (prom_enable s).

Definition sample : state := mkState [1; 2; 3] [10; 11; 12] 1 99 true.
Definition t : bool :=
  nat_list_eqb (regs (execute_wpm sample)) (regs sample).

End WpmEnabledPreservesRegs.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "wpm_enabled_preserves_regs" WpmEnabledPreservesRegs.
