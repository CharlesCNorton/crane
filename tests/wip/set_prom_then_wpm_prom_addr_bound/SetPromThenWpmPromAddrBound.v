(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: set_prom then WPM preserves programmed address bounds. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module SetPromThenWpmPromAddrBound.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record state : Type := mkState {
  regs : list nat;
  rom : list nat;
  acc : nat;
  pc : nat;
  stack : list nat;
  cur_bank : nat;
  rom_ports : list nat;
  sel_rom : nat;
  prom_addr : nat;
  prom_data : nat;
  prom_enable : bool
}.

Definition set_prom_params (s : state) (addr data : nat) (enable : bool) : state :=
  mkState (regs s) (rom s) (acc s) (pc s) (stack s) (cur_bank s)
          (rom_ports s) (sel_rom s) addr data enable.

Definition execute_wpm (s : state) : state :=
  let new_rom := if prom_enable s
                 then update_nth (prom_addr s) (prom_data s) (rom s)
                 else rom s in
  mkState (regs s) new_rom (acc s) (pc s) (stack s) (cur_bank s)
          (rom_ports s) (sel_rom s) (prom_addr s) (prom_data s) (prom_enable s).

Definition sample : state :=
  mkState [1; 2; 3; 4] [10; 11; 12; 13; 14; 15; 16; 17] 7 1025 [7; 9] 2 [3; 4; 5; 6] 5 0 0 false.

Definition after : state := execute_wpm (set_prom_params sample 2048 99 true).
Definition t : bool := Nat.ltb (prom_addr after) 4096.

End SetPromThenWpmPromAddrBound.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "set_prom_then_wpm_prom_addr_bound" SetPromThenWpmPromAddrBound.
