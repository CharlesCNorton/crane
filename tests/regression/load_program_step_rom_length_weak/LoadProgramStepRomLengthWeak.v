(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: a single PROM programming step preserves ROM length. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module LoadProgramStepRomLengthWeak.

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

Definition set_prom_params (s : state) (addr data : nat) (enable : bool) : state :=
  mkState (rom s) addr data enable.

Definition execute_wpm (s : state) : state :=
  let new_rom := if prom_enable s
                 then update_nth (prom_addr s) (prom_data s) (rom s)
                 else rom s in
  mkState new_rom (prom_addr s) (prom_data s) (prom_enable s).

Definition sample : state := mkState [10; 11; 12; 13] 0 0 false.
Definition after : state := execute_wpm (set_prom_params sample 1 99 true).
Definition t : bool := Nat.eqb (length (rom after)) 4.

End LoadProgramStepRomLengthWeak.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "load_program_step_rom_length_weak" LoadProgramStepRomLengthWeak.
