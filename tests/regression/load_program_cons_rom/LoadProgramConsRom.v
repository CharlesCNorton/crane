(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: loading a non-empty program writes successive ROM bytes from the base address. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module LoadProgramConsRom.

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

Fixpoint load_program (s : state) (base : nat) (bytes : list nat) : state :=
  match bytes with
  | [] => s
  | b :: rest =>
      let s' := set_prom_params s base b true in
      let s'' := execute_wpm s' in
      load_program s'' (base + 1) rest
  end.

Definition sample : state := mkState [10; 11; 12; 13] 0 0 false.
Definition after : state := load_program sample 1 [99; 88].
Definition t : bool :=
  andb (Nat.eqb (nth 0 (rom after) 0) 10)
    (andb (Nat.eqb (nth 1 (rom after) 0) 99)
      (andb (Nat.eqb (nth 2 (rom after) 0) 88)
            (Nat.eqb (nth 3 (rom after) 0) 13))).

End LoadProgramConsRom.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "load_program_cons_rom" LoadProgramConsRom.
