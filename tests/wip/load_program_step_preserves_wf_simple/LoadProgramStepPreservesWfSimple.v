(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: a single PROM programming step preserves basic state shape invariants. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module LoadProgramStepPreservesWfSimple.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record state : Type := mkState {
  regs_len : nat;
  rom : list nat;
  pc : nat;
  stack_len : nat;
  prom_addr : nat;
  prom_data : nat;
  prom_enable : bool
}.

Definition set_prom_params (s : state) (addr data : nat) (enable : bool) : state :=
  mkState (regs_len s) (rom s) (pc s) (stack_len s) addr data enable.

Definition execute_wpm (s : state) : state :=
  let new_rom := if prom_enable s
                 then update_nth (prom_addr s) (prom_data s) (rom s)
                 else rom s in
  mkState (regs_len s) new_rom (pc s) (stack_len s) (prom_addr s) (prom_data s) (prom_enable s).

Definition sample : state := mkState 4 [10; 11; 12; 13] 100 2 0 0 false.
Definition after : state := execute_wpm (set_prom_params sample 1 99 true).
Definition t : bool :=
  andb (Nat.eqb (regs_len after) 4)
    (andb (Nat.eqb (length (rom after)) 4)
      (andb (Nat.ltb (pc after) 4096)
            (Nat.leb (stack_len after) 3))).

End LoadProgramStepPreservesWfSimple.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "load_program_step_preserves_wf_simple" LoadProgramStepPreservesWfSimple.
