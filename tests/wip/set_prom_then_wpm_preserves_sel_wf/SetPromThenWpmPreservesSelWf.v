(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: set_prom then WPM preserves RAM selector well-formedness. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module SetPromThenWpmPreservesSelWf.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record sel : Type := mkSel {
  sel_bank : nat;
  sel_chip : nat;
  sel_reg : nat
}.

Definition WF_sel (s : sel) : Prop :=
  sel_bank s < 4 /\ sel_chip s < 4 /\ sel_reg s < 4.

Record state : Type := mkState {
  sel_ram : sel;
  rom : list nat;
  prom_addr : nat;
  prom_data : nat;
  prom_enable : bool
}.

Definition set_prom_params (s : state) (addr data : nat) (enable : bool) : state :=
  mkState (sel_ram s) (rom s) addr data enable.

Definition execute_wpm (s : state) : state :=
  let new_rom := if prom_enable s
                 then update_nth (prom_addr s) (prom_data s) (rom s)
                 else rom s in
  mkState (sel_ram s) new_rom (prom_addr s) (prom_data s) (prom_enable s).

Definition sample : state := mkState (mkSel 1 2 3) [10; 11; 12] 0 0 false.
Definition t : Prop :=
  WF_sel (sel_ram (execute_wpm (set_prom_params sample 1 99 true))).

End SetPromThenWpmPreservesSelWf.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "set_prom_then_wpm_preserves_sel_wf" SetPromThenWpmPreservesSelWf.
