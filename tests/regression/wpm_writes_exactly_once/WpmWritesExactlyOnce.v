(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: enabled WPM updates one ROM index and preserves the others. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module WpmWritesExactlyOnce.

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
Definition after : state := execute_wpm sample.
Definition t : bool :=
  andb (Nat.eqb (nth 2 (rom after) 0) 99)
    (andb (Nat.eqb (nth 0 (rom after) 0) 10)
      (andb (Nat.eqb (nth 1 (rom after) 0) 11)
            (Nat.eqb (nth 3 (rom after) 0) 13))).

End WpmWritesExactlyOnce.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "wpm_writes_exactly_once" WpmWritesExactlyOnce.
