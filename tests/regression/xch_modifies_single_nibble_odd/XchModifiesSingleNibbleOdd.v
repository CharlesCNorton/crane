(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: XCH on an odd register changes only the low nibble of its pair. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module XchModifiesSingleNibbleOdd.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record state : Type := mkState {
  regs : list nat;
  acc : nat
}.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.
Definition nibble_of_nat (n : nat) : nat := n mod 16.
Definition get_reg_pair (s : state) (r : nat) : nat :=
  let base := r - r mod 2 in
  get_reg s base * 16 + get_reg s (base + 1).

Definition execute_xch (s : state) (r : nat) : state :=
  mkState (update_nth r (nibble_of_nat (acc s)) (regs s)) (get_reg s r).

Definition sample : state := mkState [2; 9; 4; 7; 8; 1] 13.
Definition t : bool :=
  Nat.eqb
    (get_reg_pair (execute_xch sample 3) 3)
    (get_reg sample 2 * 16 + nibble_of_nat (acc sample)).

End XchModifiesSingleNibbleOdd.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "xch_modifies_single_nibble_odd" XchModifiesSingleNibbleOdd.
