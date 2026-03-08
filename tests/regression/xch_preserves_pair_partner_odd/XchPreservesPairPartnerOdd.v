(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: XCH on an odd register leaves its pair partner unchanged. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module XchPreservesPairPartnerOdd.

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

Definition execute_xch (s : state) (r : nat) : state :=
  mkState (update_nth r (nibble_of_nat (acc s)) (regs s)) (get_reg s r).

Definition sample : state := mkState [2; 9; 4; 7; 8; 1] 13.
Definition t : bool :=
  Nat.eqb (get_reg (execute_xch sample 3) 2) (get_reg sample 2).

End XchPreservesPairPartnerOdd.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "xch_preserves_pair_partner_odd" XchPreservesPairPartnerOdd.
