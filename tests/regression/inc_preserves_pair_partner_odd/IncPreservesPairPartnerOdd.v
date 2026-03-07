(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: INC on an odd register leaves its pair partner unchanged. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module IncPreservesPairPartnerOdd.

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

Definition execute_inc (s : state) (r : nat) : state :=
  mkState (update_nth r (nibble_of_nat (get_reg s r + 1)) (regs s)) (acc s).

Definition sample : state := mkState [2; 9; 4; 7; 8; 1] 13.
Definition t : bool :=
  Nat.eqb (get_reg (execute_inc sample 3) 2) (get_reg sample 2).

End IncPreservesPairPartnerOdd.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "inc_preserves_pair_partner_odd" IncPreservesPairPartnerOdd.
