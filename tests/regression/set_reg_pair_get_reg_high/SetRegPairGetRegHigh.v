(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: setting a register pair exposes the high nibble through get_reg. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module SetRegPairGetRegHigh.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record state : Type := mkState { regs : list nat }.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.

Definition set_reg (s : state) (r v : nat) : state :=
  mkState (update_nth r (v mod 16) (regs s)).

Definition set_reg_pair (s : state) (r v : nat) : state :=
  let base := r - r mod 2 in
  let hi := v / 16 in
  let lo := v mod 16 in
  let s1 := set_reg s base hi in
  set_reg s1 (base + 1) lo.

Definition sample : state := mkState [0; 0; 0; 0; 0; 0].
Definition t : bool := Nat.eqb (get_reg (set_reg_pair sample 2 171) 2) 10.

End SetRegPairGetRegHigh.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "set_reg_pair_get_reg_high" SetRegPairGetRegHigh.
