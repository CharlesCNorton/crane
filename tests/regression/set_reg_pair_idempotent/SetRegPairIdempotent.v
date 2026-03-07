(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: setting the same register pair twice keeps the final value. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module SetRegPairIdempotent.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record state : Type := mkState {
  regs : list nat
}.

Definition get_reg (s : state) (r : nat) : nat := nth r (regs s) 0.

Definition set_reg (s : state) (r v : nat) : state :=
  mkState (update_nth r (v mod 16) (regs s)).

Definition get_reg_pair (s : state) (r : nat) : nat :=
  let base := r - r mod 2 in
  get_reg s base * 16 + get_reg s (base + 1).

Definition set_reg_pair (s : state) (r v : nat) : state :=
  let base := r - r mod 2 in
  let hi := v / 16 in
  let lo := v mod 16 in
  let s1 := set_reg s base hi in
  set_reg s1 (base + 1) lo.

Definition sample : state := mkState [0; 0; 0; 0; 0; 0].
Definition t : bool :=
  Nat.eqb
    (get_reg_pair (set_reg_pair (set_reg_pair sample 2 34) 2 171) 2)
    171.

End SetRegPairIdempotent.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "set_reg_pair_idempotent" SetRegPairIdempotent.
