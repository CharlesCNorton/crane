(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: writing RAM in the current bank preserves other banks. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module RamWriteMainPreservesOtherBank.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Record state : Type := mkState {
  ram_sys : list nat;
  cur_bank : nat
}.

Definition ram_write_main_sys (s : state) (v : nat) : list nat :=
  update_nth (cur_bank s) v (ram_sys s).

Definition execute_write (s : state) (v : nat) : state :=
  mkState (ram_write_main_sys s v) (cur_bank s).

Definition sample : state := mkState [10; 20; 30; 40] 1.
Definition t : bool := Nat.eqb (nth 3 (ram_sys (execute_write sample 99)) 0) 40.

End RamWriteMainPreservesOtherBank.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "ram_write_main_preserves_other_bank" RamWriteMainPreservesOtherBank.
