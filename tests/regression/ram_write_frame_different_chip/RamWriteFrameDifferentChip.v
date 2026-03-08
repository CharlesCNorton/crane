(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: writing one chip preserves reads from a different chip. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module RamWriteFrameDifferentChip.

Fixpoint update_nth {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: xs => x :: xs
  | S n', y :: ys => y :: update_nth n' x ys
  | _, [] => []
  end.

Definition reg := list nat.
Definition chip := list reg.
Definition bank := list chip.

Definition upd_main_in_reg (rg : reg) (i : nat) (v : nat) : reg :=
  update_nth i v rg.

Definition upd_reg_in_chip (ch : chip) (r : nat) (rg : reg) : chip :=
  update_nth r rg ch.

Definition upd_chip_in_bank (bk : bank) (c : nat) (ch : chip) : bank :=
  update_nth c ch bk.

Definition sample_bank : bank :=
  [
    [[1; 2; 3]; [4; 5; 6]];
    [[7; 8; 9]; [10; 11; 12]]
  ].

Definition updated_bank : bank :=
  let ch := nth 0 sample_bank [] in
  let rg := nth 1 ch [] in
  let rg' := upd_main_in_reg rg 2 99 in
  let ch' := upd_reg_in_chip ch 1 rg' in
  upd_chip_in_bank sample_bank 0 ch'.

Definition t : bool :=
  Nat.eqb (nth 2 (nth 0 (nth 1 updated_bank []) []) 0) 7.

End RamWriteFrameDifferentChip.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "ram_write_frame_different_chip" RamWriteFrameDifferentChip.
