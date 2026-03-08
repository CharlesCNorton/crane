(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: the computed branch target stays on the page of PC+2. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

Module BranchTargetInPageProp.

Definition addr12_of_nat (n : nat) : nat := n mod 4096.

Definition page_of (p : nat) : nat :=
  addr12_of_nat p / 256.

Definition page_base (p : nat) : nat :=
  page_of p * 256.

Definition branch_target (pc off : nat) : nat :=
  page_base (addr12_of_nat (pc + 2)) + (off mod 256).

Definition p_small : nat := 777.
Definition p_same : nat := 600.
Definition p_cross_254 : nat := 254.
Definition p_cross_255 : nat := 255.
Definition t : Prop :=
  page_of (branch_target 513 42) = page_of (addr12_of_nat (513 + 2)).

End BranchTargetInPageProp.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "branch_target_in_page_prop" BranchTargetInPageProp.
