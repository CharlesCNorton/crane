(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: PrimArray — primitive persistent arrays. *)
(* STATUS: Entire PrimArray type crashes Crane with Translation.TODO. *)
(* The axioms array/make/get/set/length are all unrealized. *)

From Stdlib Require Import PArray PrimInt63 Nat Bool.

Module PrimArray.

Definition arr3 : array nat :=
  (make 3 0).[0 <- 1].[1 <- 2].[2 <- 3].

Definition get_first (a : array nat) : nat := a.[0].

Definition set_elem (a : array nat) (i : int) (v : nat) : array nat :=
  a.[i <- v].

Definition arr_length (a : array nat) : int := PArray.length a.

Definition test_arr3_first : nat := get_first arr3.
Definition test_arr3_len : int := arr_length arr3.
Definition test_set : nat := get_first (set_elem arr3 0 42).

End PrimArray.

(* Crane Extraction crashes with Translation.TODO on all PrimArray ops *)
(* Require Crane.Extraction. *)
(* From Crane Require Mapping.Std Mapping.NatIntStd. *)
(* Crane Extraction "prim_array" PrimArray. *)
