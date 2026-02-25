(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: PrimArray extraction via persistent_array<T>. *)

From Corelib Require Import PrimInt63.
From Crane Require Import Mapping.Std Mapping.NatIntStd Mapping.PrimArrayStd.
Require Crane.Extraction.

Module PrimArray.

(* --- Basic construction and access --- *)

(* A 5-element array of nats, default 0. *)
Definition arr5 : @parray nat 5%int63 0 := parray_make 5%int63 0.

(* Read element 0 from a freshly-made array — should be default (0). *)
Definition get_default : nat := parray_get arr5 0%int63.

(* Length of the array — should be 5. *)
Definition arr5_len : int := parray_length arr5.

(* --- Set and persistence --- *)

(* Set index 2 to 42. Returns a NEW array; arr5 is unchanged. *)
Definition arr5_modified : @parray nat 5%int63 0 :=
  parray_set arr5 2%int63 42.

(* Read back the set value from the new array. *)
Definition get_modified : nat := parray_get arr5_modified 2%int63.

(* Read same index from the ORIGINAL — must still be 0 (persistence). *)
Definition get_original : nat := parray_get arr5 2%int63.

(* --- Chained sets --- *)

(* Multiple sets building on each other. *)
Definition arr_chain : @parray nat 5%int63 0 :=
  parray_set (parray_set (parray_set arr5 0%int63 10) 1%int63 20) 2%int63 30.

Definition chain_0 : nat := parray_get arr_chain 0%int63.
Definition chain_1 : nat := parray_get arr_chain 1%int63.
Definition chain_2 : nat := parray_get arr_chain 2%int63.
Definition chain_3 : nat := parray_get arr_chain 3%int63. (* untouched — 0 *)

(* --- Copy --- *)

Definition arr_copy : @parray nat 5%int63 0 := parray_copy arr5_modified.
Definition copy_val : nat := parray_get arr_copy 2%int63. (* should be 42 *)

(* --- OOB access returns default --- *)

Definition oob_get : nat := parray_get arr5 99%int63.

End PrimArray.

Crane Extraction "prim_array" PrimArray.
