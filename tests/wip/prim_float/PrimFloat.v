(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Primitive floats (Float64). *)
(* NOTE: Float operations (add, mul, sub, div, eqb, ltb, leb) *)
(* all crash Crane with Translation.TODO — they are axioms *)
(* needing realization. Only constants extract. *)

From Stdlib Require Import PrimFloat.

Definition f_zero : float := 0%float.
Definition f_one : float := 1%float.
Definition f_pi : float := 3.14159%float.

Require Crane.Extraction.
From Crane Require Mapping.Std.
Crane Extraction "prim_float"
  f_zero f_one f_pi.
