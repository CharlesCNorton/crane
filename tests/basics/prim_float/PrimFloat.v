(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: PrimFloat extraction — IEEE 754 binary64 arithmetic. *)

From Corelib Require Import PrimFloat PrimInt63.
From Crane Require Import Mapping.Std.
Require Crane.Extraction.

Module PrimFloat.

(* --- Constants --- *)

Definition f_zero : float := 0%float.
Definition f_one : float := 1%float.
Definition f_neg_one : float := opp 1%float.

(* --- Arithmetic wrappers (prevent compile-time reduction) --- *)

Definition test_add (x y : float) : float := PrimFloat.add x y.
Definition test_sub (x y : float) : float := PrimFloat.sub x y.
Definition test_mul (x y : float) : float := PrimFloat.mul x y.
Definition test_div (x y : float) : float := PrimFloat.div x y.
Definition test_opp (x : float) : float := opp x.
Definition test_abs (x : float) : float := PrimFloat.abs x.
Definition test_sqrt (x : float) : float := sqrt x.

(* --- Comparison wrappers --- *)

Definition test_eqb (x y : float) : bool := PrimFloat.eqb x y.
Definition test_ltb (x y : float) : bool := PrimFloat.ltb x y.
Definition test_leb (x y : float) : bool := PrimFloat.leb x y.

(* --- Conversion --- *)

Definition test_of_uint63 (n : int) : float := of_uint63 n.

End PrimFloat.

Crane Extraction "prim_float" PrimFloat.
