(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: PrimFloat extraction — IEEE 754 binary64 arithmetic. *)

From Corelib Require Import PrimFloat PrimInt63.
From Crane Require Import Mapping.Std Mapping.PrimFloatStd.
Require Crane.Extraction.

Module PrimFloatTest.

(* --- Constants --- *)

Definition f_zero : pfloat := 0%float.
Definition f_one : pfloat := 1%float.
Definition f_neg_one : pfloat := pfloat_opp 1%float.

(* --- Arithmetic wrappers (prevent compile-time reduction) --- *)

Definition test_add (x y : pfloat) : pfloat := pfloat_add x y.
Definition test_sub (x y : pfloat) : pfloat := pfloat_sub x y.
Definition test_mul (x y : pfloat) : pfloat := pfloat_mul x y.
Definition test_div (x y : pfloat) : pfloat := pfloat_div x y.
Definition test_opp (x : pfloat) : pfloat := pfloat_opp x.
Definition test_abs (x : pfloat) : pfloat := pfloat_abs x.
Definition test_sqrt (x : pfloat) : pfloat := pfloat_sqrt x.

(* --- Comparison wrappers --- *)

Definition test_eqb (x y : pfloat) : bool := pfloat_eqb x y.
Definition test_ltb (x y : pfloat) : bool := pfloat_ltb x y.
Definition test_leb (x y : pfloat) : bool := pfloat_leb x y.

(* --- Conversion --- *)

Definition test_of_uint63 (n : int) : pfloat := pfloat_of_uint63 n.

End PrimFloatTest.

Crane Extraction "prim_float_test" PrimFloatTest.
