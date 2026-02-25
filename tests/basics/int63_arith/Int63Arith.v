(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimInt63.

Module Int63Arith.

(* Wrapper functions — these force runtime computation in C++.
   Without wrappers, Rocq reduces constant expressions at compile time
   and the extracted code would just contain literal values,
   bypassing the C++ arithmetic entirely. *)

Definition test_add (x y : int) : int := add x y.
Definition test_sub (x y : int) : int := sub x y.
Definition test_mul (x y : int) : int := mul x y.
Definition test_div (x y : int) : int := div x y.
Definition test_mod (x y : int) : int := mod x y.

Definition test_land (x y : int) : int := land x y.
Definition test_lor  (x y : int) : int := lor  x y.
Definition test_lxor (x y : int) : int := lxor x y.
Definition test_lsl  (x n : int) : int := lsl  x n.
Definition test_lsr  (x n : int) : int := lsr  x n.

Definition test_eqb (x y : int) : bool := eqb x y.
Definition test_ltb (x y : int) : bool := ltb x y.
Definition test_leb (x y : int) : bool := leb x y.

End Int63Arith.

Require Crane.Extraction.
Require Crane.Mapping.Std.

Crane Extraction "int63_arith" Int63Arith.
