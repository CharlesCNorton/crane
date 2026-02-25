(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* PrimFloatStd.v — Extraction mapping for Rocq's PrimFloat to C++ double.
 *
 * Rocq's PrimFloat is IEEE 754 binary64 (full 64-bit double precision).
 * C++ [double] has identical semantics on all mainstream platforms:
 *   - NaN != NaN (IEEE 754 standard, C++ == does this by default)
 *   - +0 == -0 (IEEE 754 standard)
 *   - Division by zero produces infinity, not UB (for floating-point)
 *   - Round-to-nearest, ties-to-even (C++ default rounding mode)
 *
 * We define wrapper functions with a [pfloat_] prefix to avoid name
 * collisions with PrimInt63's [eqb], [ltb], [leb], [sub], [add], [mul],
 * [div] which live in Mapping.Std.
 *
 * Argument indices: PrimFloat operations have no implicit type parameters
 * (unlike PrimArray), so indices start directly at %a0 = first explicit arg.
 *
 * Advanced operations (frshiftexp, ldshiftexp, normfr_mantissa, classify,
 * next_up, next_down) are deferred — they need more complex mappings
 * (e.g., pair returns, enum mappings for float_class).
 *)

From Crane Require Extraction.
From Crane Require Import Mapping.Std.
(* Import PrimFloat AFTER Mapping.Std so that [float], [add], [sub], etc.
 * resolve to PrimFloat operations rather than PrimInt63 operations. *)
From Corelib Require Import PrimFloat.

(* --- Wrapper definitions ---
 * Each wraps one PrimFloat primitive, giving it a unique name for extraction.
 * This avoids name collisions with PrimInt63's [eqb], [ltb], [leb], etc.
 * when both Mapping.Std and Mapping.PrimFloatStd are imported. *)

Definition pfloat := float.

(* Arithmetic *)
Definition pfloat_add (x y : float) : float := add x y.
Definition pfloat_sub (x y : float) : float := sub x y.
Definition pfloat_mul (x y : float) : float := mul x y.
Definition pfloat_div (x y : float) : float := div x y.
Definition pfloat_opp (x : float) : float := opp x.
Definition pfloat_abs (x : float) : float := abs x.
Definition pfloat_sqrt (x : float) : float := sqrt x.

(* Comparison *)
Definition pfloat_eqb (x y : float) : bool := eqb x y.
Definition pfloat_ltb (x y : float) : bool := ltb x y.
Definition pfloat_leb (x y : float) : bool := leb x y.

(* Conversion *)
Definition pfloat_of_uint63 (n : PrimInt63.int) : float := of_uint63 n.

(* --- Extraction directives --- *)

(* Map the primitive float type to C++ double.
 * [float] is the raw primitive type from PrimFloat.
 * [pfloat] is our wrapper alias — mapped separately in case downstream
 * code references it directly. *)
Crane Extract Inlined Constant float => "double".
Crane Extract Inlined Constant pfloat => "double".

(* Arithmetic: C++ double arithmetic matches IEEE 754 exactly. *)
Crane Extract Inlined Constant pfloat_add => "(%a0 + %a1)".
Crane Extract Inlined Constant pfloat_sub => "(%a0 - %a1)".
Crane Extract Inlined Constant pfloat_mul => "(%a0 * %a1)".
Crane Extract Inlined Constant pfloat_div => "(%a0 / %a1)".
Crane Extract Inlined Constant pfloat_opp => "(-%a0)".
Crane Extract Inlined Constant pfloat_abs => "std::abs(%a0)" From "cmath".
Crane Extract Inlined Constant pfloat_sqrt => "std::sqrt(%a0)" From "cmath".

(* Comparison: C++ IEEE 754 semantics match Rocq (NaN != NaN, +0 == -0). *)
Crane Extract Inlined Constant pfloat_eqb => "(%a0 == %a1)".
Crane Extract Inlined Constant pfloat_ltb => "(%a0 < %a1)".
Crane Extract Inlined Constant pfloat_leb => "(%a0 <= %a1)".

(* Conversion: int63 to double. *)
Crane Extract Inlined Constant pfloat_of_uint63 => "static_cast<double>(%a0)".
