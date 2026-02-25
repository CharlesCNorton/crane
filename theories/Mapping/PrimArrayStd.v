(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* PrimArrayStd.v — Extraction mapping for Rocq's PrimArray to C++.
 *
 * Rocq's PrimArray is a persistent data structure: [set] returns a new array,
 * leaving the original unchanged. The C++ side uses [persistent_array<T>],
 * a copy-on-write template that preserves these semantics.
 *
 * We define wrapper functions with a [parray_] prefix to avoid name collisions
 * with PrimString's [get] and [length] (both live in Mapping.Std). Without
 * the prefix, [Crane Extract Inlined Constant get] would be ambiguous.
 *
 * Import strategy:
 *   - [From Corelib Require PrimArray] (no Export) so PrimArray names don't
 *     leak into downstream files and shadow PrimString operations.
 *   - [From Crane Require Import Mapping.Std] for int63 support (PrimArray
 *     indices are int63).
 *
 * Argument indices (verified empirically by inspecting extracted output):
 *   Crane preserves implicit [{l : int}] and [{def : A}] in the argument
 *   numbering even though they are "erased" (passed as literal values).
 *   This matches the HACK approach in ArrayStd.v:
 *
 *     %t0 = A (element type)
 *     %a0 = l   (implicit length — passed as literal, e.g. 5)
 *     %a1 = def (implicit default — passed as literal, e.g. 0)
 *     %a2 = arr (the array object)
 *     %a3 = i   (index, for get/set)
 *     %a4 = v   (value, for set)
 *
 *   parray_make only takes %a0 (length) and %a1 (default) as explicit args,
 *   so its numbering starts at %a0 without the arr/i/v slots.
 *)

From Corelib Require PrimArray.
From Corelib Require Import PrimInt63.
From Crane Require Extraction.
From Crane Require Import Mapping.Std.

(* --- Wrapper definitions ---
 * Each wraps one PrimArray primitive, giving it a unique name for extraction.
 * Type signatures preserve the implicit [l] and [def] so Crane sees them. *)

Definition parray (A : Type) {l : int} {def : A} := PrimArray.array A.

Definition parray_make {A : Type} (l : int) (def : A)
  : @parray A l def
  := PrimArray.make l def.

Definition parray_get {A : Type} {l : int} {def : A}
  (a : @parray A l def) (i : int) : A
  := PrimArray.get a i.

Definition parray_set {A : Type} {l : int} {def : A}
  (a : @parray A l def) (i : int) (v : A) : @parray A l def
  := PrimArray.set a i v.

Definition parray_length {A : Type} {l : int} {def : A}
  (a : @parray A l def) : int
  := PrimArray.length a.

Definition parray_copy {A : Type} {l : int} {def : A}
  (a : @parray A l def) : @parray A l def
  := PrimArray.copy a.

(* --- Extraction directives ---
 * Map each wrapper to the corresponding persistent_array<T> operation.
 *
 * [parray] is a type, so it uses %t0 (the element type A).
 * [parray_make] constructs: persistent_array<A>(length, default).
 * [parray_get/set/length/copy] are method calls on the array object.
 *
 * The [From "persistent_array.h"] clause tells Crane to #include the header
 * in generated code. Only needed on directives that introduce the type;
 * method calls don't need a separate include since the type already pulls it in. *)

Crane Extract Inlined Constant parray => "persistent_array<%t0>" From "persistent_array.h".

Crane Extract Inlined Constant parray_make =>
  "persistent_array<%t0>(%a0, %a1)" From "persistent_array.h".

Crane Extract Inlined Constant parray_get => "%a2.get(%a3)".

Crane Extract Inlined Constant parray_set => "%a2.set(%a3, %a4)".

Crane Extract Inlined Constant parray_length => "%a2.length()".

Crane Extract Inlined Constant parray_copy => "%a2.copy()".
