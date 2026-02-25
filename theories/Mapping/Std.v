(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Export Mapping.Shared.

#[export] Set Crane StdLib "std".
#[export] Set Crane Format Style "LLVM".


Crane Extract Inductive option =>
  "std::optional<%t0>"
  [ "std::make_optional<%t0>(%a0)"
    "std::nullopt" ]
  "if (%scrut.has_value()) { %t0 %b0a0 = *%scrut; %br0 } else { %br1 }"
  From "optional" "memory".


Crane Extract Inductive prod =>
  "std::pair<%t0, %t1>"
  [ "std::make_pair(%a0, %a1)" ]
  "%t0 %b0a0 = %scrut.first; %t1 %b0a1 = %scrut.second; %br0"
  From "utility".
Crane Extract Inlined Constant fst => "%a0.first" From "utility".
Crane Extract Inlined Constant snd => "%a0.second" From "utility".


From Corelib Require Import PrimString.
Crane Extract Inlined Constant char63 => "char".
Crane Extract Inlined Constant string => "std::string" From "string".
Crane Extract Inlined Constant cat => "%a0 + %a1" From "string".
Crane Extract Inlined Constant get => "%a0[%a1]" From "string".
Crane Extract Inlined Constant sub => "%a0.substr(%a1, %a2)" From "string".
Crane Extract Inlined Constant length => "%a0.length()" From "string".


(* int63 primitives — int64_t with 63-bit masking.
   All arithmetic results are masked to [0, 2^63) to match Rocq semantics.
   Bitwise ops preserve the invariant (inputs have bit 63 = 0).
   Shifts guard against UB when shift amount >= 63. *)
From Corelib Require Import PrimInt63.
Crane Extract Inlined Constant int => "int64_t" From "cstdint".
Crane Extract Inlined Constant add => "((%a0 + %a1) & 0x7FFFFFFFFFFFFFFFLL)".
Crane Extract Inlined Constant sub => "((%a0 - %a1) & 0x7FFFFFFFFFFFFFFFLL)".
Crane Extract Inlined Constant mul => "((%a0 * %a1) & 0x7FFFFFFFFFFFFFFFLL)".
Crane Extract Inlined Constant div => "(%a1 == 0 ? 0 : %a0 / %a1)".
Crane Extract Inlined Constant mod => "(%a1 == 0 ? 0 : %a0 % %a1)".
Crane Extract Inlined Constant eqb => "(%a0 == %a1)".
Crane Extract Inlined Constant ltb => "(%a0 < %a1)".
Crane Extract Inlined Constant leb => "(%a0 <= %a1)".
Crane Extract Inlined Constant land => "(%a0 & %a1)".
Crane Extract Inlined Constant lor => "(%a0 | %a1)".
Crane Extract Inlined Constant lxor => "(%a0 ^ %a1)".
Crane Extract Inlined Constant lsl => "(%a1 >= 63 ? 0 : ((%a0 << %a1) & 0x7FFFFFFFFFFFFFFFLL))".
Crane Extract Inlined Constant lsr => "(%a1 >= 63 ? 0 : (%a0 >> %a1))".

(* PrimArray extraction is in Mapping.PrimArrayStd (persistent_array<T>). *)
