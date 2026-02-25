(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Crane Require Extraction.
From Crane Require Export Mapping.Shared.

#[export] Set Crane StdLib "BDE".
(* If you have bde-format, you can uncomment the line below: *)
(* #[export] Set Crane Format Style "BDE". *)
#[export] Set Crane Format Style "LLVM".


Crane Extract Inductive option =>
  "bsl::optional<%t0>"
  [ "bsl::make_optional<%t0>(%a0)"
    "bsl::nullopt" ]
  "if (%scrut.has_value()) { %t0 %b0a0 = *%scrut; %br0 } else { %br1 }"
  From "bsl_optional.h" "bsl_memory.h".


Crane Extract Inductive prod =>
  "bsl::pair<%t0, %t1>"
  [ "bsl::make_pair(%a0, %a1)" ]
  "%t0 %b0a0 = %scrut.first; %t1 %b0a1 = %scrut.second; %br0"
  From "bsl_utility.h".
Crane Extract Inlined Constant fst => "%a0.first" From "bsl_utility.h".
Crane Extract Inlined Constant snd => "%a0.second" From "bsl_utility.h".


From Corelib Require Import PrimString.
Crane Extract Inlined Constant char63 => "char".
Crane Extract Inlined Constant string => "std::string" From "bsl_string.h".
Crane Extract Inlined Constant cat => "%a0 + %a1" From "bsl_string.h".
Crane Extract Inlined Constant get => "%a0[%a1]" From "bsl_string.h".
Crane Extract Inlined Constant sub => "%a0.substr(%a1, %a2)" From "bsl_string.h".
Crane Extract Inlined Constant length => "%a0.length()" From "bsl_string.h".


From Corelib Require Import PrimInt63.
Crane Extract Inlined Constant int => "int64_t" From "bsl_cstdint.h".
Crane Extract Inlined Constant add => "%a0 + %a1".
Crane Extract Inlined Constant sub => "%a0 - %a1".
Crane Extract Inlined Constant mul => "%a0 * %a1".
Crane Extract Inlined Constant mod => "%a0 % %a1".
Crane Extract Inlined Constant eqb => "%a0 == %a1".
Crane Extract Inlined Constant ltb => "%a0 < %a1".
Crane Extract Inlined Constant leb => "%a0 <= %a1".
