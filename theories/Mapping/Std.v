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


(* TODO: unsafe as extracting int63 to int64 *)
From Corelib Require Import PrimInt63.
Crane Extract Inlined Constant int => "int".
Crane Extract Inlined Constant add => "%a0 + %a1".
Crane Extract Inlined Constant sub => "%a0 - %a1".
Crane Extract Inlined Constant mul => "%a0 * %a1".
Crane Extract Inlined Constant mod => "%a0 % %a1".
Crane Extract Inlined Constant eqb => "%a0 == %a1".
Crane Extract Inlined Constant ltb => "%a0 < %a1".
Crane Extract Inlined Constant leb => "%a0 <= %a1".

(* From Corelib Require PrimArray.
Definition array (A : Type) {l : int} {def : A} := PrimArray.array A.
Definition make {A  : Type} (l : int) (def : A) : @array A l def := PrimArray.make l def.
Definition get {A  : Type} {l : int} {def : A} : @array A l def -> int -> A :=PrimArray.get.
Definition set {A  : Type} {l : int} {def : A} : @array A l def -> int -> A -> @array A l def := PrimArray.set.
Definition length {A  : Type} {l : int} {def : A} : @array A l def -> int := PrimArray.length.
(* Definition copy {A  : Type} {l : int} {def : A} : @array A l def -> @array A l def := PrimArray.copy. *)
Crane Extract Inlined Constant array => "std::array<%t0, %a0>" From "array".
Crane Extract Inlined Constant make =>
"[]() -> std::array<%t0, %a0> {
    std::array<%t0, %a0> _arr;
    _arr.fill(%a1);
    return _arr;
}()".
Crane Extract Inlined Constant get =>
"[]() -> %t0 {
    if(%a3 < %a0){
      return %a2[%a3];
    }
    else {
      return %a1;
    }
}()".
Crane Extract Inlined Constant set =>
"[]() -> std::array<%t0, %a0> {
    if(%a3 < %a0){
      %a2[%a3] = %a4;
      return %a2;
    }
    else {
      return %a2;
    }
}()".
Crane Extract Inlined Constant length => "%a2.size()". *)
