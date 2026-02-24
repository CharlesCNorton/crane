(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Corelib Require Import PrimInt63.
From Crane Require Extraction.
From Crane Require Import Mapping.Std Mapping.NatIntStd.

#[export] Set Crane StdLib "std".
#[export] Set Crane Format Style "LLVM".

Inductive vec (A  : Type) : nat -> Type :=
  | nil : vec A 0
  | cons : forall (a:A) (n : nat), vec A n -> vec A (S n).

Local Notation "[ ]" := (nil _) (format "[ ]").
Local Notation "h :: t" := (cons _ h _ t) (at level 60, right associativity).

(* fix unfolding issue by making it one-constructor inductive type?
   (i.e. force explicit coercions) *)
Definition array (A : Type) (x : int) : Type := vec A (nat_of_int x).

Definition length {A : Type} {x : int} (v : array A x) : int := x.
Definition make {A : Type} (x : int) (a : A) : array A x :=
  (fix f n a := match n with
  | 0 => []
  | S n' => a :: (f n' a)
  end) (nat_of_int x) a.

Definition get_nth {A : Type} : forall {x : int} (v : array A x) (n : int), option A.
  Proof.
  unfold array. intros x.
  induction (nat_of_int x).
  + intros. exact None.
  + intros v. inversion v as [ | a n' v']; clear v. intros i.
  refine (if leb 0%int63 i then Some a else _).
  exact (IHn v' (sub i 1%int63)).
  Defined.

Definition set_nth {A : Type} : forall {x : int} (v : array A x) (n : int) (s : A), array A x.
  Proof.
  unfold array. intros x.
  induction (nat_of_int x).
  + intros; exact [].
  + intros v. inversion v as [ | a n' v']; clear v. intros i s.
  refine (if leb 0%int63 i then s :: v' else _).
  exact (a :: (IHn v' (sub i 1) s)).
  Defined.
Opaque array.

Crane Extract Inlined Constant array => "std::array<%t0, %a0>" From "array".
Crane Extract Inlined Constant length => "%a1.size()".
Crane Extract Inlined Constant make =>
"[]() -> std::array<%t0, %a0> {
    std::array<%t0, %a0> _arr;
    _arr.fill(%a1);
    return _arr;
}()".
Crane Extract Inlined Constant get_nth =>
"[]() -> std::optional<%t0> {
    if(%a2 < %a0) {
      return std::make_optional<%t0>(%a1[%a2]);
    } else {
      return std::nullopt;
    }
}()".
Crane Extract Inlined Constant set_nth =>
"[]()  -> std::array<%t0, %a0> {
    std::array<%t0, %a0> _arr = %a1;
    if(%a2 < %a0){
      _arr[%a2] = %a3;
    }
    return _arr;
}()".

(* Axiom array : Type -> int -> Type.
Axiom length : forall {A} {x}, array A x -> int.
Axiom make : forall {A} x, A -> array A x.
Axiom get_nth : forall {A} {x}, array A x -> int -> option A.
Axiom set_nth : forall {A} {x}, array A x -> int -> A -> array A x. *)

(*
Crane Extract Inductive vec =>
"std::array<%t0, static_cast<int>(%a0)>"
[ "{}"
"[]() -> std::array<%t0, %a1 + 1> {
  std::array<%t0, %a1 + 1> _arr;
  _arr[0] = %a0;
  std::copy(%a2.begin(), %a2.end(), _arr.begin() + 1);
  return _arr;
}" ]
"if (%scrut.empty()) {
  %br0
} else {
  %t0 %b1a0 = %scrut.front();
  unsigned int %b1a1 = %scrut.size() - 1;
  std::array<%t0, static_cast<int>(%b1a1)> %b1a2;
  std::copy(%scrut.begin() + 1, %scrut.end(), %b1a2.begin());
  %br1 }". *)






(* From Corelib Require Import PrimInt63.
From Corelib Require Export PrimArray.


Crane Extract Inlined Constant array => "auto".
Crane Extract Inlined Constant make =>
"[]() {
    %t0[%a0] _arr;
    for(int i = 0; i < %a0; i++) {
      _arr[i] = %a1;
    }
    return _arr;
}()".
Crane Extract Inlined Constant get => "%a0[%a1]". (* TODO: UNSAFE (missing default) *)
Crane Extract Inlined Constant set =>
"[]() {
    if(%a1 < sizeof(%a0)){
      %a0[%a1] = %a2;
    }
    return %a0;
}()".
Crane Extract Inlined Constant length => "sizeof(%a0)". *)




(* Axiom HACK : int -> Type.
Axiom hack : forall x, HACK x.
Definition array (A : Type) {l : int} {def : A} := prod (PrimArray.array A) (HACK l).
Definition make {A  : Type} (l : int) (def : A) : @array A l def := (PrimArray.make l def, hack l).
Definition get {A  : Type} {l : int} {def : A} : @array A l def -> int -> A := fun arr => PrimArray.get (fst arr).
Definition set {A  : Type} {l : int} {def : A} : @array A l def -> int -> A -> @array A l def := fun arr i a => (PrimArray.set (fst arr) i a, hack l).
Definition length {A  : Type} {l : int} {def : A} : @array A l def -> int := fun arr => PrimArray.length (fst arr).
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
    } else {
      return %a1;
    }
}()".
Crane Extract Inlined Constant set =>
"[]() -> std::array<%t0, %a0> {
    if(%a3 < %a0){
      %a2[%a3] = %a4;
    }
    return %a2;
}()".
Crane Extract Inlined Constant length => "%a2.size()". *)
