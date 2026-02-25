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

(* PrimArray extraction is in Mapping.PrimArrayStd (persistent_array<T>). *)



