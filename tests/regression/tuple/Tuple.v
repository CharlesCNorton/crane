(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*
   This test exposes the TODO at translation.ml:1729
   MLtuple is not handled in gen_expr, which should raise a TODO exception
*)
Require Crane.Extraction.

Module Tuple.

(* Standard tuple type for testing *)
Definition pair (A B : Type) := (A * B)%type.

(* Function that returns a tuple - this might generate MLtuple *)
Definition make_pair {A B : Type} (a : A) (b : B) : A * B :=
  (a, b).

(* Function that destructures a tuple *)
Definition fst {A B : Type} (p : A * B) : A :=
  match p with
  | (a, _) => a
  end.

Definition snd {A B : Type} (p : A * B) : B :=
  match p with
  | (_, b) => b
  end.

(* Swap elements of a pair *)
Definition swap {A B : Type} (p : A * B) : B * A :=
  match p with
  | (a, b) => (b, a)
  end.

(* Test with int pairs *)
Definition test_pair := make_pair 1 2.
Definition test_fst := fst test_pair.
Definition test_swap := swap test_pair.

End Tuple.

Crane Extraction "tuple" Tuple.
