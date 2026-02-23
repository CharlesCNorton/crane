(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Test: Deeply nested pattern matching — 4+ levels deep. *)

From Stdlib Require Import List Nat Bool.
Import ListNotations.

(* Deep match on nested options *)
Definition deep_option (x : option (option (option nat))) : nat :=
  match x with
  | Some (Some (Some n)) => n
  | Some (Some None) => 1
  | Some None => 2
  | None => 3
  end.

(* Deep match on nested pairs *)
Definition deep_pair (p : (nat * nat) * (nat * nat)) : nat :=
  match p with
  | ((a, b), (c, d)) => a + b + c + d
  end.

(* Deep match on list structure *)
Definition list_shape (l : list nat) : nat :=
  match l with
  | [] => 0
  | [x] => x
  | [x; y] => x + y
  | [x; y; z] => x + y + z
  | x :: y :: z :: _ :: rest => x + y + z + length rest
  end.

(* Deep match on nested sum types *)
Inductive outer :=
  | OLeft : inner -> outer
  | ORight : nat -> outer
with inner :=
  | ILeft : nat -> inner
  | IRight : bool -> inner.

Definition deep_sum (o : outer) : nat :=
  match o with
  | OLeft (ILeft n) => n
  | OLeft (IRight true) => 1
  | OLeft (IRight false) => 0
  | ORight n => n + 100
  end.

(* Deep match mixing constructors *)
Definition complex_match (x : option (nat * list nat)) : nat :=
  match x with
  | None => 0
  | Some (n, []) => n
  | Some (n, [m]) => n + m
  | Some (n, m :: _ :: rest) => n + m + length rest
  end.

(* Nested match with guards via if *)
Definition guarded_match (p : nat * nat) : nat :=
  match p with
  | (a, b) => if Nat.leb a b then b - a else a - b
  end.

(* === Test values === *)

Definition test_deep_some : nat := deep_option (Some (Some (Some 42))).
Definition test_deep_none : nat := deep_option (Some (Some None)).
Definition test_deep_pair : nat := deep_pair ((1, 2), (3, 4)).
Definition test_shape_3 : nat := list_shape [10; 20; 30].
Definition test_shape_long : nat := list_shape [1; 2; 3; 4; 5; 6].
Definition test_deep_sum : nat := deep_sum (OLeft (ILeft 77)).
Definition test_complex : nat := complex_match (Some (5, [10; 20; 30])).
Definition test_guarded : nat := guarded_match (3, 7).

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "deep_patterns"
  deep_option deep_pair list_shape deep_sum complex_match guarded_match
  test_deep_some test_deep_none test_deep_pair
  test_shape_3 test_shape_long test_deep_sum
  test_complex test_guarded.
