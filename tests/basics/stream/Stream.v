(* Coinductive stream test — infinite sequences with exactly one constructor *)

From Stdlib Require Import List.
Import ListNotations.

Module Stream.

CoInductive stream (A : Type) : Type :=
| scons : A -> stream A -> stream A.

Arguments scons {A} x xs.

(* Take n elements from a stream *)
Fixpoint take {A : Type} (n : nat) (s : stream A) {struct n} : list A :=
  match n with
  | O => nil
  | S n' =>
    match s with
    | scons x xs => cons x (take n' xs)
    end
  end.

(* Repeat a single value forever *)
CoFixpoint repeat {A : Type} (x : A) : stream A :=
  scons x (repeat x).

(* Counting stream: n, n+1, n+2, ... *)
CoFixpoint nats_from (n : nat) : stream nat :=
  scons n (nats_from (S n)).

(* Interleave two streams: a0, b0, a1, b1, ... *)
CoFixpoint interleave {A : Type} (sa sb : stream A) : stream A :=
  match sa with
  | scons a as_ => scons a (interleave sb as_)
  end.

(* Test values *)
Definition ones : stream nat := repeat 1.
Definition first_five_nats : list nat := take 5 (nats_from 0).
Definition first_five_ones : list nat := take 5 ones.
Definition interleaved : list nat := take 8 (interleave (nats_from 0) (repeat 7)).

End Stream.

Require Crane.Extraction.
Crane Extraction "stream" Stream.
