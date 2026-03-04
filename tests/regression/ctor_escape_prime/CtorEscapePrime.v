(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* WIP: constructor escaping collision for prime/underscore forms. *)

From Stdlib Require Import Nat.

Module CtorEscapePrime.

Inductive item : Type := | T' | T_.

Definition tag (x : item) : nat :=
  match x with
  | T' => 1
  | T_ => 2
  end.

Definition t : nat := tag T' + tag T_.

End CtorEscapePrime.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "ctor_escape_prime" CtorEscapePrime.
