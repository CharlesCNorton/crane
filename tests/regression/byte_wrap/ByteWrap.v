(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Behavioral candidate: byte_of_nat wraps values modulo 256. *)

From Stdlib Require Import Nat.

Module ByteWrap.

Definition byte_of_nat (n : nat) : nat := n mod 256.

Definition t : nat := byte_of_nat 263.

End ByteWrap.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "byte_wrap" ByteWrap.
