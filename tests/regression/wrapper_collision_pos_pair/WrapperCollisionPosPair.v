(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: wrapper naming remains unique when basename is Pos. *)

From Stdlib Require Import Nat.

Module WrapperCollisionPosPair.

Module Left.
  Module Pos.
    Definition f (n : nat) : nat := n.
  End Pos.
End Left.

Module Right.
  Module Pos.
    Definition g (n : nat) : nat := S n.
  End Pos.
End Right.

Definition t : nat := Left.Pos.f 1 + Right.Pos.g 2.

End WrapperCollisionPosPair.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "wrapper_collision_pos_pair" WrapperCollisionPosPair.
