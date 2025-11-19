(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
From Stdlib Require Import Lists.List.
Import ListNotations.

Module Tree.

Inductive tree (A : Type) : Type :=
| leaf : tree A
| node : tree A -> A -> tree A -> tree A.

Arguments leaf {A}.
Arguments node {A} t1 x t2.

Fixpoint flatten {A : Type} (t : tree A) : list A :=
  match t with
  | leaf => []
  | node l x r => flatten l ++ (x :: flatten r)
  end.

Definition tree1 := node (node leaf 3 (node leaf 7 leaf)) 1 (node leaf 4 (node (node leaf 6 leaf) 2 leaf)).

(*
Definition list1 := flatten tree1.
*)
End Tree.

Require Crane.Extraction.
Crane Extraction TestCompile "tree" Tree.
