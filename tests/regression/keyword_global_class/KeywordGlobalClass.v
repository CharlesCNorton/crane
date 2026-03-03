(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: keyword-like global names are escaped at emission sites. *)

From Stdlib Require Import Nat.

Module KeywordGlobalClass.

Definition class (n : nat) : nat := n + 1.
Definition t : nat := class 0.

End KeywordGlobalClass.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "keyword_global_class" KeywordGlobalClass.
