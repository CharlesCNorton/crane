(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(* Regression: keyword-like parameter names are escaped safely. *)

From Stdlib Require Import Nat.

Module KeywordParamVirtual.

Definition id (virtual : nat) : nat := virtual.
Definition t : nat := id 3.

End KeywordParamVirtual.

Require Crane.Extraction.
From Crane Require Mapping.Std Mapping.NatIntStd.
Crane Extraction "keyword_param_virtual" KeywordParamVirtual.
