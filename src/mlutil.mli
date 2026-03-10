(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(** Utility functions over ML types and terms, type environments, and optimization passes. *)

open Names
open Miniml
open Table

(** {2 Utility functions over ML types with meta} *)

(** Reset the meta variable counter. *)
val reset_meta_count : unit -> unit

(** Create a fresh meta variable. *)
val new_meta : 'a -> ml_type

(** Substitute type variables using a list of types. *)
val type_subst_list : ml_type list -> ml_type -> ml_type

(** Substitute type variables using an array of types. *)
val type_subst_vect : ml_type array -> ml_type -> ml_type

(** Instantiate a type schema with fresh meta variables. *)
val instantiation : ml_schema -> ml_type

(** Replace unknown meta variables with fresh type variables. *)
val instantiate_unknowns : ml_type -> ml_type

(** Attempt most general unification of two types. *)
val try_mgu : ml_type -> ml_type -> unit

(** Determine if a type coercion requires magic (unsafe cast). *)
val needs_magic : ml_type * ml_type -> bool

(** Conditionally wrap an ML term with magic if the flag is true. *)
val put_magic_if : bool -> ml_ast -> ml_ast

(** Wrap an ML term with magic if the type pair requires it. *)
val put_magic : ml_type * ml_type -> ml_ast -> ml_ast

(** Check if an ML term can be generalized. *)
val generalizable : ml_ast -> bool

(** {2 ML type environment} *)

module Mlenv : sig
  type t
  val empty : t

  (** Get the n-th most recently entered schema and instantiate it. *)
  val get : t -> int -> ml_type

  (** Add a type to the environment, after generalizing free meta variables. *)
  val push_gen : t -> ml_type -> t

  (** Add a type with no [Tvar]. *)
  val push_type : t -> ml_type -> t

  (** Add a type with no [Tvar] nor [Tmeta]. *)
  val push_std_type : t -> ml_type -> t
end

(** {2 Utility functions over ML types without meta} *)

(** Check if a mutual inductive name occurs in a type. *)
val type_mem_kn : MutInd.t -> ml_type -> bool

(** Return the maximum type variable index in a type. *)
val type_maxvar : ml_type -> int

(** Decompose an ML type into a list of argument types and a result type. *)
val type_decomp : ml_type -> ml_type list * ml_type

(** Recompose an ML type from a list of argument types and a result type. *)
val type_recomp : ml_type list * ml_type -> ml_type

(** Convert type variables to primed type variables. *)
val var2var' : ml_type -> ml_type

(** Abbreviation map type for looking up type aliases. *)
type abbrev_map = GlobRef.t -> ml_type option

(** Expand type abbreviations using the given map. *)
val type_expand : abbrev_map -> ml_type -> ml_type

(** Simplify an ML type. *)
val type_simpl : ml_type -> ml_type

(** Convert an ML type to a signature (sign). *)
val type_to_sign : abbrev_map -> ml_type -> sign

(** Convert an ML type to a full signature. *)
val type_to_signature : abbrev_map -> ml_type -> signature

(** Expunge dummy types from an ML type using the abbreviation map. *)
val type_expunge : abbrev_map -> ml_type -> ml_type

(** Expunge dummy types from an ML type guided by a signature. *)
val type_expunge_from_sign : abbrev_map -> signature -> ml_type -> ml_type

(** Test equality of two ML types. *)
val eq_ml_type : ml_type -> ml_type -> bool

(** Check if a type is Tdummy. *)
val isTdummy : ml_type -> bool

(** Check if an ML term is MLdummy. *)
val isMLdummy : ml_ast -> bool

(** Check if a sign is Kill. *)
val isKill : sign -> bool

(** Expunge dummy arguments from a case expression. *)
val case_expunge : signature -> ml_ast -> (ml_ident * ml_type) list * ml_ast

(** Expunge dummy arguments from a term. *)
val term_expunge : signature -> (ml_ident * ml_type) list * ml_ast -> ml_ast


(** {2 Special identifiers}

    [dummy_name] is to be used for dead code and will be printed as [_] in concrete (Caml) code. *)

(** The anonymous identifier used for unnamed binders. *)
val anonymous_name : Id.t

(** The dummy identifier used for dead code. *)
val dummy_name : Id.t

(** Convert a Name.t to an Id.t, using anonymous_name for anonymous names. *)
val id_of_name : Name.t -> Id.t

(** Extract the Id.t from an ml_ident. *)
val id_of_mlid : ml_ident -> Id.t

(** Generate a temporary identifier from an ml_ident. *)
val tmp_id : ml_ident -> ml_ident

(** {2 Lambda collection}

    [collect_lams MLlam(id1,...MLlam(idn,t)...)] returns the list [idn;...;id1] and the term [t]. *)

(** Collect all lambda abstractions from a term. *)
val collect_lams : ml_ast -> (ml_ident * ml_type) list * ml_ast

(** Collect exactly n lambda abstractions from a term. *)
val collect_n_lams : int -> ml_ast -> (ml_ident * ml_type) list * ml_ast

(** Remove n lambda abstractions from a term. *)
val remove_n_lams : int -> ml_ast -> ml_ast

(** Count the number of lambda abstractions at the head of a term. *)
val nb_lams : ml_ast -> int

(** Wrap a term in lambda abstractions with the given identifiers and types. *)
val named_lams : (ml_ident * ml_type) list -> ml_ast -> ml_ast

(** Wrap a term in n dummy lambda abstractions. *)
val dummy_lams : ml_ast -> int -> ml_ast

(** Wrap a term in anonymous or dummy lambda abstractions based on the signature. *)
val anonym_or_dummy_lams : ml_ast -> signature -> ml_ast

(** Wrap a term in anonymous or dummy lambda abstractions with types based on the signature. *)
val anonym_or_dummy_lams_typed : ml_ast -> ml_type list -> signature -> ml_ast

(** Generate eta-expanded argument list based on arity and signature. *)
val eta_args_sign : int -> signature -> ml_ast list

(** {2 Utility functions over ML terms} *)

(** Apply an ML term to a list of arguments. *)
val mlapp : ml_ast -> ml_ast list -> ml_ast

(** Map a function over all immediate subterms. *)
val ast_map : (ml_ast -> ml_ast) -> ml_ast -> ml_ast

(** Map a function over all immediate subterms with lifting. *)
val ast_map_lift : (int -> ml_ast -> ml_ast) -> int -> ml_ast -> ml_ast

(** Iterate a function over all immediate subterms. *)
val ast_iter : (ml_ast -> unit) -> ml_ast -> unit

(** Check if a de Bruijn index occurs in a term. *)
val ast_occurs : int -> ml_ast -> bool

(** Check if a de Bruijn index in the given interval occurs in a term. *)
val ast_occurs_itvl : int -> int -> ml_ast -> bool

(** Lift de Bruijn indices in a term. *)
val ast_lift : int -> ml_ast -> ml_ast

(** Pop the outermost de Bruijn level (inverse of lift). *)
val ast_pop : ml_ast -> ml_ast

(** Substitute a term for de Bruijn index 1. *)
val ast_subst : ml_ast -> ml_ast -> ml_ast

(** Substitute global references in a term using the given map. *)
val ast_glob_subst : ml_ast Refmap'.t -> ml_ast -> ml_ast

(** Remove unused variable bindings from a term. *)
val dump_unused_vars : ml_ast -> ml_ast

(** Normalize an ML term by beta-reduction and simplification. *)
val normalize : ml_ast -> ml_ast

(** Optimize fixpoint expressions. *)
val optimize_fix : ml_ast -> ml_ast

(** Determine if a global reference should be inlined in the given term. *)
val inline : GlobRef.t -> ml_ast -> bool

(** Check if a pattern is a basic (non-nested) pattern. *)
val is_basic_pattern : ml_pattern -> bool

(** Check if any branch has a deep (nested) pattern. *)
val has_deep_pattern : ml_branch array -> bool

(** Check if a match is regular (all patterns are basic). *)
val is_regular_match : ml_branch array -> bool

(** Exception raised when an operation is impossible. *)
exception Impossible

(** {2 Classification of signatures} *)

(** Classification of signatures based on their contents. *)
type sign_kind =
  | EmptySig
  | NonLogicalSig (* at least a [Keep] *)
  | SafeLogicalSig (* only [Kill Ktype] *)
  | UnsafeLogicalSig (* No [Keep], not all [Kill Ktype] *)

(** Classify a signature into one of the sign_kind categories. *)
val sign_kind : signature -> sign_kind

(** Remove trailing Keep elements from a signature. *)
val sign_no_final_keeps : signature -> signature

(** Remap type variables in a term using the given function. *)
val remap_tvars : (int -> int) -> ml_ast -> ml_ast
