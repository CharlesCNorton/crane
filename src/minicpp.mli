(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*s Target language for extraction: a core C++ called MiniCpp. *)

open Names

type cpp_tymod =
  | TMconst
  | TMstatic
  | TMextern


type cpp_type =
  | Tvar of int * Id.t option
  | Tglob of GlobRef.t * cpp_type list * cpp_expr list
  | Tfun of cpp_type list * cpp_type
  | Tmod of cpp_tymod * cpp_type
  | Tnamespace of GlobRef.t * cpp_type
  | Tstruct of GlobRef.t * cpp_type list   (* This overlaps with Tglob..... *)
  | Tref of cpp_type
  | Tvariant of cpp_type list
  | Tshared_ptr of cpp_type
  | Tstring
  | Tvoid
  | Ttodo
  | Tunknown

and cpp_meta = { id : int; mutable contents : cpp_type option }

and cpp_stmt =
  | SreturnVoid (* TODO: better this or option below? *)
  | Sreturn of cpp_expr
  | Sdecl of Id.t * cpp_type
  | Sasgn of Id.t * cpp_type option * cpp_expr
  | Sexpr of cpp_expr
  | Scustom_case of cpp_type * cpp_expr * cpp_type list * ((Id.t * cpp_type) list * cpp_type * cpp_stmt list) list * string

(* add something for (mutual) fixpoints? *)
and cpp_expr =
  | CPPvar of Id.t
  | CPPvar' of int (* remove eventually!!! *)
  | CPPglob of GlobRef.t * cpp_type list
  | CPPnamespace of GlobRef.t * cpp_expr
  | CPPfun_call of cpp_expr * cpp_expr list
  | CPPderef of cpp_expr
  | CPPmove of cpp_expr
  | CPPforward of cpp_type * cpp_expr
  | CPPlambda of (cpp_type * Id.t option) list * cpp_type option * cpp_stmt list
  | CPPvisit
  | CPPmk_shared of cpp_type
  | CPPoverloaded of cpp_expr list (* cpp_expressions in list should only be lambdas. TODO: enforce in the AST? split up to a funcall *)
  | CPPmatch of cpp_expr * (cpp_expr * cpp_expr) list
  | CPPstructmk of GlobRef.t * cpp_type list * cpp_expr list
  | CPPstruct of GlobRef.t * cpp_type list *  cpp_expr list (* Figure out better name situation!! *)
  | CPPget of cpp_expr * Id.t (* access from a struct (or class) *)
  | CPPget' of cpp_expr * GlobRef.t (* access from a struct (or class) *)
  | CPPstring of Pstring.t
  | CPPuint   of Uint63.t
  | CPPparray of cpp_expr array * cpp_expr
(*| CPPnamespace of Id.t * cpp_expr    should we do this for namespace acces (in general, as is not just cpp_expressions)? *)
  | CPPrequires of (cpp_type * Id.t) list * (cpp_expr * cpp_constraint) list
  (* requires (T a, T b) { { eqb(a, b) } -> std::same_as<bool> } *)

and cpp_constraint = cpp_expr

(* TODO: maybe switch all Id.t to GlobRef.t *)
and cpp_field =
  | Fvar of Id.t * cpp_type
  | Fvar' of GlobRef.t * cpp_type
  | Ffundef of Id.t * cpp_type * (Id.t * cpp_type) list * cpp_stmt list
  | Ffundecl of Id.t * cpp_type * (Id.t * cpp_type) list

(* C++ type schema.
   The integer is the number of variable in the schema. *)

type cpp_schema = int * cpp_type

val ind_ty_ptr : GlobRef.t -> cpp_type list -> cpp_type

type template_type =
  | TTtypename
  | TTfun of (cpp_type list * cpp_type)
  | TTconcept of GlobRef.t  (* e.g., 'Eq T' *)


type cpp_decl =
  | Dtemplate of (template_type * Id.t) list  * cpp_constraint option * cpp_decl
  | Dnspace of GlobRef.t option * cpp_decl list
  | Dfundef of (GlobRef.t * cpp_type list) list * cpp_type * (Id.t * cpp_type) list * cpp_stmt list
  | Dfundecl of (GlobRef.t * cpp_type list) list * cpp_type * (Id.t option * cpp_type) list
  | Dstruct of GlobRef.t * (cpp_field * bool) list (* bool indicates if cpp_field is public *)
(*| Dclass of GlobRef.t * cpp_type * (cpp_field * bool) list (* bool indicates if cpp_field is public *)*)
  | Dstruct_decl of GlobRef.t
  | Dusing of GlobRef.t * cpp_type
  | Dasgn of GlobRef.t * cpp_type * cpp_expr
  | Ddecl of GlobRef.t * cpp_type
  | Dconcept of GlobRef.t * cpp_expr (* template params are provided by an outer Dtemplate *)
  | Dstatic_assert of cpp_expr * string option
