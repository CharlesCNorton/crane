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

open Common
open Miniml
open Minicpp
open Names

exception TODO

val convert_ml_type_to_cpp_type : env -> GlobRef.t list -> Id.t list -> ml_type -> cpp_type
val gen_expr : env -> ml_ast -> cpp_expr
val gen_ind_cpp : variable list -> GlobRef.t -> GlobRef.t array -> ml_type list array -> cpp_decl
val gen_record_cpp : GlobRef.t -> GlobRef.t option list -> ml_ind_packet -> cpp_decl
val gen_cpp_case : ml_type -> ml_ast -> env -> ml_branch array -> cpp_expr
val gen_decl_for_pp : GlobRef.t -> ml_ast -> ml_type -> cpp_decl option * env * variable list
val gen_decl : GlobRef.t -> ml_ast -> ml_type -> cpp_decl * env * variable list
val gen_spec : GlobRef.t -> ml_ast -> ml_type -> cpp_decl * env
val gen_dfuns : GlobRef.t array * ml_ast array * ml_type array -> (cpp_decl * env * variable list) list
val gen_dfuns_header : GlobRef.t array * ml_ast array * ml_type array -> (cpp_decl * env) list
val gen_ind_header : variable list -> GlobRef.t -> GlobRef.t array -> ml_type list array -> cpp_decl
