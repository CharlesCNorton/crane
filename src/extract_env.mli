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

(** {1 Extraction Environment and Commands}

    Top-level entry points for the [Crane Extraction] vernacular commands.
    Coordinates the full extraction pipeline:
    {v Rocq source  -->  MiniML  -->  MiniCpp  -->  C++ files v}

    Also handles dependency resolution, file I/O, compilation with clang, and
    benchmarking. *)

open Names
open Libnames
open Table

(** [Extraction qualid]: extract a single definition and print to stdout. *)
val simple_extraction : opaque_access:Global.indirect_accessor -> qualid -> unit

(** [Crane Extraction "file" qualids]: extract listed definitions to a file. *)
val full_extraction :
  opaque_access:Global.indirect_accessor -> string option -> qualid list -> unit

(** [Separate Extraction qualids]: extract each definition to its own file. *)
val separate_extraction :
  opaque_access:Global.indirect_accessor -> qualid list -> unit

(** [Extraction Library lib]: extract an entire library module. *)
val extraction_library :
  opaque_access:Global.indirect_accessor -> bool -> lident -> unit

(** Extract to file then compile with clang. Used by the test suite. *)
val extract_and_compile :
  opaque_access:Global.indirect_accessor -> string option -> qualid list -> unit

(** Build the complete MiniML structure for a set of definitions. *)
val mono_environment :
  opaque_access:Global.indirect_accessor ->
  GlobRef.t list ->
  ModPath.t list ->
  Miniml.ml_structure

(** Pretty-print a single declaration. Used by the Relation Extraction plugin.
*)
val print_one_decl : Miniml.ml_structure -> ModPath.t -> Miniml.ml_decl -> Pp.t

(** [Show Extraction]: show the extraction of the current ongoing proof. *)
val show_extraction : pstate:Declare.Proof.t -> unit

(** [Crane Benchmark]: extract, compile, and benchmark with hyperfine. *)
val benchmark : qualid -> (benchmark_lang * string * string) list -> unit
