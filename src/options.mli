(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: options.mli,v 1.74 2007-06-15 11:48:43 marche Exp $ i*)

(*s General options *)

val verbose : bool

val if_verbose : ('a -> unit) -> 'a -> unit
val if_verbose_2 : ('a -> 'b -> unit) -> 'a -> 'b -> unit
val if_verbose_3 : ('a -> 'b -> 'c -> unit) -> 'a -> 'b -> 'c -> unit

val debug : bool

val if_debug : ('a -> unit) -> 'a -> unit
val if_debug_2 : ('a -> 'b -> unit) -> 'a -> 'b -> unit
val if_debug_3 : ('a -> 'b -> 'c -> unit) -> 'a -> 'b -> 'c -> unit

val ocaml : bool
val ocaml_annot : bool
val ocaml_externals : bool

val int_is_ident : bool

val wol : bool

val c_file : bool ref

val werror : bool

val parse_only : bool
val type_only : bool
val wp_only : bool

val fast_wp : bool
val black : bool
val white : bool
val wbb : bool
val split_user_conj : bool
val lvlmax : int
val all_vc : bool
val pruning : bool
val pruning_hyp : int
val modulo : bool

type expanding = All | Goal | NoExpanding
val defExpanding : expanding
val get_type_expanding : unit -> expanding 

type encoding = 
  | NoEncoding | Predicates | Stratified | Recursive | Monomorph 
  | SortedStratified
val get_types_encoding : unit -> encoding
val set_types_encoding : encoding -> unit

type termination = UseVariant | Partial | Total
val termination : termination

(*s Prover options *)

type coq_version = V7 | V8

type prover = 
  | Coq of coq_version | Pvs | HolLight | Mizar | Harvey | Simplify | CVCLite
  | SmtLib | Isabelle | Hol4 | Gappa | Zenon | Why | MultiWhy | Dispatcher

val prover : unit -> prover

val valid : bool
val coq_tactic : string option
val coq_preamble : string

val pvs_preamble : string

val mizar_environ : string option

val isabelle_base_theory : string

val no_simplify_prelude : bool
val simplify_triggers : bool
val no_harvey_prelude : bool
val no_zenon_prelude : bool
val no_cvcl_prelude : bool

val floats : bool
val show_time : bool
val gappa_rnd : string

(*s [file f] appends [f] to the directory specified with [-dir], if any *)

val file : string -> string

(* [out_file f] returns the file specified with option -o, 
   or [file f] otherwise *)

val out_file : string -> string

(*s Files given on the command line *)

val files : string list

(*s GUI? *)

val gui : bool ref

val lib_files_to_load : string list

(*
Local Variables: 
compile-command: "unset LANG; make -j -C .. bin/why.byte"
End: 
*)
