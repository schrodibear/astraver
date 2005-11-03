(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(*i $Id: options.mli,v 1.43 2005-11-03 14:11:36 filliatr Exp $ i*)

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
val output : (Format.formatter -> unit) -> unit

val wol : bool

val c_file : bool ref

val werror : bool

val parse_only : bool
val type_only : bool
val wp_only : bool

val black : bool
val white : bool
val wbb : bool
val lvlmax : int
val all_vc : bool

(*s Prover options *)

type coq_version = V7 | V8

type prover = 
  | Coq of coq_version | Pvs | HolLight | Mizar | Harvey | Simplify | CVCLite
  | SmtLib | Isabelle | Hol4 | Dispatcher

val prover : unit -> prover

val valid : bool
val coq_tactic : string option
val coq_preamble : string

val pvs_preamble : string

val mizar_environ : string option

val isabelle_base_theory : string

val no_simplify_prelude : bool
val no_harvey_prelude : bool
val no_cvcl_prelude : bool
val simplify_typing : bool

val fpi : bool

(*s [file f] appends [f] to the directory specified with [-dir], if any *)

val file : string -> string

(*s Files given on the command line *)

val files : string list

(*s GUI? *)

val gui : bool ref

val prelude : bool
val prelude_file : string


