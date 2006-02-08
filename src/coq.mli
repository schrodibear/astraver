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

(*i $Id: coq.mli,v 1.20 2006-02-08 09:08:22 filliatr Exp $ i*)

open Cc
open Vcg

val reset : unit -> unit

val push_obligations : obligation list -> unit

val push_validation : string -> cc_type -> validation -> unit

val push_parameter : string -> cc_type -> unit

val push_logic : string -> Logic.logic_type Env.scheme -> unit
val push_axiom : string -> Logic.predicate Env.scheme -> unit
val push_predicate : string -> Logic.predicate_def Env.scheme -> unit
val push_function : string -> Logic.function_def Env.scheme -> unit
val push_type : string -> Ident.t list -> unit

val output_file : string -> unit

(* exported for the GUI *)

val print_predicate_v8 : Format.formatter -> Logic.predicate -> unit
val print_cc_type_v8 : Format.formatter -> Cc.cc_type -> unit
val print_binder_v8 : Format.formatter -> Cc.cc_binder -> unit
val print_binder_type_v8 : Format.formatter -> Cc.cc_binder -> unit
val print_term_v8 : Format.formatter -> Logic.term -> unit
