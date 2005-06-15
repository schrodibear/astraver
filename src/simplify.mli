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

(*i $Id: simplify.mli,v 1.5 2005-06-15 07:08:29 filliatr Exp $ i*)

open Vcg

val reset : unit -> unit

val push_obligations : obligation list -> unit

val push_axiom : string -> Logic.predicate Env.scheme -> unit

val push_predicate : string -> Logic.predicate_def Env.scheme -> unit

val push_function : string -> Logic.function_def Env.scheme -> unit

val output_file : string -> unit

