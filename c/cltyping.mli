(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filliâtre - Claude Marché
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

(*i $Id: cltyping.mli,v 1.3 2004-02-04 16:21:28 filliatr Exp $ i*)

(* Typing of C annotations *)

open Clogic
open Cast

(* logical environments *)

type env
val empty : env
val add_fun : string -> tctype list * tctype -> env -> env
val add_pred : string -> tctype list -> env -> env

val type_predicate : env -> parsed_predicate -> Cast.predicate
val type_spec : env -> parsed_spec -> Cast.predicate spec
val type_loop_annot : env -> parsed_loop_annot -> Cast.loop_annot

val noattr : texpr ctype_node -> tctype
val c_void : tctype
val c_int : tctype
val c_float : tctype
val c_string : tctype
