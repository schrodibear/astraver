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

(*i $Id: cltyping.mli,v 1.6 2004-02-10 08:36:51 filliatr Exp $ i*)

(* Typing of C annotations *)

open Clogic
open Cast
open Cenv

(* logical environments *)

val type_predicate : Env.t -> parsed_predicate -> Cast.predicate
val type_spec : Env.t -> parsed_spec -> Cast.spec
val type_loop_annot : Env.t -> parsed_loop_annot -> Cast.loop_annot
val type_logic_type : Env.t -> parsed_logic_type -> tctype

val noattr : 'a ctype_node -> 'a ctype
val c_void : 'a ctype
val c_int : 'a ctype
val c_float : 'a ctype
val c_string : 'a ctype
val c_array : 'a ctype -> 'a ctype
