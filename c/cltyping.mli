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

(*i $Id: cltyping.mli,v 1.14 2004-05-26 09:12:37 filliatr Exp $ i*)

(* Typing of C annotations *)

open Clogic
open Cast
open Cenv

(* logical environments *)

val type_predicate : Env.t -> parsed_predicate -> Cast.predicate
val type_location : Env.t -> parsed_term location -> tterm location
val type_spec : tctype option -> Env.t -> parsed_spec -> Cast.spec
val type_loop_annot : Env.t -> parsed_loop_annot -> Cast.loop_annot
val type_logic_type : Env.t -> parsed_logic_type -> tctype

val noattr : 'a ctype_node -> 'a ctype
val c_void : tctype
val c_int : tctype
val c_float : tctype
val c_string : tctype
val c_array : 'a ctype -> 'a ctype
val c_pointer : 'a ctype -> 'a ctype

val valid_for_type : Loc.t -> Info.var_info -> tctype -> predicate


