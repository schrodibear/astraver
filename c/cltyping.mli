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

(*i $Id: cltyping.mli,v 1.27 2005-03-23 14:59:18 filliatr Exp $ i*)

(* Typing of C annotations *)

open Clogic
open Cast
open Cenv

(* logical environments *)
val type_term : Env.t -> parsed_term  -> tterm
val type_predicate : Env.t -> parsed_predicate -> Cast.predicate
val type_location : Env.t -> parsed_term location -> tterm location
val type_spec : tctype option -> Env.t -> parsed_spec -> Cast.spec
val type_loop_annot : Env.t -> parsed_loop_annot -> Cast.loop_annot
val type_logic_type : Env.t -> parsed_logic_type -> tctype
(*
val int_constant : string -> 'a term
*)

(*val noattr : 'a ctype_node -> 'a ctype
val c_void : 'a ctype
val c_int : 'a ctype
val c_float : 'a ctype
val c_string : 'a ctype
val c_array : 'a ctype -> 'a ctype
val c_pointer : 'a ctype -> 'a ctype
val c_addr : 'a ctype
*)
