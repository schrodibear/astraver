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

open Cast
open Info


val type_why : nexpr -> why_type

val type_why_for_term : nterm -> why_type

val not_alias : Loc.position ->
  Cast.nctype Clogic.nterm -> Cast.nctype Clogic.nterm -> Cast.npredicate 

(*
val heap_var_name : why_type -> string
*)
(*
val heap_var : why_type -> string 
val heap_field_var : string -> why_type -> string 
*)
(*
val pointer_heap_var : why_type -> string * string

val global_type_for_why : why_type -> string
*)

val file : nfile -> unit

val valid_for_type : 
  ?fresh:bool -> Loc.position -> string -> 
    nterm -> npredicate

val separation :
  Loc.position -> 
  Info.var_info -> Info.var_info -> Ctypes.ctype Clogic.npredicate

val in_struct :  nterm -> Info.var_info -> nterm 

val unifier_type_why : why_type -> why_type -> unit
