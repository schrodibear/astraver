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

(*i $Id: ceffect.mli,v 1.9 2004-04-14 07:33:55 marche Exp $ i*)

val interp_type : Cast.tctype -> string

open Info

type effect =
    {
      reads : HeapVarSet.t;
      assigns : HeapVarSet.t;
    }

(* all heap vars and their associated types *)
val heap_vars : (string, Output.base_type) Hashtbl.t
val print_heap_vars : Format.formatter -> unit -> unit

val heap_var_type : string -> Output.base_type

val location : Cast.tterm Clogic.location -> HeapVarSet.t

val locations : Cast.tterm Clogic.location list -> HeapVarSet.t

val predicate : Cast.predicate -> HeapVarSet.t

val expr : Cast.texpr -> effect

val statement : Cast.tstatement -> effect

(* computes effects for logical symbols only *)
val file : Cast.tfile -> unit

(* computes functions effects; 
   return [true] when fixpoint is reached (no more modification) *)
val functions : Cast.tfile -> bool
