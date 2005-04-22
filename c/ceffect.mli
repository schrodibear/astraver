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

(*i $Id: ceffect.mli,v 1.21 2005-04-22 13:37:01 hubert Exp $ i*)

val interp_type : Cast.nctype -> string

open Info

type effect =
    {
      reads : HeapVarSet.t;
      assigns : HeapVarSet.t;
    }

val global_var :  Info.var_info list ref

val intersect_only_alloc : HeapVarSet.t -> HeapVarSet.t -> bool

(* all heap vars and their associated types *)
val heap_vars : (string, Output.base_type) Hashtbl.t
val print_heap_vars : Format.formatter -> unit -> unit

val heap_var_type : var_info -> Output.base_type
val is_memory_var : var_info -> bool

(*val location : Cast.nterm Clogic.location -> HeapVarSet.t*)

val locations : Cast.nterm Clogic.location list -> HeapVarSet.t

val predicate : Cast.npredicate -> HeapVarSet.t

val expr : Cast.nexpr -> effect

val statement : Cast.nstatement -> effect

(* computes effects for logical symbols only *)
val file : Cast.nfile -> unit

(* computes functions effects; 
   return [true] when fixpoint is reached (no more modification) *)
val functions : Cast.nfile -> bool

(* table for weak invariants *)
val weak_invariants : (string, Cast.npredicate * HeapVarSet.t) Hashtbl.t

(* table for strong invariants *)
val strong_invariants : 
  (string, (Cast.npredicate * HeapVarSet.t * HeapVarSet.t)) Hashtbl.t

val strong_invariants_2 : 
  (string, Cast.npredicate * HeapVarSet.t * (string * Output.base_type) list ) 
  Hashtbl.t

val mem_strong_invariant_2 : string -> bool
    
(* table of warnings from computation of effects *)
val warnings : (Loc.t * string) Queue.t

