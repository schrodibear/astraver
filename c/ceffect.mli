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

(*i $Id: ceffect.mli,v 1.27 2006-06-22 13:07:16 hubert Exp $ i*)

(*
val interp_type : Cast.nctype -> string
*)

open Info

type effect =
    {
      reads : ZoneSet.t;
      assigns : ZoneSet.t;
      reads_var : HeapVarSet.t;
      assigns_var : HeapVarSet.t;
    }

val ef_union : effect -> effect -> effect

val ef_empty : effect

val global_var :  Info.var_info list ref

val intersect_only_alloc : effect -> effect -> bool

val is_alloc : Info.var_info -> bool

val assigns_alloc : effect -> bool

(* all heap vars and their associated types *)
val heap_vars : (string, Info.var_info) Hashtbl.t

(*
val zone_type : (string, Info.zone) Hashtbl.t
*)

val print_heap_vars : Format.formatter -> unit -> unit


(*
val heap_var_type : var_info -> Info.why_type
*)
(*val memorycell_name : Info.why_type -> string*)

val is_memory_var : var_info -> bool

(*val location : Cast.nterm Clogic.location -> HeapVarSet.t*)

val locations : Cast.nterm Clogic.location list -> effect

val predicate : Cast.npredicate -> effect

val expr : Cast.nexpr -> effect

val statement : Cast.nstatement -> effect

(* computes effects for logical symbols only *)
val file : Cast.nfile -> unit

(* computes functions effects; 
   return [true] when fixpoint is reached (no more modification) 
val functions : Cast.nfile -> bool*)

(* Compute functions effects *)
val effect : ('a * Cast.ndecl Cast.located list) list -> fun_info list -> unit

(* table for weak invariants *)
val weak_invariants : (string, Cast.npredicate * effect) Hashtbl.t

(* table for strong invariants *)
val strong_invariants : 
  (string, (Cast.npredicate * effect * effect)) Hashtbl.t

val strong_invariants_2 : 
  (string, Cast.npredicate * effect * (string * Output.base_type) list ) 
  Hashtbl.t

val invariants_for_struct : 
  (string, (Cast.npredicate * effect * effect)) Hashtbl.t

val mem_strong_invariant_2 : string -> bool
    
(* table of warnings from computation of effects *)
val warnings : (Loc.position * string) Queue.t

