(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)



open Info

type effect =
    {
      reads : ZoneSet.t;
      assigns : ZoneSet.t;
      reads_var : HeapVarSet.t;
      assigns_var : HeapVarSet.t;
      (* useful for generating separation invariants *)
      reads_under_pointer : HeapVarSet.t;
      assigns_under_pointer : HeapVarSet.t;
    }

val ef_union : effect -> effect -> effect

val ef_empty : effect

val global_var :  Info.var_info list ref

val intersect_only_alloc : effect -> effect -> bool

val is_alloc : Info.var_info -> bool

val assigns_alloc : effect -> bool

(* all heap vars and their associated types *)
val heap_vars : (string, Info.var_info) Hashtbl.t

val print_heap_vars : Format.formatter -> unit -> unit

val is_memory_var : var_info -> bool

val locations : Cast.nterm Clogic.location list -> effect

val predicate : Cast.npredicate -> effect

val expr : ?with_local:bool -> Cast.nexpr -> effect

val statement : ?with_local:bool -> Cast.nstatement -> effect

(* computes effects for logical symbols only *)
val file : Cast.nfile -> unit

(* Compute functions effects *)
val effect : ('a * Cast.ndecl Cast.located list) list -> fun_info list -> unit

(* table for weak invariants *)
val weak_invariants : (string, Cast.npredicate * effect) Hashtbl.t

(* table for strong invariants *)
val strong_invariants : 
  (string, (Cast.npredicate * effect * effect)) Hashtbl.t

val strong_invariants_2 : 
  (string, Cast.npredicate * effect * (string * Output.logic_type) list ) 
  Hashtbl.t

val invariants_for_struct : 
  (string, (Cast.npredicate * effect * effect)) Hashtbl.t

val mem_strong_invariant_2 : string -> bool
    
(* table of warnings from computation of effects *)
val warnings : (Loc.position * string) Queue.t

