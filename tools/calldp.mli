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

(*i $Id: calldp.mli,v 1.3 2006-03-01 14:52:12 filliatr Exp $ i*)

(* Call external decision procedures on a single input file *)

(* The input files contain only on proof obligation, apart from the case of 
   harvey where it may contain several proof obligations (used in dp) *)

type prover_result = 
  | Valid | Invalid | CannotDecide | Timeout | ProverFailure of string

val simplify : 
  ?timeout:int -> filename:string -> unit -> 
  prover_result

val harvey : 
  ?timeout:int -> ?eclauses:int -> filename:string -> unit -> 
  prover_result list

val cvcl : 
  ?timeout:int -> filename:string -> unit -> 
  prover_result

val zenon : 
  ?timeout:int -> filename:string -> unit -> 
  prover_result

val debug : bool ref
