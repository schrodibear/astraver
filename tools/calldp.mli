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

(*i $Id: calldp.mli,v 1.8 2006-10-11 08:44:29 filliatr Exp $ i*)

(* Call external decision procedures on a single input file *)

(* The input files contain only on proof obligation, apart from the case of 
   harvey where it may contain several proof obligations (used in dp) *)

type prover_result = 
  | Valid 
  | Invalid of string option 
  | CannotDecide 
  | Timeout 
  | ProverFailure of string

val simplify : 
  ?debug:bool -> ?timeout:int -> filename:string -> unit -> 
  prover_result

val harvey : 
  ?debug:bool -> ?timeout:int -> ?eclauses:int -> filename:string -> unit -> 
  prover_result list

val cvcl : 
  ?debug:bool -> ?timeout:int -> filename:string -> unit -> 
  prover_result

val zenon : 
  ?debug:bool -> ?timeout:int -> filename:string -> unit -> 
  prover_result

val rvsat : 
  ?debug:bool -> ?timeout:int -> filename:string -> unit -> 
  prover_result

val yices : 
  ?debug:bool -> ?timeout:int -> filename:string -> unit -> 
  prover_result

val ergo : 
  ?debug:bool -> ?timeout:int -> filename:string -> unit -> 
  prover_result
