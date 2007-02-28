(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: calldp.mli,v 1.14 2007-02-28 07:51:43 couchot Exp $ i*)

(* Call external decision procedures on a single input file *)

(* The input files contain only on proof obligation, apart from the case of 
   harvey where it may contain several proof obligations (used in dp) *)

type prover_result = 
  | Valid of float
  | Invalid of float * string option 
  | CannotDecide of float * string option
  | Timeout of float
  | ProverFailure of float * string

val simplify : 
  ?debug:bool -> ?timeout:int -> filename:string -> unit -> 
  prover_result

val harvey : 
  ?debug:bool -> ?timeout:int -> filename:string -> unit -> 
  prover_result 

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
