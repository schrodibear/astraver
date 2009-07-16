(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann RÉGIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2, with the special exception on linking              *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(*i $Id: calldp.mli,v 1.26 2009-07-16 14:50:54 nguyen Exp $ i*)

(* Call external decision procedures on a single input file *)

(* The input files contain only on proof obligation, apart from the case of 
   harvey where it may contain several proof obligations (used in dp) *)

type prover_result = 
  | Valid of float
  | Invalid of float * string option 
  | CannotDecide of float * string option
  | Timeout of float
  | ProverFailure of float * string

val cpulimit : string ref

val gappa :
  ?debug:bool -> ?timeout:int -> filename:string -> unit -> 
  prover_result

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

val cvc3 : 
  ?debug:bool -> ?timeout:int -> filename:string -> unit -> 
  prover_result

val z3 : 
  ?debug:bool -> ?timeout:int -> filename:string -> unit -> 
  prover_result

val ergo : 
  ?debug:bool -> ?timeout:int -> select_hypotheses:bool -> filename:string ->
  unit -> prover_result

val generic_hypotheses_selection : 
  ?debug:bool -> 
  ?timeout:int -> filename:string -> DpConfig.prover_id -> unit -> prover_result

val coq : 
  ?debug:bool -> 
  ?timeout:int -> filename:string -> unit -> prover_result
