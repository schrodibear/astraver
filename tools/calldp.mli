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

type prover = ?debug:bool -> ?timeout:int -> ?filename:string -> ?buffers:(Buffer.t list) -> unit -> 
  prover_result

val gappa : ?debug:bool -> ?timeout:int -> filename:string -> unit -> 
  prover_result

val simplify : ?debug:bool -> ?timeout:int -> filename:string -> unit -> 
  prover_result

val harvey : 
  ?debug:bool -> ?timeout:int -> filename:string -> unit -> 
  prover_result 

val zenon : 
  ?debug:bool -> ?timeout:int -> filename:string -> unit -> 
  prover_result

val rvsat : 
  ?debug:bool -> ?timeout:int -> filename:string -> unit -> 
  prover_result

val yices : prover

val cvc3 : prover

val cvcl : prover

val z3 : prover

val ergo : select_hypotheses:bool -> prover

val generic_hypotheses_selection : 
  ?debug:bool -> 
  ?timeout:int -> filename:string -> DpConfig.prover_id -> unit -> prover_result

val coq : 
  ?debug:bool -> 
  ?timeout:int -> filename:string -> unit -> prover_result
