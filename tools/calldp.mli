(********************************************************************************)
(*                                                                              *)
(*  The Why platform for program certification                                  *)
(*                                                                              *)
(*  Copyright (C) 2002-2010                                                     *)
(*                                                                              *)
(*    Yannick MOY, Univ. Paris-sud 11                                           *)
(*    Jean-Christophe FILLIATRE, CNRS                                           *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                                 *)
(*    Romain BARDOU, Univ. Paris-sud 11                                         *)
(*    Thierry HUBERT, Univ. Paris-sud 11                                        *)
(*                                                                              *)
(*  Secondary contributors:                                                     *)
(*                                                                              *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)                *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)              *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)              *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hypothesis pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                             *)
(*                                                                              *)
(*  This software is free software; you can redistribute it and/or              *)
(*  modify it under the terms of the GNU Lesser General Public                  *)
(*  License version 2.1, with the special exception on linking                  *)
(*  described in file LICENSE.                                                  *)
(*                                                                              *)
(*  This software is distributed in the hope that it will be useful,            *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of              *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                        *)
(*                                                                              *)
(********************************************************************************)



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

val pvs : 
  ?debug:bool -> 
  ?timeout:int -> filename:string -> unit -> prover_result
