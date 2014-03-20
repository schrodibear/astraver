(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
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

(* From assembly to a set of purely sequential programs *)

module type INPUT = sig
  
  module Label : sig
    type t
    val create : unit -> t
    val equal : t -> t -> bool
    val hash : t -> int
    val to_string : t -> string
  end

  type predicate
    
  val ptrue : predicate

  val string_of_predicate : predicate -> string

  type statement
    
  val void_stmt : statement

  val append_stmt : statement -> statement -> statement

  val assert_stmt : predicate -> statement

  val string_of_stmt : statement -> string
    
end


module Make(X : INPUT) : sig

  type asm =
    | Ainvariant of X.predicate
    | Ajump of X.Label.t
    | Acond of X.Label.t * X.statement * X.statement
    | Ahalt
    | Aother of X.statement

  type asm_code = (X.Label.t * asm) list
  
  type seq_code = {
    seq_pre : X.predicate option;
    seq_code : X.statement;
  }

  val transform : show_graph:bool -> asm_code -> X.Label.t -> seq_code list

end


