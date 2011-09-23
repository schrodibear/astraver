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




type prover_id =
    Simplify | Harvey | Cvcl | Zenon | Rvsat | Yices | Ergo | ErgoSelect
  | Cvc3 | SimplifySelect | Z3 | Gappa | GappaSelect
  | Coq | PVS | VeriT | Vampire

type lazy_regexp =
  {
    regexp : string;
    mutable cregexp  : Str.regexp option;
  }

type prover_data =
  {
    name : string;
    is_interactive : bool;
    mutable version: string;
    version_switch : string;
    version_regexp : string;
    versions_ok : string list;
    versions_old : string list;
    mutable command : string;
    command_switches : string;
    valid_regexp : lazy_regexp option;
    undecided_regexp : lazy_regexp;
    stdin_switch : string option;
  }


val alt_ergo : prover_data

val simplify : prover_data

val vampire: prover_data

val z3 : prover_data

val yices : prover_data

val verit: prover_data

val cvc3 : prover_data

(* cvcl is in fact cvc3 with native language *)
val cvcl : prover_data

val gappa : prover_data

val coq : prover_data

val pvs : prover_data

val prover_list : (prover_id * (prover_data * string list)) list
  (** list of all known provers: uniq id, data, list of possible command names *)

val rc_file : unit -> string

val load_rc_file : unit -> unit

val save_rc_file : unit -> unit
