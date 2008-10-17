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
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)



type prover =
  {
    name : string;
    mutable version: string;
    version_switch : string;
    version_regexp : string;
    mutable command : string;
    command_switches : string;
(*
    correct_exit_codes : int list;
*)
    valid_regexp : string;
    mutable valid_cregexp : Str.regexp option;
    undecided_regexp : string;
    mutable undecided_cregexp : Str.regexp option;
(*
    invalid_regexp : string;
    invalid_cregexp : Str.regexp option;
*)
  }
    

val alt_ergo : prover

val simplify : prover

val z3 : prover

val yices : prover

val cvc3 : prover

val prover_list : (prover * string list) list

val load_rc_file : unit -> unit

val save_rc_file : unit -> unit
