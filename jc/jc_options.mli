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



open Jc_stdlib
open Jc_env

(*s environment variables *)

val has_floats : bool ref
val libdir : string
(*val float_lib : string list*)
val get_libfiles : unit -> string list
(*val libfiles : string list ref*)
val add_to_libfiles : string -> unit

(*s command-line options *)

val parse_only : bool
val type_only : bool
val print_graph : bool
val debug : bool
val verbose : bool
val werror : bool
val why_opt : string

val verify_all_offsets : bool
val verify_invariants_only : bool
val verify : string list
val behavior : string

val interprocedural : bool
val main : string

val files : unit -> string list 
val usage : unit -> unit

val inv_sem: Jc_env.inv_sem ref
val separation_sem : Jc_env.separation_sem ref
val annotation_sem : Jc_env.annotation_sem ref
val ai_domain : Jc_env.abstract_domain ref
val int_model : Jc_env.int_model ref
val float_model : Jc_env.float_model ref
val float_instruction_set : Jc_env.float_instruction_set ref
val trust_ai : bool
val fast_ai : bool

val gen_frame_rule_with_ft : bool

val current_rounding_mode : Jc_env.float_rounding_mode ref

val verify_behavior: string -> bool

val set_int_model: int_model -> unit

val set_float_model: float_model -> unit

(*s The log file *)

val log : Format.formatter
val lprintf : ('a, Format.formatter, unit) format -> 'a
val close_log : unit -> unit

(*s error handling *)

exception Jc_error of Loc.position * string

val jc_error : Loc.position -> ('a, unit, string, 'b) format4 -> 'a

val parsing_error : Loc.position -> ('a, unit, string, 'b) format4 -> 'a

val pos_table : 
  (string, (string * int * int * int * Output.kind option * (string * Rc.rc_value) list)) 
     Hashtbl.t

val position_of_label: string -> Loc.position option

(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
