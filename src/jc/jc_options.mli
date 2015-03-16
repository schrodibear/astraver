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

open Stdlib
open Env

(* environment variables *)

val has_floats : bool ref
val libdir : string
val get_libfiles : unit -> string list
val add_to_libfiles : string -> unit

(* command-line options *)

val parse_only : bool
val type_only : bool
val print_graph : bool
val debug : bool
val verbose : bool
val werror : bool
val why_opt : string
val why3_opt : string

val verify_all_offsets : bool
val verify_invariants_only : bool
val verify : string list
val behavior : string list

val interprocedural : bool
val main : string

val files : unit -> string list
val usage : unit -> unit

val inv_sem: Env.inv_sem ref
val separation_sem : Env.separation_sem ref
val annotation_sem : Env.annotation_sem ref
val termination_policy : Env.termination_policy ref
val ai_domain : Env.abstract_domain ref
val int_model : Env.int_model ref
val float_model : Env.float_model ref
val float_instruction_set : Env.float_instruction_set ref
val trust_ai : bool
val fast_ai : bool
val forall_inst_bound: int

val gen_frame_rule_with_ft : bool

val current_rounding_mode : Env.float_rounding_mode ref

val verify_behavior: string -> bool

val set_int_model: int_model -> unit

val set_float_model: float_model -> unit

(* The log file *)

val log : Format.formatter
val lprintf : ('a, Format.formatter, unit) format -> 'a
val close_log : unit -> unit

(* error handling *)

exception Error of Why_loc.position * string

val jc_error : Why_loc.position -> ('a, unit, string, 'b) format4 -> 'a
val jc_warning : Why_loc.position -> ('a, Format.formatter, unit, unit) format4 -> 'a

val parsing_error : Why_loc.position -> ('a, unit, string, 'b) format4 -> 'a

val pos_table :
  (string, (string * int * int * int * Output_ast.vc_kind option * (string * Why_rc.rc_value) list))
     Hashtbl.t

val position_of_label: string -> Why_loc.position option

(*
  Local Variables:
  compile-command: "ocamlc -c -bin-annot -I . -I ../src jc_options.mli"
  End:
*)
