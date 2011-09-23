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



(*s environment variables *)

val libdir : string
val whylib : string
val libfile : string (* depends on the command-line option --arith-mem *)

(*s command-line options *)

val zones : bool
val show_time : bool
val no_zone_type : bool
val parse_only : bool
val type_only : bool
val print_norm : bool
val print_graph : bool
val debug : bool
val verbose : bool
val werror : bool
val with_cpp : bool
val cpp_command : string
val cpp_dump : bool
val why_opt : unit -> string
val coq_tactic : string
val separate : bool
val closed_program : bool
val local_aliasing : bool
val no_alloc_table : bool
val arith_memory_model : bool
val abstract_interp : bool
val gen_invariant : bool
val absint_as_proof : bool

val use_floats : bool ref
val floats : bool
type fp_rounding_mode = 
  | RM_nearest_even | RM_to_zero | RM_up | RM_down | RM_nearest_away 
  | RM_dynamic
val fp_rounding_mode : fp_rounding_mode ref
val dft_fp_rounding_mode : fp_rounding_mode
val fp_overflow_check : bool

type int_model = IMexact | IMbounded | IMmodulo
val int_model : int_model
val machine_ints : bool

val enum_check : bool

val char_size : int
val short_size : int
val int_size : int
val long_size : int
val long_long_size : int

val files : unit -> string list 

val verify : string -> bool

(*s The log file *)

val log : Format.formatter
val lprintf : ('a, Format.formatter, unit) format -> 'a
val close_log : unit -> unit

type evaluation_order_t =
    { binary_left_to_right : bool;
      assign_left_to_right : bool;
      call_left_to_right : bool }

val evaluation_order : evaluation_order_t
