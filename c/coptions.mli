(*
 * The Caduceus certification tool
 * Copyright (C) 2003 Jean-Christophe Filliâtre - Claude Marché
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(*i $Id: coptions.mli,v 1.19 2006-06-22 14:20:22 filliatr Exp $ i*)

(*s environment variables *)

val libdir : string
val whylib : string

(*s command-line options *)

val zones : bool
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

val use_floats : bool ref
val floats : bool
type fp_rounding_mode = 
  | RM_nearest_even | RM_to_zero | RM_up | RM_down | RM_nearest_away 
  | RM_dynamic
val fp_rounding_mode : fp_rounding_mode ref
val fp_overflow_check : bool

val int_overflow_check : bool

val min_signed_char : string
val max_signed_char : string
val max_unsigned_char : string
val min_signed_short : string
val max_signed_short : string
val max_unsigned_short : string
val min_signed_int : string
val max_signed_int : string
val max_unsigned_int : string
val min_signed_long : string
val max_signed_long : string
val max_unsigned_long : string
val min_signed_longlong : string
val max_signed_longlong : string
val max_unsigned_longlong : string

val files : unit -> string list 

val verify : string -> bool

(*s The log file *)

val log : Format.formatter
val lprintf : ('a, Format.formatter, unit) format -> 'a
val close_log : unit -> unit

