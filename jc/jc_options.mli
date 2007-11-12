(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Nicolas ROUSSET                                                     *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

(* $Id: jc_options.mli,v 1.14 2007-11-12 16:10:48 nrousset Exp $ *)

(*s environment variables *)

val libdir : string
val libfile : string

(*s command-line options *)

val parse_only : bool
val type_only : bool
val print_graph : bool
val debug : bool
val verbose : bool
val werror : bool
val why_opt : string

val verify : string list

val annot_infer : bool
val ai_domain : string
val interprocedural : bool
val main : string

val files : unit -> string list 
val usage : unit -> unit

val inv_sem: Jc_env.inv_sem

(*s The log file *)

val log : Format.formatter
val lprintf : ('a, Format.formatter, unit) format -> 'a
val close_log : unit -> unit

(*s error handling *)

exception Jc_error of Loc.position * string

val parsing_error : Loc.position -> ('a, unit, string, 'b) format4 -> 'a

val locs_table : 
  (string, (string * int * int * int * (string * Rc.rc_value) list)) 
     Hashtbl.t


(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
