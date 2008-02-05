(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann R�GIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
(*    Xavier URBAIN                                                       *)
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

(* $Id: jc_options.mli,v 1.21 2008-02-05 20:24:05 nrousset Exp $ *)

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

val interprocedural : bool
val main : string

val files : unit -> string list 
val usage : unit -> unit

val inv_sem: Jc_env.inv_sem ref
val separation_sem : Jc_env.separation_sem ref
val annotation_sem : Jc_env.annotation_sem ref
val ai_domain : Jc_env.abstract_domain ref
val trust_ai : bool

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
