
(* $Id *)

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

val files : unit -> string list 
val usage : unit -> unit

(*s The log file *)

val log : Format.formatter
val lprintf : ('a, Format.formatter, unit) format -> 'a
val close_log : unit -> unit

(*s error handling *)

exception Jc_error of Loc.position * string

val parsing_error : Loc.position -> ('a, unit, string, 'b) format4 -> 'a


