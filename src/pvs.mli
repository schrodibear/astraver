
(*i $Id: pvs.mli,v 1.5 2002-01-31 12:44:35 filliatr Exp $ i*)

open Format
open Vcg

val reset : unit -> unit

val push_verbatim : string -> unit

val push_obligations : obligation list -> unit

val output_file : string -> unit

(*i
val print_obligations : formatter -> obligation list -> unit

val begin_theory : formatter -> string -> unit
val end_theory : formatter -> string -> unit

val out_file : string -> string
i*)
