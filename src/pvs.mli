
(*i $Id: pvs.mli,v 1.4 2002-01-24 15:59:30 filliatr Exp $ i*)

open Format
open Vcg

val print_obligations : formatter -> obligation list -> unit

val begin_theory : formatter -> string -> unit
val end_theory : formatter -> string -> unit

val out_file : string -> string
