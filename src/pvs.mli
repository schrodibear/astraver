
(*i $Id: pvs.mli,v 1.3 2001-08-24 19:07:17 filliatr Exp $ i*)

open Format
open Vcg

val print_obligations : formatter -> obligation list -> unit

val begin_theory : formatter -> string -> unit
val end_theory : formatter -> string -> unit


