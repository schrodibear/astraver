
open Format
open Vcg

val print_obligations : formatter -> obligation list -> unit

val begin_theory : formatter -> string -> unit
val end_theory : formatter -> unit


