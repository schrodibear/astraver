
(*i $Id: pvs.mli,v 1.7 2002-03-26 13:43:41 filliatr Exp $ i*)

open Format
open Vcg

val reset : unit -> unit

val push_verbatim : string -> unit

val push_obligations : obligation list -> unit

val push_parameter : string -> Ast.cc_type -> unit

val output_file : string -> unit
