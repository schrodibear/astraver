
(*i $Id: pvs.mli,v 1.8 2002-09-06 11:56:52 filliatr Exp $ i*)

open Format
open Vcg

val reset : unit -> unit

val push_verbatim : string -> unit

val push_obligations : obligation list -> unit

val push_parameter : string -> Cc.cc_type -> unit

val output_file : string -> unit
