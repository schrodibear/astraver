
(*i $Id: pvs.mli,v 1.6 2002-01-31 22:48:02 filliatr Exp $ i*)

open Format
open Vcg

val reset : unit -> unit

val push_verbatim : string -> unit

val push_obligations : obligation list -> unit

val output_file : string -> unit
