(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: coq.mli,v 1.2 2002-01-31 12:44:35 filliatr Exp $ i*)

open Format
open Vcg

val reset : unit -> unit

val push_verbatim : string -> unit

val push_obligations : obligation list -> unit

val output_file : string -> unit

(*i
val out_file : string -> string

val print_obligations : formatter -> obligation list -> unit
i*)
