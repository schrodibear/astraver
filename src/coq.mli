(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: coq.mli,v 1.9 2002-10-09 16:43:06 filliatr Exp $ i*)

open Cc
open Format
open Vcg

val reset : unit -> unit

val push_obligations : obligation list -> unit

val push_validation : string -> validation -> unit

val push_parameter : string -> cc_type -> unit

val output_file : string -> unit

