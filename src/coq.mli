(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: coq.mli,v 1.8 2002-09-06 11:56:52 filliatr Exp $ i*)

open Cc
open Format
open Vcg

val reset : unit -> unit

val push_obligations : obligation list -> unit

val push_validation : string -> validation -> unit

val push_parameter : string -> cc_type -> unit

val push_exception : string -> cc_type option -> unit

val output_file : string -> unit

