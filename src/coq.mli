(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: coq.mli,v 1.7 2002-07-04 08:58:13 filliatr Exp $ i*)

open Ast
open Format
open Vcg

val reset : unit -> unit

val push_obligations : obligation list -> unit

val push_validation : string -> validation -> unit

val push_parameter : string -> cc_type -> unit

val push_exception : string -> cc_type option -> unit

val output_file : string -> unit

