(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: coq.mli,v 1.6 2002-03-26 13:43:41 filliatr Exp $ i*)

open Format
open Vcg

val reset : unit -> unit

val push_obligations : obligation list -> unit

val push_validation : string -> validation -> unit

val push_parameter : string -> Ast.cc_type -> unit

val output_file : string -> unit

