(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: coq.mli,v 1.4 2002-03-20 16:01:44 filliatr Exp $ i*)

open Format
open Vcg

val reset : unit -> unit

val push_obligations : string -> obligation list * validation -> unit

val output_file : string -> unit

