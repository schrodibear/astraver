(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: coq.mli,v 1.1 2002-01-24 15:59:30 filliatr Exp $ i*)

open Format
open Vcg

val out_file : string -> string

val print_obligations : formatter -> obligation list -> unit

