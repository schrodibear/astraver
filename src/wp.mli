(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: wp.mli,v 1.3 2001-08-24 19:07:17 filliatr Exp $ i*)

open Logic
open Env

val update_post : local_env -> string -> Effect.t -> predicate -> predicate

val propagate : Rename.t -> typed_program -> typed_program

