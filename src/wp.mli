
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: wp.mli,v 1.2 2001-08-21 20:57:02 filliatr Exp $ *)

open Logic
open Env

val update_post : local_env -> string -> Effect.t -> predicate -> predicate

val propagate : Rename.t -> typed_program -> typed_program

