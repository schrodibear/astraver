
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: wp.mli,v 1.1 2001-08-17 00:55:48 filliatr Exp $ *)

open Logic
open Env

val update_post : local_env -> string -> Effect.t -> predicate -> predicate

val propagate : Rename.t -> typed_program -> typed_program
