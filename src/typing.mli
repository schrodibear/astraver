(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: typing.mli,v 1.7 2002-03-13 10:01:37 filliatr Exp $ i*)

(*s This module realizes type and effect inference *)

open Logic
open Types
open Ast
open Env

module LabelSet : Set.S with type elt = string

val initial_labels : LabelSet.t

val check_type_v : Loc.t option -> LabelSet.t -> local_env -> type_v -> unit

val typef : LabelSet.t -> local_env -> parsed_program -> typed_program

