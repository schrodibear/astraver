(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: typing.mli,v 1.8 2002-07-05 16:14:09 filliatr Exp $ i*)

(*s This module realizes type and effect inference *)

open Logic
open Types
open Ast
open Env

val typef : LabelSet.t -> local_env -> parsed_program -> typed_program

