(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: typing.mli,v 1.9 2002-07-08 09:02:28 filliatr Exp $ i*)

(*s This module realizes type and effect inference *)

open Logic
open Types
open Ptree
open Ast
open Env

val typef : LabelSet.t -> local_env -> parsed_program -> typed_program

