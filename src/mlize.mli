(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: mlize.mli,v 1.5 2002-09-06 11:56:52 filliatr Exp $ i*)

open Ast
open Cc
open Env
open Logic

(* translation of imperative programs into intermediate functional programs *)

val trans : typed_program -> Rename.t -> predicate cc_term

