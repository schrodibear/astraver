(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: mlize.mli,v 1.4 2002-03-20 16:01:44 filliatr Exp $ i*)

open Ast
open Env
open Logic

(* translation of imperative programs into intermediate functional programs *)

val trans : typed_program -> Rename.t -> predicate cc_term

