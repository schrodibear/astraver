(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: mlize.mli,v 1.2 2001-08-24 19:07:17 filliatr Exp $ i*)

open Ast
open Env

(* translation of imperative programs into intermediate functional programs *)

val trans : Rename.t -> typed_program -> cc_term

