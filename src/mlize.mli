(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: mlize.mli,v 1.3 2002-03-12 16:05:25 filliatr Exp $ i*)

open Ast
open Env

(* translation of imperative programs into intermediate functional programs *)

val trans : typed_program -> Rename.t -> cc_term

