
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: mlize.mli,v 1.1 2001-08-17 00:55:48 filliatr Exp $ *)

open Ast
open Env

(* translation of imperative programs into intermediate functional programs *)

val trans : Rename.t -> typed_program -> cc_term

