
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: parser.mli,v 1.2 2001-08-17 00:52:38 filliatr Exp $ *)

(* Grammar for the programs *)

open Types
open Ast

val program : parsed_program Grammar.Entry.e
val type_v  : type_v Grammar.Entry.e
val type_c  : type_c Grammar.Entry.e

val decls : (decl list) Grammar.Entry.e

