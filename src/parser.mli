(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: parser.mli,v 1.3 2001-08-24 19:07:17 filliatr Exp $ i*)

(* Grammar for the programs *)

open Types
open Ast

val program : parsed_program Grammar.Entry.e
val type_v  : type_v Grammar.Entry.e
val type_c  : type_c Grammar.Entry.e

val decls : (decl list) Grammar.Entry.e

