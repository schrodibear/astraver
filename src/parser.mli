(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: parser.mli,v 1.4 2002-07-05 16:14:09 filliatr Exp $ i*)

(* Grammar for the programs *)

open Types
open Ast

val program : parsed_program Grammar.Entry.e
val type_v  : parsed_type_v Grammar.Entry.e
val type_c  : parsed_type_c Grammar.Entry.e

val decls : (decl list) Grammar.Entry.e

