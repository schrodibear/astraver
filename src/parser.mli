(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: parser.mli,v 1.5 2002-07-08 09:02:28 filliatr Exp $ i*)

(* Grammar for the programs *)

open Types
open Ptree
open Ast

val program : parsed_program Grammar.Entry.e
val type_v  : ptype_v Grammar.Entry.e
val type_c  : ptype_c Grammar.Entry.e

val decls : (decl list) Grammar.Entry.e

