(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: parser.mli,v 1.6 2002-07-29 13:38:38 filliatr Exp $ i*)

(* Grammar for the programs *)

open Types
open Ptree
open Ast

val program : parsed_program Grammar.Entry.e
val type_v  : ptype_v Grammar.Entry.e
val type_c  : ptype_c Grammar.Entry.e

val decls : (decl list) Grammar.Entry.e

(* Entries for the C parser *)

val c_spec : (lexpr pre list * Effect.t * lexpr post option) Grammar.Entry.e
