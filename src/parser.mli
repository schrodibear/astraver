
(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(* $Id: parser.mli,v 1.1 2001-08-15 21:08:52 filliatr Exp $ *)

(* Grammar for the programs *)

open Types
open Ast

val program : parsed_program Grammar.Entry.e
val type_v  : type_v Grammar.Entry.e
val type_c  : type_c Grammar.Entry.e

