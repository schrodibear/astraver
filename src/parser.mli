(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(*i $Id: parser.mli,v 1.13 2003-03-26 07:10:18 filliatr Exp $ i*)

(* Grammar for the programs *)

open Types
open Ptree

val program : parsed_program Grammar.Entry.e
val type_v  : ptype_v Grammar.Entry.e
val type_c  : ptype_c Grammar.Entry.e

val decls : (decl list) Grammar.Entry.e

(* Entries for the C parser *)

type 'a c_parser = int -> string -> 'a

val parse_c_spec : (lexpr asst list * Effect.t * lexpr post option) c_parser
val parse_c_pre : (lexpr asst option * variant option) c_parser
val parse_c_post : (lexpr post option) c_parser
val parse_c_loop_annot : (lexpr asst * variant) c_parser
val parse_c_decl : decl c_parser
val parse_c_assert : lexpr asst c_parser

