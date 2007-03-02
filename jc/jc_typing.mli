(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU General Public                   *)
(*  License version 2, as published by the Free Software Foundation.      *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(*  See the GNU General Public License version 2 for more details         *)
(*  (enclosed in the file GPL).                                           *)
(*                                                                        *)
(**************************************************************************)

open Jc_env
open Jc_fenv
open Jc_ast

val typing_error : 
    Loc.position -> ('a, Format.formatter, unit, 'b) format4 -> 'a

val logic_type_table : (string,string) Hashtbl.t
  
val logic_functions_table : 
  (int, logic_info * tterm_or_tassertion) Hashtbl.t

val functions_table : 
  (int, fun_info * tfun_spec * tstatement list) Hashtbl.t

val structs_table : 
  (string, (struct_info * (logic_info * tassertion) list)) Hashtbl.t

val range_types_table : 
  (string, (range_info * logic_info * fun_info * fun_info)) Hashtbl.t

val axioms_table : 
  (string, tassertion) Hashtbl.t

val exceptions_table : 
  (string, exception_info) Hashtbl.t

exception Typing_error of Loc.position * string

val decl : pdecl -> unit

(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
