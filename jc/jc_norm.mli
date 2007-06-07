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

val logic_type_table : (string,string) Hashtbl.t
  
val logic_functions_table : 
  (int, logic_info * term_or_assertion) Hashtbl.t

val functions_table : 
  (int, fun_info * fun_spec * statement list) Hashtbl.t

val variables_table : 
  (int, var_info * expr) Hashtbl.t

val structs_table : 
  (string, (struct_info * (logic_info * assertion) list)) Hashtbl.t

val enum_types_table : 
  (string, (enum_info * logic_info * fun_info * fun_info)) Hashtbl.t

val axioms_table : 
  (string, assertion) Hashtbl.t

val exceptions_table : 
  (string, exception_info) Hashtbl.t

val logic_function : tterm_or_tassertion -> term_or_assertion

val code_function : tfun_spec * tstatement list -> fun_spec * statement list

val static_variable : var_info * texpr -> var_info * expr

val assertion : tassertion -> assertion

(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
