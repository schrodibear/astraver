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

(*
val logic_type_table : (string,string) Hashtbl.t
  
val logic_functions_table : 
  (int, logic_info * term_or_assertion) Hashtbl.t
*)

val functions_table : 
  (int, fun_info * fun_spec * statement list option) Hashtbl.t

val variables_table : 
  (int, var_info * expr option) Hashtbl.t

(*
val structs_table : 
  (string, struct_info * (logic_info * assertion) list) Hashtbl.t
*)

(*
val enum_types_table : 
  (string, enum_info) Hashtbl.t
*)

(*
val axioms_table : 
  (string, assertion) Hashtbl.t
*)

(*
val exceptions_table : 
  (string, exception_info) Hashtbl.t
*)

val code_function : fun_info * fun_spec * tstatement list option -> var_info list
  -> fun_spec * statement list option

val static_variables : (int, Jc_env.var_info * Jc_ast.texpr option) Hashtbl.t -> var_info list


val make_int_binary : Loc.position -> expr -> bin_op -> expr -> expr

val one_const : Loc.position -> expr


(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
