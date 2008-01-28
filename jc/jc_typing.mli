(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2007                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Xavier URBAIN                                                       *)
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

val is_root_struct : struct_info -> bool

val substruct : struct_info -> struct_info -> bool

val logic_type_table : (string,string) Hashtbl.t
  

val logic_constants_table : 
  (int, var_info * term option) Hashtbl.t

val logic_functions_table : 
  (int, logic_info * term_or_assertion) Hashtbl.t

val functions_table : 
  (int, fun_info * Loc.position * fun_spec * tstatement list option) Hashtbl.t

val variables_table : 
  (int, var_info * texpr option) Hashtbl.t

val structs_table : 
  (string, (struct_info * (logic_info * assertion) list)) Hashtbl.t

val variants_table :
  (string, variant_info) Hashtbl.t

val enum_types_table : 
  (string, (enum_info (* * logic_info * fun_info * fun_info *))) Hashtbl.t

(*
val enum_conversion_functions_table : (fun_info, string) Hashtbl.t
val enum_conversion_logic_functions_table : (logic_info, string) Hashtbl.t
*)

val axioms_table : 
  (string, bool * logic_label list * assertion) Hashtbl.t

val global_invariants_table : 
  (logic_info, assertion) Hashtbl.t

val exceptions_table : 
  (string, exception_info) Hashtbl.t

exception Typing_error of Loc.position * string

val coerce : jc_type -> native_type -> texpr -> texpr

val type_range_of_term : jc_type -> term -> assertion

val find_struct_variant : Jc_env.struct_info -> Jc_env.variant_info

val type_file : pdecl list -> unit

(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
