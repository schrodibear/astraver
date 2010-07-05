(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2010                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS                                     *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*    Thierry HUBERT, Univ. Paris-sud 11                                  *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Jc_stdlib
open Jc_env
open Jc_ast
open Jc_fenv

val default_label : label list -> label option
 
val typing_error : 
    Loc.position -> ('a, Format.formatter, unit, 'b) format4 -> 'a

val is_root_struct : struct_info -> bool

val substruct : struct_info -> pointer_class -> bool

val logic_type_table : (string,string * type_var_info list) Hashtbl.t
  

val logic_constants_table : 
  (int, logic_info * Jc_fenv.logic_info Jc_ast.term) Hashtbl.t

val logic_functions_table : 
  (int, logic_info * term_or_assertion) Hashtbl.t

val functions_table : 
  (int, fun_info * Loc.position * fun_spec * expr option) Hashtbl.t

val variables_table : 
  (int, var_info * expr option) Hashtbl.t

val structs_table : 
  (string, (struct_info * (logic_info * assertion) list)) Hashtbl.t

val roots_table :
  (string, root_info) Hashtbl.t

val enum_types_table : 
  (string, (enum_info (* * logic_info * fun_info * fun_info *))) Hashtbl.t

(*
val enum_conversion_functions_table : (fun_info, string) Hashtbl.t
val enum_conversion_logic_functions_table : (logic_info, string) Hashtbl.t
*)

val lemmas_table : 
  (string, Loc.position * bool * type_var_info list * label list * assertion) Hashtbl.t

type axiomatic_decl =
  | ABaxiom of Loc.position * string * Jc_env.label list * Jc_constructors.assertion

type axiomatic_data = private
    {
      mutable axiomatics_defined_ids : logic_info list;
      mutable axiomatics_decls : axiomatic_decl list;
    }

val axiomatics_table : (string, axiomatic_data) Hashtbl.t

val global_invariants_table : 
  (logic_info, assertion) Hashtbl.t

val exceptions_table : 
  (string, exception_info) Hashtbl.t

exception Typing_error of Loc.position * string

val coerce : jc_type -> native_type -> expr -> expr

val type_range_of_term : jc_type -> term -> assertion

val find_struct_root : Jc_env.struct_info -> Jc_env.root_info

val type_file : nexpr decl list -> unit

val print_file : Format.formatter -> unit -> unit

val type_labels_in_decl : nexpr decl -> unit

val pragma_gen_sep :  (int,
   [ `Sep | `Inc | `Cni] *
   [ `Logic of Jc_fenv.logic_info * string list * Jc_env.var_info list
   | `Pointer of Jc_env.var_info ] list) Jc_stdlib.Hashtbl.t

val pragma_gen_frame : 
  (int, Jc_fenv.logic_info * Jc_fenv.logic_info) Jc_stdlib.Hashtbl.t

val comparable_types : jc_type -> jc_type -> bool

(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
