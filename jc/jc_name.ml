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

(* $Id: jc_name.ml,v 1.3 2008-01-11 12:43:45 marche Exp $ *)

open Jc_env
open Jc_ast
open Jc_region
open Output

let simple_logic_type s =
  { logic_type_name = s; logic_type_args = [] }

let tr_native_type t =
  match t with
    | Tunit -> "unit"
    | Tboolean -> "bool"
    | Tinteger -> "int"
    | Treal -> "real"

let tr_base_type t =
  match t with
    | JCTnative t -> simple_logic_type (tr_native_type t)
    | JCTlogic s -> simple_logic_type s
    | JCTenum ri -> 
	simple_logic_type ri.jc_enum_info_name
    | JCTpointer (st, a, b) -> 
	let ti = simple_logic_type (st.jc_struct_info_root) in
	{ logic_type_name = "pointer";
	  logic_type_args = [ ti ] }
    | JCTnull -> assert false


let tag_name st = st.jc_struct_info_name ^ "_tag"

let alloc_table_name a = a ^ "_alloc_table"

let alloc_table_type a = 
  {
    logic_type_name = "alloc_table";
    logic_type_args = [simple_logic_type a];
  }

let alloc_region_table_name (a,r) = 
  if !Jc_common_options.separation then 
    a ^ "_" ^ (Region.name r) ^ "_alloc_table"
  else alloc_table_name a

let tag_table_name st = st.jc_struct_info_root ^ "_tag_table"

let field_memory_name fi = fi.jc_field_info_final_name

let field_region_memory_name (fi,r) = 
  if !Jc_common_options.separation then 
    fi.jc_field_info_final_name ^ "_" ^ (Region.name r)
  else field_memory_name fi

let memory_type t v =
  { logic_type_name = "memory";
    logic_type_args = [t;v] }

let memory_field fi =
  memory_type 
    (simple_logic_type fi.jc_field_info_root)
    (tr_base_type fi.jc_field_info_type)


let valid_pred_name st = "valid_" ^ st.jc_struct_info_name

let valid_one_pred_name st = "valid_one_" ^ st.jc_struct_info_name

let alloc_param_name st = "alloc_" ^ st.jc_struct_info_name

let alloc_one_param_name st = "alloc_one_" ^ st.jc_struct_info_name

(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
