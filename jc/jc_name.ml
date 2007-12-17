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

(* $Id: jc_name.ml,v 1.1 2007-12-17 14:18:55 moy Exp $ *)

open Jc_env
open Jc_ast
open Jc_region

let tag_name st = st.jc_struct_info_name ^ "_tag"

let alloc_table_name st = st.jc_struct_info_root ^ "_alloc_table"
let tag_table_name st = st.jc_struct_info_root ^ "_tag_table"
let field_region_memory_name (fi,r) = 
  if !Jc_common_options.separation then 
    let fi,r = FieldRegion.repr (fi,r) in
    fi.jc_field_info_final_name ^ "_" ^ r.jc_reg_final_name
  else fi.jc_field_info_final_name
let field_memory_name fi = fi.jc_field_info_final_name

let valid_pred_name st = "valid_" ^ st.jc_struct_info_name
let valid_one_pred_name st = "valid_one_" ^ st.jc_struct_info_name
let alloc_param_name st = "alloc_" ^ st.jc_struct_info_name
let alloc_one_param_name st = "alloc_one_" ^ st.jc_struct_info_name

(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
