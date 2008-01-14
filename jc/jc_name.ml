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

(* $Id: jc_name.ml,v 1.4 2008-01-14 15:26:30 bardou Exp $ *)

open Jc_env
open Jc_ast
open Jc_region
open Jc_pervasives
open Output

let alloc_table_type_name = "alloc_table"
let tag_table_type_name = "tag_table"
let pointer_type_name = "pointer"
let memory_type_name = "memory"
let tag_id_type_name = "tag_id"

let simple_logic_type s =
  { logic_type_name = s; logic_type_args = [] }

let variant_type_name vi = vi.jc_variant_info_name

let struct_type_name st = variant_type_name (struct_variant st)

(* Why type which modelises a variant. *)
let variant_model_type vi =
  simple_logic_type (variant_type_name vi)

(* Why type which modelises a structure "root". *)
let struct_model_type st = variant_model_type (struct_variant st)

let variant_alloc_table_name vi = vi.jc_variant_info_name ^ "_alloc_table"

let variant_tag_table_name vi = vi.jc_variant_info_name ^ "_tag_table"

let tag_name st = st.jc_struct_info_name ^ "_tag"

let tag_table_name st =
  (struct_type_name st) ^ "_tag_table"

let alloc_table_name st =
  (struct_type_name st) ^ "_alloc_table"

let alloc_region_table_name (a, r) = 
  if !Jc_common_options.separation then 
    (root_name a) ^ "_" ^ (Region.name r) ^ "_alloc_table"
  else alloc_table_name a

let field_memory_name fi = fi.jc_field_info_final_name

let field_region_memory_name (fi,r) = 
  if !Jc_common_options.separation then 
    fi.jc_field_info_final_name ^ "_" ^ (Region.name r)
  else field_memory_name fi

let valid_pred_name st = "valid_" ^ st.jc_struct_info_name

let valid_one_pred_name st = "valid_one_" ^ st.jc_struct_info_name

let alloc_param_name st = "alloc_" ^ st.jc_struct_info_name

let alloc_one_param_name st = "alloc_one_" ^ st.jc_struct_info_name

let jessie_return_variable = "jessie_returned_value"
let jessie_return_exception = "Return"

let exception_name ei =
  ei.jc_exception_info_name ^ "_exc"

let mutable_name st =
  "mutable_"^(root_name st)

let committed_name st =
  "committed_"^(root_name st)

let fully_packed_name st =
  "fully_packed_"^(root_name st)

let hierarchy_invariant_name st =
  "global_invariant_"^(root_name st)

let pack_name st =
  "pack_"^(root_name st)

let unpack_name st =
  "unpack_"^(root_name st)

(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
