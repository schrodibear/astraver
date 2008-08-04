(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*  Copyright (C) 2002-2008                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
(*    Yann RÉGIS-GIANAS                                                   *)
(*    Nicolas ROUSSET                                                     *)
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

(* $Id: jc_name.ml,v 1.20 2008-08-04 13:48:33 moy Exp $ *)

open Jc_env
open Jc_ast
open Jc_region
open Jc_pervasives
open Output

let alloc_table_type_name = "alloc_table"
let tag_table_type_name = "tag_table"
let pointer_type_name = "pointer"
let pset_type_name = "pset"
let memory_type_name = "memory"
let tag_id_type_name = "tag_id"
let bitvector_type_name = "bitvector"

let simple_logic_type s =
  { logic_type_name = s; logic_type_args = [] }

let variant_type_name vi = vi.jc_variant_info_name

let struct_type_name st = variant_type_name (struct_variant st)

let pointer_class_type_name = function
  | JCtag(st, _) -> struct_type_name st
  | JCvariant vi -> variant_type_name vi
  | JCunion vi -> variant_type_name vi

let alloc_class_name = function
  | JCalloc_struct vi -> variant_type_name vi
  | JCalloc_union vi -> variant_type_name vi
  | JCalloc_bitvector -> bitvector_type_name

let variant_alloc_table_name vi = vi.jc_variant_info_name ^ "_alloc_table"

let variant_tag_table_name vi = vi.jc_variant_info_name ^ "_tag_table"

let variant_axiom_on_tags_name vi = vi.jc_variant_info_name ^ "_tags"

let axiom_int_of_tag_name st = st.jc_struct_info_name ^ "_int"

let tag_name st = st.jc_struct_info_name ^ "_tag"

let tag_table_name_vi vi =
  (variant_type_name vi) ^ "_tag_table"

let tag_table_name = function
  | JCtag(st, _) -> tag_table_name_vi (struct_variant st)
  | JCvariant vi | JCunion vi -> tag_table_name_vi vi

(* let alloc_table_name pc = *)
(*   (pointer_class_type_name pc) ^ "_alloc_table" *)

let generic_alloc_table_name ac =
  (alloc_class_name ac) ^ "_alloc_table"

let alloc_region_table_name (ac,r) = 
  if !Jc_common_options.separation_sem = SepRegions then 
    (alloc_class_name ac) ^ "_" ^ (Region.name r) ^ "_alloc_table"
  else
    (alloc_class_name ac) ^ "_alloc_table"

let field_memory_name fi = 
  if field_of_union fi then
    (union_of_field fi).jc_variant_info_name ^ "_fields"
  else
    fi.jc_field_info_final_name

let field_region_memory_name (fi,r) = 
  if !Jc_common_options.separation_sem = SepRegions then 
    (field_memory_name fi) ^ "_" ^ (Region.name r)
  else field_memory_name fi

let union_memory_name vi =
  vi.jc_variant_info_name ^ "_fields"

let union_region_memory_name (vi,r) = 
  if !Jc_common_options.separation_sem = SepRegions then 
    (union_memory_name vi) ^ "_" ^ (Region.name r)
  else union_memory_name vi

let bitvector_region_memory_name r = 
  if !Jc_common_options.separation_sem = SepRegions then 
    bitvector_type_name ^ "_" ^ (Region.name r)
  else bitvector_type_name

let union_memory_type_name vi = 
  vi.jc_variant_info_name ^ "_union"

let memory_name (mc,r) =
  match mc with
    | JCmem_field fi -> field_region_memory_name (fi,r)
    | JCmem_union vi -> union_region_memory_name (vi,r)
    | JCmem_bitvector -> bitvector_region_memory_name r

let valid_pred_name = function
  | JCtag(st, _) -> "valid_struct_" ^ st.jc_struct_info_name
  | JCvariant vi -> "valid_variant_" ^ vi.jc_variant_info_name
  | JCunion vi -> "valid_union_" ^ vi.jc_variant_info_name
(*
let valid_one_pred_name = function
  | JCtag st -> "valid_one_" ^ st.jc_struct_info_name
  | JCvariant vi -> "valid_one_" ^ vi.jc_variant_info_name
*)
let alloc_param_name st = "alloc_" ^ st.jc_struct_info_name

let alloc_one_param_name st = "alloc_one_" ^ st.jc_struct_info_name

let jessie_return_variable = "return"
let jessie_return_exception = "Return"

let exception_name ei =
  ei.jc_exception_info_name ^ "_exc"

let mutable_name pc =
  "mutable_"^(pointer_class_type_name pc)

let committed_name pc =
  "committed_"^(pointer_class_type_name pc)

let fully_packed_name st =
  "fully_packed_"^(root_name st)

let hierarchy_invariant_name st =
  "global_invariant_"^(root_name st)

let pack_name st =
  "pack_"^(root_name st)

let unpack_name st =
  "unpack_"^(root_name st)

let fully_packed_name = "fully_packed"

(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
