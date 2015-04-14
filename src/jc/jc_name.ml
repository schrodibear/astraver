(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
(*                                                                        *)
(*  Jessie2 fork:                                                         *)
(*    Mikhail MANDRYKIN, ISP RAS       (adaptation for Linux sources)     *)
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

open Env
open Ast
open Region
open Common
open Output_ast

let pointer_type_name = "pointer"
let pset_type_name = "pset"
let tag_id_type_name = "tag_id"

let old s = "old_" ^ s

module Type =
struct
  let root ri = ri.ri_name
  let struc st = root (struct_root st)
  let pointer_class =
    function
    | JCtag (st, _) -> struc st
    | JCroot vi -> root vi
  let bitvector = "bitvector"
  let memory = "memory"
  let alloc_table = "alloc_table"
  let tag_table = "tag_table"
end

module Class =
struct
  let pointer =
    function
    | JCtag (st, _) when struct_of_union st -> "root_" ^ (struct_root st).ri_name
    | JCtag (st, _) -> "struct_" ^ st.si_name
    | JCroot vi -> "root_" ^ vi.ri_name

  let alloc =
    function
    | JCalloc_root vi -> Type.root vi
    | JCalloc_bitvector -> Type.bitvector

  let memory =
    function
    | JCmem_field fi -> fi.fi_final_name
    | JCmem_plain_union vi -> Type.root vi
    | JCmem_bitvector -> Type.bitvector
end

let tag st = st.si_name ^ "_tag"

let tag_table (ri, r) =
  if !Common_options.separation_sem = SepRegions && not (is_dummy_region r)
  then
    (Type.root ri) ^ "_" ^ (Region.name r) ^ "_tag_table"
  else
    (Type.root ri) ^ "_tag_table"

let alloc_table (ac, r) =
  if !Common_options.separation_sem = SepRegions && not (is_dummy_region r)
  then
    (Class.alloc ac) ^ "_" ^ (Region.name r) ^ "_alloc_table"
  else
    (Class.alloc ac) ^ "_alloc_table"

module Generic =
struct
  let tag_table ri =  (Type.root ri) ^ "_tag_table"
  let alloc_table ac = (Class.alloc ac) ^ "_alloc_table"
  let memory mc = Class.memory mc
end

module Axiom =
struct
  let int_of_tag st = st.si_name ^ "_int"
end

module Theory =
struct
  type t = string * bool
  let root ri = String.capitalize (Type.root ri) ^ "_root", false
  (* ATTENTION: this theory is non-existent, there is no more "obsolete" support for BV,
     the new implementation of BV in Why3 should become supported by Jessie2. *)
  let bitvector = "Bitvector", false
  let jessie = "jessie3theories.Jc_memory_model", false
  let bool = "bool.Bool", true
  let single = "jessie3theories.Single", true
  let double = "jessie3theories.Double", true
  let binary80 = "jessie3theories.Binary80", true
  let real = "real.Real", true
  let current = "", false
  let struct_ =
    function
    | JCtag (si, _) -> "Struct_" ^ si.si_name, true
    | JCroot ri -> "Root_" ^ ri.ri_name, true
end

module Module =
struct
  type t = string * bool
  let jessie = "Jessie3", false
  let struct_ ~safe si = (fst (Theory.struct_ si) ^ if safe then "safe" else "unsafe"), true
end

module Pred =
struct
  let valid ~equal ~left ~right ac pc =
    let prefix =
      match ac with
      | JCalloc_root _ ->
        if equal then
          "strict_valid"
        else
          begin match left, right with
          | false, false -> assert false
          | false, true -> "right_valid"
          | true, false -> "left_valid"
          | true, true -> "valid"
          end
      | JCalloc_bitvector -> "valid_bitvector" (* TODO ? *)
    in
    Theory.struct_ pc, prefix ^ "_" ^ (Class.pointer pc)

  let fresh ~for_ ac pc =
    let for_ =
      match for_ with
      | `alloc_tables -> "alloc"
      | `tag_tables -> "tag"
    in
    let prefix =
      match ac with
      | JCalloc_root _ -> "fresh_" ^ for_
      | JCalloc_bitvector -> "fresh_bitvector" (* TODO *)
    in
    Theory.struct_ pc, prefix ^ "_" ^ (Class.pointer pc)

  let instanceof ~exact
      (type t1) (type t2) (type t3) (type t4) (type t5) : arg:(t1, t2, t3, _, t4, t5) arg -> _ =
    fun ~arg ac pc ->
      let prefix =
        let pred_name = if exact then "typeof" else "instanceof" in
        match ac with
        | JCalloc_root _ ->
          pred_name ^ (match arg with Singleton -> "_singleton" | Range_l_r -> "")
        | JCalloc_bitvector -> pred_name ^ "_bitvector" (* TODO *)
      in
      Theory.struct_ pc, prefix ^ "_" ^ (Class.pointer pc)

  let frame ~for_ ac pc =
    let for_ =
      match for_ with
      | `alloc_tables_in `alloc -> "alloc"
      | `alloc_tables_in `free -> "free"
      | `tag_tables -> "tag"
    in
    let prefix =
      match ac with
      | JCalloc_root _ -> "frame_" ^ for_
      | JCalloc_bitvector -> "frame_" ^ for_ ^ "_bitvector" (* TODO *)
    in
    Theory.struct_ pc, prefix ^ "_" ^ (Class.pointer pc)
end

module Param =
struct
  let alloc (type t1) (type t2) :
    arg:(Module.t * string, check_size:bool -> Module.t * string, _, _, t1, t2) arg -> _ -> _ -> t2 =
    fun ~arg ac pc ->
      let prefix =
        match ac with
        | JCalloc_root _ ->
          "allocate" ^ (match arg with Singleton -> "_singleton" | Range_0_n -> "")
        | JCalloc_bitvector -> "allocate_bitvector"
      in
      let n = prefix ^ "_" ^ (Class.pointer pc) in
      match arg with
      | Singleton -> Module.struct_ ~safe:true pc, n
      | Range_0_n ->
        fun ~check_size -> Module.struct_ ~safe:(not check_size) pc, if check_size then n ^ "_requires" else n

  let free ~safe ac pc =
    let prefix =
      match ac with
      | JCalloc_root _ -> "free"
      | JCalloc_bitvector -> "free_bitvector"
    in
    Module.struct_ ~safe pc, (if safe then "safe_" else "") ^ prefix ^ "_" ^ (Class.pointer pc)

  let any_enum ae = "any" ^ string_of_some_enum ae
end

let root_alloc_table_name vi = vi.ri_name ^ "_alloc_table"

let root_tag_table_name vi = vi.ri_name ^ "_tag_table"

let root_axiom_on_tags_name vi = vi.ri_name ^ "_tags"

let of_pointer_address_name vi =
  vi.ri_name ^ "_of_pointer_address"

let field_memory_name fi =
  let rt = struct_root fi.fi_struct in
  if root_is_plain_union rt then
    rt.ri_name ^ "_fields"
  else
    fi.fi_final_name

let field_region_memory_name (fi, r) =
  if !Common_options.separation_sem = SepRegions && not (is_dummy_region r)
  then
    (field_memory_name fi) ^ "_" ^ (Region.name r)
  else
    field_memory_name fi

let union_memory_name vi =
  vi.ri_name ^ "_fields"

let union_region_memory_name (vi, r) =
  if !Common_options.separation_sem = SepRegions && not (is_dummy_region r)
  then
    (union_memory_name vi) ^ "_" ^ (Region.name r)
  else
    union_memory_name vi

let bitvector_region_memory_name r =
  if !Common_options.separation_sem = SepRegions && not (is_dummy_region r)
  then
    Type.bitvector ^ "_" ^ (Region.name r)
  else
    Type.bitvector

let union_memory_type_name vi =
  vi.ri_name ^ "_union"

let memory_name (mc,r) =
  match mc with
  | JCmem_field fi -> field_region_memory_name (fi,r)
  | JCmem_plain_union vi -> union_region_memory_name (vi,r)
  | JCmem_bitvector -> bitvector_region_memory_name r

let alloc_bitvector_logic_name pc =
  (Class.pointer pc) ^ "_alloc_bitvector"

let mem_bitvector_logic_name pc =
  (Class.pointer pc) ^ "_mem_bitvector"

let alloc_of_bitvector_param_name pc =
  (Class.pointer pc) ^ "_alloc_of_bitvector"

let mem_of_bitvector_param_name pc =
  (Class.pointer pc) ^ "_mem_of_bitvector"

let alloc_to_bitvector_param_name pc =
  (Class.pointer pc) ^ "_alloc_to_bitvector"

let mem_to_bitvector_param_name pc =
  (Class.pointer pc) ^ "_mem_to_bitvector"

let jessie_return_variable = "return"
let jessie_return_exception = "Return"

let exception_name ei =
  ei.exi_name ^ "_exc"

let mutable_name pc =
  "mutable_" ^ (Class.pointer pc)

let committed_name pc =
  "committed_" ^ (Class.pointer pc)

let fully_packed_name st =
  "fully_packed_"^(root_name st)

let hierarchy_invariant_name st =
  "global_invariant_"^(root_name st)

let pack_name st =
  "pack_"^(root_name st)

let unpack_name st =
  "unpack_"^(root_name st)

let fully_packed_name = "fully_packed"

let unique_name =
  let unique_names = Hashtbl.create 127 in
  function s ->
    try
      let s = if s = "" then "unnamed" else s in
      let count = Hashtbl.find unique_names s in
      incr count;
      s ^ "_" ^ (string_of_int !count)
    with Not_found ->
      Hashtbl.add unique_names s (ref 0); s

let cast_factor_name = "cast_factor"

let reinterpret_parameter_name ~safety_checking =
  if safety_checking () then "reinterpret_parameter"
                        else "safe_reinterpret_parameter"

let reinterpret_cast_name op =
  "reinterpret_cast_" ^
  match op with
  | `Retain -> "retain"
  | `Merge _ -> "merge"
  | `Split _ -> "split"

let logic_integer_of_bitvector_name = "integer_of_bitvector"
let logic_bitvector_of_integer_name = "bitvector_of_integer"
let logic_real_of_bitvector_name = "real_of_bitvector"

let native_name =
  function
  | Tunit -> "unit"
  | Tboolean -> "boolean"
  | Tinteger -> "integer"
  | Treal -> "real"
  | Tgenfloat `Double -> "double"
  | Tgenfloat `Float -> "single"
  | Tgenfloat `Binary80 -> "binary80"
  | Tstring -> "string"

let logic_bitvector_of_variant_name vi = "bitvector_of_" ^ vi.ri_name
let logic_variant_of_bitvector_name vi = vi.ri_name ^ "_of_bitvector"

let logic_union_of_field_name fi = "bitvector_of_" ^ fi.fi_name
let logic_field_of_union_name fi = fi.fi_name ^ "_of_bitvector"

let why_name_of_format =
  function
  | `Float -> "Single"
  | `Double -> "Double"
  | `Binary80 -> "Binary80"

(*
  Local Variables:
  compile-command: "ocamlc -c -bin-annot -I . -I ../src jc_name.ml"
  End:
*)
