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

open Stdlib

open Env
open Fenv
open Ast
open Region
open Common
open Output_ast

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
  let pointer = "pointer"
  let pset = "pset"
  let tag_id = "tag_id"
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

let label =
  let open Env in
  function
  | LabelHere -> "Here"
  | LabelOld -> ""
  | LabelPre -> "Pre"
  | LabelPost -> "Post"
  | LabelName lab -> lab.lab_final_name

let voidp = "voidP"

let charp = "charP"

let tag st = st.si_name ^ "_tag"

let tag_table (ri, r) =
  if not (is_dummy_region r) then
    (Type.root ri) ^ "_" ^ (Region.name r) ^ "_tag_table"
  else
    (Type.root ri) ^ "_tag_table"

let alloc_table (ac, r) =
  if not (is_dummy_region r) then
    (Class.alloc ac) ^ "_" ^ (Region.name r) ^ "_alloc_table"
  else
    (Class.alloc ac) ^ "_alloc_table"

let memory (fi, r) =
  if not (is_dummy_region r) then
    fi.fi_final_name ^ "_" ^ (Region.name r)
  else
    fi.fi_final_name

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
  type t = string * [ `Short | `Qualified ]
  let root ri = "Root_" ^ (Type.root ri), `Short
  (* ATTENTION: this theory is non-existent, there is no more "obsolete" support for BV,
     the new implementation of BV in Why3 should become supported by Jessie2. *)
  let bitvector = "Bitvector", `Short
  let bool = "Bool", `Qualified
  let single = "Single", `Qualified
  let double = "Double", `Qualified
  let binary80 = "Binary80", `Qualified
  let real = "Real", `Qualified
  let current = "", `Short
  let struct_ =
    function
    | JCtag (si, _) -> "Struct_" ^ si.si_name, `Short
    | JCroot ri -> "Root_" ^ ri.ri_name, `Short
  let axiomatic = (^) "Axiomatic_"
  let axiomatic_of li =
    Option.map_default li.li_axiomatic ~default:("Logic_" ^ li.li_final_name) ~f:axiomatic, `Short
  let logic_type name = "Logic_type_" ^ name, `Short
  let lemma ~is_axiom id = (if is_axiom then "Axiom_" else "Lemma_") ^ id, `Short
  let reinterpret_mem = axiomatic "Jessie_memory_reinterpretation_predicates"
  let reinterpret_pred =
    let regexp = Str.regexp_string "_as_" in
    fun s ->
      let from, to_ = List.(fdup2 hd last @@ Str.split regexp s) in
      if from <> to_ then Some (String.capitalize @@ to_ ^ "_of_" ^ from, `Qualified)
                     else None

  module Jessie =
  struct
    let pointer = "Jessie_pointer", `Short
    let zwf = "Jessie_zwf", `Short
    let alloc_table = "Jessie_alloc_table", `Short
    let memory = "Jessie_memory", `Short
    let pset = "Jessie_pset", `Short
    let pset_range = "Jessie_pset_range", `Short
    let pset_range_left = "Jessie_pset_range_left", `Short
    let pset_range_right = "Jessie_pset_range_right", `Short
    let pset_deref = "Jessie_pset_deref", `Short
    let pset_union = "Jessie_pset_union", `Short
    let pset_all = "Jessie_pset_all", `Short
    let pset_disjoint = "Jessie_pset_disjoint", `Short
    let pset_included = "Jessie_pset_included", `Short
    let assigns = "Jessie_assigns", `Short
    let tag_id = "Jessie_tag_id", `Short
    let voidp = "Jessie_voidp", `Short
    let voidp_tag_id = "Jessie_voidp_tag_id", `Short
    let charp_tag_id = "Jessie_charp_tag_id", `Short
    let tag = "Jessie_tag", `Short
    let tag_table_type = "Jessie_tag_table_type", `Short
    let tag_table = "Jessie_tag_table", `Short
    let sidecast = "Jessie_sidecast", `Short
    let reinterpret = "Jessie_reinterpret", `Short
    let reinterpret_cast = "Jessie_reinterpret_cast", `Short
    let allocable = "Jessie_allocable", `Short
    let alloc = "Jessie_alloc", `Short
    let same_except = "Jessie_same_except", `Short
    let rmem = "Jessie_rmem", `Short
  end
end

module Module =
struct
  type t = string * [ `Short | `Qualified ]
  let struct_ ~safe pc = (fst (Theory.struct_ pc) ^ if safe then "_safe" else "_unsafe"), `Short
  let func ~extern ~safe f =
    "Function_" ^ f.fun_final_name ^
    match extern, safe with
    | true, false -> ""
    | true, true -> "_safe"
    | false, false -> "_behaviors"
    | false, true -> "_safety"
  let exceptions = "Exceptions", `Short
  let globals pc =
    "Globals_" ^ Option.map_default ~default:"simple" ~f:(String.lowercase % fst % Theory.struct_) pc, `Short

  module Jessie =
  struct
    let return = "Jessie_return", `Short
    let sub_pointer_safe = "Jessie_sub_pointer_safe", `Short
    let sub_pointer_unsafe = "Jessie_sub_pointer_unsafe", `Short
    let eq_pointer_safe = "Jessie_eq_pointer_safe", `Short
    let eq_pointer_unsafe = "Jessie_eq_pointer_unsafe", `Short
    let acc_safe = "Jessie_acc_safe", `Short
    let acc_unsafe = "Jessie_acc_unsafe", `Short
    let acc_offset_safe = "Jessie_acc_offset_safe", `Short
    let upd_safe = "Jessie_upd_safe", `Short
    let upd_unsafe = "Jessie_upd_unsafe", `Short
    let upd_offset_safe = "Jessie_upd_offset_safe", `Short
    let instanceof = "Jessie_instanceof", `Short
    let downcast_safe = "Jessie_downcast_safe", `Short
    let downcast_unsafe = "Jessie_downcast_unsafe", `Short
    let sidecast_safe = "Jessie_sidecast_safe", `Short
    let sidecast_safe_reinterpret = "Jessie_sidecast_safe_reinterpret", `Short
    let sidecast_unsafe = "Jessie_sidecast_unsafe", `Short
    let shift_safe = "Jessie_shift_safe", `Short
    let shift_unsafe = "Jessie_shift_unsafe", `Short
    let any_int = "Jessie_any_int", `Short
    let any_real = "Jessie_any_real", `Short
    let any_bool = "Jessie_any_bool", `Short
    let any_pointer = "Jessie_any_pointer", `Short
    let any_memory = "Jessie_any_memory", `Short
    let any_alloc_table = "Jessie_any_alloc_table", `Short
    let any_tag_table = "Jessie_any_tag_table", `Short
    let reinterpret_unsafe = "Jessie_reinterpret_unsafe", `Short
    let reinterpret_safe = "Jessie_reinterpret_safe", `Short
  end
end

let exception_ ei =
  Module.exceptions, ei.exi_name ^ "_exc"

module Pred =
struct
  let valid ~equal ~left ~right ac pc =
    let prefix =
      match ac with
      | JCalloc_root _ ->
        (if equal then "strict_" else "") ^
        begin match left, right with
        | false, false -> assert false
        | false, true -> "right_"
        | true, false -> "left_"
        | true, true -> ""
        end ^
        "valid"
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

  let containerof
      (type t1) (type t2) (type t3) (type t4) (type t5) : arg:(t1, t2, t3, _, t4, t5) arg -> _ =
    fun ~arg ac pc ->
      let prefix =
        let container_of = "container_of" in
        match ac with
        | JCalloc_root _ ->
          container_of ^ (match arg with Singleton -> "_singleton" | Range_l_r -> "")
        | JCalloc_bitvector -> container_of ^ "_bitvector" (* TODO *)
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

let of_pointer_address_name vi =
  vi.ri_name ^ "_of_pointer_address"

let field_memory_name fi =
  let rt = struct_root fi.fi_struct in
  if root_is_plain_union rt then
    rt.ri_name ^ "_fields"
  else
    fi.fi_final_name

let field_region_memory_name (fi, r) =
  if not (is_dummy_region r) then
    (field_memory_name fi) ^ "_" ^ (Region.name r)
  else
    field_memory_name fi

let union_memory_name vi =
  vi.ri_name ^ "_fields"

let union_region_memory_name (vi, r) =
  if not (is_dummy_region r) then
    (union_memory_name vi) ^ "_" ^ (Region.name r)
  else
    union_memory_name vi

let bitvector_region_memory_name r =
  if not (is_dummy_region r) then
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
let jessie_return_exception = Module.Jessie.return, "Return"

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
