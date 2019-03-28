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
open Envset
open Region
open Ast
open Fenv

open Name
open Constructors
open Common

open Struct_tools

open Format
open Pp

type precision_mode = MApprox | MPrecise
let current_mode = ref MApprox

(* Constant memories *)
let constant_memories = StringHashtblIter.create 17

(* Constant allocation tables *)
let constant_alloc_tables = StringHashtblIter.create 17

(* Constant allocation tables *)
let constant_tag_tables = StringHashtblIter.create 17

let add_constant_memory (mc,r) =
  StringHashtblIter.add constant_memories (memory_name (mc,r)) (mc,r)

let add_constant_alloc_table (ac,r) =
  StringHashtblIter.add constant_alloc_tables (Name.alloc_table (ac,r)) (ac,r)

let add_constant_tag_table (vi,r) =
  StringHashtblIter.add constant_tag_tables (Name.tag_table (vi,r)) (vi,r)

(* Transposition for calls *)

let transpose_labels ~label_assoc labs =
  match label_assoc with
  | None -> labs
  | Some assoc ->
    LogicLabelSet.fold
      (fun lab acc ->
         let lab = try List.assoc lab assoc with Not_found -> lab in
         LogicLabelSet.add lab acc)
      labs
      LogicLabelSet.empty

let transpose_region ~region_assoc r =
  if Region.polymorphic r then
    try Some (RegionList.assoc r region_assoc)
    with Not_found -> None (* Local region *)
  else Some r

(* TODO: complete for recursive *)
let make_region_mem_assoc ~params =
  let aux acc r ty =
    if Region.bitwise r then
      match ty with
        | JCTpointer(pc,_,_) ->
            let all_mems = all_memories pc in
            List.fold_left (fun acc mc -> MemorySet.add (mc,r) acc) acc all_mems
        | JCTnative _ | JCTlogic _ | JCTenum _ | JCTnull | JCTany -> acc
        | JCTtype_var _ -> assert false
    else acc
  in
  List.fold_left
    (fun acc v -> aux acc v.vi_region v.vi_type)
    MemorySet.empty params

let transpose_alloc_table ~region_mem_assoc (ac,r) =
  if Region.bitwise r then
    try
      (* Translate bitwise allocation table into typed ones *)
      let mems = MemorySet.find_region r region_mem_assoc in
      MemorySet.fold (fun (mc,r) acc ->
                       let ac = alloc_class_of_mem_class mc in
                       AllocSet.add (ac,r) acc
                    ) mems AllocSet.empty
    with Not_found ->
      (* No possible effect on caller types *)
      AllocSet.empty
  else AllocSet.singleton (ac,r)

let transpose_tag_table ~region_mem_assoc (vi,r) =
  if Region.bitwise r then
    try
      (* Translate bitwise tag table into typed ones *)
      let mems = MemorySet.find_region r region_mem_assoc in
      MemorySet.fold (fun (mc,r) acc ->
                       let vi = root_info_of_mem_class mc in
                       TagSet.add (vi,r) acc
                     ) mems TagSet.empty
    with Not_found ->
      (* No possible effect on caller types *)
      TagSet.empty
  else TagSet.singleton (vi,r)

let transpose_memory ~region_mem_assoc (mc,r) =
  if Region.bitwise r then
    try
      (* Translate bitwise memories into typed ones *)
      MemorySet.find_region r region_mem_assoc
    with Not_found ->
      (* No possible effect on caller types *)
      MemorySet.empty
  else MemorySet.singleton (mc,r)

let has_alloc_table (ac,r) alloc_effect =
  let allocs = AllocSet.of_list (AllocMap.keys alloc_effect) in
  if Region.bitwise r then AllocSet.mem_region r allocs
  else AllocSet.mem (ac,r) allocs

let has_memory (mc,r) mem_effect =
  let mems = MemorySet.of_list (MemoryMap.keys mem_effect) in
  if Region.bitwise r then MemorySet.mem_region r mems
  else MemorySet.mem (mc,r) mems

(* Printing effects *)

let print_list_assoc_label pr fmt ls =
  fprintf fmt "%a"
    (print_list comma
       (fun fmt (k, labs) ->
          fprintf fmt "%a at (%a)"
            pr k
            (print_list comma Print_misc.label)
            (LogicLabelSet.elements labs)))
    ls

let print_alloc_table fmt (ac, r) =
  fprintf fmt "(%a : %a)" Region.print r Print_misc.alloc_class ac

let print_tag_table fmt (vi, r) =
  fprintf fmt "(%a : %s)" Region.print r vi.ri_name

let print_memory fmt (mc, r) =
  fprintf fmt "(%a : %a)" Region.print r Print_misc.memory_class mc

let print_location fmt (loc, (mc, r)) =
  fprintf fmt "(%a at %a)" print_memory (mc, r) Print.location loc

let print_variable fmt v =
  fprintf fmt "%s" v.vi_name

let print_exception fmt exc =
  fprintf fmt "%s" exc.exi_name

let print_effect fmt ef =
  fprintf fmt
    ("@[@[ alloc_table: @[%a@]@]@\n" ^^
     "@[ tag_table: @[%a@]@]@\n" ^^
     "@[ memories: @[%a@]@]@\n" ^^
     "@[ raw memories: @[%a@]@]@\n" ^^
     "@[ precise memories: @[%a@]@]@\n" ^^
     "@[ globals: @[%a@]@]@\n" ^^
     "@[ locals: @[%a@]@]@]@.")
    (print_list_assoc_label print_alloc_table)
    (AllocMap.elements ef.e_alloc_tables)
    (print_list_assoc_label print_tag_table)
    (TagMap.elements ef.e_tag_tables)
    (print_list_assoc_label print_memory)
    (MemoryMap.elements ef.e_memories)
    (print_list_assoc_label print_memory)
    (MemoryMap.elements ef.e_raw_memories)
    (print_list_assoc_label print_location)
    (LocationMap.elements ef.e_precise_memories)
    (print_list_assoc_label print_variable)
    (VarMap.elements ef.e_globals)
    (print_list_assoc_label print_variable)
    (VarMap.elements ef.e_locals)

(* Operations on effects *)

let ef_union ef1 ef2 =
  {
    e_alloc_tables =
      AllocMap.merge LogicLabelSet.union
        ef1.e_alloc_tables ef2.e_alloc_tables;
    e_tag_tables =
      TagMap.merge LogicLabelSet.union
        ef1.e_tag_tables ef2.e_tag_tables;
    e_raw_memories =
      MemoryMap.merge LogicLabelSet.union
        ef1.e_raw_memories ef2.e_raw_memories;
    e_precise_memories =
      LocationMap.merge LogicLabelSet.union
        ef1.e_precise_memories ef2.e_precise_memories;
    e_memories =
      MemoryMap.merge LogicLabelSet.union
        ef1.e_memories ef2.e_memories;
    e_globals =
      VarMap.merge LogicLabelSet.union
        ef1.e_globals ef2.e_globals;
    e_locals =
      VarMap.merge LogicLabelSet.union
        ef1.e_locals ef2.e_locals;
    e_mutable =
      StringSet.union
        ef1.e_mutable ef2.e_mutable;
    e_committed =
      StringSet.union
        ef1.e_committed ef2.e_committed;
  }

  let ef_inter ef1 ef2 =
    {
      e_alloc_tables =
        AllocMap.inter_merge LogicLabelSet.union (fun _ -> false)
          ef1.e_alloc_tables ef2.e_alloc_tables;
      e_tag_tables =
        TagMap.inter_merge LogicLabelSet.union (fun _ -> false)
          ef1.e_tag_tables ef2.e_tag_tables;
      e_raw_memories =
        MemoryMap.inter_merge LogicLabelSet.union (fun _ -> false)
          ef1.e_raw_memories ef2.e_raw_memories;
      e_precise_memories =
        LocationMap.inter_merge LogicLabelSet.union (fun _ -> false)
          ef1.e_precise_memories ef2.e_precise_memories;
      e_memories =
        MemoryMap.inter_merge LogicLabelSet.union (fun _ -> false)
          ef1.e_memories ef2.e_memories;
      e_globals =
        VarMap.inter_merge LogicLabelSet.union (fun _ -> false)
          ef1.e_globals ef2.e_globals;
      e_locals =
        VarMap.inter_merge LogicLabelSet.union (fun _ -> false)
          ef1.e_locals ef2.e_locals;
      e_mutable =
        StringSet.inter
          ef1.e_mutable ef2.e_mutable;
      e_committed =
        StringSet.inter
          ef1.e_committed ef2.e_committed;
    }

let ef_diff ef1 ef2 =
  let module Hide = struct
    type v = LogicLabelSet.t
    module type S = sig
      type t
      val diff_merge : (v -> v -> v) -> (v -> bool) -> t -> t -> t
    end
    module Hide (M : Map.S) = struct
      type t = v M.t
      let diff_merge = M.diff_merge
    end
  end in
  let diff (type t) (module M : Hide.S with type t = t) f =
    LogicLabelSet.(M.diff_merge union (not % is_empty) (f ef1) (f ef2))
  in
  let open Hide in
  {
    e_alloc_tables = diff (module Hide(AllocMap)) (fun e -> e.e_alloc_tables);
    e_tag_tables = diff (module Hide(TagMap)) (fun e -> e.e_tag_tables);
    e_raw_memories = diff (module Hide(MemoryMap)) (fun e -> e.e_raw_memories);
    e_precise_memories = diff (module Hide(LocationMap)) (fun e -> e.e_precise_memories);
    e_memories = diff (module Hide(MemoryMap)) (fun e -> e.e_memories);
    e_globals = diff (module Hide(VarMap)) (fun e -> e.e_globals);
    e_locals = diff (module Hide(VarMap)) (fun e -> e.e_locals);
    e_mutable = StringSet.diff ef1.e_mutable ef2.e_mutable;
    e_committed = StringSet.diff ef1.e_committed ef2.e_committed
  }

let ef_filter_by_region f ef =
  let f (_, r) _ = f r
  and f' (_, (_, r)) _ = f r
  and f_vi vi _ = f vi.vi_region in
  { ef with
    e_alloc_tables = AllocMap.filter f ef.e_alloc_tables;
    e_tag_tables = TagMap.filter f ef.e_tag_tables;
    e_raw_memories = MemoryMap.filter f ef.e_raw_memories;
    e_precise_memories = LocationMap.filter f' ef.e_precise_memories;
    e_memories = MemoryMap.filter f ef.e_memories;
    e_globals = VarMap.filter f_vi ef.e_globals;
    e_locals = VarMap.filter f_vi ef.e_locals;
  }

let ef_filter_labels ~label_assoc ef =
  let filter_labels labs =
    List.fold_left
      (fun acc (l1,l2) ->
         if LogicLabelSet.mem l2 labs then LogicLabelSet.add l1 acc else acc)
      LogicLabelSet.empty label_assoc
  in
  { ef with
      e_memories =
        MemoryMap.fold
          (fun m labs acc ->
             MemoryMap.add m (filter_labels labs) acc
          ) ef.e_memories MemoryMap.empty;
  }

let ef_assoc ?label_assoc ~region_assoc ~region_mem_assoc ef =
  { ef with
    e_alloc_tables =
      AllocMap.fold
        (fun (ac, distr) labs acc ->
           let labs = transpose_labels ~label_assoc labs in
           match transpose_region ~region_assoc distr with
           | None -> acc
           | Some locr ->
             let allocs = transpose_alloc_table ~region_mem_assoc (ac, distr) in
             AllocSet.fold
               (fun (ac, _r) acc ->
                  if not (Region.polymorphic locr) then
                    add_constant_alloc_table (ac, locr);
                  AllocMap.add_merge LogicLabelSet.union (ac, locr) labs acc)
               allocs
               acc)
        ef.e_alloc_tables
        AllocMap.empty;
      e_tag_tables =
        TagMap.fold
          (fun (vi,distr) labs acc ->
             let labs = transpose_labels ~label_assoc labs in
             match transpose_region ~region_assoc distr with
               | None -> acc
               | Some locr ->
                 let tags = transpose_tag_table ~region_mem_assoc (vi, distr) in
                 TagSet.fold
                   (fun (vi, _r) acc ->
                      if not (Region.polymorphic locr) then
                        add_constant_tag_table (vi, locr);
                      TagMap.add_merge LogicLabelSet.union (vi, locr) labs acc)
                   tags
                   acc)
          ef.e_tag_tables
          TagMap.empty;
      e_raw_memories =
        MemoryMap.fold
          (fun (mc,distr) labs acc ->
             let labs = transpose_labels ~label_assoc labs in
             match transpose_region ~region_assoc distr with
               | None -> acc
               | Some locr ->
                   let mems =
                     transpose_memory ~region_mem_assoc (mc,distr)
                   in
                   MemorySet.fold
                     (fun (mc,_r) acc ->
                        if not (Region.polymorphic locr) then
                          add_constant_memory (mc,locr);
                        MemoryMap.add_merge LogicLabelSet.union (mc,locr) labs acc
                     ) mems acc
          ) ef.e_raw_memories MemoryMap.empty;
      e_memories =
        MemoryMap.fold
          (fun (mc,distr) labs acc ->
             let labs = transpose_labels ~label_assoc labs in
             match transpose_region ~region_assoc distr with
               | None -> acc
               | Some locr ->
                   let mems =
                     transpose_memory ~region_mem_assoc (mc,distr)
                   in
                   MemorySet.fold
                     (fun (mc,_r) acc ->
                        if not (Region.polymorphic locr) then
                          add_constant_memory (mc,locr);
                        MemoryMap.add_merge LogicLabelSet.union (mc,locr) labs acc
                     ) mems acc
          ) ef.e_memories MemoryMap.empty;
      e_globals =
        VarMap.fold
          (fun v labs acc ->
             VarMap.add v (transpose_labels ~label_assoc labs) acc
          ) ef.e_globals VarMap.empty;
      e_locals = VarMap.empty;
  }

let same_effects ef1 ef2 =
  let eq = LogicLabelSet.equal in
  AllocMap.equal eq ef1.e_alloc_tables ef2.e_alloc_tables
  && TagMap.equal eq ef1.e_tag_tables ef2.e_tag_tables
  && MemoryMap.equal eq ef1.e_raw_memories ef2.e_raw_memories
  && LocationMap.equal eq
    ef1.e_precise_memories ef2.e_precise_memories
  && MemoryMap.equal eq ef1.e_memories ef2.e_memories
  && VarMap.equal eq ef1.e_globals ef2.e_globals
  && VarMap.equal eq ef1.e_locals ef2.e_locals
  && StringSet.equal ef1.e_mutable ef2.e_mutable
  && StringSet.equal ef1.e_committed ef2.e_committed

(* Operations on function effects *)

let fef_reads ef =
  {
    fe_reads = ef;
    fe_writes = empty_effects;
    fe_raises = ExceptionSet.empty;
    fe_reinterpret = false
  }

let fef_union fef1 fef2 =
  {
    fe_reads = ef_union fef1.fe_reads fef2.fe_reads;
    fe_writes = ef_union fef1.fe_writes fef2.fe_writes;
    fe_raises = ExceptionSet.union fef1.fe_raises fef2.fe_raises;
    fe_reinterpret = fef1.fe_reinterpret || fef2.fe_reinterpret
  }

let fef_diff fef1 fef2 =
  {
    fe_reads = ef_diff fef1.fe_reads fef2.fe_reads;
    fe_writes = ef_diff fef1.fe_writes fef2.fe_writes;
    fe_raises = ExceptionSet.diff fef1.fe_raises fef2.fe_raises;
    fe_reinterpret = fef1.fe_reinterpret && not fef2.fe_reinterpret
  }

let fef_filter_by_region f fef =
  {
    fef with
    fe_reads = ef_filter_by_region f fef.fe_reads;
    fe_writes = ef_filter_by_region f fef.fe_writes
  }

let fef_assoc ~region_assoc ~region_mem_assoc fef =
  {
    fe_reads = ef_assoc ~region_assoc ~region_mem_assoc fef.fe_reads;
    fe_writes = ef_assoc ~region_assoc ~region_mem_assoc fef.fe_writes;
    fe_raises = fef.fe_raises;
    fe_reinterpret = fef.fe_reinterpret
  }

let same_feffects fef1 fef2 =
  same_effects fef1.fe_reads fef2.fe_reads
  && same_effects fef1.fe_writes fef2.fe_writes
  && ExceptionSet.equal fef1.fe_raises fef2.fe_raises

(* Query of a single effect *)

let has_memory_effect ef (mc,r) =
  try
    ignore (MemoryMap.find (mc,r) ef.e_memories);
    true
  with Not_found ->
    try
      ignore (MemoryMap.find (mc,r) ef.e_raw_memories);
      true
    with Not_found ->
      let locs =
        LocationMap.filter
          (fun (_loc,mem) _ -> Memory.equal mem (mc,r))
          ef.e_precise_memories
      in
      not (LocationMap.is_empty locs)

(* Addition of a single effect *)

let add_alloc_effect lab ef (ac, r) =
  if not (Region.polymorphic r) then add_constant_alloc_table (ac,r);
  let labs = LogicLabelSet.singleton lab in
  { ef with e_alloc_tables =
      AllocMap.add_merge LogicLabelSet.union
        (ac,r) labs ef.e_alloc_tables }

let add_tag_effect lab ef (vi,r) =
  if not (Region.polymorphic r) then add_constant_tag_table (vi,r);
  let labs = LogicLabelSet.singleton lab in
  { ef with e_tag_tables =
      TagMap.add_merge LogicLabelSet.union
        (vi,r) labs ef.e_tag_tables }

let add_memory_effect lab ef (mc,r) =
  if not (Region.polymorphic r) then add_constant_memory (mc,r);
  let labs = LogicLabelSet.singleton lab in
  match !current_mode with
    | MApprox ->
        { ef with e_memories =
            MemoryMap.add_merge LogicLabelSet.union
              (mc,r) labs ef.e_memories }
    | MPrecise ->
        { ef with e_raw_memories =
            MemoryMap.add_merge LogicLabelSet.union
              (mc,r) labs ef.e_raw_memories }

let add_precise_memory_effect lab ef (loc,(mc,r)) =
  let labs = LogicLabelSet.singleton lab in
  { ef with e_precise_memories =
      LocationMap.add_merge LogicLabelSet.union
        (loc,(mc,r)) labs ef.e_precise_memories }

let add_global_effect lab ef v =
  let labs = LogicLabelSet.singleton lab in
  { ef with e_globals =
      VarMap.add_merge LogicLabelSet.union v labs ef.e_globals }

let add_local_effect lab ef v =
  let labs = LogicLabelSet.singleton lab in
  { ef with e_locals =
      VarMap.add_merge LogicLabelSet.union v labs ef.e_locals }

let add_mutable_effect ef pc =
  { ef with e_mutable = StringSet.add
      (Name.Class.pointer pc) ef.e_mutable }

let add_committed_effect ef pc =
  { ef with e_committed = StringSet.add
      (Name.Class.pointer pc) ef.e_committed }

(* Addition of a single read *)

let add_alloc_reads lab fef acr =
  { fef with fe_reads = add_alloc_effect lab fef.fe_reads acr }

let add_alloc_reads' lab acr fef = add_alloc_reads lab fef acr

let add_tag_reads lab fef rir =
  { fef with fe_reads = add_tag_effect lab fef.fe_reads rir }

let add_tag_reads' lab rir fef = add_tag_reads lab fef rir

let add_memory_reads lab fef mcr =
  { fef with fe_reads = add_memory_effect lab fef.fe_reads mcr }

let add_memory_reads' lab mcr fef = add_memory_reads lab fef mcr

let add_precise_memory_reads lab fef (loc,(mc,r)) =
  { fef with fe_reads =
      add_precise_memory_effect lab fef.fe_reads (loc,(mc,r)) }

let add_global_reads lab fef v =
  { fef with fe_reads = add_global_effect lab fef.fe_reads v }

let add_local_reads lab fef v =
  { fef with fe_reads = add_local_effect lab fef.fe_reads v }

let add_mutable_reads fef pc =
  { fef with fe_reads = add_mutable_effect fef.fe_reads pc }

let add_committed_reads fef pc =
  { fef with fe_reads = add_committed_effect fef.fe_reads pc }

(* Addition of a single write *)

let add_alloc_writes lab fef acr =
  { fef with fe_writes = add_alloc_effect lab fef.fe_writes acr }

let add_alloc_writes' lab acr fef = add_alloc_writes lab fef acr

let add_tag_writes lab fef rir =
  { fef with fe_writes = add_tag_effect lab fef.fe_writes rir }

let add_tag_writes' lab rir fef = add_tag_writes lab fef rir

let add_memory_writes lab fef mcr =
  { fef with fe_writes = add_memory_effect lab fef.fe_writes mcr }

let add_memory_writes' lab mcr fef = add_memory_writes lab fef mcr

let add_precise_memory_writes lab fef (loc,(mc,r)) =
  { fef with fe_writes =
      add_precise_memory_effect lab fef.fe_writes (loc,(mc,r)) }

let add_global_writes lab fef vi =
  { fef with fe_writes = add_global_effect lab fef.fe_writes vi }

let add_local_writes lab fef vi =
  { fef with fe_writes = add_local_effect lab fef.fe_writes vi }

let add_mutable_writes fef pc =
  { fef with fe_writes = add_mutable_effect fef.fe_writes pc }

let add_committed_writes fef pc =
  { fef with fe_writes = add_committed_effect fef.fe_writes pc }

(* Addition of a single exception *)

let add_exception_effect fef exc =
  { fef with fe_raises = ExceptionSet.add exc fef.fe_raises }


(*****************************************************************************)
(*                                  Unions                                   *)
(*****************************************************************************)

type shift_offset =
  | Int_offset of int
  | Expr_offset of Fenv.expr
  | Term_offset of Fenv.term

let offset_of_expr e =
  match e#node with
    | JCEconst (JCCinteger s) ->
        (try
           Int_offset (int_of_string s)
         with Failure _ -> Expr_offset e)
    | _ -> Expr_offset e

let offset_of_term t =
  match t#node with
    | JCTconst (JCCinteger s) ->
        (try
           Int_offset (int_of_string s)
         with Failure _ -> Term_offset t)
    | _ -> Term_offset t

let offset_of_field fi =
  match field_offset_in_bytes fi with
    | None ->
        Format.eprintf "Effect.offset_of_field: fi=%s@."
          fi.fi_name;
        assert false
    | Some off -> Int_offset off

let mult_offset i off =
  match off with
    | Int_offset j -> Int_offset (i * j)
    | Expr_offset e ->
        let ie = Expr.mkint ~value:i ()  in
        let mule =
          Expr.mkbinary
            ~expr1:ie ~op:(`Bmul,`Integer) ~expr2:e ~typ:integer_type ()
        in
        Expr_offset mule
    | Term_offset t ->
        let it = Term.mkint ~value:i ()  in
        let mult =
          Term.mkbinary
            ~term1:it ~op:(`Bmul,`Integer) ~term2:t ~typ:integer_type ()
        in
        Term_offset mult

let add_offset off1 off2 =
  match off1,off2 with
    | Int_offset i, Int_offset j ->
        let k = i + j in
        Int_offset k
    | Expr_offset e1, Expr_offset e2 ->
        let adde =
          Expr.mkbinary
            ~expr1:e1 ~op:(`Badd,`Integer) ~expr2:e2 ~typ:integer_type ()
        in
        Expr_offset adde
    | Expr_offset e, Int_offset i
    | Int_offset i, Expr_offset e ->
        let ie = Expr.mkint ~value:i ()  in
        let adde =
          Expr.mkbinary
            ~expr1:ie ~op:(`Badd,`Integer) ~expr2:e ~typ:integer_type ()
        in
        Expr_offset adde
    | Term_offset t1, Term_offset t2 ->
        let addt =
          Term.mkbinary
            ~term1:t1 ~op:(`Badd,`Integer) ~term2:t2 ~typ:integer_type ()
        in
        Term_offset addt
    | Term_offset t, Int_offset i
    | Int_offset i, Term_offset t ->
        let it = Term.mkint ~value:i ()  in
        let addt =
          Term.mkbinary
            ~term1:it ~op:(`Badd,`Integer) ~term2:t ~typ:integer_type ()
        in
        Term_offset addt
    | Expr_offset _, Term_offset _
    | Term_offset _, Expr_offset _ -> assert false

let possible_union_type = function
  | JCTpointer(pc,_,_) ->
      let rt = pointer_class_root pc in
      if root_is_union rt then Some rt else None
  | _ -> None

let union_type ty =
  match possible_union_type ty with Some rt -> rt | None -> assert false

let type_is_union ty =
  match possible_union_type ty with Some _rt -> true | None -> false

let overlapping_union_memories fi =
  let st = fi.fi_struct in
  let rt = struct_root st in
  let stlist =
    List.filter
      (fun st' -> not (st.si_name = st'.si_name))
      rt.ri_hroots
  in
  let mems =
    List.flatten
      (List.map
         (fun st -> all_memories ~select:fully_allocated (JCtag(st,[])))
         stlist)
  in
  MemClassSet.to_list (MemClassSet.of_list mems)

let possible_union_access e fi_opt =
  let fieldoffbytes fi =
    match field_offset_in_bytes fi with
      | None -> assert false
      | Some off -> Int_offset off
  in
  (* Count offset in bytes before last field access in union *)
  let rec access e =
    match e#node with
      | JCEderef(e,fi) when embedded_field fi ->
          begin match access e with
            | Some(e,off) ->
                Some (e, add_offset off (fieldoffbytes fi))
            | None ->
                if type_is_union e#typ then
                  Some (e, fieldoffbytes fi)
                else None
          end
      | JCEshift(e1,e2) ->
          begin match access e1 with
            | Some(e,off1) ->
                let off2 = offset_of_expr e2 in
                let siz = struct_size_in_bytes (pointer_struct e1#typ) in
                let off2 = mult_offset siz off2 in
                Some (e, add_offset off1 off2)
            | None -> None
          end
      | JCEalloc(_e1,st) ->
          if struct_of_union st then
            Some(e,Int_offset 0)
          else None
      | _ ->
          if type_is_union e#typ then
            Some (e,Int_offset 0)
          else None
  in
  match fi_opt with
    | None -> access e
    | Some fi ->
        match access e with
          | Some(e,off) -> Some (e, add_offset off (fieldoffbytes fi))
          | None ->
              if type_is_union e#typ then Some (e, fieldoffbytes fi) else None

(* Optionally returns a triple of
   1) a prefix [ue] of type union
   2) the field of the union [ue] accessed
   3) the offset from the address of [ue] to the final field
*)
let possible_union_deref e fi =
  let rec access e fi =
    match e#node with
      | JCEderef(e1,fi1) when embedded_field fi1 ->
          begin match access e1 fi1 with
            | Some(e2,fi2,off) ->
                Some(e2,fi2,add_offset off (offset_of_field fi))
            | None ->
                if type_is_union e1#typ then
                  Some(e1,fi,offset_of_field fi)
                else None
          end
      | JCEshift(e1,_e2) ->
          begin match access e1 fi with
            | Some(e2,fi2,off1) ->
                let off2 = offset_of_expr e2 in
                let siz = struct_size_in_bytes (pointer_struct e1#typ) in
                let off2 = mult_offset siz off2 in
                Some(e2,fi2,add_offset off1 off2)
            | None -> None
          end
      | _ -> None
  in
  match access e fi with
    | Some(e1,fi1,off) -> Some(e1,fi1,add_offset off (offset_of_field fi))
    | None ->
        if type_is_union e#typ then Some(e,fi,offset_of_field fi) else None

let destruct_union_access e fi_opt =
  match possible_union_access e fi_opt with
    | Some x -> x
    | None -> assert false

let tpossible_union_access t fi_opt =
  let fieldoffbytes fi =
    match field_offset_in_bytes fi with
      | None -> assert false
      | Some off -> Int_offset off
  in
  (* Count offset in bytes before last field access in union *)
  let rec access t =
    match t#node with
      | JCTderef(t,_lab,fi) when embedded_field fi ->
          begin match access t with
            | Some(t,off) ->
                Some (t, add_offset off (fieldoffbytes fi))
            | None ->
                if type_is_union t#typ then
                  Some (t, fieldoffbytes fi)
                else None
          end
      | JCTshift(t1,t2) ->
          begin match access t1 with
            | Some(t3,off1) ->
                let off2 = offset_of_term t2 in
                let siz = struct_size_in_bytes (pointer_struct t1#typ) in
                let off2 = mult_offset siz off2 in
                Some (t3, add_offset off1 off2)
            | None -> None
          end
      | _ ->
          if type_is_union t#typ then
            Some (t,Int_offset 0)
          else None
  in

  match fi_opt with
    | None ->
        access t
    | Some fi ->
(*         let fieldoff fi = Int_offset (string_of_int (field_offset fi)) in *)
        match access t with
          | Some(t,off) ->
              Some (t, add_offset off (fieldoffbytes fi))
          | None ->
              if type_is_union t#typ then
                Some (t, fieldoffbytes fi)
              else None

let tpossible_union_deref t fi =
  let rec access t fi =
    match t#node with
      | JCTderef(t1,_lab,fi1) when embedded_field fi1 ->
          begin match access t1 fi1 with
            | Some(t2,fi2,off) ->
                Some(t2,fi2,add_offset off (offset_of_field fi))
            | None ->
                if type_is_union t1#typ then
                  Some(t1,fi,offset_of_field fi)
                else None
          end
      | JCTshift(t1,_t2) ->
          begin match access t1 fi with
            | Some(t2,fi2,off1) ->
                let off2 = offset_of_term t2 in
                let siz = struct_size_in_bytes (pointer_struct t1#typ) in
                let off2 = mult_offset siz off2 in
                Some(t2,fi2,add_offset off1 off2)
            | None -> None
          end
      | _ -> None
  in
  match access t fi with
    | Some(t1,fi1,off) -> Some(t1,fi1,add_offset off (offset_of_field fi))
    | None ->
        if type_is_union t#typ then Some(t,fi,offset_of_field fi) else None

let tdestruct_union_access t fi_opt =
  match tpossible_union_access t fi_opt with
    | Some x -> x
    | None -> assert false

let lpossible_union_access _t _fi = None (* TODO *)

let lpossible_union_deref _t _fi = None (* TODO *)

let ldestruct_union_access loc fi_opt =
  match lpossible_union_access loc fi_opt with
    | Some x -> x
    | None -> assert false

let foreign_union _e = [] (* TODO: subterms of union that are not in union *)
let tforeign_union _t = []

let common_deref_alloc_class ~type_safe union_access e =
  if not type_safe && Region.bitwise e#region then
    JCalloc_bitvector
  else match union_access e None with
    | None -> JCalloc_root (struct_root (pointer_struct e#typ))
    | Some(e,_off) -> JCalloc_root (union_type e#typ)

let deref_alloc_class ~type_safe e =
  common_deref_alloc_class ~type_safe possible_union_access e

let tderef_alloc_class ~type_safe t =
  common_deref_alloc_class ~type_safe tpossible_union_access t

let lderef_alloc_class ~type_safe locs =
  common_deref_alloc_class ~type_safe lpossible_union_access locs

let common_deref_mem_class ~type_safe union_deref e fi =
  if not type_safe && Region.bitwise e#region then
    JCmem_bitvector, None
  else match union_deref e fi with
    | None ->
        assert (not (root_is_union (struct_root fi.fi_struct)));
        JCmem_field fi, None
    | Some(e1,fi1,_off) ->
        let rt = union_type e1#typ in
        if root_is_plain_union rt then JCmem_plain_union rt, Some fi1
        else JCmem_field fi, Some fi1

let deref_mem_class ~type_safe e fi =
  common_deref_mem_class ~type_safe possible_union_deref e fi

let tderef_mem_class ~type_safe t fi =
  common_deref_mem_class ~type_safe tpossible_union_deref t fi

let lderef_mem_class ~type_safe locs fi =
  common_deref_mem_class ~type_safe lpossible_union_deref locs fi


(******************************************************************************)
(*                                  patterns                                  *)
(******************************************************************************)

(* TODO: check the use of "label" and "r" *)
let rec pattern ef (*label r*) p =
  let r = dummy_region in
  match p#node with
    | JCPstruct(st, fpl) ->
        let ef = add_tag_effect (*label*)LabelHere ef (struct_root st,r) in
        List.fold_left
          (fun ef (fi, pat) ->
             let mc = JCmem_field fi in
             let ef = add_memory_effect (*label*)LabelHere ef (mc,r) in
             pattern ef (*label r*) pat)
          ef fpl
    | JCPor(p1, p2) ->
        pattern (pattern ef (*label r*) p1) (*label r*) p2
    | JCPas(p, _) ->
        pattern ef (*label r*) p
    | JCPvar _
    | JCPany
    | JCPconst _ ->
        ef


(******************************************************************************)
(*                              environment                                   *)
(******************************************************************************)

let current_function = ref None
let set_current_function f = current_function := Some f
let reset_current_function () = current_function := None
let get_current_function () =
  match !current_function with None -> assert false | Some f -> f

(******************************************************************************)
(*                             immutable locations                            *)
(******************************************************************************)

let term_of_expr e =
  let rec term e =
    let tnode = match e#node with
      | JCEconst c -> JCTconst c
      | JCEvar vi -> JCTvar vi
      | JCEbinary (e1, (bop,opty), e2) ->
          JCTbinary (term e1, ((bop :> bin_op),opty), term e2)
      | JCEunary (uop, e1) -> JCTunary (uop, term e1)
      | JCEshift (e1, e2) -> JCTshift (term e1, term e2)
      | JCEderef (e1, fi) -> JCTderef (term e1, LabelHere, fi)
      | JCEinstanceof (e1, st) -> JCTinstanceof (term e1, LabelHere, st)
      | JCEdowncast (e1, st) -> JCTdowncast (term e1, LabelHere, st)
      | JCEsidecast (e1, st) -> JCTsidecast (term e1, LabelHere, st)
      | JCErange_cast(e1,_) | JCEreal_cast(e1,_) ->
          (* range does not modify term value *)
          (term e1)#node
      | JCEif (e1, e2, e3) -> JCTif (term e1, term e2, term e3)
      | JCEoffset (off, e1, st) -> JCToffset (off, term e1, st)
      | JCEalloc (e, _) -> (* Note: \offset_max(t) = length(t) - 1 *)
          JCTbinary (term e, (`Bsub,`Integer), new term ~typ:integer_type (JCTconst (JCCinteger "1")) )
      | JCEfree _ -> failwith "Not a term"
      | _ -> failwith "Not a term"
(*       | JCEmatch (e, pel) -> *)
(*           let ptl = List.map (fun (p, e) -> (p, term_of_expr e)) pel in *)
(*             JCTmatch (term_of_expr e, ptl) *)
    in
      new term ~typ:e#typ ~region:e#region tnode
  in
    try Some (term e) with Failure _ -> None

let rec location_of_expr e =
  try
    let loc_node = match e#node with
      | JCEvar v ->
          JCLvar v
      | JCEderef(e1,fi) ->
          JCLderef(location_set_of_expr e1, LabelHere, fi, e#region)
      | _ -> failwith "No location for expr"
    in
    Some(new location_with ~typ:e#typ ~node:loc_node e)
  with Failure "No location for expr" -> None

and location_set_of_expr e =
  let locs_node = match e#node with
    | JCEvar v ->
        JCLSvar v
    | JCEderef(e1,fi) ->
        JCLSderef(location_set_of_expr e1, LabelHere, fi, e#region)
    | JCEshift(e1,e2) ->
        let t2_opt = term_of_expr e2 in
        JCLSrange(location_set_of_expr e1, t2_opt, t2_opt)
    | _ -> failwith "No location for expr"
  in
  new location_set_with ~typ:e#typ ~node:locs_node e

let location_set_of_expr e =
  try Some(location_set_of_expr e) with Failure "No location for expr" -> None

let rec location_of_term t =
  try
    let node = match t#node with
      | JCTvar v ->
          JCLvar v
      | JCTderef(t1,_lab,fi) ->
          JCLderef(location_set_of_term t1, LabelHere, fi, t#region)
      | JCTat(t1,lab) ->
          (match location_of_term t1 with
               None -> failwith "No location for term"
             | Some l1 -> JCLat(l1,lab))
      | _ -> failwith "No location for term"
    in
    Some(new location_with ~typ:t#typ ~node t)
  with Failure "No location for term" -> None

and location_set_of_term t =
  let locs_node = match t#node with
    | JCTvar v ->
        JCLSvar v
    | JCTderef(t1,_lab,fi) ->
        JCLSderef(location_set_of_term t1, LabelHere, fi, t#region)
    | JCTat (t1,lab) -> JCLSat(location_set_of_term t1,lab)
    | _ -> failwith "No location for term"
  in
  new location_set_with ~typ:t#typ ~node:locs_node t

let rec term_of_location_set locs =
  term_with_node_nomark locs @@
    let range_typ = function
      | Some t, _ | _, Some t -> t#typ (* Relying on earlier type checks (equality is assumed) *)
      | None, None -> JCTnative Tinteger
    in
    let range_term t1_opt t2_opt =
      term_with_node_nomark
        locs
        ~typ:(range_typ (t1_opt, t2_opt))
        ~region:dummy_region
        (JCTrange (t1_opt, t2_opt))
    in
    match locs#node, locs#region with
      | JCLSvar vi, _ -> JCTvar vi
      | JCLSderef (locs, lab, fi, r), r' when Region.equal r r' ->
          JCTderef (term_of_location_set locs, lab, fi)
      | JCLSderef (_, _, _, r), r' ->
          Typing.typing_error
            ~loc:locs#pos
            "Failed to transform location set to term: %a: different regions: %a != %a"
            Print.location_set locs Region.print r Region.print r'
      | JCLSrange (locs, t1_opt, t2_opt), _ -> JCTshift (term_of_location_set locs, range_term t1_opt t2_opt)
      | JCLSrange_term (t, t1_opt, t2_opt), _ -> JCTshift (t, range_term t1_opt t2_opt)
      | JCLSat (locs, lab), _ -> JCTat (term_of_location_set locs, lab)

let rec term_of_location ?(label=LabelHere) loc =
  term_with_node_nomark loc @@
    match loc#node, loc#region with
      | JCLvar vi, _ -> JCTvar vi
      | JCLderef (locs, lab, fi, r), r' when Region.equal r r' ->
          JCTderef (term_of_location_set locs, lab, fi)
      | JCLderef (_, _, _, r), r' ->
          Typing.typing_error
            ~loc:loc#pos
            "Failed to transform location to term: %a: different regions: %a != %a"
            Print.location loc Region.print r Region.print r'
      | JCLderef_term (t, fi), _ -> JCTderef (t, label, fi)
      | JCLsingleton t, _ -> t#node
      | JCLat (loc, label), _ -> JCTat (term_of_location ~label loc, label)

(* last location can be mutated *)
let rec immutable_location fef loc =
  match loc#node with
    | JCLvar _v -> true
    | JCLderef(locs,_lab,_fi,_r) ->
        immutable_location_set fef locs
    | JCLat(l1,_lab) -> immutable_location fef l1
    | _ -> false

and immutable_location_set fef locs =
  match locs#node with
    | JCLSvar v -> not v.vi_assigned
    | JCLSderef(locs,_lab,fi,_r) ->
        let mc,_fi_opt = lderef_mem_class ~type_safe:true locs fi in
        immutable_location_set fef locs
        && not (MemoryMap.mem (mc,locs#region) fef.fe_writes.e_memories)
    | JCLSat(l1,_lab) -> immutable_location_set fef l1
    | _ -> false

let expr_immutable_location e =
  match !current_mode with
    | MApprox -> None
    | MPrecise ->
        match !current_function with
          | None -> None
          | Some f ->
              let fef = f.fun_effects in
              match location_of_expr e with
                | None -> None
                | Some loc ->
                    if immutable_location fef loc then
                      Some loc
                    else None

let term_immutable_location t =
  match !current_mode with
    | MApprox -> None
    | MPrecise ->
        match !current_function with
          | None -> None
          | Some f ->
              let fef = f.fun_effects in
              match location_of_term t with
                | None -> None
                | Some loc ->
                    if immutable_location fef loc then
                      Some loc
                    else None

(* let immutable_heap_location fef ~full_expr e1 fi = *)
(*   match !current_mode with *)
(*     | MApprox -> None *)
(*     | MPrecise -> *)
(*         match e1#node with *)
(*           | JCEvar v -> *)
(*               if v.vi_assigned then  *)
(*                 None *)
(*               else *)
(*                 Some(new location_with ~node:(JCLvar v) full_expr) *)
(*           | _ -> None *)

(* let timmutable_heap_location ef ~full_term t1 fi = (\* TODO: fef *\) *)
(*   match !current_mode with *)
(*     | MApprox -> None *)
(*     | MPrecise -> *)
(*         match t1#node with *)
(*           | JCTvar v -> *)
(*               if v.vi_assigned then  *)
(*                 None *)
(*               else *)
(*                 Some(new location_with ~node:(JCLvar v) full_term) *)
(*           | _ -> None *)


(******************************************************************************)
(*                             terms and assertions                           *)
(******************************************************************************)

let rec single_term ef t =
  let lab =
    match t#label with None -> LabelHere | Some lab -> lab
  in
  match t#node with
    | JCTvar vi ->
        let lab = if not vi.vi_assigned then LabelHere else lab in
        true,
        if vi.vi_static then
          add_global_effect lab ef vi
        else if not vi.vi_bound then
          add_local_effect lab ef vi
        else
          ef
    | JCToffset(_k,t,_st) ->
        let ac = tderef_alloc_class ~type_safe:true t in
        true,
        add_alloc_effect lab ef (ac, t#region)
    | JCTapp app ->
        let region_mem_assoc =
          make_region_mem_assoc app.app_fun.li_parameters
        in
        let ef_app =
          ef_assoc
            ~label_assoc:app.app_label_assoc
            ~region_assoc:app.app_region_assoc
            ~region_mem_assoc
            app.app_fun.li_effects
        in
        (if app.app_fun.li_name = "content" then
           Format.eprintf "**Effects for logic application content(): %a@."
           print_effect ef_app);
        true,
        ef_union ef_app ef
    | JCTderef(t1,lab,fi) ->
        let mc,ufi_opt = tderef_mem_class ~type_safe:true t1 fi in
        let mem = mc, t1#region in
        begin match term_immutable_location t with
          | Some loc ->
              let ef = add_precise_memory_effect lab ef (loc,mem) in
              (* TODO: treat union *)
              true, ef
          | None ->
              let ef = add_memory_effect lab ef mem in
              begin match mc,ufi_opt with
                | JCmem_plain_union _vi, _ ->
                    false, (* do not call on sub-terms of union *)
                    List.fold_left term ef (tforeign_union t1)
                | JCmem_field _, _
                | JCmem_bitvector, _ ->
                    true, ef
              end
        end
    | JCTdowncast (t, lab, st)
    | JCTsidecast (t, lab, st)
    | JCTinstanceof(t, lab, st) ->
        true,
        add_tag_effect lab ef (struct_root st, t#region)
    | JCTmatch(_t,ptl) ->
        true,
        List.fold_left pattern ef (List.map fst ptl)
    | JCTconst _ | JCTrange _ | JCTbinary _ | JCTunary _
    | JCTshift _ | JCTold _ | JCTat _ | JCTaddress _ | JCTbase_block _
    | JCTrange_cast _ | JCTrange_cast_mod _ | JCTreal_cast _ | JCTif _ | JCTlet _ ->
        true, ef

and term ef t =
  Iterators.fold_rec_term single_term ef t

let tag ef lab _t vi_opt r =
  match vi_opt with
    | None -> ef
    | Some vi -> add_tag_effect lab ef (vi,r)

let all_allocs_ac ac pc e =
  match ac with
  | JCalloc_bitvector -> [ac]
  | JCalloc_root rt ->
    match rt.ri_kind with
    | Rvariant -> all_allocs ~select:fully_allocated pc
    | RdiscrUnion ->
      Typing.typing_error ~loc:e#pos "Unsupported discriminated union, sorry"
    | RplainUnion -> [ac]

let all_mems_ac ac pc =
  match ac with
  | JCalloc_bitvector -> []
  | JCalloc_root rt ->
    match rt.ri_kind with
    | Rvariant -> all_memories ~select:fully_allocated pc
    | RdiscrUnion -> assert false
    | RplainUnion -> []

let all_tags_ac ac pc st =
  match ac with
  | JCalloc_bitvector -> [ struct_root st ]
  | JCalloc_root rt ->
      match rt.ri_kind with
        | Rvariant -> all_tags ~select:fully_allocated pc
        | RdiscrUnion -> assert false
        | RplainUnion -> [ struct_root st ]

let add_struct_alloc_effect lab ef t =
  let pc = JCtag (pointer_struct t#typ, []) in
  let ac = tderef_alloc_class ~type_safe:true t in
  let ef = List.fold_left (fun ef mc -> add_memory_effect lab ef (mc, t#region)) ef @@ all_mems_ac ac pc in
  List.fold_left (fun ef ac -> add_alloc_effect lab ef (ac, t#region)) ef @@ all_allocs_ac ac pc t

let single_assertion ef a =
  let lab =
    match a#label with None -> LabelHere | Some lab -> lab
  in
  match a#node with
    | JCAfresh(oldlab,lab,t,_n) ->
        true,
        let ef = add_struct_alloc_effect oldlab ef t in
        add_struct_alloc_effect lab ef t
    | JCAfreeable(lab,t) | JCAallocable(lab, t) ->
        true, add_struct_alloc_effect lab ef t
    | JCAinstanceof(t,lab,st) ->
        true,
        add_tag_effect lab ef (struct_root st,t#region)
    | JCAapp app ->
        let region_mem_assoc =
          make_region_mem_assoc app.app_fun.li_parameters
        in
        let ef_app =
          ef_assoc
            ~label_assoc:app.app_label_assoc
            ~region_assoc:app.app_region_assoc
            ~region_mem_assoc
            app.app_fun.li_effects
        in
        true,
        ef_union ef_app ef
    | JCAmutable(t,st,ta) ->
        true,
        add_mutable_effect
          (tag ef lab ta (* Yannick: really effect on tag here? *)
             (Some (struct_root st)) t#region)
          (JCtag(st, []))
    | JCAlet(_vi,_t,_p) ->
        true,ef
    | JCAmatch(_t,pal) ->
        true,
        List.fold_left pattern ef (List.map fst pal)
    | JCAeqtype (tag1, tag2, _) ->
      let add_tag_effect ef tag =
        match tag#node with
        | JCTtypeof (t, st) -> add_tag_effect lab ef (struct_root st, t#region)
        | JCTtag _ | JCTbottom -> ef
      in
      true, Pair.fold_left ~f:add_tag_effect ~init:ef (tag1, tag2)
    | JCAtrue | JCAfalse | JCAif _ | JCAbool_term _ | JCAnot _
    | JCAold _ | JCAat _ | JCAquantifier _ | JCArelation _
    | JCAand _ | JCAor _ | JCAiff _ | JCAimplies _
    | JCAsubtype _ ->
        true, ef

let assertion ef a =
  Iterators.fold_rec_term_and_assertion single_term single_assertion ef a


(******************************************************************************)
(*                                locations                                   *)
(******************************************************************************)

let single_term fef t =
  let cont,ef = single_term fef.fe_reads t in
  cont,{ fef with fe_reads = ef }

let single_assertion fef a =
  let cont,ef = single_assertion fef.fe_reads a in
  cont,{ fef with fe_reads = ef }

let add_memory_writes_noembedded lab (mc, _ as mcr) =
  match mc with
  | JCmem_field fi                   ->
    begin match fi.fi_type with
    | JCTpointer (_, Some _, Some _) -> add_memory_reads' lab mcr
    | _                              -> add_memory_writes' lab mcr
    end
  | _                                -> add_memory_writes' lab mcr

let rec single_location ~in_clause fef loc =
  let lab =
    match loc#label with
    | None -> LabelHere
    | Some lab -> lab
  in
  let add_deref x ?(lab = x#label |? lab) ?(r=x#region) get_mem_class fi =
    let r = if in_clause = `Allocates then r else x#region in
    let add_by_mc ~only_mem fef mc =
      match in_clause with
      | `Assigns ->
        fef |>
        add_memory_writes_noembedded lab (mc, r) |>
        (* Add effect on allocation table for [not_assigns] predicate *)
        Fn.on
          (not only_mem) @@
          add_alloc_reads' lab (alloc_class_of_mem_class mc, x#region)
      | `Allocates when not only_mem ->
        let ac = alloc_class_of_mem_class mc in
        add_alloc_writes lab fef (ac, x#region)
      | `Allocates -> fef
      | `Reads ->
        add_memory_reads lab fef (mc, r)
    in
    let mc, ufi_opt = get_mem_class ~type_safe:true x fi in
    add_by_mc ~only_mem:false fef mc |>
    match mc, ufi_opt with
    | JCmem_field _, Some ufi ->
      fun fef -> List.fold_left (add_by_mc ~only_mem:true) fef (overlapping_union_memories ufi)
    | JCmem_field _, None
    | JCmem_plain_union _, _
    | JCmem_bitvector, _ -> Fn.id
  in
  true,
  match loc#node with
  | JCLvar v ->
    begin match in_clause with
    | `Assigns when v.vi_assigned && v.vi_static -> add_global_writes lab fef v
    | `Assigns -> fef
    | `Allocates ->
      let ac = lderef_alloc_class ~type_safe:true loc in
      add_alloc_writes lab fef (ac, loc#region)
    (* If the variable is not assigned it's translated into logic function,
     * which is not compatible with reads clause in Why3.
     *)
    | `Reads when v.vi_assigned -> add_global_reads lab fef v
    | `Reads -> fef
    end
  | JCLderef (locs, lab, fi, r) -> add_deref locs ~lab ~r lderef_mem_class fi
  | JCLderef_term (t, fi) -> add_deref t tderef_mem_class fi
  | JCLsingleton t -> snd @@ single_term fef t
  | JCLat (loc, lab) ->
    loc#set_label @@ Some (loc#label |? lab);
    snd @@ single_location ~in_clause fef loc

let rec single_location_set ~in_clause fef locs =
  let single_location = single_location ~in_clause fef % location_with_node locs in
  let single_location_set = single_location_set ~in_clause fef in
  match locs#node with
  | JCLSvar v ->
    single_location (JCLvar v)
  | JCLSderef (locs, lab, fi, r) ->
    single_location (JCLderef (locs, lab, fi, r))
  | JCLSrange (ls, _, _) ->
    single_location_set ls
  | JCLSrange_term (t, _, _) ->
    single_term fef t
  | JCLSat (locs, lab) ->
    locs#set_label @@ Some (locs#label |? lab);
    single_location_set locs

let location ~in_clause fef loc =
  let fef =
    Iterators.fold_rec_location single_term
      (single_location ~in_clause) (single_location_set ~in_clause) fef loc
  in
  fef


(******************************************************************************)
(*                                expressions                                 *)
(******************************************************************************)

let rec expr fef e =
  Iterators.fold_rec_expr_and_term_and_assertion
    single_term single_assertion
    (single_location ~in_clause:`Assigns)
    (single_location_set ~in_clause:`Assigns)
    (fun (fef : fun_effect) e -> match e#node with
       | JCEvar v ->
           true,
           if v.vi_static then
             add_global_reads LabelHere fef v
           else
             add_local_reads LabelHere fef v
       | JCEassign_var(v,_e) ->
           true,
           if v.vi_static then
             add_global_writes LabelHere fef v
           else
             add_local_writes LabelHere fef v
       | JCEoffset(_k,e,_st) ->
           let ac = deref_alloc_class ~type_safe:true e in
           true,
           add_alloc_reads LabelHere fef (ac,e#region)
       | JCEapp app ->
           let fef_call = match app.call_fun with
             | JClogic_fun f ->
                 let region_mem_assoc =
                   make_region_mem_assoc f.li_parameters
                 in
                 fef_reads
                   (ef_assoc
                      ~label_assoc:app.call_label_assoc
                      ~region_assoc:app.call_region_assoc
                      ~region_mem_assoc
                      f.li_effects)
             | JCfun f ->
                 let region_mem_assoc =
                   make_region_mem_assoc (List.map snd f.fun_parameters)
                 in
                 fef_assoc
                   ~region_assoc:app.call_region_assoc f.fun_effects
                   ~region_mem_assoc
           in
           true,
           fef_union fef_call fef
       | JCEderef(e1,fi) ->
           let mc,ufi_opt = deref_mem_class ~type_safe:true e1 fi in
           let ac = deref_alloc_class ~type_safe:true e1 in
           let mem = mc, e1#region in
           begin match expr_immutable_location e with
             | Some loc ->
                 let fef =
                   add_precise_memory_reads LabelHere fef (loc, mem)
                 in
                 let fef = add_alloc_reads LabelHere fef (ac, e1#region) in
                 (* TODO: treat union *)
                 true, fef
             | None ->
                 let fef = add_memory_reads LabelHere fef mem in
                 let fef = add_alloc_reads LabelHere fef (ac, e1#region) in
                 begin match mc,ufi_opt with
                   | JCmem_plain_union _vi, _ ->
                       false, (* do not call on sub-expressions of union *)
                       List.fold_left expr fef (foreign_union e1)
                   | JCmem_field _, _
                   | JCmem_bitvector, _ ->
                       true, fef
                 end
           end
       | JCEassign_heap(e1,fi,_e2) ->
           let mc,ufi_opt = deref_mem_class ~type_safe:true e1 fi in
           let ac = deref_alloc_class ~type_safe:true e1 in
           let deref = new expr_with ~node:(JCEderef(e1,fi)) e in
           let mem = mc, e1#region in
           begin match expr_immutable_location deref with
             | Some loc ->
                 let fef =
                   add_precise_memory_writes LabelHere fef (loc,mem)
                 in
                 (* allocation table is read *)
                 let fef = add_alloc_reads LabelHere fef (ac,e1#region) in
                 (* TODO: treat union *)
                 true, fef
             | None ->
                 let fef = add_memory_writes LabelHere fef mem in
                 (* allocation table is read *)
                 let fef = add_alloc_reads LabelHere fef (ac,e1#region) in
                 begin match mc,ufi_opt with
                   | JCmem_plain_union _vi, _ ->
                       false, (* do not call on sub-expressions of union *)
                       List.fold_left expr fef (foreign_union e1)
                   | JCmem_field _fi, Some ufi ->
                       let mems = overlapping_union_memories ufi in
                       true,
                       List.fold_left
                         (fun fef mc ->
                            add_memory_writes LabelHere fef (mc,e1#region))
                         fef mems
                   | JCmem_field _, None | JCmem_bitvector, _ ->
                       true, fef
                 end
           end
       | JCEdowncast (e, st)
       | JCEsidecast (e, st)
       | JCEinstanceof (e, st) ->
           true,
           add_tag_reads LabelHere fef (struct_root st,e#region)
       | JCEshift (e1, _) ->
           true,
           let st =
             match e1#typ with
             | JCTpointer (JCtag (st, _), _, _) -> st
             | _ -> Typing.typing_error ~loc:e1#pos "Shifting of a non-pointer"
           in
           add_tag_reads LabelHere fef (struct_root st, e#region)
       | JCEalloc(_e1,st) ->
           let pc = JCtag(st,[]) in
           let ac = deref_alloc_class ~type_safe:true e in
           let fef =
             List.fold_left
               (fun fef mc -> add_memory_writes_noembedded LabelHere (mc,e#region) fef)
               fef
               (all_mems_ac ac pc)
           in
           let fef =
             List.fold_left
               (fun fef ac -> add_alloc_writes LabelHere fef (ac,e#region))
               fef
               (all_allocs_ac ac pc e)
           in
           true,
           List.fold_left
             (fun fef vi -> add_tag_writes LabelHere fef (vi,e#region))
             fef
             (all_tags_ac ac pc st)
       | JCEfree e ->
           let pc = pointer_class e#typ in
           let ac = alloc_class_of_pointer_class pc in
           let fef =
             List.fold_left (fun fef mc -> add_memory_reads LabelHere fef (mc,e#region)) fef (all_mems_ac ac pc)
           in
           true,
           List.fold_left
             (add_alloc_writes LabelHere %% Fn.id @@ Pair.cons' e#region)
             fef
             (all_allocs_ac ac pc e)
       | JCEreinterpret (e, st) ->
         (*  Current support for reinterpretation is very limited --
          *  it's supported only for two-level type hierarchies (e.g. void * -- other pointers),
          *  for pointers to structures with a single non-embedded field of an integral type.
          *  So actually only conversions between char <--> short <--> int <--> long and such are supported.
          *)
         let error msg = Typing.typing_error ~loc:e#pos ("Unsupported reinterpretation " ^^ msg) in
         let check_equal (type t) (module O : OrderedType with type t = t) v1 v2 =
           if O.equal v1 v2 then
             v1
           else
             error "(types from different hierarchies)"
         in
         let check_singleton msg =
           function
           | [s] -> s
           | _ -> error "for %s" msg
         in
         let pc =
           match st.si_hroot.si_root with
           | Some ri ->
             begin try
               check_equal (module PointerClass) (JCroot ri) @@ JCroot (pointer_class_root @@ pointer_class e#typ)
             with
             | Invalid_argument _ | Assert_failure _ -> error "(source type isn't a pointer or has no root)"
             end
           | None -> error "(destination type has no root)"
         in
         let ac =
           check_equal (module AllocClass) (alloc_class_of_pointer_class pc) @@
             deref_alloc_class ~type_safe:true e |>
           check_equal (module AllocClass) @@
             check_singleton "embedded fields" @@
               all_allocs ~select:fully_allocated pc
         in
         let ri = check_singleton "nested subtype" @@ all_tags ~select:fully_allocated pc in
         let fi1, fi2 =
           let st1 =
             match e#typ with
             | JCTpointer (JCtag (st, _), _, _) -> st
             | _ -> error "for a root pointer or a non-pointer"
           in
           Pair.map ~f:(check_singleton "several fields") (st1.si_fields, st.si_fields)
         in
         if not (is_integral_type fi1.fi_type && is_integral_type fi2.fi_type) then error "for non-integral field";
         let r = e#region in
         fef |>
         add_alloc_writes' LabelHere (ac, r) |>
         add_tag_writes' LabelHere (ri, r) |>
         add_memory_reads' LabelHere (JCmem_field fi1, r) |>
         add_memory_writes' LabelHere (JCmem_field fi2, r) |>
         fun fef -> true, { fef with fe_reinterpret = true }
       | JCEpack(st,e,_st) ->
           (* Assert the invariants of the structure
              => need the reads of the invariants *)
           let (_, invs) =
             StringHashtblIter.find
               Typing.structs_table st.si_name
           in
           let fef =
             List.fold_left
               (fun fef (li, _) ->
                  { fef with fe_reads =
                      ef_union fef.fe_reads li.li_effects })
               fef
               invs
           in
           (* Fields *)
           let fef = List.fold_left
             (fun fef fi ->
                match fi.fi_type with
                  | JCTpointer(pc, _, _) ->
                      (* Assert fields fully mutable
                         => need mutable and tag_table (of field) as reads *)
                      let fef = add_mutable_reads fef pc in
                      let fef =
                        add_tag_reads LabelHere fef
                          (pointer_class_root pc,e#region)
                      in
                      (* Modify field's "committed" field
                         => need committed (of field) as reads and writes *)
                      let fef = add_committed_reads fef pc in
                      let fef = add_committed_writes fef pc in
                      (* ...and field as reads *)
                      add_memory_reads LabelHere fef (JCmem_field fi,e#region)
                  | _ -> fef)
             fef
             st.si_fields in
           (* Change structure mutable => need mutable as reads and writes *)
           let fef = add_mutable_reads fef (JCtag(st, [])) in
           let fef = add_mutable_writes fef (JCtag(st, [])) in
           (* And that's all *)
           true, fef
       | JCEunpack(st,e,_st) ->
           (* Change structure mutable => need mutable as reads and writes *)
           let fef = add_mutable_reads fef (JCtag(st, [])) in
           let fef = add_mutable_writes fef (JCtag(st, [])) in
           (* Fields *)
           let fef = List.fold_left
             (fun fef fi ->
                match fi.fi_type with
                  | JCTpointer(st, _, _) ->
                      (* Modify field's "committed" field
                         => need committed (of field) as reads and writes *)
                      let fef = add_committed_reads fef st in
                      let fef = add_committed_writes fef st in
                      (* ...and field as reads *)
                      add_memory_reads LabelHere fef (JCmem_field fi,e#region)
                  | _ -> fef)
             fef
             st.si_fields in
           (* And that's all *)
           true, fef
       | JCEthrow(exc,_e_opt) ->
           true,
           add_exception_effect fef exc
       | JCEtry(s,catches,finally) ->
           let fef = expr fef s in
           let fef =
             List.fold_left
               (fun fef (exc,_vi_opt,_s) ->
                  { fef with
                      fe_raises = ExceptionSet.remove exc fef.fe_raises }
               ) fef catches
           in
           let fef =
             List.fold_left
               (fun fef (_exc,_vi_opt,s) -> expr fef s) fef catches
           in
           false, (* do not recurse on try-block due to catches *)
           expr fef finally
       | JCEmatch(_e, psl) ->
           let pef = List.fold_left pattern empty_effects (List.map fst psl) in
           true,
           { fef with fe_reads = ef_union fef.fe_reads pef }
       | JCEbinary (e1, ((`Beq | `Bneq), `Pointer), e2) ->
         [e1; e2] |>
         List.filter (fun e -> e#node <> JCEconst JCCnull) |>
         List.map (fun e -> deref_alloc_class ~type_safe:true e, e#region) |>
         List.fold_left (add_alloc_reads LabelHere) fef |>
         fun fef -> true, fef
       | JCEloop _ | JCElet _ | JCEassert _ | JCEcontract _ | JCEblock _
       | JCEconst _  | JCEif _ | JCErange_cast _ | JCErange_cast_mod _
       | JCEreal_cast _ | JCEunary _ | JCEaddress _ | JCEbinary _
       | JCEreturn_void  | JCEreturn _ | JCEbase_block _ | JCEfresh _ ->
           true, fef
    ) fef e

let behavior fef (_pos,_id,b) =
  let ita =
    Iterators.fold_rec_term_and_assertion single_term single_assertion
  in
  let itl =
    Iterators.fold_rec_location single_term
      (single_location ~in_clause:`Assigns)
      (single_location_set ~in_clause:`Assigns)
  in
  let itl_alloc =
    Iterators.fold_rec_location single_term
      (single_location ~in_clause:`Allocates)
      (single_location_set ~in_clause:`Allocates)
  in
  let fef = Option.fold ~f:ita ~init:fef b.b_assumes in
  let fef =
    Option.fold
      ~f:(fun fef (_,locs) -> List.fold_left itl fef locs)
      ~init:fef
      b.b_assigns
  in
  let fef =
    Option.fold
      ~f:(fun fef (_,locs) ->
        List.fold_left itl_alloc fef locs)
      ~init:fef
      b.b_allocates
  in
  let fef = ita fef b.b_ensures in
  let fef = ita fef b.b_free_ensures in
  Option.fold ~f:add_exception_effect ~init:fef b.b_throws




let spec s fef =
  let fef =
    List.fold_left behavior fef
      (s.fs_default_behavior :: s.fs_behavior)
  in
  let fef = { fef with fe_reads = Option.fold_right' ~f:((Fn.flip term) % fst) s.fs_decreases fef.fe_reads } in
  let fef = { fef with fe_reads = assertion fef.fe_reads s.fs_requires } in
  { fef with fe_reads = assertion fef.fe_reads s.fs_free_requires }




(* Type invariant added to precondition for pointer parameters with bounds.
   Therefore, add allocation table to reads. *)
let parameter fef v =
  match v.vi_type with
  | JCTpointer (pc, Some _i, Some _j) ->
    let ac = alloc_class_of_pointer_class pc in
    add_alloc_reads LabelOld fef (ac, v.vi_region)
  | _ -> fef

let parameter' v fef = parameter fef v

(******************************************************************************)
(*                                 fix-point                                  *)
(******************************************************************************)

let li_effects_from_assertion fi ax_effects =
  let li_effects_from_app f acc x =
    match f x#node with
    | Some app when Logic_info.equal app.app_fun fi ->
      ef_union (ef_filter_labels app.app_label_assoc ax_effects) acc
    | Some _ | None -> acc
  in
  Iterators.fold_term_and_assertion
    (li_effects_from_app
      (function
       | JCTapp app -> Some app
       | _ -> None))
    (li_effects_from_app
      (function
       | JCAapp app -> Some app
       | _ -> None))

let axiomatic_decl_effect, li_effects_from_ax_decl =
  let with_axiomatic_decl f acc d =
    match d with
    | Typing.ADprop (_, _, _, `Lemma, _) -> acc
    (* Lemma effects are never counted in function effects (even for UIFs) *)
    | Typing.ADprop (_, _, _, `Axiom, a) -> f acc a
  in
  with_axiomatic_decl assertion,
  fun fi ax_effects -> with_axiomatic_decl (li_effects_from_assertion fi ax_effects)

let li_effects_from_axiomatic fi ax acc =
  let open Typing in
  try
    let decls = (StringHashtblIter.find axiomatics_table ax).axiomatics_decls in
    let ef = List.fold_left axiomatic_decl_effect empty_effects decls in
    List.fold_left (li_effects_from_ax_decl fi ef) acc decls
  with
  | Not_found ->
    Options.jc_error
      Loc.dummy_position
      "effects_from_axiomatic: can't find axiomatic: %s" ax

exception Dangling_region of region * Loc.position * effect * string * Loc.position

let check_li_effects_from_axiomatic li =
  let check_decl d =
    let check_app ax_pos ax_name app_pos app =
      let is_dangling =
        let region_assoc = app.app_region_assoc in
        fun r -> not @@ Option.is_some (transpose_region ~region_assoc r)
      in
      ignore @@ ef_filter_by_region
        (fun r ->
           if is_dangling r then
             let ef = ef_filter_by_region is_dangling li.li_effects in
             raise @@ Dangling_region (r, app_pos, ef, ax_name, ax_pos)
           else false)
        li.li_effects
    in
    match d with
    | Typing.ADprop (pos, name, _, _, a) ->
      let check_app = check_app pos name in
      Iterators.iter_term_and_assertion
        (fun t -> match t#node with JCTapp app when Logic_info.equal app.app_fun li -> check_app t#pos app | _ -> ())
        (fun a -> match a#node with JCAapp app when Logic_info.equal app.app_fun li -> check_app a#pos app | _ -> ())
        a
  in
  try
    Option.iter
      Typing.(fun ax -> List.iter check_decl (StringHashtblIter.find axiomatics_table ax).axiomatics_decls)
      li.li_axiomatic
  with
  | Dangling_region (r, app_pos, ef, ax_name, ax_pos) ->
    Options.jc_warning
      app_pos
      ("Encountered dangling region \"%s\"@[<4>@ in logic function \"%s\"@ " ^^
       "at %a@ in axiom \"%s\"@ (defined at %a).@\n" ^^
       "It seems the function \"%s\"@ should have an explicit reads clause specifying variable(s) of type %a.@\n" ^^
       "The inferred side effect of the logic function is:@ %a@]")
      r.r_name
      li.li_name
      Loc.gen_report_position app_pos
      ax_name
      Loc.gen_report_position ax_pos
      li.li_name
      print_type r.r_type
      print_effect ef
  | Not_found ->
    Options.jc_error
      Loc.dummy_position
      "check_effects_from_axiomatic: can't find axiomatic for function: %s" li.li_name

let logic_fun_effects f =
  let f, ta = IntHashtblIter.find Typing.logic_functions_table f.li_tag in
  let ef = f.li_effects in
  let ef =
    match ta with
    | JCTerm t -> term ef t
    | JCAssertion a -> assertion ef a
    | JCInductive l ->
      let ax_effects =
        List.fold_left
          (fun ef (_, _, a) -> assertion ef a)
          empty_effects
          l
      in
      List.fold_left (fun acc (_, _, a) -> li_effects_from_assertion f ax_effects acc a) ef l
    | JCNone ->
      begin match f.li_axiomatic with
        (* axiomatic def in a *)
        | Some a ->
          let ef = li_effects_from_axiomatic f a ef in
          check_li_effects_from_axiomatic f;
          ef
        | None -> (* not allowed outside axiomatics *)
          Options.jc_error
            Loc.dummy_position
            "Undefined pure logic function %s declared outside axiomatic"
            f.li_name
      end
    | JCReads loclist ->
      List.fold_left
        (fun ef loc ->
           ef_union ef (location ~in_clause:`Reads empty_fun_effect loc).fe_reads)
        ef
        loclist
  in
  if same_effects ef f.li_effects then
    `Final ef
  else begin
    f.li_effects <- ef;
    `Provisional ef
  end

let fun_effects f =
  let f, _pos, s, e_opt = IntHashtblIter.find Typing.functions_table f.fun_tag in
  f.fun_effects |>
  spec s |>
  Option.fold_left' ~f:expr e_opt |>
  List.fold_right parameter' (List.map snd f.fun_parameters) |>
  fun fef ->
  if same_feffects fef f.fun_effects then
    `Final fef
  else begin
    f.fun_effects <- fef;
    `Provisional fef
  end

let finished f acc x =
  acc &&
  match f x with
  | `Provisional _ -> false
  | `Final _ -> true

let rec fix f =
  if not (f ()) then
    fix f

let logic_effects funs =
  List.iter (fun f -> f.li_effects <- empty_effects) funs;
  fix
    (fun () ->
       Options.lprintf "Effects: doing one iteration@.";
       List.fold_left (finished logic_fun_effects) true funs);
  Options.lprintf "Effects: fixpoint reached@.";
  List.iter
    (fun f ->
       Options.lprintf "Effects for logic function %s:@\n%a@."
         f.li_name print_effect f.li_effects)
    funs

let function_effects funs =
  List.iter (fun f -> f.fun_effects <- empty_fun_effect) funs;
  let iterate () =
    fix
      (fun () ->
         Options.lprintf "Effects: doing one iteration...@.";
         List.fold_left (finished fun_effects) true funs)
  in

  (* Compute raw effects to bootstrap *)
  current_mode := MApprox;
  iterate ();
  (* Compute precise effects *)
  current_mode := MPrecise;
  iterate ();
  (* Reset mode to raw effects for individual calls *)
  current_mode := MApprox;
  Options.lprintf "Effects: fixpoint reached@.";

  List.iter
    (fun f ->
       Options.lprintf
         "Effects for function %s:@\n@[ reads: %a@]@\n@[ writes: %a@]@\n@[ raises: %a@]@."
         f.fun_name
         print_effect f.fun_effects.fe_reads
         print_effect f.fun_effects.fe_writes
         (print_list comma print_exception)
         (ExceptionSet.elements f.fun_effects.fe_raises))
    funs

let is_poly_mem_param =
  function
  | { vi_type = JCTpointer (JCtag ({ si_fields = []; _ }, _), _, _); _ } ->
    true
  | _ -> false

let is_poly_mem_function f =
  f.li_axiomatic <> None &&
  List.exists is_poly_mem_param f.li_parameters

let poly_mem_regions f =
  List.filter is_poly_mem_param f.li_parameters |>
  List.map @@ function { vi_region = r; _ } -> r


let restrict_poly_mems_in_assertion mm =
  let map_app (* app *) =
    let map_f (* f *) =
      let memo f (* fi *) =
        let memo = Hashtbl.create 5 in
        fun fi ->
        try Hashtbl.find memo fi.li_tag
        with Not_found ->
          let r = f fi in
          Hashtbl.replace memo fi.li_tag r;
          r
      in
      memo @@
      fun f ->
      let mems =
        let poly_regs = poly_mem_regions f in
        MemoryMap.(
          f.li_effects.e_memories |>
          filter (fun (_, r as key) _ -> not (List.exists (Region.equal r) poly_regs) || mem key mm) |>
          merge (Fn.curry @@ fst) mm)
      in
      { f with li_effects = { f.li_effects with e_memories = mems }}
   in
   fun app -> { app with app_fun = map_f app.app_fun }
  in
  Iterators.map_term_and_assertion
    (fun a ->
      match a#node with
      | JCAapp app when is_poly_mem_function app.app_fun ->
        assertion_with_node a @@ JCAapp (map_app app)
      | _ -> a)
    (fun t ->
      match t#node with
      | JCTapp app when is_poly_mem_function app.app_fun ->
        term_with_node t @@ JCTapp (map_app app)
      | _ -> t)

let restrict_poly_mems_in_axiomatic_decl mm =
  Typing.(fun (ADprop (pos, name, ls, kind, a)) -> ADprop (pos, name, ls, kind, restrict_poly_mems_in_assertion mm a))
