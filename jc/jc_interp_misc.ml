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

open Output

(*
open Jc_env
open Jc_ast
open Jc_pervasives
open Jc_iterators
*)

open Jc_ast
open Jc_pervasives
open Jc_envset
open Jc_env
open Jc_fenv
open Jc_region
open Jc_name
open Jc_struct_tools

(* The following functions should be eliminated eventually, but before,
 * effect.ml must be redone.
 * They are here, and not in Jc_name, so that Krakatoa do not depends on
 * Jc_typing. *)

let find_struct a =
(*
  Format.printf "[find_struct] %s@." a;
*)
  fst (Hashtbl.find Jc_typing.structs_table a)

let find_variant a =
  Hashtbl.find Jc_typing.variants_table a

let find_pointer_class a =
  try
    JCtag (find_struct a, []) (* TODO: fill parameters ? *)
  with Not_found ->
    JCvariant (find_variant a)

let mutable_name2 a =
  mutable_name (JCtag (find_struct a, []))

let committed_name2 a =
  committed_name (JCtag (find_struct a, []))



(******************************************************************************)
(*                              environment                                   *)
(******************************************************************************)

let current_function = ref None
let set_current_function f = current_function := Some f
let reset_current_function () = current_function := None
let get_current_function () = 
  match !current_function with None -> assert false | Some f -> f

let current_behavior : string option ref = ref None
let set_current_behavior behav = current_behavior := Some behav
let reset_current_behavior () = current_behavior := None
let get_current_behavior () = 
  match !current_behavior with None -> assert false | Some behav -> behav
let compatible_with_current_behavior = function
  | [] -> true
  | ls -> List.exists (fun behav -> behav = get_current_behavior ()) ls
let safety_checking () = get_current_behavior () = "safety"

let current_spec : fun_spec option ref = ref None
let set_current_spec s = current_spec := Some s
let reset_current_spec () = current_spec := None
let get_current_spec () = 
  match !current_spec with None -> assert false | Some s -> s


(******************************************************************************)
(*                                   types                                    *)
(******************************************************************************)

(* basic model types *)

let why_integer_type = simple_logic_type "int"

let variant_model_type vi =
  simple_logic_type (variant_type_name vi)

let struct_model_type st = 
  variant_model_type (struct_variant st)

let pointer_class_model_type pc = 
  variant_model_type (pointer_class_variant pc)

let bitvector_type = simple_logic_type bitvector_type_name

let alloc_class_type = function
  | JCalloc_struct vi -> variant_model_type vi
  | JCalloc_union vi -> variant_model_type vi
  | JCalloc_bitvector -> bitvector_type

let memory_class_type mc = 
  alloc_class_type (alloc_class_of_mem_class mc)

(* raw types *)

let raw_pointer_type ty' =
  { logic_type_name = pointer_type_name;
    logic_type_args = [ty']; }

let raw_pset_type ty' =
  { logic_type_name = pset_type_name;
    logic_type_args = [ty']; }

let raw_alloc_table_type ty' =
  { logic_type_name = alloc_table_type_name;
    logic_type_args = [ty']; }

let raw_tag_table_type ty' = 
  { logic_type_name = tag_table_type_name;
    logic_type_args = [ty']; }

let raw_tag_id_type ty' = 
  { logic_type_name = tag_id_type_name;
    logic_type_args = [ty']; }

let raw_memory_type ty1' ty2' =
  { logic_type_name = memory_type_name;
    logic_type_args = [ty1';ty2'] }

(* translation *)

let tr_native_type = function
  | Tunit -> "unit"
  | Tboolean -> "bool"
  | Tinteger -> "int"
  | Treal -> "real"
  | Tstring -> "string"

let tr_base_type = function
  | JCTnative ty -> 
      simple_logic_type (tr_native_type ty)
  | JCTlogic s -> 
      simple_logic_type s
  | JCTenum ri -> 
      simple_logic_type ri.jc_enum_info_name
  | JCTpointer(pc, _, _) ->
      raw_pointer_type (pointer_class_model_type pc)
  | JCTnull | JCTany -> assert false
  | JCTtype_var _ -> assert false (* TODO (need environment) *)

let tr_type ty = Base_type (tr_base_type ty)

(* model types *)

let pointer_type pc = raw_pointer_type (pointer_class_model_type pc)

let pset_type ac = raw_pset_type (alloc_class_type ac)

let alloc_table_type ac = raw_alloc_table_type (alloc_class_type ac)

let tag_table_type vi = raw_tag_table_type (variant_model_type vi)

let tag_id_type vi = raw_tag_id_type (variant_model_type vi)

let memory_type mc = 
  let value_type = match mc with
    | JCmem_field fi -> tr_base_type fi.jc_field_info_type
    | JCmem_union _vi -> bitvector_type
    | JCmem_bitvector -> bitvector_type
  in
  raw_memory_type (memory_class_type mc) value_type

(* query model types *)

let is_alloc_table_type ty' = ty'.logic_type_name = alloc_table_type_name

let is_tag_table_type ty' = ty'.logic_type_name = tag_table_type_name

let is_memory_type ty' = ty'.logic_type_name = memory_type_name

let deconstruct_memory_type_args ty =
  match ty.logic_type_args with [t;v] -> t,v | _ -> assert false

	


(******************************************************************************)
(*                                 variables                                  *)
(******************************************************************************)

let lvar_name ~constant ~label_in_name ?label_assoc lab n =
  let lab = match label_assoc with
    | None -> lab 
    | Some assoc -> try List.assoc lab assoc with Not_found -> lab
  in	
  if label_in_name && not constant then 
    match lab with
      | LabelHere -> n
      | LabelOld -> assert false
      | LabelPre -> n ^ "_at_Pre"
      | LabelPost -> n ^ "_at_Post"
      | LabelName lab -> n ^ "_at_" ^ lab.label_info_final_name
  else n

let lvar ~constant ~label_in_name lab n =
  let n = lvar_name ~constant ~label_in_name lab n in
  if label_in_name || constant then 
    LVar n
  else match lab with 
    | LabelHere -> LVar n
    | LabelOld -> LVarAtLabel(n,"")
    | LabelPre -> LVarAtLabel(n,"init")
    | LabelPost -> LVar n
    | LabelName lab -> LVarAtLabel(n,lab.label_info_final_name)

(* simple variables *)

let plain_var n = Var n
let deref_var n = Deref n

let var_name' = function
  | Var n | Deref n -> n
  | _ -> assert false

let var v =
  if v.jc_var_info_assigned 
  then deref_var v.jc_var_info_final_name
  else plain_var v.jc_var_info_final_name

let param v = 
  plain_var v.jc_var_info_final_name, tr_base_type v.jc_var_info_type 

let tvar_name ~label_in_name lab v = 
  lvar_name ~constant:(not v.jc_var_info_assigned) ~label_in_name
    lab v.jc_var_info_final_name

let tvar ~label_in_name lab v = 
  lvar ~constant:(not v.jc_var_info_assigned) ~label_in_name
    lab v.jc_var_info_final_name

let tparam ~label_in_name lab v = 
  tvar_name ~label_in_name lab v, tr_base_type v.jc_var_info_type 

(* model variables *)

let mutable_memory infunction (mc,r) =
  if Region.polymorphic r then
    MemoryMap.mem (mc,r)
      infunction.jc_fun_info_effects.jc_writes.jc_effect_memories
  else true

let mutable_alloc_table infunction (ac,r) =
  if Region.polymorphic r then
    AllocMap.mem (ac,r)
      infunction.jc_fun_info_effects.jc_writes.jc_effect_alloc_table
  else true

let mutable_tag_table infunction (vi,r) =
  if Region.polymorphic r then
    TagMap.mem (vi,r)
      infunction.jc_fun_info_effects.jc_writes.jc_effect_tag_table
  else true

let plain_memory_var (mc,r) = Var (memory_name (mc,r))
let deref_memory_var (mc,r) = Deref (memory_name (mc,r))

let memory_var (mc,r) =
  if mutable_memory (get_current_function ()) (mc,r) then
    deref_memory_var (mc,r)
  else plain_memory_var (mc,r)

let tmemory_var ~label_in_name lab (mc,r) =
  let mem = memory_name (mc,r) in
  let constant = match !current_function with
    | None -> false (* Variables at different labels should be different *)
    | Some infunction -> not (mutable_memory infunction (mc,r))
  in
  lvar ~constant ~label_in_name lab mem

let tmemory_param ~label_in_name lab (mc,r) =
  let mem = memory_name (mc,r) in
  let constant = match !current_function with
    | None -> false (* Variables at different labels should be different *)
    | Some infunction -> not (mutable_memory infunction (mc,r))
  in
  let n = lvar_name ~constant ~label_in_name lab mem in
  let ty' = memory_type mc in
  n, ty'

let plain_alloc_table_var (ac,r) = Var (alloc_table_name (ac,r))
let deref_alloc_table_var (ac,r) = Deref (alloc_table_name (ac,r))

let alloc_table_var (ac,r) =
  if mutable_alloc_table (get_current_function ()) (ac,r) then
    deref_alloc_table_var (ac,r)
  else plain_alloc_table_var (ac,r)

let talloc_table_var ~label_in_name lab (ac,r) =
  let alloc = alloc_table_name (ac,r) in
  let constant = match !current_function with
    | None -> false (* Variables at different labels should be different *)
    | Some infunction -> not (mutable_alloc_table infunction (ac,r))
  in
  lvar ~constant ~label_in_name lab alloc

let talloc_table_param ~label_in_name lab (ac,r) =
  let mem = alloc_table_name (ac,r) in
  let constant = match !current_function with
    | None -> false (* Variables at different labels should be different *)
    | Some infunction -> not (mutable_alloc_table infunction (ac,r))
  in
  let n = lvar_name ~constant ~label_in_name lab mem in
  let ty' = alloc_table_type ac in
  n, ty'

let plain_tag_table_var (vi,r) = Var (tag_table_name (vi,r))
let deref_tag_table_var (vi,r) = Deref (tag_table_name (vi,r))

let tag_table_var (vi,r) =
  if mutable_tag_table (get_current_function ()) (vi,r) then
    deref_tag_table_var (vi,r)
  else plain_tag_table_var (vi,r)

let ttag_table_var ~label_in_name lab (vi,r) =
  let tag = tag_table_name (vi,r) in
  let constant = match !current_function with
    | None -> false (* Variables at different labels should be different *)
    | Some infunction -> not (mutable_tag_table infunction (vi,r))
  in
  lvar ~constant ~label_in_name lab tag

let ttag_table_param ~label_in_name lab (vi,r) =
  let mem = tag_table_name (vi,r) in
  let constant = match !current_function with
    | None -> false (* Variables at different labels should be different *)
    | Some infunction -> not (mutable_tag_table infunction (vi,r))
  in
  let n = lvar_name ~constant ~label_in_name lab mem in
  let ty' = tag_table_type vi in
  n, ty'


(******************************************************************************)
(*                               call arguments                               *)
(******************************************************************************)

type param_or_effect_mode = MParam | MLocal | MEffect

let add_alloc_table_argument ~mode ~no_deref (ac,distr) region_assoc acc =
  let allocvar = if no_deref then plain_alloc_table_var else alloc_table_var in
  let ty' = alloc_table_type ac in
  if Region.polymorphic distr then
    try 
      (* Polymorphic allocation table. Both passed in argument by the caller, 
	 and counted as effect. *)
      let locr = RegionList.assoc distr region_assoc in
      match mode with
	| MParam | MEffect -> (allocvar (ac,locr), ty') :: acc 
	| MLocal -> acc
    with Not_found -> 
      (* MLocal allocation table. Neither passed in argument by the caller, 
	 nor counted as effect. *)
      match mode with
	| MParam | MEffect -> acc
	| MLocal -> (allocvar (ac,distr), ty') :: acc 
  else 
    (* Constant allocation table. Not passed in argument by the caller, 
       but counted as effect. *)
    match mode with
      | MParam | MLocal -> acc
      | MEffect -> (allocvar (ac,distr), ty') :: acc 

let write_alloc_tables ~mode ~callee_writes ~region_assoc =
  AllocMap.fold
    (fun (ac,distr) _labs acc ->
       add_alloc_table_argument 
	 ~mode ~no_deref:true (ac,distr) region_assoc acc
    ) callee_writes.jc_effect_alloc_table []

let read_alloc_tables ~mode ~callee_writes ~callee_reads ~region_assoc =
  AllocMap.fold
    (fun (ac,distr) _labs acc ->
       if AllocMap.mem (ac,distr) callee_writes.jc_effect_alloc_table then
	 (* Allocation table is written, thus it is already taken care of
	    as a parameter. *)
	 match mode with
	   | MParam | MLocal -> acc
	   | MEffect ->
	       add_alloc_table_argument 
		 ~mode ~no_deref:false (ac,distr) region_assoc acc
       else if mutable_alloc_table (get_current_function ()) (ac,distr) then
	 add_alloc_table_argument 
	   ~mode ~no_deref:false (ac,distr) region_assoc acc
       else
	 (* Allocation table is immutable, thus it is not passed by
	    reference. As such, it cannot be counted in effects. *)
	 match mode with
	   | MParam | MLocal ->
	       add_alloc_table_argument 
		 ~mode ~no_deref:false (ac,distr) region_assoc acc
	   | MEffect -> acc
    ) callee_reads.jc_effect_alloc_table []

let add_tag_table_argument ~mode ~no_deref (vi,distr) region_assoc acc =
  let tagvar = if no_deref then plain_tag_table_var else tag_table_var in
  let ty' = tag_table_type vi in
  if Region.polymorphic distr then
    try 
      (* Polymorphic tag table. Both passed in argument by the caller, 
	 and counted as effect. *)
      let locr = RegionList.assoc distr region_assoc in
      match mode with
	| MParam | MEffect -> (tagvar (vi,locr), ty') :: acc
	| MLocal -> acc
    with Not_found -> 
      (* MLocal tag table. Neither passed in argument by the caller, 
	 nor counted as effect. *)
      match mode with
	| MParam | MEffect -> acc
	| MLocal -> (tagvar (vi,distr), ty') :: acc 
  else 
    (* Constant tag table. Not passed in argument by the caller, 
       but counted as effect. *)
    match mode with
      | MParam | MLocal -> acc
      | MEffect -> (tagvar (vi,distr), ty') :: acc 

let write_tag_tables ~mode ~callee_writes ~region_assoc =
  TagMap.fold
    (fun (vi,distr) _labs acc ->
       add_tag_table_argument 
	 ~mode ~no_deref:true (vi,distr) region_assoc acc
    ) callee_writes.jc_effect_tag_table []

let read_tag_tables ~mode ~callee_writes ~callee_reads ~region_assoc =
  TagMap.fold
    (fun (vi,distr) _labs acc ->
       if TagMap.mem (vi,distr) callee_writes.jc_effect_tag_table then
	 (* Tag table is written, thus it is already taken care of
	    as a parameter. *)
	 match mode with
	   | MParam | MLocal -> acc
	   | MEffect ->
	       add_tag_table_argument 
		 ~mode ~no_deref:false (vi,distr) region_assoc acc
       else if mutable_tag_table (get_current_function ()) (vi,distr) then
	 add_tag_table_argument 
	   ~mode ~no_deref:false (vi,distr) region_assoc acc
       else
	 (* Tag table is immutable, thus it is not passed by
	    reference. As such, it cannot be counted in effects. *)
	 match mode with
	   | MParam | MLocal ->
	       add_tag_table_argument 
		 ~mode ~no_deref:false (vi,distr) region_assoc acc
	   | MEffect -> acc
    ) callee_reads.jc_effect_tag_table []

let add_memory_argument ~mode ~no_deref (mc,distr) region_assoc acc =
  let memvar = if no_deref then plain_memory_var else memory_var in
  let ty' = memory_type mc in
  if Region.polymorphic distr then
    try 
      (* Polymorphic memory. Both passed in argument by the caller, 
	 and counted as effect. *)
      let locr = RegionList.assoc distr region_assoc in
      match mode with
	| MParam | MEffect -> (memvar (mc,locr), ty') :: acc
	| MLocal -> acc
    with Not_found -> 
      (* MLocal memory. Neither passed in argument by the caller, 
	 nor counted as effect. *)
      match mode with
	| MParam | MEffect -> acc
	| MLocal -> (memvar (mc,distr), ty') :: acc 
  else 
    (* Constant memory. Not passed in argument by the caller, 
       but counted as effect. *)
    match mode with
      | MParam | MLocal -> acc
      | MEffect -> (memvar (mc,distr), ty') :: acc 

let write_memories ~mode ~callee_writes ~region_assoc =
  MemoryMap.fold
    (fun (mc,distr) _labs acc -> 
       add_memory_argument 
	 ~mode ~no_deref:true (mc,distr) region_assoc acc
    ) callee_writes.jc_effect_memories []

let read_memories ~mode ~callee_writes ~callee_reads ~region_assoc =
  MemoryMap.fold
    (fun (mc,distr) _labs acc ->
       if MemoryMap.mem (mc,distr) callee_writes.jc_effect_memories then
	 (* Memory is written, thus it is already taken care of
	    as a parameter. *)
	 match mode with
	   | MParam | MLocal -> acc
	   | MEffect ->
	       add_memory_argument 
		 ~mode ~no_deref:false (mc,distr) region_assoc acc
       else if mutable_memory (get_current_function ()) (mc,distr) then
	 add_memory_argument 
	   ~mode ~no_deref:false (mc,distr) region_assoc acc
       else
	 (* Memory is immutable, thus it is not passed by
	    reference. As such, it cannot be counted in effects. *)
	 match mode with
	   | MParam | MLocal ->
	       add_memory_argument 
		 ~mode ~no_deref:false (mc,distr) region_assoc acc
	   | MEffect -> acc
    ) callee_reads.jc_effect_memories []

let write_globals ~callee_writes =
  VarMap.fold
    (fun v _labs acc -> param v :: acc) callee_writes.jc_effect_globals []

let read_globals ~callee_reads =
  VarMap.fold
    (fun v _labs acc -> param v :: acc) callee_reads.jc_effect_globals []

(* Yannick: change this to avoid recovering the real type from its name
   in mutable and committed effects *)

let write_mutable callee_writes =
  StringSet.fold
    (fun v acc -> (mutable_name2 v)::acc) callee_writes.jc_effect_mutable []

let read_mutable callee_reads =
  StringSet.fold
    (fun v acc -> (mutable_name2 v)::acc) callee_reads.jc_effect_mutable []

let write_committed callee_writes =
  StringSet.fold
    (fun v acc -> (committed_name2 v)::acc) callee_writes.jc_effect_committed []

let read_committed callee_reads =
  StringSet.fold
    (fun v acc -> (committed_name2 v)::acc) callee_reads.jc_effect_committed []

let write_model_parameters ~mode ~callee_reads ~callee_writes ~region_assoc =
  let write_allocs = 
    write_alloc_tables ~mode ~callee_writes ~region_assoc 
  in
  let write_tags = 
    write_tag_tables ~mode ~callee_writes ~region_assoc 
  in
  let write_mems = 
    write_memories ~mode ~callee_writes ~region_assoc 
  in
  let write_globs = match mode with
    | MParam | MLocal -> []
    | MEffect -> write_globals ~callee_writes
  in
  write_allocs @ write_tags @ write_mems @ write_globs

let write_parameters ?region_assoc ?region_list ~callee_reads ~callee_writes =
  let region_assoc = match region_assoc,region_list with
    | Some region_assoc, None -> region_assoc
    | None, Some region_list -> List.map (fun r -> (r,r)) region_list
    | _ -> assert false
  in
  let vars' = 
    write_model_parameters 
      ~mode:MParam ~callee_reads ~callee_writes ~region_assoc
  in
  List.map (function (Var n,ty') -> (n,ty') | _ -> assert false) vars'

let write_arguments ?region_assoc ?region_list ~callee_reads ~callee_writes =
  let region_assoc = match region_assoc,region_list with
    | Some region_assoc, None -> region_assoc
    | None, Some region_list -> List.map (fun r -> (r,r)) region_list
    | _ -> assert false
  in
  let vars' = 
    write_model_parameters 
      ~mode:MParam ~callee_reads ~callee_writes ~region_assoc
  in
  List.map fst vars'

let write_locals ?region_assoc ?region_list ~callee_reads ~callee_writes =
  let region_assoc = match region_assoc,region_list with
    | Some region_assoc, None -> region_assoc
    | None, Some region_list -> List.map (fun r -> (r,r)) region_list
    | _ -> assert false
  in
  let vars' =
    write_model_parameters 
      ~mode:MLocal ~callee_reads ~callee_writes ~region_assoc
  in
  List.map (function (Var n,ty') -> (n,ty') | _ -> assert false) vars'

let write_effects ~callee_reads ~callee_writes ~region_list =
  let region_assoc = List.map (fun r -> (r,r)) region_list in
  let vars' = 
    write_model_parameters 
      ~mode:MEffect ~callee_reads ~callee_writes ~region_assoc
  in
  List.map (function (Var n,_ty') -> n | _ -> assert false) vars'

let read_model_parameters ~mode ~callee_reads ~callee_writes ~region_assoc =
  let read_allocs = 
    read_alloc_tables ~mode ~callee_reads ~callee_writes ~region_assoc 
  in
  let read_tags = 
    read_tag_tables ~mode ~callee_reads ~callee_writes ~region_assoc 
  in
  let read_mems =
    read_memories ~mode ~callee_reads ~callee_writes ~region_assoc 
  in
  let read_globs = match mode with
    | MParam | MLocal -> []
    | MEffect -> read_globals ~callee_reads
  in
  read_allocs @ read_tags @ read_mems @ read_globs

let read_parameters ?region_assoc ?region_list ~callee_reads ~callee_writes =
  let region_assoc = match region_assoc,region_list with
    | Some region_assoc, None -> region_assoc
    | None, Some region_list -> List.map (fun r -> (r,r)) region_list
    | _ -> assert false
  in
  let vars' = 
    read_model_parameters 
      ~mode:MParam ~callee_reads ~callee_writes ~region_assoc
  in
  List.map (function (Var n,ty') -> (n,ty') | _ -> assert false) vars'

let read_arguments ?region_assoc ?region_list ~callee_reads ~callee_writes =
  let region_assoc = match region_assoc,region_list with
    | Some region_assoc, None -> region_assoc
    | None, Some region_list -> List.map (fun r -> (r,r)) region_list
    | _ -> assert false
  in
  let vars' = 
    read_model_parameters 
      ~mode:MParam ~callee_reads ~callee_writes ~region_assoc
  in
  List.map fst vars'

let read_locals ?region_assoc ?region_list ~callee_reads ~callee_writes =
  let region_assoc = match region_assoc,region_list with
    | Some region_assoc, None -> region_assoc
    | None, Some region_list -> List.map (fun r -> (r,r)) region_list
    | _ -> assert false
  in
  let vars' =
    read_model_parameters 
      ~mode:MLocal ~callee_reads ~callee_writes ~region_assoc
  in
  List.map (function (Var n,ty') -> (n,ty') | _ -> assert false) vars'

let read_effects ~callee_reads ~callee_writes ~region_list =
  let region_assoc = List.map (fun r -> (r,r)) region_list in
  let vars' = 
    read_model_parameters 
      ~mode:MEffect ~callee_reads ~callee_writes ~region_assoc
  in
  List.map (var_name' $ fst) vars'

let make_arguments ~callee_reads ~callee_writes ~region_assoc args =
  let writes = 
    write_arguments 
      ~callee_reads ~callee_writes ~region_assoc ?region_list:None 
  in
  let reads = 
    read_arguments 
      ~callee_reads ~callee_writes ~region_assoc ?region_list:None 
  in
  args @ writes @ reads

let transpose_labels ~label_assoc labs =
  match label_assoc with
    | None -> labs
    | Some assoc ->
	LogicLabelSet.fold
	  (fun lab acc ->
	     try
	       let lab = List.assoc lab assoc in
	       LogicLabelSet.add lab acc
	     with Not_found -> LogicLabelSet.add lab acc)
	  labs LogicLabelSet.empty

let transpose_region ~region_assoc r =
  match region_assoc with
    | None -> Some r
    | Some assoc ->
	if Region.polymorphic r then
	  try Some (RegionList.assoc r assoc)
	  with Not_found -> None (* MLocal region *)
	else Some r

let tmemory_detailed_params ~label_in_name ?region_assoc ?label_assoc reads =
  MemoryMap.fold
    (fun (mc,distr) labs acc ->
       let labs = transpose_labels ?label_assoc labs in
       let locr = the (transpose_region ?region_assoc distr) in
       LogicLabelSet.fold
	 (fun lab acc ->
	    let param = tmemory_param ~label_in_name lab (mc,locr) in
	    ((mc,locr), param) :: acc
	 ) labs acc
    ) reads.jc_effect_memories []

let tmemory_params ~label_in_name ?region_assoc ?label_assoc reads =
  List.map snd 
    (tmemory_detailed_params ~label_in_name ?region_assoc ?label_assoc reads)

let talloc_table_detailed_params 
    ~label_in_name ?region_assoc ?label_assoc reads =
  AllocMap.fold
    (fun (ac,distr) labs acc ->
       let labs = transpose_labels ?label_assoc labs in
       let locr = the (transpose_region ?region_assoc distr) in
       LogicLabelSet.fold
	 (fun lab acc ->
	    let param = talloc_table_param ~label_in_name lab (ac,locr) in
	    ((ac,locr), param) :: acc
	 ) labs acc
    ) reads.jc_effect_alloc_table []

let talloc_table_params ~label_in_name ?region_assoc ?label_assoc reads =
  List.map snd
    (talloc_table_detailed_params 
       ~label_in_name ?region_assoc ?label_assoc reads)

let ttag_table_detailed_params ~label_in_name ?region_assoc ?label_assoc reads =
  TagMap.fold
    (fun (vi,distr) labs acc ->
       let labs = transpose_labels ?label_assoc labs in
       let locr = the (transpose_region ?region_assoc distr) in
       LogicLabelSet.fold
	 (fun lab acc ->
	    let param = ttag_table_param ~label_in_name lab (vi,locr) in
	    ((vi,locr), param) :: acc
	 ) labs acc
    ) reads.jc_effect_tag_table []

let ttag_table_params ~label_in_name ?region_assoc ?label_assoc reads =
  List.map snd
    (ttag_table_detailed_params 
       ~label_in_name ?region_assoc ?label_assoc reads)

let tglob_detailed_params ~label_in_name ?region_assoc ?label_assoc reads =
  VarMap.fold
    (fun v labs acc ->
       let labs = transpose_labels ?label_assoc labs in
       LogicLabelSet.fold
	 (fun lab acc ->
	    let param = tparam ~label_in_name lab v in
	    (v, param) :: acc
	 ) labs acc
    ) reads.jc_effect_globals []

let tglob_params ~label_in_name ?region_assoc ?label_assoc reads =
  List.map snd
    (tglob_detailed_params ~label_in_name ?region_assoc ?label_assoc reads)

let tmodel_parameters ~label_in_name ?region_assoc ?label_assoc reads =
  let allocs =
    talloc_table_params ~label_in_name ?region_assoc ?label_assoc reads
  in
  let tags = 
    ttag_table_params ~label_in_name ?region_assoc ?label_assoc reads
  in
  let mems = 
    tmemory_params ~label_in_name ?region_assoc ?label_assoc reads 
  in
  let globs = 
    tglob_params ~label_in_name ?region_assoc ?label_assoc reads 
  in
  allocs @ tags @ mems @ globs

let make_logic_arguments ~label_in_name ~region_assoc ~label_assoc f args =
  let model_params = 
    tmodel_parameters ~label_in_name ~region_assoc ~label_assoc 
      f.jc_logic_info_effects
  in
  let model_args = List.map (fun (n,_ty') -> LVar n) model_params in
  args @ model_args

let make_logic_fun_call ~label_in_name ~region_assoc ~label_assoc f args =
  let args = 
    make_logic_arguments ~label_in_name ~region_assoc ~label_assoc f args 
  in
  LApp(f.jc_logic_info_final_name, args)

let make_logic_pred_call ~label_in_name ~region_assoc ~label_assoc f args =
  let args = 
    make_logic_arguments ~label_in_name ~region_assoc ~label_assoc f args
  in 
  LPred(f.jc_logic_info_final_name, args)


(* *)
let logic_info_reads acc li = 
  let acc =
    MemoryMap.fold
      (fun (mc,r) _ acc -> 
	 StringSet.add (memory_name(mc,r)) acc)
      li.jc_logic_info_effects.jc_effect_memories
      acc
  in
  let acc =
    AllocMap.fold
      (fun (ac,r) labs acc ->
	 StringSet.add (alloc_table_name (ac, r)) acc)
      li.jc_logic_info_effects.jc_effect_alloc_table
      acc
  in
  TagMap.fold
    (fun v _ acc -> StringSet.add (tag_table_name v) acc)
    li.jc_logic_info_effects.jc_effect_tag_table
    acc


(* fold all effects into a list *)
let all_effects ef =
  let res =
    MemoryMap.fold
      (fun (mc,r) labels acc -> 
	let mem = memory_name(mc,r) in
	if Region.polymorphic r then
(*	  if RegionList.mem r f.jc_fun_info_param_regions then
	    if FieldRegionMap.mem (fi,r) 
	      f.jc_fun_info_effects.jc_writes.jc_effect_memories 
	    then mem::acc 
	    else acc
	  else acc*)
	  assert false (* TODO *)
	else mem::acc)
      ef.jc_effect_memories
      []
  in
  let res =
    VarMap.fold
      (fun v labs acc -> v.jc_var_info_final_name::acc)
      ef.jc_effect_globals
      res
  in
  let res =
    AllocMap.fold
      (fun (a,r) labs acc -> 
	let alloc = alloc_table_name(a,r) in
	if Region.polymorphic r then
(*	  if RegionList.mem r f.jc_fun_info_param_regions then
	    if AllocSet.mem (a,r) 
	      f.jc_fun_info_effects.jc_writes.jc_effect_alloc_table 
	    then alloc::acc 
	    else acc
	  else acc*)
	  assert false (* TODO *)
	else alloc::acc)
      ef.jc_effect_alloc_table
      res
  in
  let res =
    TagMap.fold
      (fun v _ acc -> (tag_table_name v)::acc)
      ef.jc_effect_tag_table
      res
  in
  let res =
    StringSet.fold
      (fun v acc -> (mutable_name2 v)::acc)
      ef.jc_effect_mutable
      res
  in
  let res =
    StringSet.fold
      (fun v acc -> (committed_name2 v)::acc)
      ef.jc_effect_committed
      res
  in
  res

(* functions to make Why expressions *)

let make_if_term cond a b =
  LApp("ite", [ cond; a; b ])

let make_eq_term ty a b =
  let eq = match ty with
    | JCTpointer _ | JCTnull -> "eq_pointer_bool"
    | JCTenum _ | JCTlogic _ | JCTany -> assert false
    | JCTnative Tunit -> "eq_unit_bool"
    | JCTnative Tboolean -> "eq_bool_bool"
    | JCTnative Tinteger -> "eq_int_bool"
    | JCTnative Treal -> "eq_real_bool"
    | JCTnative Tstring -> "eq_string_bool"
    | JCTtype_var _ -> assert false (* TODO: need environment *)
  in
  LApp(eq, [a; b])

let make_and_term a b =
  make_if_term a b (LConst(Prim_bool false))

let make_or_term a b =
  make_if_term a (LConst(Prim_bool true)) b

let make_not_term a =
  make_if_term a (LConst(Prim_bool false)) (LConst(Prim_bool true))

let make_eq a b =
  LPred("eq", [ a; b ])

let make_select f this =
  LApp("select", [ f; this ])

let make_select_fi fi =
  make_select (LVar fi.jc_field_info_final_name)

let make_select_committed pc =
  make_select (LVar (committed_name pc))

let make_typeof_vi (vi,r) x =
  LApp("typeof", [ LVar (tag_table_name (vi,r)); x ])

let make_typeof st r x =
  make_typeof_vi (struct_variant st,r) x

let make_subtag t u =
  LPred("subtag", [ t; u ])

let make_subtag_bool t u =
  LApp("subtag_bool", [ t; u ])

let make_instanceof tt p st =
  LPred("instanceof", [ tt; p; LVar (tag_name st) ])

let make_offset_min ac p =
  LApp("offset_min", [LVar(generic_alloc_table_name ac); p])

let make_offset_max ac p =
  LApp("offset_max", [LVar(generic_alloc_table_name ac); p])

let make_int_of_tag st =
  LApp("int_of_tag", [LVar(tag_name st)])

let any_value ty = 
  match ty with
  | JCTnative t -> 
      begin match t with
	| Tunit -> Void
	| Tboolean -> App (Var "any_bool", Void)
	| Tinteger -> App (Var "any_int", Void)
	| Treal -> App (Var "any_real", Void)
	| Tstring -> App (Var "any_string", Void)
      end
  | JCTnull 
  | JCTpointer _ -> App (Var "any_pointer", Void)
  | JCTenum ri -> 
      App (Var ("any_" ^ ri.jc_enum_info_name), Void)
  | JCTlogic _ | JCTany -> assert false
  | JCTtype_var _ -> assert false (* TODO: need environment *)

let any_value' ty' =
  let anyfun = 
    if is_alloc_table_type ty' then "any_alloc_table"
    else if is_tag_table_type ty' then "any_tag_table"
    else if is_memory_type ty' then "any_memory"
    else assert false
  in
  App(Var anyfun,Void)


let pc_of_name name = JCtag (find_struct name, []) (* TODO: parameters *)


let const c =
  match c with
    | JCCvoid -> Prim_void
    | JCCnull -> assert false
    | JCCreal s -> Prim_real s
    | JCCinteger s -> Prim_int (Num.string_of_num (Numconst.integer s))
    | JCCboolean b -> Prim_bool b
    | JCCstring s -> assert false (* TODO *)

type forall_or_let =
  | JCforall of string * Output.logic_type
  | JClet of string * Output.term



(*****************************************************************************)
(*                                  Unions                                   *)
(*****************************************************************************)

type shift_offset = Int_offset of string | Expr_offset of Jc_ast.expr 

let add_offset off1 off2 = 
  match off1,off2 with
    | Int_offset i, Int_offset j -> 
	let k = int_of_string i + int_of_string j in
	Int_offset (string_of_int k)
    | _ -> assert false (* TODO *)

let possible_union_type = function
  | JCTpointer(pc,_,_) -> 
      let vi = pointer_class_variant pc in
      if vi.jc_variant_info_is_union then Some vi else None
  | _ -> None

let union_type ty = 
  match possible_union_type ty with Some vi -> vi | None -> assert false

let of_union_type ty =
  match possible_union_type ty with Some _vi -> true | None -> false

(* TODO: take JCEalloc into account *)
let access_union e fi_opt = 
  let fieldoffbytes fi = 
    match field_offset_in_bytes fi with
      | None -> assert false
      | Some off -> Int_offset (string_of_int off) 
  in
  (* Count offset in bytes before last field access in union *)
  let rec access e = 
    match e#node with
      | JCEderef(e,fi) when embedded_field fi ->
	  begin match access e with
	    | Some(e,off) ->
		Some (e, add_offset off (fieldoffbytes fi))
	    | None -> 
		if of_union_type e#typ then
		  Some (e, fieldoffbytes fi)
		else None
	  end
      | JCEshift(e1,e2) ->
	  None (* assert false *) (* TODO *)
      | _ ->	
	  if of_union_type e#typ then
	    Some (e,Int_offset "0")
	  else None
  in
  match fi_opt with
    | None ->
	access e
    | Some fi ->
	(* let fieldoff fi = Int_offset (string_of_int (field_offset fi)) in *)
	match access e with
	  | Some(e,off) ->
	      Some (e, add_offset off (fieldoffbytes fi))
	  | None -> 
	      if of_union_type e#typ then
		Some (e, fieldoffbytes fi)
	      else None

let destruct_union_access e fi_opt = 
  assert false (* TODO *)

let tdestruct_union_access e fi_opt = 
  assert false (* TODO *)

let ldestruct_union_access e fi_opt = 
  assert false (* TODO *)

let taccess_union t fi_opt =
  let fieldoffbytes fi = 
    match field_offset_in_bytes fi with
      | None -> assert false
      | Some off -> Int_offset (string_of_int off) 
  in
  (* Count offset in bytes before last field access in union *)
  let rec access t = 
    match t#node with
      | JCTderef(t,_lab,fi) when embedded_field fi ->
	  begin match access t with
	    | Some(t,off) ->
		Some (t, add_offset off (fieldoffbytes fi))
	    | None -> 
		if of_union_type t#typ then
		  Some (t, fieldoffbytes fi)
		else None
	  end
      | JCTshift(t1,t2) ->
	  None
(* 	  Format.printf "term %a@." Jc_output.term t; *)
(* 	  assert false (\* TODO *\) *)
      | _ ->	
	  if of_union_type t#typ then
	    Some (t,Int_offset "0")
	  else None
  in

  match fi_opt with
    | None ->
	access t
    | Some fi ->
(* 	let fieldoff fi = Int_offset (string_of_int (field_offset fi)) in *)
	match access t with
	  | Some(t,off) ->
	      Some (t, add_offset off (fieldoffbytes fi))
	  | None -> 
	      if of_union_type t#typ then
		Some (t, fieldoffbytes fi)
	      else None

let laccess_union t fi = None (* TODO *)

let foreign_union e = [] (* TODO: subterms of union that are not in union *)
let tforeign_union t = []

let common_deref_alloc_class access_union e =
  if Region.bitwise e#region then
    JCalloc_bitvector
  else match access_union e None with 
    | None -> JCalloc_struct (struct_variant (pointer_struct e#typ))
    | Some(e,_off) -> JCalloc_union (union_type e#typ)

let deref_alloc_class e =
  common_deref_alloc_class access_union e
  
let tderef_alloc_class t =
  common_deref_alloc_class taccess_union t

let lderef_alloc_class locs =
  common_deref_alloc_class laccess_union locs

let common_deref_mem_class access_union e fi =
  if Region.bitwise e#region then
    JCmem_bitvector
  else match access_union e (Some fi) with 
    | None -> JCmem_field fi
    | Some(e,_off) -> JCmem_union (union_type e#typ)

let deref_mem_class e fi =
  common_deref_mem_class access_union e fi

let tderef_mem_class t fi =
  common_deref_mem_class taccess_union t fi

let lderef_mem_class locs fi =
  common_deref_mem_class laccess_union locs fi


(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
