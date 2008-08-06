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

(* Why type which modelises a variant. *)
let variant_model_type vi =
  simple_logic_type (variant_type_name vi)

(* Why type which modelises a structure "root". *)
let struct_model_type st = variant_model_type (struct_variant st)

let pointer_class_model_type = function
  | JCtag(st, _) -> struct_model_type st
  | JCvariant vi -> variant_model_type vi
  | JCunion vi -> variant_model_type vi

let struct_model_type2 name =
  let st, _ = Hashtbl.find Jc_typing.structs_table name in
  struct_model_type st

let raw_pointer_type ty =
  {
    logic_type_name = pointer_type_name;
    logic_type_args = [ty];
  }

let raw_pset_type ty =
  {
    logic_type_name = pset_type_name;
    logic_type_args = [ty];
  }

let pointer_type pc = raw_pointer_type (pointer_class_model_type pc)

let tag_table_type pc = 
  {
    logic_type_name = tag_table_type_name;
    logic_type_args = [pointer_class_model_type pc];
  }

let tag_id_type pc = 
  {
    logic_type_name = tag_id_type_name;
    logic_type_args = [pointer_class_model_type pc];
  }

let raw_alloc_table_type ty =
  {
    logic_type_name = alloc_table_type_name;
    logic_type_args = [ty];
  }

let bitvector_type = simple_logic_type bitvector_type_name

let alloc_class_type = function
  | JCalloc_struct vi -> variant_model_type vi
  | JCalloc_union vi -> variant_model_type vi
  | JCalloc_bitvector -> bitvector_type

let alloc_table_type ac = 
  raw_alloc_table_type (alloc_class_type ac)

let is_alloc_table_type ty = ty.logic_type_name == alloc_table_type_name

let tr_native_type t =
  match t with
    | Tunit -> "unit"
    | Tboolean -> "bool"
    | Tinteger -> "int"
    | Treal -> "real"
    | Tstring -> "string"

let tr_base_type t =
  match t with
    | JCTnative t -> simple_logic_type (tr_native_type t)
    | JCTlogic s -> simple_logic_type s
    | JCTenum ri -> 
	simple_logic_type ri.jc_enum_info_name
    | JCTpointer (JCtag(st, _ (* TODO ? *)), _, _) ->
	{ logic_type_name = pointer_type_name;
	  logic_type_args = [struct_model_type st] }
    | JCTpointer ((JCvariant vi | JCunion vi), _, _) ->
	{ logic_type_name = pointer_type_name;
	  logic_type_args = [variant_model_type vi] }
    | JCTnull | JCTany -> assert false
    | JCTtype_var _ -> assert false (* TODO (need environment) *)

let why_integer_type = simple_logic_type "int"
  
let tr_type t = Base_type (tr_base_type t)

let memory_type t v =
  { logic_type_name = memory_type_name;
    logic_type_args = [t;v] }

let is_memory_type ty = ty.logic_type_name == memory_type_name

let deconstruct_memory_type_args ty =
  match ty.logic_type_args with [t;v] -> t,v | _ -> assert false

let field_memory_type fi =
  memory_type 
    (struct_model_type fi.jc_field_info_root)
    (tr_base_type fi.jc_field_info_type)

let union_memory_type vi =
  memory_type 
    (variant_model_type vi)
    (if integral_union vi then why_integer_type 
     else 
       bitvector_type)

let bitvector_memory_type =
  memory_type bitvector_type bitvector_type
	
let field_or_variant_memory_type mc =
  match mc with
    | JCmem_field fi -> field_memory_type fi
    | JCmem_union vi -> union_memory_type vi
    | JCmem_bitvector -> bitvector_memory_type

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
let get_current_spec () = !current_spec

let mutable_memory infunction (mc,r) =
  if Region.polymorphic r then
    MemoryMap.mem (mc,r)
      infunction.jc_fun_info_effects.jc_writes.jc_effect_memories
  else true

let mutable_alloc_table infunction (root,r) =
  if Region.polymorphic r then
    AllocMap.mem (root,r)
      infunction.jc_fun_info_effects.jc_writes.jc_effect_alloc_table
  else true

let mutable_fvmemory infunction (mc,r) =
  if Region.polymorphic r then
    MemoryMap.mem 
      (mc,r)
      infunction.jc_fun_info_effects.jc_writes.jc_effect_memories
  else true

let memory_logic_params ~label_in_name ?region_assoc ?label_assoc li =
  MemoryMap.fold
    (fun (mc,r) labs acc ->
       let r =
	 match region_assoc with 
	   | Some region_assoc when Region.polymorphic r ->
	       begin
		 Jc_options.lprintf "assoc:%a@." Region.print_assoc region_assoc;
		 Jc_options.lprintf "r:%a@." Region.print r;
		 try RegionList.assoc r region_assoc with Not_found -> assert false
	       end
	   | _ -> r
       in
       let name = memory_name(mc,r) in
       let mut = match !current_function with
	 | None -> true
	 | Some infunction -> mutable_fvmemory infunction (mc,r) 
       in
       LogicLabelSet.fold
	 (fun lab acc ->
	    let name = 
	      if mut then 
		label_var ~label_in_name ?label_assoc lab name 
	      else 
		label_var ~label_in_name ?label_assoc LabelHere name 
	    in
	    ((mc,r),(name, field_or_variant_memory_type mc))::acc)
	 labs acc)
    li.jc_logic_info_effects.jc_effect_memories
    []

let alloc_logic_params ~label_in_name ?region_assoc ?label_assoc li =
  AllocMap.fold
    (fun (ac,r) labs acc ->
       let r =
	 match region_assoc with
	   | Some assoc when Region.polymorphic r ->
	       begin
		 Jc_options.lprintf "assoc:%a@." Region.print_assoc assoc;
		 Jc_options.lprintf "r:%a@." Region.print r;
		 try RegionList.assoc r assoc with Not_found -> assert false
	       end
	   | _ -> r
       in
       (alloc_table_name (ac, r),
	alloc_table_type (ac))::acc)
    li.jc_logic_info_effects.jc_effect_alloc_table
    []

let logic_params ~label_in_name ?region_assoc ?label_assoc li =
  let mems = List.map snd
    (memory_logic_params ~label_in_name ?region_assoc ?label_assoc li)
  in
  let allocs =
    alloc_logic_params ~label_in_name ?region_assoc ?label_assoc li
  in
  let tags = 
    TagMap.fold
      (fun (v,r) labs acc -> 
	 let t = { logic_type_args = [variant_model_type v];
		   logic_type_name = "tag_table" }
	 in
	 let name = tag_table_name (v,r) in
	 LogicLabelSet.fold
	   (fun lab acc ->
	      let name = label_var ~label_in_name ?label_assoc lab name in
	      (name, t)::acc)
	   labs acc)
      li.jc_logic_info_effects.jc_effect_tag_table
      []
  in
  let globs = 
    VarMap.fold
      (fun v labs acc -> 
	 (v.jc_var_info_final_name, tr_base_type v.jc_var_info_type) :: acc
      ) li.jc_logic_info_effects.jc_effect_globals
      []
  in
  mems @ allocs @ tags @ globs

let logic_params_call ~label_in_name li l region_assoc label_assoc =
  List.map 
    (fun (id,t) -> LVar id)
    (logic_params ~label_in_name ~region_assoc ~label_assoc li) @ l

let make_logic_fun_call ~label_in_name li l region_assoc label_assoc =
  let params = logic_params_call ~label_in_name li l region_assoc label_assoc in
  LApp(li.jc_logic_info_final_name,params)

let make_logic_pred_call ~label_in_name li l region_assoc label_assoc =
  let params = logic_params_call ~label_in_name li l region_assoc label_assoc in 
    LPred (li.jc_logic_info_final_name, params)



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
(* *)


(*

(* same as in jc_interp.ml *)
let tag_name st = st.jc_struct_info_name ^ "_tag"

(* same as in jc_interp.ml *)
let logic_params li l =
  let l =
    FieldRegionSet.fold
      (fun (fi,r) acc -> (LVar(field_region_memory_name(fi,r)))::acc)
      li.jc_logic_info_effects.jc_effect_memories
      l	    
  in
  let l = 
    AllocSet.fold
      (fun (a,r) acc -> (LVar(alloc_table_name(a,r))::acc))
      li.jc_logic_info_effects.jc_effect_alloc_table
      l
  in
  StringSet.fold
    (fun v acc -> (LVar (v ^ "_tag_table"))::acc)
    li.jc_logic_info_effects.jc_effect_tag_table
    l	    

*)

let stringmap_elements map =
  StringMap.fold (fun _ i acc -> i::acc) map []

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

let alloc_table_type2 a =
  {
    logic_type_name = alloc_table_type_name;
    logic_type_args = [variant_model_type (find_variant a)];
  }

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

let pc_of_name name = JCtag (find_struct name, []) (* TODO: parameters *)

(* see make_valid_pred in jc_interp.ml *)
let make_valid_pred_app pc p a b =
  let allocs = List.map
    (fun ac -> LVar(generic_alloc_table_name ac))
    (Jc_struct_tools.all_allocs ~select:fully_allocated pc)
  in
  let memories = List.map
    (fun fi -> LVar(field_memory_name fi))
    (Jc_struct_tools.all_memories ~select:fully_allocated pc)
  in
  LPred(valid_pred_name pc, p::a::b::allocs@memories)

let const_of_num n = LConst(Prim_int(Num.string_of_num n))

type forall_or_let =
  | JCforall of string * Output.logic_type
  | JClet of string * Output.term

let make_pred_binds binds body =
  List.fold_left
    (fun body bind ->
       match bind with
	 | JCforall(id, ty) -> LForall(id, ty, body)
	 | JClet(id, value) -> LLet(id, value, body))
    body (List.rev binds)

let const c =
  match c with
    | JCCvoid -> Prim_void
    | JCCnull -> assert false
    | JCCreal s -> Prim_real s
    | JCCinteger s -> Prim_int (Num.string_of_num (Numconst.integer s))
    | JCCboolean b -> Prim_bool b
    | JCCstring s -> assert false (* TODO *)


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

let union_type = function
  | JCTpointer(pc,_,_) -> 
      let vi = pointer_class_variant pc in
      if vi.jc_variant_info_is_union then Some vi else None
  | _ -> None

let of_union_type ty =
  match union_type ty with Some _vi -> true | None -> false

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
    | Some(e,_off) -> JCalloc_union (the (union_type e#typ))

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
    | Some(e,_off) -> JCmem_union (the (union_type e#typ))

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
