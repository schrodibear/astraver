
open Output

(*
open Jc_env
open Jc_ast
open Jc_pervasives
open Jc_iterators
*)

open Jc_pervasives
open Jc_envset
open Jc_env
open Jc_fenv
open Jc_region
open Jc_name

let struct_model_type2 name =
  let st, _ = Hashtbl.find Jc_typing.structs_table name in
  struct_model_type st

let pointer_type st = 
  {
    logic_type_name = pointer_type_name;
    logic_type_args = [struct_model_type st];
  }

let tag_table_type st = 
  {
    logic_type_name = tag_table_type_name;
    logic_type_args = [struct_model_type st];
  }

let tag_id_type st = 
  {
    logic_type_name = tag_id_type_name;
    logic_type_args = [struct_model_type st];
  }

let alloc_table_type st =
  {
    logic_type_name = alloc_table_type_name;
    logic_type_args = [struct_model_type st];
  }

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
	{ logic_type_name = pointer_type_name;
	  logic_type_args = [struct_model_type st] }
    | JCTvariant_pointer (vi, a, b) ->
	{ logic_type_name = pointer_type_name;
	  logic_type_args = [variant_model_type vi] }
    | JCTnull -> assert false

let memory_type t v =
  { logic_type_name = memory_type_name;
    logic_type_args = [t;v] }

let memory_field fi =
  memory_type 
    (struct_model_type fi.jc_field_info_root)
    (tr_base_type fi.jc_field_info_type)

	
let logic_params ~label_in_name ?region_assoc ?label_assoc li =
  let l =
    FieldRegionMap.fold
      (fun (fi,r) labs acc ->
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
	 let name = field_region_memory_name(fi,r) in
	 LogicLabelSet.fold
	   (fun lab acc ->
	      let label =
		match label_assoc with
		  | None -> lab 
		  | Some a ->
		      try List.assoc lab a
		      with Not_found -> lab
	      in			
	      let name =
		if label_in_name then label_var label name
		else
		  match label with (* hack ?? *)
		    | LabelNone -> assert false
		    | LabelHere -> name
		    | LabelPost -> name
		    | LabelPre -> name ^ "@"
		    | LabelInit -> name ^ "@init"
		    | LabelName l -> name ^ "@" ^ l
	      in
	      (name, memory_field fi)::acc)
	   labs acc)
      li.jc_logic_info_effects.jc_effect_memories
      []
  in
  let l = 
    StringRegionSet.fold
      (fun (a,r) acc ->
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
	let st, _ = Hashtbl.find Jc_typing.structs_table a in
	(alloc_region_table_name (st, r), alloc_table_type st)::acc)
      li.jc_logic_info_effects.jc_effect_alloc_table
      l	    
  in
  StringSet.fold
    (fun v acc -> 
       let t = { logic_type_args = [simple_logic_type v];
		 logic_type_name = "tag_table" }
       in
       (v ^ "_tag_table", t)::acc)
    li.jc_logic_info_effects.jc_effect_tag_table
    l	    

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
    FieldRegionMap.fold
      (fun (fi,r) _ acc -> StringSet.add (field_region_memory_name(fi,r)) acc)
      li.jc_logic_info_effects.jc_effect_memories
      acc
  in
  let acc =
    StringRegionSet.fold
      (fun (a,r) acc ->
	 let st, _ = Hashtbl.find Jc_typing.structs_table a in
	 StringSet.add (alloc_region_table_name (st, r)) acc)
      li.jc_logic_info_effects.jc_effect_alloc_table
      acc
  in
  StringSet.fold
    (fun v acc -> StringSet.add (v^"_tag_table") acc)
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
    StringRegionSet.fold
      (fun (a,r) acc -> (LVar(alloc_region_table_name(a,r))::acc))
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
  fst (Hashtbl.find Jc_typing.structs_table a)

let tag_table_name2 a =
  tag_table_name (find_struct a)

let alloc_table_name2 a =
  alloc_table_name (find_struct a)

let alloc_region_table_name2 (a, r) =
  alloc_region_table_name (find_struct a, r)

let mutable_name2 a =
  mutable_name (find_struct a)

let committed_name2 a =
  committed_name (find_struct a)

let alloc_table_type2 a =
  {
    logic_type_name = alloc_table_type_name;
    logic_type_args = [struct_model_type (find_struct a)];
  }

(* fold all effects into a list *)
let all_effects ef =
  let res =
    FieldRegionMap.fold
      (fun (fi,r) labels acc -> 
	let mem = field_region_memory_name(fi,r) in
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
    VarSet.fold
      (fun v acc -> v.jc_var_info_final_name::acc)
      ef.jc_effect_globals
      res
  in
  let res =
    StringRegionSet.fold
      (fun (a,r) acc -> 
	let alloc = alloc_region_table_name2(a,r) in
	if Region.polymorphic r then
(*	  if RegionList.mem r f.jc_fun_info_param_regions then
	    if StringRegionSet.mem (a,r) 
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
    StringSet.fold
      (fun v acc -> (tag_table_name2 v)::acc)
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

let make_eq a b =
  LPred("eq", [ a; b ])

let make_select f this =
  LApp("select", [ f; this ])

let make_select_fi fi =
  make_select (LVar fi.jc_field_info_final_name)

let make_select_committed root =
  make_select (LVar (committed_name root))

let make_typeof_vi vi x =
  LApp("typeof", [ LVar (tag_table_name_vi vi); x ])

let make_typeof st x =
  make_typeof_vi (struct_variant st) x

let make_subtag t u =
  LPred("subtag", [ t; u ])

let any_value ty = 
  match ty with
  | JCTnative t -> 
      begin match t with
	| Tunit -> Void
	| Tboolean -> App (Var "any_bool", Void)
	| Tinteger -> App (Var "any_int", Void)
	| Treal -> App (Var "any_real", Void)
      end
  | JCTnull 
  | JCTpointer _
  | JCTvariant_pointer _ -> App (Var "any_pointer", Void)
  | JCTenum ri -> 
      App (Var ("any_" ^ ri.jc_enum_info_name), Void)
  | JCTlogic _ -> assert false

(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)