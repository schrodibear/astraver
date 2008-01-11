
open Output

(*
open Jc_env
open Jc_ast
open Jc_pervasives
open Jc_iterators
*)

open Jc_envset
open Jc_fenv
open Jc_region
open Jc_name


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
	 StringSet.fold
	   (fun lab acc ->
	      let name =
		match label_assoc with
		  | None -> (* assert false *) name 
		  | Some a ->
		      try
			let l = List.assoc lab a in
			if label_in_name then
			  name ^ "_at_" ^ l
			else
			  match l with
			    | "Pre" -> name ^ "@"
			    | "Post" -> name
			    | _ -> name ^ "@" ^ l
		      with Not_found -> (* assert false *) name (**)
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
	(alloc_region_table_name(a,r),alloc_table_type a)::acc)
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



(**)
let logic_info_reads acc li = 
  let acc =
    FieldRegionMap.fold
      (fun (fi,r) _ acc -> StringSet.add (field_region_memory_name(fi,r)) acc)
      li.jc_logic_info_effects.jc_effect_memories
      acc
  in
  let acc =
    StringRegionSet.fold
      (fun (a,r) acc -> StringSet.add (alloc_region_table_name(a,r)) acc)
      li.jc_logic_info_effects.jc_effect_alloc_table
      acc
  in
  StringSet.fold
    (fun v acc -> StringSet.add (v^"_tag_table") acc)
    li.jc_logic_info_effects.jc_effect_tag_table
    acc
(**)


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
