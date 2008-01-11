
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


let logic_params ?assoc li =
  let l =
    FieldRegionMap.fold
      (fun (fi,r) labs acc -> 
	let r =
	  match assoc with 
	    | Some assoc when Region.polymorphic r ->
		begin
		  Jc_options.lprintf "assoc:%a@." Region.print_assoc assoc;
		  Jc_options.lprintf "r:%a@." Region.print r;
		  try RegionList.assoc r assoc with Not_found -> assert false
		end
	    | _ -> r
	in
	(field_region_memory_name(fi,r), memory_field fi)::acc)
      li.jc_logic_info_effects.jc_effect_memories
      []
  in
  let l = 
    StringRegionSet.fold
      (fun (a,r) acc ->
	let r =
	  match assoc with
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

let logic_params_call li l assoc =
  List.map 
    (fun (id,t) -> LVar id)
    (logic_params ~assoc li) @ l

let make_logic_fun_call li l assoc =
  let params = logic_params_call li l assoc in
  LApp(li.jc_logic_info_final_name,params)

let make_logic_pred_call li l =
  let params = logic_params_call li l [] in (* TODO: add assoc *)
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
