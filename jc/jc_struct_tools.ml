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

open Jc_name
open Jc_pervasives
open Jc_env
open Jc_envset

let alloc_class_of_mem_class = function
  | JCmem_field fi -> JCalloc_root (struct_variant fi.jc_field_info_struct)
  | JCmem_discr_union fi -> 
      JCalloc_root (struct_variant fi.jc_field_info_struct)
  | JCmem_plain_union vi -> JCalloc_root vi
  | JCmem_bitvector -> JCalloc_bitvector

let alloc_class_of_pointer_class = function
  | JCtag(st,_) -> JCalloc_root (struct_variant st)
  | JCroot vi -> JCalloc_root vi

let variant_of_alloc_class = function
  | JCalloc_root vi -> vi
  | JCalloc_bitvector -> assert false (* no variant *)

let variant_of_mem_class = variant_of_alloc_class $ alloc_class_of_mem_class

(* keep the pointers only and return their pointer_class *)
let fields_pointer_class = List.flatten $
  (List.map
     (fun fi -> match fi.jc_field_info_type with
	| JCTpointer(pc, _, _) -> [pc]
	| _ -> []))

let embedded_field fi = 
  match fi.jc_field_info_type with
    | JCTpointer(_fpc, Some _fa, Some _fb) -> true
    | _ -> false

(* TODO !!!!!!!!!!!!!
   add fields of parent 
*)

let field_offset fi =
  let st = fi.jc_field_info_struct in
  let off,counting = 
    List.fold_left (fun (off,counting) fi' ->
		      if counting then
			if fi.jc_field_info_tag = fi'.jc_field_info_tag then
			  off,false
			else
			  off + the fi'.jc_field_info_bitsize, counting
		      else
			off,counting
		   ) (0,true) st.jc_struct_info_fields
  in 
  assert (not counting);
  off

let field_offset_in_bytes fi =
  let off = field_offset fi in
  if off mod 8 = 0 then Some(off/8) else None

let field_type_has_bitvector_representation fi =
  match fi.jc_field_info_type with
    | JCTenum _ 
    | JCTpointer _ -> true
    | JCTnative _
    | JCTlogic _
    | JCTnull
    | JCTany
    | JCTtype_var _ -> false

let struct_fields st =
  let rec aux acc st =
    let acc = st.jc_struct_info_fields @ acc in
    match st.jc_struct_info_parent with
      | None -> acc
      | Some(st',_) -> aux acc st'
  in
  aux [] st

let struct_has_size st =
  not (List.exists 
	 (fun fi -> fi.jc_field_info_bitsize = None) 
	 (struct_fields st))

let struct_size st =
  match List.rev st.jc_struct_info_fields with
    | [] -> 0
    | last_fi::_ -> field_offset last_fi + the last_fi.jc_field_info_bitsize

let struct_size_in_bytes st =
  let s = struct_size st in
  assert (s mod 8 = 0);
  s/8

let rec all_fields acc = function
  | JCroot vi -> acc
  | JCtag ({ jc_struct_info_parent = Some(p, pp) } as st, _) ->
      all_fields (st.jc_struct_info_fields @ acc) (JCtag(p, pp))
  | JCtag ({ jc_struct_info_parent = None } as st, _) ->
      st.jc_struct_info_fields @ acc

let all_fields = all_fields []

let rec all_memories select forbidden acc pc =
  match pc with
    | JCtag(st,_) as pc ->
	if StringSet.mem st.jc_struct_info_name forbidden then
	  acc
	else if struct_of_plain_union st then
	  all_memories select forbidden acc (JCroot (struct_variant st))
	else
	  let fields = List.filter select (all_fields pc) in
	  let mems = List.map (fun fi -> JCmem_field fi) fields in
	  (* add the fields to our list *)
	  let acc = 
	    List.fold_left
	      (fun acc mc -> StringMap.add (memory_class_name mc) mc acc)
	      acc mems
	  in
	  (* continue recursively on the fields *)
	  let forbidden = StringSet.add st.jc_struct_info_name forbidden in
	  List.fold_left
	    (all_memories select forbidden)
	    acc
	    (fields_pointer_class fields)
    | JCroot vi ->
	match vi.jc_root_info_kind with
	  | Rvariant -> acc
	  | RdiscrUnion ->
	      assert false (* TODO *)
	  | RplainUnion ->
	      let mc = JCmem_plain_union vi in
	      StringMap.add (memory_class_name mc) mc acc

let all_memories ?(select = fun _ -> true) pc =
  Jc_options.lprintf "all_memories(%s):@." (Jc_output_misc.pointer_class pc);
  let map = all_memories select StringSet.empty StringMap.empty pc in
  let list = List.rev (StringMap.fold (fun _ ty acc -> ty::acc) map []) in
  Jc_options.lprintf "  Found %n memories.@." (List.length list);
  list

let rec all_types select forbidden acc pc =
  Jc_options.lprintf "  all_types(%s)@." (Jc_output_misc.pointer_class pc);
  match pc with
    | JCtag(st, _) as pc ->
	if StringSet.mem st.jc_struct_info_name forbidden then
	  acc
	else
	  let vi = struct_variant st in
	  let forbidden = StringSet.add st.jc_struct_info_name forbidden in
	  List.fold_left
	    (all_types select forbidden)
	    (StringMap.add vi.jc_root_info_name vi acc)
	    (fields_pointer_class (List.filter select (all_fields pc)))
    | JCroot vi ->
	StringMap.add vi.jc_root_info_name vi acc

let all_types ?(select = fun _ -> true) pc =
  Jc_options.lprintf "all_types(%s):@." (Jc_output_misc.pointer_class pc);
  let map = all_types select StringSet.empty StringMap.empty pc in
  let list = List.rev (StringMap.fold (fun _ ty acc -> ty::acc) map []) in
  Jc_options.lprintf "  Found %n types.@." (List.length list);
  list

let fully_allocated fi =
  match fi.jc_field_info_type with
    | JCTpointer(_, Some _, Some _) -> true
    | JCTpointer(_, None, Some _)
    | JCTpointer(_, Some _, None)
    | JCTpointer(_, None, None)
    | JCTnull
    | JCTenum _
    | JCTlogic _
    | JCTnative _
    | JCTany -> false
    | JCTtype_var _ -> assert false (* TODO: need environment *)

let rec all_allocs select forbidden acc pc =
  match pc with
    | JCtag(st,_) as pc ->
	if StringSet.mem st.jc_struct_info_name forbidden then
	  acc
	else if struct_of_union st then
	  all_allocs select forbidden acc (JCroot (struct_variant st))
	else
	  let ac = JCalloc_root (struct_variant st) in
	  let forbidden = StringSet.add st.jc_struct_info_name forbidden in
	  List.fold_left
	    (all_allocs select forbidden)
	    (StringMap.add (alloc_class_name ac) ac acc)
	    (fields_pointer_class (List.filter select (all_fields pc)))
    | JCroot vi ->
	let ac = JCalloc_root vi in
	StringMap.add (alloc_class_name ac) ac acc

let all_allocs ?(select = fun _ -> true) pc =
  Jc_options.lprintf "all_allocs(%s):@." (Jc_output_misc.pointer_class pc);
  let map = 
    all_allocs select StringSet.empty StringMap.empty pc
  in
  let list = List.rev (StringMap.fold (fun _ ty acc -> ty::acc) map []) in
  Jc_options.lprintf "  Found %n allocs.@." (List.length list);
  list

let rec all_tags select forbidden acc pc =
  match pc with
    | JCtag(st,_) as pc ->
	if StringSet.mem st.jc_struct_info_name forbidden then
	  acc
	else
	  let vi = struct_variant st in
	  let forbidden = StringSet.add st.jc_struct_info_name forbidden in
	  List.fold_left
	    (all_tags select forbidden)
	    (StringMap.add vi.jc_root_info_name vi acc)
	    (fields_pointer_class (List.filter select (all_fields pc)))
    | JCroot vi ->
	StringMap.add vi.jc_root_info_name vi acc

let all_tags ?(select = fun _ -> true) pc =
  Jc_options.lprintf "all_tags(%s):@." (Jc_output_misc.pointer_class pc);
  let map = 
    all_tags select StringSet.empty StringMap.empty pc
  in
  let list = List.rev (StringMap.fold (fun _ ty acc -> ty::acc) map []) in
  Jc_options.lprintf "  Found %n tags.@." (List.length list);
  list


(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)

