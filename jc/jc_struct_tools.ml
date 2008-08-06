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
  | JCmem_field fi -> JCalloc_struct (struct_variant fi.jc_field_info_struct)
  | JCmem_union vi -> JCalloc_union vi
  | JCmem_bitvector -> JCalloc_bitvector

let alloc_class_of_pointer_class = function
  | JCtag(st,_) -> JCalloc_struct (struct_variant st)
  | JCvariant vi -> JCalloc_struct vi
  | JCunion vi -> JCalloc_union vi

let variant_of_alloc_class = function
  | JCalloc_struct vi -> vi
  | JCalloc_union vi -> vi
  | JCalloc_bitvector -> assert false (* no variant *)

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

let struct_size st =
  match List.rev st.jc_struct_info_fields with
    | [] -> 0
    | last_fi::_ -> field_offset last_fi + the last_fi.jc_field_info_bitsize

let struct_size_in_bytes st =
  let s = struct_size st in
  assert (s mod 8 = 0);
  s/8

let rec all_fields acc = function
  | JCvariant vi | JCunion vi -> acc
  | JCtag ({ jc_struct_info_parent = Some(p, pp) } as st, _) ->
      all_fields (st.jc_struct_info_fields @ acc) (JCtag(p, pp))
  | JCtag ({ jc_struct_info_parent = None } as st, _) ->
      st.jc_struct_info_fields @ acc

let all_fields = all_fields []

let rec all_memories select forbidden acc pc =
  Jc_options.lprintf "  all_memories(%s)@." (pointer_class_name pc);
  match pc with
    | JCtag(st, _) as pc ->
	if StringSet.mem st.jc_struct_info_name forbidden 
	  || (struct_variant st).jc_variant_info_is_union then
	    acc
	else
	  let fields = List.filter select (all_fields pc) in
	  (* add the fields to our list *)
	  let acc = List.fold_left
	    (fun acc fi -> StringMap.add (field_memory_name fi) fi acc)
	    acc
	    fields
	  in
	  (* continue recursively on the fields *)
	  let forbidden = StringSet.add st.jc_struct_info_name forbidden in
	  List.fold_left
	    (all_memories select forbidden)
	    acc
	    (fields_pointer_class fields)
    | JCvariant vi | JCunion vi ->
	acc

let all_memories ?(select = fun _ -> true) pc =
  Jc_options.lprintf "all_memories(%s):@." (pointer_class_name pc);
  let map = all_memories select StringSet.empty StringMap.empty pc in
  let list = List.rev (StringMap.fold (fun _ ty acc -> ty::acc) map []) in
  Jc_options.lprintf "  Found %n memories.@." (List.length list);
  list

let rec all_types select forbidden acc pc =
  Jc_options.lprintf "  all_types(%s)@." (pointer_class_name pc);
  match pc with
    | JCtag(st, _) as pc ->
	if StringSet.mem st.jc_struct_info_name forbidden then
	  acc
	else
	  let vi = struct_variant st in
	  let forbidden = StringSet.add st.jc_struct_info_name forbidden in
	  List.fold_left
	    (all_types select forbidden)
	    (StringMap.add vi.jc_variant_info_name vi acc)
	    (fields_pointer_class (List.filter select (all_fields pc)))
    | JCvariant vi | JCunion vi ->
	StringMap.add vi.jc_variant_info_name vi acc

let all_types ?(select = fun _ -> true) pc =
  Jc_options.lprintf "all_types(%s):@." (pointer_class_name pc);
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
	else
	  let ac = JCalloc_struct (struct_variant st) in
	  let forbidden = StringSet.add st.jc_struct_info_name forbidden in
	  List.fold_left
	    (all_allocs select forbidden)
	    (StringMap.add (alloc_class_name ac) ac acc)
	    (fields_pointer_class (List.filter select (all_fields pc)))
    | JCvariant vi ->
	let ac = JCalloc_struct vi in
	StringMap.add (alloc_class_name ac) ac acc
    | JCunion vi ->
	let ac = JCalloc_union vi in
	StringMap.add (alloc_class_name ac) ac acc

let all_allocs ?(select = fun _ -> true) pc =
  Jc_options.lprintf "all_allocs(%s):@." (pointer_class_name pc);
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
	    (StringMap.add vi.jc_variant_info_name vi acc)
	    (fields_pointer_class (List.filter select (all_fields pc)))
    | JCvariant vi ->
	StringMap.add vi.jc_variant_info_name vi acc
    | JCunion vi ->
	StringMap.add vi.jc_variant_info_name vi acc

let all_tags ?(select = fun _ -> true) pc =
  Jc_options.lprintf "all_tags(%s):@." (pointer_class_name pc);
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

