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
open Common
open Env
open Envset

let alloc_class_of_mem_class =
  function
  | JCmem_field fi -> JCalloc_root (struct_root fi.fi_struct)
  | JCmem_plain_union vi -> JCalloc_root vi
  | JCmem_bitvector -> JCalloc_bitvector

let alloc_class_of_pointer_class =
  function
  | JCtag (st, _) -> JCalloc_root (struct_root st)
  | JCroot vi -> JCalloc_root vi

let root_info_of_alloc_class = function
  | JCalloc_root vi -> vi
  | JCalloc_bitvector ->
    (* no variant *)
    failwith "root_info_of_alloc_class: bitvector regions have no roots"

let root_info_of_mem_class = root_info_of_alloc_class % alloc_class_of_mem_class

(* keep the pointers only and return their pointer_class *)
let fields_pointer_class =
  List.flatten %
    List.map
      (fun fi ->
         match fi.fi_type with
	 | JCTpointer(pc, _, _) -> [pc]
	 | _ -> [])

let embedded_field fi =
  match fi.fi_type with
    | JCTpointer(_fpc, Some _fa, Some _fb) -> true
    | _ -> false

(* TODO !!!!!!!!!!!!!
   add fields of parent
*)

let field_offset fi =
  let st = fi.fi_struct in
  let off,counting =
    List.fold_left (fun (off,counting) fi' ->
		      if counting then
			if fi.fi_tag = fi'.fi_tag then
			  off,false
			else
			  off + fi'.fi_bitsize, counting
		      else
			off,counting
		   ) (0,true) st.si_fields
  in
  assert (not counting);
  off

let field_offset_in_bytes fi =
  let off = field_offset fi in
  if off mod 8 = 0 then Some(off/8) else None

let field_type_has_bitvector_representation fi =
  match fi.fi_type with
    | JCTenum _
    | JCTpointer _ -> true
    | JCTnative _
    | JCTlogic _
    | JCTnull
    | JCTany
    | JCTtype_var _ -> false

let[@warning "-32"] struct_fields st =
  let rec aux acc st =
    let acc = st.si_fields @ acc in
    match st.si_parent with
      | None -> acc
      | Some(st',_) -> aux acc st'
  in
  aux [] st

let struct_has_size _st = true

let struct_size st =
  match List.rev st.si_fields with
  | [] -> 0
  | last_fi :: _ -> field_offset last_fi + last_fi.fi_bitsize

let struct_size_in_bytes st =
  let s = struct_size st in
  assert (s mod 8 = 0);
  s/8

let rec all_fields acc = function[@warning "-9"]
  | JCroot _vi -> acc
  | JCtag ({ si_parent = Some(p, pp) } as st, _) ->
      all_fields (st.si_fields @ acc) (JCtag(p, pp))
  | JCtag ({ si_parent = None } as st, _) ->
      st.si_fields @ acc

let all_fields = all_fields []

let rec all_memories select forbidden acc pc =
  match pc with
    | JCtag(st,_) as pc ->
	if StringSet.mem st.si_name forbidden then
	  acc
	else
	  let fields = List.filter select (all_fields pc) in
	  let mems = List.map (fun fi -> JCmem_field fi) fields in
	  (* add the fields to our list *)
	  let acc =
	    List.fold_left
	      (fun acc mc -> StringMap.add (Name.Class.memory mc) mc acc)
	      acc mems
	  in
	  (* continue recursively on the fields *)
	  let forbidden = StringSet.add st.si_name forbidden in
	  List.fold_left
	    (all_memories select forbidden) acc (fields_pointer_class fields)
    | JCroot rt ->
	match rt.ri_kind with
	  | Rvariant -> acc
	  | RdiscrUnion ->
	      List.fold_left
		(all_memories select forbidden) acc
		(List.map (fun st -> JCtag(st,[])) rt.ri_hroots)
	  | RplainUnion ->
	      let mc = JCmem_plain_union rt in
	      StringMap.add (Name.Class.memory mc) mc acc

let all_memories ?(select = fun _ -> true) pc =
  Options.lprintf "all_memories(%s):@." (Print_misc.pointer_class pc);
  let map = all_memories select StringSet.empty StringMap.empty pc in
  let list = List.rev (StringMap.fold (fun _ ty acc -> ty::acc) map []) in
  Options.lprintf "  Found %n memories.@." (List.length list);
  list

let rec all_types select forbidden acc pc =
  Options.lprintf "  all_types(%s)@." (Print_misc.pointer_class pc);
  match pc with
    | JCtag(st, _) as pc ->
	if StringSet.mem st.si_name forbidden then
	  acc
	else
	  let vi = struct_root st in
	  let forbidden = StringSet.add st.si_name forbidden in
	  List.fold_left
	    (all_types select forbidden)
	    (StringMap.add vi.ri_name vi acc)
	    (fields_pointer_class (List.filter select (all_fields pc)))
    | JCroot vi ->
	StringMap.add vi.ri_name vi acc

let all_types ?(select = fun _ -> true) pc =
  Options.lprintf "all_types(%s):@." (Print_misc.pointer_class pc);
  let map = all_types select StringSet.empty StringMap.empty pc in
  let list = List.rev (StringMap.fold (fun _ ty acc -> ty::acc) map []) in
  Options.lprintf "  Found %n types.@." (List.length list);
  list

let fully_allocated fi =
  match fi.fi_type with
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
	if StringSet.mem st.si_name forbidden then
	  acc
	else
	  let ac = JCalloc_root (struct_root st) in
	  let forbidden = StringSet.add st.si_name forbidden in
	  List.fold_left
	    (all_allocs select forbidden)
	    (StringMap.add (Name.Class.alloc ac) ac acc)
	    (fields_pointer_class (List.filter select (all_fields pc)))
    | JCroot rt ->
	let ac = JCalloc_root rt in
	let acc = StringMap.add (Name.Class.alloc ac) ac acc in
	match rt.ri_kind with
	  | Rvariant
	  | RplainUnion -> acc
	  | RdiscrUnion ->
	      List.fold_left
		(all_allocs select forbidden) acc
		(List.map (fun st -> JCtag(st,[])) rt.ri_hroots)

let all_allocs ?(select = fun _ -> true) pc =
  Options.lprintf "all_allocs(%s):@." (Print_misc.pointer_class pc);
  let map =
    all_allocs select StringSet.empty StringMap.empty pc
  in
  let list = List.rev (StringMap.fold (fun _ ty acc -> ty::acc) map []) in
  Options.lprintf "  Found %n allocs.@." (List.length list);
  list

let rec all_tags select forbidden acc pc =
  match pc with
    | JCtag(st,_) as pc ->
	if StringSet.mem st.si_name forbidden then
	  acc
	else
	  let vi = struct_root st in
	  let forbidden = StringSet.add st.si_name forbidden in
	  List.fold_left
	    (all_tags select forbidden)
	    (StringMap.add vi.ri_name vi acc)
	    (fields_pointer_class (List.filter select (all_fields pc)))
    | JCroot vi ->
	StringMap.add vi.ri_name vi acc

let all_tags ?(select = fun _ -> true) pc =
  Options.lprintf "all_tags(%s):@." (Print_misc.pointer_class pc);
  let map =
    all_tags select StringSet.empty StringMap.empty pc
  in
  let list = List.rev (StringMap.fold (fun _ ty acc -> ty::acc) map []) in
  Options.lprintf "  Found %n tags.@." (List.length list);
  list
