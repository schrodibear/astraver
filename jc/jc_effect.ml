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


(* $Id: jc_effect.ml,v 1.120 2008-08-07 12:32:30 moy Exp $ *)

open Jc_interp_misc
open Jc_name
open Jc_env
open Jc_envset
open Jc_fenv
open Jc_ast
open Jc_pervasives
open Jc_iterators
open Format
open Pp
open Jc_region
open Jc_struct_tools
  
(* Constant memories *)
let constant_memories = Hashtbl.create 17

(* Constant allocation tables *)
let constant_alloc_tables = Hashtbl.create 17

(* Constant allocation tables *)
let constant_tag_tables = Hashtbl.create 17

let add_constant_memory (mc,r) =
  Hashtbl.add constant_memories (memory_name (mc,r)) (mc,r)

let add_constant_alloc_table (ac,r) =
  Hashtbl.add constant_alloc_tables (alloc_table_name (ac,r)) (ac,r)

let add_constant_tag_table (vi,r) =
  Hashtbl.add constant_tag_tables (tag_table_name (vi,r)) (vi,r)

(* Operations on effects *)

let ef_union ef1 ef2 = 
  { 
    jc_effect_alloc_table = 
      AllocMap.merge LogicLabelSet.union
	ef1.jc_effect_alloc_table ef2.jc_effect_alloc_table;
    jc_effect_tag_table = 
      TagMap.merge LogicLabelSet.union
	ef1.jc_effect_tag_table ef2.jc_effect_tag_table;
    jc_effect_memories = 
      MemoryMap.merge LogicLabelSet.union
	ef1.jc_effect_memories ef2.jc_effect_memories;
    jc_effect_globals = 
      VarMap.merge LogicLabelSet.union 
	ef1.jc_effect_globals ef2.jc_effect_globals;
    jc_effect_mutable =
      StringSet.union
	ef1.jc_effect_mutable ef2.jc_effect_mutable;
    jc_effect_committed =
      StringSet.union
	ef1.jc_effect_committed ef2.jc_effect_committed;
  }

let ef_assoc ?label_assoc region_assoc ef =
  let transpose_labels labs =
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
  in
  let transpose_region r =
    if Region.polymorphic r then
      try Some (RegionList.assoc r region_assoc)
      with Not_found -> None 
	(* Local region not counted as effect for the caller *)
    else Some r
  in
  { ef with 
      jc_effect_alloc_table = 
        AllocMap.fold 
	  (fun (ac,r) labs acc ->
	     let labs = transpose_labels labs in
	     match transpose_region r with
	       | None -> acc
	       | Some r ->
		   if not (Region.polymorphic r) then
		     add_constant_alloc_table (ac,r);
		   AllocMap.add (ac,r) labs acc 
	  ) ef.jc_effect_alloc_table AllocMap.empty;
      jc_effect_tag_table =
        TagMap.fold 
	  (fun (vi,r) labs acc -> 
	     let labs = transpose_labels labs in
	     match transpose_region r with
	       | None -> acc
	       | Some r ->
		   if not (Region.polymorphic r) then
		     add_constant_tag_table (vi,r);
		   TagMap.add (vi,r) labs acc 
	  ) ef.jc_effect_tag_table TagMap.empty;
      jc_effect_memories =
        MemoryMap.fold 
	  (fun (mc,r) labs acc ->
	     let labs = transpose_labels labs in
	     match transpose_region r with
	       | None -> acc
	       | Some r ->
		   if not (Region.polymorphic r) then 
		     add_constant_memory (mc,r);
		   MemoryMap.add (mc,r) labs acc
	  ) ef.jc_effect_memories MemoryMap.empty;
      jc_effect_globals =
        VarMap.fold 
	  (fun v labs acc -> VarMap.add v (transpose_labels labs) acc)
	  ef.jc_effect_globals VarMap.empty;
  }

let same_effects ef1 ef2 =
  let eq = LogicLabelSet.equal in
  AllocMap.equal eq ef1.jc_effect_alloc_table ef2.jc_effect_alloc_table
  && TagMap.equal eq ef1.jc_effect_tag_table ef2.jc_effect_tag_table
  && MemoryMap.equal eq ef1.jc_effect_memories ef2.jc_effect_memories
  && VarMap.equal eq ef1.jc_effect_globals ef2.jc_effect_globals
  && StringSet.equal ef1.jc_effect_mutable ef2.jc_effect_mutable
  && StringSet.equal ef1.jc_effect_committed ef2.jc_effect_committed
    
(* Operations on function effects *)

let fef_reads ef =
  { 
    jc_reads = ef;
    jc_writes = empty_effects;
    jc_raises = ExceptionSet.empty;
  }

let fef_union fef1 fef2 =
  { 
    jc_reads = ef_union fef1.jc_reads fef2.jc_reads;
    jc_writes = ef_union fef1.jc_writes fef2.jc_writes;
    jc_raises = ExceptionSet.union fef1.jc_raises fef2.jc_raises;
  }

let fef_assoc region_assoc fef =
  { 
    jc_reads = ef_assoc region_assoc fef.jc_reads;
    jc_writes = ef_assoc region_assoc fef.jc_writes;
    jc_raises = fef.jc_raises;
  }

let same_feffects fef1 fef2 =
  same_effects fef1.jc_reads fef2.jc_reads 
  && same_effects fef1.jc_writes fef2.jc_writes 
  && ExceptionSet.equal fef1.jc_raises fef2.jc_raises

(* Addition of a single effect *)
    
let add_alloc_effect lab ef (ac, r) =
  if not (Region.polymorphic r) then add_constant_alloc_table (ac,r);
  let labs = LogicLabelSet.singleton lab in
  { ef with jc_effect_alloc_table = 
      AllocMap.add_merge LogicLabelSet.union 
	(ac,r) labs ef.jc_effect_alloc_table }

let add_tag_effect lab ef (vi,r) =
  if not (Region.polymorphic r) then add_constant_tag_table (vi,r);
  let labs = LogicLabelSet.singleton lab in
  { ef with jc_effect_tag_table = 
      TagMap.add_merge LogicLabelSet.union 
	(vi,r) labs ef.jc_effect_tag_table }

let add_memory_effect lab ef (mc,r) =
  if not (Region.polymorphic r) then add_constant_memory (mc,r);
  let labs = LogicLabelSet.singleton lab in
  { ef with jc_effect_memories = 
      MemoryMap.add_merge LogicLabelSet.union 
	(mc,r) labs ef.jc_effect_memories }
  
let add_global_effect lab ef v =
  let labs = LogicLabelSet.singleton lab in
  { ef with jc_effect_globals = 
      VarMap.add_merge LogicLabelSet.union 
	v labs ef.jc_effect_globals } 

let add_mutable_effect ef pc =
  { ef with jc_effect_mutable = StringSet.add
      (pointer_class_type_name pc) ef.jc_effect_mutable }
  
let add_committed_effect ef pc =
  { ef with jc_effect_committed = StringSet.add
      (pointer_class_type_name pc) ef.jc_effect_committed }

(* Addition of a single read *)

let add_alloc_reads lab fef (ac,r) =
  { fef with jc_reads = add_alloc_effect lab fef.jc_reads (ac,r) }

let add_tag_reads lab fef (vi,r) =
  { fef with jc_reads = add_tag_effect lab fef.jc_reads (vi,r) }

let add_memory_reads lab fef (mc,r) =
  { fef with jc_reads = add_memory_effect lab fef.jc_reads (mc,r) }

let add_global_reads lab fef v =
  { fef with jc_reads = add_global_effect lab fef.jc_reads v }

let add_mutable_reads fef pc =
  { fef with jc_reads = add_mutable_effect fef.jc_reads pc }

let add_committed_reads fef pc =
  { fef with jc_reads = add_committed_effect fef.jc_reads pc }

let add_memory_alloc_reads lab fef (mc,r) =
  let fef = add_memory_reads lab fef (mc,r) in
  let ac = alloc_class_of_mem_class mc in
  add_alloc_reads lab fef (ac,r)

(* Addition of a single write *)

let add_alloc_writes lab fef (ac,r) =
  { fef with jc_writes = add_alloc_effect lab fef.jc_writes (ac,r) }

let add_tag_writes lab fef (vi,r) =
  { fef with jc_writes = add_tag_effect lab fef.jc_writes (vi,r) }

let add_memory_writes lab fef (mc,r) =
  { fef with jc_writes = add_memory_effect lab fef.jc_writes (mc,r) }

let add_global_writes lab fef vi =
  { fef with jc_writes = add_global_effect lab fef.jc_writes vi }

let add_mutable_writes fef pc =
  { fef with jc_writes = add_mutable_effect fef.jc_writes pc }

let add_committed_writes fef pc =
  { fef with jc_writes = add_committed_effect fef.jc_writes pc }

let add_memory_alloc_writes lab fef (mc,r) =
  let fef = add_memory_writes lab fef (mc,r) in
  let ac = alloc_class_of_mem_class mc in
  add_alloc_reads lab fef (ac,r) (* allocation table is read *)

(* Addition of a single exception *)

let add_exception_effect fef exc =
  { fef with jc_raises = ExceptionSet.add exc fef.jc_raises }
  

(******************************************************************************)
(*                                  patterns                                  *)
(******************************************************************************)

(* TODO: check the use of "label" and "r" *)
let rec pattern ef (*label r*) p =
  let r = dummy_region in
  match p#node with
    | JCPstruct(st, fpl) ->
	let ef = add_tag_effect (*label*)LabelHere ef (struct_variant st,r) in
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
(*                             terms and assertions                           *)
(******************************************************************************)

let rec single_term ef t =
  let lab = 
    match t#label with None -> LabelHere | Some lab -> lab
  in
  match t#node with
    | JCTvar vi ->
	true,
	if vi.jc_var_info_static then
	  add_global_effect lab ef vi
	else ef
    | JCToffset(_k,t,st) ->
        let ac = JCalloc_struct (struct_variant st) in
	true,
	add_alloc_effect lab ef (ac,t#region)
    | JCTapp app -> 
	true,
	ef_assoc ~label_assoc:app.jc_app_label_assoc 
	  app.jc_app_region_assoc 
	  app.jc_app_fun.jc_logic_info_effects 
    | JCTderef(t,lab,fi) ->
	let mc = tderef_mem_class t fi in
	let ef = add_memory_effect lab ef (mc,t#region) in
	begin match mc with
	  | JCmem_union _vi -> 
	      false, (* do not call on sub-terms of union *)
	      List.fold_left term ef (tforeign_union t)
	  | JCmem_field _ | JCmem_bitvector ->
	      true, ef
	end
    | JCTcast(t,lab,st)
    | JCTinstanceof(t,lab,st) ->
	true,
	add_tag_effect lab ef (struct_variant st,t#region)
    | JCTmatch(t,ptl) ->
	true,
	List.fold_left pattern ef (List.map fst ptl)
    | JCTconst _ | JCTrange _ | JCTbinary _ | JCTunary _
    | JCTshift _ | JCTold _ | JCTat _ | JCTaddress _
    | JCTbitwise_cast _ | JCTrange_cast _ | JCTreal_cast _ | JCTif _ ->
	true, ef

and term ef t =
  fold_rec_term single_term ef t

let tag ef lab t vi_opt r =
  match vi_opt with
    | None -> ef
    | Some vi -> add_tag_effect lab ef (vi,r)

let single_assertion ef a =
  let lab = 
    match a#label with None -> LabelHere | Some lab -> lab
  in
  match a#node with
    | JCAinstanceof(t,lab,st) -> 
	true,
	add_tag_effect lab ef (struct_variant st,t#region)
    | JCAapp app -> 
	true,
	ef_assoc ~label_assoc:app.jc_app_label_assoc 
	  app.jc_app_region_assoc 
	  app.jc_app_fun.jc_logic_info_effects 
    | JCAmutable(t,st,ta) ->
	true,
	add_mutable_effect
	  (tag ef lab ta (* Yannick: really effect on tag here? *)
	     (Some (struct_variant st)) t#region)
	  (JCtag(st, []))
    | JCAmatch(t,pal) ->
	true,
	List.fold_left pattern ef (List.map fst pal)
    | JCAtrue | JCAfalse | JCAif _ | JCAbool_term _ | JCAnot _
    | JCAold _ | JCAat _ | JCAquantifier _ | JCArelation _
    | JCAand _ | JCAor _ | JCAiff _ | JCAimplies _ 
    | JCAeqtype _ | JCAsubtype _ ->
	true, ef

let assertion ef a =
  fold_rec_term_and_assertion single_term single_assertion ef a


(******************************************************************************)
(*                                locations                                   *)
(******************************************************************************)

let single_location ~in_assigns fef loc =
  let lab = 
    match loc#label with None -> LabelHere | Some lab -> lab
  in
  let fef = match loc#node with
    | JCLvar v ->
	if v.jc_var_info_static then
	  if in_assigns then
	    add_global_writes lab fef v
	  else
	    add_global_reads lab fef v
	else fef
    | JCLderef(locs,lab,fi,r) ->
	let mc = lderef_mem_class locs fi in
	if in_assigns then
	  add_memory_writes lab fef (mc,locs#region)
	else
	  add_memory_reads lab fef (mc,locs#region)
    | JCLat(loc,_lab) ->
	fef
  in true, fef

let single_location_set fef locs =
  let lab = 
    match locs#label with None -> LabelHere | Some lab -> lab
  in
  let fef = match locs#node with
    | JCLSvar v ->
	if v.jc_var_info_static then
	  add_global_reads lab fef v
	else fef
    | JCLSderef(locs,lab,fi,r) ->
	let mc = lderef_mem_class locs fi in
	add_memory_reads lab fef (mc,locs#region)
    | JCLSrange(locs,_t1_opt,_t2_opt) ->
	fef
  in true, fef

let location ~in_assigns fef loc =
  fold_rec_location 
    (single_location ~in_assigns) single_location_set fef loc

(******************************************************************************)
(*                                expressions                                 *)
(******************************************************************************)

let single_term fef t = 
  let cont,ef = single_term fef.jc_reads t in
  cont,{ fef with jc_reads = ef }

let single_assertion fef a = 
  let cont,ef = single_assertion fef.jc_reads a in
  cont,{ fef with jc_reads = ef }

let rec expr fef e =
  fold_rec_expr_and_term_and_assertion single_term single_assertion
    (single_location ~in_assigns:true) single_location_set
    (fun (fef : fun_effect) e -> match e#node with
       | JCEvar vi ->
	   true,
	   if vi.jc_var_info_static then
	     add_global_reads LabelHere fef vi
	   else fef
       | JCEassign_var(vi,_e) -> 
	   true,
	   if vi.jc_var_info_static then
	     add_global_writes LabelHere fef vi
	   else fef
       | JCEoffset(_k,e,st) ->
	   let ac = JCalloc_struct (struct_variant st) in
	   true,
	   add_alloc_reads LabelHere fef (ac,e#region)
       | JCEapp app -> 
	   let fef_call = match app.jc_call_fun with
	     | JClogic_fun f -> 
		 fef_reads 
		   (ef_assoc ~label_assoc:app.jc_call_label_assoc 
		      app.jc_call_region_assoc
		      f.jc_logic_info_effects)
	     | JCfun f -> 
		 fef_assoc app.jc_call_region_assoc f.jc_fun_info_effects 
	   in
	   true,
	   fef_union fef_call fef
       | JCEderef(e,fi) -> 
	   let mc = deref_mem_class e fi in
	   let fef = add_memory_alloc_reads LabelHere fef (mc,e#region) in
	   begin match mc with
	     | JCmem_union _vi -> 
		 false, (* do not call on sub-expressions of union *)
		 List.fold_left expr fef (foreign_union e)
	     | JCmem_field _ | JCmem_bitvector ->
		 true, fef
	   end
       | JCEassign_heap(e1,fi,_e2) ->
	   let mc = deref_mem_class e1 fi in
	   let fef = add_memory_alloc_writes LabelHere fef (mc,e1#region) in
	   begin match mc with
	     | JCmem_union _vi -> 
		 false, (* do not call on sub-expressions of union *)
		 List.fold_left expr fef (foreign_union e1)
	     | JCmem_field _ | JCmem_bitvector ->
		 true, fef
	   end
       | JCEcast(e,st)
       | JCEinstanceof(e,st) -> 
	   true,
	   add_tag_reads LabelHere fef (struct_variant st,e#region)
       | JCEalloc(_e1,st) ->
	   let pc = JCtag(st,[]) in
	   let fields = all_memories ~select:fully_allocated pc in
	   let allocs = all_allocs ~select:fully_allocated pc in
	   let tags = all_tags ~select:fully_allocated pc in
	   let fef = 
	     List.fold_left 
	       (fun fef fi -> 
		  let mc = JCmem_field fi in
		  add_memory_writes LabelHere fef (mc,e#region)
	       ) fef fields
	   in
	   let fef = 
	     List.fold_left
	       (fun fef ac -> add_alloc_writes LabelHere fef (ac,e#region))
	       fef allocs
	   in
	   true,
	   List.fold_left 
	     (fun fef vi -> add_tag_writes LabelHere fef (vi,e#region))
	     fef tags
       | JCEfree e ->
	   let pc = pointer_class e#typ in
	   let ac = alloc_class_of_pointer_class pc in
	   true,
	   add_alloc_writes LabelHere fef (ac,e#region)
       | JCEpack(st,e,_st) ->
	   (* Assert the invariants of the structure 
	      => need the reads of the invariants *)
	   let (_, invs) = 
	     Hashtbl.find Jc_typing.structs_table st.jc_struct_info_name 
	   in
	   let fef =
	     List.fold_left
	       (fun fef (li, _) -> 
		  { fef with jc_reads = 
		      ef_union fef.jc_reads li.jc_logic_info_effects })
	       fef
	       invs
	   in
	   (* Fields *)
	   let fef = List.fold_left
	     (fun fef fi ->
		match fi.jc_field_info_type with
		  | JCTpointer(pc, _, _) ->
	              (* Assert fields fully mutable 
			 => need mutable and tag_table (of field) as reads *)
		      let fef = add_mutable_reads fef pc in
		      let fef = 
			add_tag_reads LabelHere fef 
			  (pointer_class_variant pc,e#region) 
		      in
	              (* Modify field's "committed" field 
			 => need committed (of field) as reads and writes *)
		      let fef = add_committed_reads fef pc in
		      let fef = add_committed_writes fef pc in
		      (* ...and field as reads *)
		      add_memory_reads LabelHere fef (JCmem_field fi,e#region)
		  | _ -> fef)
	     fef
	     st.jc_struct_info_fields in
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
		match fi.jc_field_info_type with
		  | JCTpointer(st, _, _) ->
	              (* Modify field's "committed" field
			 => need committed (of field) as reads and writes *)
		      let fef = add_committed_reads fef st in
		      let fef = add_committed_writes fef st in
		      (* ...and field as reads *)
		      add_memory_reads LabelHere fef (JCmem_field fi,e#region)
		  | _ -> fef)
	     fef
	     st.jc_struct_info_fields in
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
		      jc_raises = ExceptionSet.remove exc fef.jc_raises }
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
	   { fef with jc_reads = ef_union fef.jc_reads pef }
       | JCEloop _ | JCElet _ | JCEassert _ | JCEcontract _ | JCEblock _ 
       | JCEconst _  | JCEshift _ | JCEif _ | JCErange_cast _
       | JCEreal_cast _ | JCEunary _ | JCEaddress _ | JCEbinary _ 
       | JCEreturn_void  | JCEreturn _ | JCEbitwise_cast _ ->
	   true, fef
    ) fef e

let behavior fef (_pos,_id,b) =
  let fef = 
    fold_rec_behavior single_term single_assertion
      (single_location ~in_assigns:true) single_location_set fef b
  in
  Option_misc.fold_left add_exception_effect fef b.jc_behavior_throws

let spec fef s = 
  let fef = List.fold_left behavior fef s.jc_fun_behavior in
  let fef = { fef with jc_reads = assertion fef.jc_reads s.jc_fun_requires } in
  { fef with jc_reads = assertion fef.jc_reads s.jc_fun_free_requires }

(* Yannick: why add effects for parameters? *)

(* let parameter fef v = *)
(*   match v.jc_var_info_type with *)
(*     | JCTpointer(pc,_,_) -> *)
(* 	let vi = pointer_class_variant pc in *)
(* 	let ac = alloc_class_of_pointer_class pc in *)
(* 	add_alloc_reads (add_tag_reads LabelOld ef vi) (ac,v.jc_var_info_region) *)
(*     | _ -> ef *)
	
(* computing the fixpoint *)

let fixpoint_reached = ref false

let logic_fun_effects f = 
  let f,ta = 
    Hashtbl.find Jc_typing.logic_functions_table f.jc_logic_info_tag 
  in
  let ef = f.jc_logic_info_effects in
  let ef = match ta with
    | JCTerm t -> term ef t 
    | JCAssertion a -> assertion ef a
    | JCReads loclist ->
	List.fold_left
	  (fun ef loc ->
	     let fef = location ~in_assigns:false empty_fun_effect loc in
	     ef_union ef fef.jc_reads 
	  ) ef loclist
  in
  if same_effects ef f.jc_logic_info_effects then () else
    (fixpoint_reached := false;
     f.jc_logic_info_effects <- ef)

let fun_effects fi =
  let (f,_pos,s,e_opt) = 
    Hashtbl.find Jc_typing.functions_table fi.jc_fun_info_tag 
  in
  let fef = f.jc_fun_info_effects in
  let fef = spec fef s in
  let fef = Option_misc.fold_left expr fef e_opt in
(*   let fef = List.fold_left parameter fef f.jc_fun_info_parameters in *)
  if same_feffects fef f.jc_fun_info_effects then () else
    (fixpoint_reached := false;
     f.jc_fun_info_effects <- fef)

let print_list_assoc_label pr fmt ls =
  fprintf fmt "%a" 
    (print_list comma 
       (fun fmt (k,labs) ->
	  fprintf fmt "%a (%a)" 
	    pr k
	    (print_list comma Jc_output_misc.label)
	    (LogicLabelSet.elements labs))
    ) ls

let print_memory fmt (mc,r) =
  fprintf fmt "(%a,%a)" Jc_output_misc.memory_class mc Region.print r

let print_alloc_table fmt (ac,r) =
  fprintf fmt "(%a,%a)" Jc_output_misc.alloc_class ac Region.print r

let print_tag_table fmt (vi,r) =
  fprintf fmt "(%s,%a)" vi.jc_variant_info_name Region.print r

let print_global fmt v =
  fprintf fmt "%s" v.jc_var_info_name

let print_exception fmt exc =
  fprintf fmt "%s" exc.jc_exception_info_name

let print_effect fmt ef =
  fprintf fmt 
"@[@[ alloc_table: @[%a@]@]@\n\
@[ tag_table: @[%a@]@]@\n\
@[ memories: @[%a@]@]@\n\
@[ globals: @[%a@]@]@]@." 
    (print_list_assoc_label print_alloc_table)
    (AllocMap.elements ef.jc_effect_alloc_table)
    (print_list_assoc_label print_tag_table)
    (TagMap.elements ef.jc_effect_tag_table)
    (print_list_assoc_label print_memory)
    (MemoryMap.elements ef.jc_effect_memories)
    (print_list_assoc_label print_global)
    (VarMap.elements ef.jc_effect_globals)

let logic_effects funs =
  fixpoint_reached := false;
  while not !fixpoint_reached do
    fixpoint_reached := true;
    Jc_options.lprintf "Effects: doing one iteration...@.";
    List.iter logic_fun_effects funs
  done;
  Jc_options.lprintf "Effects: fixpoint reached@.";
  List.iter
    (fun f ->
       Jc_options.lprintf "Effects for logic function %s:@\n%a@."
	 f.jc_logic_info_name print_effect f.jc_logic_info_effects
    ) funs
    
let function_effects funs =
  fixpoint_reached := false;
  while not !fixpoint_reached do
    fixpoint_reached := true;
    Jc_options.lprintf "Effects: doing one iteration...@.";
    List.iter fun_effects funs
  done;
  Jc_options.lprintf "Effects: fixpoint reached@.";

  (* Global variables that are only read are translated into logic 
     functions in Why, and thus they should not appear in effects. *)
  Jc_options.lprintf "Effects: removing global reads w/o writes@.";
  List.iter
    (fun f ->
       let fef = f.jc_fun_info_effects in
       let efr = fef.jc_reads.jc_effect_globals in
       let efw = fef.jc_writes.jc_effect_globals in
       let ef = 
	 VarMap.filter 
	   (fun v _labs -> VarMap.mem v efw || v.jc_var_info_assigned) efr
       in
       let ef = { fef.jc_reads with jc_effect_globals = ef } in
       f.jc_fun_info_effects <- { fef with jc_reads = ef }
    ) funs;

  List.iter
    (fun f ->
       Jc_options.lprintf
	 "Effects for function %s:@\n\
@[ reads: %a@]@\n\
@[ writes: %a@]@\n\
@[ raises: %a@]@." 
	 f.jc_fun_info_name
	 print_effect f.jc_fun_info_effects.jc_reads
	 print_effect f.jc_fun_info_effects.jc_writes
	 (print_list comma print_exception)
	 (ExceptionSet.elements f.jc_fun_info_effects.jc_raises)
    ) funs


(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
