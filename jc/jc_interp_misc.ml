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

open Jc_stdlib
open Jc_env
open Jc_envset
open Jc_region
open Jc_ast
open Jc_fenv

open Jc_name
open Jc_constructors
open Jc_pervasives
open Jc_struct_tools

open Output

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
let why_unit_type = simple_logic_type "unit"

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
  | JCalloc_bitvector -> why_unit_type

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

(* pointer model types *)

let pointer_type ac pc = 
  match ac with
    | JCalloc_struct _ | JCalloc_union _ ->
	raw_pointer_type (pointer_class_model_type pc)
    | JCalloc_bitvector ->
	raw_pointer_type why_unit_type

(* translation *)

let tr_native_type = function
  | Tunit -> "unit"
  | Tboolean -> "bool"
  | Tinteger -> "int"
  | Treal -> "real"
  | Tstring -> "string"

let tr_base_type ?region = function
  | JCTnative ty -> 
      simple_logic_type (tr_native_type ty)
  | JCTlogic s -> 
      simple_logic_type s
  | JCTenum ri -> 
      simple_logic_type ri.jc_enum_info_name
  | JCTpointer(pc, _, _) ->
      let ac = match region with 
	| None -> 
	    alloc_class_of_pointer_class pc
	| Some r ->
	    if Region.bitwise (the region) then JCalloc_bitvector
	    else alloc_class_of_pointer_class pc
      in
      pointer_type ac pc
  | JCTnull | JCTany -> assert false
  | JCTtype_var _ -> assert false (* TODO (need environment) *)

let tr_type ~region ty = Base_type (tr_base_type ~region ty)

let tr_var_base_type v = 
  tr_base_type ~region:v.jc_var_info_region v.jc_var_info_type

let tr_var_type v = 
  tr_type ~region:v.jc_var_info_region v.jc_var_info_type

(* model types *)

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


let logic_enum_of_int ri = ri.jc_enum_info_name ^ "_of_integer"
let safe_fun_enum_of_int ri = "safe_" ^ ri.jc_enum_info_name ^ "_of_integer_"
(* Yannick: why have both logic_enum_of_int and safe_fun_enum_of_int? *)
let fun_enum_of_int ri = ri.jc_enum_info_name ^ "_of_integer_"
let logic_int_of_enum ri = "integer_of_" ^ ri.jc_enum_info_name
let mod_of_enum ri = "mod_" ^ ri.jc_enum_info_name ^ "_of_integer"
let fun_any_enum ri = "any_" ^ ri.jc_enum_info_name
let eq_of_enum ri = "eq_" ^ ri.jc_enum_info_name

let logic_bitvector_of_enum ri = "bitvector_of_" ^ ri.jc_enum_info_name
let logic_enum_of_bitvector ri = ri.jc_enum_info_name  ^ "_of_bitvector"

let logic_union_of_field fi = "bitvector_of_" ^ fi.jc_field_info_name
let logic_field_of_union fi = fi.jc_field_info_name ^ "_of_bitvector"


let any_value = function
  | JCTnative ty -> 
      begin match ty with
	| Tunit -> Void
	| Tboolean -> App(Var "any_bool", Void)
	| Tinteger -> App(Var "any_int", Void)
	| Treal -> App(Var "any_real", Void)
	| Tstring -> App(Var "any_string", Void)
      end
  | JCTnull 
  | JCTpointer _ -> App(Var "any_pointer", Void)
  | JCTenum ri -> App (Var(fun_any_enum ri), Void)
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
  if label_in_name then 
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

let param ~type_safe v = 
  v.jc_var_info_final_name, 
  if type_safe then
    tr_base_type v.jc_var_info_type 
  else
    tr_base_type ~region:v.jc_var_info_region v.jc_var_info_type 

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
      infunction.jc_fun_info_effects.jc_writes.jc_effect_alloc_tables
  else true

let mutable_tag_table infunction (vi,r) =
  if Region.polymorphic r then
    TagMap.mem (vi,r)
      infunction.jc_fun_info_effects.jc_writes.jc_effect_tag_tables
  else true

let plain_memory_var (mc,r) = Var (memory_name (mc,r))
let deref_memory_var (mc,r) = Deref (memory_name (mc,r))

let memory_var ?(test_current_function=false) (mc,r) =
  if test_current_function && !current_function = None then
    plain_memory_var (mc,r)
  else if mutable_memory (get_current_function ()) (mc,r) then
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


(*****************************************************************************)
(*                                  Unions                                   *)
(*****************************************************************************)

type shift_offset = 
  | Int_offset of string
  | Expr_offset of Jc_fenv.expr 
  | Term_offset of Jc_fenv.term 

let offset_of_expr e =
  match e#node with
    | JCEconst (JCCinteger s) -> Int_offset s
    | _ -> Expr_offset e

let offset_of_term t =
  match t#node with
    | JCTconst (JCCinteger s) -> Int_offset s
    | _ -> Term_offset t

let mult_offset i off =
  match off with
    | Int_offset j -> Int_offset (string_of_int (i * (int_of_string j)))
    | Expr_offset _ -> assert false (* TODO *)
    | Term_offset _ -> assert false (* TODO *)

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

let possible_union_access e fi_opt = 
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
	    Some(e,Int_offset "0")
	  else None
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
  the (possible_union_access e fi_opt)

let tpossible_union_access t fi_opt =
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
	  begin match access t1 with
	    | Some(t3,off1) ->
		let off2 = offset_of_term t2 in
		let siz = struct_size_in_bytes (pointer_struct t1#typ) in
		let off2 = mult_offset siz off2 in
		Some (t3, add_offset off1 off2)
	    | None -> None
	  end
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

let tdestruct_union_access t fi_opt = 
  the (tpossible_union_access t fi_opt)

let lpossible_union_access t fi = None (* TODO *)

let ldestruct_union_access loc fi_opt = 
  the (lpossible_union_access loc fi_opt)

let foreign_union e = [] (* TODO: subterms of union that are not in union *)
let tforeign_union t = []

let common_deref_alloc_class ~type_safe union_access e =
  if not type_safe && Region.bitwise e#region then
    JCalloc_bitvector
  else match union_access e None with 
    | None -> JCalloc_struct (struct_variant (pointer_struct e#typ))
    | Some(e,_off) -> JCalloc_union (union_type e#typ)

let deref_alloc_class e =
  common_deref_alloc_class ~type_safe:false possible_union_access e
  
let tderef_alloc_class ~type_safe t =
  common_deref_alloc_class ~type_safe tpossible_union_access t

let lderef_alloc_class ~type_safe locs =
  common_deref_alloc_class ~type_safe lpossible_union_access locs

let common_deref_mem_class ~type_safe union_access e fi =
  if not type_safe && Region.bitwise e#region then
    JCmem_bitvector
  else match union_access e (Some fi) with 
    | None -> JCmem_field fi
    | Some(e,_off) -> JCmem_union (union_type e#typ)

let deref_mem_class e fi =
  common_deref_mem_class ~type_safe:false possible_union_access e fi

let tderef_mem_class ~type_safe t fi =
  common_deref_mem_class ~type_safe tpossible_union_access t fi

let lderef_mem_class ~type_safe locs fi =
  common_deref_mem_class ~type_safe lpossible_union_access locs fi


(******************************************************************************)
(*                           locations and separation                         *)
(******************************************************************************)

let ref_term : (type_safe:bool -> global_assertion:bool -> relocate:bool 
		 -> label -> label -> Jc_fenv.term -> Output.term) ref 
    = ref (fun ~type_safe ~global_assertion ~relocate _ _ _ -> assert false)

let rec location ~type_safe ~global_assertion lab loc = 
  let flocs = location_set ~type_safe ~global_assertion lab in
  match loc#node with
    | JCLvar _v ->
	LVar "pset_empty"
    | JCLderef(locs,_lab,_fi,_r) ->
	flocs locs
    | _ -> assert false (* TODO *)

and location_set ~type_safe ~global_assertion lab locs = 
  let flocs = location_set ~type_safe ~global_assertion lab in
  let ft = !ref_term ~type_safe ~global_assertion ~relocate:false lab lab in
  match locs#node with
    | JCLSvar v ->
	LApp("pset_singleton",[ tvar ~label_in_name:global_assertion lab v ])
    | JCLSderef(locs,lab,fi,r) ->
	let mc = lderef_mem_class ~type_safe locs fi in
        let mem = 
	  tmemory_var ~label_in_name:global_assertion lab (mc,locs#region) 
	in
	LApp("pset_deref",[ mem; flocs locs ])
    | JCLSrange(locs,Some t1,Some t2) ->
	LApp("pset_range",[ flocs locs; ft t1; ft t2 ])
    | JCLSrange(locs,None,Some t2) ->
	LApp("pset_range_left",[ flocs locs; ft t2 ])
    | JCLSrange(locs,Some t1,None) ->
	LApp("pset_range_right",[ flocs locs; ft t1 ])
    | JCLSrange(locs,None,None) ->
	LApp("pset_all",[ flocs locs ])

let rec location_list' = function
  | [] -> LVar "pset_empty"
  | [e'] -> e'
  | e' :: el' -> LApp("pset_union",[ e'; location_list' el' ])

let separation_condition loclist loclist' =
  let floc = location ~type_safe:false ~global_assertion:false LabelHere in
  let pset = location_list' (List.map floc loclist) in
  let pset' = location_list' (List.map floc loclist') in
  LPred("pset_disjoint",[ pset; pset' ])

type memory_effect = RawMemory of Memory.t | PreciseMemory of Location.t

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
      | JCEcast (e1, st) -> JCTcast (term e1, LabelHere, st)
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
(* 	  let ptl = List.map (fun (p, e) -> (p, term_of_expr e)) pel in *)
(* 	    JCTmatch (term_of_expr e, ptl) *)
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
    Some(new location_with ~node:loc_node e)
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
  new location_set_with ~node:locs_node e

let location_set_of_expr e =
  try Some(location_set_of_expr e) with Failure "No location for expr" -> None

let rec location_of_term t = 
  try
    let loc_node = match t#node with
      | JCTvar v -> 
	  JCLvar v
      | JCTderef(t1,lab,fi) ->
	  JCLderef(location_set_of_term t1, LabelHere, fi, t#region)
      | _ -> failwith "No location for term"
    in
    Some(new location_with ~node:loc_node t)
  with Failure "No location for term" -> None

and location_set_of_term t =
  let locs_node = match t#node with
    | JCTvar v -> 
	JCLSvar v
    | JCTderef(t1,lab,fi) ->
	JCLSderef(location_set_of_term t1, LabelHere, fi, t#region)
    | _ -> failwith "No location for term"
  in
  new location_set_with ~node:locs_node t

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
  if Region.polymorphic r then
    try Some (RegionList.assoc r region_assoc)
    with Not_found -> None (* Local region *)
  else Some r

let rec transpose_location ~region_assoc ~param_assoc (loc,(mc,rdist)) =
  match transpose_region ~region_assoc rdist with
    | None -> None
    | Some rloc ->
	try
	  let node = match loc#node with
	    | JCLvar v ->
		if v.jc_var_info_static then
		  JCLvar v
		else
		  begin match List.mem_assoc_eq VarOrd.equal v param_assoc with
		    | None -> (* Local variable *)
			failwith "Cannot transpose location"
		    | Some e -> 
			match location_of_expr e with
			  | None -> failwith "Cannot transpose location"
			  | Some loc' -> loc'#node
		  end
	    | JCLderef(locs,lab,fi,r) ->
		let locs = 
		  transpose_location_set ~region_assoc ~param_assoc locs
		in
		JCLderef(locs,lab,fi,r) (* TODO: remove useless lab & r *)
	    | _ -> assert false (* TODO *)
	  in
	  let loc = new location_with ~region:rloc ~node loc in
	  Some(PreciseMemory(loc,(mc,rloc)))
	with Failure "Cannot transpose location" ->
	  Some(RawMemory(mc,rloc))

and transpose_location_set ~region_assoc ~param_assoc locs =
  match transpose_region ~region_assoc locs#region with
    | None -> failwith "Cannot transpose location"
    | Some rloc ->
	let node = match locs#node with
	  | JCLSvar v ->
	      if v.jc_var_info_static then
		JCLSvar v
	      else
		begin match List.mem_assoc_eq VarOrd.equal v param_assoc with
		  | None -> (* Local variable *)
		      failwith "Cannot transpose location"
		  | Some e -> 
		      match location_set_of_expr e with
			| None -> failwith "Cannot transpose location"
			| Some locs' -> locs'#node
	      end
	  | JCLSderef(locs',lab,fi,r) ->
	      let locs' = 
		transpose_location_set ~region_assoc ~param_assoc locs'
	      in
	      JCLSderef(locs',lab,fi,r) (* TODO: remove useless lab & r *)
	  | _ -> assert false (* TODO *)
	in
	new location_set_with ~region:rloc ~node locs

let transpose_location_set ~region_assoc ~param_assoc locs w=
  try Some(transpose_location_set ~region_assoc ~param_assoc locs)
  with Failure "Cannot transpose location" -> None

let transpose_location_list
    ~region_assoc ~param_assoc rw_raw_mems rw_precise_mems (mc,distr) =
  let loclist =
    if MemorySet.mem (mc,distr) rw_raw_mems then
      assert false (* TODO: paremeters *)
    else
      LocationSet.to_list
	(LocationSet.filter
	   (fun (_loc,(_mc,r)) -> Region.equal r distr)
	   rw_precise_mems)
  in
  List.fold_left
    (fun acc (loc,(mc,rdist)) ->
       match transpose_location ~region_assoc ~param_assoc (loc,(mc,rdist)) with
	 | None -> acc
	 | Some(RawMemory(mc,rloc)) -> assert false
	 | Some(PreciseMemory(loc,(mc,rloc))) ->
	     loc :: acc
    ) [] loclist

let write_read_separation_condition 
    ~callee_reads ~callee_writes ~region_assoc ~param_assoc 
    inter_names writes reads =
  List.fold_left
    (fun acc ((mc,distr),(v,_ty')) ->
       let n = var_name' v in
       if StringSet.mem n inter_names then
	 (* There is a read/write interference on this memory *)
	 List.fold_left 
	   (fun acc ((mc',distr'),(v',_ty')) ->
	      let n' = var_name' v' in
	      if n = n' then
		let rw_raw_mems =
		  MemorySet.of_list
		    (MemoryMap.keys callee_reads.jc_effect_raw_memories
		     @ MemoryMap.keys callee_writes.jc_effect_raw_memories)
		in
		let rw_precise_mems =
		  LocationSet.of_list
		    (LocationMap.keys callee_reads.jc_effect_precise_memories
		     @ 
		     LocationMap.keys callee_writes.jc_effect_precise_memories)
		in
		let loclist =
		  transpose_location_list ~region_assoc ~param_assoc
		    rw_raw_mems rw_precise_mems (mc,distr)
		in
		let loclist' =
		  transpose_location_list ~region_assoc ~param_assoc
		    rw_raw_mems rw_precise_mems (mc',distr')
		in
		assert (loclist <> []);
		assert (loclist' <> []);
		let pre = separation_condition loclist loclist' in
		make_and pre acc
	      else acc
	   ) acc writes
       else acc
    ) LTrue reads

let write_write_separation_condition 
    ~callee_reads ~callee_writes ~region_assoc ~param_assoc
    ww_inter_names writes reads =
  let writes = 
    List.filter 
      (fun ((mc,distr),(v,_ty)) -> 
	 let n = var_name' v in
	 StringSet.mem n ww_inter_names
      ) writes 
  in
  let write_pairs = List.all_pairs writes in
  List.fold_left
    (fun acc (((mc,distr),(v,_ty)), ((mc',distr'),(v',_ty'))) ->
       let n = var_name' v in
       let n' = var_name' v' in
       if n = n' then
	 (* There is a write/write interference on this memory *)
	 let rw_raw_mems =
	   MemorySet.of_list
	     (MemoryMap.keys callee_reads.jc_effect_raw_memories
	      @ MemoryMap.keys callee_writes.jc_effect_raw_memories)
	 in
	 let rw_precise_mems =
	   LocationSet.of_list
	     (LocationMap.keys callee_reads.jc_effect_precise_memories
	      @ 
	      LocationMap.keys callee_writes.jc_effect_precise_memories)
	 in
	 let loclist =
	   transpose_location_list ~region_assoc ~param_assoc
	     rw_raw_mems rw_precise_mems (mc,distr)
	 in
	 let loclist' =
	   transpose_location_list ~region_assoc ~param_assoc
	     rw_raw_mems rw_precise_mems (mc',distr')
	 in
	 assert (loclist <> []);
	 assert (loclist' <> []);
	 let pre = separation_condition loclist loclist' in
	 make_and pre acc
       else acc
    ) LTrue write_pairs


(******************************************************************************)
(*                                  effects                                   *)
(******************************************************************************)

let rec all_possible_memory_effects acc r ty =
  match ty with
    | JCTpointer(pc,_,_) ->
	begin match pc with
	  | JCunion _ | JCvariant _ -> acc (* TODO *)
	  | JCtag(st,_) ->
	      List.fold_left 
		(fun acc fi ->
		   let mc = JCmem_field fi in
		   let mem = mc,r in
		   if MemorySet.mem mem acc then 
		     acc
		   else
		     all_possible_memory_effects 
		       (MemorySet.add mem acc) r fi.jc_field_info_type
		) acc st.jc_struct_info_fields
	end
    | JCTnative _
    | JCTnull 
    | JCTenum _
    | JCTlogic _
    | JCTany -> acc
    | JCTtype_var _ -> assert false (* TODO: need environment *)


let rewrite_effects ~type_safe ~params ef =
  let all_mems = 
    List.fold_left 
      (fun acc v ->
	 all_possible_memory_effects acc v.jc_var_info_region v.jc_var_info_type
      ) MemorySet.empty params
  in
  if not type_safe then ef else
    { ef with
	jc_effect_memories = 
	MemoryMap.fold 
	  (fun (mc,r) labs acc ->
	     match mc with
	       | JCmem_field _ | JCmem_union _ -> 
		   MemoryMap.add (mc,r) labs acc
	       | JCmem_bitvector ->
		   MemorySet.fold 
		     (fun (mc',r') acc ->
			if Region.equal r r' then 
			  MemoryMap.add (mc',r') labs acc
			else acc
		     ) all_mems acc
	  ) ef.jc_effect_memories MemoryMap.empty
    }


(******************************************************************************)
(*                               call arguments                               *)
(******************************************************************************)

type param_or_effect_mode = MParam | MLocal | MEffect

let add_alloc_table_argument 
    ~mode ~type_safe ~no_deref (ac,distr) region_assoc acc =
  let allocvar = if no_deref then plain_alloc_table_var else alloc_table_var in
  let ty' = alloc_table_type ac in
  if Region.polymorphic distr then
    try 
      (* Polymorphic allocation table. Both passed in argument by the caller, 
	 and counted as effect. *)
      let locr = RegionList.assoc distr region_assoc in
      if not type_safe && Region.bitwise locr then
	(* Bitwise allocation table in the caller. Translate the allocation 
	   class and accumulate it only if not already present. *)
	let locac = JCalloc_bitvector in
	let locty' = alloc_table_type locac in
	let v1' = allocvar (locac,locr) in
	if List.exists 
	  (fun (v2',_ty') -> var_name' v1' = var_name' v2') acc then acc
	else
	  match mode with
	    | MParam | MEffect -> (v1', locty') :: acc 
	    | MLocal -> acc
      else
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

let alloc_table_writes ~mode ~type_safe ~callee_writes ~region_assoc =
  AllocMap.fold
    (fun (ac,distr) _labs acc ->
       add_alloc_table_argument 
	 ~mode ~type_safe ~no_deref:true (ac,distr) region_assoc acc
    ) callee_writes.jc_effect_alloc_tables []

let alloc_table_reads 
    ~mode ~type_safe ~callee_writes ~callee_reads ~region_assoc =
  AllocMap.fold
    (fun (ac,distr) _labs acc ->
       if AllocMap.mem (ac,distr) callee_writes.jc_effect_alloc_tables then
	 (* Allocation table is written, thus it is already taken care of
	    as a parameter. *)
	 match mode with
	   | MParam | MLocal -> acc
	   | MEffect ->
	       add_alloc_table_argument 
		 ~mode ~type_safe ~no_deref:false (ac,distr) region_assoc acc
       else if mutable_alloc_table (get_current_function ()) (ac,distr) then
	 add_alloc_table_argument 
	   ~mode ~type_safe ~no_deref:false (ac,distr) region_assoc acc
       else
	 (* Allocation table is immutable, thus it is not passed by
	    reference. As such, it cannot be counted in effects. *)
	 match mode with
	   | MParam | MLocal ->
	       add_alloc_table_argument 
		 ~mode ~type_safe ~no_deref:false (ac,distr) region_assoc acc
	   | MEffect -> acc
    ) callee_reads.jc_effect_alloc_tables []

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

let tag_table_writes ~mode ~callee_writes ~region_assoc =
  TagMap.fold
    (fun (vi,distr) _labs acc ->
       add_tag_table_argument 
	 ~mode ~no_deref:true (vi,distr) region_assoc acc
    ) callee_writes.jc_effect_tag_tables []

let tag_table_reads ~mode ~callee_writes ~callee_reads ~region_assoc =
  TagMap.fold
    (fun (vi,distr) _labs acc ->
       if TagMap.mem (vi,distr) callee_writes.jc_effect_tag_tables then
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
    ) callee_reads.jc_effect_tag_tables []

let add_memory_argument 
    ~mode ~type_safe ~no_deref (mc,distr as mem) region_assoc acc =
  let memvar = 
    if no_deref then plain_memory_var 
    else memory_var ~test_current_function:false
  in
  let ty' = memory_type mc in
  if Region.polymorphic distr then
    try 
      (* Polymorphic memory. Both passed in argument by the caller, 
	 and counted as effect. *)
      let locr = RegionList.assoc distr region_assoc in
      if not type_safe && Region.bitwise locr then
	(* Bitwise memory in the caller. Translate the memory class 
	   and accumulate it only if not already present. *)
	let locmc = JCmem_bitvector in
	let locty' = memory_type locmc in
	let v1' = memvar (locmc,locr) in
	if List.exists 
	  (fun (_mem, (v2',_ty')) -> var_name' v1' = var_name' v2') acc then acc
	else
	  match mode with
	    | MParam | MEffect -> (mem, (v1', locty')) :: acc
	    | MLocal -> acc
      else
	match mode with
	  | MParam | MEffect -> (mem, (memvar (mc,locr), ty')) :: acc
	  | MLocal -> acc
    with Not_found -> 
      (* MLocal memory. Neither passed in argument by the caller, 
	 nor counted as effect. *)
      match mode with
	| MParam | MEffect -> acc
	| MLocal -> (mem, (memvar (mc,distr), ty')) :: acc 
  else 
    (* Constant memory. Not passed in argument by the caller, 
       but counted as effect. *)
    match mode with
      | MParam | MLocal -> acc
      | MEffect -> (mem, (memvar (mc,distr), ty')) :: acc 

let memory_detailed_writes ~mode ~type_safe ~callee_writes ~region_assoc =
  MemoryMap.fold
    (fun (mc,distr) _labs acc -> 
       add_memory_argument 
	 ~mode ~type_safe ~no_deref:true (mc,distr) region_assoc acc
    ) callee_writes.jc_effect_memories []

let memory_writes ~mode ~type_safe ~callee_writes ~region_assoc =
  List.map snd 
    (memory_detailed_writes ~mode ~type_safe ~callee_writes ~region_assoc)

let memory_detailed_reads
    ~mode ~type_safe ~callee_writes ~callee_reads ~region_assoc =
  MemoryMap.fold
    (fun (mc,distr) _labs acc ->
       if MemoryMap.mem (mc,distr) callee_writes.jc_effect_memories then
	 (* Memory is written, thus it is already taken care of
	    as a parameter. *)
	 match mode with
	   | MParam | MLocal -> acc
	   | MEffect ->
	       add_memory_argument 
		 ~mode ~type_safe ~no_deref:false (mc,distr) region_assoc acc
       else if mutable_memory (get_current_function ()) (mc,distr) then
	 add_memory_argument 
	   ~mode ~type_safe ~no_deref:false (mc,distr) region_assoc acc
       else
	 (* Memory is immutable, thus it is not passed by
	    reference. As such, it cannot be counted in effects. *)
	 match mode with
	   | MParam | MLocal ->
	       add_memory_argument 
		 ~mode ~type_safe ~no_deref:false (mc,distr) region_assoc acc
	   | MEffect -> acc
    ) callee_reads.jc_effect_memories []

let memory_reads ~mode ~type_safe ~callee_writes ~callee_reads ~region_assoc =
  List.map snd 
    (memory_detailed_reads
       ~mode ~type_safe ~callee_writes ~callee_reads ~region_assoc)

let global_writes ~callee_writes =
  VarMap.fold
    (fun v _labs acc -> 
       let n,ty' = param ~type_safe:false v in 
       (plain_var n,ty') :: acc
    ) callee_writes.jc_effect_globals []

let global_reads ~callee_reads =
  VarMap.fold
    (fun v _labs acc -> 
       let n,ty' = param ~type_safe:false v in
       (plain_var n,ty') :: acc
    ) callee_reads.jc_effect_globals []

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

let write_model_parameters 
    ~type_safe ~mode ~callee_reads ~callee_writes ~region_assoc ~params =
  let callee_writes = rewrite_effects ~type_safe ~params callee_writes in
  let write_allocs = 
    alloc_table_writes ~mode ~type_safe ~callee_writes ~region_assoc 
  in
  let write_tags = 
    tag_table_writes ~mode ~callee_writes ~region_assoc 
  in
  let write_mems = 
    memory_writes ~mode ~type_safe ~callee_writes ~region_assoc 
  in
  let write_globs = match mode with
    | MParam | MLocal -> []
    | MEffect -> global_writes ~callee_writes
  in
  (* TODO: add mutable and committed effects *)
  write_allocs @ write_tags @ write_mems @ write_globs

let write_parameters 
    ~type_safe ~region_list ~callee_reads ~callee_writes ~params =
  let region_assoc = List.map (fun r -> (r,r)) region_list in
  let vars' = 
    write_model_parameters ~type_safe ~mode:MParam
      ~callee_reads ~callee_writes ~region_assoc ~params
  in
  List.map (function (Var n,ty') -> (n,ty') | _ -> assert false) vars'

let write_locals ~region_list ~callee_reads ~callee_writes ~params =
  let region_assoc = List.map (fun r -> (r,r)) region_list in
  let vars' =
    write_model_parameters ~type_safe:false ~mode:MLocal 
      ~callee_reads ~callee_writes ~region_assoc ~params
  in
  List.map (function (Var n,ty') -> (n,ty') | _ -> assert false) vars'

let write_effects ~callee_reads ~callee_writes ~region_list ~params =
  let region_assoc = List.map (fun r -> (r,r)) region_list in
  let vars' = 
    write_model_parameters ~type_safe:true ~mode:MEffect
      ~callee_reads ~callee_writes ~region_assoc ~params
  in
  List.map (function (Var n,_ty') -> n | _ -> assert false) vars'

let read_model_parameters 
    ~type_safe ~mode ~callee_reads ~callee_writes ~region_assoc ~params =
  let callee_reads = rewrite_effects ~type_safe ~params callee_reads in
  let callee_writes = rewrite_effects ~type_safe ~params callee_writes in
  let read_allocs = 
    alloc_table_reads 
      ~mode ~type_safe ~callee_reads ~callee_writes ~region_assoc 
  in
  let read_tags = 
    tag_table_reads ~mode ~callee_reads ~callee_writes ~region_assoc 
  in
  let read_mems =
    memory_reads ~mode ~type_safe ~callee_reads ~callee_writes ~region_assoc 
  in
  let read_globs = match mode with
    | MParam | MLocal -> []
    | MEffect -> global_reads ~callee_reads
  in
  (* TODO: add mutable and committed effects *)
  read_allocs @ read_tags @ read_mems @ read_globs

let read_parameters 
    ~type_safe ~region_list ~callee_reads ~callee_writes ~params =
  let region_assoc = List.map (fun r -> (r,r)) region_list in
  let vars' = 
    read_model_parameters ~type_safe ~mode:MParam
      ~callee_reads ~callee_writes ~region_assoc ~params
  in
  List.map (function (Var n,ty') -> (n,ty') | _ -> assert false) vars'

let read_locals ~region_list ~callee_reads ~callee_writes ~params =
  let region_assoc = List.map (fun r -> (r,r)) region_list in
  let vars' =
    read_model_parameters ~type_safe:false ~mode:MLocal
      ~callee_reads ~callee_writes ~region_assoc ~params
  in
  List.map (function (Var n,ty') -> (n,ty') | _ -> assert false) vars'

let read_effects ~callee_reads ~callee_writes ~region_list ~params =
  let region_assoc = List.map (fun r -> (r,r)) region_list in
  let vars' = 
    read_model_parameters ~type_safe:true ~mode:MEffect
      ~callee_reads ~callee_writes ~region_assoc ~params
  in
  List.map (var_name' $ fst) vars'

let alloc_table_arguments ~callee_reads ~callee_writes ~region_assoc =
  let writes = 
    alloc_table_writes 
      ~mode:MParam ~type_safe:false ~callee_writes ~region_assoc
  in
  let reads = 
    alloc_table_reads 
      ~mode:MParam ~type_safe:false ~callee_reads ~callee_writes ~region_assoc
  in
  (List.map fst writes), (List.map fst reads)

let tag_table_arguments ~callee_reads ~callee_writes ~region_assoc =
  let writes = 
    tag_table_writes ~mode:MParam ~callee_writes ~region_assoc
  in
  let reads = 
    tag_table_reads 
      ~mode:MParam ~callee_reads ~callee_writes ~region_assoc
  in
  (List.map fst writes), (List.map fst reads)

let specialized_functions = Hashtbl.create 0 

let memory_arguments 
    ~callee_reads ~callee_writes ~region_assoc ~param_assoc fname =
  let writes = 
    memory_detailed_writes
      ~mode:MParam ~type_safe:false ~callee_writes ~region_assoc
  in
  let reads = 
    memory_detailed_reads 
      ~mode:MParam ~type_safe:false ~callee_reads ~callee_writes ~region_assoc
  in
  (* Check if there are duplicates between reads and writes *)
  let write_names = List.map (var_name' $ fst $ snd) writes in
  let read_names = List.map (var_name' $ fst $ snd) reads in
  let rw_inter_names = 
    StringSet.inter 
      (StringSet.of_list write_names) (StringSet.of_list read_names) 
  in
  let rw_pre =
    if StringSet.is_empty rw_inter_names then
      LTrue (* no read/write interference *)
    else
      write_read_separation_condition 
	~callee_reads ~callee_writes ~region_assoc ~param_assoc
	rw_inter_names writes reads
  in
  (* TODO: rewrite postcondition to assert it after the call, when 
     there is an interference. see, e.g., example [separation.c] in Jessie 
     tests.
  *)
  (* Check if there are duplicates between writes *)
  let ww_inter_names = 
    snd (List.fold_left 
	   (fun (first_occur,next_occur) n ->
	      if StringSet.mem n first_occur then
		first_occur, StringSet.add n next_occur
	      else StringSet.add n first_occur, next_occur
	   ) (StringSet.empty,StringSet.empty) write_names)
  in
  let ww_pre =
    if StringSet.is_empty ww_inter_names then
      LTrue (* no write/write interference *)
    else
      write_write_separation_condition 
	~callee_reads ~callee_writes ~region_assoc ~param_assoc
	ww_inter_names writes reads
  in
  let pre = make_and rw_pre ww_pre in
  if pre = LTrue then 
    let writes = List.map (fst $ snd) writes in
    let reads = List.map (fst $ snd) reads in
    LTrue, fname, writes, reads
  else 
    (* Presence of interferences. Function must be specialized. *)
    let new_fname = unique_name (fname ^ "_specialized") in
    let writes, name_assoc, already_used_names = 
      List.fold_right 
	(fun ((mc,distr),(v,_ty)) (acc,name_assoc,already_used_names) ->
	   let n = var_name' v in
	   if StringMap.mem n already_used_names then
	     let ndest = StringMap.find n already_used_names in
	     let nsrc = memory_name (mc,distr) in
	     acc, StringMap.add nsrc ndest name_assoc, already_used_names
	   else
	     let ndest = memory_name (mc,distr) in
	     v :: acc, name_assoc, StringMap.add n ndest already_used_names
	) writes ([], StringMap.empty, StringMap.empty)
    in
    let reads, name_assoc, _ = 
      List.fold_right 
	(fun ((mc,distr),(v,_ty)) (acc,name_assoc,already_used_names) ->
	   let n = var_name' v in
	   if StringMap.mem n already_used_names then
	     let ndest = StringMap.find n already_used_names in
	     let nsrc = memory_name (mc,distr) in
	     acc, StringMap.add nsrc ndest name_assoc, already_used_names
	   else
	     let ndest = memory_name (mc,distr) in
	     v :: acc, name_assoc, StringMap.add n ndest already_used_names
	) reads ([], name_assoc, already_used_names)
    in
    Hashtbl.add specialized_functions new_fname (fname,name_assoc);
    pre, new_fname, writes, reads
  
let global_arguments ~callee_reads ~callee_writes ~region_assoc =
  let writes = global_writes ~callee_writes in
  let reads = global_reads ~callee_reads in
  (List.map fst writes), (List.map fst reads)

let make_arguments 
    ~callee_reads ~callee_writes ~region_assoc ~param_assoc 
    ~with_globals fname args =

  Format.printf "make arguments %a@." (Pp.print_list Pp.comma (fun fmt (r1,r2) -> Format.printf "(%a,%a)" Region.print r1 Region.print r2)) region_assoc;

  let write_allocs, read_allocs = 
    alloc_table_arguments ~callee_reads ~callee_writes ~region_assoc
  in
  let write_tags, read_tags = 
    tag_table_arguments ~callee_reads ~callee_writes ~region_assoc
  in
  let pre_mems, fname, write_mems, read_mems = 
    memory_arguments 
      ~callee_reads ~callee_writes ~region_assoc ~param_assoc fname
  in
  let write_globs, read_globs = 
    if with_globals then
      global_arguments ~callee_reads ~callee_writes ~region_assoc
    else
      [], []
  in
  (* Return complete list of arguments *)
  (* TODO: add mutable and committed effects *)
  let args =
    args
    @ write_allocs @ write_tags @ write_mems @ write_globs
    @ read_allocs @ read_tags @ read_mems @ read_globs
  in
  pre_mems, fname, args

let tmemory_detailed_params ~label_in_name ?region_assoc ?label_assoc reads =
  MemoryMap.fold
    (fun (mc,distr) labs acc ->
       let labs = transpose_labels ?label_assoc labs in
       let locr = match region_assoc with
	 | None -> distr
	 | Some region_assoc -> the (transpose_region ~region_assoc distr) 
       in
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
       let locr = match region_assoc with
	 | None -> distr
	 | Some region_assoc -> the (transpose_region ~region_assoc distr) 
       in
       LogicLabelSet.fold
	 (fun lab acc ->
	    let param = talloc_table_param ~label_in_name lab (ac,locr) in
	    ((ac,locr), param) :: acc
	 ) labs acc
    ) reads.jc_effect_alloc_tables []

let talloc_table_params ~label_in_name ?region_assoc ?label_assoc reads =
  List.map snd
    (talloc_table_detailed_params 
       ~label_in_name ?region_assoc ?label_assoc reads)

let ttag_table_detailed_params ~label_in_name ?region_assoc ?label_assoc reads =
  TagMap.fold
    (fun (vi,distr) labs acc ->
       let labs = transpose_labels ?label_assoc labs in
       let locr = match region_assoc with
	 | None -> distr
	 | Some region_assoc -> the (transpose_region ~region_assoc distr) 
       in
       LogicLabelSet.fold
	 (fun lab acc ->
	    let param = ttag_table_param ~label_in_name lab (vi,locr) in
	    ((vi,locr), param) :: acc
	 ) labs acc
    ) reads.jc_effect_tag_tables []

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
      li.jc_logic_info_effects.jc_effect_alloc_tables
      acc
  in
  TagMap.fold
    (fun v _ acc -> StringSet.add (tag_table_name v) acc)
    li.jc_logic_info_effects.jc_effect_tag_tables
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
	      f.jc_fun_info_effects.jc_writes.jc_effect_alloc_tables 
	    then alloc::acc 
	    else acc
	  else acc*)
	  assert false (* TODO *)
	else alloc::acc)
      ef.jc_effect_alloc_tables
      res
  in
  let res =
    TagMap.fold
      (fun v _ acc -> (tag_table_name v)::acc)
      ef.jc_effect_tag_tables
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




(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
