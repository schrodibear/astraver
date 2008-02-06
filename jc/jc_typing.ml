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

(* $Id: jc_typing.ml,v 1.178 2008-02-06 16:50:44 marche Exp $ *)

open Jc_env
open Jc_envset
open Jc_fenv
open Jc_pervasives
open Jc_ast
open Format
open Jc_region

exception Typing_error of Loc.position * string

let typing_error l = 
  Format.kfprintf 
    (fun fmt -> raise (Typing_error(l, flush_str_formatter()))) 
    str_formatter

let logic_type_table = Hashtbl.create 97

let exceptions_table = Hashtbl.create 97

let enum_types_table = Hashtbl.create 97

let structs_table = Hashtbl.create 97
let variants_table = Hashtbl.create 97

let mutable_fields_table = Hashtbl.create 97 (* structure name (string) -> field info *)
let committed_fields_table = Hashtbl.create 97 (* structure name (string) -> field info *)

let logic_functions_table = Hashtbl.create 97
let logic_functions_env = Hashtbl.create 97
let logic_constants_table = Hashtbl.create 97
let logic_constants_env = Hashtbl.create 97
let functions_table = Hashtbl.create 97
let functions_env = Hashtbl.create 97
let variables_table = Hashtbl.create 97
let variables_env = Hashtbl.create 97

let field_tag_counter = ref 0

let create_mutable_field st =
  incr field_tag_counter;
  let name = "committed_"^st.jc_struct_info_name in
  let fi = {
    jc_field_info_tag = !field_tag_counter;
    jc_field_info_name = name;
    jc_field_info_final_name = Jc_envset.get_unique_name name;
    jc_field_info_type = boolean_type;
    jc_field_info_root = st.jc_struct_info_root;
    jc_field_info_struct = st;
    jc_field_info_rep = false;
  } in
  Hashtbl.add committed_fields_table st.jc_struct_info_name fi

let find_struct_info loc id =
  try
    let st,_ = Hashtbl.find structs_table id in st
  with Not_found ->
    typing_error loc "undeclared structure %s" id

let find_struct_variant st =
  match st.jc_struct_info_root.jc_struct_info_variant with
    | None -> raise Not_found
    | Some vi -> vi

let is_numeric t =
  match t with
    | JCTnative (Tinteger | Treal) -> true
    | JCTenum _ -> true
    | _ -> false

let is_integer t =
  match t with
    | JCTnative Tinteger -> true
    | JCTenum _ -> true
    | _ -> false

let is_root_struct st = 
  match st.jc_struct_info_parent with None -> true | Some _ -> false

let lub_numeric_types t1 t2 =
  match t1,t2 with
    | JCTnative Treal,_ | _,JCTnative Treal -> Treal
    | _ -> Tinteger

let rec substruct st = function
  | (JCtag st') as tov ->
      if st == st' then true else
	begin match st.jc_struct_info_parent with
	  | None -> false
	  | Some p -> substruct p tov
	end
  | JCvariant vi ->
      struct_variant st == vi

let subtype ?(allow_implicit_cast=true) t1 t2 =
  match t1,t2 with
    | JCTnative t1, JCTnative t2 ->
	t1=t2
    | JCTenum ri1, JCTenum ri2 -> 
	true
	  (*
	Num.ge_num ri1.jc_enum_info_min ri2.jc_enum_info_min 	&&
	Num.le_num ri1.jc_enum_info_max ri2.jc_enum_info_max
	  *)
    | JCTenum _, JCTnative Tinteger ->
	true
    | JCTnative Tinteger, JCTenum _ -> 
	allow_implicit_cast 
    | JCTlogic s1, JCTlogic s2 ->
	s1=s2
    | JCTpointer(JCtag s1, _, _), JCTpointer(tov, _, _) -> 
	substruct s1 tov
    | JCTpointer(JCvariant v1, _, _), JCTpointer(JCvariant v2, _, _) ->
	v1 == v2
    | JCTnull, (JCTnull | JCTpointer _) ->
	true
    | _ ->
	false

let subtype_strict = subtype ~allow_implicit_cast:false

let maxtype loc t u =
  if subtype t u then u else
    if subtype u t then t else
      typing_error loc "incompatible result types"

let comparable_types t1 t2 =
  match t1,t2 with
    | JCTnative t1, JCTnative t2 -> t1=t2
    | JCTenum _, JCTenum _ -> true
    | JCTenum _, JCTnative Tinteger -> true
    | JCTnative Tinteger, JCTenum _ -> true
    | JCTlogic s1, JCTlogic s2 -> s1=s2
    | JCTpointer(JCtag s1,_,_), JCTpointer(JCtag s2,_,_) -> 
	s1.jc_struct_info_root == s2.jc_struct_info_root
    | JCTnull, JCTnull -> true
    | JCTnull, JCTpointer _
    | JCTpointer _, JCTnull -> true
    | _ -> false


let rec list_assoc_name f id l =
  match l with
    | [] -> raise Not_found
    | fi::r -> 
	if (f fi) = id then fi
	else list_assoc_name f id r


let rec find_field_struct loc st allow_mutable = function
  | ("mutable" | "committed") as x ->
      if allow_mutable && !Jc_common_options.inv_sem = InvOwnership then
	let table =
	  if x = "mutable" then mutable_fields_table
	  else committed_fields_table
	in
	Hashtbl.find table (root_name st)
      else typing_error loc "field %s cannot be used here" x
  | f ->
      try
	list_assoc_name
	  (fun f -> f.jc_field_info_name) f st.jc_struct_info_fields
      with Not_found ->
	match st.jc_struct_info_parent with
	  | None -> 
	      typing_error loc "no field %s in structure %s" 
		f st.jc_struct_info_name
	  | Some st -> find_field_struct loc st allow_mutable f

  
let find_field loc ty f allow_mutable =
  match ty with
    | JCTpointer(JCtag st, _, _) -> find_field_struct loc st allow_mutable f
    | JCTpointer(JCvariant _, _, _)
    | JCTnative _ 
    | JCTenum _
    | JCTlogic _
    | JCTnull ->
	typing_error loc "not a structure type"

let find_fun_info id = Hashtbl.find functions_env id

let find_logic_info id = Hashtbl.find logic_functions_env id

(* types *)

let type_type t =
  match t.jc_ptype_node with
    | JCPTnative n -> JCTnative n
    | JCPTpointer (id, a, b) -> 
	(* first we try the most precise type (the tag) *)
	begin try
	  let st, _ = Hashtbl.find structs_table id in
	  JCTpointer(JCtag st, a, b)
	with Not_found ->
	  try
	    let vi = Hashtbl.find variants_table id in
	    JCTpointer(JCvariant vi, a, b)
	  with Not_found ->
	    typing_error t.jc_ptype_loc "unknown type or tag: %s" id
	end
    | JCPTidentifier id -> 
	try
	  let _ = Hashtbl.find logic_type_table id in
	  JCTlogic id
	with Not_found ->
	  try
	    let (ri (* ,_,_,_ *)) = Hashtbl.find enum_types_table id in
	    JCTenum ri
	  with Not_found ->
	    typing_error t.jc_ptype_loc "unknown type %s" id

let unary_op t op =
  match t,op with
    | _, UPpostfix_inc -> assert false
    | _, UPpostfix_dec -> assert false
    | _, UPprefix_inc -> assert false
    | _, UPprefix_dec -> assert false
    | Tinteger, UPplus -> Uplus_int
    | Tinteger, UPminus -> Uminus_int
    | Treal, UPplus -> Uplus_real
    | Treal, UPminus -> Uminus_real
    | Tinteger, UPbw_not -> Ubw_not
    | _, UPbw_not -> assert false
    | Tboolean, UPnot -> Unot
    | _, UPnot -> assert false
    | Tunit,_ -> assert false
    | Tboolean,_ -> assert false


let bin_op t op =
  match t,op with

    | Tinteger, BPgt -> Bgt_int 
    | Tinteger, BPlt -> Blt_int
    | Tinteger, BPge -> Bge_int
    | Tinteger, BPle -> Ble_int
    | Tinteger, BPeq -> Beq_int
    | Tinteger, BPneq -> Bneq_int

    | Treal, BPgt -> Bgt_real
    | Treal, BPlt -> Blt_real
    | Treal, BPge -> Bge_real
    | Treal, BPle -> Ble_real
    | Treal, BPeq -> Beq_real
    | Treal, BPneq -> Bneq_real

    | Tboolean, BPeq -> Beq_bool
    | Tboolean, BPneq -> Bneq_bool

    (* use native type TUnit in place of inexistant native pointer type *)
    | Tunit, BPeq -> Beq_pointer
    | Tunit, BPneq -> Bneq_pointer

    | Tinteger, BPadd -> Badd_int
    | Treal, BPadd -> Badd_real
    | Tinteger, BPmul -> Bmul_int
    | Treal, BPmul -> Bmul_real
    | Tinteger, BPsub -> Bsub_int
    | Treal, BPsub -> Bsub_real
    | Tinteger, BPdiv -> Bdiv_int
    | Treal, BPdiv -> Bdiv_real
    | Tinteger, BPmod -> Bmod_int
    | Tboolean, BPland -> Bland 
    | Tboolean, BPlor -> Blor

    | _, BPbw_and -> Bbw_and
    | _, BPbw_or -> Bbw_or
    | _, BPbw_xor -> Bbw_xor
    | _, BPlogical_shift_right -> Blogical_shift_right
    | _, BParith_shift_right -> Barith_shift_right
    | _, BPshift_left -> Bshift_left

    | _, BPland -> assert false
    | _, BPlor -> assert false
    | Treal, BPmod -> assert false
	(* not allowed as expression op *)
    | _,BPiff -> assert false
    | _,BPimplies -> assert false
    | Tunit,_ -> assert false
    | Tboolean, _ -> assert false


let incr_op op =
  match op with
    | UPpostfix_inc -> Postfix_inc
    | UPpostfix_dec -> Postfix_dec
    | UPprefix_inc -> Prefix_inc
    | UPprefix_dec -> Prefix_dec
    | _ -> assert false

(******************************************************************************)
(*                                  patterns                                  *)
(******************************************************************************)

let valid_pointer_type st =
  JCTpointer(st, Some (Num.num_of_int 0), Some (Num.num_of_int 0))

(* ety = expected type *)
(* env: the variables already bound *)
(* vars: the var_info to use if encountering a given variable *)
(* Return: (env, pat) where:
     env is the new environment (i.e. the union of the old env and of vars)
     pat is the typed pattern. *)
let rec pattern env vars pat ety =
  let get_var ety id =
    let id = id.jc_identifier_name in
    if List.mem_assoc id env then
      typing_error pat.jc_ppattern_loc
	"the variable %s appears twice in the pattern" id;
    try
      StringMap.find id vars
    with Not_found ->
      let vi = var ety id in
      vi.jc_var_info_assigned <- true;
      vi
  in
  let tpn, ty, newenv = match pat.jc_ppattern_node with
    | JCPPstruct(id, lpl) ->
	let tov = match ety with
	  | JCTpointer(tov, _, _) -> tov
	  | JCTnative _ | JCTenum _ | JCTlogic _ | JCTnull ->
	      typing_error pat.jc_ppattern_loc
		"this pattern doesn't match a structure nor a variant"
	in
	(* tag *)
	let st = find_struct_info id.jc_identifier_loc id.jc_identifier_name in
	if not (substruct st tov) then
	  typing_error id.jc_identifier_loc
	    "tag %s is not a subtag of %s"
	    st.jc_struct_info_name (tag_or_variant_name tov);
	(* fields *)
	let env, tlpl = List.fold_left
	  (fun (env, acc) (l, p) ->
	     let fi = find_field_struct l.jc_identifier_loc st false
	       l.jc_identifier_name
	     in
	     let env, tp = pattern env vars p fi.jc_field_info_type in
	     env, (fi, tp)::acc)
	  (env, []) lpl
	in
	JCPstruct(st, List.rev tlpl), valid_pointer_type (JCtag st), env
    | JCPPvar id ->
	let vi = get_var ety id in
	JCPvar vi, ety, (id.jc_identifier_name, vi)::env
    | JCPPor(p1, p2) ->
	let _, tp1 = pattern env vars p1 ety in
	let vars = pattern_vars vars tp1 in
	let env, tp2 = pattern env vars p2 ety in
	JCPor(tp1, tp2), ety, env
    | JCPPas(p, id) ->
	let env, tp = pattern env vars p ety in
	let vi = get_var tp.jc_pattern_type id in
	JCPas(tp, vi), ety, (id.jc_identifier_name, vi)::env
    | JCPPany ->
	JCPany, ety, env
    | JCPPconst c ->
	let ty, _, c = const c in
	if not (subtype_strict ty ety) then
	  typing_error pat.jc_ppattern_loc
	    "type %a is not a subtype of %a" print_type ty print_type ety;
	JCPconst c, ety, env
  in newenv, {
    jc_pattern_node = tpn;
    jc_pattern_loc = pat.jc_ppattern_loc;
    jc_pattern_type = ty;
  }
let pattern = pattern [] StringMap.empty

(******************************************************************************)
(*                                   terms                                    *)
(******************************************************************************)

let num_op op =
  match op with
    | BPadd -> Badd_int
    | BPsub -> Bsub_int
    | BPmul -> Bmul_int
    | BPdiv -> Bdiv_int
    | BPmod -> Bmod_int
    | _ -> assert false

let num_un_op t op e =
  match op with
    | UPminus
    | UPbw_not -> JCTunary(unary_op t op,e)
    | UPplus -> e.jc_term_node
    | _ -> assert false


let make_logic_unary_op loc (op : Jc_ast.punary_op) e =
  let t = e.jc_term_type in
  match op with
    | UPnot -> assert false
    | UPminus | UPplus | UPbw_not -> 
	let t =
	  match t with
	    | JCTnative t ->
		begin
		  match t with
		    | Tinteger -> Tinteger
		    | _ -> assert false (* TODO *)
		end
	    | _ ->
		typing_error loc "numeric type expected for unary + and -"
	in JCTnative t,dummy_region,num_un_op t op e
    | UPpostfix_dec | UPpostfix_inc | UPprefix_dec | UPprefix_inc ->
	typing_error loc "pre/post incr/decr not allowed as logical term"

let term_coerce t1 t2 e =
  let tn1,e_int =
    match t1 with
      | JCTenum ri ->
(*
	  let (_,to_int,_,_) = 
	    Hashtbl.find enum_types_table ri.jc_enum_info_name 
	  in
	  { jc_term_node = JCTapp(to_int,[e]) ;
	    jc_term_type = integer_type;
	    jc_term_loc = e.jc_term_loc }  
*)
	  Tinteger, e
      | JCTnative t -> t, e
      | _ -> assert false
  in
  match tn1,t2 with
    | Tinteger, Treal -> 
	let app = {
	  jc_app_fun = real_of_integer;
	  jc_app_args = [e_int];
	  jc_app_region_assoc = [];
	  jc_app_label_assoc = [];
	} in
	{ jc_term_node = JCTapp app;
	  jc_term_type = real_type;
	  jc_term_region = e.jc_term_region;
	  jc_term_loc = e.jc_term_loc;
	  jc_term_label = e.jc_term_label;
	}  
    | _ -> e_int

let logic_bin_op t op =
  bin_op t op
(*
  match t,op with
    | _, BPgt -> gt_int
    | _, BPlt -> lt_int
    | _, BPge -> ge_int
    | _, BPle -> le_int
    | _, BPeq -> eq
    | _, BPneq -> neq
    | Tinteger, BPadd -> add_int
    | Treal, BPadd -> add_real
    | _, BPsub -> sub_int
    | _, BPmul -> mul_int
    | _, BPdiv -> div_int
    | _, BPmod -> mod_int
    | Tboolean, BPland -> band 
    | Tboolean, BPlor -> bor
	(* not allowed as expression op *)
    | _,BPimplies -> assert false
    | Tunit,_ -> assert false
    | _ -> assert false
*)

let make_logic_bin_op loc op e1 e2 =
  let t1 = e1.jc_term_type and t2 = e2.jc_term_type in
  match op with
    | BPgt | BPlt | BPge | BPle ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  boolean_type,dummy_region,
	  JCTbinary(term_coerce t1 t e1, logic_bin_op t op, 
		     term_coerce t2 t e2)
	else
	  typing_error loc "numeric types expected for >, <, >= and <="
    | BPeq | BPneq ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  boolean_type,dummy_region,
	  JCTbinary(term_coerce t1 t e1, logic_bin_op t op,
		     term_coerce t2 t e2)
	else
	if is_pointer_type t1 && is_pointer_type t2 && (comparable_types t1 t2) then
	  boolean_type,dummy_region,
	  JCTbinary(e1, logic_bin_op Tunit op, e2)
	else
	  typing_error loc "numeric or pointer types expected for == and !="
    | BPadd ->
	if is_pointer_type t1 && is_integer t2 then
	  t1,e1.jc_term_region,JCTshift(e1, term_coerce t2 Tinteger e2)
	else if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  JCTnative t,dummy_region, JCTbinary(term_coerce t1 t e1, logic_bin_op t op,
	                         term_coerce t2 t e2)
	else
	  typing_error loc "unexpected types for +"
    | BPsub ->
	if is_pointer_type t1 && is_integer t2 then
	  let e2 = { e2 with 
	    jc_term_node = let _,_,te = make_logic_unary_op loc UPminus e2 in te;
	  } in
	  t1,e1.jc_term_region,JCTshift(e1, term_coerce t2 Tinteger e2)
	else if 
	  is_pointer_type t1 && is_pointer_type t2 
	  && comparable_types t1 t2 
	then
	  integer_type,dummy_region, JCTsub_pointer(e1, e2)
	else if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  JCTnative t,dummy_region, JCTbinary(term_coerce t1 t e1, logic_bin_op t op, 
	                         term_coerce t2 t e2)
	else
	  typing_error loc "unexpected types for -"
    | BPmul | BPdiv | BPmod | BPbw_and | BPbw_or | BPbw_xor 
    | BPlogical_shift_right | BParith_shift_right | BPshift_left ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  (JCTnative t,dummy_region,
	   JCTbinary(term_coerce t1 t e1, logic_bin_op t op,
		      term_coerce t2 t e2))
	else typing_error loc "numeric types expected for *, / and %%"
    | BPland | BPlor -> 
	let t=
	  match (t1,t2) with
	    | JCTnative t1, JCTnative t2 ->
		begin
		  match (t1,t2) with
		    | Tboolean,Tboolean -> Tboolean
		    | _ -> assert false (* TODO *)
		end
	    | _ ->
		typing_error loc "booleans expected"
	in JCTnative t,dummy_region,JCTbinary(e1, logic_bin_op t op, e2)

	(* not allowed as term op *)
    | BPimplies | BPiff -> assert false

	  
let rec term label_env logic_label env e =
  let ft = term label_env logic_label env in
  let lab = ref "" in
  let t,tr,te =
    match e.jc_pexpr_node with
      | JCPElabel(l,e) ->
	  let tt = ft e in
	  lab := l; 
	  tt.jc_term_type,tt.jc_term_region,tt.jc_term_node
      | JCPEvar id ->
	  begin
	    try
	      let vi = List.assoc id env
	      in vi.jc_var_info_type,vi.jc_var_info_region,JCTvar vi
	    with Not_found -> 
	      try 
		let vi = Hashtbl.find variables_env id 
		in vi.jc_var_info_type,vi.jc_var_info_region,JCTvar vi
	      with Not_found -> 
		try 
		  let vi = Hashtbl.find logic_constants_env id 
		  in vi.jc_var_info_type,vi.jc_var_info_region,JCTvar vi
		with Not_found -> 
		  typing_error e.jc_pexpr_loc "unbound identifier %s" id
	  end
      | JCPEinstanceof(e1,t) -> 
	  begin
	    match logic_label with
	      | None ->
		  typing_error e.jc_pexpr_loc "No memory state for this instanceof (\\at missing ?)"
	      | Some l ->
		  let te1 = ft e1 in
		  let st = find_struct_info e.jc_pexpr_loc t in
		  boolean_type,dummy_region, JCTinstanceof(te1,l,st)
	  end
      | JCPEcast(e1, t) -> 
	  let te1 = ft e1 in
	  begin
	    try
	      let ri = Hashtbl.find enum_types_table t in
	      if is_numeric te1.jc_term_type then
		JCTenum ri,dummy_region, te1.jc_term_node
	      else
		typing_error e.jc_pexpr_loc "numeric type expected"
	    with Not_found ->
	      match logic_label with
		| None ->
		    typing_error e.jc_pexpr_loc "No memory state for this cast (\\at missing ?)"
		| Some l ->
		    let st = find_struct_info e.jc_pexpr_loc t in
		    match te1.jc_term_type with
		      | JCTpointer(st1,a,b) ->
			  if substruct st st1 then
			    (JCTpointer(JCtag st,a,b),
			     te1.jc_term_region, JCTcast(te1,l,st))
			  else
			    typing_error e.jc_pexpr_loc "invalid cast"
		      | _ ->
			  typing_error e.jc_pexpr_loc "only structures can be cast"
	  end
      | JCPEbinary (e1, op, e2) -> 
	  let e1 = ft e1 and e2 = ft e2 in
	  make_logic_bin_op e.jc_pexpr_loc op e1 e2 
      | JCPEunary(op, e2) -> 
	  let te2 = ft e2
	  in
	  make_logic_unary_op e.jc_pexpr_loc op te2
      | JCPEapp (id, labs, args) ->
	  List.iter
	    (fun l -> if List.mem l label_env then () else
	       typing_error e.jc_pexpr_loc "label `%a' not found" Jc_output.label l)
	    labs;
(*
	  begin
	    match e1.jc_pexpr_node with
	      | JCPEvar id ->
*)
		  if List.length args = 0 then
		    let vi = Hashtbl.find logic_constants_env id in
		    vi.jc_var_info_type,vi.jc_var_info_region,JCTvar vi
		  else begin
		    try
		      let pi = find_logic_info id in
		      let tl =
			try
			  List.map2
			    (fun vi e ->
			       let ty = vi.jc_var_info_type in
			       let te = ft e in
			       if subtype_strict te.jc_term_type ty then te
			       else
				 typing_error e.jc_pexpr_loc 
				   "type %a expected instead of %a" 
				   print_type ty print_type te.jc_term_type) 
			    pi.jc_logic_info_parameters args
			with  Invalid_argument _ ->
			  typing_error e.jc_pexpr_loc 
			    "wrong number of arguments for %s" id
		      in
		      let ty = match pi.jc_logic_info_result_type with
			| None -> assert false | Some ty -> ty
		      in
		      let label_assoc = 
			match logic_label, pi.jc_logic_info_labels, labs with
			  | Some l, [lf], [] -> [lf,l]
			  | _ ->
			      try
				List.map2
				  (fun l1 l2 -> (l1,l2))
				  pi.jc_logic_info_labels labs
			      with Invalid_argument _ ->
				typing_error e.jc_pexpr_loc 
				  "wrong number of labels for %s" id
		      in
		      let app = {
			jc_app_fun = pi;
			jc_app_args = tl;
			jc_app_region_assoc = [];
			jc_app_label_assoc = label_assoc;
		      } in
		      ty,Region.make_var ty pi.jc_logic_info_name,JCTapp app
		    with Not_found ->
		      typing_error e.jc_pexpr_loc 
			"unbound logic function identifier %s" id
		  end
(*
	      | _ -> 
		  typing_error e.jc_pexpr_loc "unsupported logic function application"
	  end
*)
      | JCPEderef (e1, f) -> 
	  let te = ft e1 in
	  let fi = find_field e.jc_pexpr_loc te.jc_term_type f true in
	  begin
	    match logic_label with
	      | None ->
		  typing_error e.jc_pexpr_loc "No memory state for this dereferenciation (\\at missing ?)"
	      | Some l ->
		  fi.jc_field_info_type, 
		  Region.make_field te.jc_term_region fi,
		  JCTderef(te,l,fi)	  
	  end
      | JCPEconst c -> 
	  let t,tr,c = const c in t,tr,JCTconst c
      | JCPEold e -> 
	  if List.mem LabelOld label_env then
	    let te = term label_env (Some LabelOld) env e in 
	    te.jc_term_type,te.jc_term_region,JCTold(te)
	  else
	    typing_error e.jc_pexpr_loc "\\old not defined in this context"
      | JCPEat(e,lab) -> 
	  if List.mem lab label_env then
	    let te = term label_env (Some lab) env e in 
	    te.jc_term_type,te.jc_term_region,JCTat(te,lab)
	  else
	    typing_error e.jc_pexpr_loc "label `%a' not found" Jc_output.label lab
      | JCPEoffset(k,e) -> 
	  let te = ft e in 
	  begin
	    match te.jc_term_type with 
	      | JCTpointer(JCtag st, _, _) ->
		  integer_type, dummy_region, JCToffset(k, te, st)
	      | JCTpointer(JCvariant vi, _, _) ->
		  assert false (* TODO *)
	      | _ ->
		  typing_error e.jc_pexpr_loc "pointer expected"
	  end
      | JCPEif(e1,e2,e3) ->
	  let te1 = ft e1 and te2 = ft e2 and te3 = ft e3 in
	  begin
	    match te1.jc_term_type with
	      | JCTnative Tboolean ->
		  let t =
		    let t2 = te2.jc_term_type and t3 = te3.jc_term_type in
		    if subtype_strict t2 t3 then t3 else
		      if subtype_strict t3 t2 then t2 else
			typing_error e.jc_pexpr_loc 
			  "incompatible result types"
		  in
		  t,te1.jc_term_region, JCTif(te1,te2,te3)
	      | _ ->
		  typing_error e1.jc_pexpr_loc 
		    "boolean expression expected"
	  end
      | JCPElet(id,e1,e2) ->
	  let te1 = ft e1 in
	  let vi = var te1.jc_term_type id in
	  let te2 = term label_env logic_label ((id,vi)::env) e2 in
	  te2.jc_term_type,te2.jc_term_region, te2.jc_term_node
	  (* non-pure expressions *)
      | JCPEassign_op _ 
      | JCPEassign _ -> 
	  typing_error e.jc_pexpr_loc 
	    "assignment not allowed as logic term"
	    (* propositional (non-boolean) expressions *)
      | JCPEquantifier _ -> 
	  typing_error e.jc_pexpr_loc 
	    "quantification not allowed as logic term"
      | JCPEalloc _ | JCPEfree _ ->
	  typing_error e.jc_pexpr_loc 
	    "memory (de-)allocation not allowed as logic term"
      | JCPErange(Some e1,Some e2) ->
	  let e1 = ft e1 and e2 = ft e2 in
	  let t1 = e1.jc_term_type and t2 = e2.jc_term_type in
	  assert (is_numeric t1 && is_numeric t2);
	  let t = lub_numeric_types t1 t2 in
	  JCTnative t, dummy_region, 
	  JCTrange(Some (term_coerce t1 t e1),Some (term_coerce t2 t e2))
      | JCPErange(Some e,None) ->
	  let e = ft e in
	  let t = e.jc_term_type in
	  assert (is_numeric t);
	  t, dummy_region,JCTrange(Some e,None)
      | JCPErange(None,Some e) ->
	  let e = ft e in
	  let t = e.jc_term_type in
	  assert (is_numeric t);
	  t,dummy_region, JCTrange(None,Some e)
      | JCPErange(None,None) ->
	  integer_type, dummy_region,JCTrange(None,None)
      | JCPEmutable(e, t) ->
	  assert false (* TODO *)
      | JCPEtagequality _ ->
	  assert false (* TODO *)
      | JCPEmatch(arg, pel) ->
	  let targ = ft arg in
	  let rty, tpel = match pel with
	    | [] -> assert false (* should not be allowed by the parser *)
	    | (p1, e1)::rem ->
		(* type the first item *)
		let penv, tp1 = pattern p1 targ.jc_term_type in
		let newenv = penv @ env in
		let te1 = term label_env logic_label newenv e1 in
		(* type the remaining items *)
		List.fold_left
		  (fun (accrty, acctpel) (p, e2) ->
		     let penv, tp = pattern p targ.jc_term_type in
		     let newenv = penv @ env in
		     let te2 = term label_env logic_label newenv e2 in
		     maxtype e.jc_pexpr_loc accrty te2.jc_term_type,
		     (tp, te2)::acctpel)
		  (te1.jc_term_type, [tp1, te1])
		  rem
	  in
	  rty, targ.jc_term_region, JCTmatch(targ, List.rev tpel)
	    
  in { jc_term_node = te;
       jc_term_type = t;
       jc_term_region = tr;
       jc_term_loc = e.jc_pexpr_loc;
       jc_term_label = !lab;
     }

  
let rel_unary_op loc op t =
  match op with
    | UPnot | UPbw_not -> assert false
    | UPminus | UPplus -> 
	typing_error loc "not a proposition"
    | UPpostfix_dec | UPpostfix_inc | UPprefix_dec | UPprefix_inc ->
	typing_error loc "pre/post incr/decr not allowed as logical term"


let rel_bin_op t op =
  bin_op t op
(*
  match t,op with
    | Tinteger,BPgt -> gt_int
    | Tinteger,BPlt -> lt_int
    | Tinteger,BPge -> ge_int
    | Tinteger,BPle -> le_int
    | _,BPeq -> eq
    | _,BPneq -> neq
    | _,(BPadd | BPsub | BPmul | BPdiv | BPmod) -> assert false
    | _,(BPland | BPlor | BPimplies | BPiff) -> assert false
    | _ -> assert false  (* TODO *)
*)


let make_and a1 a2 =
  match (a1.jc_assertion_node,a2.jc_assertion_node) with
    | (JCAtrue,_) -> a2
    | (_,JCAtrue) -> a1
(*
    | (LFalse,_) -> LFalse
    | (_,LFalse) -> LFalse
*)
    | (JCAand l1 , JCAand l2) -> raw_asrt(JCAand(l1@l2))
    | (JCAand l1 , _ ) -> raw_asrt(JCAand(l1@[a2]))
    | (_ , JCAand l2) -> raw_asrt(JCAand(a1::l2))
    | _ -> raw_asrt(JCAand [a1;a2])

let make_or a1 a2 =
  match (a1.jc_assertion_node,a2.jc_assertion_node) with
    | (JCAfalse,_) -> a2
    | (_,JCAfalse) -> a1
(*
    | (LFalse,_) -> LFalse
    | (_,LFalse) -> LFalse
*)
    | (JCAor l1 , JCAor l2) -> raw_asrt(JCAor(l1@l2))
    | (JCAor l1 , _ ) -> raw_asrt(JCAor(l1@[a2]))
    | (_ , JCAor l2) -> raw_asrt(JCAor(a1::l2))
    | _ -> raw_asrt(JCAor [a1;a2])


let make_rel_bin_op loc op e1 e2 =
  let t1 = e1.jc_term_type and t2 = e2.jc_term_type in
  match op with
    | BPgt | BPlt | BPge | BPle ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  JCArelation(term_coerce t1 t e1, rel_bin_op t op, term_coerce t2 t e2)
	else
	  typing_error loc "numeric types expected for >, <, >= and <="
    | BPeq | BPneq ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  JCArelation(term_coerce t1 t e1, rel_bin_op t op,
		     term_coerce t2 t e2)
	else
	  if comparable_types t1 t2 then 
	    JCArelation(e1, rel_bin_op Tunit op, e2)
	  else
	    typing_error loc "terms should have the same type for == and !="
	(* non propositional operators *)
    | BPadd | BPsub | BPmul | BPdiv | BPmod | BPbw_and | BPbw_or | BPbw_xor
    | BPlogical_shift_right | BParith_shift_right | BPshift_left 
	-> assert false
	(* already recognized as connectives *)
    | BPland | BPlor -> assert false 
    | BPimplies -> assert false
    | BPiff -> assert false

let tag label_env logic_label env hierarchy t =
  let check_hierarchy loc st =
    if hierarchy <> "" &&
      root_name st != hierarchy then
	typing_error loc
	  "this is in the hierarchy of %s, while it should be in the hierarchy \
of %s"
	  (root_name st) hierarchy
  in
  let tt = match t.jc_ptag_node with
    | JCPTtag id ->
	let st = find_struct_info id.jc_identifier_loc id.jc_identifier_name in
	check_hierarchy id.jc_identifier_loc st;
	JCTtag st
    | JCPTbottom -> JCTbottom
    | JCPTtypeof tof ->
	let ttof = term label_env logic_label env tof in
	match ttof.jc_term_type with
	  | JCTpointer(JCtag st, _, _) ->
	      check_hierarchy tof.jc_pexpr_loc st;
	      JCTtypeof (ttof, st)
	  | _ -> typing_error tof.jc_pexpr_loc "tag pointer expression expected"
  in {
    jc_tag_node = tt;
    jc_tag_loc = t.jc_ptag_loc
  }

let rec assertion label_env logic_label env e =
  let fa = assertion label_env logic_label env in
  let ft = term label_env logic_label env in
  let lab = ref "" in
  let te =
    match e.jc_pexpr_node with
      | JCPElabel(l,e) ->
	  let te = fa e in
	  lab := l; 
	  te.jc_assertion_node
      | JCPEvar id -> 
	  let vi = 
	    try List.assoc id env 
	    with Not_found -> 
	      try Hashtbl.find variables_env id
	      with Not_found -> 
		typing_error e.jc_pexpr_loc "unbound identifier %s" id
	  in 
	  begin
	    match vi.jc_var_info_type with
	      | JCTnative Tboolean ->
		  JCAbool_term { jc_term_loc = e.jc_pexpr_loc;
				 jc_term_label = "";
				  jc_term_type = vi.jc_var_info_type;
				  jc_term_region = vi.jc_var_info_region;
				  jc_term_node = JCTvar vi }
	      | _ ->
		  typing_error e.jc_pexpr_loc "non boolean expression"
	  end
      | JCPEinstanceof(e1, t) -> 
	  begin
	    match logic_label with
	      | None ->
		  typing_error e.jc_pexpr_loc "No memory state for this instanceof (\\at missing ?)"
	      | Some l ->
		  let te1 = ft e1 in
		  let st = find_struct_info e.jc_pexpr_loc t in
		  JCAinstanceof(te1,l,st) 
	  end
      | JCPEcast(e, t) -> assert false
      | JCPEbinary (e1, BPland, e2) -> 
	  let a1 = fa e1 and a2 = fa e2 in
	  (make_and a1 a2).jc_assertion_node
      | JCPEbinary (e1, BPlor, e2) -> 
	  (make_or (fa e1) (fa e2)).jc_assertion_node
      | JCPEbinary (e1, BPimplies, e2) -> 
	  let a1 = fa e1 and a2 = fa e2 in
	  JCAimplies(a1,a2)
      | JCPEbinary (e1, BPiff, e2) -> 
	  JCAiff(fa e1,fa e2)
      | JCPEunary (UPnot, e2) -> 
	  JCAnot(fa e2)
      | JCPEbinary (e1, op, e2) -> 
	  let e1 = ft e1 and e2 = ft e2 in
	  make_rel_bin_op e.jc_pexpr_loc op e1 e2
      | JCPEunary(op, e2) -> 
	  assert false
(*
	  let e2 = term env e2 in
	  JCAapp { jc_app_fun = rel_unary_op e.jc_pexpr_loc op e2.jc_term_type;
		   jc_app_args = [e2])
*)
      | JCPEapp (id, labs, args) ->
	  List.iter
	    (fun l -> if List.mem l label_env then () else
	       typing_error e.jc_pexpr_loc "label `%a' not found" Jc_output.label l)
	    labs;
	  (*
	    begin
	    match e1.jc_pexpr_node with
	    | JCPEvar id ->
	  *)
	  begin
	    try
	      let pi = find_logic_info id in
	      let tl =
		try
		  List.map2
		    (fun vi e ->
		       let ty = vi.jc_var_info_type in
		       let te = ft e in
			 if subtype_strict te.jc_term_type ty then te
			 else
			   typing_error e.jc_pexpr_loc 
			     "type %a expected instead of %a" 
			     print_type ty print_type te.jc_term_type) 
		    pi.jc_logic_info_parameters args
		with  Invalid_argument _ ->
		  typing_error e.jc_pexpr_loc 
		    "wrong number of arguments for %s" id
	      in
	      let label_assoc =
		match logic_label, pi.jc_logic_info_labels, labs with
		  | None, [lf], [] -> [lf,lf] (* CORRECT ? *)
		  | Some l, [lf], [] -> [lf,l]
		  | _ ->
		      try
			List.map2
			  (fun l1 l2 -> (l1,l2))
			  pi.jc_logic_info_labels labs
		      with Invalid_argument _ ->
			typing_error e.jc_pexpr_loc 
			  "wrong number of labels for %s" id
	      in
	      let app = {
		jc_app_fun = pi;
			jc_app_args = tl;
			jc_app_region_assoc = [];
			jc_app_label_assoc = label_assoc;
		      } in
		      JCAapp app
		    with Not_found ->
		      typing_error e.jc_pexpr_loc 
			"unbound predicate identifier %s" id
		  end
(*
	      | _ -> 
		  typing_error e.jc_pexpr_loc "unsupported predicate application"
	  end
*)
      | JCPEderef (e, id) -> 
	  begin
	    match logic_label with
	      | None ->
		  typing_error e.jc_pexpr_loc "No memory state for this \
dereferenciation (\\at missing ?)"
	      | Some l ->
		  let te = ft e in
		  let fi = find_field e.jc_pexpr_loc te.jc_term_type id true in
		  match fi.jc_field_info_type with
		    | JCTnative Tboolean ->
			JCAbool_term { jc_term_loc = e.jc_pexpr_loc;
				       jc_term_label = "";
				       jc_term_type = fi.jc_field_info_type;
				       jc_term_region = 
		            Region.make_field te.jc_term_region fi;
				       jc_term_node = JCTderef(te,l,fi) }
		    | _ ->
			typing_error e.jc_pexpr_loc "non boolean expression"
	  end
(*
      | JCPEshift (_, _) -> assert false
*)
      | JCPEconst c -> 
	  begin
	    match c with
	      | JCCboolean true -> JCAtrue
	      | JCCboolean false -> JCAfalse
	      | _ ->
		  typing_error e.jc_pexpr_loc "non propositional constant"
	  end
      | JCPEquantifier(q,ty,idl,e1) -> 
	  let ty = type_type ty in
	  (make_quantifier q e.jc_pexpr_loc ty idl label_env logic_label env e1).jc_assertion_node
      | JCPEold e -> 
	  if List.mem LabelOld label_env then
	    JCAold(assertion label_env (Some LabelOld) env e)
	  else
	    typing_error e.jc_pexpr_loc "\\old not defined in this context"
      | JCPEat(e,lab) -> 
	  if List.mem lab label_env then
	    JCAat(assertion label_env (Some lab) env e,lab)
	  else
	    typing_error e.jc_pexpr_loc "label `%a' not found" Jc_output.label lab
      | JCPEif(e1,e2,e3) ->
	  let te1 = ft e1 and te2 = fa e2 and te3 = fa e3 in
	  begin
	    match te1.jc_term_type with
	      | JCTnative Tboolean ->
		  JCAif(te1,te2,te3)
	      | _ ->
		  typing_error e1.jc_pexpr_loc 
		    "boolean expression expected"
	  end
      | JCPElet _ -> assert false
	  (* non propositional expressions *)
      | JCPEoffset _ | JCPErange _ ->
	  typing_error e.jc_pexpr_loc "offsets and range are not propositions"
	  (* non-pure expressions *)
      | JCPEassign_op _ 
      | JCPEassign _ -> 
	  typing_error e.jc_pexpr_loc "assignment not allowed as logic term"
      | JCPEalloc _ | JCPEfree _ ->
	  typing_error e.jc_pexpr_loc 
	    "memory (de-)allocation not allowed as logic term"
      | JCPEmutable(e, t) ->
	  let te = ft e in
	  let te_st = match te.jc_term_type with
	    | JCTpointer(JCtag st, _, _) -> st
	    | _ -> typing_error e.jc_pexpr_loc "tag pointer expression expected"
	  in
	  let tt = tag label_env logic_label env (root_name te_st) t in
	  JCAmutable(te, te_st, tt)
      | JCPEtagequality(tag1, tag2) ->
	  let ttag1 = tag label_env logic_label env "" tag1 in
	  let ttag2 = tag label_env logic_label env "" tag2 in
	  let st = match ttag1.jc_tag_node, ttag2.jc_tag_node with
	    | JCTbottom, JCTbottom -> None
	    | JCTbottom, JCTtag st
	    | JCTtag st, JCTbottom
	    | JCTbottom, JCTtypeof(_, st)
	    | JCTtypeof(_, st), JCTbottom -> Some (root_name st)
	    | JCTtag st1, JCTtag st2
	    | JCTtypeof(_, st1), JCTtag st2
	    | JCTtag st1, JCTtypeof(_, st2)
	    | JCTtypeof(_, st1), JCTtypeof(_, st2) ->
		if st1.jc_struct_info_root != st2.jc_struct_info_root then
		  typing_error e.jc_pexpr_loc "the hierarchy %s and %s are \
different"
		    (root_name st1)
		    (root_name st2)
		else
		  Some (root_name st1)
	  in
	  JCAtagequality(
	    ttag1, ttag2, st)
      | JCPEmatch _ ->
	  let te = ft e in
	  if te.jc_term_type = JCTnative Tboolean then
	    JCAbool_term(ft e)
	  else
	    typing_error e.jc_pexpr_loc "This term should have type bool"

  in { jc_assertion_node = te;
       jc_assertion_label = !lab;
       jc_assertion_loc = e.jc_pexpr_loc }

and make_quantifier q loc ty idl label_env logic_label env e : assertion =
  match idl with
    | [] -> assertion label_env logic_label env e
    | id::r ->
	let vi = var ty id in
	let f = 
	  JCAquantifier(q,vi,make_quantifier q loc ty r label_env logic_label ((id,vi)::env) e) 
	in
	{ jc_assertion_loc = loc ; 
	  jc_assertion_label = ""; 
	  jc_assertion_node = f }

(* expressions *)

let set_assigned v =
(* Yannick: jc_options cannot be exported, and jc_typing must be
   --> to use log here, move it out of jc_options
  Jc_options.lprintf "Local var %s is assigned@." v.jc_var_info_name; 
*)
  v.jc_var_info_assigned <- true

let make_unary_op loc (op : Jc_ast.punary_op) e2 =
  let t2 = e2.jc_texpr_type in
  match op with
    | UPprefix_inc | UPpostfix_inc | UPprefix_dec | UPpostfix_dec ->
	begin
	  match e2.jc_texpr_node with
	    | JCTEvar v ->
		set_assigned v;
		t2,v.jc_var_info_region,JCTEincr_local(incr_op op,v)
	    | JCTEderef(e,f) ->
		t2,e2.jc_texpr_region,JCTEincr_heap(incr_op op, e, f)
	    | _ -> typing_error e2.jc_texpr_loc "not an lvalue"
	end
    | UPnot -> 
	let t=
	  match t2 with
	    | JCTnative t2 ->
		begin
		  match t2 with
		    | Tboolean -> Tboolean
		    | _ -> assert false (* TODO *)
		end
	    | _ ->
		typing_error loc "boolean expected"
	in JCTnative t,dummy_region,JCTEunary(unary_op t op, e2)
    | UPplus | UPminus | UPbw_not -> 
	if is_numeric t2 then
	  let t = lub_numeric_types t2 t2 in
	  JCTnative t,dummy_region,JCTEunary(unary_op t op, e2)
	else
	  typing_error loc "numeric type expected"

let coerce t1 t2 e =
  let tn1,e_int =
    match t1 with
      | JCTenum ri -> Tinteger,e 
      | JCTnative t -> t,e
      | _ -> assert false
  in
  match tn1,t2 with
    | Tinteger,Treal -> 
	{ jc_texpr_node = JCTEcall(real_of_integer_,[e_int]) ;
	  jc_texpr_type = real_type;
	  jc_texpr_region = dummy_region;
	  jc_texpr_label = "";
	  jc_texpr_loc = e.jc_texpr_loc }  
    | _ -> e_int

let make_bin_op loc op e1 e2 =
  let t1 = e1.jc_texpr_type and t2 = e2.jc_texpr_type in
  match op with
    | BPgt | BPlt | BPge | BPle ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  boolean_type,dummy_region,
	  JCTEbinary (coerce t1 t e1, bin_op t op, coerce t2 t e2)
	else
	  typing_error loc "numeric types expected for <, >, <= and >="
    | BPeq | BPneq ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	    (boolean_type,dummy_region,
	     JCTEbinary(coerce t1 t e1, bin_op t op, coerce t2 t e2))
	else
	  if t1 = boolean_type && t2 = boolean_type then
	    (boolean_type,dummy_region,JCTEbinary (e1, bin_op Tboolean op, e2))
	  else
	    if is_pointer_type t1 && is_pointer_type t2 && comparable_types t1 t2 then
	      (boolean_type,dummy_region,
	       JCTEbinary(e1, 
			  (if op = BPeq then Beq_pointer else Bneq_pointer), e2))
	    else
	      typing_error loc "numeric, boolean or pointer types expected for == and !="
    | BPadd ->
	if is_pointer_type t1 && is_integer t2 then
	  t1,e1.jc_texpr_region,JCTEshift(e1, coerce t2 Tinteger e2)
	else if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  JCTnative t,dummy_region,JCTEbinary(coerce t1 t e1, bin_op t op, coerce t2 t e2)
	else
	  typing_error loc "unexpected types for +"
    | BPsub ->
	if is_pointer_type t1 && is_integer t2 then
	  let e2 = { e2 with
	    jc_texpr_node = let _,_,te = make_unary_op loc UPminus e2 in te;
	  } in
	  t1,e1.jc_texpr_region,JCTEshift(e1, coerce t2 Tinteger e2)
	else if 
	  is_pointer_type t1 && is_pointer_type t2 
	  && comparable_types t1 t2 
	then
	  integer_type,dummy_region,JCTEsub_pointer(e1, e2)
	else if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  JCTnative t,dummy_region,JCTEbinary(coerce t1 t e1, bin_op t op, coerce t2 t e2)
	else
	  typing_error loc "unexpected types for -"
    | BPmul | BPdiv | BPmod | BPbw_and | BPbw_or | BPbw_xor 
    | BPlogical_shift_right | BParith_shift_right | BPshift_left ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  JCTnative t,dummy_region,
	  JCTEbinary(coerce t1 t e1, bin_op t op, coerce t2 t e2)
	else
	  typing_error loc "numeric types expected for bitwaise operators"
    | BPland | BPlor -> 
	let t=
	  match (t1,t2) with
	    | JCTnative t1, JCTnative t2 ->
		begin
		  match (t1,t2) with
		    | Tboolean,Tboolean -> Tboolean
		    | _ -> assert false (* TODO *)
		end
	    | _ ->
		typing_error loc "booleans expected"
	in JCTnative t,dummy_region,JCTEbinary(e1, bin_op t op, e2)

	(* not allowed as expression op *)
    | BPimplies | BPiff -> assert false



let rec expr env e =
  let lab = ref "" in
  let t,tr,te =
    match e.jc_pexpr_node with
      | JCPElabel(l,e) ->
	  let te = expr env e in
	  lab := l; 
	  te.jc_texpr_type,te.jc_texpr_region,te.jc_texpr_node
      | JCPEvar id ->
	  begin
	    try
	      let vi = List.assoc id env
	      in vi.jc_var_info_type,vi.jc_var_info_region,JCTEvar vi
	    with Not_found -> 
	      try 
		let vi = Hashtbl.find variables_env id
		in vi.jc_var_info_type,vi.jc_var_info_region,JCTEvar vi
	      with Not_found -> 
		try 
		  let vi = Hashtbl.find logic_constants_env id 
		  in vi.jc_var_info_type,vi.jc_var_info_region,JCTEvar vi
		with Not_found -> 
		  typing_error e.jc_pexpr_loc "unbound identifier %s" id
	  end
      | JCPEinstanceof(e1, t) -> 
	  let te1 = expr env e1 in
	  let st = find_struct_info e.jc_pexpr_loc t in
	  boolean_type,dummy_region, JCTEinstanceof(te1,st)
      | JCPEcast(e1, t) -> 
	  let te1 = expr env e1 in
	  begin
	    try
	      let ri = Hashtbl.find enum_types_table t in
	      if is_numeric te1.jc_texpr_type then
		JCTenum ri,te1.jc_texpr_region, JCTErange_cast(ri,te1)
	      else
		typing_error e.jc_pexpr_loc "numeric type expected"
	    with Not_found ->
	      let st = find_struct_info e.jc_pexpr_loc t in
	      match te1.jc_texpr_type with
		| JCTpointer(st1,a,b) ->
		    if substruct st st1 then
		      (JCTpointer(JCtag st,a,b),
		       te1.jc_texpr_region, JCTEcast(te1,st))
		    else
		      typing_error e.jc_pexpr_loc "invalid cast"
		| _ ->
		    typing_error e.jc_pexpr_loc "only structures can be cast"
	  end
      | JCPEalloc (e1, t) ->
	  let te1 = expr env e1 in
	  let st = find_struct_info e.jc_pexpr_loc t in
	  let ty = JCTpointer (JCtag st,Some zero,None) in
	  ty,Region.make_var ty "alloc", JCTEalloc (te1, st)
      | JCPEfree e1 ->
	  let e1 = expr env e1 in
	  unit_type,dummy_region, JCTEfree e1
      | JCPEbinary (e1, op, e2) -> 
	  let e1 = expr env e1 and e2 = expr env e2 in
	  make_bin_op e.jc_pexpr_loc op e1 e2
      | JCPEunary (op, e2) -> 
	  let e2 = expr env e2 in
	  make_unary_op e.jc_pexpr_loc op e2
      | JCPEassign (e1, e2) -> 
	  begin
	    let te1 = expr env e1 and te2 = expr env e2 in
            let t1 = te1.jc_texpr_type and t2 = te2.jc_texpr_type in
	    if subtype t2 t1 then 
	      match te1.jc_texpr_node with
		| JCTEvar v ->
		    set_assigned v;
		    t1,te2.jc_texpr_region,JCTEassign_var(v,te2)
		| JCTEderef(e,f) ->
		    t1,te2.jc_texpr_region,JCTEassign_heap(e, f, te2)
		| _ -> typing_error e1.jc_pexpr_loc "not an lvalue"
	    else
	      typing_error e2.jc_pexpr_loc 
		"type '%a' expected in assignment instead of '%a'"
		print_type t1 print_type t2
	  end
      | JCPEassign_op (e1, op, e2) -> 
	  begin
	    let te1 = expr env e1 and te2 = expr env e2 in
            let t1 = te1.jc_texpr_type in 
	    match te1.jc_texpr_node with
	      | JCTEvar v ->
		  set_assigned v;
		  let t,tr,res = make_bin_op e.jc_pexpr_loc op te1 te2 in
		  if subtype t t1 then
		    match res with
		      | JCTEbinary(_,op,_) ->
			  t1,tr,JCTEassign_var_op(v, op, te2)
		      | _ -> assert false
		  else
		    typing_error e2.jc_pexpr_loc 
		      "type '%a' expected in op-assignment instead of '%a'"
		      print_type t1 print_type t
	      | JCTEderef(te,f) ->
		  let t,tr,res = make_bin_op e.jc_pexpr_loc op te1 te2 in
		  if subtype t t1 then
		    match res with
		      | JCTEbinary(_,op,_) ->
			  t1,tr,JCTEassign_heap_op(te, f, op, te2)
		      | _ -> assert false
		  else
		    typing_error e2.jc_pexpr_loc 
		      "type '%a' expected in op-assignment instead of '%a'"
		      print_type t1 print_type t
(*

		  let vi = newvar e.jc_texpr_type in
		  vi.jc_var_info_assigned <- true;
		  let v = { jc_texpr_loc = e.jc_texpr_loc;
			    jc_texpr_type = e.jc_texpr_type;
			    jc_texpr_node = JCTEvar vi; }
		  in			    
		  let res = JCTEderef(v,f) in
		  let res =
		    { jc_texpr_node = res;
		      jc_texpr_type = f.jc_field_info_type;
		      jc_texpr_loc = e.jc_texpr_loc;
		    } 
		  in
		  let t,res = make_bin_op e.jc_texpr_loc op res te2 in
		  let res =
		    { jc_texpr_node = res;
		      jc_texpr_type = t;
		      jc_texpr_loc = e2.jc_pexpr_loc;
		    } 
		  in
		  if subtype t t1 then 
		    let res = JCTEassign_heap(v,f,res) in
		    let res =
		      { jc_texpr_node = res;
			jc_texpr_type = t1;
			jc_texpr_loc = e2.jc_pexpr_loc;
		      } 
		    in
		    t1,JCTElet(vi,e,res)
		  else
		    typing_error e2.jc_pexpr_loc 
		      "type '%a' expected"
		      print_type t1
*)
	      | _ -> typing_error e1.jc_pexpr_loc "not an lvalue"
	  end

      | JCPEapp (id, labs, l) -> 
(*
	  begin
	    match e1.jc_pexpr_node with
	      | JCPEvar id ->
*)
	  begin
	    assert (labs = []);
		    try
		      let fi = find_fun_info id in
		      let tl =
			try
			  List.map2
			    (fun vi e ->
			       let ty = vi.jc_var_info_type in
			       let te = expr env e in
			       if subtype te.jc_texpr_type ty then te
			       else
				 typing_error e.jc_pexpr_loc 
				   "type %a expected instead of %a" 
				   print_type ty print_type te.jc_texpr_type) 
			    fi.jc_fun_info_parameters l
			with  Invalid_argument _ ->
			  typing_error e.jc_pexpr_loc 
			    "wrong number of arguments for %s" id
		      in
		      let ty = fi.jc_fun_info_result.jc_var_info_type in
		      ty,
		      Region.make_var ty fi.jc_fun_info_name,
		      JCTEcall(fi, tl)
		    with Not_found ->
		      typing_error e.jc_pexpr_loc 
			"unbound function identifier %s" id
		  end
(*
	      | _ -> 
		  typing_error e.jc_pexpr_loc "unsupported function call"
	  end
*)
      | JCPEderef (e1, f) -> 
	  let te = expr env e1 in
	  let fi = find_field e.jc_pexpr_loc te.jc_texpr_type f false in
	  fi.jc_field_info_type,
	  Region.make_field te.jc_texpr_region fi,
	  JCTEderef(te,fi)
(*
      | JCPEshift (_, _) -> assert false
*)
      | JCPEconst c -> let t,tr,tc = const c in t,tr,JCTEconst tc
      | JCPEif(e1,e2,e3) ->
	  let te1 = expr env e1 
	  and te2 = expr env e2
	  and te3 = expr env e3 
	  in
	  begin
	    match te1.jc_texpr_type with
	      | JCTnative Tboolean ->
		  let t = maxtype e.jc_pexpr_loc 
		    te2.jc_texpr_type te3.jc_texpr_type in
		  t,te1.jc_texpr_region, JCTEif(te1,te2,te3)
	      | _ ->
		  typing_error e1.jc_pexpr_loc 
		    "boolean expression expected"
	  end
      | JCPElet(id,e1,e2) ->
	  let te1 = expr env e1 in
	  let vi = var te1.jc_texpr_type id in
	  let te2 = expr ((id,vi)::env) e2 in
	  te2.jc_texpr_type,te2.jc_texpr_region,JCTElet(vi,te1,te2)
	  (* logic expressions, not allowed as program expressions *)
      | JCPEoffset(k, e) ->
	  let te = expr env e in
	  begin
	    match te.jc_texpr_type with 
	      | JCTpointer(JCtag st,_,_) ->
		  integer_type,dummy_region,JCTEoffset(k,te,st)
	      | _ ->
		  typing_error e.jc_pexpr_loc "pointer expected"
	  end
      | JCPEmatch(arg, pel) ->
	  let targ = expr env arg in
	  let rty, tpel = match pel with
	    | [] -> assert false (* should not be allowed by the parser *)
	    | (p1, e1)::rem ->
		(* type the first item *)
		let penv, tp1 = pattern p1 targ.jc_texpr_type in
		let newenv = penv @ env in
		let te1 = expr newenv e1 in
		(* type the remaining items *)
		List.fold_left
		  (fun (accrty, acctpel) (p, e2) ->
		     let penv, tp = pattern p targ.jc_texpr_type in
		     let newenv = penv @ env in
		     let te2 = expr newenv e2 in
		     maxtype e.jc_pexpr_loc accrty te2.jc_texpr_type,
		     (tp, te2)::acctpel)
		  (te1.jc_texpr_type, [tp1, te1])
		  rem
	  in
	  rty, targ.jc_texpr_region, JCTEmatch(targ, List.rev tpel)
      | JCPEquantifier _ 
      | JCPEold _ 
      | JCPEat _
      | JCPErange _
      | JCPEmutable _
      | JCPEtagequality _ ->
	  typing_error e.jc_pexpr_loc "not allowed in this context"

  in { jc_texpr_node = te; 
       jc_texpr_type = t;
       jc_texpr_region = tr;
       jc_texpr_label = !lab;
       jc_texpr_loc = e.jc_pexpr_loc }

let loop_annot = 
  let globtag = ref 0 in
  let get() = let tag = !globtag in incr globtag; tag in
  fun label_env env i v ->
    let label_env = LabelHere::LabelPre::label_env in
    let ti = assertion label_env (Some LabelHere) env i
    and tv = match v with 
      | None -> None 
      | Some v -> Some (term label_env (Some LabelHere) env v)
    in
    (* TODO: check variant is integer, or other order ? *) 
    { 
      jc_loop_tag = get();
      jc_loop_invariant = ti;
      jc_free_loop_invariant = true_assertion;
      jc_loop_variant = tv;
    }


let make_block (l:tstatement list) : tstatement_node =
  match l with
    | [s] -> s.jc_tstatement_node
    | _ -> JCTSblock l

(* structure of labels in a function body : using Huet's zipper.
   Contrary to what is done in Caduceus, where gotos are first identified as
   GotoBackward/GotoForwardOuter/GotoForwardInner, and later on translated
   as exceptions in WHY, here both are done during typing.
*)

type label_tree =
  | LabelItem of label_info
  | LabelBlock of label_tree list

let rec printf_label_tree fmt lt =
  match lt with 
    | LabelItem s -> fprintf fmt "%s" s.label_info_name
    | LabelBlock l -> 
	fprintf fmt "{ %a }" (Pp.print_list Pp.space printf_label_tree ) l

let rec in_label_tree lab = function
  | LabelItem l -> if l.label_info_name=lab then l else raise Not_found
  | LabelBlock l -> in_label_tree_list lab l

and in_label_tree_list lab = function
  | [] -> raise Not_found
  | h::r -> 
      try in_label_tree lab h
      with Not_found -> in_label_tree_list lab r

let rec in_label_upper_tree_list lab = function
  | [] -> raise Not_found
  | LabelItem l :: _ when l.label_info_name=lab -> l
  | _ :: r -> in_label_upper_tree_list lab r

let build_label_tree s : label_tree list =
  (* [acc] is the tree of labels for the list of statements that follow 
     the current one, in the same block.
     [fwdacc] is the tree of labels for all the statements that follow 
     the current one to the end of the function. It is used to identify
     unused labels.
  *)
  let rec build_bwd s (acc,fwdacc) =
    match s.jc_pstatement_node with
      | JCPSskip  
      | JCPSexpr _ 
      | JCPSbreak _
      | JCPScontinue _
      | JCPSreturn _
      | JCPSpack _
      | JCPSunpack _ 
      | JCPSthrow _ 
      | JCPSdecl _ 
      | JCPSassert _ -> acc,fwdacc
      | JCPSgoto lab ->
	  begin try 
	    (* Count number of forward gotos. Labels with 0 count will
	       not be considered in generated try-catch. *)
	    let info = in_label_tree_list lab fwdacc in
	    info.times_used <- info.times_used + 1
	  with Not_found -> () end;
	  acc,fwdacc
      | JCPSif (e, s1, s2) ->
	  let l1,fwdl1 = build_bwd s1 ([],fwdacc) in
	  let l2,fwdl2 = build_bwd s2 ([],fwdl1) in 
	  (LabelBlock l1) :: (LabelBlock l2) :: acc, fwdl2
      | JCPSmatch (e, psl) ->
	  List.fold_left
	    (fun (acc, fwdacc) (_, sl) ->
	       let l, fwdl = List.fold_right build_bwd sl ([], fwdacc) in
	       (LabelBlock l)::acc, fwdl)
	    (acc, fwdacc)
	    psl
      | JCPSlabel (lab, s) ->
	  let info = { label_info_name = lab; times_used = 0 } in
	  let l,fwdl = build_bwd s (acc,fwdacc) in
	  (LabelItem info) :: l, (LabelItem info) :: fwdl
      | JCPSblock sl ->
	  let l,fwdl = List.fold_right build_bwd sl ([],fwdacc) in
	  (LabelBlock l) :: acc, fwdl
      | JCPSfor (_,_, _, _, _, _, s) 
      | JCPSwhile (_,_, _, _, s) ->
	  let l,fwdl = build_bwd s ([],fwdacc) in
	  (LabelBlock l) :: acc, fwdl
      | JCPSswitch (_, cl) ->
	  let l,fwdl = 
	    List.fold_right 
	      (fun (_,sl) (acc,fwdacc) ->
		 let l,fwdl = List.fold_right build_bwd sl ([],fwdacc) in
		 LabelBlock l :: acc, fwdl)
	      cl ([],fwdacc)
	  in (LabelBlock l) :: acc, fwdl
      | JCPStry (s,hl,fs) ->
	  let lf,fwdl = build_bwd fs ([],fwdacc) in
	  let l,fwdl = 
	    List.fold_right
	      (fun (_,_,s) (acc,fwdacc) ->
		 let l,fwdl = build_bwd s ([],fwdacc) in
		 LabelBlock l :: acc, fwdl)
	      hl ([],fwdl)
	  in
	  let ls,fwdl = build_bwd s ([],fwdl) in
	  LabelBlock ls
	  :: LabelBlock l
	  :: LabelBlock lf
	  :: acc, fwdl
  in
  let l,_ = build_bwd s ([],[]) in l

let build_label_tree sl : label_tree list =
  let bs = { jc_pstatement_node = JCPSblock sl;
	     jc_pstatement_loc = Loc.dummy_position; } in
  match build_label_tree bs with
    | [LabelBlock l] -> l
    | _ -> assert false

let rec statement label_env env lz s =
  let ts,lz =
    match s.jc_pstatement_node with
      | JCPSskip -> JCTSblock [], lz
      | JCPSthrow (id, Some e) -> 
	  let ei =
	    try Hashtbl.find exceptions_table id.jc_identifier_name 
	    with Not_found ->
	      typing_error id.jc_identifier_loc 
		"undeclared exception %s" id.jc_identifier_name
	  in
	  let te = expr env e in
	  let tei = match ei.jc_exception_info_type with
	    | Some tei -> tei
	    | None -> typing_error e.jc_pexpr_loc "no expression expected" 
	  in
	  if subtype te.jc_texpr_type tei then 
	    JCTSthrow(ei, Some te), lz
	  else
	    typing_error e.jc_pexpr_loc "%a type expected" print_type tei
      | JCPSthrow (id, None) ->
	  let ei =
	    try Hashtbl.find exceptions_table id.jc_identifier_name 
	    with Not_found ->
	      typing_error id.jc_identifier_loc 
		"undeclared exception %s" id.jc_identifier_name
	  in
	  JCTSthrow(ei, None), lz
      | JCPStry (s, catches, finally) -> 
	  let lz1,lz2,lz3,lz4 = match lz with
	    | before,LabelBlock b1::LabelBlock b2::LabelBlock b3::after ->
		(before,b1@after),
		(before,b2@after),
		(before,b3@after),
		(LabelBlock b1::LabelBlock b2::LabelBlock b3::before,after)
	    | _ -> assert false
	  in
	  let ts,_ = statement label_env env lz1 s in
	  let catches,_ = 
	    List.fold_left
	      (fun (acc,lz) (id,v,st) ->
		 let lz1,lz2 = match lz with
		   | before,LabelBlock b1::after ->
		       (before,b1@after),
		       (LabelBlock b1::before,after)
		   | _ -> assert false
		 in
		 let ei =
		   try Hashtbl.find exceptions_table id.jc_identifier_name 
		   with Not_found ->
		     typing_error id.jc_identifier_loc 
		       "undeclared exception %s" id.jc_identifier_name
		 in
		 let tei = match ei.jc_exception_info_type with
		   | Some tei -> tei
		   | None -> typing_error id.jc_identifier_loc 
		       "exception without value" 
		 in
		 let vi = var tei v in
		 let env' = (v,vi) :: env in
		 let s,_ = statement label_env env' lz1 st in
		 (ei,Some vi,s)::acc, lz2)
	      ([],lz2) catches
	  in
	  let fs,_ = statement label_env env lz3 finally in
	  JCTStry(ts,catches,fs), lz4
      | JCPSgoto lab -> 
	  let before,after = lz in
	  begin try
	    let _ = in_label_tree_list lab before in
	    typing_error s.jc_pstatement_loc "unsupported backward goto"
	  with Not_found ->
	    try
	      let _ = in_label_upper_tree_list lab after in
	      let id = "Goto_" ^ lab in
	      let ei =
		try Hashtbl.find exceptions_table id
		with Not_found ->
		  let ei = exception_info None id in
		  Hashtbl.add exceptions_table id ei;
		  ei
	      in
	      JCTSthrow(ei, None), lz
	    with Not_found ->
	      try
		let _ = in_label_tree_list lab after in
		typing_error s.jc_pstatement_loc 
		  "unsupported forward inner goto"
	      with Not_found ->
		typing_error s.jc_pstatement_loc "undefined label '%s'" lab
	  end
      | JCPSlabel (lab,s) -> 
	  let info,lz1 = match lz with
	    | before,LabelItem lab'::after ->
		assert (lab=lab'.label_info_name);
		lab',(LabelItem lab'::before,after)
	    | _ -> assert false
	  in
	  if info.times_used = 0 then
	    begin
	      (* unused label *)
	      let ts,lz2 = statement (LabelName lab::label_env) env lz1 s in
	      ts.jc_tstatement_node, lz2
	    end
	  else
	    let id = "Goto_" ^ lab in
	    let ei =
	      try Hashtbl.find exceptions_table id
	      with Not_found ->
		let ei = exception_info None id in
		Hashtbl.add exceptions_table id ei;
		ei
	    in
	    JCTSthrow(ei, None), lz1
      | JCPScontinue _ -> assert false
      | JCPSbreak l -> (* TODO: check l exists, check enclosing loop exists, *)
	  let li = { label_info_name = l ; times_used = 0 } in
	  JCTSbreak li, lz 
      | JCPSreturn None ->
	  JCTSreturn_void, lz
      | JCPSreturn (Some e) -> 
	  let te = expr env e in 
	  let vi = List.assoc "\\result" env in
	    if subtype te.jc_texpr_type vi.jc_var_info_type then
	      JCTSreturn (vi.jc_var_info_type, te), lz
	    else
	      typing_error s.jc_pstatement_loc 
		"type '%a' expected in return instead of '%a'"
		print_type vi.jc_var_info_type print_type te.jc_texpr_type
      | JCPSwhile(lab,cond,inv,var,body) -> 
	  let tc = expr env cond in
	  if subtype tc.jc_texpr_type boolean_type then
	    let lz1,lz2 = match lz with
	      | before,LabelBlock b1::after ->
		  (before,b1@after),
		  (LabelBlock b1::before,after)
	      | _ -> assert false
	    in
	    let lo = loop_annot label_env env inv var
	    and ts,_ = statement label_env env lz1 body
	    in
	    JCTSwhile(lab,tc,lo,ts), lz2
	  else 
	    typing_error cond.jc_pexpr_loc "boolean expected"
      | JCPSfor(lab,init,cond,updates,inv,var,body) -> 
	  let tcond = expr env cond in
	  if subtype tcond.jc_texpr_type boolean_type then
	    let lz1,lz2 = match lz with
	      | before,LabelBlock b1::after ->
		  (before,b1@after),
		  (LabelBlock b1::before,after)
	      | _ -> assert false
	    in
	    let lo = loop_annot label_env env inv var
	    and tbody,_ = statement label_env env lz1 body
	    and tupdates = List.map (expr env) updates
	    in
	    match init with
	      |	[] ->
		  JCTSfor(lab,tcond,tupdates,lo,tbody), lz2
	      | _ ->
		  let l =
		    List.fold_right
		      (fun init acc ->
			 let tinit = expr env init in
			 { jc_tstatement_loc = init.jc_pexpr_loc;
			   jc_tstatement_node = JCTSexpr tinit } :: acc)
		      init
		      [ { jc_tstatement_loc = s.jc_pstatement_loc;
			  jc_tstatement_node = 
			    JCTSfor(lab,tcond,tupdates,lo,tbody) 
			} ]
		  in JCTSblock l, lz2
	  else 
	    typing_error cond.jc_pexpr_loc "boolean expected"
	  
      | JCPSif (c, s1, s2) -> 
	  let tc = expr env c in
	  if subtype tc.jc_texpr_type boolean_type then
	    let lz1,lz2,lz3 = match lz with
	      | before,LabelBlock b1::LabelBlock b2::after ->
		  (before,b1@(LabelBlock b2)::after),
		  (before,b2@(LabelBlock b1)::after),
		  (LabelBlock b1::LabelBlock b2::before,after)
	      | (before,after) -> 
		  printf "before if: %a" printf_label_tree (LabelBlock before);
		  printf "after if: %a" printf_label_tree (LabelBlock after);
		  assert false
	    in
	    let ts1,_ = statement label_env env lz1 s1
	    and ts2,_ = statement label_env env lz2 s2
	    in
	    JCTSif(tc,ts1,ts2), lz3
	  else 
	    typing_error s.jc_pstatement_loc "boolean expected"
      | JCPSdecl (ty, id, e) -> 
	  typing_error s.jc_pstatement_loc
	    "decl of `%s' with statements afterwards" id, lz
      | JCPSassert( (*id,*) e) ->
          let a = assertion label_env (Some LabelHere) env e in
          JCTSassert((*Option_misc.map (fun x -> x.jc_identifier_name) id,*) a), lz
      | JCPSexpr e -> 
	  let te = expr env e in JCTSexpr te, lz
      | JCPSblock l -> 
	  let lz1,lz2 = match lz with
	    | before,LabelBlock b1::after ->
		(before,b1@after),
		(LabelBlock b1::before,after)
	    | _ -> assert false
	  in
	  make_block (statement_list label_env env lz1 l), lz2
      | JCPSpack (e, t) ->
	  let te = expr env e in
	  begin match te.jc_texpr_type with
	    | JCTpointer(JCtag st, _, _) ->
		let as_t = match t with
		  | Some t -> find_struct_info t.jc_identifier_loc t.jc_identifier_name
		  | None -> st
		in
		JCTSpack(st, te, as_t), lz
	    | _ ->
		typing_error s.jc_pstatement_loc 
		  "only structures can be packed"
	  end
      | JCPSunpack (e, t) ->
	  let te = expr env e in 
	  begin match te.jc_texpr_type with
	    | JCTpointer(JCtag st, _, _) ->
		let from_t = match t with
		  | Some t -> find_struct_info t.jc_identifier_loc t.jc_identifier_name
		  | None -> (*st*)
		      let rec res = {
			jc_struct_info_name = "bottom";
			jc_struct_info_parent = None;
			jc_struct_info_root = res;
			jc_struct_info_fields = [];
			jc_struct_info_variant = None;
		      }
		      in res
		in
		JCTSunpack(st, te, from_t), lz
	    | _ ->
		typing_error s.jc_pstatement_loc 
		  "only structures can be unpacked"
	  end
      | JCPSswitch (e,csl) ->
	  let tc = expr env e in
	  if subtype tc.jc_texpr_type integer_type then
	    let lz1,lz2 = match lz with
	      | before,LabelBlock b1::after ->
		  (before,b1@after),
		  (LabelBlock b1::before,after)
	      | _ -> assert false
	    in
	    let tcsl,_ = 
	      List.fold_left
		(fun (acc,lz) (labels,sl) -> 
		   let lz1,lz2 = match lz with
		     | before,LabelBlock b1::after ->
			 (before,b1@after),
			 (LabelBlock b1::before,after)
		     | _ -> assert false
		   in
		   let labels =
		     List.map
		       (fun e ->
			  match e with
			    | Some e ->
				let te = expr env e in
				if subtype te.jc_texpr_type integer_type then
				  Some te
				else
				  typing_error e.jc_pexpr_loc 
				    "integer expected in case"
			    | None -> None)
		       labels
		   in
		   let ts = statement_list label_env env lz1 sl in
		   (labels,ts) :: acc, lz2
		) ([],lz1) csl
	    in
	    JCTSswitch(tc,List.rev tcsl), lz2
	  else 
	    typing_error s.jc_pstatement_loc "integer expected"
      | JCPSmatch(e, psl) ->
	  let te = expr env e in
	  (* type patterns and bodies *)
	  let tpsl = List.map
	    (fun (p, sl) ->
	       let penv, tp = pattern p te.jc_texpr_type in
	       let newenv = penv @ env in
	       let tsl = statement_list label_env newenv lz sl in
	       tp, tsl)
	    psl
	  in
	  JCTSmatch(te, tpsl),
	  lz (* TODO *)
  in 
  let ts = { jc_tstatement_node = ts;
	     jc_tstatement_loc = s.jc_pstatement_loc } in
  ts, lz

(* Remarque de Romain : Pourquoi statement renvoie-t-il un "lz" mais pas
 * statement_list ? *)
and statement_list label_env env lz l : tstatement list =
  let rec block label_env env lz = function
    | [] -> [], []
    | s :: r -> 
	match s.jc_pstatement_node with
	  | JCPSskip -> block label_env env lz r
	  | JCPSdecl (ty, id, e) ->
	      let ty = type_type ty in
	      let vi = var ty id in
	      let te = 
		Option_misc.map
		  (fun e ->
		     let te = expr env e in
		     if subtype te.jc_texpr_type ty then 
		       te
		     else
		       typing_error s.jc_pstatement_loc 
			 "type '%a' expected in declaration instead of '%a'"
			 print_type ty print_type te.jc_texpr_type)
		  e
	      in
	      let tr,bl = block label_env ((id,vi)::env) lz r in
	      let tr = { jc_tstatement_loc = s.jc_pstatement_loc;
			 jc_tstatement_node = make_block tr } 
	      in
	      [ { jc_tstatement_loc = s.jc_pstatement_loc;
		  jc_tstatement_node = JCTSdecl(vi, te, tr); } ], bl

	  | JCPSlabel (lab,s) ->
	      let lab_info,lz1 = match lz with
		| before,LabelItem lab'::after ->
		    assert (lab=lab'.label_info_name);
		    lab',(LabelItem lab'::before,after)
		| _ -> assert false
	      in
	      let (bs,bl) = block (LabelName lab::label_env) env lz1 (s::r) in
	      let bs = { jc_tstatement_node = make_block bs;
			 jc_tstatement_loc = s.jc_pstatement_loc } 
	      in
	      if lab_info.times_used = 0 then
		begin		  
		  (* unused label *)
		  [{ jc_tstatement_loc = s.jc_pstatement_loc;
		    jc_tstatement_node = JCTSlabel (lab_info,bs)}], bl
		end
	      else
		let id = "Goto_" ^ lab in
		let ei =
		  try Hashtbl.find exceptions_table id
		  with Not_found ->
		    let ei = exception_info None id in
		    Hashtbl.add exceptions_table id ei;
		    ei
		in
		[ { jc_tstatement_loc = s.jc_pstatement_loc;
		    jc_tstatement_node = JCTSthrow(ei, None); } ], (lab,bs)::bl
	  | _ -> 
	      let s,lz' = statement label_env env lz s in
	      let r,bl = block label_env env lz' r in
	      s :: r, bl
  in
  let bs,bl = block label_env env lz l in
  let bs = { jc_tstatement_node = make_block bs;
	     jc_tstatement_loc = Loc.dummy_position } in
  let ts = List.fold_left 
    (fun acc (lab,si) ->
       let id = "Goto_" ^ lab in
       let ei =
	 try Hashtbl.find exceptions_table id
	 with Not_found ->
	   let ei = exception_info None id in
	   Hashtbl.add exceptions_table id ei;
	   ei
       in
       let skip = { jc_tstatement_node = JCTSblock [];
		    jc_tstatement_loc = Loc.dummy_position } in
       let sn = JCTStry(acc,[ei,None,si],skip) in
       { jc_tstatement_node = sn;
	 jc_tstatement_loc = Loc.dummy_position }
    ) bs bl
  in [ts]

(* Push labels of loops inside the loop structure, so that no program 
 * transformation can break this link between a label and a loop.
 * If a label is already associated to the loop, do not change it.
 *)
let rec pstatement ?(label="") s = 
  let pnode = match s.jc_pstatement_node with
    | JCPSlabel(lab,s) -> JCPSlabel(lab,pstatement ~label:lab s)
    | JCPSwhile(lab,cond,inv,var,body) -> 
	let lab = if lab = "" then label else lab in
	JCPSwhile(lab,cond,inv,var,pstatement body)
    | JCPSfor(lab,init,cond,updates,inv,var,body) -> 
	let lab = if lab = "" then label else lab in
	JCPSfor(lab,init,cond,updates,inv,var,pstatement body)
    | JCPStry(s,catches,finally) -> 
	let catches =
	  List.map (fun (ei,vio,s) -> (ei,vio,pstatement s)) catches
	in
	JCPStry(pstatement s,catches,pstatement finally)
    | JCPSif(c,s1,s2) -> 
	JCPSif(c,pstatement s1,pstatement s2)
    | JCPSblock ls -> 
	JCPSblock(pstatement_list ls)
    | JCPSswitch(e,cases) ->
	let cases = 
	  List.map (fun (values,ls) -> values,pstatement_list ls) cases in
	JCPSswitch(e,cases)
    | JCPSmatch(e,psl) ->
	let psl = List.map (fun (pat,ls) -> pat,pstatement_list ls) psl in
	JCPSmatch(e,psl)
    | JCPSskip | JCPSthrow _ | JCPSgoto _ | JCPScontinue _ | JCPSbreak _ 
    | JCPSreturn _ | JCPSdecl _ | JCPSassert _ | JCPSexpr _ | JCPSpack _ 
    | JCPSunpack _ ->
	s.jc_pstatement_node
  in 
  { s with jc_pstatement_node = pnode; }

and pstatement_list ls = List.map (fun s -> pstatement s) ls

let const_zero = 
  { jc_term_loc = Loc.dummy_position;
    jc_term_label = "";
    jc_term_type = integer_type;
    jc_term_region = dummy_region;
    jc_term_node = JCTconst (JCCinteger "0");
  }


let rec location_set label_env logic_label env e =
  match e.jc_pexpr_node with
    | JCPElabel(l,e) ->	
	  assert false (* TODO *)
    | JCPEvar id ->
	begin
	  try
	    let vi = List.assoc id env in 
	    match vi.jc_var_info_type with
	      | JCTpointer(_,_,_) ->
		  vi.jc_var_info_type,vi.jc_var_info_region,JCLSvar(vi)
	      | _ -> assert false
	  with Not_found -> 
	    try 
	      let vi = Hashtbl.find variables_env id in
	      match vi.jc_var_info_type with
		| JCTpointer(st,_,_) ->
		    vi.jc_var_info_type,vi.jc_var_info_region,JCLSvar(vi)
		| _ -> assert false
	    with Not_found -> 
	      typing_error e.jc_pexpr_loc "unbound identifier %s" id
	end
    | JCPEbinary(e,BPadd,i) ->
	let ty,tr,te = location_set label_env logic_label env e in
	let ti = term label_env logic_label env i in
	begin
	  match ty,ti.jc_term_type with 
	    | JCTpointer(st,_,_), JCTnative Tinteger ->
		begin match ti.jc_term_node with
		  | JCTrange(t1,t2) -> ty,tr,JCLSrange(te,t1,t2)
		  | _ -> ty,tr,JCLSrange(te,Some ti,Some ti)
		end
	    | JCTpointer _, _ -> 
		typing_error i.jc_pexpr_loc "integer expected, got %a" print_type ti.jc_term_type
	    | _ -> 
		typing_error e.jc_pexpr_loc "pointer expected"
	end
    | JCPEbinary _ -> assert false
    | JCPEderef (ls, f) -> 
	let t,tr,tls = location_set label_env logic_label env ls in
	let fi = find_field e.jc_pexpr_loc t f false in
	let fr = Region.make_field tr fi in
	begin match logic_label with
	  | None ->
	      typing_error e.jc_pexpr_loc "No memory state for this \
dereferenciation (\\at missing ?)"
	  | Some lab ->
	      fi.jc_field_info_type,fr,JCLSderef(tls,lab,fi,fr)	  
	end
    | JCPEif (_, _, _)
    | JCPElet _
    | JCPEoffset _
    | JCPEold _
    | JCPEat _
    | JCPEquantifier (_,_, _, _)
    | JCPEcast (_, _)
    | JCPEinstanceof (_, _)
    | JCPEunary (_, _)
    | JCPEassign_op (_, _, _)
    | JCPEassign (_, _)
    | JCPEapp _
    | JCPEconst _
    | JCPErange (_,_)
    | JCPEalloc (_,_)
    | JCPEmutable _
    | JCPEtagequality _
    | JCPEfree _
    | JCPEmatch _ -> assert false

let rec location label_env logic_label env e =
  match e.jc_pexpr_node with
    | JCPElabel(l,e) ->
	  assert false (* TODO *)
    | JCPEvar id ->
	begin
	  try
	    let vi = List.assoc id env in
	    vi.jc_var_info_type,vi.jc_var_info_region,JCLvar vi
	  with Not_found -> 
	    try 
	      let vi = Hashtbl.find variables_env id in
	      vi.jc_var_info_type,vi.jc_var_info_region,JCLvar vi
	    with Not_found -> 
	      typing_error e.jc_pexpr_loc "unbound identifier %s" id
	  end
    | JCPEderef(ls,f) ->
	begin
	  match logic_label with
	    | None -> typing_error e.jc_pexpr_loc "No label for this dereferenciation (\\at missing ?)"
	    | Some l ->
		let t,tr,tls = location_set label_env logic_label env ls in
		let fi = find_field e.jc_pexpr_loc t f false in
		let fr = Region.make_field tr fi in
		fi.jc_field_info_type,fr,JCLderef(tls,l,fi,fr)	  
	end
    | JCPEat(e,lab) ->
	if List.mem lab label_env then
	  let t,tr,tl = location label_env (Some lab) env e in
	  t,tr,JCLat(tl,lab)
	else
	  typing_error e.jc_pexpr_loc "label `%a' not found" Jc_output.label lab
	
	
    | JCPEold _ -> assert false (* TODO *)

    | JCPEif _ 
    | JCPEmatch _
    | JCPElet _ 
    | JCPEcast _
    | JCPEinstanceof _
    | JCPEoffset _
    | JCPEquantifier (_,_, _, _)
    | JCPEunary _
    | JCPEbinary (_, _, _)
    | JCPEassign_op (_, _, _)
    | JCPEassign (_, _)
    | JCPEapp _
    | JCPEconst _ 
    | JCPErange (_,_)
    | JCPEalloc (_,_)
    | JCPEmutable _
    | JCPEtagequality _
    | JCPEfree _ ->
	typing_error e.jc_pexpr_loc "invalid memory location"

let clause env vi_result c acc =
  match c with
    | JCPCrequires(e) ->
	{ acc with 
	  jc_fun_requires = 
	    make_and (assertion [] (Some LabelHere) env e) acc.jc_fun_requires; }
    | JCPCbehavior(loc,id,throws,assumes,requires,assigns,ensures) ->
	let throws,env_result = 
	  match throws with
	    | None -> None, (vi_result.jc_var_info_name,vi_result)::env 
	    | Some id -> 
		try 
		  let ei = 
		    Hashtbl.find exceptions_table id.jc_identifier_name 
		  in
		  let tei = match ei.jc_exception_info_type with
		    | Some tei -> tei
		    | None -> typing_error id.jc_identifier_loc
			"exception without value"
		  in
		  let vi = var tei "\\result" in
		  vi.jc_var_info_final_name <- "result";
		  Some ei, (vi.jc_var_info_name,vi)::env 
		with Not_found ->
		  typing_error id.jc_identifier_loc 
		    "undeclared exception %s" id.jc_identifier_name
	in
	let assumes = Option_misc.map (assertion [] (Some LabelHere) env) assumes in
(*
	let requires = Option_misc.map (assertion (Some "Here") env) requires in
*)
	let assigns = 
	  Option_misc.map 
	    (fun (loc,l) -> 
	      (loc,List.map (fun a -> let _,_,tl = location [LabelOld] (Some LabelHere) env a in tl) l)) 
	    assigns 
	in
	let b = {
	  jc_behavior_throws = throws;
	  jc_behavior_assumes = assumes;
(*
	  jc_behavior_requires = requires;
*)
	  jc_behavior_assigns = assigns;
	  jc_behavior_ensures = assertion [LabelOld;LabelHere] (Some LabelHere) env_result ensures }
	in
(*
	eprintf "lab,loc for ensures: \"%s\", %a@."
	  b.jc_behavior_ensures.jc_assertion_label
	  Loc.gen_report_position b.jc_behavior_ensures.jc_assertion_loc;
*)
	{ acc with jc_fun_behavior = (loc,id,b)::acc.jc_fun_behavior }
	  

  
let param (t,id) =
  let ty = type_type t in
  let vi = var ~formal:true ty id in 
  (id,vi)

let assertion_true =
  { jc_assertion_node = JCAtrue;
    jc_assertion_label = "";
    jc_assertion_loc = Loc.dummy_position }

let field st root (rep, t, id) =
  let ty = type_type t in
  incr field_tag_counter;
  let name = st.jc_struct_info_name ^ "_" ^ id in
  let fi = {
    jc_field_info_tag = !field_tag_counter;
    jc_field_info_name = id ;
    jc_field_info_final_name = Jc_envset.get_unique_name name;
    jc_field_info_type = ty;
    jc_field_info_root = root;
    jc_field_info_struct = st;
    jc_field_info_rep = rep or (not (is_pointer_type ty));
  } in
  fi

let axioms_table = Hashtbl.create 17
let global_invariants_table = Hashtbl.create 17

(*let add_typedecl d (id, parent) =
  let root,par = 
    match parent with
      | None -> 
	  (None, None)
      | Some p ->
	  let st = find_struct_info d.jc_pdecl_loc p in
	  (Some st.jc_struct_info_root, Some st)
  in
  let struct_info, root =
    try
      let struct_info,_ = Hashtbl.find structs_table id in
      let root = match root with
	| Some x -> x
	| None -> struct_info
      in
      struct_info.jc_struct_info_root <- root;
      struct_info.jc_struct_info_parent <- par;
      struct_info, root
    with Not_found ->
      assert false (* cannot happen, thanks to the function decl_declare *)
(*      let rec struct_info =
	{ jc_struct_info_name = id;
	  jc_struct_info_fields = [];
	  jc_struct_info_parent = par;
	  jc_struct_info_root = struct_info;
	  jc_struct_info_variant = None;
	}
      in
      (* adding structure name in global environment before typing 
	 the fields, because of possible recursive definition *)
      Hashtbl.replace structs_table id (struct_info,[]);
      struct_info, struct_info*)
  in
  root, struct_info*)

let add_fundecl (ty,loc,id,pl) =
  try
    let fi = Hashtbl.find functions_env id in
    Format.eprintf 
      "FIXME: Warning: ignoring second declaration of function %s@." id;
    let param_env =
      List.map (fun v -> v.jc_var_info_name, v) fi.jc_fun_info_parameters
    in
    param_env, fi
  with Not_found ->
    let param_env = List.map param pl in
    let ty = type_type ty in
    let fi = make_fun_info id ty in
      fi.jc_fun_info_parameters <- List.map snd param_env;
      Hashtbl.replace functions_env id fi;
      param_env, fi

let add_logic_fundecl (ty,id,labels,pl) =
  try
    let pi = Hashtbl.find logic_functions_env id in
    let ty = pi.jc_logic_info_result_type in
    let param_env =
      List.map (fun v -> v.jc_var_info_name, v) pi.jc_logic_info_parameters
    in
    param_env, ty, pi
  with Not_found ->
    let param_env = List.map param pl in
    let ty = Option_misc.map type_type ty in
    let pi = make_rel id in
    pi.jc_logic_info_parameters <- List.map snd param_env;
    pi.jc_logic_info_result_type <- ty;
    pi.jc_logic_info_labels <- labels;
    Hashtbl.replace logic_functions_env id pi;
    param_env, ty, pi

let add_logic_constdecl (ty,id) =
  try
    let vi = Hashtbl.find logic_constants_env id in
    vi.jc_var_info_type, vi 
  with Not_found ->
    let ty = type_type ty in
    let vi = var ~static:true ty id in
    Hashtbl.add logic_constants_env id vi;
    ty, vi

let type_range_of_term ty t =
  match ty with
    | JCTpointer (JCtag st, n1opt, n2opt) ->
(*	let instanceofcstr = raw_asrt (JCAinstanceof (t, st)) in *)
(* 	let mincstr = match n1opt with
	  | None -> true_assertion
	  | Some n1 ->
 	      let mint = 
		term_no_loc (JCToffset (Offset_min, t, st)) integer_type in
 	      let n1t =
 		term_no_loc (JCTconst (JCCinteger (Num.string_of_num n1))) 
		  integer_type
 	      in
 	      raw_asrt (JCArelation (mint, Beq_int, n1t))
 	in *)
 	let maxcstr = match n2opt with
	  | None -> true_assertion
	  | Some n2 ->
 	      let maxt = 
		term_no_loc (JCToffset (Offset_max, t, st)) integer_type in
 	      let n2t =
 		term_no_loc (JCTconst (JCCinteger (Num.string_of_num n2)))
		  integer_type
 	      in
 		raw_asrt (JCArelation (maxt, Beq_int, n2t))
 	in
	  maxcstr
(*        if is_root_struct st then *)
(* 	  Jc_pervasives.make_and [mincstr; maxcstr] *)
(*        else
 	  Jc_pervasives.make_and [instanceofcstr; mincstr; maxcstr] *)
    | JCTpointer (JCvariant vi, _, _) ->
	assert false (* TODO, but need to change JCToffset before *)
    | _ -> true_assertion

(* First pass: declare everything with no typing
 * (use dummy values that will be replaced by "decl")
 * (declare identifiers so that previous definitions can (possibly recursively)
 * use them) *)
(*let rec decl_declare d =
  match d.jc_pdecl_node with
    | JCPDtag(id, parent, fields, inv) ->
	(* declare structure name *)
	let rec struct_info = {
	  jc_struct_info_name = id;
	  jc_struct_info_fields = [];
	  jc_struct_info_parent = None;
	  jc_struct_info_root = struct_info;
	  jc_struct_info_variant = None;
	} in
	Hashtbl.add structs_table id (struct_info, []);
	(* declare mutable field (if needed) *)
	if parent = None && !Jc_common_options.inv_sem = InvOwnership then
	  create_mutable_field struct_info;
	(* TODO: declare fields *)
        (* TODO: declare invariants *)
	Hashtbl.replace structs_table id (struct_info, [])
    | JCPDvarianttype(id, _) ->
	Hashtbl.replace variants_table id {
	  jc_variant_info_name = id;
	  jc_variant_info_roots = [];
	}
    | JCPDvar _
    | JCPDfun _
    | JCPDrecfuns _
    | JCPDenumtype _
    | JCPDlogictype _
    | JCPDaxiom _
    | JCPDexception _
    | JCPDlogic _
    | JCPDglobinv _ ->
	() (* TODO *)
*)

let default_label l =
  match l with
    | [l] -> Some l
    | _ -> None

let rec decl d =
  match d.jc_pdecl_node with
    | JCPDvar (ty, id, init) ->
	let ty = type_type ty in
	let vi = var ~static:true ty id in
	let e = Option_misc.map (expr []) init in
	  Hashtbl.add variables_env id vi;
	  Hashtbl.add variables_table vi.jc_var_info_tag (vi, e);
    | JCPDfun (ty, id, pl, specs, body) -> 
	let loc = id.jc_identifier_loc in
	let param_env, fi = 
	  add_fundecl (ty, loc, id.jc_identifier_name, pl) 
	in
	let vi = fi.jc_fun_info_result in
	let s = List.fold_right 
		  (clause param_env vi) specs 
		  { jc_fun_requires = assertion_true;
		    jc_fun_free_requires = assertion_true;
		    jc_fun_behavior = [] }
	in
	let body = Option_misc.map pstatement_list body in
	let b = 
	  Option_misc.map 
	    (fun body ->
	       let lz = build_label_tree body in
	       (* Nicolas: 
		  this was printed by default... 
		  i put it in debug mode but don't know it's the right way to do so *)
	       (* Yannick: jc_options cannot be exported, and jc_typing must 
		  --> to use log here, move it out of jc_options 
		  if Jc_options.debug then 
		    printf "%a" printf_label_tree (LabelBlock lz); 
	        *)
		 statement_list [] (("\\result",vi)::param_env) ([],lz) body
	    ) body
	in
	  Hashtbl.add functions_table fi.jc_fun_info_tag (fi,loc,s,b)
    | JCPDrecfuns pdecls ->
        (* first pass: adding function names *)
	List.iter 
	  (fun d -> match d.jc_pdecl_node with
	     | JCPDfun(ty,id,pl,_,_) ->
		 ignore (add_fundecl (ty,id.jc_identifier_loc,
				      id.jc_identifier_name,pl))
	     | JCPDlogic(Some ty,id,labels,[],_) ->
		 ignore (add_logic_constdecl (ty,id))
	     | JCPDlogic(ty,id,labels,pl,_) ->
		 ignore (add_logic_fundecl (ty,id,labels,pl))
	     | _ -> assert false
	  ) pdecls;
        (* second pass: type function body *)
	List.iter decl pdecls
    | JCPDenumtype(id,min,max) ->
	let ri =
	  { jc_enum_info_name = id;
	    jc_enum_info_min = min;
	    jc_enum_info_max = max;
	  }
	in
(*
	let to_int = make_logic_fun ("integer_of_"^id) integer_type in
	let to_int_ = make_fun_info ("integer_of_"^id) integer_type in
	let of_int = make_fun_info (id^"_of_integer") (JCTenum ri) in
*)
	Hashtbl.add enum_types_table id (ri (*,to_int,to_int_,of_int*));
(*
	Hashtbl.add enum_conversion_logic_functions_table to_int id;
	Hashtbl.add enum_conversion_functions_table to_int_ id;
	Hashtbl.add enum_conversion_functions_table of_int id
*)

    | JCPDtag(id, parent, fields, inv) ->
	let struct_info, _ = Hashtbl.find structs_table id in
	let root = struct_info.jc_struct_info_root in
	(* fields *)
	let env = List.map (field struct_info root) fields in
	struct_info.jc_struct_info_fields <- env;
        (* declare invariants as logical functions *)
	let invariants =
	  List.fold_left
	    (fun acc (id, x, e) ->
	       if !Jc_common_options.inv_sem = InvNone then
		 typing_error id.jc_identifier_loc
		   "use of structure invariants requires declaration \
of an invariant policy";
	       let vi =
		 var (JCTpointer (JCtag struct_info, Some zero, Some zero)) x in
	       let p = assertion [] (Some LabelHere) [(x, vi)] e in
	       let pi = make_rel id.jc_identifier_name in
	       pi.jc_logic_info_parameters <- [vi];
	       pi.jc_logic_info_labels <- [LabelHere];
	       eprintf "generating logic fun %s with one default label@."
		 pi.jc_logic_info_name;
	       Hashtbl.replace logic_functions_table 
		 pi.jc_logic_info_tag (pi, JCAssertion p);
	       Hashtbl.replace logic_functions_env id.jc_identifier_name pi;
	       (pi, p) :: acc)
	    []
	    inv
	in 
	Hashtbl.replace structs_table id (struct_info, invariants)

    | JCPDvarianttype(id, tags) -> ()

(*    | JCPDrectypes(pdecls) ->
        (* first pass: adding structure names *)
	List.iter (fun d -> match d.jc_pdecl_node with
		     | JCPDstructtype(id,_,_,_) ->
			 (* parent type may not be declared yet *)
			 ignore (add_typedecl d (id,None))
		     | _ -> assert false
		  ) pdecls;
        (* second pass: adding structure fields *)
	List.iter (fun d -> match d.jc_pdecl_node with
		     | JCPDstructtype(id,parent,fields,_) ->
			 let root,struct_info = add_typedecl d (id,parent) in
			 let env = List.map (field struct_info root) fields in
			 struct_info.jc_struct_info_fields <- env;
			 Hashtbl.replace structs_table id (struct_info,[])
		     | _ -> assert false
		  ) pdecls;
        (* third pass: typing invariants *)
	List.iter decl pdecls*)

    | JCPDlogictype(id) ->
	begin 
	  try
	    let _ = Hashtbl.find logic_type_table id in
	    assert false
	  with Not_found ->
	    Hashtbl.add logic_type_table id id
	end
    | JCPDlemma(id,is_axiom,labels,e) ->
	let te = assertion labels (default_label labels) [] e in
	Hashtbl.add axioms_table id (is_axiom,labels,te)
    | JCPDglobinv (id, e) ->
	let a = assertion [] (Some LabelHere) (* None *) [] e in
	let li = make_rel id in
	  if !Jc_common_options.inv_sem = InvArguments then 
	    Hashtbl.replace logic_functions_table 
	      li.jc_logic_info_tag (li, JCAssertion a);
	  Hashtbl.add global_invariants_table li a
    | JCPDexception(id,t) ->
	let tt = type_type t in
	Hashtbl.add exceptions_table id (exception_info (Some tt) id)
    | JCPDlogic(Some ty, id, labels, [], body) ->
	let ty,vi = add_logic_constdecl (ty,id) in
	let t = match body with
	  | JCPReads reads -> 
	      assert (reads =[]);
	      None
	  | JCPExpr body ->
              let t = term labels (default_label labels) [] body in
              if not (subtype t.jc_term_type ty) then 
		typing_error d.jc_pdecl_loc 
		  "inferred type differs from declared type" 
	      else Some t
	in
	Hashtbl.add logic_constants_table vi.jc_var_info_tag (vi, t)
    | JCPDlogic(None, id, labels, pl, body) ->
	let param_env,ty,pi = add_logic_fundecl (None,id,labels,pl) in
	let p = match body with
	  | JCPReads reads ->
	      JCReads (
		(List.map 
		   (fun a -> 
		      let _,_,tl = 
			location labels (default_label labels) param_env a 
		      in tl)) reads)
	  | JCPExpr body ->
	      JCAssertion(assertion labels (default_label labels) param_env body)
	in
        Hashtbl.add logic_functions_table pi.jc_logic_info_tag (pi, p)
    | JCPDlogic(Some ty, id, labels, pl, body) ->
	let param_env,ty,pi = add_logic_fundecl (Some ty,id,labels,pl) in
	let ty = match ty with Some ty -> ty | None -> assert false in
	let t = match body with
	  | JCPReads reads ->
	      JCReads (
		(List.map 
		   (fun a -> 
		      let _,_,tl = location labels (default_label labels) param_env a 
		      in tl)) reads)
	  | JCPExpr body ->
              let t = term labels (default_label labels) param_env body in
              if not (subtype t.jc_term_type ty) then 
		typing_error d.jc_pdecl_loc 
		  "inferred type differs from declared type" 
	      else JCTerm t
	in
	Hashtbl.add logic_functions_table pi.jc_logic_info_tag (pi, t)

let declare_struct_info d = match d.jc_pdecl_node with
  | JCPDtag(id, parent, _, _) ->
      let rec si = {
	jc_struct_info_name = id;
	jc_struct_info_fields = [];
	jc_struct_info_parent = None;
	jc_struct_info_root = si;
	jc_struct_info_variant = None;
      } in
      Hashtbl.add structs_table id (si, []);
      (* declare the "mutable" field (if needed) *)
      if parent = None && !Jc_common_options.inv_sem = InvOwnership then
	create_mutable_field si
  | _ -> ()

let compute_struct_info_parent d = match d.jc_pdecl_node with
  | JCPDtag(id, Some parent, _, _) ->
      let si, _ = Hashtbl.find structs_table id in
      let psi = find_struct_info d.jc_pdecl_loc parent in
      si.jc_struct_info_parent <- Some psi
  | _ -> ()

let fixpoint_struct_info_roots () =
  let modified = ref false in
  Hashtbl.iter
    (fun _ (si, _) ->
       match si.jc_struct_info_parent with
	 | Some psi ->
	     if si.jc_struct_info_root != psi.jc_struct_info_root then begin
	       si.jc_struct_info_root <- psi.jc_struct_info_root;
	       modified := true
	     end
	 | None -> ())
    structs_table;
  !modified

let type_variant d = match d.jc_pdecl_node with
  | JCPDvarianttype(id, tags) ->
      (* declare the variant *)
      let vi = {
	jc_variant_info_name = id;
	jc_variant_info_roots = [];
      } in
      Hashtbl.add variants_table id vi;
      (* tags *)
      let roots = List.map
	(fun tag ->
	   (* find the structure *)
	   let st, _ = try
	     Hashtbl.find structs_table tag.jc_identifier_name
	   with Not_found ->
	     typing_error tag.jc_identifier_loc
	       "undefined tag: %s" tag.jc_identifier_name
	   in
	   (* the structure must be root *)
	   if st.jc_struct_info_parent <> None then
	     typing_error tag.jc_identifier_loc
	       "the tag %s is not root" tag.jc_identifier_name;
	   (* the structure must not be used by another variant *)
	   match st.jc_struct_info_variant with
	     | None ->
		 (* update the structure variant and return the root *)
		 st.jc_struct_info_variant <- Some vi;
		 st
	     | Some prev -> typing_error tag.jc_identifier_loc
		 "tag %s is already used by type %s" tag.jc_identifier_name
		   prev.jc_variant_info_name)
	tags
      in
      (* update the variant *)
      vi.jc_variant_info_roots <- roots
  | _ -> ()

let check_struct d = match d.jc_pdecl_node with
  | JCPDtag(id, _, _, _) ->
      let loc = d.jc_pdecl_loc in
      let st = find_struct_info loc id in
      if st.jc_struct_info_root.jc_struct_info_variant = None then
	typing_error loc "the tag %s is not used by any type"
	  st.jc_struct_info_name
  | _ -> ()

(* type declarations in the right order *)
let type_file ast =
  (* TODO: type enums before *)
  (* records and variants *)
  List.iter declare_struct_info ast;
  List.iter compute_struct_info_parent ast;
  while fixpoint_struct_info_roots () do () done;
  List.iter type_variant ast;
  List.iter check_struct ast;
  (* remaining declarations *)
  List.iter decl ast

(*
Local Variables: 
compile-command: "LC_ALL=C make -j -C .. bin/jessie.byte"
End: 
*)
