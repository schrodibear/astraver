(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-Fran�ois COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLI�TRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCH�                                                       *)
(*    Yannick MOY                                                         *)
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

open Jc_env
open Jc_envset
open Jc_fenv
open Jc_pervasives
open Jc_ast
open Format

exception Typing_error of Loc.position * string

let string_of_native t =
  match t with
    | Tunit -> "unit"
    | Tinteger -> "integer"
    | Treal -> "real"
    | Tboolean -> "boolean"

let print_type fmt t =
  match t with
    | JCTnative n -> fprintf fmt "%s" (string_of_native n)
    | JCTlogic s -> fprintf fmt "%s" s
    | JCTenum ri -> fprintf fmt "%s" ri.jc_enum_info_name
    | JCTpointer (s,a,b) -> 
	if Num.gt_num a b then
	  fprintf fmt "%s[..]" s.jc_struct_info_name
	else
	  if Num.eq_num a b then
	  fprintf fmt "%s[%s]" s.jc_struct_info_name
	    (Num.string_of_num a)
	else
	  fprintf fmt "%s[%s..%s]" s.jc_struct_info_name
	  (Num.string_of_num a) (Num.string_of_num b)
    | JCTnull -> fprintf fmt "(nulltype)"  

let typing_error l = 
  Format.kfprintf 
    (fun fmt -> raise (Typing_error(l, flush_str_formatter()))) 
    str_formatter

let logic_type_table = Hashtbl.create 97

let exceptions_table = Hashtbl.create 97

let enum_types_table = Hashtbl.create 97

let enum_conversion_functions_table = Hashtbl.create 97
let enum_conversion_logic_functions_table = Hashtbl.create 97

let structs_table = Hashtbl.create 97

let mutable_fields_table = Hashtbl.create 97 (* structure name (string) -> field info *)
let committed_fields_table = Hashtbl.create 97 (* structure name (string) -> field info *)

let logic_functions_table = Hashtbl.create 97
let logic_functions_env = Hashtbl.create 97
let functions_table = Hashtbl.create 97
let functions_env = Hashtbl.create 97
let variables_table = Hashtbl.create 97
let variables_env = Hashtbl.create 97

let field_tag_counter = ref 0

let create_mutable_field id =
(*  incr field_tag_counter;
  let fi = {
    jc_field_info_tag = !field_tag_counter;
    jc_field_info_name = "mutable_"^id;
    jc_field_info_type = boolean_type;
    jc_field_info_root = id;
    jc_field_info_struct = id;
  } in
  Hashtbl.add mutable_fields_table id fi;*)
  incr field_tag_counter;
  let fi = {
    jc_field_info_tag = !field_tag_counter;
    jc_field_info_name = "committed_"^id;
    jc_field_info_type = boolean_type;
    jc_field_info_root = id;
    jc_field_info_struct = id;
  } in
  Hashtbl.add committed_fields_table id fi

let find_struct_info loc id =
  try
    let st,_ = Hashtbl.find structs_table id in st
  with Not_found ->
    typing_error loc "undeclared structure %s" id

let is_numeric t =
  match t with
    | JCTnative (Tinteger|Treal) -> true
    | JCTenum _ -> true
    | _ -> false

let is_integer t =
  match t with
    | JCTnative Tinteger -> true
    | JCTenum _ -> true
    | _ -> false

let lub_numeric_types t1 t2 =
  match t1,t2 with
    | JCTnative Treal,_ | _,JCTnative Treal -> Treal
    | _ -> Tinteger

let rec substruct s1 s2 =
  if s1==s2 then true else
    let st = find_struct_info Loc.dummy_position s1.jc_struct_info_name in
    match st.jc_struct_info_parent with 
      | None -> false
      | Some s -> substruct s s2

let subtype t1 t2 =
  match t1,t2 with
    | JCTnative t1, JCTnative t2 -> t1=t2
    | JCTenum ri1, JCTenum ri2 -> 
	true
	  (*
	Num.ge_num ri1.jc_enum_info_min ri2.jc_enum_info_min 	&&
	Num.le_num ri1.jc_enum_info_max ri2.jc_enum_info_max
	  *)
    | JCTenum _, JCTnative Tinteger -> true
    | JCTnative Tinteger, JCTenum _ -> true
    | JCTlogic s1, JCTlogic s2 -> s1=s2
    | JCTpointer(s1,_,_), JCTpointer(s2,_,_) -> 
	  substruct s1 s2
    | JCTnull, JCTnull -> true
    | JCTnull, JCTpointer _ -> true
    | _ -> false

let comparable_types t1 t2 =
  match t1,t2 with
    | JCTnative t1, JCTnative t2 -> t1=t2
    | JCTenum _, JCTenum _ -> true
    | JCTenum _, JCTnative Tinteger -> true
    | JCTnative Tinteger, JCTenum _ -> true
    | JCTlogic s1, JCTlogic s2 -> s1=s2
    | JCTpointer(s1,_,_), JCTpointer(s2,_,_) -> 
	  s1.jc_struct_info_root = s2.jc_struct_info_root
    | JCTnull, JCTnull -> true
    | JCTnull, JCTpointer _
    | JCTpointer _, JCTnull -> true
    | _ -> false

let is_pointer_type t =
  match t with
    | JCTnull -> true
    | JCTpointer _ -> true
    | _ -> false


let rec find_field_struct loc st allow_mutable = function
  | ("mutable" | "committed") as x ->
      if allow_mutable then
	let table =
	  if x = "mutable" then mutable_fields_table
	  else committed_fields_table
	in
	Hashtbl.find table st.jc_struct_info_root
      else typing_error loc "field %s cannot be used here" x
  | f ->
      try
	List.assoc f st.jc_struct_info_fields
      with Not_found ->
	match st.jc_struct_info_parent with
	  | None -> 
	      typing_error loc "no field %s in structure %s" 
		f st.jc_struct_info_name
	  | Some st -> find_field_struct loc st allow_mutable f

  
let find_field loc ty f allow_mutable =
  match ty with
    | JCTpointer(st,_,_) -> find_field_struct loc st allow_mutable f
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
	let st = find_struct_info t.jc_ptype_loc id in
	JCTpointer(st, a, b)
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
    | Tboolean, UPnot -> Unot
    | Tunit,_ -> assert false
    | _ -> assert false

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
    | _, BPshift_right -> Bshift_right
    | _, BPshift_left -> Bshift_left

    | _, BPland -> assert false
    | _, BPlor -> assert false
    | Treal, BPmod -> assert false
	(* not allowed as expression op *)
    | _,BPiff -> assert false
    | _,BPimplies -> assert false
    | Tunit,_ -> assert false
    | Tboolean, BPeq -> assert false
    | Tboolean, BPneq -> assert false
    | Tboolean, _ -> assert false


let incr_op op =
  match op with
    | UPpostfix_inc -> Postfix_inc
    | UPpostfix_dec -> Postfix_dec
    | UPprefix_inc -> Prefix_inc
    | UPprefix_dec -> Prefix_dec
    | _ -> assert false


(* terms *)

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
    | UPbw_not -> JCTTunary(unary_op t op,e)
    | UPplus -> e.jc_tterm_node
    | _ -> assert false


let logic_unary_op loc (op : Jc_ast.punary_op) e =
  let t = e.jc_tterm_type in
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
	in JCTnative t,num_un_op t op e
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
	  { jc_tterm_node = JCTTapp(to_int,[e]) ;
	    jc_tterm_type = integer_type;
	    jc_tterm_loc = e.jc_tterm_loc }  
*)
	  Tinteger, e
      | JCTnative t -> t, e
      | _ -> assert false
  in
  match tn1,t2 with
    | Tinteger, Treal -> 
	{ jc_tterm_node = JCTTapp(real_of_integer,[e_int]) ;
	  jc_tterm_type = real_type;
	  jc_tterm_loc = e.jc_tterm_loc }  
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
  let t1 = e1.jc_tterm_type and t2 = e2.jc_tterm_type in
  match op with
    | BPgt | BPlt | BPge | BPle ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  boolean_type,
	  JCTTbinary(term_coerce t1 t e1, logic_bin_op t op, 
		     term_coerce t2 t e2)
	else
	  typing_error loc "numeric types expected for >, <, >= and <="
    | BPeq | BPneq ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  boolean_type,
	  JCTTbinary(term_coerce t1 t e1, logic_bin_op t op,
		     term_coerce t2 t e2)
	else
	if is_pointer_type t1 && is_pointer_type t2 && (comparable_types t1 t2) then
	  boolean_type,
	  JCTTbinary(e1, logic_bin_op Tunit op, e2)
	else
	  typing_error loc "numeric or pointer types expected for == and !="
    | BPadd | BPsub ->
	begin
	  match t1 with
	    | JCTpointer(st,_,_) ->
		if is_integer t2 then
		  t1, JCTTshift(e1, term_coerce t2 Tinteger e2)
		else
		  typing_error loc "integer type expected"
	    | _ ->
		if is_numeric t1 && is_numeric t2 then
		  let t = lub_numeric_types t1 t2 in
		  JCTnative t,
		  JCTTbinary(term_coerce t1 t e1, logic_bin_op t op,
			     term_coerce t2 t e2)
		else
		  typing_error loc "numeric types expected for + and -"
	end
    | BPmul | BPdiv | BPmod | BPbw_and | BPbw_or | BPbw_xor 
    | BPshift_right | BPshift_left ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  (JCTnative t,
	   JCTTbinary(term_coerce t1 t e1, logic_bin_op t op,
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
	in JCTnative t,JCTTbinary(e1, logic_bin_op t op, e2)

	(* not allowed as term op *)
    | BPimplies | BPiff -> assert false

	  
let rec term env e =
  let t,te =
    match e.jc_pexpr_node with
      | JCPEvar id ->
	  begin
	    try
	      let vi = List.assoc id env
	      in vi.jc_var_info_type,JCTTvar vi
	    with Not_found -> 
	      try 
		let vi = Hashtbl.find variables_env id 
		in vi.jc_var_info_type,JCTTvar vi
	      with Not_found -> 
		typing_error e.jc_pexpr_loc "unbound identifier %s" id
	  end
      | JCPEinstanceof(e1,t) -> 
	  let te1 = term env e1 in
	  let st = find_struct_info e.jc_pexpr_loc t in
	  boolean_type, JCTTinstanceof(te1,st)
      | JCPEcast(e1, t) -> 
	  let te1 = term env e1 in
	  let st = find_struct_info e.jc_pexpr_loc t in
	  begin
	    match te1.jc_tterm_type with
	      | JCTpointer(st1,a,b) ->
		  if substruct st st1 then
		    JCTpointer(st,a,b), JCTTcast(te1,st)
		  else
		    typing_error e.jc_pexpr_loc "invalid cast"
	      | _ ->
		  typing_error e.jc_pexpr_loc "only structures can be cast"
	  end
      | JCPEbinary (e1, op, e2) -> 
	  let e1 = term env e1 and e2 = term env e2 in
	  make_logic_bin_op e.jc_pexpr_loc op e1 e2 
      | JCPEunary(op, e2) -> 
	  let te2 = term env e2
	  in
	  logic_unary_op e.jc_pexpr_loc op te2
      | JCPEapp (e1, args) ->
	  begin
	    match e1.jc_pexpr_node with
	      | JCPEvar id ->
		  begin
		    try
		      let pi = find_logic_info id in
		      let tl =
			try
			  List.map2
			    (fun vi e ->
			       let ty = vi.jc_var_info_type in
			       let te = term env e in
			       if subtype te.jc_tterm_type ty then te
			       else
				 typing_error e.jc_pexpr_loc 
				   "type %a expected instead of %a" 
				   print_type ty print_type te.jc_tterm_type) 
			    pi.jc_logic_info_parameters args
			with  Invalid_argument _ ->
			  typing_error e.jc_pexpr_loc 
			    "wrong number of arguments for %s" id
		      in
		      let ty = match pi.jc_logic_info_result_type with
			| None -> assert false | Some ty -> ty
		      in
		      ty, JCTTapp(pi, tl)
		    with Not_found ->
		      typing_error e.jc_pexpr_loc 
			"unbound logic function identifier %s" id
		  end
	      | _ -> 
		  typing_error e.jc_pexpr_loc "unsupported logic function application"
	  end
      | JCPEderef (e1, f) -> 
	  let te = term env e1 in
	  let fi = find_field e.jc_pexpr_loc te.jc_tterm_type f true in
	  fi.jc_field_info_type, JCTTderef(te,fi)	  
      | JCPEconst c -> 
	  let t,c = const c in t,JCTTconst c
      | JCPEold e -> 
	  let te = term env e in te.jc_tterm_type,JCTTold(te)
      | JCPEoffset(k,e) -> 
	  let te = term env e in 
	  begin
	    match te.jc_tterm_type with 
	      | JCTpointer(st,_,_) ->
		  integer_type,JCTToffset(k,te,st)
	      | _ ->
		  typing_error e.jc_pexpr_loc "pointer expected"
	  end
      | JCPEif(e1,e2,e3) ->
	  let te1 = term env e1 
	  and te2 = term env e2
	  and te3 = term env e3 
	  in
	  begin
	    match te1.jc_tterm_type with
	      | JCTnative Tboolean ->
		  let t =
		    let t2 = te2.jc_tterm_type and t3 = te3.jc_tterm_type in
		    if subtype t2 t3 then t3 else
		      if subtype t3 t2 then t2 else
			typing_error e.jc_pexpr_loc 
			  "incompatible result types"
		  in
		  t, JCTTif(te1,te2,te3)
	      | _ ->
		  typing_error e1.jc_pexpr_loc 
		    "boolean expression expected"
	  end
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
      | JCPErange(e1,e2) ->
	  let e1 = term env e1 and e2 = term env e2 in
	  let t1 = e1.jc_tterm_type and t2 = e2.jc_tterm_type in
	  assert (is_numeric t1 && is_numeric t2);
	  let t = lub_numeric_types t1 t2 in
	  JCTnative t, JCTTrange(term_coerce t1 t e1, term_coerce t2 t e2)
      | JCPEmutable(e, t) ->
	  assert false (* TODO *)
	    
  in { jc_tterm_node = te;
       jc_tterm_type = t;
       jc_tterm_loc = e.jc_pexpr_loc }

  
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
  match (a1.jc_tassertion_node,a2.jc_tassertion_node) with
    | (JCTAtrue,a2) -> a2
    | (a1,JCTAtrue) -> a1
(*
    | (LFalse,_) -> LFalse
    | (_,LFalse) -> LFalse
*)
    | (JCTAand l1 , JCTAand l2) -> JCTAand(l1@l2)
    | (JCTAand l1 , _ ) -> JCTAand(l1@[a2])
    | (_ , JCTAand l2) -> JCTAand(a1::l2)
    | _ -> JCTAand [a1;a2]

let make_or a1 a2 =
  match (a1.jc_tassertion_node,a2.jc_tassertion_node) with
    | (JCTAfalse,a2) -> a2
    | (a1,JCTAfalse) -> a1
(*
    | (LFalse,_) -> LFalse
    | (_,LFalse) -> LFalse
*)
    | (JCTAor l1 , JCTAor l2) -> JCTAor(l1@l2)
    | (JCTAor l1 , _ ) -> JCTAor(l1@[a2])
    | (_ , JCTAor l2) -> JCTAor(a1::l2)
    | _ -> JCTAor [a1;a2]


let make_rel_bin_op loc op e1 e2 =
  let t1 = e1.jc_tterm_type and t2 = e2.jc_tterm_type in
  match op with
    | BPgt | BPlt | BPge | BPle ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  JCTArelation(term_coerce t1 t e1, rel_bin_op t op, term_coerce t2 t e2)
	else
	  typing_error loc "numeric types expected for >, <, >= and <="
    | BPeq | BPneq ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  JCTArelation(term_coerce t1 t e1, rel_bin_op t op,
		     term_coerce t2 t e2)
	else
	  if comparable_types t1 t2 then 
	    JCTArelation(e1, rel_bin_op Tunit op, e2)
	  else
	    typing_error loc "terms should have the same type for == and !="
	(* non propositional operators *)
    | BPadd | BPsub | BPmul | BPdiv | BPmod | BPbw_and | BPbw_or | BPbw_xor
    | BPshift_right | BPshift_left 
	-> assert false
	(* already recognized as connectives *)
    | BPland | BPlor -> assert false 
    | BPimplies -> assert false
    | BPiff -> assert false


let rec assertion env e =
  let te =
    match e.jc_pexpr_node with
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
		  JCTAbool_term { jc_tterm_loc = e.jc_pexpr_loc;
				  jc_tterm_type = vi.jc_var_info_type;
				  jc_tterm_node = JCTTvar vi }
	      | _ ->
		  typing_error e.jc_pexpr_loc "non boolean expression"
	  end
      | JCPEinstanceof(e1, t) -> 
	  let te1 = term env e1 in
	  let st = find_struct_info e.jc_pexpr_loc t in
	  JCTAinstanceof(te1,st) 
      | JCPEcast(e, t) -> assert false
      | JCPEbinary (e1, BPland, e2) -> 
	  let a1 = assertion env e1 in
	  let a2 = assertion env e2 in
	  make_and a1 a2
      | JCPEbinary (e1, BPlor, e2) -> 
	  make_or (assertion env e1) (assertion env e2)
      | JCPEbinary (e1, BPimplies, e2) -> 
	  let a1 = assertion env e1 in
	  let a2 = assertion env e2 in
	  JCTAimplies(a1,a2)
      | JCPEbinary (e1, BPiff, e2) -> 
	  JCTAiff(assertion env e1,assertion env e2)
      | JCPEunary (UPnot, e2) -> 
	  JCTAnot(assertion env e2)
      | JCPEbinary (e1, op, e2) -> 
	  let e1 = term env e1 and e2 = term env e2 in
	  make_rel_bin_op e.jc_pexpr_loc op e1 e2
      | JCPEunary(op, e2) -> 
	  let e2 = term env e2 in
	  JCTAapp(rel_unary_op e.jc_pexpr_loc op e2.jc_tterm_type,[e2])
      | JCPEapp (e1, args) ->
	  begin
	    match e1.jc_pexpr_node with
	      | JCPEvar id ->
		  begin
		    try
		      let pi = find_logic_info id in
		      let tl =
			try
			  List.map2
			    (fun vi e ->
			       let ty = vi.jc_var_info_type in
			       let te = term env e in
			       if subtype te.jc_tterm_type ty then te
			       else
				 typing_error e.jc_pexpr_loc 
				   "type %a expected instead of %a" 
				   print_type ty print_type te.jc_tterm_type) 
			    pi.jc_logic_info_parameters args
			with  Invalid_argument _ ->
			  typing_error e.jc_pexpr_loc 
			    "wrong number of arguments for %s" id
		      in
		      JCTAapp(pi, tl)
		    with Not_found ->
		      typing_error e.jc_pexpr_loc 
			"unbound predicate identifier %s" id
		  end
	      | _ -> 
		  typing_error e.jc_pexpr_loc "unsupported predicate application"
	  end
      | JCPEderef (e, id) -> 
	  let te = term env e in
	  let fi = find_field e.jc_pexpr_loc te.jc_tterm_type id true in
	  begin
	    match fi.jc_field_info_type with
	      | JCTnative Tboolean ->
		  JCTAbool_term { jc_tterm_loc = e.jc_pexpr_loc;
				  jc_tterm_type = fi.jc_field_info_type;
				  jc_tterm_node = JCTTderef(te,fi) }
	      | _ ->
		  typing_error e.jc_pexpr_loc "non boolean expression"
	  end
(*
      | JCPEshift (_, _) -> assert false
*)
      | JCPEconst c -> 
	  begin
	    match c with
	      | JCCboolean true -> JCTAtrue
	      | JCCboolean false -> JCTAfalse
	      | _ ->
		  typing_error e.jc_pexpr_loc "non propositional constant"
	  end
      | JCPEquantifier(q,ty,idl,e1) -> 
	  let ty = type_type ty in
	  (make_quantifier q e.jc_pexpr_loc ty idl env e1).jc_tassertion_node
      | JCPEold e -> JCTAold(assertion env e)
      | JCPEif(e1,e2,e3) ->
	  let te1 = term env e1 
	  and te2 = assertion env e2
	  and te3 = assertion env e3 
	  in
	  begin
	    match te1.jc_tterm_type with
	      | JCTnative Tboolean ->
		  JCTAif(te1,te2,te3)
	      | _ ->
		  typing_error e1.jc_pexpr_loc 
		    "boolean expression expected"
	  end
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
	  let te = term env e in
	  let st = match t with
	    | Some t -> Some (find_struct_info t.jc_identifier_loc t.jc_identifier_name)
	    | None -> None
	  in
	  let est = match te.jc_tterm_type with
	    | JCTpointer(est, _, _) -> est
	    | _ -> typing_error e.jc_pexpr_loc "pointer expression expected"
	  in
	  JCTAmutable(te, est, st)

  in { jc_tassertion_node = te;
       jc_tassertion_loc = e.jc_pexpr_loc }

and make_quantifier q loc ty idl env e : tassertion =
  match idl with
    | [] -> assertion env e
    | id::r ->
	let vi = var ty id in
	let f = 
	  JCTAquantifier(q,vi,make_quantifier q loc ty r ((id,vi)::env) e) 
	in
	{jc_tassertion_loc = loc ; jc_tassertion_node = f }

(* expressions *)

let set_assigned v =
(* Yannick: jc_options cannot be exported, and jc_typing must be
   --> to use log here, move it out of jc_options
  Jc_options.lprintf "Local var %s is assigned@." v.jc_var_info_name; 
*)
  v.jc_var_info_assigned <- true

let make_unary_app loc (op : Jc_ast.punary_op) e2 =
  let t2 = e2.jc_texpr_type in
  match op with
    | UPprefix_inc | UPpostfix_inc | UPprefix_dec | UPpostfix_dec ->
	begin
	  match e2.jc_texpr_node with
	    | JCTEvar v ->
		set_assigned v;
		t2,JCTEincr_local(incr_op op,v)
	    | JCTEderef(e,f) ->
		t2,JCTEincr_heap(incr_op op, e, f)
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
	in JCTnative t,JCTEunary(unary_op t op, e2)
    | UPplus | UPminus | UPbw_not -> 
	let t=
	  match t2 with
	    | JCTnative t2 ->
		begin
		  match t2 with
		    | Tinteger -> Tinteger
		    | Treal -> Treal
		    | _ -> assert false (* TODO *)
		end
	    | _ ->
		typing_error loc "numeric type expected"
	in JCTnative t,JCTEunary(unary_op t op, e2)

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
	  jc_texpr_loc = e.jc_texpr_loc }  
    | _ -> e_int




let make_bin_app loc op e1 e2 =
  let t1 = e1.jc_texpr_type and t2 = e2.jc_texpr_type in
  match op with
    | BPgt | BPlt | BPge | BPle ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  boolean_type,
	  JCTEbinary (coerce t1 t e1, bin_op t op, coerce t2 t e2)
	else
	  typing_error loc "numeric types expected for <, >, <= and >="
    | BPeq | BPneq ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  (boolean_type,
	   JCTEbinary(coerce t1 t e1, bin_op t op, coerce t2 t e2))
	else
	  if is_pointer_type t1 && is_pointer_type t2 && comparable_types t1 t2 then
	    (boolean_type,
	     JCTEbinary(e1, 
			(if op = BPeq then Beq_pointer else Bneq_pointer), e2))
	  else
	  typing_error loc "numeric or pointer types expected for == and !="
    | BPadd | BPsub ->
	begin
	  match t1 with
	    | JCTpointer(st,_,_) ->
		if is_integer t2 then
		  t1, JCTEshift(e1, coerce t2 Tinteger e2)
		else
		  typing_error loc "integer type expected"
	    | _ ->
		if is_numeric t1 && is_numeric t2 then
		  let t = lub_numeric_types t1 t2 in
		  JCTnative t,
		  JCTEbinary(coerce t1 t e1, bin_op t op, coerce t2 t e2)
		else
		  typing_error loc "numeric types expected for + and -"
	end
    | BPmul | BPdiv | BPmod | BPbw_and | BPbw_or | BPbw_xor 
    | BPshift_right | BPshift_left ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  JCTnative t,
	  JCTEbinary(coerce t1 t e1, bin_op t op, coerce t2 t e2)
	else
	  typing_error loc "numeric types expected for *, / and %%"
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
	in JCTnative t,JCTEbinary(e1, bin_op t op, e2)

	(* not allowed as expression op *)
    | BPimplies | BPiff -> assert false



let rec expr env e =
  let t,te =
    match e.jc_pexpr_node with
      | JCPEvar id ->
	  begin
	    try
	      let vi = List.assoc id env
	      in vi.jc_var_info_type,JCTEvar vi
	    with Not_found -> 
	      try 
		let vi = Hashtbl.find variables_env id
		in vi.jc_var_info_type,JCTEvar vi
	      with Not_found -> 
		typing_error e.jc_pexpr_loc "unbound identifier %s" id
	  end
      | JCPEinstanceof(e1, t) -> 
	  let te1 = expr env e1 in
	  let st = find_struct_info e.jc_pexpr_loc t in
	  boolean_type, JCTEinstanceof(te1,st)
      | JCPEcast(e1, t) -> 
	  let te1 = expr env e1 in
	  let st = find_struct_info e.jc_pexpr_loc t in
	  begin
	    match te1.jc_texpr_type with
	      | JCTpointer(st1,a,b) ->
		  if substruct st st1 then
		    JCTpointer(st,a,b), JCTEcast(te1,st)
		  else
		    typing_error e.jc_pexpr_loc "invalid cast"
	      | _ ->
		  typing_error e.jc_pexpr_loc "only structures can be cast"
	  end
      | JCPEalloc(e1, t) ->
	  let te1 = expr env e1 in
	  let st = find_struct_info e.jc_pexpr_loc t in
	  JCTpointer(st,Num.Int 0, Num.Int (-1)), JCTEalloc (te1, st)
      | JCPEfree e1 ->
	  let e1 = expr env e1 in
	  unit_type, JCTEfree e1
      | JCPEbinary (e1, op, e2) -> 
	  let e1 = expr env e1 and e2 = expr env e2 in
	  make_bin_app e.jc_pexpr_loc op e1 e2
      | JCPEunary (op, e2) -> 
	  let e2 = expr env e2 in
	  make_unary_app e.jc_pexpr_loc op e2
      | JCPEassign (e1, e2) -> 
	  begin
	    let te1 = expr env e1 and te2 = expr env e2 in
            let t1 = te1.jc_texpr_type and t2 = te2.jc_texpr_type in
	    if subtype t2 t1 then 
	      match te1.jc_texpr_node with
		| JCTEvar v ->
		    set_assigned v;
		    t1,JCTEassign_var(v,te2)
		| JCTEderef(e,f) ->
		    t1,JCTEassign_heap(e, f, te2)
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
		  let t,res = make_bin_app e.jc_pexpr_loc op te1 te2 in
		  if subtype t t1 then
		    match res with
		      | JCTEbinary(_,op,_) ->
			  t1,JCTEassign_var_op(v, op, te2)
		      | _ -> assert false
		  else
		    typing_error e2.jc_pexpr_loc 
		      "type '%a' expected in op-assignment instead of '%a'"
		      print_type t1 print_type t
	      | JCTEderef(te,f) ->
		  let t,res = make_bin_app e.jc_pexpr_loc op te1 te2 in
		  if subtype t t1 then
		    match res with
		      | JCTEbinary(_,op,_) ->
			  t1,JCTEassign_heap_op(te, f, op, te2)
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
		  let t,res = make_bin_app e.jc_texpr_loc op res te2 in
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

      | JCPEapp (e1, l) -> 
	  begin
	    match e1.jc_pexpr_node with
	      | JCPEvar id ->
		  begin
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
		      fi.jc_fun_info_return_type,JCTEcall(fi, tl)
		    with Not_found ->
		      typing_error e.jc_pexpr_loc 
			"unbound function identifier %s" id
		  end
	      | _ -> 
		  typing_error e.jc_pexpr_loc "unsupported function call"
	  end
      | JCPEderef (e1, f) -> 
	  let te = expr env e1 in
	  let fi = find_field e.jc_pexpr_loc te.jc_texpr_type f false in
	  fi.jc_field_info_type,JCTEderef(te,fi)
(*
      | JCPEshift (_, _) -> assert false
*)
      | JCPEconst c -> let t,tc = const c in t,JCTEconst tc
      | JCPEif(e1,e2,e3) ->
	  let te1 = expr env e1 
	  and te2 = expr env e2
	  and te3 = expr env e3 
	  in
	  begin
	    match te1.jc_texpr_type with
	      | JCTnative Tboolean ->
		  let t =
		    let t2 = te2.jc_texpr_type and t3 = te3.jc_texpr_type in
		    if subtype t2 t3 then t3 else
		      if subtype t3 t2 then t2 else
			typing_error e.jc_pexpr_loc 
			  "incompatible result types"
		  in
		  t, JCTEif(te1,te2,te3)
	      | _ ->
		  typing_error e1.jc_pexpr_loc 
		    "boolean expression expected"
	  end
	  (* logic expressions, not allowed as program expressions *)
      | JCPEoffset(k, e) ->
	  let te = expr env e in
	  begin
	    match te.jc_texpr_type with 
	      | JCTpointer(st,_,_) ->
		  integer_type,JCTEoffset(k,te,st)
	      | _ ->
		  typing_error e.jc_pexpr_loc "pointer expected"
	  end
      | JCPEquantifier _ 
      | JCPEold _ 
      | JCPErange _ ->
	  typing_error e.jc_pexpr_loc "not allowed in this context"
      | JCPEmutable(e, t) ->
	  assert false (* TODO *)

  in { jc_texpr_node = te; 
       jc_texpr_type = t;
       jc_texpr_loc = e.jc_pexpr_loc }

  

let loop_annot env i v =
  let ti = assertion env i
  and tv = term env v
  in
  (* TODO: check variant is integer, or other order ? *) 
  { jc_tloop_invariant = ti ;
    jc_tloop_variant = tv;
  }


let make_block (l:tstatement list) : tstatement_node =
  match l with
    | [s] -> s.jc_tstatement_node
    | _ -> JCTSblock l

let rec statement env s =
  let ts =
    match s.jc_pstatement_node with
      | JCPSskip -> JCTSblock []
      | JCPSthrow (id, Some e) -> 
	  let ei =
	    try Hashtbl.find exceptions_table id.jc_identifier_name 
	    with Not_found ->
	      typing_error id.jc_identifier_loc 
		"undeclared exception %s" id.jc_identifier_name
	  in
	  let te = expr env e in
	  if subtype te.jc_texpr_type ei.jc_exception_info_type then 
	    JCTSthrow(ei, Some te)
	  else
	    typing_error e.jc_pexpr_loc "%a type expected" 
	      print_type ei.jc_exception_info_type
      | JCPSthrow (id, None) -> assert false (* should never happen *)
      | JCPStry (s, catches, finally) -> 
	  let ts = statement env s in
	  let catches = 
	    List.map
	      (fun (id,v,st) ->
		 let ei =
		   try Hashtbl.find exceptions_table id.jc_identifier_name 
		   with Not_found ->
		     typing_error id.jc_identifier_loc 
		       "undeclared exception %s" id.jc_identifier_name
		 in
		 let vi = var ei.jc_exception_info_type v in
		 let env' = (v,vi) :: env in
		 (ei,vi,statement env' st))
	      catches
	  in
	  JCTStry(ts,catches,statement env finally)
      | JCPSgoto lab -> 
	  JCTSgoto lab
      | JCPSlabel (lab,s) -> 
	  JCTSlabel (lab,statement env s)
      | JCPScontinue _ -> assert false
      | JCPSbreak l -> 
	  JCTSbreak l (* TODO: check l exists, check enclosing loop exists, *)
      | JCPSreturn None ->
	  JCTSreturn_void
      | JCPSreturn (Some e) -> 
	  let te = expr env e in 
	  let vi = List.assoc "\\result" env in
	  if subtype te.jc_texpr_type vi.jc_var_info_type then
	    JCTSreturn(vi.jc_var_info_type,te)
	  else
	    typing_error s.jc_pstatement_loc 
	      "type '%a' expected in return instead of '%a'"
	      print_type vi.jc_var_info_type print_type te.jc_texpr_type
      | JCPSwhile(cond,inv,var,body) -> 
	  let tc = expr env cond in
	  if subtype tc.jc_texpr_type boolean_type then
	    let ts = statement env body
	    and lo = loop_annot env inv var
	    in
	    JCTSwhile(tc,lo,ts)
	  else 
	    typing_error cond.jc_pexpr_loc "boolean expected"
      | JCPSfor(init,cond,updates,inv,var,body) -> 
	  let tcond = expr env cond in
	  if subtype tcond.jc_texpr_type boolean_type then
	    let tbody = statement env body
	    and lo = loop_annot env inv var
	    and tupdates = List.map (expr env) updates
	    in
	    match init with
	      |	[] ->
		  JCTSfor(tcond,tupdates,lo,tbody)
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
			    JCTSfor(tcond,tupdates,lo,tbody) 
			} ]
		  in JCTSblock l
	  else 
	    typing_error cond.jc_pexpr_loc "boolean expected"
	  
      | JCPSif (c, s1, s2) -> 
	  let tc = expr env c in
	  if subtype tc.jc_texpr_type boolean_type then
	    let ts1 = statement env s1
	    and ts2 = statement env s2
	    in
	    JCTSif(tc,ts1,ts2)
	  else 
	    typing_error s.jc_pstatement_loc "boolean expected"
      | JCPSdecl (ty, id, e) -> 
	  typing_error s.jc_pstatement_loc
	    "decl of `%s' with statements afterwards" id
      | JCPSassert(id,e) ->
          let a = assertion env e in
          JCTSassert(Option_misc.map (fun x -> x.jc_identifier_name) id,a)
      | JCPSexpr e -> 
	  let te = expr env e in JCTSexpr te
      | JCPSblock l -> make_block (statement_list env l)
      | JCPSpack (e, t) ->
	  let te = expr env e in
	  begin match te.jc_texpr_type with
	    | JCTpointer(st, _, _) ->
		let as_t = match t with
		  | Some t -> find_struct_info t.jc_identifier_loc t.jc_identifier_name
		  | None -> st
		in
		JCTSpack(st, te, as_t)
	    | _ ->
		typing_error s.jc_pstatement_loc 
		  "only structures can be packed"
	  end
      | JCPSunpack (e, t) ->
	  let te = expr env e in 
	  begin match te.jc_texpr_type with
	    | JCTpointer(st, _, _) ->
		let from_t = match t with
		  | Some t -> find_struct_info t.jc_identifier_loc t.jc_identifier_name
		  | None -> (*st*)
		      { 
			jc_struct_info_name = "bottom";
			jc_struct_info_parent = None;
			jc_struct_info_root = "";
			jc_struct_info_fields = [];
		      }
		in
		JCTSunpack(st, te, from_t)
	    | _ ->
		typing_error s.jc_pstatement_loc 
		  "only structures can be unpacked"
	  end
      | JCPSswitch (e,csl) ->
	  let tc = expr env e in
	  if subtype tc.jc_texpr_type integer_type then
	    let tcsl = List.map 
	      (fun (labels,sl) -> 
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
		 let ts = statement_list env sl in
		 labels,ts
	      ) csl
	    in
	    JCTSswitch(tc,tcsl)
	  else 
	    typing_error s.jc_pstatement_loc "integer expected"

  in { jc_tstatement_node = ts;
       jc_tstatement_loc = s.jc_pstatement_loc }

and statement_list env l : tstatement list =
    match l with
      | [] -> []
      | s :: r -> 
	  match s.jc_pstatement_node with
	    | JCPSskip -> statement_list env r
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
		let tr = statement_list ((id,vi)::env) r in
		let tr = { jc_tstatement_loc = s.jc_pstatement_loc;
			   jc_tstatement_node = make_block tr } 
		in
		[ { jc_tstatement_loc = s.jc_pstatement_loc;
		    jc_tstatement_node = JCTSdecl(vi, te, tr); } ]
	    | _ -> 
		let s = statement env s in
		let r = statement_list env r in
		s :: r
  

let const_zero = 
  { jc_tterm_loc = Loc.dummy_position;
    jc_tterm_type = integer_type;
    jc_tterm_node = JCTTconst (JCCinteger "0");
  }


let rec location_set env e =
  match e.jc_pexpr_node with
    | JCPEvar id ->
	begin
	  try
	    let vi = List.assoc id env in 
	    match vi.jc_var_info_type with
	      | JCTpointer(st,_,_) ->
		  vi.jc_var_info_type,JCTLSvar(vi)
	      | _ -> assert false
	  with Not_found -> 
	    try 
	      let vi = Hashtbl.find variables_env id in
	      match vi.jc_var_info_type with
		| JCTpointer(st,_,_) ->
		    vi.jc_var_info_type,JCTLSvar(vi)
		| _ -> assert false
	    with Not_found -> 
	      typing_error e.jc_pexpr_loc "unbound identifier %s" id
	end
    | JCPEbinary(e,BPadd,i) ->
	let ty,te = location_set env e in
	let ti = term env i in
	begin
	  match ty,ti.jc_tterm_type with 
	    | JCTpointer(st,_,_), JCTnative Tinteger ->
		begin match ti.jc_tterm_node with
		  | JCTTrange(t1,t2) -> ty,JCTLSrange(te,t1,t2)
		  | _ -> ty,JCTLSrange(te,ti,ti)
		end
	    | JCTpointer _, _ -> 
		typing_error i.jc_pexpr_loc "integer expected, got %a" print_type ti.jc_tterm_type
	    | _ -> 
		typing_error e.jc_pexpr_loc "pointer expected"
	end
    | JCPEbinary _ -> assert false
    | JCPEderef (ls, f) -> 
	let t,tls = location_set env ls in
	let fi = find_field e.jc_pexpr_loc t f false in
	fi.jc_field_info_type, JCTLSderef(tls,fi)	  

    | JCPEif (_, _, _)
    | JCPEoffset _
    | JCPEold _
    | JCPEquantifier (_,_, _, _)
    | JCPEcast (_, _)
    | JCPEinstanceof (_, _)
    | JCPEunary (_, _)
    | JCPEassign_op (_, _, _)
    | JCPEassign (_, _)
    | JCPEapp (_, _)
    | JCPEconst _
    | JCPErange (_,_)
    | JCPEalloc (_,_)
    | JCPEmutable _ (* TODO ? *)
    | JCPEfree _ -> assert false

let location env e =
  match e.jc_pexpr_node with
    | JCPEvar id ->
	begin
	  try
	    let vi = List.assoc id env in
	    vi.jc_var_info_type,JCTLvar vi
	  with Not_found -> 
	    try 
	      let vi = Hashtbl.find variables_env id in
	      vi.jc_var_info_type,JCTLvar vi
	    with Not_found -> 
	      typing_error e.jc_pexpr_loc "unbound identifier %s" id
	  end
    | JCPEderef(ls,f) ->
	let t,tls = location_set env ls in
	let fi = find_field e.jc_pexpr_loc t f false in
	fi.jc_field_info_type, JCTLderef(tls,fi)	  
(*
    | JCPEshift (_, _)  -> assert false (* TODO *)
*)
    | JCPEif _ 
    | JCPEcast _
    | JCPEinstanceof _
    | JCPEold _ 
    | JCPEoffset _
    | JCPEquantifier (_,_, _, _)
    | JCPEunary _
    | JCPEbinary (_, _, _)
    | JCPEassign_op (_, _, _)
    | JCPEassign (_, _)
    | JCPEapp (_, _)
    | JCPEconst _ 
    | JCPErange (_,_)
    | JCPEalloc (_,_)
    | JCPEmutable _ (* TODO ? *)
    | JCPEfree _ ->
	typing_error e.jc_pexpr_loc "invalid memory location"

let clause env vi_result c acc =
  match c with
    | JCPCrequires(e) ->
	{ acc with 
	    jc_tfun_requires = assertion env e }
    | JCPCbehavior(id,throws,assumes,requires,assigns,ensures) ->
	let throws,env_result = 
	  match throws with
	    | None -> None, (vi_result.jc_var_info_name,vi_result)::env 
	    | Some id -> 
		try 
		  let ei = 
		    Hashtbl.find exceptions_table id.jc_identifier_name 
		  in
		  let vi = var ei.jc_exception_info_type "\\result" in
		  vi.jc_var_info_final_name <- "result";
		  Some ei, (vi.jc_var_info_name,vi)::env 
		with Not_found ->
		  typing_error id.jc_identifier_loc 
		    "undeclared exception %s" id.jc_identifier_name
	in
	let assumes = Option_misc.map (assertion env) assumes in
(*
	let requires = Option_misc.map (assertion env) requires in
*)
	let assigns = 
	  Option_misc.map (List.map (fun a -> snd (location env a))) assigns in
	let b = {
	  jc_tbehavior_throws = throws;
	  jc_tbehavior_assumes = assumes;
(*
	  jc_tbehavior_requires = requires;
*)
	  jc_tbehavior_assigns = assigns;
	  jc_tbehavior_ensures = assertion env_result ensures }
	in
	{ acc with jc_tfun_behavior = (id,b)::acc.jc_tfun_behavior }
	  

  
let param (t,id) =
  let ty = type_type t in
  let vi = var ~formal:true ty id in 
  (id,vi)

let assertion_true =
  { jc_tassertion_node = JCTAtrue;
    jc_tassertion_loc = Loc.dummy_position }

let field st root (t,id) =
  let ty = type_type t in
  incr field_tag_counter;
  let fi = {
    jc_field_info_tag = !field_tag_counter;
    jc_field_info_name = id;
    jc_field_info_type = ty;
    jc_field_info_root = root;
    jc_field_info_struct = st;
  }
  in (id,fi)


let axioms_table = Hashtbl.create 17
let global_invariants_table = Hashtbl.create 17

let add_typedecl d (id,parent) =
  let root,par = 
    match parent with
      | None -> 
	  (id,None)
      | Some p ->
	  let st = find_struct_info d.jc_pdecl_loc p in
	  (st.jc_struct_info_root,Some st)
  in
  let struct_info =
    try
      let struct_info,_ = Hashtbl.find structs_table id in
      struct_info.jc_struct_info_root <- root;
      struct_info.jc_struct_info_parent <- par;
      struct_info
    with Not_found ->
      let struct_info =
	{ jc_struct_info_name = id;
	  jc_struct_info_fields = [];
	  jc_struct_info_parent = par;
	  jc_struct_info_root = root;
	}
      in
      (* adding structure name in global environment before typing 
	 the fields, because of possible recursive definition *)
      Hashtbl.replace structs_table id (struct_info,[]);
      struct_info
  in
  root,struct_info

let add_fundecl (ty,id,pl) =
  try
    let fi = Hashtbl.find functions_env id in
    let ty = fi.jc_fun_info_return_type in
    let param_env =
      List.map (fun v -> v.jc_var_info_name, v) fi.jc_fun_info_parameters
    in
    param_env, ty, fi
  with Not_found ->
    let param_env = List.map param pl in
    let ty = type_type ty in
    let fi = make_fun_info id ty in
    fi.jc_fun_info_parameters <- List.map snd param_env;
    Hashtbl.replace functions_env id fi;
    param_env, ty, fi

let add_logic_fundecl (ty,id,pl) =
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
    Hashtbl.replace logic_functions_env id pi;
    param_env, ty, pi

let rec decl d =
  match d.jc_pdecl_node with
    | JCPDvar(ty,id,init) ->
	let ty = type_type ty in
	let vi = var ~static:true ty id in
	let e = Option_misc.map (expr []) init in
	Hashtbl.add variables_env id vi;
	Hashtbl.add variables_table vi.jc_var_info_tag (vi,e)
    | JCPDfun(ty,id,pl,specs,body) -> 
	let param_env,ty,fi = add_fundecl (ty,id,pl) in
	let vi = var ty "\\result" in
	vi.jc_var_info_final_name <- "result";
	let s = List.fold_right 
		  (clause param_env vi) specs 
		  { jc_tfun_requires = assertion_true;
		    jc_tfun_behavior = [] }
	in
	let b = 
	  Option_misc.map (statement_list (("\\result",vi)::param_env)) body 
	in
	Hashtbl.add functions_table fi.jc_fun_info_tag (fi,s,b)
    | JCPDrecfuns pdecls ->
        (* first pass: adding function names *)
	List.iter (fun d -> match d.jc_pdecl_node with
		     | JCPDfun(ty,id,pl,_,_) ->
			 ignore (add_fundecl (ty,id,pl))
		     | JCPDlogic(ty,id,pl,_) ->
			 ignore (add_logic_fundecl (ty,id,pl))
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
    | JCPDstructtype(id,parent,fields,inv) ->
	(* mutable field *)
	if parent = None then create_mutable_field id;
	(* adding structure name in global environment before typing 
	   the fields, because of possible recursive definition *)
	let root,struct_info = add_typedecl d (id,parent) in
	let env = List.map (field struct_info.jc_struct_info_name root) fields in
	struct_info.jc_struct_info_fields <- env;
	(* declare invariants as logical functions *)
	let invariants =
	  List.fold_left
	    (fun acc (id,x,e) ->	
	       let vi = var (JCTpointer(struct_info,zero,zero)) x in
	       let p = assertion [(x,vi)] e in
	       let pi = make_rel id in
	       pi.jc_logic_info_parameters <- [vi];
	       Hashtbl.replace logic_functions_table 
		 pi.jc_logic_info_tag (pi,JCTAssertion p);
	       Hashtbl.replace logic_functions_env id pi;
	       (pi,p) :: acc)
	    []
	    inv
	in
	Hashtbl.replace structs_table id (struct_info,invariants)
    | JCPDrectypes(pdecls) ->
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
			 let env = List.map (field struct_info.jc_struct_info_name root) fields in
			 struct_info.jc_struct_info_fields <- env;
			 Hashtbl.replace structs_table id (struct_info,[])
		     | _ -> assert false
		  ) pdecls;
        (* third pass: typing invariants *)
	List.iter decl pdecls
    | JCPDlogictype(id) ->
	begin 
	  try
	    let _ = Hashtbl.find logic_type_table id in
	    assert false
	  with Not_found ->
	    Hashtbl.add logic_type_table id id
	end
    | JCPDaxiom(id,e) ->
	let te = assertion [] e in
	Hashtbl.add axioms_table id te
    | JCPDglobinv(id,e) ->
	let te = assertion [] e in
	Hashtbl.add global_invariants_table id te
    | JCPDexception(id,t) ->
	let tt = type_type t in
	Hashtbl.add exceptions_table id (exception_info tt id)
    | JCPDlogic(None, id, pl, body) ->
	let param_env,ty,pi = add_logic_fundecl (None,id,pl) in
	let p = match body with
	  | JCPReads reads ->
	      JCTReads ((List.map (fun a -> snd (location param_env a))) reads)
	  | JCPExpr body ->
	      JCTAssertion(assertion param_env body)
	in
        Hashtbl.add logic_functions_table pi.jc_logic_info_tag (pi, p)
    | JCPDlogic(Some ty, id, pl, body) ->
	let param_env,ty,pi = add_logic_fundecl (Some ty,id,pl) in
	let ty = match ty with Some ty -> ty | None -> assert false in
	let t = match body with
	  | JCPReads reads ->
	      JCTReads ((List.map (fun a -> snd (location param_env a))) reads)
	  | JCPExpr body ->
              let t = term param_env body in
              if not (subtype t.jc_tterm_type ty) then 
		typing_error d.jc_pdecl_loc 
		  "inferred type differs from declared type" 
	      else JCTTerm t
	in
	Hashtbl.add logic_functions_table pi.jc_logic_info_tag (pi, t)

(*
Local Variables: 
compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
End: 
*)
