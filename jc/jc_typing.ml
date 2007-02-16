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

let typing_error l = 
  Format.kfprintf 
    (fun fmt -> raise (Typing_error(l, flush_str_formatter()))) 
    str_formatter


let logic_type_table = Hashtbl.create 97

let exceptions_table = Hashtbl.create 97

let range_types_table = Hashtbl.create 97

let structs_table = Hashtbl.create 97

let find_struct_info loc id =
  try
    let st,_ = Hashtbl.find structs_table id in st
  with Not_found ->
    typing_error loc "undeclared structure %s" id

let is_numeric t =
  match t with
    | JCTnative (Tinteger|Treal) -> true
    | JCTrange _ -> true
    | _ -> false

let is_integer t =
  match t with
    | JCTnative Tinteger -> true
    | JCTrange _ -> true
    | _ -> false

let lub_numeric_types t1 t2 =
  match t1,t2 with
    | JCTnative Treal,_ | _,JCTnative Treal -> Treal
    | _ -> Tinteger

let rec substruct s1 s2 =
  if s1=s2 then true else
    let st = find_struct_info Loc.dummy_position s1.jc_struct_info_name in
    match st.jc_struct_info_parent with 
      | None -> false
      | Some s -> substruct s s2

let subtype t1 t2 =
  match t1,t2 with
    | JCTnative t1, JCTnative t2 -> t1=t2
    | JCTrange ri1, JCTrange ri2 -> 
	Num.ge_num ri1.jc_range_info_min ri2.jc_range_info_min 	&&
	Num.le_num ri1.jc_range_info_max ri2.jc_range_info_max
    | JCTrange _, JCTnative Tinteger -> true
    | JCTlogic s1, JCTlogic s2 -> s1=s2
    | JCTpointer(s1,_,_),JCTpointer(s2,_,_) -> 
	  substruct s1 s2
    | _ -> false

let comparable_types t1 t2 =
  match t1,t2 with
    | JCTnative t1, JCTnative t2 -> t1=t2
    | JCTrange _, JCTrange _ -> true
    | JCTrange _, JCTnative Tinteger -> true
    | JCTnative Tinteger, JCTrange _ -> true
    | JCTlogic s1, JCTlogic s2 -> s1=s2
    | JCTpointer(s1,_,_),JCTpointer(s2,_,_) -> 
	  s1.jc_struct_info_root = s2.jc_struct_info_root
    | _ -> false
  

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
    | JCTrange ri -> fprintf fmt "%s" ri.jc_range_info_name
    | JCTpointer (s,_,_) -> fprintf fmt "%s" s.jc_struct_info_name


let logic_functions_table = Hashtbl.create 97
let functions_table = Hashtbl.create 97
let functions_env = Hashtbl.create 97


let rec find_field_struct loc st f =
  try
    List.assoc f st.jc_struct_info_fields
  with Not_found ->
    match st.jc_struct_info_parent with
      | None -> 
	  typing_error loc "no field %s in structure %s" 
	    f st.jc_struct_info_name
      | Some st -> find_field_struct loc st f

  
let find_field loc ty f =
  match ty with
    | JCTpointer(st,_,_) -> find_field_struct loc st f
    | JCTnative _ 
    | JCTrange _
    | JCTlogic _ ->
	typing_error loc "not a structure type"

let find_fun_info id = Hashtbl.find functions_env id
    
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
	    let (ri,_,_,_) = Hashtbl.find range_types_table id in
	    JCTrange ri
	  with Not_found ->
	    typing_error t.jc_ptype_loc "unknown type %s" id



(* constants *)

let const c =
  match c with
    | JCCvoid -> unit_type,c
    | JCCinteger _ -> integer_type,c
    | JCCreal _ -> real_type,c
    | JCCboolean _ -> boolean_type,c
    | JCCnull -> assert false

(* variables *)

let var_tag_counter = ref 0

let var ty id =
  incr var_tag_counter;
  let vi = {
    jc_var_info_tag = !var_tag_counter;
    jc_var_info_name = id;
    jc_var_info_final_name = id;
    jc_var_info_type = ty;
    jc_var_info_assigned = false;
  }
  in vi

(* exceptions *)

let exception_tag_counter = ref 0

let exception_info id ty =
  incr exception_tag_counter;
  let ei = {
    jc_exception_info_tag = !exception_tag_counter;
    jc_exception_info_name = id;
    jc_exception_info_type = ty;
  }
  in ei

(* terms *)

let num_op op =
  match op with
    | Badd -> add_int
    | Bsub -> sub_int
    | Bmul -> mul_int
    | Bdiv -> div_int
    | Bmod -> mod_int
    | _ -> assert false

let num_un_op op e =
  match op with
    | Uminus -> JCTapp(minus_int,[e])
    | Uplus -> e.jc_term_node
    | _ -> assert false

let eq_op op arg_type  =
  match (op,arg_type) with
    | (Beq,Tinteger) -> eq_int_bool
    | (Bneq,Tinteger) -> neq_int_bool
    | _ -> assert false

let logic_unary_op loc (op : Jc_ast.punary_op) t e =
  match op with
    | Unot -> assert false
    | Uminus | Uplus -> 
	let t =
	  match t with
	    | JCTnative t ->
		begin
		  match t with
		    | Tinteger -> Tinteger
		    | _ -> assert false (* TODO *)
		end
	    | _ ->
		typing_error loc "numeric type expected"
	in JCTnative t,num_un_op op e
    | Upostfix_dec | Upostfix_inc | Uprefix_dec | Uprefix_inc ->
	typing_error loc "pre/post incr/decr not allowed as logical term"

let term_coerce t1 t2 e =
  let e_int =
    match t1 with
      | JCTrange ri ->
	  let (_,to_int,_,_) = 
	    Hashtbl.find range_types_table ri.jc_range_info_name 
	  in
	  { jc_term_node = JCTapp(to_int,[e]) ;
	    jc_term_loc = e.jc_term_loc }  
      | _ -> e
  in
  match t2 with
    | Tinteger -> e_int
    | Treal -> 
	{ jc_term_node = JCTapp(real_of_integer,[e_int]) ;
	  jc_term_loc = e.jc_term_loc }  
    | _ -> assert false

let logic_bin_op loc (op : Jc_ast.pbin_op) t1 e1 t2 e2 =
  match op with
    | Bgt | Blt | Bge | Ble -> 
	typing_error loc "comparison not allowed as a term (todo)"
    | Beq | Bneq ->
	let t =
	  match t1,t2 with
	    | JCTnative t1, JCTnative t2 ->
		begin
		  match (t1,t2) with
		    | Tinteger,Tinteger -> Tinteger
		    | _ -> assert false (* TODO *)
		end
	    | _ -> assert false
	in
	JCTnative t,JCTapp(eq_op op t,[e1;e2])
    | Badd | Bsub ->
	begin
	  match (t1,t2) with
	    | JCTnative nt1, JCTnative nt2 ->
		begin
		  match (nt1,nt2) with
		    | Tinteger,Tinteger -> 
			t1,JCTapp(num_op op,[e1;e2])
		    | _ -> assert false (* TODO *)
		end
	    | JCTpointer(st,a,b), JCTnative t2 ->
		begin
		  match t2 with
		    | Tinteger -> 
			JCTpointer(st,zero,minus_one), JCTapp(shift,[e1;e2])
		    | _ -> assert false (* TODO *)
		end
	    | _ ->
		typing_error loc "numeric types expected"
	end 
    | Bmul | Bdiv | Bmod ->
	let t =
	  match (t1,t2) with
	    | JCTnative t1, JCTnative t2 ->
		begin
		  match (t1,t2) with
		    | Tinteger,Tinteger -> Tinteger
		    | _ -> assert false (* TODO *)
		end
	    | _ ->
		typing_error loc "numeric types expected"
	in JCTnative t,JCTapp(num_op op,[e1;e2])
    | Bland | Blor -> assert false (* TODO *)
    | Bimplies -> assert false
    | Biff -> assert false

let logic_bin_op t op =
  match t,op with
    | _, Bgt -> gt_int
    | _, Blt -> lt_int
    | _, Bge -> ge_int
    | _, Ble -> le_int
    | _, Beq -> eq
    | _, Bneq -> neq
    | Tinteger, Badd -> add_int
    | Treal, Badd -> add_real
    | _, Bsub -> sub_int
    | _, Bmul -> mul_int
    | _, Bdiv -> div_int
    | _, Bmod -> mod_int
    | Tboolean, Bland -> band 
    | Tboolean, Blor -> bor
	(* not allowed as expression op *)
    | _,Bimplies -> assert false
    | Tunit,_ -> assert false
    | _ -> assert false

let make_logic_bin_op loc op t1 e1 t2 e2 =
  match op with
    | Bgt | Blt | Bge | Ble | Beq | Bneq ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  JCTnative Tboolean,
	  JCTapp(logic_bin_op Tboolean op,[term_coerce t1 t e1; term_coerce t2 t e2])
	else
	  typing_error loc "numeric types expected"
    | Badd | Bsub ->
	begin
	  match t1 with
	    | JCTpointer(st,_,_) ->
		if is_integer t2 then
		  t1, JCTapp(shift,[e1;term_coerce t2 Tinteger e2])
		else
		  typing_error loc "integer type expected"
	    | _ ->
		if is_numeric t1 && is_numeric t2 then
		  let t = lub_numeric_types t1 t2 in
		  JCTnative t,
		  JCTapp(logic_bin_op t op,[term_coerce t1 t e1; term_coerce t2 t e2])
		else
		  typing_error loc "numeric types expected"
	end
    | Bmul | Bdiv | Bmod ->
	let t=
	  match (t1,t2) with
	    | JCTnative t1, JCTnative t2 ->
		begin
		  match (t1,t2) with
		    | Tinteger,Tinteger -> Tinteger
		    | Treal,Treal -> Treal
		    | _ -> assert false (* TODO *)
		end
	    | _ ->
		typing_error loc "numeric types expected"
	in JCTnative t,JCTapp(logic_bin_op t op,[e1;e2])
    | Bland | Blor -> 
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
	in JCTnative t,JCTapp(logic_bin_op t op,[e1;e2])

	(* not allowed as term op *)
    | Bimplies | Biff -> assert false

	  
let rec term env e =
  let t,te =
    match e.jc_pexpr_node with
      | JCPEvar id ->
	  begin
	    try
	      let vi = List.assoc id env
	      in vi.jc_var_info_type,JCTvar vi
	    with Not_found -> 
	      typing_error e.jc_pexpr_loc "unbound identifier %s" id
	  end
      | JCPEinstanceof(e1,t) -> 
	  let t1,te1 = term env e1 in
	  let st = find_struct_info e.jc_pexpr_loc t in
	  JCTnative Tboolean, JCTinstanceof(te1,st)
      | JCPEcast(e1, t) -> 
	  let t1,te1 = term env e1 in
	  let st = find_struct_info e.jc_pexpr_loc t in
	  begin
	    match t1 with
	      | JCTpointer(st1,a,b) ->
		  if substruct st st1 then
		    JCTpointer(st,a,b), JCTcast(te1,st)
		  else
		    typing_error e.jc_pexpr_loc "invalid cast"
	      | _ ->
		  typing_error e.jc_pexpr_loc "only structures can be cast"
	  end
      | JCPEbinary (e1, op, e2) -> 
	  let t1,e1 = term env e1
	  and t2,e2 = term env e2
	  in
	  make_logic_bin_op e.jc_pexpr_loc op t1 e1 t2 e2
      | JCPEunary(op, e2) -> 
	  let t2,e2 = term env e2
	  in
	  logic_unary_op e.jc_pexpr_loc op t2 e2
      | JCPEapp (_, _) -> assert false
      | JCPEderef (e1, f) -> 
	  let t,te = term env e1 in
	  let fi = find_field e.jc_pexpr_loc t f in
	  fi.jc_field_info_type, JCTderef(te,fi)	  
(*
      | JCPEshift (_, _) -> assert false
*)
      | JCPEconst c -> 
	  let t,c = const c in t,JCTconst c
      | JCPEold e -> 
	  let t,e = term env e in t,JCTold(e)
      | JCPEoffset_max e -> 
	  let t,te = term env e in 
	  begin
	    match t with 
	      | JCTpointer(st,_,_) ->
		  integer_type,JCToffset_max(te,st)
	      | _ ->
		  typing_error e.jc_pexpr_loc "pointer expected"
	  end
      | JCPEoffset_min e -> 
	  let t,te = term env e in 
	  begin
	    match t with 
	      | JCTpointer(st,_,_) ->
		  integer_type,JCToffset_min(te,st)
	      | _ ->
		  typing_error e.jc_pexpr_loc "pointer expected"
	  end
      | JCPEif(e1,e2,e3) ->
	  let t1,te1 = term env e1 
	  and t2,te2 = term env e2
	  and t3,te3 = term env e3 
	  in
	  begin
	    match t1 with
	      | JCTnative Tboolean ->
		  let t =
		    if subtype t2 t3 then t3 else
		      if subtype t3 t2 then t2 else
			typing_error e.jc_pexpr_loc 
			  "imcompatible result types"
		  in
		  t, JCTif(te1,te2,te3)
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
      | JCPEforall _ -> 
	  typing_error e.jc_pexpr_loc 
	    "quantification not allowed as logic term"

  in t,{ jc_term_node = te;
	 jc_term_loc = e.jc_pexpr_loc }

  
let rel_unary_op loc op t =
  match op with
    | Unot -> assert false
    | Uminus | Uplus -> 
	typing_error loc "not a proposition"
    | Upostfix_dec | Upostfix_inc | Uprefix_dec | Uprefix_inc ->
	typing_error loc "pre/post incr/decr not allowed as logical term"


let rel_bin_op t op =
  match t,op with
    | Tinteger,Bgt -> gt_int
    | Tinteger,Blt -> lt_int
    | Tinteger,Bge -> ge_int
    | Tinteger,Ble -> le_int
    | _,Beq -> eq
    | _,Bneq -> neq
    | _,(Badd | Bsub | Bmul | Bdiv | Bmod) -> assert false
    | _,(Bland | Blor | Bimplies | Biff) -> assert false
    | _ -> assert false  (* TODO *)


let make_and a1 a2 =
  match (a1.jc_assertion_node,a2.jc_assertion_node) with
    | (JCAtrue,a2) -> a2
    | (a1,JCAtrue) -> a1
(*
    | (LFalse,_) -> LFalse
    | (_,LFalse) -> LFalse
*)
    | (JCAand l1 , JCAand l2) -> JCAand(l1@l2)
    | (JCAand l1 , _ ) -> JCAand(l1@[a2])
    | (_ , JCAand l2) -> JCAand(a1::l2)
    | _ -> JCAand [a1;a2]

let make_or a1 a2 =
  match (a1.jc_assertion_node,a2.jc_assertion_node) with
    | (JCAfalse,a2) -> a2
    | (a1,JCAfalse) -> a1
(*
    | (LFalse,_) -> LFalse
    | (_,LFalse) -> LFalse
*)
    | (JCAor l1 , JCAor l2) -> JCAor(l1@l2)
    | (JCAor l1 , _ ) -> JCAor(l1@[a2])
    | (_ , JCAor l2) -> JCAor(a1::l2)
    | _ -> JCAor [a1;a2]


let make_rel_bin_op loc op t1 e1 t2 e2 =
  match op with
    | Bgt | Blt | Bge | Ble ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  JCAapp(rel_bin_op t op,[term_coerce t1 t e1; term_coerce t2 t e2])
	else
	  typing_error loc "numeric types expected"
    | Beq | Bneq ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  JCAapp(rel_bin_op Tunit op,[term_coerce t1 t e1; term_coerce t2 t e2])
	else
	  if comparable_types t1 t2 then 
	    JCAapp(rel_bin_op Tunit op,[e1;e2])
	  else
	    typing_error loc "terms should have the same type"
	(* non propositional operators *)
    | Badd | Bsub | Bmul | Bdiv | Bmod -> assert false
	(* already recognized as connectives *)
    | Bland | Blor -> assert false 
    | Bimplies -> assert false
    | Biff -> assert false


let rec assertion env e =
  let te =
    match e.jc_pexpr_node with
      | JCPEvar id -> 
	  let vi = 
	    try List.assoc id env 
	    with Not_found -> 
	      typing_error e.jc_pexpr_loc "unbound identifier %s" id
	  in 
	  begin
	    match vi.jc_var_info_type with
	      | JCTnative Tboolean ->
		  JCAbool_term { jc_term_loc = e.jc_pexpr_loc;
				 jc_term_node = JCTvar vi }
	      | _ ->
		  typing_error e.jc_pexpr_loc "non boolean expression"
	  end
      | JCPEinstanceof(e1, t) -> 
	  let t1,te1 = term env e1 in
	  let st = find_struct_info e.jc_pexpr_loc t in
	  JCAinstanceof(te1,st) 
      | JCPEcast(e, t) -> assert false
      | JCPEbinary (e1, Bland, e2) -> 
	  make_and (assertion env e1) (assertion env e2)
      | JCPEbinary (e1, Blor, e2) -> 
	  make_or (assertion env e1) (assertion env e2)
      | JCPEbinary (e1, Bimplies, e2) -> 
	  JCAimplies(assertion env e1,assertion env e2)
      | JCPEbinary (e1, Biff, e2) -> 
	  JCAiff(assertion env e1,assertion env e2)
      | JCPEunary (Unot, e2) -> 
	  JCAnot(assertion env e2)
      | JCPEbinary (e1, op, e2) -> 
	  let t1,e1 = term env e1
	  and t2,e2 = term env e2
	  in
	  make_rel_bin_op e.jc_pexpr_loc op t1 e1 t2 e2
      | JCPEunary(op, e2) -> 
	  let t2,e2 = term env e2
	  in
	  JCAapp(rel_unary_op e.jc_pexpr_loc op t2,[e2])
      | JCPEapp (_, _) -> assert false
      | JCPEderef (e, id) -> 
	  let t,te = term env e in
	  let fi = find_field e.jc_pexpr_loc t id in
	  begin
	    match fi.jc_field_info_type with
	      | JCTnative Tboolean ->
		  JCAbool_term { jc_term_loc = e.jc_pexpr_loc;
				 jc_term_node = JCTderef(te,fi) }
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
      | JCPEforall(ty,idl,e1) -> 
	  let ty = type_type ty in
	  (make_forall e.jc_pexpr_loc ty idl env e1).jc_assertion_node
      | JCPEold e -> JCAold(assertion env e)
      | JCPEif(e1,e2,e3) ->
	  let t1,te1 = term env e1 
	  and te2 = assertion env e2
	  and te3 = assertion env e3 
	  in
	  begin
	    match t1 with
	      | JCTnative Tboolean ->
		  JCAif(te1,te2,te3)
	      | _ ->
		  typing_error e1.jc_pexpr_loc 
		    "boolean expression expected"
	  end
	  (* non propositional expressions *)
      | JCPEoffset_max _ | JCPEoffset_min _ ->
	  typing_error e.jc_pexpr_loc "offsets are not propositions"
	  (* non-pure expressions *)
      | JCPEassign_op _ 
      | JCPEassign _ -> 
	  typing_error e.jc_pexpr_loc "assignment not allowed as logic term"


  in { jc_assertion_node = te;
       jc_assertion_loc = e.jc_pexpr_loc }

and make_forall loc ty idl env e : assertion =
  match idl with
    | [] -> assertion env e
    | id::r ->
	let vi = var ty id in
	let f = JCAforall(vi,make_forall loc ty r ((id,vi)::env) e) in
	{jc_assertion_loc = loc ; jc_assertion_node = f }

(* expressions *)

let unary_op t op =
  match t,op with
    | _, Upostfix_inc -> assert false
    | _, Upostfix_dec -> assert false
    | _, Uprefix_inc -> assert false
    | _, Uprefix_dec -> assert false
    | Tinteger, Uplus -> uplus_int
    | Tinteger, Uminus -> uminus_int
    | Treal, Uplus -> uplus_real
    | Treal, Uminus -> uminus_real
    | Tboolean, Unot -> not_
    | Tunit,_ -> assert false
    | _ -> assert false

let incr_op op =
  match op with
    | Upostfix_inc -> Postfix_inc
    | Upostfix_dec -> Postfix_dec
    | Uprefix_inc -> Prefix_inc
    | Uprefix_dec -> Prefix_dec
    | _ -> assert false

let set_assigned v =
  Jc_options.lprintf "Local var %s is assigned@." v.jc_var_info_name;
  v.jc_var_info_assigned <- true

let make_unary_app loc (op : Jc_ast.punary_op) t2 e2 =
  match op with
    | Uprefix_inc | Upostfix_inc | Uprefix_dec | Upostfix_dec ->
	begin
	  match e2.jc_expr_node with
	    | JCEvar v ->
		set_assigned v;
		t2,JCEincr_local(incr_op op,v)
	    | JCEderef(e,f) ->
		t2,JCEincr_heap(incr_op op, f, e)
	    | _ -> typing_error e2.jc_expr_loc "not an lvalue"
	end
    | Unot -> 
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
	in JCTnative t,JCEcall(unary_op t op,[e2])
    | Uplus | Uminus -> 
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
	in JCTnative t,JCEcall(unary_op t op,[e2])

let bin_op t op =
  match t,op with
    | _, Bgt -> gt_int_
    | _, Blt -> lt_int_
    | _, Bge -> ge_int_
    | _, Ble -> le_int_
    | _, Beq -> eq_int_
    | _, Bneq -> neq_int_
    | Tinteger, Badd -> add_int_
    | Treal, Badd -> add_real_
    | _, Bsub -> sub_int_
    | _, Bmul -> mul_int_
    | _, Bdiv -> div_int_
    | _, Bmod -> mod_int_
    | Tboolean, Bland -> and_ 
    | Tboolean, Blor -> or_
	(* not allowed as expression op *)
    | _,Bimplies -> assert false
    | Tunit,_ -> assert false
    | _ -> assert false

let coerce t1 t2 e =
  let tn1,e_int =
    match t1 with
      | JCTrange ri ->
	  let (_,_,to_int_,_) = 
	    Hashtbl.find range_types_table ri.jc_range_info_name 
	  in
	  Tinteger,{ jc_expr_node = JCEcall(to_int_,[e]) ;
	    jc_expr_loc = e.jc_expr_loc }  
      | JCTnative t -> t,e
      | _ -> assert false
  in
  match tn1,t2 with
    | Tinteger,Treal -> 
	{ jc_expr_node = JCEcall(real_of_integer_,[e_int]) ;
	  jc_expr_loc = e.jc_expr_loc }  
    | _ -> e_int


let restrict t1 t2 e =
  match t1,t2 with
    | JCTnative Tinteger, JCTrange ri -> 
	let (_,_,_,of_int) = 
	  Hashtbl.find range_types_table ri.jc_range_info_name 
	in
	{ jc_expr_node = JCEcall(of_int,[e]) ;
	  jc_expr_loc = e.jc_expr_loc }  	
    | _ -> 
	typing_error e.jc_expr_loc "cannot coerce type '%a' to type '%a'"
	  print_type t1 print_type t2
	

let make_bin_app loc op t1 e1 t2 e2 =
  match op with
    | Bgt | Blt | Bge | Ble | Beq | Bneq ->
	if is_numeric t1 && is_numeric t2 then
	  let t = lub_numeric_types t1 t2 in
	  JCTnative Tboolean,
	  JCEcall(bin_op Tboolean op,[coerce t1 t e1; coerce t2 t e2])
	else
	  typing_error loc "numeric types expected"
    | Badd | Bsub ->
	begin
	  match t1 with
	    | JCTpointer(st,_,_) ->
		if is_integer t2 then
		  t1, JCEcall(shift_,[e1;coerce t2 Tinteger e2])
		else
		  typing_error loc "integer type expected"
	    | _ ->
		if is_numeric t1 && is_numeric t2 then
		  let t = lub_numeric_types t1 t2 in
		  JCTnative t,
		  JCEcall(bin_op t op,[coerce t1 t e1; coerce t2 t e2])
		else
		  typing_error loc "numeric types expected"
	end
    | Bmul | Bdiv | Bmod ->
	let t=
	  match (t1,t2) with
	    | JCTnative t1, JCTnative t2 ->
		begin
		  match (t1,t2) with
		    | Tinteger,Tinteger -> Tinteger
		    | Treal,Treal -> Treal
		    | _ -> assert false (* TODO *)
		end
	    | _ ->
		typing_error loc "numeric types expected"
	in JCTnative t,JCEcall(bin_op t op,[e1;e2])
    | Bland | Blor -> 
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
	in JCTnative t,JCEcall(bin_op t op,[e1;e2])

	(* not allowed as expression op *)
    | Bimplies | Biff -> assert false



let rec expr env e =
  let t,te =
    match e.jc_pexpr_node with
      | JCPEvar id ->
	  begin
	    try
	      let vi = List.assoc id env
	      in vi.jc_var_info_type,JCEvar vi
	    with Not_found -> 
	      typing_error e.jc_pexpr_loc "unbound identifier %s" id
	  end
      | JCPEinstanceof(e1, t) -> 
	  let t1,te1 = expr env e1 in
	  let st = find_struct_info e.jc_pexpr_loc t in
	  JCTnative Tboolean, JCEinstanceof(te1,st)
      | JCPEcast(e1, t) -> 
	  let t1,te1 = expr env e1 in
	  let st = find_struct_info e.jc_pexpr_loc t in
	  begin
	    match t1 with
	      | JCTpointer(st1,a,b) ->
		  if substruct st st1 then
		    JCTpointer(st,a,b), JCEcast(te1,st)
		  else
		    typing_error e.jc_pexpr_loc "invalid cast"
	      | _ ->
		  typing_error e.jc_pexpr_loc "only structures can be cast"
	  end
      | JCPEbinary (e1, op, e2) -> 
	  let t1,e1 = expr env e1
	  and t2,e2 = expr env e2
	  in
	  make_bin_app e.jc_pexpr_loc op t1 e1 t2 e2
      | JCPEunary (op, e2) -> 
	  let t2,e2 = expr env e2
	  in
	  make_unary_app e.jc_pexpr_loc op t2 e2
      | JCPEassign (e1, e2) -> 
	  begin
	    let t1,te1 = expr env e1
	    and t2,te2 = expr env e2
	    in
	    let te2 =	      
	      if subtype t2 t1 then te2 else
		try
		  restrict t2 t1 te2
		with
		    Invalid_argument _ ->
		      typing_error e2.jc_pexpr_loc 
			"type '%a' expected"
			print_type t1
	    in
	    match te1.jc_expr_node with
	      | JCEvar v ->
		  set_assigned v;
		  t1,JCEassign_local(v,te2)
	      | JCEderef(e,f) ->
		  t1,JCEassign_heap(e, f, te2)
	      | _ -> typing_error e1.jc_pexpr_loc "not an lvalue"
	  end
      | JCPEassign_op (e1, op, e2) -> 
	  begin
	    let t1,te1 = expr env e1
	    and t2,te2 = expr env e2
	    in
	    if subtype t2 t1 then
	      match t1 with
		| JCTnative t ->
		    begin
		      match te1.jc_expr_node with
			| JCEvar v ->
			    set_assigned v;
			    t1,JCEassign_op_local(v, bin_op t op, te2)
			| JCEderef(e,f) ->
			    t1,JCEassign_op_heap(e, f, bin_op t op, te2)
			| _ -> typing_error e1.jc_pexpr_loc "not an lvalue"
		    end
		| _ ->
		    typing_error e.jc_pexpr_loc "incompatible type"
	    else
	      typing_error e.jc_pexpr_loc "incompatible types"
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
			       let t,te = expr env e in
			       if subtype t ty then te
			       else
				 typing_error e.jc_pexpr_loc 
				   "type %a expected" 
				   print_type ty) 
			    fi.jc_fun_info_parameters l
			with  Invalid_argument _ ->
			  typing_error e.jc_pexpr_loc 
			    "wrong number of arguments for %s" id
		      in
		      fi.jc_fun_info_return_type,JCEcall(fi, tl)
		    with Not_found ->
		      typing_error e.jc_pexpr_loc 
			"unbound function identifier %s" id
		  end
	      | _ -> 
		  typing_error e.jc_pexpr_loc "unsupported function call"
	  end
      | JCPEderef (e1, f) -> 
	  let t,te = expr env e1 in
	  let fi = find_field e.jc_pexpr_loc t f in
	  fi.jc_field_info_type,JCEderef(te,fi)
(*
      | JCPEshift (_, _) -> assert false
*)
      | JCPEconst c -> let t,tc = const c in t,JCEconst tc
      | JCPEif(e1,e2,e3) ->
	  let t1,te1 = expr env e1 
	  and t2,te2 = expr env e2
	  and t3,te3 = expr env e3 
	  in
	  begin
	    match t1 with
	      | JCTnative Tboolean ->
		  let t =
		    if subtype t2 t3 then t3 else
		      if subtype t3 t2 then t2 else
			typing_error e.jc_pexpr_loc 
			  "imcompatible result types"
		  in
		  t, JCEif(te1,te2,te3)
	      | _ ->
		  typing_error e1.jc_pexpr_loc 
		    "boolean expression expected"
	  end
	  (* logic expressions, not allowed as program expressions *)
      | JCPEforall _ 
      | JCPEold _ 
      | JCPEoffset_max _ 
      | JCPEoffset_min _ ->
	  typing_error e.jc_pexpr_loc "not allowed in this context"

  in t,{ jc_expr_node = te; jc_expr_loc = e.jc_pexpr_loc }

  

let loop_annot env i v =
  let ti = assertion env i
  and ttv,tv = term env v
  in
  (* TODO: check variant is integer, or other order ? *) 
  { jc_loop_invariant = ti ;
    jc_loop_variant = tv;
  }


let make_block (l:statement list) : statement_node =
  match l with
    | [s] -> s.jc_statement_node
    | _ -> JCSblock l

let rec statement env s =
  let ts =
    match s.jc_pstatement_node with
      | JCPSskip -> JCSblock []
      | JCPSthrow (id, e) -> 
	  let ei =
	    try Hashtbl.find exceptions_table id.jc_identifier_name 
	    with Not_found ->
	      typing_error id.jc_identifier_loc 
		"undeclared exception %s" id.jc_identifier_name
	  in
	  let t,te = expr env e in
	  if subtype t ei.jc_exception_info_type then 
	    JCSthrow(ei,te)
	  else
	    typing_error e.jc_pexpr_loc "%a type expected" 
	      print_type ei.jc_exception_info_type
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
	  JCStry(ts,catches,statement env finally)
      | JCPSgoto _ -> assert false
      | JCPScontinue _ -> assert false
      | JCPSbreak l -> 
	  JCSbreak l (* TODO: check l exists, check enclosing loop exists, *)
      | JCPSreturn e -> 
	  let t,te = expr env e in 
	  let vi = List.assoc "\\result" env in
	  if subtype t vi.jc_var_info_type then
	    JCSreturn te
	  else
	    begin
	      try
		JCSreturn (restrict t vi.jc_var_info_type te)
	      with
		  Invalid_argument _ ->
		    typing_error s.jc_pstatement_loc "type '%a' expected"
		      print_type vi.jc_var_info_type
	    end
      | JCPSwhile(c,i,v,s) -> 
	  let t,tc = expr env c in
	  if subtype t (JCTnative Tboolean) then
	    let ts = statement env s
	    and lo = loop_annot env i v
	    in
	    JCSwhile(tc,lo,ts)
	  else 
	    typing_error s.jc_pstatement_loc "boolean expected"
	  
      | JCPSif (c, s1, s2) -> 
	  let t,tc = expr env c in
	  if subtype t (JCTnative Tboolean) then
	    let ts1 = statement env s1
	    and ts2 = statement env s2
	    in
	    JCSif(tc,ts1,ts2)
	  else 
	    typing_error s.jc_pstatement_loc "boolean expected"
      | JCPSdecl (ty, id, e) -> assert false
      | JCPSassert _ -> assert false
      | JCPSexpr e -> 
	  let t,te = expr env e in 
	  JCSexpr (te)
      | JCPSblock l -> make_block (statement_list env l)
      | JCPSpack e ->
	  let t,te = expr env e in 
	  begin match t with
	    | JCTpointer(st,_,_) ->
		JCSpack(st,te)
	    | _ ->
		typing_error s.jc_pstatement_loc 
		  "only structures can be packed"
	  end
      | JCPSunpack e ->
	  let t,te = expr env e in 
	  begin match t with
	    | JCTpointer(st,_,_) ->
		JCSunpack(st,te)
	    | _ ->
		typing_error s.jc_pstatement_loc 
		  "only structures can be unpacked"
	  end

  in { jc_statement_node = ts;
       jc_statement_loc = s.jc_pstatement_loc }

and statement_list env l : statement list =
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
		       let t,te = expr env e in
		       if subtype t ty then te
		       else
			 try
			   restrict t ty te
			 with
			     Invalid_argument _ ->
			       typing_error s.jc_pstatement_loc 
				 "type '%a' expected"
				   print_type ty)
		    e
		in
		let tr = statement_list ((id,vi)::env) r in
		let tr = { jc_statement_loc = s.jc_pstatement_loc;
			   jc_statement_node = make_block tr } 
		in
		[ { jc_statement_loc = s.jc_pstatement_loc;
		    jc_statement_node = JCSdecl(vi, te, tr); } ]
	    | _ -> 
		let s = statement env s in
		let r = statement_list env r in
		s :: r
  

let const_zero = 
  { jc_term_loc = Loc.dummy_position;
    jc_term_node = JCTconst (JCCinteger "0");
  }


let rec location_set env e =
  match e.jc_pexpr_node with
    | JCPEvar id ->
	begin
	  try
	    let vi = List.assoc id env in 
	    match vi.jc_var_info_type with
	      | JCTpointer(st,_,_) ->
		  vi.jc_var_info_type,JCLSvar(vi)
	      | _ -> assert false
	  with Not_found -> 
	    typing_error e.jc_pexpr_loc "unbound identifier %s" id
	end
    | JCPEbinary(e,Badd,i) ->
	let tye,te = location_set env e in
	let tyi,ti = term env i in
	begin
	  match tye,tyi with 
	    | JCTpointer(st,_,_), JCTnative Tinteger ->
		tye,JCLSrange(te,ti,ti)
	    | JCTpointer _, _ -> 
		typing_error i.jc_pexpr_loc "integer expected, got %a" print_type tyi
	    | _ -> 
		typing_error e.jc_pexpr_loc "pointer expected"
	end
    | JCPEbinary _ -> assert false
    | JCPEderef (ls, f) -> 
	let t,tls = location_set env ls in
	let fi = find_field e.jc_pexpr_loc t f in
	fi.jc_field_info_type, JCLSderef(tls,fi)	  

    | JCPEif (_, _, _)
    | JCPEoffset_min _
    | JCPEoffset_max _
    | JCPEold _
    | JCPEforall (_, _, _)
    | JCPEcast (_, _)
    | JCPEinstanceof (_, _)
    | JCPEunary (_, _)
    | JCPEassign_op (_, _, _)
    | JCPEassign (_, _)
    | JCPEapp (_, _)
    | JCPEconst _ -> assert false

let location env e =
  match e.jc_pexpr_node with
    | JCPEvar id ->
	begin
	  try
	    let vi = List.assoc id env in
	    vi.jc_var_info_type,JCLvar vi
	  with Not_found -> 
	    typing_error e.jc_pexpr_loc "unbound identifier %s" id
	  end
    | JCPEderef(ls,f) ->
	let t,tls = location_set env ls in
	let fi = find_field e.jc_pexpr_loc t f in
	fi.jc_field_info_type, JCLderef(tls,fi)	  
(*
    | JCPEshift (_, _)  -> assert false (* TODO *)
*)
    | JCPEif _ 
    | JCPEcast _
    | JCPEinstanceof _
    | JCPEold _ 
    | JCPEoffset_max _ 
    | JCPEoffset_min _
    | JCPEforall (_, _, _)
    | JCPEunary _
    | JCPEbinary (_, _, _)
    | JCPEassign_op (_, _, _)
    | JCPEassign (_, _)
    | JCPEapp (_, _)
    | JCPEconst _ -> 
	typing_error e.jc_pexpr_loc "invalid memory location"

let clause env vi_result c acc =
  match c with
    | JCPCrequires(e) ->
	{ acc with 
	    jc_fun_requires = assertion env e }
    | JCPCbehavior(id,throws,assumes,assigns,ensures) ->
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
	let assigns = 
	  Option_misc.map (List.map (fun a -> snd (location env a))) assigns in
	let b = {
	  jc_behavior_throws = throws;
	  jc_behavior_assumes = assumes;
	  jc_behavior_assigns = assigns;
	  jc_behavior_ensures = assertion env_result ensures }
	in
	{ acc with jc_fun_behavior = (id,b)::acc.jc_fun_behavior }
	  

  
let param (t,id) =
  let ty = type_type t in
  let vi = var ty id in 
  (id,vi)

let assertion_true =
  { jc_assertion_node = JCAtrue;
    jc_assertion_loc = Loc.dummy_position }

let field_tag_counter = ref 0

let field root (t,id) =
  let ty = type_type t in
  incr field_tag_counter;
  let fi = {
    jc_field_info_tag = !field_tag_counter;
    jc_field_info_name = id;
    jc_field_info_type = ty;
    jc_field_info_root = root;
  }
  in (id,fi)


let axioms_table = Hashtbl.create 17

let decl d =
  match d.jc_pdecl_node with
    | JCPDfun(ty,id,pl,specs,body) -> 
	let param_env = List.map param pl in
	let ty = type_type ty in
	let fi = make_fun_info id ty in
	fi.jc_fun_info_parameters <- List.map snd param_env;
	let vi = var ty "\\result" in
	vi.jc_var_info_final_name <- "result";
	let s = List.fold_right 
		  (clause param_env vi) specs 
		  { jc_fun_requires = assertion_true;
		    jc_fun_behavior = [] }
	in
	let b = statement_list (("\\result",vi)::param_env) body in
	Hashtbl.add functions_env id fi;
	Hashtbl.add functions_table fi.jc_fun_info_tag (fi,s,b)
    | JCPDrangetype(id,min,max) ->
	let ri =
	  { jc_range_info_name = id;
	    jc_range_info_min = min;
	    jc_range_info_max = max;
	  }
	in
	let to_int = make_term_op ("int_of_"^id) integer_type in
	let to_int_ = make_fun_info ("int_of_"^id) integer_type in
	let of_int = make_fun_info (id^"_of_int") (JCTrange ri) in
	Hashtbl.add range_types_table id (ri,to_int,to_int_,of_int)
    | JCPDstructtype(id,parent,fields,inv) ->
	let root,par = 
	  match parent with
	    | None -> 
		(id,None)
	    | Some p ->
		let st = find_struct_info d.jc_pdecl_loc p in
		(st.jc_struct_info_root,Some st)
	in
	let env = List.map (field root) fields in
	let struct_info =
	  { jc_struct_info_name = id;
	    jc_struct_info_fields = env;
	    jc_struct_info_parent = par;
	    jc_struct_info_root = root;
	  }
	in
	let invariants =
	  List.fold_left
	    (fun acc (id,x,e) ->	
	       let vi = var (JCTpointer(struct_info,zero,zero)) x in
	       let p = assertion [(x,vi)] e in
	       let pi = make_rel id in
	       pi.jc_logic_info_parameters <- [vi];
	       Hashtbl.add logic_functions_table 
		 pi.jc_logic_info_tag (pi,JCAssertion p);
	       (pi,p) :: acc)
	    []
	    inv
	in
	Hashtbl.add structs_table id (struct_info,invariants)
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

    | JCPDexception(id,t) ->
	let tt = type_type t in
	Hashtbl.add exceptions_table id (exception_info id tt)

(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
