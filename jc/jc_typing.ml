(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2006                                               *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
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
open Jc_ast

let unit_type = JCTlogic "unit"
let boolean_type = JCTlogic "bool"
let integer_type = JCTlogic "integer"
let real_type = JCTlogic "real"

let same_type t1 t2 =
  match t1,t2 with
    | JCTnative t1, JCTnative t2 -> t1=t2
    | JCTlogic s1, JCTlogic s2 -> s1=s2
    | (JCTpointer(s1) | JCTvalidpointer(s1,_,_)),
	(JCTpointer(s2) | JCTvalidpointer(s2,_,_)) -> s1=s2
    | _ -> false
	
open Format

let string_of_native t =
  match t with
    | `Tunit -> "unit"
    | `Tinteger -> "integer"
    | `Treal -> "real"
    | `Tboolean -> "boolean"


let print_type fmt t =
  match t with
    | JCTnative n -> fprintf fmt "%s" (string_of_native n)
    | JCTlogic s
    | JCTpointer s 
    | JCTvalidpointer (s,_,_) -> fprintf fmt "%s" s


let functions_table = Hashtbl.create 97
let functions_env = Hashtbl.create 97

let structs_table = Hashtbl.create 97

exception Typing_error of Loc.position * string

let typing_error l = 
  Format.kfprintf 
    (fun fmt -> raise (Typing_error(l, flush_str_formatter()))) 
    str_formatter


let find_field loc ty f =
  match ty with
    | JCTpointer id
    | JCTvalidpointer(id,_,_) ->
	begin
	  try
	    let st = Hashtbl.find structs_table id in
	    try
	      List.assoc f st
	    with Not_found ->
	      typing_error loc "no field %s in structure %s" f id
	  with Not_found ->
	    typing_error loc "undeclared structure %s" id
	end
    | JCTnative _ 
    | JCTlogic _ ->
	typing_error loc "not a structure type"

let find_fun_info id = Hashtbl.find functions_env id
    
(* types *)

let type_type t =
  match t with
    | JCPTnative n -> JCTnative n
    | JCPTvalidpointer (id, a, b) -> 
	JCTvalidpointer(id, a, b)
    | JCPTidentifier id -> 
	(* TODO *)
	JCTlogic id

(* constants *)

let const c =
  match c with
    | JCCinteger _ -> integer_type,c
    | JCCreal _ -> real_type,c
    | JCCbool _ -> boolean_type,c
    | JCCnull -> assert false

(* terms *)

let make_term_op name ty =
  { jc_logic_info_name = name;
    jc_logic_info_result_type = Some ty;
  }

let eq_int_bool = make_term_op "eq_int_bool" boolean_type
let neq_int_bool = make_term_op "neq_int_bool" boolean_type
let neq_pointer_bool = make_term_op "neq_pointer_bool" boolean_type
let add_int = make_term_op "add_int" integer_type
let sub_int = make_term_op "sub_int" integer_type

let logic_bin_op loc op t1 e1 t2 e2 =
  let t,op =
    match op with
      | `Bge -> assert false (* TODO *)
      | `Ble -> assert false (* TODO *)
      | `Beq -> boolean_type,eq_int_bool
      | `Bneq ->
	  if t1=t2
	  then
	    begin
	      match t1 with
		| JCTlogic "integer" -> boolean_type,neq_int_bool
		| JCTpointer _ -> boolean_type,neq_pointer_bool
		| _ -> assert false (* TODO *)
	    end
	  else
	    typing_error loc "terms should have the same type"
      | `Badd -> integer_type,add_int
      | `Bsub -> integer_type,sub_int
      | `Bland -> assert false (* TODO *)
      | `Bimplies -> assert false
  in
  t,JCTapp(op,[e1;e2])

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
      | JCPEbinary (e1, op, e2) -> 
	  let t1,e1 = term env e1
	  and t2,e2 = term env e2
	  in
	  logic_bin_op e.jc_pexpr_loc op t1 e1 t2 e2
      | JCPEapp (_, _) -> assert false
      | JCPEderef (e1, f) -> 
	  let t,te = term env e1 in
	  let fi = find_field e.jc_pexpr_loc t f in
	  fi.jc_field_info_type, JCTderef(te,fi)	  
      | JCPEshift (_, _) -> assert false
      | JCPEconst c -> 
	  let t,c = const c in t,JCTconst c
      | JCPEold e -> 
	  let t,e = term env e in t,JCTold(e)
	  (* non-pure expressions *)
      | JCPEassign_op _ 
      | JCPEassign _ -> 
	  typing_error e.jc_pexpr_loc "assignment not allowed as logic term"
	  (* propositional (non-boolean) expressions *)
      | JCPEforall _ -> 
	  typing_error e.jc_pexpr_loc "quantification not allowed as logic term"

  in t,{ jc_term_node = te;
	 jc_term_loc = e.jc_pexpr_loc }

  
let make_rel name =
  { jc_logic_info_name = name;
    jc_logic_info_result_type = None }

let ge_int = make_rel "ge_int"
let le_int = make_rel "le_int"
let eq_int = make_rel "eq_int"
let neq_int = make_rel "neq"
let neq_pointer = make_rel "neq"
    
let rel_bin_op loc op t1 t2 =
  match op with
    | `Bge -> ge_int
    | `Ble -> le_int
    | `Beq -> eq_int
    | `Bneq -> 
	if t1=t2 then 
	  begin
	    match t1 with
	      | JCTlogic "integer" -> neq_int
	      | JCTlogic _ -> assert false
	      | JCTvalidpointer (_, _, _) 
	      | JCTpointer _ -> neq_pointer
	      | JCTnative _ -> assert false
	  end
	else
	  typing_error loc "terms should have the same type"
	(* non propositional operators *)
    | `Badd -> assert false
    | `Bsub -> assert false
	(* already recognized as connectives *)
    | `Bland -> assert false 
    | `Bimplies -> assert false

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

let rec assertion env e =
  let te =
    match e.jc_pexpr_node with
      | JCPEvar id -> assert false
      | JCPEbinary (e1, `Bland, e2) -> 
	  make_and (assertion env e1) (assertion env e2)
      | JCPEbinary (e1, `Bimplies, e2) -> 
	  JCAimplies(assertion env e1,assertion env e2)
      | JCPEbinary (e1, op, e2) -> 
	  let t1,e1 = term env e1
	  and t2,e2 = term env e2
	  in
	  JCAapp(rel_bin_op e.jc_pexpr_loc op t1 t2,[e1;e2])
      | JCPEapp (_, _) -> assert false
      | JCPEderef (_, _) -> assert false
      | JCPEshift (_, _) -> assert false
      | JCPEconst _ -> assert false
      | JCPEforall(ty,id,e) -> 
	  let ty = type_type ty in
	  let vi = {
	    jc_var_info_name = id;
	    jc_var_info_final_name = id;
	    jc_var_info_type = ty;
	    jc_var_info_assigned = false;
	  }
	  in JCAforall(vi,assertion ((id,vi)::env) e)
      | JCPEold e -> JCAold(assertion env e)
	  (* non-pure expressions *)
      | JCPEassign_op _ 
      | JCPEassign _ -> 
	  typing_error e.jc_pexpr_loc "assignment not allowed as logic term"


  in { jc_assertion_node = te;
       jc_assertion_loc = e.jc_pexpr_loc }

(* expressions *)

let fun_info_counter = ref 0

let make_fun_info name ty =
  incr fun_info_counter;
  { jc_fun_info_tag = !fun_info_counter;
    jc_fun_info_name = name;
    jc_fun_info_parameters = [];
    jc_fun_info_return_type = ty;
    jc_fun_info_calls = [];
    jc_fun_info_logic_apps = [];
    jc_fun_info_effects = { jc_writes_fields = FieldSet.empty } 
 }

let ge_int = make_fun_info "ge_int_" boolean_type
let le_int = make_fun_info "le_int_" boolean_type 
let eq_int = make_fun_info "eq_int_" integer_type
let neq_int = make_fun_info "neq_int_" integer_type
let add_int = make_fun_info "add_int" integer_type
let sub_int = make_fun_info "sub_int" integer_type
    
let bin_op op =
  match op with
    | `Bge -> ge_int
    | `Ble -> le_int
    | `Beq -> eq_int
    | `Bneq -> neq_int
    | `Badd -> add_int
    | `Bsub -> sub_int
    | `Bland -> assert false (* TODO *)
	(* not allowed as expression op *)
    | `Bimplies -> assert false

let make_bin_app loc op t1 e1 t2 e2 =
  match op with
    | `Bge | `Ble | `Beq | `Bneq ->
	let t=
	  match (t1,t2) with
	    | JCTnative t1, JCTnative t2 ->
		begin
		  match (t1,t2) with
		    | `Tinteger,`Tinteger -> ()
		    | _ -> assert false (* TODO *)
		end
	    | _ ->
		typing_error loc "numeric types expected"
	in JCTnative `Tboolean,JCEcall(bin_op op,[e1;e2])

    | `Badd | `Bsub ->
	let t=
	  match (t1,t2) with
	    | JCTnative t1, JCTnative t2 ->
		begin
		  match (t1,t2) with
		    | `Tinteger,`Tinteger -> `Tinteger
		    | _ -> assert false (* TODO *)
		end
	    | _ ->
		typing_error loc "numeric types expected"
	in JCTnative t,JCEcall(bin_op op,[e1;e2])
    | `Bland -> assert false (* TODO *)
	(* not allowed as expression op *)
    | `Bimplies -> assert false

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
      | JCPEbinary (e1, op, e2) -> 
	  let t1,e1 = expr env e1
	  and t2,e2 = expr env e2
	  in
	  make_bin_app e.jc_pexpr_loc op t1 e1 t2 e2
      | JCPEassign (e1, e2) -> 
	  begin
	    let t1,te1 = expr env e1
	    and t2,te2 = expr env e2
	    in
	    if same_type t1 t2 then
	      match te1.jc_expr_node with
		| JCEvar v ->
		    t1,JCEassign_local(v,te2)
		| JCEderef(e,f) ->
		    t1,JCEassign_heap(e, f, te2)
		| _ -> typing_error e1.jc_pexpr_loc "not an lvalue"
	    else
	      typing_error e.jc_pexpr_loc "same type expected"
	  end
      | JCPEassign_op (e1, op, e2) -> 
	  begin
	    let t1,te1 = expr env e1
	    and t2,te2 = expr env e2
	    in
	    if same_type t1 t2 then
	    match te1.jc_expr_node with
	      | JCEvar v ->
		  t1,JCEassign_op_local(v, bin_op op, te2)
	      | JCEderef(e,f) ->
		  t1,JCEassign_op_heap(e, f, bin_op op, te2)
	      | _ -> typing_error e1.jc_pexpr_loc "not an lvalue"
	    else
	      typing_error e.jc_pexpr_loc "same type expected"
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
			       if same_type ty t then te
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
      | JCPEshift (_, _) -> assert false
      | JCPEconst c -> let t,tc = const c in t,JCEconst tc
	  (* logic expressions, not allowed as program expressions *)
      | JCPEforall _ 
      | JCPEold _ -> 
	  typing_error e.jc_pexpr_loc "not allowed in this context"

  in t,{ jc_expr_node = te; jc_expr_loc = e.jc_pexpr_loc }

  

let rec statement env s =
  let ts =
    match s.jc_pstatement_node with
      | JCPSskip -> JCSskip
      | JCPSthrow (_, _) -> assert false
      | JCPStry (_, _, _) -> assert false
      | JCPSgoto _ -> assert false
      | JCPScontinue _ -> assert false
      | JCPSbreak _ -> assert false
      | JCPSreturn e -> 
	  let t,te = expr env e in 
	  (* TODO *)
	  JCSreturn te
      | JCPSwhile (_, _) -> assert false
      | JCPSif (c, s1, s2) -> 
	  let t,tc = expr env c in
	  if same_type t (JCTnative `Tboolean) then
	    JCSif(tc,statement env s1,statement env s2)
	  else 
	    typing_error s.jc_pstatement_loc "boolean expected"
      | JCPSdecl (_, _, _) -> assert false
      | JCPSassert _ -> assert false
      | JCPSexpr e -> 
	  let t,te = expr env e in 
	  JCSexpr (te)
      | JCPSblock l -> JCSblock (List.map (statement env) l)


  in { jc_statement_node = ts;
       jc_statement_loc = s.jc_pstatement_loc }

let clause env c acc =
  match c with
    | JCPCrequires(e) ->
	{ acc with 
	    jc_fun_requires = assertion env e }
    | JCPCbehavior(id,assigns,ensures) ->
	let assigns =
	  match assigns with
	    | None -> None
	    | Some a -> 
		let t,e = term env a in
		Some(e)
	in
	let b = {
	  jc_behavior_assigns = assigns;
	  jc_behavior_ensures = assertion env ensures }
	in
	{ acc with jc_fun_behavior = (id,b)::acc.jc_fun_behavior }
	  

  
let param (t,id) =
  let ty = type_type t in
  let vi = {
    jc_var_info_name = id;
    jc_var_info_final_name = id;
    jc_var_info_type = ty;
    jc_var_info_assigned = false;
  }
  in (id,vi)

let assertion_true =
  { jc_assertion_node = JCAtrue;
    jc_assertion_loc = Loc.dummy_position }

let field (t,id) =
  let ty = type_type t in
  let fi = {
    jc_field_info_tag = 0;
    jc_field_info_name = id;
    jc_field_info_type = ty;
  }
  in (id,fi)

let decl d =
  match d.jc_pdecl_node with
    | JCPDfun(ty,id,pl,specs,body) -> 
	let param_env = List.map param pl in
	let ty = type_type ty in
	let fi = make_fun_info id ty in
	fi.jc_fun_info_parameters <- List.map snd param_env;
	let param_env_result =
	  ("\\result",{
	     jc_var_info_name = "\\result";
	     jc_var_info_final_name = "result";
	     jc_var_info_type = ty;
	     jc_var_info_assigned = false;
	  })::param_env
	in
	let s = List.fold_right 
		  (clause param_env_result) specs 
		  { jc_fun_requires = assertion_true;
		    jc_fun_behavior = [] }
	in
	let b = List.map (statement param_env) body in
	Hashtbl.add functions_env id fi;
	Hashtbl.add functions_table fi.jc_fun_info_tag (fi,s,b)
    | JCPDtype(id,fields,inv) ->
	let env = List.map field fields in
(*	let i =
	  match inv with
	    | None -> assertion_true
	    | Some e -> assertion env e
	in
*)	Hashtbl.add structs_table id env



