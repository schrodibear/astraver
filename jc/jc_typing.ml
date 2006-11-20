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
open Jc_pervasives
open Jc_ast
open Format

exception Typing_error of Loc.position * string

let typing_error l = 
  Format.kfprintf 
    (fun fmt -> raise (Typing_error(l, flush_str_formatter()))) 
    str_formatter





let structs_table = Hashtbl.create 97

(*
let same_type t1 t2 =
  match t1,t2 with
    | JCTnative t1, JCTnative t2 -> t1=t2
    | JCTlogic s1, JCTlogic s2 -> s1=s2
    | (JCTpointer(s1) | JCTvalidpointer(s1,_,_)),
	(JCTpointer(s2) | JCTvalidpointer(s2,_,_)) -> s1=s2
    | _ -> false
*)

let rec substruct s1 s2 =
  if s1=s2 then true else
    try
      eprintf "looking for parent of %s:@." s1.jc_struct_info_name; 
      let st = Hashtbl.find structs_table s1.jc_struct_info_name in
      match st.jc_struct_info_parent with 
	| None -> 
	    eprintf "it has no parent@."; 
	    false
	| Some s -> 
	    eprintf "it is %s:@." s.jc_struct_info_name; 
	    substruct s s2
    with Not_found -> assert false

let subtype t1 t2 =
  match t1,t2 with
    | JCTnative t1, JCTnative t2 -> t1=t2
    | JCTlogic s1, JCTlogic s2 -> s1=s2
    | (JCTpointer(s1) | JCTvalidpointer(s1,_,_)),
	(JCTpointer(s2) | JCTvalidpointer(s2,_,_)) -> 
	  substruct s1 s2
    | _ -> false
  

let string_of_native t =
  match t with
    | `Tunit -> "unit"
    | `Tinteger -> "integer"
    | `Treal -> "real"
    | `Tboolean -> "boolean"


let print_type fmt t =
  match t with
    | JCTnative n -> fprintf fmt "%s" (string_of_native n)
    | JCTlogic s -> fprintf fmt "%s" s
    | JCTpointer s 
    | JCTvalidpointer (s,_,_) -> fprintf fmt "%s" s.jc_struct_info_name


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
    | JCTpointer st
    | JCTvalidpointer(st,_,_) -> find_field_struct loc st f
    | JCTnative _ 
    | JCTlogic _ ->
	typing_error loc "not a structure type"

let find_fun_info id = Hashtbl.find functions_env id
    
(* types *)

let type_type t =
  match t.jc_ptype_node with
    | JCPTnative n -> JCTnative n
    | JCPTvalidpointer (id, a, b) -> 
	begin
	  try
	    let st = Hashtbl.find structs_table id in
	    JCTvalidpointer(st, a, b)
	  with Not_found ->
	    typing_error t.jc_ptype_loc "undeclared structure %s" id
	end
    | JCPTidentifier id -> 
	(* TODO *)
	typing_error t.jc_ptype_loc "unknown type %s" id


(* constants *)

let const c =
  match c with
    | JCCinteger _ -> integer_type,c
    | JCCreal _ -> real_type,c
    | JCCboolean _ -> boolean_type,c
    | JCCnull -> assert false

(* terms *)

let num_op op =
  match op with
    | `Badd -> add_int
    | `Bsub -> sub_int
    | `Bmul -> mul_int
    | `Bdiv -> div_int
    | `Bmod -> mod_int
    | _ -> assert false

let eq_op op arg_type  =
  match (op,arg_type) with
    | (`Beq,`Tinteger) -> eq_int_bool
    | (`Bneq,`Tinteger) -> neq_int_bool
    | _ -> assert false

let logic_unary_op loc (op : Jc_ast.punary_op) t e =
  match op with
    | `Unot -> assert false
    | `Uminus | `Uplus -> assert false (* TODO *)
    | `Upostfix_dec | `Upostfix_inc | `Uprefix_dec | `Uprefix_inc ->
	typing_error loc "pre/post incr/decr not allowed as logical term"

let logic_bin_op loc (op : Jc_ast.pbin_op) t1 e1 t2 e2 =
  match op with
    | `Bgt -> assert false (* TODO *)
    | `Blt -> assert false (* TODO *)
    | `Bge -> assert false (* TODO *)
    | `Ble -> assert false (* TODO *)
    | `Beq | `Bneq ->
	let t =
	  match t1,t2 with
	    | JCTnative t1, JCTnative t2 ->
		begin
		  match (t1,t2) with
		    | `Tinteger,`Tinteger -> `Tinteger
		    | _ -> assert false (* TODO *)
		end
	    | _ -> assert false
	in
	JCTnative t,JCTapp(eq_op op t,[e1;e2])
    | `Badd | `Bsub | `Bmul | `Bdiv | `Bmod ->
	let t =
	  match (t1,t2) with
	    | JCTnative t1, JCTnative t2 ->
		begin
		  match (t1,t2) with
		    | `Tinteger,`Tinteger -> `Tinteger
		    | _ -> assert false (* TODO *)
		end
	    | _ ->
		typing_error loc "numeric types expected"
	in JCTnative t,JCTapp(num_op op,[e1;e2])
    | `Bland | `Blor -> assert false (* TODO *)
    | `Bimplies -> assert false
	  
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
	  begin
	    try
	      let st = Hashtbl.find structs_table t in
	      JCTnative `Tboolean, JCTinstanceof(te1,st)
	    with Not_found ->
	      typing_error e.jc_pexpr_loc "undefined structure '%s'" t
	    end
      | JCPEcast(e1, t) -> 
	  let t1,te1 = term env e1 in
	  begin
	    try
	      let st = Hashtbl.find structs_table t in
	      JCTpointer(st), JCTcast(te1,st)
	    with Not_found ->
	      typing_error e.jc_pexpr_loc "undefined structure '%s'" t
	    end
      | JCPEbinary (e1, op, e2) -> 
	  let t1,e1 = term env e1
	  and t2,e2 = term env e2
	  in
	  logic_bin_op e.jc_pexpr_loc op t1 e1 t2 e2
      | JCPEunary(op, e2) -> 
	  let t2,e2 = term env e2
	  in
	  logic_unary_op e.jc_pexpr_loc op t2 e2
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
      | JCPEif(e1,e2,e3) ->
	  let t1,te1 = term env e1 
	  and t2,te2 = term env e2
	  and t3,te3 = term env e3 
	  in
	  begin
	    match t1 with
	      | JCTnative `Tboolean ->
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
    | `Unot -> assert false
    | `Uminus | `Uplus -> 
	typing_error loc "not a proposition"
    | `Upostfix_dec | `Upostfix_inc | `Uprefix_dec | `Uprefix_inc ->
	typing_error loc "pre/post incr/decr not allowed as logical term"


let rel_bin_op loc op t1 t2 =
  match op with
    | `Bgt -> gt_int
    | `Blt -> lt_int
    | `Bge -> ge_int
    | `Ble -> le_int
    | `Beq | `Bneq -> 
	let op = match op with
	  | `Beq -> eq
	  | `Bneq -> neq
	  | _ -> assert false
	in
	if t1=t2 then 
	  begin
	    match t1 with
	      | JCTnative _ -> op
	      | JCTlogic _ -> assert false
	      | JCTvalidpointer (_, _, _) 
	      | JCTpointer _ -> op
	  end
	else
	  typing_error loc "terms should have the same type"
	(* non propositional operators *)
    | `Badd | `Bsub | `Bmul | `Bdiv | `Bmod -> assert false
	(* already recognized as connectives *)
    | `Bland | `Blor -> assert false 
    | `Bimplies -> assert false
    | `Binstanceof -> assert false


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
      | JCPEinstanceof(e1, t) -> 
	  let t1,te1 = term env e1 in
	  begin
	    try
	      let st = Hashtbl.find structs_table t in
	      JCAinstanceof(te1,st)
	    with Not_found ->
	      typing_error e.jc_pexpr_loc "undefined structure '%s'" t
	    end
      | JCPEcast(e, t) -> assert false
      | JCPEbinary (e1, `Bland, e2) -> 
	  make_and (assertion env e1) (assertion env e2)
      | JCPEbinary (e1, `Bimplies, e2) -> 
	  JCAimplies(assertion env e1,assertion env e2)
      | JCPEunary (`Unot, e2) -> 
	  JCAnot(assertion env e2)
      | JCPEbinary (e1, op, e2) -> 
	  let t1,e1 = term env e1
	  and t2,e2 = term env e2
	  in
	  JCAapp(rel_bin_op e.jc_pexpr_loc op t1 t2,[e1;e2])
      | JCPEunary(op, e2) -> 
	  let t2,e2 = term env e2
	  in
	  JCAapp(rel_unary_op e.jc_pexpr_loc op t2,[e2])
      | JCPEapp (_, _) -> assert false
      | JCPEderef (_, _) -> assert false
      | JCPEshift (_, _) -> assert false
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
	  (make_forall e.jc_pexpr_loc ty idl [] e1).jc_assertion_node
      | JCPEold e -> JCAold(assertion env e)
      | JCPEif(e1,e2,e3) ->
	  let t1,te1 = term env e1 
	  and te2 = assertion env e2
	  and te3 = assertion env e3 
	  in
	  begin
	    match t1 with
	      | JCTnative `Tboolean ->
		  JCAif(te1,te2,te3)
	      | _ ->
		  typing_error e1.jc_pexpr_loc 
		    "boolean expression expected"
	  end
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
	let vi = {
	  jc_var_info_name = id;
	  jc_var_info_final_name = id;
	  jc_var_info_type = ty;
	  jc_var_info_assigned = false;
	}
	in
	let f = JCAforall(vi,make_forall loc ty r ((id,vi)::env) e) in
	{jc_assertion_loc = loc ; jc_assertion_node = f }

(* expressions *)

let bin_op t op =
  match t,op with
    | _, `Bgt -> gt_int_
    | _, `Blt -> lt_int_
    | _, `Bge -> ge_int_
    | _, `Ble -> le_int_
    | _, `Beq -> eq_int_
    | _, `Bneq -> neq_int_
    | `Tinteger, `Badd -> add_int_
    | `Treal, `Badd -> add_real_
    | _, `Bsub -> sub_int_
    | _, `Bmul -> mul_int_
    | _, `Bdiv -> div_int_
    | _, `Bmod -> mod_int_
    | `Tboolean, `Bland -> and_ 
    | `Tboolean, `Blor -> or_
	(* not allowed as expression op *)
    | _,`Bimplies -> assert false
    | _,`Binstanceof -> assert false
    | `Tunit,_ -> assert false

let make_bin_app loc op t1 e1 t2 e2 =
  match op with
    | `Bgt | `Blt | `Bge | `Ble | `Beq | `Bneq ->
	begin
	  match (t1,t2) with
	    | JCTnative t1, JCTnative t2 ->
		begin
		  match (t1,t2) with
		    | `Tinteger,`Tinteger -> ()
		    | _ -> assert false (* TODO *)
		end
	    | _ ->
		typing_error loc "numeric types expected"
	end;
	JCTnative `Tboolean,JCEcall(bin_op `Tboolean op,[e1;e2])
    | `Badd | `Bsub | `Bmul | `Bdiv | `Bmod ->
	let t=
	  match (t1,t2) with
	    | JCTnative t1, JCTnative t2 ->
		begin
		  match (t1,t2) with
		    | `Tinteger,`Tinteger -> `Tinteger
		    | `Treal,`Treal -> `Treal
		    | _ -> assert false (* TODO *)
		end
	    | _ ->
		typing_error loc "numeric types expected"
	in JCTnative t,JCEcall(bin_op t op,[e1;e2])
    | `Bland | `Blor -> 
	let t=
	  match (t1,t2) with
	    | JCTnative t1, JCTnative t2 ->
		begin
		  match (t1,t2) with
		    | `Tboolean,`Tboolean -> `Tboolean
		    | _ -> assert false (* TODO *)
		end
	    | _ ->
		typing_error loc "booleans expected"
	in JCTnative t,JCEcall(bin_op t op,[e1;e2])

	(* not allowed as expression op *)
    | `Bimplies -> assert false
    | `Binstanceof -> assert false


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
	  begin
	    try
	      let st = Hashtbl.find structs_table t in
	      JCTnative `Tboolean, JCEinstanceof(te1,st)
	    with Not_found ->
	      typing_error e.jc_pexpr_loc "undefined structure '%s'" t
	    end
      | JCPEcast(e1, t) -> 
	  let t1,te1 = expr env e1 in
	  begin
	    try
	      let st = Hashtbl.find structs_table t in
	      JCTpointer(st), JCEcast(te1,st)
	    with Not_found ->
	      typing_error e.jc_pexpr_loc "undefined structure '%s'" t
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
	    if subtype t2 t1 then
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
	    if subtype t2 t1 then
	      match t1 with
		| JCTnative t ->
		    begin
		      match te1.jc_expr_node with
			| JCEvar v ->
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
      | JCPEshift (_, _) -> assert false
      | JCPEconst c -> let t,tc = const c in t,JCEconst tc
      | JCPEif(e1,e2,e3) ->
	  let t1,te1 = expr env e1 
	  and t2,te2 = expr env e2
	  and t3,te3 = expr env e3 
	  in
	  begin
	    match t1 with
	      | JCTnative `Tboolean ->
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
      | JCPEold _ -> 
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
      | JCPSwhile(c,i,v,s) -> 
	  let t,tc = expr env c in
	  if subtype t (JCTnative `Tboolean) then
	    let ts = statement env s
	    and lo = loop_annot env i v
	    in
	    JCSwhile(tc,lo,ts)
	  else 
	    typing_error s.jc_pstatement_loc "boolean expected"
	  
      | JCPSif (c, s1, s2) -> 
	  let t,tc = expr env c in
	  if subtype t (JCTnative `Tboolean) then
	    let ts1 = statement env s1
	    and ts2 = statement env s2
	    in
	    JCSif(tc,ts1,ts2)
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

let rec location env e =
  match e.jc_pexpr_node with
    | JCPEvar id ->
	begin
	  try
	    let vi = List.assoc id env
	    in vi.jc_var_info_type,JCLvar vi
	  with Not_found -> 
	    typing_error e.jc_pexpr_loc "unbound identifier %s" id
	  end
    | JCPEderef(e1,f) ->
	let t,te = location env e1 in
	let fi = find_field e.jc_pexpr_loc t f in
	fi.jc_field_info_type, JCLderef(te,fi)	  
    | JCPEshift (_, _)  -> assert false (* TODO *)
    | JCPEif _ 
    | JCPEcast _
    | JCPEinstanceof _
    | JCPEold _ 
    | JCPEforall (_, _, _)
    | JCPEbinary (_, _, _)
    | JCPEassign_op (_, _, _)
    | JCPEassign (_, _)
    | JCPEapp (_, _)
    | JCPEconst _ -> 
	typing_error e.jc_pexpr_loc "invalid memory location"

let clause env c acc =
  match c with
    | JCPCrequires(e) ->
	{ acc with 
	    jc_fun_requires = assertion env e }
    | JCPCbehavior(id,assigns,ensures) ->
	let assigns = 
	  Option_misc.map (List.map (fun a -> snd (location env a))) assigns in
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

let field_tag_counter = ref 0

let field (t,id) =
  let ty = type_type t in
  incr field_tag_counter;
  let fi = {
    jc_field_info_tag = !field_tag_counter;
    jc_field_info_name = id;
    jc_field_info_type = ty;
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
    | JCPDtype(id,parent,fields,inv) ->
	let env = List.map field fields in
	let root,par = 
	  match parent with
	    | None -> (id,None)
	    | Some p ->
		try
		  let st = Hashtbl.find structs_table p in
		  (st.jc_struct_info_root,Some st)
		with
		    Not_found ->
		      typing_error d.jc_pdecl_loc "Undefined type '%s'" p
	in
	(*	
		let i =
		match inv with
		| None -> assertion_true
		| Some e -> assertion env e
		in
	*)	
	Hashtbl.add structs_table id 
	  { jc_struct_info_name = id;
	    jc_struct_info_fields = env;
	    jc_struct_info_parent = par;
	    jc_struct_info_root = root;
	  }
    | JCPDaxiom(id,e) ->
	let te = assertion [] e in
	Hashtbl.add axioms_table id te


(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
