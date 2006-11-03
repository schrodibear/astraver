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
open Jc_ast
open Output

let const c =
  match c with
    | JCCnull -> assert false
    | JCCreal s -> Prim_real s
    | JCCinteger s -> Prim_int s
    | JCCbool b -> Prim_bool b

let tr_native_type t =
  match t with
    | `Tunit -> "unit"
    | `Tboolean -> "bool"
    | `Tinteger -> "int"
    | `Treal -> "real"

let simple_logic_type s =
  { logic_type_name = s; logic_type_args = [] }
  
let tr_base_type t =
  match t with
    | JCTnative t -> simple_logic_type (tr_native_type t)
    | JCTlogic s -> simple_logic_type s
    | JCTvalidpointer (id, a, b) -> 
	let ti = simple_logic_type id in
	{ logic_type_name = "pointer";
	  logic_type_args = [ti] }
    | JCTpointer _ -> assert false

let tr_type t =
  match t with
    | JCTnative _ | JCTlogic _ -> Base_type(tr_base_type t)
    | JCTvalidpointer _ -> Base_type(tr_base_type t)	
    | JCTpointer _ -> assert false

let lvar ?(assigned=true) label v =
  if assigned then
    match label with 
      | None -> LVar v 
      | Some l -> LVarAtLabel(v,l)
  else LVar v

let rec term label oldlabel t =
  let ft = term label oldlabel in
  match t.jc_term_node with
    | JCTconst JCCnull -> LVar "null"
    | JCTvar v -> 
	lvar ~assigned:v.jc_var_info_assigned label v.jc_var_info_final_name
    | JCTconst c -> LConst(const c)
    | JCTshift(t1,t2) -> LApp("shift",[ft t1; ft t2])
    | JCTderef(t,f) -> LApp("select",[lvar label f.jc_field_info_name;ft t])
    | JCTapp(f,l) -> 
	LApp(f.jc_logic_info_name,List.map ft l)
    | JCTold(t) -> term (Some oldlabel) oldlabel t

let rec assertion label oldlabel a =
  let fa = assertion label oldlabel 
  and ft = term label oldlabel
  in
  match a.jc_assertion_node with
    | JCAtrue -> LTrue
    | JCAand l -> make_and_list (List.map fa l)
    | JCAimplies(a1,a2) -> make_impl (fa a1) (fa a2)
    | JCAapp(f,l) -> LPred(f.jc_logic_info_name,List.map ft l)
    | JCAforall(v,p) -> 
	LForall(v.jc_var_info_final_name,
		tr_base_type v.jc_var_info_type,
		fa p)
    | JCAold a -> assertion (Some oldlabel) oldlabel a

type interp_lvalue =
  | LocalRef of var_info
  | HeapRef of field_info * expr

let tempvar_count = ref 0
let reset_tmp_var () = tempvar_count := 0
let tmp_why_var () = incr tempvar_count; "jessie_" ^ string_of_int !tempvar_count

let rec expr e =
  match e.jc_expr_node with
    | JCEconst JCCnull -> Var "null"
    | JCEconst c -> Cte(const c)
    | JCEvar v -> Var v.jc_var_info_final_name
    | JCEshift(e1,e2) -> make_app "shift" [expr e1; expr e2]
    | JCEderef(e,f) -> make_app "acc_" [Var f.jc_field_info_name; expr e]
    | JCEassign_local (vi, e2) -> 
	assert false
	  (*
	    let n = v.var_unique_name in
	    append
	    (Assign(n, bin_op op (Deref n) (interp_expr e2)))
	    (Deref n)
	  *)
    | JCEassign_heap(e1,fi,e2) -> 
	let tmp1 = tmp_why_var () in
	let tmp2 = tmp_why_var () in
	let memory = fi.jc_field_info_name in
	Let(tmp1, expr e1,
	    Let(tmp2, expr e2,
		append
		  (make_app "safe_upd_"
		     [Var memory; Var tmp1; Var tmp2])
		  (Var tmp2))) 
    | JCEassign_op_local (vi, op, e2) -> 
	assert false
	  (*
	    let n = v.var_unique_name in
	    append
	    (Assign(n, bin_op op (Deref n) (interp_expr e2)))
	    (Deref n)
	  *)
    | JCEassign_op_heap(e1,fi,op,e2) -> 
	let tmp1 = tmp_why_var () in
	let tmp2 = tmp_why_var () in
	let memory = fi.jc_field_info_name in
	Let(tmp1, expr e1,
	    Let(tmp2, 
		make_app op.jc_fun_info_name
		  [ make_app "acc_" [Var memory; Var tmp1] ;
		    expr e2 ],
		append
		  (make_app "safe_upd_"
		     [Var memory; Var tmp1; Var tmp2])
		  (Var tmp2))) 
    | JCEcall(f,l) -> 
	make_app f.jc_fun_info_name (List.map expr l)

let statement_expr e =
  match e.jc_expr_node with
    | JCEconst JCCnull -> assert false
    | JCEconst c -> assert false
    | JCEvar v -> assert false
    | JCEshift(e1,e2) -> assert false
    | JCEderef(e,f) -> assert false
    | JCEassign_local (vi, e2) -> 
	assert false
	  (*
	    let n = v.var_unique_name in
	    append
	    (Assign(n, bin_op op (Deref n) (interp_expr e2)))
	    (Deref n)
	  *)
    | JCEassign_heap(e1,fi,e2) -> 
	let tmp1 = tmp_why_var () in
	let tmp2 = tmp_why_var () in
	let memory = fi.jc_field_info_name in
	Let(tmp1, expr e1,
	    Let(tmp2, expr e2,
		make_app "safe_upd_"
		   [Var memory; Var tmp1; Var tmp2]))
    | JCEassign_op_local (vi, op, e2) -> 
	assert false
	  (*
	    let n = v.var_unique_name in
	    append
	    (Assign(n, bin_op op (Deref n) (interp_expr e2)))
	    (Deref n)
	  *)
    | JCEassign_op_heap(e1,fi,op,e2) -> 
	let tmp1 = tmp_why_var () in
	let tmp2 = tmp_why_var () in
	let memory = fi.jc_field_info_name in
	Let(tmp1, expr e1,
	    Let(tmp2, 
		make_app op.jc_fun_info_name
		  [ make_app "acc_" [Var memory; Var tmp1] ;
		    expr e2 ],
		make_app "safe_upd_"
		  [Var memory; Var tmp1; Var tmp2]))
    | JCEcall(f,l) -> 
	make_app f.jc_fun_info_name (List.map expr l)

let rec statement s = 
  match s.jc_statement_node with
    | JCSskip -> Void
    | JCSblock l -> statement_list l
    | JCSexpr e -> statement_expr e
    | JCSif (e, s1, s2) -> 
	If(expr e, statement s1, statement s2)
    | JCSwhile (_, _, _) -> assert false
    | JCSassert _ -> assert false
    | JCSdecl _ -> assert false
    | JCSreturn e -> 
	expr e
    | JCSbreak l -> assert false
    | JCScontinue l -> assert false
    | JCSgoto l -> assert false
    | JCSthrow (_, _) -> assert false
    | JCStry (_, _, _) -> assert false

and statement_list l =
  match l with
    | [] -> Void
    | [i] -> statement i
    | i::r -> append (statement i) (statement_list r)

(******************
 structures
******************)

let tr_struct id fl acc =
  let acc = 
    List.fold_left
      (fun acc fi ->
	 let mem =
	   { logic_type_name = "memory";
	     logic_type_args = [simple_logic_type id;
				tr_base_type fi.jc_field_info_type] }
	 in
	 Param(false,
	       fi.jc_field_info_name,
	       Ref_type(Base_type mem))::acc)
      acc fl
  in (Type(id,[]))::acc

       

(*****************
 functions
**************)

let parameter v =
  (v.jc_var_info_final_name,tr_type v.jc_var_info_type)

let tr_fun f spec body acc = 
  let requires = assertion None "" spec.jc_fun_requires in
  let global_ensures =
    List.fold_right
      (fun (id,e) acc -> make_and (assertion None "" e.jc_behavior_ensures) acc)
      spec.jc_fun_behavior LTrue
  in
  let why_param = 
    let annot_type =
      Annot_type(requires,tr_type f.jc_fun_info_return_type,
		 [],[], global_ensures,[])
    in
    let fun_type =
      List.fold_right
	(fun v acc ->
	   Prod_type(v.jc_var_info_final_name,tr_type v.jc_var_info_type,acc))
	f.jc_fun_info_parameters
	annot_type
    in
    Param(false,f.jc_fun_info_name,fun_type)
  in
  let params = List.map parameter f.jc_fun_info_parameters in
  let acc =
    List.fold_right
      (fun (id,b) acc ->
	 let d =
	   Def(f.jc_fun_info_name ^ "_ensures_" ^ id,
	       Fun(params,
		   requires,statement_list body,
		   assertion None "" b.jc_behavior_ensures,[]))
	 in d::acc)
      spec.jc_fun_behavior acc
  in why_param::acc

  
