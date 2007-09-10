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

(* Yannick

open Format
open Jc_ast
open Jc_env
open Jc_envset
open Jc_fenv
open Jc_options
open Jc_pervasives

open Apron
open Coeff
open Interval
open Lincons1


(*
  usage: jessie -ai [other_options]
  
  ai behaviour with other jessie options:
  
  -v prints inferred annotations
  -d prints debug info
 *)
  
(* Type of current invariant, made up of 3 parts:
 * - abstract value at current program point
 * - associative list of exceptions and abstract values obtained after throwing
 *   an exception of this type
 * - abstract value after returning from the function
 *)
type 'a abstract_invariants = 
    'a Abstract1.t * (exception_info * 'a Abstract1.t) list * 'a Abstract1.t

type 'a abstract_interpreter = {
  jc_absint_manager : 'a Manager.t;
  jc_absint_widening_threshold : int;
  jc_absint_loop_invariants : (int,'a abstract_invariants) Hashtbl.t;
  jc_absint_loop_iterations : (int,int) Hashtbl.t;
  jc_absint_target_statements : statement list;
  jc_absint_target_invariants : (statement * 'a Abstract1.t ref) list;
}

let make_term loc node t = 
  { jc_term_node = node; jc_term_type = t; jc_term_loc = loc }

let make_term_no_loc node t = 
  { jc_term_node = node; jc_term_type = t; jc_term_loc = Loc.dummy_position }

let make_assertion loc node =
  { jc_assertion_node = node; jc_assertion_loc = loc }

let make_assertion_no_loc node =
  { jc_assertion_node = node; jc_assertion_loc = Loc.dummy_position }


(*****************************************************************************)
(* From expressions to terms and assertions.                                 *)
(*****************************************************************************)

let raw_term t = {
  jc_term_node = t;
  jc_term_type = unit_type;
  jc_term_loc = Loc.dummy_position;
}

let raw_asrt a = {
  jc_assertion_node = a;
  jc_assertion_loc = Loc.dummy_position;
}

let rec term_of_expr e =
  let tnode = match e.jc_expr_node with
    | JCEconst c -> JCTconst c
    | JCEvar vi -> JCTvar vi
    | JCEbinary(e1,bop,e2) -> JCTbinary(term_of_expr e1,bop,term_of_expr e2)
    | JCEunary(uop,e1) -> JCTunary(uop,term_of_expr e1)
    | JCEshift(e1,e2) -> JCTshift(term_of_expr e1, term_of_expr e2)
    | JCEsub_pointer(e1,e2) -> JCTsub_pointer(term_of_expr e1, term_of_expr e2)
    | JCEderef(e1,fi) -> JCTderef(term_of_expr e1,fi)
    | JCEinstanceof(e1,st) -> JCTinstanceof(term_of_expr e1,st)
    | JCEcast(e1,st) -> JCTcast(term_of_expr e1,st)
    | JCErange_cast _ -> assert false (* TODO *)
    | JCEif(e1,e2,e3) -> JCTif(term_of_expr e1,term_of_expr e2,term_of_expr e3)
    | JCEoffset(off,e1,st) -> JCToffset(off, term_of_expr e1, st)
    | JCEalloc _ -> assert false (* TODO *)
    | JCEfree _ -> assert false (* TODO *)
  in
  raw_term tnode

let rec asrt_of_expr e =
  let anode = match e.jc_expr_node with
    | JCEconst (JCCboolean true) -> JCAtrue
    | JCEconst (JCCboolean false) -> JCAfalse
    | JCEconst _ -> assert false
    | JCEvar _ -> assert false (* TODO: what about boolean variables ? *)
    | JCEbinary(e1,bop,e2) ->
	if is_relation_binary_op bop then
	  JCArelation(term_of_expr e1,bop,term_of_expr e2)
	else if is_logical_binary_op bop then
	  match bop with
	  | Bland -> JCAand [asrt_of_expr e1;asrt_of_expr e2]
	  | Blor -> JCAor [asrt_of_expr e1;asrt_of_expr e2]
	  | Bimplies -> JCAimplies(asrt_of_expr e1,asrt_of_expr e2)
	  | Biff -> JCAiff(asrt_of_expr e1,asrt_of_expr e2)
	  | _ -> assert false
	else assert false
    | JCEunary(uop,e1) ->
	if is_logical_unary_op uop then
	  match uop with
	  | Unot -> JCAnot(asrt_of_expr e1)
	  | _ -> assert false
	else assert false
    | JCEinstanceof(e1,st) -> JCAinstanceof(term_of_expr e1,st)
    | JCEif(e1,e2,e3) -> JCAif(term_of_expr e1,asrt_of_expr e2,asrt_of_expr e3)
    | JCEderef _ -> JCAbool_term (term_of_expr e)
    | JCEcast _ | JCErange_cast _ | JCEshift _ | JCEsub_pointer _ 
    | JCEoffset _ | JCEalloc _ | JCEfree _ -> assert false
  in
  raw_asrt anode

let equality_operator_for_type = function
  | JCTnative ty ->
      begin match ty with
      | Tunit -> assert false
      | Treal -> Beq_real
      | Tboolean -> Biff
      | Tinteger -> Beq_int
      end
  | JCTlogic _ -> assert false
  | JCTenum _ -> Beq_int
  | JCTpointer _ -> Beq_pointer
  | JCTnull -> Beq_pointer


(*****************************************************************************)
(* Abstract variables naming and creation.                                   *)
(*****************************************************************************)

module Vai : sig

  val has_variable : var_info -> bool
  val has_offset_min_variable : var_info -> bool
  val has_offset_max_variable : var_info -> bool

  val variable : var_info -> Var.t
  val offset_min_variable : var_info -> Var.t
  val offset_max_variable : var_info -> Var.t
  val all_variables : var_info -> Var.t list

  val term : Var.t -> term

end = struct
  
  let variable_table = Hashtbl.create 0
  let offset_min_variable_table = Hashtbl.create 0
  let offset_max_variable_table = Hashtbl.create 0
  let term_table = Hashtbl.create 0

  let has_variable vi =
    match vi.jc_var_info_type with
    | JCTnative ty ->
	begin match ty with
	| Tunit | Treal -> false
	| Tboolean | Tinteger -> true
	end
    | JCTenum ei -> true
    | JCTpointer _ | JCTlogic _ | JCTnull -> false

  let has_offset_min_variable vi =
    match vi.jc_var_info_type with
    | JCTpointer _ -> true
    | JCTnative _ | JCTenum _ | JCTlogic _ | JCTnull -> false

  let has_offset_max_variable = has_offset_min_variable

  let variable vi =
    try
      Hashtbl.find variable_table vi
    with Not_found ->
      let va = Var.of_string vi.jc_var_info_name in
      Hashtbl.add variable_table vi va;
      let t = make_term_no_loc (JCTvar vi) vi.jc_var_info_type in
      Hashtbl.add term_table va t;
      va
	  
  let offset_min_variable vi = 
    try
      Hashtbl.find offset_min_variable_table vi
    with Not_found ->
      let va = Var.of_string ("__jc_offset_min_" ^ vi.jc_var_info_name) in
      Hashtbl.add offset_min_variable_table vi va;
      let t = make_term_no_loc (JCTvar vi) vi.jc_var_info_type in
      let st = match vi.jc_var_info_type with
	| JCTpointer(st,_,_) -> st
	| _ -> assert false
      in
      let tmin = make_term_no_loc (JCToffset(Offset_min,t,st)) integer_type in
      Hashtbl.add term_table va tmin;
      va
	  
  let offset_max_variable vi = 
    try
      Hashtbl.find offset_max_variable_table vi
    with Not_found ->
      let va = Var.of_string ("__jc_offset_max_" ^ vi.jc_var_info_name) in
      Hashtbl.add offset_max_variable_table vi va;
      let t = make_term_no_loc (JCTvar vi) vi.jc_var_info_type in
      let st = match vi.jc_var_info_type with
	| JCTpointer(st,_,_) -> st
	| _ -> assert false
      in
      let tmax = make_term_no_loc (JCToffset(Offset_max,t,st)) integer_type in
      Hashtbl.add term_table va tmax;
      va

  let all_variables vi =
    (if has_variable vi then [variable vi] else [])
    @ (if has_offset_min_variable vi then [offset_min_variable vi] else [])
    @ (if has_offset_max_variable vi then [offset_max_variable vi] else [])

  let term va = Hashtbl.find term_table va

end      


(*****************************************************************************)
(* Building assertions from inferred invariants.                             *)
(*****************************************************************************)

let mkterm linexpr =
  let vars = 
    Array.to_list (fst (Environment.vars (Linexpr1.get_env linexpr))) 
  in
  let rec add_term t va =
    match Linexpr1.get_coeff linexpr va with
    | Scalar s ->
	let vt = match Scalar.to_string s with
	  | "0." | "0" -> None
	  | "1" -> Some (Vai.term va)
	  | "-1" -> 
	      let tnode = JCTunary (Uminus_int, Vai.term va) in
	      let t = make_term_no_loc tnode integer_type in
	      Some t
	  | s -> 
	      let ctnode = JCTconst (JCCinteger s) in
	      let ct = make_term_no_loc ctnode integer_type in
	      let tnode = JCTbinary (ct, Bmul_int, Vai.term va) in
	      let t = make_term_no_loc tnode integer_type in
	      Some t
	in
	begin match t,vt with
	| None,vt -> vt
	| t,None -> t
	| Some t,Some vt ->
	    let tnode = JCTbinary (t, Badd_int, vt) in
	    let t = make_term_no_loc tnode integer_type in
	    Some t
	end
    | Interval _ -> assert false
  in
  let cst = match Linexpr1.get_cst linexpr with
    | Scalar s ->
	begin match Scalar.to_string s with
	| "0." | "0" -> None
	| s -> 
	    let ctnode = JCTconst (JCCinteger s) in
	    let ct = make_term_no_loc ctnode integer_type in
	    Some ct
	end
    | Interval _ -> assert false
  in
  match List.fold_left add_term cst vars with
  | None -> assert false
  | Some t -> t

let mkassertion lincons =
  let t1 = mkterm (Lincons1.get_linexpr1 lincons) in
  let op,c2 = match Lincons1.get_typ lincons with
    | EQ -> Beq_int, JCCinteger "0"
    | SUPEQ -> Bge_int, JCCinteger "0"
    | SUP -> Bgt_int, JCCinteger "0"
    | DISEQ -> Bneq_int, JCCinteger "0"
    | EQMOD scalar -> Bmod_int, JCCinteger (Scalar.to_string scalar)
  in
  let t2 = make_term_no_loc (JCTconst c2) integer_type in
  make_assertion_no_loc (JCArelation(t1,op,t2)) 

let mkinvariant mgr absval =
  let linconsarr = Abstract1.to_lincons_array mgr absval in
  let rec mkrec acc i = 
    if i >= 0 then
      mkrec (mkassertion (Lincons1.array_get linconsarr i) :: acc) (i-1)
    else acc
  in
  let asserts = mkrec [] (Lincons1.array_length linconsarr - 1) in
  make_assertion_no_loc (JCAand asserts)


(*****************************************************************************)
(* Extracting linear expressions and constraints from AST expressions.       *)
(*****************************************************************************)

let rec not_asrt a =
  let anode = match a.jc_assertion_node with
    | JCAtrue -> JCAfalse
    | JCAfalse -> JCAtrue
    | JCArelation(t1,bop,t2) ->
	begin match bop with
	| Blt_int -> JCArelation (t1, Bge_int, t2)
	| Bgt_int -> JCArelation (t1, Ble_int, t2)
	| Ble_int -> JCArelation (t1, Bgt_int, t2)
	| Bge_int -> JCArelation (t1, Blt_int, t2)
	| Beq_int -> JCArelation (t1, Bneq_int, t2)
	| Bneq_int -> JCArelation (t1, Beq_int, t2)
	| Blt_real -> JCArelation (t1, Bge_real, t2)
	| Bgt_real -> JCArelation (t1, Ble_real, t2)
	| Ble_real -> JCArelation (t1, Bgt_real, t2)
	| Bge_real -> JCArelation (t1, Blt_real, t2)
	| Beq_real -> JCArelation (t1, Bneq_real, t2)
	| Bneq_real -> JCArelation (t1, Beq_real, t2)
	| _ -> assert false
	end
    | JCAnot a -> 
	a.jc_assertion_node
    | JCAand _ | JCAor _ | JCAimplies _ | JCAiff _ | JCAapp _ 
    | JCAquantifier _ | JCAold _ | JCAinstanceof _ | JCAbool_term _
    | JCAif _ | JCAmutable _ | JCAtagequality _ ->
	JCAnot a
  in
  { a with jc_assertion_node = anode; }

let linstr_of_term env t =
  let rec linearize t =
    match t.jc_term_node with
    | JCTconst c ->
	begin match c with
	| JCCinteger s -> 
	    ([],int_of_string s)
	| JCCboolean _ | JCCvoid | JCCnull | JCCreal _ -> 
	    failwith "Not linear"
	end
    | JCTvar vi -> 
	let va = Vai.variable vi in
	if Environment.mem_var env va then ([Var.to_string va,1],0)
	else failwith "Not linear"
    | JCTbinary(t1,bop,t2) ->
	if is_arithmetic_binary_op bop then
	  let coeffs1,cst1 = linearize t1 in
	  let coeffs2,cst2 = linearize t2 in
          begin match bop with
	  | Badd_int ->
	      let coeffs = 
		List.fold_right (fun (va1,c1) acc ->
		  try 
		    let c2 = List.assoc va1 coeffs2 in
		    (va1,c1 + c2) :: acc
		  with Not_found -> (va1,c1) :: acc
		) coeffs1 []
	      in
	      let coeffs = 
		List.fold_right (fun (va2,c2) acc ->
		  if List.mem_assoc va2 coeffs then acc
		  else (va2,c2) :: acc
		) coeffs2 coeffs
	      in
	      (coeffs,cst1 + cst2)
	  | Bsub_int ->
	      let coeffs = 
		List.fold_right (fun (va1,c1) acc ->
		  try 
		    let c2 = List.assoc va1 coeffs2 in
		    (va1,c1 - c2) :: acc
		  with Not_found -> (va1,c1) :: acc
		) coeffs1 []
	      in
	      let coeffs = 
		List.fold_right (fun (va2,c2) acc ->
		  if List.mem_assoc va2 coeffs then acc
		  else (va2,- c2) :: acc
		) coeffs2 coeffs
	      in
	      (coeffs,cst1 + cst2)
	  | Bmul_int ->
	      begin match coeffs1,cst1,coeffs2,cst2 with
	      | [],_,[],_ -> ([],cst1 * cst2)
	      | [],cstmul,coeffs,cstadd | coeffs,cstadd,[],cstmul -> 
		  let coeffs = 
		    List.map (fun (va,c) -> (va,c * cstmul)) coeffs
		  in
		  (coeffs,cstadd * cstmul)
	      | _ -> failwith "Not linear"
	      end
	  | Badd_real | Bsub_real | Bmul_real | Bdiv_real ->
	      failwith "Not integer"
	  | Bdiv_int | Bmod_int -> 
	      failwith "Not linear"
	  | _ -> assert false
	end
      else failwith "Not linear"
  | JCTunary(uop,t1) ->
      if is_arithmetic_unary_op uop then
	let coeffs1,cst1 = linearize t1 in
	begin match uop with
	| Uplus_int -> 
	    (coeffs1,cst1)
	| Uminus_int -> 
	    let coeffs = List.map (fun (va,c) -> (va,-c)) coeffs1 in
	    (coeffs,- cst1)
	| Uplus_real | Uminus_real ->
	    failwith "Not integer"
	| _ -> assert false
	end
      else failwith "Not linear"
  | JCTshift _ | JCTsub_pointer _ | JCTderef _ | JCTinstanceof _ | JCTapp _
  | JCTold _ | JCTcast _ | JCTrange _ | JCTif _ | JCToffset _ -> 
      failwith "Not linear"
  in
  let mkmulstr = function
    | (va,0) -> ""
    | (va,c) -> string_of_int c ^ " * " ^ va 
  in
  let rec mkaddstr = function
    | [] -> ""
    | [va,c] -> mkmulstr (va,c)
    | (va,c) :: r -> 
	match mkmulstr (va,c) with
	| "" -> mkaddstr r
	| s -> s ^ " + " ^ (mkaddstr r)
  in
  try 
    let coeffs,cst = linearize t in
    Some (mkaddstr coeffs, cst)
  with Failure _ -> None

let rec linstr_of_assertion env a =
  match a.jc_assertion_node with
  | JCAtrue -> "true"
  | JCAfalse -> "false"
  | JCArelation(t1,bop,t2) ->
      let subt = raw_term (JCTbinary(t1,Bsub_int,t2)) in
      begin match linstr_of_term env subt with
      | None -> ""
      | Some (str,cst) ->
	  let cstr = string_of_int (- cst) in
	  match bop with
	  | Blt_int | Blt_real -> str ^ " < " ^ cstr
	  | Bgt_int | Bgt_real -> str ^ " > " ^ cstr
	  | Ble_int | Ble_real -> str ^ " < " ^ (string_of_int ((- cst) + 1))
	  | Bge_int | Bge_real -> str ^ " > " ^ (string_of_int ((- cst) - 1))
	  | Beq_int | Beq_real | Beq_pointer -> str ^ " = " ^ cstr
	  | Bneq_int | Bneq_real | Bneq_pointer -> ""
	  | _ -> assert false
      end
  | JCAnot a ->
      let nota = not_asrt a in
      begin match nota.jc_assertion_node with
      | JCAnot _ -> ""
      | _ -> linstr_of_assertion env nota
      end
  | JCAand _ | JCAor _ | JCAimplies _ | JCAiff _ | JCAapp _ 
  | JCAquantifier _ | JCAold _ | JCAinstanceof _ | JCAbool_term _
  | JCAif _ | JCAmutable _ | JCAtagequality _ -> ""

let offset_min_linstr_of_assertion env a = "" (* TODO *)
let offset_max_linstr_of_assertion env a = "" (* TODO *)

let expr env e = 
  match linstr_of_term env (term_of_expr e) with
  | None -> ""
  | Some ("",cst) -> string_of_int cst
  | Some (str,cst) -> str ^ " + " ^ (string_of_int cst)

(*
  match e.jc_expr_node with
  | JCEconst c ->
      begin match c with
      | JCCboolean b -> if b then "1" else "0"
      | JCCinteger s -> s
      | JCCvoid | JCCnull | JCCreal _ -> ""
      end
  | JCEvar vi -> 
      let va = Vai.variable vi in
      if Environment.mem_var env va then Var.to_string va else ""
  | JCEbinary(e1,bop,e2) ->
      if is_arithmetic_binary_op bop then
	let str1 = expr env e1 in
	if str1 = "" then "" else
	let str2 = expr env e2 in
	if str2 = "" then "" else
        begin match bop with
	| Badd_int | Badd_real -> str1 ^ "+" ^ str2
	| Bsub_int | Bsub_real -> str1 ^ "-" ^ str2
	| Bmul_int | Bmul_real -> str1 ^ "*" ^ str2
	| Bdiv_int | Bdiv_real | Bmod_int -> ""
	| _ -> assert false
	end
      else ""
  | JCEunary(uop,e1) ->
      if is_arithmetic_unary_op uop then
	let str1 = expr env e1 in
	begin match uop with
	| Uplus_int | Uplus_real -> str1
	| Uminus_int | Uminus_real -> "- " ^ str1
	| _ -> assert false
	end
      else ""
  | JCEshift _ | JCEsub_pointer _ | JCEderef _ | JCEinstanceof _ | JCEcast _
  | JCErange_cast _ | JCEif _ | JCEoffset _ | JCEalloc _ | JCEfree _ -> ""
*)

let not_boolean_expr env e = linstr_of_assertion env (not_asrt (asrt_of_expr e))

let boolean_expr env e = linstr_of_assertion env (asrt_of_expr e)
(*
  match e.jc_expr_node with
  | JCEconst c ->
      begin match c with
      | JCCboolean b -> if b then "true" else "false"
      | JCCinteger _ | JCCvoid | JCCnull | JCCreal _ -> ""
      end
  | JCEvar vi -> 
      let va = Vai.variable vi in
      if Environment.mem_var env va then (Var.to_string va ^ " = 1") else ""
  | JCEbinary(e1,bop,e2) ->
      if is_relation_binary_op bop then
	let str1 = expr env e1 in
	if str1 = "" then "" else
	let str2 = expr env e2 in
	if str2 = "" then "" else
	begin match bop with
	| Blt_int | Blt_real -> str1 ^ " < " ^ str2
	| Bgt_int | Bgt_real -> str1 ^ " > " ^ str2
	| Ble_int | Ble_real -> str1 ^ " <= " ^ str2
	| Bge_int | Bge_real -> str1 ^ " >= " ^ str2
	| Beq_int | Beq_real | Beq_pointer -> str1 ^ " = " ^ str2
	| Bneq_int | Bneq_real | Bneq_pointer -> str1 ^ " != " ^ str2
	| _ -> assert false
	end
      else ""
  | JCEunary(uop,e1) ->
      if is_logical_unary_op uop then
	let str1 = expr env e1 in
	begin match uop with
	| Unot -> str1 ^ " != 0"
	| _ -> assert false
	end
      else ""
  | JCEshift _ | JCEsub_pointer _ | JCEderef _ | JCEinstanceof _ | JCEcast _
  | JCErange_cast _ | JCEif _ | JCEoffset _ | JCEalloc _ | JCEfree _ -> ""
*)

let rec offset_min_expr env e = "" (* TODO *)
let rec offset_max_expr env e = "" (* TODO *)
let rec boolean_offset_min_expr env e = "" (* TODO *)
let rec boolean_offset_max_expr env e = "" (* TODO *)
let rec not_boolean_offset_min_expr env e = "" (* TODO *)
let rec not_boolean_offset_max_expr env e = "" (* TODO *)



(*****************************************************************************)
(* Performing abstract interpretation.                                       *)
(*****************************************************************************)

let assignment mgr pre vi e =
  let env = Abstract1.env pre in
  let vars,linexprs = 
    if Vai.has_variable vi then
      let va = Vai.variable vi in
      if Environment.mem_var env va then
	let lin = Parser.linexpr1_of_string env (expr env e) in
	[va], [lin]
      else [], []
    else [], []
  in
  let vars,linexprs = 
    if Vai.has_offset_min_variable vi then
      let va = Vai.offset_min_variable vi in
      if Environment.mem_var env va then
	let lin = Parser.linexpr1_of_string env (offset_min_expr env e) in
	va :: vars, lin :: linexprs
      else vars, linexprs
    else vars, linexprs
  in
  let vars,linexprs = 
    if Vai.has_offset_max_variable vi then
      let va = Vai.offset_max_variable vi in
      if Environment.mem_var env va then
	let lin = Parser.linexpr1_of_string env (offset_max_expr env e) in
	va :: vars, lin :: linexprs
      else vars, linexprs
    else vars, linexprs
  in
  let vars = Array.of_list vars and linexprs = Array.of_list linexprs in
  Abstract1.assign_linexpr_array_with mgr pre vars linexprs None;
  pre

let test_expr ~(neg:bool) mgr pre e =
  let env = Abstract1.env pre in
  let be = if neg then not_boolean_expr env e else boolean_expr env e in
  let bemin = 
    if neg then not_boolean_offset_min_expr env e 
    else boolean_offset_min_expr env e 
  in
  let bemax = 
    if neg then not_boolean_offset_max_expr env e
    else boolean_offset_max_expr env e
  in
  if be = "false" || bemin = "false" || bemax = "false" then
    Abstract1.bottom mgr (Abstract1.env pre)
  else
    let cstrs = 
      (if be = "true" || be = "" then [] else [be])
      @ (if bemin = "true" || bemin = "" then [] else [bemin])
      @ (if bemax = "true" || bemax = "" then [] else [bemax])
    in
    if cstrs = [] then 
      pre
    else
      let lincons = Parser.lincons1_of_lstring env cstrs in
      let envprint = Environment.print ~first:"[" ~sep:"," ~last:"]" in
      if Jc_options.debug then
	printf "pre.env = %a@.lincons.env = %a@." 
	  envprint (Abstract1.env pre)
	  envprint (Lincons1.array_get_env lincons);
      Abstract1.meet_lincons_array_with mgr pre lincons;
      pre

let test_assertion mgr pre a =
  let env = Abstract1.env pre in
  let be = linstr_of_assertion env a in
  let bemin = offset_min_linstr_of_assertion env a in
  let bemax = offset_max_linstr_of_assertion env a in
  if be = "false" || bemin = "false" || bemax = "false" then
    Abstract1.bottom mgr (Abstract1.env pre)
  else
    let cstrs = 
      (if be = "true" || be = "" then [] else [be])
      @ (if bemin = "true" || bemin = "" then [] else [bemin])
      @ (if bemax = "true" || bemax = "" then [] else [bemax])
    in
    if cstrs = [] then 
      pre
    else
      let lincons = Parser.lincons1_of_lstring env cstrs in
      let envprint = Environment.print ~first:"[" ~sep:"," ~last:"]" in
      if Jc_options.debug then
	printf "pre.env = %a@.lincons.env = %a@." 
	  envprint (Abstract1.env pre)
	  envprint (Lincons1.array_get_env lincons);
      Abstract1.meet_lincons_array_with mgr pre lincons;
      pre

(* Contrary to what is said in APRON documentation, arguments of [join] should
   be on the same environment. *)
let join mgr absval1 absval2 =
  let env1 = Abstract1.env absval1 in
  let absval2 = Abstract1.change_environment mgr absval2 env1 false in
  Abstract1.join_with mgr absval1 absval2;
  absval1

(* Contrary to what is said in APRON documentation, arguments of [widening] 
   should be on the same environment. *)
let widening mgr absval1 absval2 =
  let env1 = Abstract1.env absval1 in
  let absval2 = Abstract1.change_environment mgr absval2 env1 false in
  (* Due to problem with POLKA, join before widening so that arguments are in
     increasing order (1st included in 2nd). *)
  ignore (join mgr absval2 absval1);
  Abstract1.widening mgr absval1 absval2 (* no destructive version *)

let join_invariants mgr (cur1,postexcl1,postret1) (cur2,postexcl2,postret2) =
  let join_exclists postexcl1 postexcl2 =
    let join1 = List.fold_right (fun (ei,post1) acc ->
      try
	let post2 = List.assoc ei postexcl2 in
	(ei, join mgr post1 post2) :: acc
      with Not_found -> (ei,post1) :: acc
    ) postexcl1 []
    in
    List.fold_right (fun (ei,post2) acc ->
      try 
	let post = List.assoc ei acc in
	(ei, post) :: acc
      with Not_found -> (ei,post2) :: acc
    ) postexcl2 join1
  in
  if Jc_options.debug then
    printf "cur1 = %a@.cur2 = %a@." Abstract1.print cur1 Abstract1.print cur2;
  join mgr cur1 cur2,
  join_exclists postexcl1 postexcl2,
  join mgr postret1 postret2

let widen_invariants mgr (cur1,postexcl1,postret1) (cur2,postexcl2,postret2) =
  let widen_exclists postexcl1 postexcl2 =
    let widen1 = List.fold_right (fun (ei,post1) acc ->
      try
	let post2 = List.assoc ei postexcl2 in
	(ei, widening mgr post1 post2) :: acc
      with Not_found -> (ei,post1) :: acc
    ) postexcl1 []
    in
    List.fold_right (fun (ei,post2) acc ->
      try 
	let post = List.assoc ei acc in
	(ei, post) :: acc
      with Not_found -> (ei,post2) :: acc
    ) postexcl2 widen1
  in
  if Jc_options.debug then
    printf "widen1 = %a@.widen2 = %a@." Abstract1.print cur1 Abstract1.print cur2;
  let w = widening mgr cur1 cur2 in
  if Jc_options.debug then
    printf "widen res = %a@." Abstract1.print w;
  w,
  widen_exclists postexcl1 postexcl2,
  widening mgr postret1 postret2

let eq_invariants mgr (cur1,postexcl1,postret1) (cur2,postexcl2,postret2) =
  let eq_exclists postexcl1 postexcl2 =
    List.length postexcl1 = List.length postexcl2 &&
    List.fold_right (fun (ei,post1) acc ->
      acc &&
	try
	  let post2 = List.assoc ei postexcl2 in
	  Abstract1.is_eq mgr post1 post2 = Manager.True
	with Not_found -> false
    ) postexcl1 true
  in
  Abstract1.is_eq mgr cur1 cur2 = Manager.True
  && eq_exclists postexcl1 postexcl2
  && Abstract1.is_eq mgr postret1 postret2 = Manager.True

let copy_invariants mgr (cur,postexcl,postret) =
  Abstract1.copy mgr cur,
  List.map (fun (ei,post) -> (ei,Abstract1.copy mgr post)) postexcl,
  Abstract1.copy mgr postret

let rec ai_statement abs (pre,postexcl,postret as curinvs) s =
  if List.memq s abs.jc_absint_target_statements then
    begin try 
      (List.assq s abs.jc_absint_target_invariants) := pre
    with Not_found -> assert false end;
  let mgr = abs.jc_absint_manager in
  match s.jc_statement_node with
  | JCSdecl(vi,eo,s) ->
      let vars = Vai.all_variables vi in
      let env = 
	Environment.add (Abstract1.env pre) (Array.of_list vars) [||] 
      in 
      Abstract1.change_environment_with mgr pre env false;
      let pre = match eo with
	| None -> pre
        | Some e -> assignment mgr pre vi e
      in
      ai_statement abs (pre,postexcl,postret) s
  | JCSassign_var(vi,e) ->
      assignment mgr pre vi e, postexcl, postret
  | JCSassign_heap _ ->
      curinvs
  | JCSassert(_,a) ->
      test_assertion mgr pre a, postexcl, postret
  | JCSblock sl ->
      List.fold_left (ai_statement abs) curinvs sl
  | JCSif(e,ts,fs) ->
      let copy_pre = Abstract1.copy mgr pre in
      let tpre = test_expr ~neg:false mgr pre e in
      let tinvs = ai_statement abs (tpre,postexcl,postret) ts in
      let fpre = test_expr ~neg:true mgr copy_pre e in
      let finvs = ai_statement abs (fpre,postexcl,postret) fs in
      join_invariants mgr tinvs finvs
  | JCSreturn_void ->
      let pre = Abstract1.bottom mgr (Abstract1.env pre) in
      let postret = Abstract1.top mgr (Abstract1.env pre) in
      pre, postexcl, postret
  | JCSreturn(_,e) ->
      let pre = Abstract1.bottom mgr (Abstract1.env postret) in
      let postret = join mgr postret pre in
      pre, postexcl, postret
  | JCSthrow(ei,_) ->
      let bot = Abstract1.bottom mgr (Abstract1.env pre) in
      let postexc = pre in 
      (* TODO: add thrown value as abstract variable. *)
      let postexc =
	try join mgr (List.assoc ei postexcl) postexc
	with Not_found -> postexc
      in
      let postexcl = (ei, postexc) :: (List.remove_assoc ei postexcl) in
      bot, postexcl, postret
  | JCSpack _ | JCSunpack _ ->
      curinvs
  | JCStry(s,hl,fs) ->
      let pre,postexcl,postret = ai_statement abs curinvs s in
      let curpostexcl =
	List.filter (fun (ei,_) ->
	  not (List.exists (fun (ej,_,_) ->
	    ei.jc_exception_info_tag = ej.jc_exception_info_tag) hl)) postexcl
      in
      let curinvs =
	List.fold_left 
	  (fun curinvs (ei,_,s) ->
	    try
	      let postexc = List.assoc ei postexcl in
	      let postret = Abstract1.bottom mgr (Abstract1.env pre) in
	      let excinvs = ai_statement abs (postexc,[],postret) s in
	      join_invariants mgr curinvs excinvs
	    with Not_found -> curinvs
	  ) (pre,curpostexcl,postret) hl
      in
      (* BAD: ai_statement abs curinvs fs *)
      begin match fs.jc_statement_node with 
      | JCSblock [] -> curinvs
      | _ -> assert false (* TODO: apply finally stmt to all paths. *)
      end
  | JCSloop(la,ls) ->
      let loop_invariants = abs.jc_absint_loop_invariants in
      let loop_iterations = abs.jc_absint_loop_iterations in
      let num = 
	try Hashtbl.find loop_iterations la.jc_loop_tag 
	with Not_found -> 0
      in
      Hashtbl.replace loop_iterations la.jc_loop_tag (num+1);
      if num < abs.jc_absint_widening_threshold then
	let nextinvs = ai_statement abs (copy_invariants mgr curinvs) ls in
	let joininvs = join_invariants mgr curinvs nextinvs in
	ai_statement abs joininvs s
(* begin useless, only because no eq *)
      else if num = abs.jc_absint_widening_threshold then
	let nextinvs = ai_statement abs (copy_invariants mgr curinvs) ls in
	let wideninvs = widen_invariants mgr curinvs nextinvs in
	ai_statement abs (copy_invariants mgr wideninvs) s
(* end useless, only because no eq *)
      else
	begin try
	  let loopinvs = Hashtbl.find loop_invariants la.jc_loop_tag in
(* 	  let loopinvscopy = copy_invariants mgr loopinvs in *)
	  let wideninvs = widen_invariants mgr loopinvs curinvs in
	  Hashtbl.replace loop_invariants la.jc_loop_tag wideninvs;
(* Problem with convergence, [is_eq] does not seem to work. *)
(* 	  if eq_invariants mgr loopinvscopy wideninvs then *)
(* 	    copy_invariants mgr wideninvs *)
(* 	  else *)
(* 	    ai_statement abs (copy_invariants mgr wideninvs) s *)
	  (* Propagate to assertions. *)
	  copy_invariants mgr wideninvs
	with Not_found ->
	  let nextinvs = ai_statement abs (copy_invariants mgr curinvs) ls in
	  let wideninvs = widen_invariants mgr curinvs nextinvs in
	  Hashtbl.replace loop_invariants la.jc_loop_tag wideninvs;
	  ai_statement abs (copy_invariants mgr wideninvs) s
	end
  | JCScall(vio,f,args,s) -> 
      curinvs

let rec record_invariants abs s =
  let mgr = abs.jc_absint_manager in
  match s.jc_statement_node with
  | JCSdecl(_,_,s) -> 
      record_invariants abs s
  | JCSblock sl ->
      List.iter (record_invariants abs) sl
  | JCSif(_,ts,fs) ->
      record_invariants abs ts;
      record_invariants abs fs
  | JCStry(s,hl,fs) ->
      record_invariants abs s;
      List.iter (fun (_,_,s) -> record_invariants abs s) hl;
      record_invariants abs fs
  | JCSloop(la,ls) ->
      let loop_invariants = abs.jc_absint_loop_invariants in
      begin try
	let loopinv,_,_ = Hashtbl.find loop_invariants la.jc_loop_tag in
	(* Abstract1.minimize mgr loopinv; NOT IMPLEMENTED IN APRON *)
	if Jc_options.verbose then
	  printf "Inferring loop annotation %a@." Abstract1.print loopinv;
	let a = mkinvariant mgr loopinv in
	la.jc_loop_invariant <- 
	  make_assertion_no_loc (JCAand [la.jc_loop_invariant; a])
      with Not_found -> () end
  | JCSassign_var _ | JCSassign_heap _ | JCSassert _ 
  | JCSreturn_void | JCSreturn _ | JCSthrow _ | JCSpack _ | JCSunpack _ 
  | JCScall _ ->
      ()

let ai_function mgr targets (fi,sl) =
  try
    let env = Environment.make [||] [||] in
    
    (* Add global variables as abstract variables in [env]. *)
    let globvars =
      Hashtbl.fold (fun _ (vi, _) acc -> Vai.all_variables vi @ acc)
	Jc_norm.variables_table []
    in
    let env = Environment.add env (Array.of_list globvars) [||] in
    
    (* Add parameters as abstract variables in [env]. *)
    let params =
      List.fold_left (fun acc vi -> Vai.all_variables vi @ acc)
	[] fi.jc_fun_info_parameters
    in
    let env = Environment.add env (Array.of_list params) [||] in

    let bot = Abstract1.bottom mgr env in
    let abs = { 
      jc_absint_manager = mgr;
      jc_absint_widening_threshold = 1;
      jc_absint_loop_invariants = Hashtbl.create 0;
      jc_absint_loop_iterations = Hashtbl.create 0;
      jc_absint_target_statements = targets;
      jc_absint_target_invariants = List.map (fun s -> (s,ref bot)) targets;
    } in
    
    (* TODO: add \return as abstract variable. *)
    
    (* Annotation inference on the function body. *)
    let pre = Abstract1.top mgr env and postret = Abstract1.bottom mgr env in
    ignore (List.fold_left (ai_statement abs) (pre,[],postret) sl);
    List.iter (record_invariants abs) sl;
    List.map (fun (s,absvalptr) -> (s,mkinvariant mgr !absvalptr))
      abs.jc_absint_target_invariants
      
  with Manager.Error exc ->
    Manager.print_exclog std_formatter exc;
    printf "@.";
    []


(*****************************************************************************)
(* From terms and assertions to ATP formulas and the opposite way.           *)
(*****************************************************************************)

module Vwp : sig
  val to_atp : var_info -> string
  val from_atp : string -> var_info
end = struct

  let variable_table = Hashtbl.create 0

  let to_atp vi = 
    begin try 
      let vj = Hashtbl.find variable_table vi.jc_var_info_name in
      assert (vi.jc_var_info_tag = vj.jc_var_info_tag)
    with Not_found ->
      Hashtbl.add variable_table vi.jc_var_info_name vi
    end;
    vi.jc_var_info_name

  let from_atp s = Hashtbl.find variable_table s

end

let is_neq_binop = function
  | Bneq_int | Bneq_real | Bneq_pointer -> true
  | _ -> false

let atp_relation_of_binop = function
  | Blt_int | Blt_real -> "<"
  | Bgt_int | Bgt_real -> ">"
  | Ble_int | Ble_real -> "<="
  | Bge_int | Bge_real -> ">="
  | Beq_int | Beq_real | Beq_pointer -> "="
  | Bneq_int | Bneq_real | Bneq_pointer -> 
      assert false (* Should be treated as "not (t1 eq t2)". *)
  | _ -> assert false

let atp_arithmetic_of_binop = function
  | Badd_int | Badd_real -> "+"
  | Bsub_int | Bsub_real -> "-"
  | Bmul_int | Bmul_real -> "*"
  | Bdiv_int | Bdiv_real -> "/"
  | _ -> assert false  

let rec atp_of_term t = 
  match t.jc_term_node with
  | JCTconst c ->
      begin match c with
      | JCCinteger s -> 
	  Atp.Fn(s,[])
      | JCCboolean _ | JCCvoid | JCCnull | JCCreal _ -> 
	  assert false
      end
  | JCTvar vi ->
      Atp.Var (Vwp.to_atp vi)
  | JCTbinary(t1,bop,t2) ->
      Atp.Fn(atp_arithmetic_of_binop bop, List.map atp_of_term [t1;t2])
  | JCTunary(uop,t1) ->
      Atp.Fn(Jc_output.unary_op uop, [atp_of_term t1])
  | JCTshift _ | JCTsub_pointer _ | JCTderef _ | JCTapp _ | JCTold _
  | JCToffset _ | JCTinstanceof _ | JCTcast _ | JCTif _ | JCTrange _ ->
      assert false

let rec term_of_atp tm =
  let tnode = match tm with
    | Atp.Var s -> 
	JCTvar (Vwp.from_atp s)
    | Atp.Fn("+",[tm1;tm2]) ->
	JCTbinary(term_of_atp tm1,Badd_int,term_of_atp tm2)
    | Atp.Fn("-",[tm1;tm2]) ->
	JCTbinary(term_of_atp tm1,Bsub_int,term_of_atp tm2)
    | Atp.Fn("*",[tm1;tm2]) ->
	JCTbinary(term_of_atp tm1,Bmul_int,term_of_atp tm2)
    | Atp.Fn("/",[tm1;tm2]) ->
	JCTbinary(term_of_atp tm1,Bdiv_int,term_of_atp tm2)
    | Atp.Fn("-",[tm1]) ->
	JCTunary(Uminus_int,term_of_atp tm1)
    | Atp.Fn(s,[]) ->
	JCTconst (JCCinteger s)
    | tm -> 
	printf "Unexpected ATP term %a@." (fun fmt tm -> Atp.printert tm) tm;
	assert false
  in
  raw_term tnode

let rec atp_of_asrt a = 
  match a.jc_assertion_node with
  | JCAtrue -> 
      Atp.True
  | JCAfalse -> 
      Atp.False
  | JCArelation(t1,bop,t2) ->
      if is_neq_binop bop then
	Atp.Not(Atp.Atom(Atp.R("=",List.map atp_of_term [t1;t2])))
      else
	Atp.Atom(Atp.R(atp_relation_of_binop bop,List.map atp_of_term [t1;t2]))
  | JCAand al -> 
      let rec mkand = function
	| [] -> Atp.True
	| [a] -> atp_of_asrt a
	| a :: al -> Atp.And (atp_of_asrt a, mkand al)
      in
      mkand al
  | JCAor al -> 
      let rec mkor = function
	| [] -> Atp.False
	| [a] -> atp_of_asrt a
	| a :: al -> Atp.Or (atp_of_asrt a, mkor al)
      in
      mkor al
  | JCAimplies(a1,a2) ->
      Atp.Imp(atp_of_asrt a1,atp_of_asrt a2)
  | JCAiff(a1,a2) ->
      Atp.Iff(atp_of_asrt a1,atp_of_asrt a2)
  | JCAnot a ->
      Atp.Not(atp_of_asrt a)
  | JCAquantifier(Forall,vi,a) ->
      Atp.Forall(vi.jc_var_info_name,atp_of_asrt a)
  | JCAquantifier(Exists,vi,a) ->
      Atp.Exists(vi.jc_var_info_name,atp_of_asrt a)
  | JCAapp _ | JCAold _ | JCAinstanceof _ | JCAbool_term _
  | JCAif _ | JCAmutable _ | JCAtagequality _ ->
      assert false

let rec asrt_of_atp fm =
  let anode = match fm with
    | Atp.False ->
	JCAfalse
    | Atp.True ->
	JCAtrue
    | Atp.Atom(Atp.R("=",[tm1;tm2])) ->
	JCArelation(term_of_atp tm1,Beq_int,term_of_atp tm2)
    | Atp.Atom(Atp.R("<",[tm1;tm2])) ->
	JCArelation(term_of_atp tm1,Blt_int,term_of_atp tm2)
    | Atp.Atom(Atp.R(">",[tm1;tm2])) ->
	JCArelation(term_of_atp tm1,Bgt_int,term_of_atp tm2)
    | Atp.Atom(Atp.R("<=",[tm1;tm2])) ->
	JCArelation(term_of_atp tm1,Ble_int,term_of_atp tm2)
    | Atp.Atom(Atp.R(">=",[tm1;tm2])) ->
	JCArelation(term_of_atp tm1,Bge_int,term_of_atp tm2)
    | Atp.Atom _ ->
	printf "Unexpected ATP atom %a@." (fun fmt fm -> Atp.printer fm) fm;
	assert false
    | Atp.Not fm ->
	JCAnot (asrt_of_atp fm)
    | Atp.And(fm1,fm2) ->
	JCAand [asrt_of_atp fm1;asrt_of_atp fm2]
    | Atp.Or(fm1,fm2) ->
	JCAor [asrt_of_atp fm1;asrt_of_atp fm2]
    | Atp.Imp(fm1,fm2) ->
	JCAimplies(asrt_of_atp fm1,asrt_of_atp fm2)
    | Atp.Iff(fm1,fm2) ->
	JCAiff(asrt_of_atp fm1,asrt_of_atp fm2)
    | Atp.Forall(s,fm) ->
	JCAquantifier(Forall,Vwp.from_atp s,asrt_of_atp fm)
    | Atp.Exists(s,fm) ->
	JCAquantifier(Exists,Vwp.from_atp s,asrt_of_atp fm)
  in
  raw_asrt anode


(*****************************************************************************)
(* Computing weakest preconditions.                                          *)
(*****************************************************************************)

type weakest_precond = {
  jc_weakpre_target_statement : statement;
  jc_weakpre_goal_assertion : assertion;
}

type postconditions = {
  jc_post_normal : assertion option;
  jc_post_exceptional : (exception_info * assertion) list;
  jc_post_modified_vars : VarSet.t list;
}

let add_modified_var posts v =
  let vars = match posts.jc_post_modified_vars with
    | vs :: r -> VarSet.add v vs :: r
    | [] -> assert false
  in
  { posts with jc_post_modified_vars = vars; }

let add_modified_vars posts vs =
  let vars = match posts.jc_post_modified_vars with
    | vs2 :: r -> VarSet.union vs vs2 :: r
    | [] -> assert false
  in
  { posts with jc_post_modified_vars = vars; }

let remove_modified_var posts v =
  let vars = match posts.jc_post_modified_vars with
    | vs :: r -> VarSet.remove v vs :: r
    | [] -> assert false
  in
  { posts with jc_post_modified_vars = vars; }

let push_modified_vars posts = 
  let vars = posts.jc_post_modified_vars in
  { posts with jc_post_modified_vars = VarSet.empty :: vars; }

let pop_modified_vars posts = 
  let vs,vars = match posts.jc_post_modified_vars with
    | vs :: r -> vs,r
    | [] -> assert false
  in
  vs,{ posts with jc_post_modified_vars = vars; }

let rec wp_statement weak s curposts =
  let target_stmt = weak.jc_weakpre_target_statement in
  let goal_asrt = weak.jc_weakpre_goal_assertion in
  if s == target_stmt then { curposts with jc_post_normal = Some goal_asrt; }
  else match s.jc_statement_node with
  | JCSdecl(vi,eo,s) ->
      let curposts = wp_statement weak s curposts in
      let post = match curposts.jc_post_normal with
	| None -> None
	| Some a -> 
	    let a = match eo with
	      | None -> a
	      | Some e ->
		  let t1 = raw_term (JCTvar vi) in
		  let t2 = term_of_expr e in
		  let bop = equality_operator_for_type vi.jc_var_info_type in
		  let eq = raw_asrt (JCArelation(t1,bop,t2)) in
		  raw_asrt (JCAimplies(eq,a))
	    in
	    Some (raw_asrt (JCAquantifier(Forall,vi,a)))
      in
      let curposts = remove_modified_var curposts vi in
      { curposts with jc_post_normal = post; }
  | JCSassign_var(vi,e) ->
      let post = match curposts.jc_post_normal with
	| None -> None
	| Some a -> 
	    let t1 = raw_term (JCTvar vi) in
	    let t2 = term_of_expr e in
	    let bop = equality_operator_for_type vi.jc_var_info_type in
	    let eq = raw_asrt (JCArelation(t1,bop,t2)) in
	    Some (raw_asrt (JCAimplies(eq,a)))
      in
      let curposts = add_modified_var curposts vi in
      { curposts with jc_post_normal = post; }
  | JCSassign_heap _ -> assert false (* TODO *)
  | JCSassert(_,a1) ->
      let post = match curposts.jc_post_normal with
	| None -> None
	| Some a -> Some (raw_asrt (JCAimplies(a1,a)))
      in
      { curposts with jc_post_normal = post; }
  | JCSblock sl ->
      List.fold_right (wp_statement weak) sl curposts
  | JCSif(e,ts,fs) ->
      let tposts = wp_statement weak ts curposts in
      let tpost = match tposts.jc_post_normal with
	| None -> None
	| Some a -> 
	    let ta = asrt_of_expr e in
	    Some (raw_asrt (JCAimplies(ta,a)))
      in
      let fposts = wp_statement weak fs curposts in
      let fpost = match fposts.jc_post_normal with
	| None -> None
	| Some a -> 
	    let fa = not_asrt (asrt_of_expr e) in
	    Some (raw_asrt (JCAimplies(fa,a)))
      in
      let post = match tpost,fpost with
	| None,opta | opta,None -> opta
	| Some ta,Some fa -> Some (raw_asrt (JCAand [ta;fa]))
      in
      let tvs,_ = pop_modified_vars tposts in
      let fvs,_ = pop_modified_vars fposts in
      let vs = VarSet.union tvs fvs in
      let curposts = add_modified_vars curposts vs in
      { curposts with jc_post_normal = post; }
  | JCSreturn_void | JCSreturn _ -> 
      { curposts with jc_post_normal = None; }
  | JCSthrow(ei,_) -> (* TODO: link with value caught *)
      let post = 
	try Some (List.assoc ei curposts.jc_post_exceptional) 
	with Not_found -> None 
      in
      { curposts with jc_post_normal = post; }
  | JCSpack _ | JCSunpack _ -> 
      curposts
  | JCStry(s,hl,fs) ->
      begin match fs.jc_statement_node with 
      | JCSblock [] -> ()
      | _ -> assert false (* TODO: apply finally stmt to all paths. *)
      end;
      let handlpostexcl,handlvs = 
	List.fold_left 
	  (fun (curpostexcl,curvs) (ei,vio,s) ->
	    let excposts = wp_statement weak s curposts in
	    let curpostexcl = match excposts.jc_post_normal with
	      | None -> curpostexcl
	      | Some a -> (ei,a) :: curpostexcl
	    in
	    let excvs,_ = pop_modified_vars excposts in
	    let curvs = VarSet.union curvs excvs in
	    (curpostexcl,curvs)
	  ) ([],VarSet.empty) hl
      in
      let curpostexcl = 
	List.filter (fun (ei,_) ->
	  not (List.exists (fun (ej,_,_) ->
	    ei.jc_exception_info_tag = ej.jc_exception_info_tag) hl)
	) curposts.jc_post_exceptional
      in
      let curpostexcl = handlpostexcl @ curpostexcl in
      let tmpposts = { curposts with jc_post_exceptional = curpostexcl; } in
      let bodyposts = wp_statement weak s tmpposts in
      let bodyvs,_ = pop_modified_vars bodyposts in
      let vs = VarSet.union handlvs bodyvs in
      let curposts = add_modified_vars curposts vs in
      { curposts with jc_post_normal = bodyposts.jc_post_normal; }
  | JCSloop(la,ls) ->
      let loopposts = push_modified_vars curposts in
      let loopposts = wp_statement weak ls loopposts in
      let vs,loopposts = pop_modified_vars loopposts in
      (* Add modified variables of current loop to enclosing loop. *)
      let curposts = add_modified_vars curposts vs in
      let post = match loopposts.jc_post_normal with
	| None -> None
	| Some a -> 
	    Some (VarSet.fold 
	      (fun vi a -> raw_asrt (JCAquantifier(Forall,vi,a))) vs a)
      in
      { curposts with jc_post_normal = post; }
  | JCScall(vio,f,args,s) -> 
      curposts

let rec collect_asserts weakl s =
  match s.jc_statement_node with
  | JCSdecl(_,_,s) -> 
      collect_asserts weakl s
  | JCSblock sl ->
      List.fold_left collect_asserts weakl sl
  | JCSif(_,ts,fs) ->
      collect_asserts (collect_asserts weakl ts) fs
  | JCStry(s,hl,fs) ->
      let weakl = collect_asserts weakl s in
      let weakl = 
	List.fold_left (fun weakl (_,_,s) -> collect_asserts weakl s) weakl hl
      in
      collect_asserts weakl fs
  | JCSloop(_,ls) ->
      collect_asserts weakl ls
  | JCSassert(_,a) ->
      { jc_weakpre_target_statement = s;
	jc_weakpre_goal_assertion = a;
      } :: weakl
  | JCSassign_var _ | JCSassign_heap _ | JCSreturn_void | JCSreturn _
  | JCSthrow _ | JCSpack _ | JCSunpack _ | JCScall _ ->
      weakl
let simplify =
  let mgr = Polka.manager_alloc_strict () in
  function a ->
    let dnf = Atp.dnf (atp_of_asrt a) in
    let vars = Atp.fv dnf in
    let vars = List.map Vwp.from_atp vars in
    let vars = List.map Vai.variable vars in
    let env = Environment.make (Array.of_list vars) [||] in
    let disjuncts = Atp.disjuncts dnf in
    let disjuncts = List.map Atp.conjuncts disjuncts in
    let disjuncts = List.map (List.map asrt_of_atp) disjuncts in
    let abstract_disjuncts,other_disjuncts = 
      List.fold_right (fun conjunct (abstractl,otherl) ->
	try 
	  let absval = Abstract1.top mgr env in
	  let cstrs = List.map (linstr_of_assertion env) conjunct in
	  let lincons = Parser.lincons1_of_lstring env cstrs in
	  Abstract1.meet_lincons_array_with mgr absval lincons;
	  absval :: abstractl, otherl
	with Failure _ ->
	  abstractl, raw_asrt (JCAand conjunct) :: otherl
      ) disjuncts ([],[])
    in
    let abstract_disjuncts = 
      List.fold_right (fun absval acc ->
	let acc = List.filter 
	  (fun av -> not (Abstract1.is_leq mgr av absval = Manager.True)) acc
	in
	if List.exists 
	  (fun av -> Abstract1.is_leq mgr absval av = Manager.True) acc then acc
	else absval :: acc
      ) abstract_disjuncts []
    in
    List.iter (Abstract1.minimize mgr) abstract_disjuncts;
    let abstract_disjuncts = List.map (mkinvariant mgr) abstract_disjuncts in
    let disjuncts = abstract_disjuncts @ other_disjuncts in
    raw_asrt (JCAor disjuncts)

let wp_function weakl (fi,sl) =
  List.iter (fun weak ->
    let initposts = {
      jc_post_normal = None;
      jc_post_exceptional = [];
      jc_post_modified_vars = [];
    } in
    let initposts = push_modified_vars initposts in
    let posts = List.fold_right (wp_statement weak) sl initposts in
    let _,posts = pop_modified_vars posts in
    assert (posts.jc_post_modified_vars = []);
    match posts.jc_post_normal with
    | None -> ()
    | Some a -> 
	printf "wp : %a@." Jc_output.assertion a;
	let fm = atp_of_asrt a in
	Atp.printer fm; printf "@.";
	let qe = Atp.integer_qelim fm in
	Atp.printer qe; printf "@.";
	let qe = Atp.dnf qe in
	Atp.printer qe; printf "@.";
	let qe = asrt_of_atp qe in
	printf "qe : %a@." Jc_output.assertion qe;
	let qe = simplify qe in
	printf "qe : %a@." Jc_output.assertion qe
  ) weakl
    

(*****************************************************************************)
(* Main functions.                                                           *)
(*****************************************************************************)

let code_function = function
  | f,s,None -> ()
  | f,s,Some sl ->
      begin match Jc_options.ai_domain with
      | "box" -> 
	  let mgr = Box.manager_alloc () in
	  ignore (ai_function mgr [] (f,sl))
      | "oct" -> 
	  let mgr = Oct.manager_alloc () in
	  ignore (ai_function mgr [] (f,sl))
      | "pol" -> 
	  let mgr = Polka.manager_alloc_strict () in
	  ignore (ai_function mgr [] (f,sl))
      | "wp" ->
	  let weakl = List.fold_left collect_asserts [] sl in
	  wp_function weakl (f,sl)
      | "boxwp" | "octwp" | "polwp" ->
	  let weakl = List.fold_left collect_asserts [] sl in
	  let targets = 
	    List.map (fun weak -> weak.jc_weakpre_target_statement) weakl in
	  let invl = match Jc_options.ai_domain with
	    | "boxwp" -> 
		let mgr = Box.manager_alloc () in
		ai_function mgr targets (f,sl) 
	    | "octwp" -> 
		let mgr = Oct.manager_alloc () in
		ai_function mgr targets (f,sl) 
	    | "polwp" -> 
		let mgr = Polka.manager_alloc_strict () in
		ai_function mgr targets (f,sl) 
	    | _ -> assert false
	  in
	  let weakl = 
	    List.fold_right (fun weak acc ->
	      try 
		let inv = List.assq weak.jc_weakpre_target_statement invl in 
		let inv = simplify inv in
		let weak = { weak with jc_weakpre_goal_assertion =
		    raw_asrt(JCAimplies(inv,weak.jc_weakpre_goal_assertion))
		} in
		weak :: acc
	      with Not_found -> assert false
	    ) weakl []
	  in
	  wp_function weakl (f,sl)
      | _ -> assert false
      end
  
Yannick *)

open Apron
open Format
open Jc_ast
open Jc_env
open Jc_fenv
open Jc_options
open Jc_pervasives
open Coeff
open Interval
open Lincons1


(*

  usage: jessie -ai [other_options] f 
  
  ai behaviour with other jessie options:
  
  -v prints inferred annotations
  -d prints awful debug info
 
 *)
  

let terms_vars_table = Hashtbl.create 97

let calls_changed = ref false;;


let make_term loc node t = 
  { jc_term_node = node; jc_term_type = t; jc_term_loc = loc }
;;

let make_term_no_loc node t = 
  { jc_term_node = node; jc_term_type = t; jc_term_loc = Loc.dummy_position }
;;


let make_assertion loc node =
  { jc_assertion_node = node; jc_assertion_loc = loc }
;;

let make_assertion_no_loc node =
  { jc_assertion_node = node; jc_assertion_loc = Loc.dummy_position }
;;


let make_and loc al =
  let al =
    List.filter
      (fun a -> a.jc_assertion_node <> JCAtrue)
      al
  in
  make_assertion loc (JCAand al)
;;


let term_of_coeff c =
  match c with
  | Scalar scalar -> 
      let s = Scalar.to_string scalar in
      s, make_term_no_loc (JCTconst (JCCinteger s)) (JCTnative Tinteger)
  | Interval i ->
      assert false (* TODO ? *)
;;

let term_of_lincons1 lincons =
  let vl = Array.to_list (fst (Environment.vars lincons.env)) in
  let c = Lincons1.get_cst lincons in
  let s, t = term_of_coeff c in
  let t =
    List.fold_left
      (fun acc v ->
	let s, c = term_of_coeff (Lincons1.get_coeff lincons v) in
	try
	  let t = Hashtbl.find terms_vars_table v in
	  let t = 
	    match s with 
	    | "0." -> None
	    | "1" -> Some t
	    | "-1" -> 
		Some 
		  (make_term_no_loc 
		     (JCTunary (Uminus_int, t)) 
		     (JCTnative Tinteger))
	    | _ -> 
		Some 
		  (make_term_no_loc 
		     (JCTbinary (c, Bmul_int, t)) 
		     (JCTnative Tinteger))
	  in
	  match acc, t with
	  | _, None -> acc
	  | None, _ -> t
	  | Some acc, Some t -> 
	      Some
		(make_term_no_loc 
		   (JCTbinary (t, Badd_int, acc)) 
		   (JCTnative Tinteger))
	with Not_found ->
	  assert false (* should never happen *))
      (if s = "0" then None else Some t)
      vl
  in
  match t with 
  | None -> assert false (* should never happen *)
  | Some t -> t
;;

let bin_op_and_rvalue_of_lincons1 lincons =
  match (Lincons1.get_typ lincons) with
  | EQ -> Beq_int, JCCinteger "0"
  | SUPEQ -> Bge_int, JCCinteger "0"
  | SUP -> Bgt_int, JCCinteger "0"
  | DISEQ -> Bneq_int, JCCinteger "0"
  | EQMOD scalar -> Bmod_int, JCCinteger (Scalar.to_string scalar)
;;

let absvalue_to_assertion man loc env a =
  if debug then printf "absvalue_to_assertion...@.";
  let lincons = Abstract1.to_lincons_array man a in
  let lincons1l = 
    List.fold_left
      (fun acc lincons0 -> ({ lincons0 = lincons0; env = lincons.array_env })::acc)
      []
      (Array.to_list lincons.lincons0_array)
  in
  let al = 
    List.map
      (fun lincons ->
	let t1 = term_of_lincons1 lincons in
	let op, t2 = bin_op_and_rvalue_of_lincons1 lincons in
	make_assertion_no_loc 
	  (JCArelation (t1, op, 
			(make_term_no_loc 
			   (JCTconst t2)
			   (JCTnative Tinteger)))))
      lincons1l
  in
  make_assertion_no_loc (JCAand al)
;;


let abstract_vars_of_vi vi =
  match vi.jc_var_info_type with
  | JCTnative nt ->
      begin
        match nt with
        | Tunit -> []
	| Tboolean | Tinteger -> 
	    let v = Var.of_string vi.jc_var_info_name in
	    Hashtbl.add terms_vars_table
	      v (make_term_no_loc (JCTvar vi) vi.jc_var_info_type);
	    [v]
	| Treal -> []
      end
  | JCTlogic _ -> assert false (* should never happen *)
  | JCTenum ei ->
      let v = Var.of_string vi.jc_var_info_name in
      Hashtbl.add terms_vars_table
	v (make_term_no_loc (JCTvar vi) vi.jc_var_info_type);
      (* TODO: restrict v to the intervalle [min; max] *)
      [v]
  | JCTpointer (si, n1, n2) ->
      let s = vi.jc_var_info_name in
      let offset_min = s ^ "_offset_min" in
      let v1 = Var.of_string offset_min in
      let t1 = 
	make_term_no_loc 
	  (JCToffset (Offset_min, 
		      make_term_no_loc (JCTvar vi) vi.jc_var_info_type, 
		      si))
	  (JCTnative Tinteger) 
      in
      Hashtbl.add terms_vars_table v1 t1;
      let offset_max = s ^ "_offset_max" in
      let v2 = Var.of_string offset_max in
      let t2 = 
	make_term_no_loc 
	  (JCToffset (Offset_max, 
		      make_term_no_loc (JCTvar vi) vi.jc_var_info_type,
		      si))
	  (JCTnative Tinteger) 
      in
      Hashtbl.add terms_vars_table v2 t2;
(*      let offset_min_spec = offset_min ^ "<=" ^ Num.string_of_num n1 in
      let offset_max_spec = offset_max ^ ">=" ^ Num.string_of_num n2 in
      let lincons = Parser.lincons1_of_lstring env [offset_min_spec; offset_max_spec] in
      let absvalue = Abstract1.of_lincons_array man env lincons in
      if debug then printf "%s spec: %a@." s Abstract1.print absvalue;
      let post = Abstract1.meet man pre absvalue in *)
      [v1; v2]
  | JCTnull -> assert false (* should never happen *)
;;

let abstract_vars_spec_of_vi man pre vi =
  match vi.jc_var_info_type with
  | JCTnative nt -> pre
  | JCTlogic _ -> assert false (* should never happen *)
  | JCTenum ei -> pre (* TODO *)
  | JCTpointer (si, n1, n2) ->
      let s = vi.jc_var_info_name in
      let offset_min = s ^ "_offset_min" in
      let offset_max = s ^ "_offset_max" in
      let offset_min_spec = offset_min ^ "<=" ^ Num.string_of_num n1 in
      let offset_max_spec = offset_max ^ ">=" ^ Num.string_of_num n2 in
      let lincons = 
	Parser.lincons1_of_lstring (Abstract1.env pre) [offset_min_spec; offset_max_spec]
      in
      let absvalue = Abstract1.of_lincons_array man (Abstract1.env pre) lincons in
      if debug then printf "%s spec: %a@." s Abstract1.print absvalue;
      let post = Abstract1.meet man pre absvalue in
      post
  | JCTnull -> assert false (* should never happen *)
;;

let fresh_variable man env pre vi =
  (* create a new variable *)
  let v = Var.of_string vi.jc_var_info_name in
  Hashtbl.add terms_vars_table v
    (make_term_no_loc (JCTvar vi) vi.jc_var_info_type);
  (* add the variable to env *)
  try
    (env, pre)
  with Failure _ ->
    assert false (* should never happen *)
;;


let rec not_expr e =
  if debug then printf "not_expr...@.";
  let expr_node = 
    match e.jc_expr_node with
    | JCEconst c ->
	if debug then printf "  JCEconst...@.";
	begin
	  match c with
          | JCCvoid -> assert false (* TODO ? *)
          | JCCnull -> assert false (* TODO ? *)
          | JCCboolean b -> JCEunary (Unot, e)
          | JCCinteger s -> assert false (* TODO ? *)
          | JCCreal s -> assert false (* TODO ? *)
	end
    | JCEvar vi ->
	if debug then printf "  JCEvar...@.";
	begin
	  match vi.jc_var_info_type with
	  | JCTnative nt ->
	      begin
		match nt with 
		| Tunit -> assert false (* TODO *)
		| Tboolean -> JCEunary (Unot, e)
		| Tinteger -> assert false (* TODO *)
		| Treal -> assert false (* TODO *)
	      end
	  | JCTlogic s -> assert false (* TODO *)
	  | JCTenum ei -> assert false (* TODO *)
	  | JCTpointer (si, n1, n2) -> assert false (* TODO *)
	  | JCTnull -> assert false (* TODO *)
	end
    | JCEbinary (e1, bop, e2) ->
	if debug then printf "  JCEbinary...@.";
	begin
	  match bop with
	  | Blt_int -> JCEbinary (e1, Bge_int, e2)
	  | Bgt_int -> JCEbinary (e1, Ble_int, e2)
	  | Ble_int -> JCEbinary (e1, Bgt_int, e2)
	  | Bge_int -> JCEbinary (e1, Blt_int, e2)
	  | Beq_int -> (* fails because != not supported by apron0.9.6 *)
	      JCEbinary (e1, Bneq_int, e2) 
	  | Bneq_int -> assert false (* TO DO *)
	  | Blt_real -> assert false (* TO DO *)
	  | Bgt_real -> assert false (* TO DO *)
	  | Ble_real -> assert false (* TO DO *)
	  | Bge_real -> assert false (* TO DO *)
	  | Beq_real -> assert false (* TO DO *)
	  | Bneq_real -> assert false (* TO DO *)
	  | Badd_int -> assert false (* TO DO *)
	  | Bsub_int -> assert false (* TO DO *)
	  | Bmul_int -> assert false (* TO DO *)
	  | Bdiv_int -> assert false (* TO DO *)
	  | Bmod_int -> assert false (* TO DO *)
	  | Badd_real -> assert false (* TO DO *)
	  | Bsub_real -> assert false (* TO DO *)
	  | Bmul_real -> assert false (* TO DO *)
	  | Bdiv_real -> assert false (* TO DO *)
	  | Bland -> assert false (* TO DO *)
	  | Blor -> assert false (* TO DO *)
	  | Bimplies -> assert false (* TO DO *)
	  | Biff -> assert false (* TO DO *)
	  | Beq_pointer -> assert false (* TO DO *)
	  | Bneq_pointer -> assert false (* TO DO *)
	  | Bbw_and -> assert false (* TO DO *)
	  | Bbw_or -> assert false (* TO DO *)
	  | Bbw_xor -> assert false (* TO DO *)
	  | Bshift_left -> assert false (* TO DO *)
	  | Bshift_right -> assert false (* TO DO *)
	end
    | JCEunary (uop, e) -> assert false (* TO DO *)
    | JCEshift (e1, e2) -> assert false (* TO DO *)
    | JCEsub_pointer (e1, e2) -> assert false (* TO DO *)
    | JCEderef _ ->
	if debug then printf "  JCEderef...@.";
	JCEunary (Unot, e)
    | JCEinstanceof _ ->
	if debug then printf "  JCEinstanceof...@.";
	JCEunary (Unot, e)
    | JCEcast (e, si) -> assert false (* TO DO *)
    | JCErange_cast (ei, e) -> assert false (* TO DO *)
    | JCEif (e1, e2, e3) -> assert false (* TO DO *)
    | JCEoffset (ok, e, si) -> assert false (* TO DO *)
    | JCEalloc (e1, si) -> assert false (* TO DO *)
    | JCEfree e -> assert false (* TO DO *)
  in
  { e with jc_expr_node = expr_node }
;;


(*
let rec e_without_strict e =
  let expr_node =
    match e.jc_expr_node with
    | JCEbinary (e1, Blt_int, e2) ->
	let loc = e2.jc_expr_loc in
	let e2 = Jc_norm.make_int_binary loc e2 Bsub_int (Jc_norm.one_const loc) in 
	JCEbinary (e1, Ble_int, e2)
    | JCEbinary (e1, Bgt_int, e2) ->
	let loc = e2.jc_expr_loc in
	let e2 = Jc_norm.make_int_binary loc e2 Badd_int (Jc_norm.one_const loc) in 
	JCEbinary (e1, Bge_int, e2)
    | node -> 
	node 
  in
  { e with jc_expr_node = expr_node }
;;
*)


let rec expr man env pre e =
  if debug then printf "expr...@.";
  (* BEGIN PREPROC
  (* Bug APRON (?) with ops <, > *)
  let e = e_without_strict e in
  END PREPROC *)
  match e.jc_expr_node with
  | JCEconst c ->
      if debug then printf "  JCEconst...@.";
      begin
	match c with
        | JCCvoid -> assert false (* TODO ? *)
        | JCCnull -> env, pre, ["0"; "-1"]
        | JCCboolean b -> env, pre, [if b then "1" else "0"]
        | JCCinteger s -> env, pre, [s]
        | JCCreal _ -> env, pre, []
      end
  | JCEvar vi -> 
      if debug then printf "  JCEvar...@.";
      begin
	match vi.jc_var_info_type with
	| JCTnative nt ->
	    begin
	      match nt with
	      | Tunit -> assert false (* should never happen *)
	      | Tboolean -> env, pre, [vi.jc_var_info_name ^ " = 1"]
	      | Tinteger -> env, pre, [vi.jc_var_info_name]
	      | Treal -> assert false (* TODO *)
	    end
	| JCTlogic _ -> assert false (* should never happen *)
	| JCTenum ei ->
	    env, pre, [vi.jc_var_info_name]
	| JCTpointer (si, n1, n2) -> 
(*	    env, pre, [Num.string_of_num n1; Num.string_of_num n2] *)
	    env, pre, [vi.jc_var_info_name ^ "_offset_min";
		       vi.jc_var_info_name ^ "_offset_max"]
	| JCTnull -> assert false (* should never happen *)
      end
  | JCEbinary (e1, bop, e2) ->
      if debug then printf "  JCEbinary...@.";
      let env, pre, e1 = expr man env pre e1 in
      if e1 = [] then env, pre, [] else 
      let env, pre, e2 = expr man env pre e2 in
      if e2 = [] then env, pre, [] else
      begin
	match bop with
	| Blt_int | Blt_real -> 
	    env, pre, List.map2 (fun e1 e2 -> e1 ^ "<" ^ e2) e1 e2
	| Bgt_int | Bgt_real -> 
	    env, pre, List.map2 (fun e1 e2 -> e1 ^ ">" ^ e2) e1 e2
	| Ble_int | Ble_real -> 
	    env, pre, List.map2 (fun e1 e2 -> e1 ^ "<=" ^ e2) e1 e2
	| Bge_int | Bge_real ->
	    env, pre, List.map2 (fun e1 e2 -> e1 ^ ">=" ^ e2) e1 e2
	| Beq_int | Beq_real | Beq_pointer ->
	    env, pre, List.map2 (fun e1 e2 -> e1 ^ "=" ^ e2) e1 e2
	| Bneq_int | Bneq_real | Bneq_pointer ->
	    env, pre, List.map2 (fun e1 e2 -> e1 ^ "!=" ^ e2) e1 e2
	| Badd_int | Badd_real ->
	    env, pre, List.map2 (fun e1 e2 -> e1 ^ "+" ^ e2) e1 e2
	| Bsub_int | Bsub_real ->
	    env, pre, List.map2 (fun e1 e2 -> e1 ^ "-" ^ e2) e1 e2
	| Bmul_int | Bmul_real ->
	    env, pre, List.map2 (fun e1 e2 -> e1 ^ "*" ^ e2) e1 e2
	| Bdiv_int ->
	    env, pre, List.map2 (fun e1 e2 -> "1/" ^ e2 ^ "*" ^ e1) e1 e2
	| Bdiv_real -> assert false (* TODO ? *)
	| Bmod_int -> assert false (* TODO ? *)
	| Bland | Blor -> assert false (* should never happen *)
	| Bimplies -> assert false (* should never happen *)
	| Biff -> assert false (* should never happen *)
	| Bbw_and -> assert false (* TODO ? *)
	| Bbw_or -> assert false (* TODO *)
	| Bbw_xor -> assert false (* TODO *)
	| Bshift_left -> assert false (* TODO *)
	| Bshift_right -> assert false (* TODO *)
      end
  | JCEunary (uop, e) ->
      if debug then printf "  JCEunary...@.";
      let env, pre, strl = expr man env pre e in
      begin
	match uop with
	| Uplus_int -> assert false (* TODO ? *)
	| Uminus_int -> assert false (* TODO ? *)
	| Uplus_real -> assert false (* TODO ? *)
	| Uminus_real -> assert false (* TODO ? *)
	| Unot ->
	    begin
	      match e.jc_expr_node with
	      | JCEvar vi -> env, pre, [vi.jc_var_info_name ^ "= 0"]
	      | _ ->
		  let strl = 
		    List.map 
		      (fun str -> 
			if str = "0" then "1" else
			if str = "1" then "0" else
			str ^ "= 0")
		      strl
		  in
		  env, pre, strl
	    end
	| Ubw_not -> assert false (* TODO ? *)
      end
  | JCEshift (e1, e2) ->
      if debug then printf "  JCEshift...@.";
      let env, pre, strl1 = expr man env pre e1 in
      assert (List.length strl1 = 2);
      let env, pre, strl2 = expr man env pre e2 in
      assert (List.length strl2 = 1);
      env, pre, [(List.nth strl1 1) ^ "-" ^ List.hd strl2; List.nth strl1 0]
  | JCEsub_pointer (e1, e2) -> assert false (* TO DO *)
  | JCEderef (e, fi) ->
      if debug then printf "  JCEderef...@.";
      env, pre, []
  | JCEinstanceof (e, si) ->
      env, pre, []
  | JCEcast (e, si) ->
      if debug then printf "  JCEcast...@.";
      let env, pre, strl = expr man env pre e in
      env, pre, strl
  | JCErange_cast (ei, e) -> assert false (* TO DO *)
  | JCEif (e1, e2, e3) -> assert false (* TO DO *)
  | JCEoffset (ok, e, si) ->
      if debug then printf "  JCEoffset...@.";
      let s =
	match e.jc_expr_node with
	| JCEconst c -> assert false (* TO DO *)
	| JCEvar vi -> 
	    begin
	      match ok with
	      | Offset_max -> vi.jc_var_info_name ^ "_offset_max"
	      | Offset_min -> vi.jc_var_info_name ^ "_offset_min"
	    end
	| JCEbinary (e1, op, e2) -> assert false (* TO DO *)
	| JCEunary (op, e) -> assert false (* TO DO *)
	| JCEshift (e1, e2) -> assert false (* TO DO *)
	| JCEsub_pointer (e1, e2) -> assert false (* TO DO *)
	| JCEderef (e, fi) -> assert false (* TO DO *)
	| JCEinstanceof (e, si) -> assert false (* TO DO *)
	| JCEcast (e, si) -> assert false (* TO DO *)
	| JCErange_cast (ei, e) -> assert false (* TO DO *)
	| JCEif (e1, e2, e3) -> assert false (* TO DO *)
	| JCEoffset (ok, e, si) -> assert false (* TO DO *)
	| JCEalloc (e, si) -> assert false (* TO DO *)
	| JCEfree e -> assert false (* TO DO *)
      in
      env, pre, [s]
  | JCEalloc (e, si) ->
      if debug then printf "  JCEalloc...@.";
      (* TODO: understand how to handle e *)
      (* let env, pre, s = expr man env pre e1 in *)
      env, pre, ["0" ; "0"] (* values of \offset_min and \offset_max ? *)
  | JCEfree (e) -> assert false (* TODO ? *)
;;


let rec loop_condition man pre e sb se la fil =
  (* make the constraint from the loop condition *)
  let pre = Abstract1.join man (Abstract1.bottom man (Abstract1.env pre)) pre in (* Useless ? *)
  let env, pre, strl = expr man (Abstract1.env pre) pre e in
  let absvalue =
    (* TODO: special case of *while(false)* *)
    (* special case of *while(true)* *)
    if List.length strl = 1 && List.hd strl = "1" then
      Abstract1.top man env
    else
      let lincons = Parser.lincons1_of_lstring env strl in
      Abstract1.of_lincons_array man env lincons
  in
  if debug then printf "loop condition: %s@." (if List.length strl > 0 then List.hd strl else "0");
  if debug then printf "loop condition as abstract value: %a@." Abstract1.print absvalue;
  let pre = Abstract1.meet man pre absvalue in
  let sb, body, _ = statement man pre true None fil sb in
  (* compute loop invariant *)
  let body = Abstract1.change_environment man body (Abstract1.env pre) false in
  let loop_inv = Abstract1.widening man pre body in
  if debug then printf "after widening: %a@." Abstract1.print loop_inv;
  (* update env in absvalue *)
  let loop_inv = 
    Abstract1.change_environment man loop_inv (Abstract1.env absvalue) false
  in
  let loop_inv = Abstract1.meet man loop_inv absvalue in
  if debug then printf "2nd loop_condition: %a@." Abstract1.print loop_inv;
  let sb, body, _ = statement man loop_inv false None fil sb in
  let body = Abstract1.change_environment man body (Abstract1.env pre) false in
  let loop_inv = Abstract1.join man pre body in
  if verbose then printf "    inferred loop invariant: %a@." Abstract1.print loop_inv;
  let loop_invariant = la.jc_loop_invariant in
  let inferred_loop_inv = 
    absvalue_to_assertion 
      man
      (loop_invariant.jc_assertion_loc)
      (Abstract1.env loop_inv)
      loop_inv
  in
  let la = 
    { la with 
      jc_loop_invariant = make_and 
	(loop_invariant.jc_assertion_loc)
	[loop_invariant; inferred_loop_inv] }
  in
  let env, pre, strl = expr man env pre (not_expr e) in
  let absvalue = 
    (* special case of *while(true)* exit *)
    if List.length strl = 1 && List.hd strl = "0" then
      Abstract1.bottom man env
    (* TODO: special case of *while(false)* exit *)
    else
    let lincons = Parser.lincons1_of_lstring (Abstract1.env pre) strl in
    Abstract1.of_lincons_array man (Abstract1.env pre) lincons
  in
  let post = Abstract1.meet man loop_inv absvalue in
  JCSif (e, sb, se), post, Some la

and statement man pre fv lao fil s =
  if debug then printf "statement ...@.";
  let jc_statement_node, post, lao =
    match s.jc_statement_node with
    | JCScall (vio, fi, el, s) ->
        if debug then printf "  JCScall ...@.";
	let fi =
	  if List.mem fi fil then
	    begin
	      let new_params =
		List.map2
		  (fun vi e ->
		    match vi.jc_var_info_type with
		    | JCTnative _ -> vi (* TODO ? *)
		    | JCTlogic _ -> assert false (* should never happen *)
		    | JCTenum _ -> vi (* TODO ? *)
		    | JCTpointer (si, n1, n2) ->
			if Num.le_num n1 n2 then
			  begin
			    match e.jc_expr_node with
			    | JCEconst c ->
				begin
				  match c with
				  | JCCvoid -> vi (* TODO ? *)
				  | JCCnull ->
				      calls_changed := true;
				      { vi with jc_var_info_type = JCTpointer (si, Num.Int 0, Num.Int (-1)) }
				  | JCCboolean _ -> vi (* TODO ? *)
				  | JCCinteger _ -> vi (* TODO ? *)
				  | JCCreal _ -> vi (* TODO ? *)
				end
			    | JCEvar vie ->
				let v = 
				  Hashtbl.fold
				    (fun v t acc ->
				      match t.jc_term_node with
				      | JCTvar vi' -> acc
				      | JCToffset (ok, t, si) ->
					  begin
					    match t.jc_term_node with
					    | JCTvar vi' ->
						if vi'.jc_var_info_name = vie.jc_var_info_name then
						  begin
						    match ok with
						    | Offset_min -> v, snd acc
						    | Offset_max -> fst acc, v
						  end
						else
						  acc
					    | _ -> assert false (* should never happen *)
					  end
				      | _ -> acc)
				    terms_vars_table
				    (Var.of_string "", Var.of_string "")
				in
				let v_min = fst v in
				let v_max = snd v in
				let interval_min = Abstract1.bound_variable man pre v_min in
				let interval_max = Abstract1.bound_variable man pre v_max in
				let sup_min = Num.num_of_string (Scalar.to_string interval_min.sup) in
				let inf_max = Num.num_of_string (Scalar.to_string interval_max.inf) in
				let n1 = Num.min_num n1 sup_min in
				let n2 = Num.min_num n2 inf_max in
				calls_changed := true;
				{ vi with jc_var_info_type = JCTpointer (si, n1, n2) }
			  | JCEbinary (e1, bop, e2) -> vi (* TODO ? *)
			  | JCEunary (uop, e) -> vi (* TODO ? *)
			  | JCEshift (e1, e2) -> vi (* TODO ? *)
			  | JCEsub_pointer (e1, e2) -> assert false (* TO DO *)
			  | JCEderef (e, fi) -> vi (* TODO ? *)
			  | JCEinstanceof (e, si) -> vi (* TODO ? *)
			  | JCEcast (e, si) -> vi (* TODO ? *)
			  | JCErange_cast (ei, e) -> vi (* TODO ? *)
			  | JCEif (e1, e2, e3) -> vi (* TODO ? *)
			  | JCEoffset (ok, e, si) -> vi (* TODO ? *)
			  | JCEalloc (e, si) -> vi (* TODO ? *)
			  | JCEfree e -> vi (* TODO ? *)			
			end
		      else
			(* the type is the more general => nothing to be done *)
			vi
		    | JCTnull -> vi (* TODO ? *))
		  fi.jc_fun_info_parameters
		  el
	      in
	      { fi with jc_fun_info_parameters = new_params }
	    end
	  else
	    fi
	in
	let (_, fs, bo) = Hashtbl.find Jc_norm.functions_table fi.jc_fun_info_tag in
	Hashtbl.replace Jc_norm.functions_table fi.jc_fun_info_tag (fi, fs, bo);
        begin
          match vio with
          | None -> 
	      (* TODO: add the post of f if any + 
		 check the parameters and store the info *)
	      JCScall (None, fi, el, s), pre, lao
          | Some vi -> 
              begin
		match fi.jc_fun_info_name with
		| "shift" -> 
                    (* cases to distinguish parameters ? *)
                    (* just add the fresh variable to env *)
                    let env, pre = 
		      if fv then fresh_variable man (Abstract1.env pre) pre vi 
		      else (Abstract1.env pre), pre
		    in
                    let s, post, lao = statement man pre fv lao fil s in
                    JCScall (vio, fi, el, s), post, lao
		| _ -> (* TODO?: add the post of fi to pre *)
		    JCScall (vio, fi, el, s), pre, lao
              end
        end
    | JCSassign_var (vi, e) ->
	if debug then printf "  JCSassign_var ...%s@." vi.jc_var_info_name;
	let env, pre, strl = expr man (Abstract1.env pre) pre e in
	if strl = [] then JCSassign_var (vi, e), pre, lao else
	let vl = abstract_vars_of_vi vi in
	let linexprl = 
	  List.map 
	    (Parser.linexpr1_of_string env)
	    strl
	in
	let post = 
	  Abstract1.assign_linexpr_array man pre 
	    (Array.of_list vl)
	    (Array.of_list linexprl) 
	    None
	in
	JCSassign_var (vi, e), post, lao
    | JCSassign_heap (e1, fi, e2) ->
	if debug then printf "  JCSassign_heap ...@.";
	JCSassign_heap(e1, fi, e2), pre, lao
    | JCSassert (so, a) ->
	(* TODO ? : add assertion *a* to pre *)
	JCSassert (so, a), pre, lao
    | JCSblock sl ->
	if debug then printf "  JCSblock ...@.";
	let sl, post, lao =
          List.fold_left
            (fun (sl, pre, lao) s ->
              let s, post, lao = statement man pre fv lao fil s in
              (List.rev (s::(List.rev sl)), post, lao) ) 
            ([], pre, lao) 
            sl
	in
	JCSblock sl, post, lao
    | JCSdecl (vi, eo, s) ->
	if debug then printf "  JCSdecl ...%s@." vi.jc_var_info_name;
	let vl = abstract_vars_of_vi vi in
	let env = Environment.add (Abstract1.env pre) (Array.of_list vl) [||] in
	let pre = Abstract1.change_environment man pre env false in
        begin
          match eo with
          | None ->
              let s, post, lao = statement man pre fv lao fil s in
              (* TO DO ? : update env in pre *)
              JCSdecl (vi, eo, s), post, lao
          | Some e ->
	      let env, pre, strl = expr man (Abstract1.env pre) pre e in
	      if strl = [] then JCSdecl (vi, eo, s), pre, lao else
	      let linexprl =
		List.map
		  (Parser.linexpr1_of_string env)
		  strl
	      in
	      assert (List.length vl = List.length linexprl);
	      let post = 
		Abstract1.assign_linexpr_array man pre
		  (Array.of_list vl) 
		  (Array.of_list linexprl) 
		  None
	      in
 (*             let post = Abstract1.meet_lincons_array man pre lincons in *)
              let s, post, lao = statement man post fv lao fil s in
              JCSdecl (vi, eo, s), post, lao
        end;
    | JCSif (e, s1, s2) ->
        if debug then printf "  JCSif ...@.";
	begin
	  match lao with
	  | None -> (* a 'true' *if* *)
	      (* Step 1: if branch *)
	      let env, pre, strl = expr man (Abstract1.env pre) pre e in
	      let lincons = Parser.lincons1_of_lstring env strl in
	      let absvalue = Abstract1.of_lincons_array man env lincons in
	      if debug then printf "if condition: %a@." Abstract1.print absvalue;
	      let if_pre = Abstract1.meet man pre absvalue in
	      let s1, post1, lao = statement man if_pre fv lao fil s1 in
	      (* Step 2: else branch *)
	      let env, pre, strl = expr man (Abstract1.env pre) pre (not_expr e) in
	      let lincons = Parser.lincons1_of_lstring env strl in
	      let absvalue = Abstract1.of_lincons_array man env lincons in
	      if debug then printf "else condition: %a@." Abstract1.print absvalue;
	      let else_pre = Abstract1.meet man pre absvalue in
	      let s2, post2, lao = statement man else_pre fv lao fil s2 in
	      (* Step 3: join the two branches *)
	      Abstract1.change_environment_with man post1 (Abstract1.env pre) false;
	      Abstract1.change_environment_with man post2 (Abstract1.env pre) false;
	      let post = Abstract1.join man post1 post2 in
	      JCSif (e, s1, s2), post, lao
	  | Some la -> (* the *if* is actually a *loop condition* *)
	      if debug then printf "   the if is a loop_condition @.";
	      loop_condition man pre e s1 s2 la fil
	end
    | JCSloop (la, s) ->
        if debug then printf "  JCSloop ...@.";
	let s, post, la = 
	  let s, post, lao = statement man pre fv (Some la) fil s in
	  s, post, 
	  match lao with 
	  | None -> assert false (* should never happen *) 
	  | Some la -> la
	in
	JCSloop (la, s), post, lao
    | JCSreturn_void ->
	JCSreturn_void, pre, lao
    | JCSreturn (t, e) ->
	(* TODO: postcondition on result ? *)
	JCSreturn (t, e), pre, lao
    | JCStry (sb, catchl, sf) ->
	if debug then printf "  JCStry ...@.";
	let sb, post, lao = statement man pre true lao fil sb in
	let catchl, postl =
	  List.fold_left
	    (fun (acc1, acc2) (ei, vio, s) ->
	      let env, post = 
		match vio with
		| None -> Abstract1.env post, post
		| Some vi -> fresh_variable man (Abstract1.env post) post vi
	      in
	      let s, post, lao = statement man post true lao fil s in
	      (ei, vio, s)::acc1, post::acc2)
	    ([], [])
	    catchl
	in
	let pref = Abstract1.join_array man (Array.of_list (post::postl)) in
	let sf, post, lao = statement man pref true lao fil sf in
	JCStry (sb, catchl, sf), post, lao
    | JCSthrow (ei, eo) ->
        if debug then printf "  JCSthrow ...@.";
	JCSthrow (ei, eo), pre, lao
    | JCSpack (si1, e, si2) ->
	JCSpack (si1, e, si2), pre, lao
    | JCSunpack (si1, e, si2) ->
	JCSunpack (si1, e, si2), pre, lao
  in
  { s with jc_statement_node = jc_statement_node }, post, lao
									   ;;

									   
let code_function fi bo = 
  if debug then printf "code_function...@.";
  if verbose then printf "  function %s@." fi.jc_fun_info_name;
  try
    (* let man = Box.manager_alloc () in *) (* Intervalles abstract domain *)
    let man = Oct.manager_alloc () in (* Octagon abstract domain *)
    (* let man = Polka.manager_alloc_strict () in *) (* Polyhedra abstract domain *)
    let env = Environment.make [||] [||] in
    
    (* add global variables as abstract variables in env *)
    let vars =
      Hashtbl.fold
	(fun tag (vi, eo) acc -> 
	  let vl = abstract_vars_of_vi vi in	
	  vl@acc)
	Jc_norm.variables_table
	[]
    in
    let env = Environment.add env (Array.of_list vars) [||] in
    
    (* add parameters as abstract variables in env *)
    let params =
      List.fold_left
        (fun acc vi ->
	  let vl = abstract_vars_of_vi vi in
	  vl@acc)
        []
        fi.jc_fun_info_parameters
    in
    let env = Environment.add env (Array.of_list params) [||] in

    (* add parameters specs *)
    let post =
      List.fold_left
        (fun pre vi ->
	  let post = abstract_vars_spec_of_vi man pre vi in
	  post)
        (Abstract1.top man env)
        fi.jc_fun_info_parameters
    in

    match bo with
    | None -> None
    | Some sl ->
	(* annotation inference on the function body *)
	Some
	  (fst
	     (List.fold_left
		(fun (sl, pre) s ->
		  let s, post, _ = statement man pre true None fi.jc_fun_info_calls s in
		  (List.rev (s::(List.rev sl)), post)) 
		([], post)
		sl))
  with Manager.Error e ->
    Manager.print_exclog std_formatter e;
    bo
;;


let rec calls_infer fi fs bo =
  let bo = code_function fi bo in
  let (fi, _, _) = Hashtbl.find Jc_norm.functions_table fi.jc_fun_info_tag in
  Hashtbl.replace Jc_norm.functions_table fi.jc_fun_info_tag (fi, fs, bo);
  List.iter
    (fun fi ->
      let fi, fs, bo =
	try 
	  Hashtbl.find Jc_norm.functions_table fi.jc_fun_info_tag
	with Not_found -> assert false (* should never happen *)
      in
      calls_infer fi fs bo)
    fi.jc_fun_info_calls
;;


let rec main_function fi fs bo = 
  calls_infer fi fs bo;
  if !calls_changed then 
    main_function fi fs bo
  else
    ()


(* TODO : cas appels récursifs (direct ou indirect) 
    -> utiliser le graphe d'appel
*)
   



(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
