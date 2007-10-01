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
(*    Nicolas ROUSSET                                                     *)
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


open Pp
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
  usage: jessie -ai <box,oct,pol,wp,boxwp,octwp,polwp>
  
  ai behaviour with other jessie options:
  
  -v prints inferred annotations
  -d prints debug info
 *)
  

let raw_term t = {
  jc_term_node = t;
  jc_term_type = unit_type;
  jc_term_loc = Loc.dummy_position;
}

let raw_asrt a = {
  jc_assertion_node = a;
  jc_assertion_loc = Loc.dummy_position;
}

let type_term t ty = {
  jc_term_node = t;
  jc_term_type = ty;
  jc_term_loc = Loc.dummy_position;
}

let var_term vi = {
  jc_term_node = JCTvar vi;
  jc_term_type = vi.jc_var_info_type;
  jc_term_loc = Loc.dummy_position;
}

let full_term t ty loc = {
  jc_term_node = t;
  jc_term_type = ty;
  jc_term_loc = loc;
}

let full_asrt a loc = {
  jc_assertion_node = a;
  jc_assertion_loc = loc;
}

let raw_expr e = {
  jc_expr_node = e;
  jc_expr_type = unit_type;
  jc_expr_loc = Loc.dummy_position;
}

let type_expr e ty = {
  jc_expr_node = e;
  jc_expr_type = ty;
  jc_expr_loc = Loc.dummy_position;
}

let loc_expr e loc = {
  jc_expr_node = e;
  jc_expr_type = unit_type;
  jc_expr_loc = loc;
}

let full_expr e ty loc = {
  jc_expr_node = e;
  jc_expr_type = ty;
  jc_expr_loc = loc;
}

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

let make_and al = 
  let anode = match al with
    | [] -> JCAtrue
    | [a] -> a.jc_assertion_node
    | al -> JCAand al
  in
  raw_asrt anode

let make_or al = 
  let anode = match al with
    | [] -> JCAfalse
    | [a] -> a.jc_assertion_node
    | al -> JCAor al
  in
  raw_asrt anode

let deep_raw_term t =
  post_map_term raw_term t

let rec deep_raw_asrt a =
  let term = deep_raw_term and asrt = deep_raw_asrt in
  let anode = match a.jc_assertion_node with
    | JCArelation(t1,bop,t2) ->
	JCArelation(term t1,bop,term t2)
    | JCAnot a -> 
	JCAnot (asrt a)
    | JCAand al ->
	JCAand(List.map asrt al)
    | JCAor al ->
	JCAor(List.map asrt al)
    | JCAimplies(a1,a2) ->
	JCAimplies(asrt a1,asrt a2)
    | JCAiff(a1,a2) ->
	JCAiff(asrt a1,asrt a2)
    | JCAapp(li,tl) ->
	JCAapp(li,List.map term tl)
    | JCAquantifier(qt,vi,a) ->
	JCAquantifier(qt,vi,asrt a)
    | JCAold a ->
	JCAold(asrt a)      
    | JCAinstanceof(t,st) ->
	JCAinstanceof(term t,st)
    | JCAbool_term t ->
	JCAbool_term(term t)
    | JCAif(t,a1,a2) ->
	JCAif(term t,asrt a1,asrt a2)
    | JCAmutable(t,st,tag) ->
	JCAmutable(term t,st,tag)
    | JCAtrue | JCAfalse | JCAtagequality _ as anode -> anode
  in
  raw_asrt anode

let rec term_name =
  let string_explode s = 
    let rec next acc i = 
      if i >= 0 then next (s.[i] :: acc) (i-1) else acc
    in
    next [] (String.length s - 1)
  in
  let string_implode ls =
    let s = String.create (List.length ls) in
    ignore (List.fold_left (fun i c -> s.[i] <- c; i + 1) 0 ls);
    s
  in
  let filter_alphanumeric s =
    let alphanum c = 
      String.contains "abcdefghijklmnopqrstuvwxyz" c
    || String.contains "ABCDEFGHIJKLMNOPQRSTUVWXYZ" c
    || String.contains "123456789" c
    || c = '_'
    in
    string_implode (List.filter alphanum (string_explode s))
  in
  function t ->
    match t.jc_term_node with
    | JCTconst c ->
	begin match c with
	| JCCinteger s -> filter_alphanumeric s
	| JCCboolean b -> if b then "true" else "false"
	| JCCvoid -> "void"
	| JCCnull -> "null" 
	| JCCreal s -> filter_alphanumeric s
	end
    | JCTvar vi -> vi.jc_var_info_name
    | JCTbinary(t1,bop,t2) ->
	let bop_name = match bop with
	  | Blt_int | Blt_real -> "inf"
	  | Bgt_int | Bgt_real -> "sup"
	  | Ble_int | Ble_real -> "infeq"
	  | Bge_int | Bge_real -> "supeq"
	  | Beq_int | Beq_real | Beq_pointer -> "eq"
	  | Bneq_int | Bneq_real | Bneq_pointer -> "neq"
	  | Badd_int | Badd_real -> "plus"
	  | Bsub_int | Bsub_real -> "minus"
	  | Bmul_int | Bmul_real -> "times"
	  | Bdiv_int | Bdiv_real -> "div"
	  | Bmod_int -> "mod"
	  | Bland -> "and"
	  | Blor -> "or"
	  | Bimplies -> "implies"
	  | Biff -> "iff"
	  | Bbw_and -> "bwand"
	  | Bbw_or -> "bwor"
	  | Bbw_xor -> "bwxor"
	  | Bshift_right -> "shiftright"
	  | Bshift_left -> "shiftleft"
	in
	term_name t1 ^ "_" ^ bop_name ^ "_" ^ (term_name t2)
    | JCTunary(uop,t1) ->
	let uop_name = match uop with
	  | Uplus_int | Uplus_real -> "plus"
	  | Uminus_int | Uminus_real -> "minus"
	  | Unot -> "not"
	  | Ubw_not -> "bwnot"
	in
	uop_name ^ "_" ^ (term_name t1)
    | JCTshift (t1, t2) ->
	term_name t1 ^ "_shift_" ^ (term_name t2)
    | JCTsub_pointer(t1,t2) ->
	term_name t1 ^ "_sub_pointer_" ^ (term_name t2)
    | JCTderef(t1,fi) ->
	term_name t1 ^ "_field_" ^ fi.jc_field_info_name
    | JCTapp(li,tl) ->
	li.jc_logic_info_name ^ "_of_" ^ 
	  List.fold_right(fun t acc ->
	    if acc = "" then term_name t
	    else term_name t ^ "_and_" ^ acc
	  ) tl ""
    | JCTold t ->
	"old_" ^ (term_name t)
    | JCToffset(Offset_max,t,st) ->
	"offset_max_" ^ (term_name t)
    | JCToffset(Offset_min,t,st) ->
	"offset_min_" ^ (term_name t)
    | JCTinstanceof(t,st) ->
	(term_name t) ^ "_instanceof_" ^ st.jc_struct_info_name
    | JCTcast(t,st) ->
	(term_name t) ^ "_cast_" ^ st.jc_struct_info_name
    | JCTif(t1,t2,t3) ->
	"if_" ^ (term_name t1) ^ "_then_" ^ (term_name t2) 
	^ "_else_" ^ (term_name t3)
    | JCTrange(Some t1,Some t2) ->
	(term_name t1) ^ "_range_" ^ (term_name t2)
    | JCTrange(Some t1,None) ->
	(term_name t1) ^ "_range_none"
    | JCTrange(None,Some t2) ->
	"none_range_" ^ (term_name t2)
    | JCTrange(None,None) ->
	"none_range_none"

let rec destruct_pointer t = 
  match t.jc_term_node with
  | JCTconst JCCnull -> None, None
  | JCTvar vi -> Some vi, None
  | JCTshift(t1,t2) ->
      begin match destruct_pointer t1 with
      | viopt, None -> viopt, Some t2
      | viopt,Some offt -> 
	  let tnode = JCTbinary(offt,Badd_int,t2) in
	  let offt = full_term tnode integer_type t2.jc_term_loc in
	  viopt,Some offt
      end
  | JCTcast _ -> assert false (* TODO *)
  | _ -> assert false


(*****************************************************************************)
(* Types.                                                                    *)
(*****************************************************************************)

(* Assertion to be checked at some program point. *)
type target_assertion = {
  jc_target_statement : statement;
  jc_target_location : Loc.position;
  jc_target_assertion : assertion;
  mutable jc_target_invariant : assertion;
}

(* Type of current invariant in abstract interpretation, made up of 3 parts:
 * - abstract value at current program point
 * - associative list of exceptions and abstract values obtained after throwing
 *   an exception of this type
 * - abstract value after returning from the function
 *)
type 'a abstract_invariants = {
  jc_absinv_normal : 'a Abstract1.t;
  jc_absinv_exceptional : (exception_info * 'a Abstract1.t) list;
  jc_absinv_return : 'a Abstract1.t;
}

(* Parameters of an abstract interpretation. *)
type 'a abstract_interpreter = {
  jc_absint_manager : 'a Manager.t;
  jc_absint_function_environment : Environment.t;
  jc_absint_function_name : string;
  jc_absint_widening_threshold : int;
  jc_absint_loop_invariants : (int,'a abstract_invariants) Hashtbl.t;
  jc_absint_loop_iterations : (int,int) Hashtbl.t;
  jc_absint_target_assertions : target_assertion list;
}

(* Type of current postcondition in weakest precondition computation:
 * - postcondition at current program point
 * - associative list of exceptions and postconditions that should be satisfied
 *   when an exception of this type is caught
 * - stack of sets of modified variables, each set except the first one 
 *   corresponding to an enclosed loop
 *)
type weakest_postconditions = {
  jc_post_normal : assertion option;
  jc_post_exceptional : (exception_info * assertion) list;
  jc_post_modified_vars : VarSet.t list;
}


(*****************************************************************************)
(* Debug.                                                                    *)
(*****************************************************************************)

let print_abstract_invariants fmt invs =
  fprintf fmt "@[<v 2>{@\nnormal: %a@\nexceptional: %a@\nreturn: %a@\n}@]"
    Abstract1.print invs.jc_absinv_normal
    (print_list comma (fun fmt (ei,absval) -> 
      fprintf fmt "(%s,%a)" ei.jc_exception_info_name Abstract1.print absval))
    invs.jc_absinv_exceptional
    Abstract1.print invs.jc_absinv_return


(*****************************************************************************)
(* From expressions to terms and assertions.                                 *)
(*****************************************************************************)

let term_of_expr e =
  let rec term e = 
    let tnode = match e.jc_expr_node with
      | JCEconst c -> JCTconst c
      | JCEvar vi -> JCTvar vi
      | JCEbinary(e1,bop,e2) -> JCTbinary(term e1,bop,term e2)
      | JCEunary(uop,e1) -> JCTunary(uop,term e1)
      | JCEshift(e1,e2) -> JCTshift(term e1, term e2)
      | JCEsub_pointer(e1,e2) -> JCTsub_pointer(term e1,term e2)
      | JCEderef(e1,fi) -> JCTderef(term e1,fi)
      | JCEinstanceof(e1,st) -> JCTinstanceof(term e1,st)
      | JCEcast(e1,st) -> JCTcast(term e1,st)
      | JCErange_cast _ -> failwith "Not a term"
      | JCEif(e1,e2,e3) -> JCTif(term e1,term e2,term e3)
      | JCEoffset(off,e1,st) -> JCToffset(off, term e1, st)
      | JCEalloc _ -> failwith "Not a term"
      | JCEfree _ -> failwith "Not a term"
    in
    raw_term tnode
  in
  try Some (term e) with Failure _ -> None

let raw_term_of_expr = term_of_expr

let rec asrt_of_expr e =
  let anode = match e.jc_expr_node with
    | JCEconst (JCCboolean true) -> JCAtrue
    | JCEconst (JCCboolean false) -> JCAfalse
    | JCEconst _ -> assert false
    | JCEvar _ -> assert false (* TODO: what about boolean variables ? *)
    | JCEbinary(e1,bop,e2) ->
	if is_relation_binary_op bop then
	  match term_of_expr e1,term_of_expr e2 with
	  | Some t1,Some t2 -> JCArelation(t1,bop,t2)
	  | _ -> JCAtrue
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
    | JCEinstanceof(e1,st) ->
	begin match term_of_expr e1 with
	| Some t1 -> JCAinstanceof(t1,st)
	| None -> JCAtrue 
	end
    | JCEif(e1,e2,e3) -> 
	begin match term_of_expr e1 with
	| Some t1 -> JCAif(t1,asrt_of_expr e2,asrt_of_expr e3)
	| None -> JCAtrue 
	end
    | JCEderef _ -> 
	begin match term_of_expr e with
	| Some t -> JCAbool_term t
	| None -> JCAtrue 
	end
    | JCEcast _ | JCErange_cast _ | JCEshift _ | JCEsub_pointer _ 
    | JCEoffset _ | JCEalloc _ | JCEfree _ -> assert false
  in
  raw_asrt anode

let raw_asrt_of_expr = asrt_of_expr


(*****************************************************************************)
(* Replacing variables in terms and assertions.                              *)
(*****************************************************************************)

(* All terms involved should be raw terms. *)
let rec replace_term_in_term srct targetvi t = 
  pre_map_term 
    (fun t ->
      if srct = t then Some (JCTvar targetvi)
      else match t.jc_term_node with
      | JCTvar vi ->
	  assert(vi.jc_var_info_tag != targetvi.jc_var_info_tag);
	  None
      | _ -> None
    ) t
      
(* All assertions and terms involved should be raw. *)
let rec replace_term_in_assertion srct targetvi a = 
  let term = replace_term_in_term srct targetvi in
  let asrt = replace_term_in_assertion srct targetvi in
  let anode = match a.jc_assertion_node with
    | JCArelation(t1,bop,t2) ->
	JCArelation(term t1,bop,term t2)
    | JCAnot a -> 
	JCAnot (asrt a)
    | JCAand al ->
	JCAand(List.map asrt al)
    | JCAor al ->
	JCAor(List.map asrt al)
    | JCAimplies(a1,a2) ->
	JCAimplies(asrt a1,asrt a2)
    | JCAiff(a1,a2) ->
	JCAiff(asrt a1,asrt a2)
    | JCAapp(li,tl) ->
	JCAapp(li,List.map term tl)
    | JCAquantifier(qt,vi,a) ->
	assert(vi.jc_var_info_tag != targetvi.jc_var_info_tag);
	JCAquantifier(qt,vi,asrt a)
    | JCAold a ->
	JCAold(asrt a)      
    | JCAinstanceof(t,st) ->
	JCAinstanceof(term t,st)
    | JCAbool_term t ->
	JCAbool_term(term t)
    | JCAif(t,a1,a2) ->
	JCAif(term t,asrt a1,asrt a2)
    | JCAmutable(t,st,tag) ->
	JCAmutable(term t,st,tag)
    | JCAtrue | JCAfalse | JCAtagequality _ as anode -> anode
  in
  { a with jc_assertion_node = anode; }


(*****************************************************************************)
(* Abstract variables naming and creation.                                   *)
(*****************************************************************************)

let strlen_f = make_logic_fun "strlen" unit_type

module Vai : sig

  val has_variable : term -> bool
  val has_offset_min_variable : term -> bool
  val has_offset_max_variable : term -> bool
  val has_strlen_variable : term -> bool

  val variable : term -> Var.t
  val offset_min_variable : term -> Var.t
  val offset_max_variable : term -> Var.t
  val strlen_variable : term -> Var.t
  val all_variables : term -> Var.t list

  val term : Var.t -> term
  val variable_of_term : term -> Var.t

  val is_strlen_variable : Var.t -> bool

end = struct
  
  let variable_table = Hashtbl.create 0
  let offset_min_variable_table = Hashtbl.create 0
  let offset_max_variable_table = Hashtbl.create 0
  let strlen_variable_table = Hashtbl.create 0
  let term_table = Hashtbl.create 0

  let has_variable t =
    match t.jc_term_type with
    | JCTnative ty ->
	begin match ty with
	| Tunit | Treal -> false
	| Tboolean | Tinteger -> true
	end
    | JCTenum ei -> true
    | JCTpointer _ | JCTlogic _ | JCTnull -> false

  let has_offset_min_variable t =
    match t.jc_term_type with
    | JCTpointer _ -> true
    | JCTnative _ | JCTenum _ | JCTlogic _ | JCTnull -> false

  let has_offset_max_variable = has_offset_min_variable

  let has_strlen_variable t = 
    match t.jc_term_type with
    | JCTpointer _ -> true
    | JCTnative _ | JCTenum _ | JCTlogic _ | JCTnull -> false

  let variable t =
    let t = deep_raw_term t in
    try
      Hashtbl.find variable_table t
    with Not_found ->
      let va = Var.of_string (term_name t) in
      Hashtbl.add variable_table t va;
      Hashtbl.add term_table va t;
      va
	  
  let offset_min_variable t = 
    let ty = t.jc_term_type in
    let t = deep_raw_term t in
    try
      Hashtbl.find offset_min_variable_table t
    with Not_found ->
      let va = Var.of_string ("__jc_offset_min_" ^ (term_name t)) in
      Hashtbl.add offset_min_variable_table t va;
      let st = match ty with
	| JCTpointer(st,_,_) -> st
	| _ -> assert false
      in
      let tmin = type_term (JCToffset(Offset_min,t,st)) integer_type in
      Hashtbl.add term_table va tmin;
      va
	  
  let offset_max_variable t = 
    let ty = t.jc_term_type in
    let t = deep_raw_term t in
    try
      Hashtbl.find offset_max_variable_table t
    with Not_found ->
      let va = Var.of_string ("__jc_offset_max_" ^ (term_name t)) in
      Hashtbl.add offset_max_variable_table t va;
      let st = match ty with
	| JCTpointer(st,_,_) -> st
	| _ -> assert false
      in
      let tmax = type_term (JCToffset(Offset_max,t,st)) integer_type in
      Hashtbl.add term_table va tmax;
      va

  let strlen_variable t =
    let t = deep_raw_term t in
    try
      Hashtbl.find strlen_variable_table t
    with Not_found ->
      let va = Var.of_string ("__jc_strlen_" ^ (term_name t)) in
      Hashtbl.add strlen_variable_table t va;
      let tstr = type_term (JCTapp(strlen_f,[t])) integer_type in
      Hashtbl.add term_table va tstr;
      va

  let all_variables t =
    (if has_variable t then [variable t] else [])
    @ (if has_offset_min_variable t then [offset_min_variable t] else [])
    @ (if has_offset_max_variable t then [offset_max_variable t] else [])
    @ (if has_strlen_variable t then [strlen_variable t] else [])

  let term va = Hashtbl.find term_table va

  let variable_of_term t =
    match t.jc_term_node with
    | JCTvar _ | JCTderef _ -> variable t
    | JCToffset(Offset_min,t,_) ->
	begin match t.jc_term_node with
	| JCTvar vi -> offset_min_variable t
	| _ -> assert false
	end
    | JCToffset(Offset_max,t,_) ->
	begin match t.jc_term_node with
	| JCTvar vi -> offset_max_variable t
	| _ -> assert false
	end
    | JCTapp(f,[t]) ->
	if f.jc_logic_info_name = "strlen" then
	  strlen_variable t
	else assert false
    | _ -> assert false

  let is_strlen_variable va = 
    match (term va).jc_term_node with
    | JCTapp(f,[t]) ->
	f.jc_logic_info_name = "strlen"
    | _ -> false

end      


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

let raw_not_asrt = not_asrt

let rec linearize t =
  match t.jc_term_node with
  | JCTconst c ->
      begin match c with
      | JCCinteger s -> ([], int_of_string s)
      | JCCboolean _ | JCCvoid | JCCnull | JCCreal _ ->
	  failwith "Not linear"
      end
  | JCTvar _ | JCTderef _ ->
      ([deep_raw_term t,1],0)
  | JCTbinary(t1,bop,t2) ->
      if is_arithmetic_binary_op bop then
	let coeffs1, cst1 = linearize t1 in
	let coeffs2, cst2 = linearize t2 in
        begin match bop with
	| Badd_int ->
	    let coeffs = 
	      List.fold_right (fun (vt1, c1) acc ->
		try 
		  let c2 = List.assoc vt1 coeffs2 in
		  (vt1, c1 + c2) :: acc
		with Not_found -> (vt1, c1) :: acc) 
		coeffs1 []
	    in
	    let coeffs = 
	      List.fold_right (fun (vt2, c2) acc ->
		if List.mem_assoc vt2 coeffs then acc
		else (vt2, c2) :: acc) 
		coeffs2 coeffs
	    in
	    (coeffs, cst1 + cst2)
	| Bsub_int ->
	    let coeffs = 
	      List.fold_right (fun (vt1,c1) acc ->
		try 
		  let c2 = List.assoc vt1 coeffs2 in
		  (vt1,c1 - c2) :: acc
		with Not_found -> (vt1,c1) :: acc
	      ) coeffs1 []
	    in
	    let coeffs = 
	      List.fold_right (fun (vt2,c2) acc ->
		if List.mem_assoc vt2 coeffs then acc
		else (vt2,- c2) :: acc
	      ) coeffs2 coeffs
	    in
	    (coeffs,cst1 - cst2)
	| Bmul_int ->
	    begin match coeffs1,cst1,coeffs2,cst2 with
	    | [],_,[],_ -> ([],cst1 * cst2)
	    | [],cstmul,coeffs,cstadd | coeffs,cstadd,[],cstmul -> 
		let coeffs = 
		  List.map (fun (vt,c) -> (vt,c * cstmul)) coeffs
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
	    let coeffs = List.map (fun (vt,c) -> (vt,-c)) coeffs1 in
	    (coeffs,- cst1)
	| Uplus_real | Uminus_real ->
	    failwith "Not integer"
	| _ -> assert false
	end
      else failwith "Not linear"
  | JCToffset(_,vt,_) ->
      begin match vt.jc_term_node with
      | JCTvar vi -> ([t,1],0)
      | _ -> assert false
      end
  | JCTapp(f,_) ->
      if f.jc_logic_info_name = "strlen" then
	([t,1],0)
      else failwith "Not linear"
  | JCTshift _ | JCTsub_pointer _ | JCTinstanceof _
  | JCTold _ | JCTcast _ | JCTrange _ | JCTif _ -> 
      failwith "Not linear"

let linstr_of_term env t =
  let mkmulstr = function
    | (va, 0) -> ""
    | (va, c) -> string_of_int c ^ " * " ^ va 
  in
  let rec mkaddstr = function
    | [] -> ""
    | [va,c] -> mkmulstr (va,c)
    | (va,c) :: r -> 
	match mkmulstr (va,c), mkaddstr r with
	| "","" -> ""
	| s,"" | "",s -> s
	| s1,s2 -> s1 ^ " + " ^ s2
  in
  try
    let coeffs, cst = linearize t in
    let coeffs = 
      List.map (fun (t,c) ->
	let va = Vai.variable_of_term t in
	if Environment.mem_var env va then (Var.to_string va,c)
	else failwith "Not in environment"
      ) coeffs 
    in
    Some (mkaddstr coeffs, cst)
  with Failure _ -> None

let offset_min_linstr_of_term env t =
  match destruct_pointer t with
  | None,_ -> None
  | Some vi,offt ->
      let vt = raw_term(JCTvar vi) in
      let st = match vi.jc_var_info_type with
	| JCTpointer(st,_,_) -> st
	| _ -> assert false
      in
      let mint = raw_term(JCToffset(Offset_min,vt,st)) in
      let t = match offt with 
	| None -> mint
	| Some offt -> raw_term(JCTbinary(mint,Badd_int,offt)) 
      in
      linstr_of_term env t
      
let offset_max_linstr_of_term env t =
  match destruct_pointer t with
  | None,_ -> None
  | Some vi,offt ->
      let vt = raw_term(JCTvar vi) in
      let st = match vi.jc_var_info_type with
	| JCTpointer(st,_,_) -> st
	| _ -> assert false
      in
      let maxt = raw_term(JCToffset(Offset_max,vt,st)) in
      let t = match offt with 
	| None -> maxt
	| Some offt -> raw_term(JCTbinary(maxt,Bsub_int,offt)) 
      in
      linstr_of_term env t

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
	  (* Do not use <= and >= with APRON. Convert to equivalent strict. *)
	  match bop with
	    (* Begin old version - Nicolas *)
	    (* in cousot76.jc wrong invariant generated (i.e. i >= 102 instead of 101) *)
	    (* | Blt_int -> str ^ " < " ^ cstr
	       | Bgt_int -> str ^ " > " ^ cstr
	       | Ble_int -> str ^ " < " ^ (string_of_int ((- cst) + 1))
	       | Bge_int -> str ^ " > " ^ (string_of_int ((- cst) - 1)) *)
	    (* End old version - Nicolas *)
	    (* Begin new version - Nicolas *)
	  | Blt_int -> str ^ " <= " ^ (string_of_int ((- cst) - 1))
	  | Bgt_int -> str ^ " >= " ^ (string_of_int ((- cst) + 1))
	  | Ble_int -> str ^ " <= " ^ cstr
	  | Bge_int -> str ^ " >= " ^ cstr
	   (* End new version - Nicolas *)
	  | Beq_int -> str ^ " = " ^ cstr
	  | Blt_real | Bgt_real | Ble_real | Bge_real -> ""
	  | Beq_real | Beq_pointer -> ""
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

let linstr_of_expr env e = 
  match term_of_expr e with
  | None -> None
  | Some t ->
      match linstr_of_term env t with
      | None -> None
      | Some ("",cst) -> Some (string_of_int cst)
      | Some (str,cst) -> Some (str ^ " + " ^ (string_of_int cst))

let offset_min_linstr_of_expr env e = 
  match term_of_expr e with
  | None -> None
  | Some t -> 
      match offset_min_linstr_of_term env t with
      | None -> None
      | Some ("",cst) -> Some (string_of_int cst)
      | Some (str,cst) -> Some (str ^ " + " ^ (string_of_int cst))
	
let offset_max_linstr_of_expr env e =
  match term_of_expr e with
  | None -> None
  | Some t -> 
      match offset_max_linstr_of_term env t with
      | None -> None
      | Some ("",cst) -> Some (string_of_int cst)
      | Some (str,cst) -> Some (str ^ " + " ^ (string_of_int cst))

let is_null_term t = 
  match t.jc_term_node with
  | JCTconst (JCCinteger "0") -> true
  | _ -> false

let rec strlen_linstr_of_assertion env a = 
  match a.jc_assertion_node with
  | JCArelation(t1,(Bneq_int | Beq_int as op),t2) ->
      if is_null_term t2 then
	begin match t1.jc_term_node with
	| JCTderef(t1,_) -> 
	    begin match destruct_pointer t1 with
	    | None,_ -> None
	    | Some vi,offt ->
		let vit = var_term vi in
		let va = Vai.strlen_variable vit in
		let env = 
		  if Environment.mem_var env va then env
		  else Environment.add env [|va|] [||] 
		in 
		let strt = Vai.term va in
		let t = match offt with 
		  | None -> strt
		  | Some offt -> raw_term(JCTbinary(strt,Bsub_int,offt)) 
		in
		match linstr_of_term env t with
		| None -> None
		| Some ("",_) -> assert false
		| Some (str,cst) ->
		    match op with
		    | Bneq_int -> 
			let stra = str ^ " > " ^ (string_of_int (- cst)) in
			Some (stra,env)
		    | Beq_int -> 
			let stra = str ^ " = " ^ (string_of_int (- cst)) in
			Some (stra,env)
		    | _ -> assert false
	    end
	| _ -> None
	end
      else None
  | JCAnot a ->
      let nota = not_asrt a in
      begin match nota.jc_assertion_node with
      | JCAnot _ -> None
      | _ -> strlen_linstr_of_assertion env nota
      end
  | _ -> None


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
	      let t = type_term tnode integer_type in
	      Some t
	  | s -> 
	      let ctnode = JCTconst (JCCinteger s) in
	      let ct = type_term ctnode integer_type in
	      let tnode = JCTbinary (ct, Bmul_int, Vai.term va) in
	      let t = type_term tnode integer_type in
	      Some t
	in
	begin match t,vt with
	| None,vt -> vt
	| t,None -> t
	| Some t,Some vt ->
	    let tnode = JCTbinary (t, Badd_int, vt) in
	    let t = type_term tnode integer_type in
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
	    let ct = type_term ctnode integer_type in
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
  let t2 = type_term (JCTconst c2) integer_type in
  raw_asrt (JCArelation(t1,op,t2)) 

let presentify a =
  let rec linterms_of_term t =
    let mkmulterm = function
      | (t,0) -> None
      | (t,1) -> Some t
      | (t,-1) ->
	  Some(raw_term(JCTunary(Uminus_int,t)))
      | (t,c) ->
	  let c = raw_term(JCTconst(JCCinteger(string_of_int c))) in
	  Some(raw_term(JCTbinary(c,Bmul_int,t)))
    in
    let rec mkaddterm = function
      | [] -> None
      | [t,c] -> mkmulterm (t,c)
      | (t,c) :: r ->
	  match mkmulterm (t,c), mkaddterm r with
	  | None,None -> None
	  | Some t,None | None,Some t -> Some t
	  | Some t1,Some t2 -> Some(raw_term(JCTbinary(t1,Badd_int,t2)))
    in
    try
      let coeffs,cst = linearize t in
      let posl,negl =
	List.fold_right (fun (t,c) (pl,nl) ->
	  if c > 0 then (t,c) :: pl, nl
	  else if c < 0 then pl, (t,-c) :: nl
	  else pl, nl
	) coeffs ([],[])
      in
      let cstt = raw_term(JCTconst(JCCinteger(string_of_int(abs cst)))) in
      let post = match mkaddterm posl with
	| None -> 
	    if cst > 0 then cstt else raw_term(JCTconst(JCCinteger "0"))
	| Some t -> 
	    if cst > 0 then raw_term(JCTbinary(t,Badd_int,cstt)) else t
      in
      let negt = match mkaddterm negl with
	| None ->
	    if cst < 0 then cstt else raw_term(JCTconst(JCCinteger "0"))
	| Some t ->
	    if cst < 0 then raw_term(JCTbinary(t,Badd_int,cstt)) else t
      in
      Some (post,negt)
    with Failure _ -> None
  in
  let rec linasrt_of_assertion a =
    match a.jc_assertion_node with
    | JCArelation(t1,bop,t2) ->
	let subt = raw_term (JCTbinary(t1,Bsub_int,t2)) in
	begin match linterms_of_term subt with
	| None -> a
	| Some (post,negt) -> raw_asrt(JCArelation(post,bop,negt))
	end
    | JCAnot a ->
	let nota = not_asrt a in
	begin match nota.jc_assertion_node with
	| JCAnot _ -> a
	| _ -> linasrt_of_assertion nota
	end
    | JCAtrue | JCAfalse | JCAand _ | JCAor _ | JCAimplies _ | JCAiff _
    | JCAapp _ | JCAquantifier _ | JCAold _ | JCAinstanceof _ | JCAbool_term _
    | JCAif _ | JCAmutable _ | JCAtagequality _ -> a
  in
  linasrt_of_assertion a

let mkinvariant mgr absval =
  if Abstract1.is_top mgr absval = Manager.True then
    raw_asrt JCAtrue    
  else if Abstract1.is_bottom mgr absval = Manager.True then
    raw_asrt JCAfalse
  else
    let linconsarr = Abstract1.to_lincons_array mgr absval in
    let rec mkrec acc i = 
      if i >= 0 then
	mkrec (mkassertion (Lincons1.array_get linconsarr i) :: acc) (i-1)
      else acc
    in
    let asserts = mkrec [] (Lincons1.array_length linconsarr - 1) in
    make_and (List.map presentify asserts)


(*****************************************************************************)
(* Performing abstract interpretation.                                       *)
(*****************************************************************************)

let assignment mgr pre t e =
  let env = Abstract1.env pre in
  let forget_vars, vars, linexprs = 
    if Vai.has_variable t then
      let va = Vai.variable t in
      if Environment.mem_var env va then
	match linstr_of_expr env e with
	| None -> [va], [], []
	| Some str ->
	    let lin = 
	      try Parser.linexpr1_of_string env str
	      with Parser.Error _ -> assert false
	    in
	    [], [va], [lin]
      else [], [], []
    else [], [], []
  in
  let forget_vars, vars,linexprs = 
    if Vai.has_offset_min_variable t then
      let va = Vai.offset_min_variable t in
      if Environment.mem_var env va then
	match offset_min_linstr_of_expr env e with
	| None -> [va], [], []
	| Some str ->
	    let lin = 
	      try Parser.linexpr1_of_string env str
	      with Parser.Error msg -> printf "%s@." msg; assert false
	    in
	    forget_vars, va :: vars, lin :: linexprs
      else forget_vars, vars, linexprs
    else forget_vars, vars, linexprs
  in
  let forget_vars, vars,linexprs = 
    if Vai.has_offset_max_variable t then
      let va = Vai.offset_max_variable t in
      if Environment.mem_var env va then
	match offset_max_linstr_of_expr env e with
	| None -> [va], [], []
	| Some str ->
	    let lin = 
	      try Parser.linexpr1_of_string env str
	      with Parser.Error _ -> assert false
	    in
	    forget_vars, va :: vars, lin :: linexprs
      else forget_vars, vars, linexprs
    else forget_vars, vars, linexprs
  in
  if vars <> [] then
    begin
      let vars = Array.of_list vars in
      let linexprs = Array.of_list linexprs in
      Abstract1.assign_linexpr_array_with mgr pre vars linexprs None
    end;
  if forget_vars <> [] then
    begin
      let forget_vars = Array.of_list forget_vars in
      Abstract1.forget_array_with mgr pre forget_vars false
    end;
  pre

let test_assertion mgr pre a =
  let env = Abstract1.env pre in
  let be = linstr_of_assertion env a in
  let bemin = offset_min_linstr_of_assertion env a in
  let bemax = offset_max_linstr_of_assertion env a in
  let bestr,env = match strlen_linstr_of_assertion env a with
    | None -> "",env
    | Some strenv -> strenv
  in
  if be = "false" || bemin = "false" || bemax = "false" || bestr = "false" then
    Abstract1.bottom mgr (Abstract1.env pre)
  else
    let cstrs = 
      (if be = "true" || be = "" then [] else [be])
      @ (if bemin = "true" || bemin = "" then [] else [bemin])
      @ (if bemax = "true" || bemax = "" then [] else [bemax])
      @ (if bestr = "true" || bestr = "" then [] else [bestr])
    in
    if cstrs = [] then 
      pre
    else
      let lincons = 
	try Parser.lincons1_of_lstring env cstrs 
	with Parser.Error _ -> assert false
      in
      let envprint = Environment.print ~first:"[" ~sep:"," ~last:"]" in
      if Jc_options.debug then
	printf "pre.env = %a@.lincons.env = %a@." 
	  envprint (Abstract1.env pre)
	  envprint (Lincons1.array_get_env lincons);
      Abstract1.change_environment_with mgr pre env false;
      Abstract1.meet_lincons_array_with mgr pre lincons;
      pre

let test_expr ~(neg:bool) mgr pre e =
  let a = asrt_of_expr e in
  let a = if neg then not_asrt a else a in
  test_assertion mgr pre a

(* Arguments of [join] should be on the same environment. *)
let join mgr absval1 absval2 =
  let env1 = Abstract1.env absval1 in
  let absval2 = Abstract1.change_environment mgr absval2 env1 false in
  Abstract1.join_with mgr absval1 absval2;
  absval1

(* Arguments of [widening] should be on the same environment. *)
let widening mgr absval1 absval2 =
  let env1 = Abstract1.env absval1 in
  let absval2 = Abstract1.change_environment mgr absval2 env1 false in
  (* Join before widening so that arguments are in increasing order. *)
  ignore (join mgr absval2 absval1);
  Abstract1.widening mgr absval1 absval2 (* no destructive version *)

let join_invariants mgr invs1 invs2 =
  if Jc_options.debug then
    printf "@[<v 2>[join]@\n%a@\nand@\n%a@]@." 
      print_abstract_invariants invs1 print_abstract_invariants invs2;
  let join_exclists postexcl1 postexcl2 =
    let join1 = List.fold_right (fun (ei,post1) acc ->
      try
	let post2 = List.assoc ei postexcl2 in
	(ei, join mgr post1 post2) :: acc
      with Not_found -> (ei,post1) :: acc
    ) postexcl1 []
    in
    List.fold_right (fun (ei,post2) acc ->
      if List.mem_assoc ei join1 then acc 
      else (ei, post2) :: acc
    ) postexcl2 join1
  in
  {
    jc_absinv_normal =
      join mgr invs1.jc_absinv_normal invs2.jc_absinv_normal;
    jc_absinv_exceptional =
      join_exclists invs1.jc_absinv_exceptional invs2.jc_absinv_exceptional;
    jc_absinv_return = 
      join mgr invs1.jc_absinv_return invs2.jc_absinv_return;
  }

let widen_invariants mgr invs1 invs2 =
  if Jc_options.debug then
    printf "@[<v 2>[widening]@\n%a@\nand@\n%a@]@." 
      print_abstract_invariants invs1 print_abstract_invariants invs2;
  let widen_exclists postexcl1 postexcl2 =
    let widen1 = List.fold_right (fun (ei,post1) acc ->
      try
	let post2 = List.assoc ei postexcl2 in
	(ei, widening mgr post1 post2) :: acc
      with Not_found -> (ei,post1) :: acc
    ) postexcl1 []
    in
    List.fold_right (fun (ei,post2) acc ->
      if List.mem_assoc ei widen1 then acc 
      else (ei, post2) :: acc
    ) postexcl2 widen1
  in
  {
    jc_absinv_normal =
      widening mgr invs1.jc_absinv_normal invs2.jc_absinv_normal;
    jc_absinv_exceptional =
      widen_exclists invs1.jc_absinv_exceptional invs2.jc_absinv_exceptional;
    jc_absinv_return = 
      widening mgr invs1.jc_absinv_return invs2.jc_absinv_return;
  }

let eq_invariants mgr invs1 invs2 =
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
  Abstract1.is_eq mgr invs1.jc_absinv_normal invs2.jc_absinv_normal =
  Manager.True
    && eq_exclists invs1.jc_absinv_exceptional invs2.jc_absinv_exceptional
    && Abstract1.is_eq mgr invs1.jc_absinv_return invs2.jc_absinv_return =
  Manager.True

let copy_invariants mgr invs = { 
  jc_absinv_normal = Abstract1.copy mgr invs.jc_absinv_normal;
  jc_absinv_exceptional = 
  List.map (fun (ei,post) -> (ei,Abstract1.copy mgr post)) 
    invs.jc_absinv_exceptional;
  jc_absinv_return = Abstract1.copy mgr invs.jc_absinv_return;
}

let rec ai_expression abs curinvs e =
  let expr = ai_expression abs in
  let mgr = abs.jc_absint_manager in
  match e.jc_expr_node with
  | JCEconst _ | JCEvar _ | JCErange_cast _ -> 
      curinvs
  | JCEbinary(e1,_,e2) | JCEshift(e1,e2) | JCEsub_pointer(e1,e2) ->
      expr (expr curinvs e1) e2
  | JCEunary(_,e1) | JCEinstanceof(e1,_) | JCEcast(e1,_) | JCEoffset(_,e1,_) 
  | JCEalloc(e1,_) | JCEfree e1 -> 
      expr curinvs e1
  | JCEif(e1,e2,e3) -> 
      expr (expr (expr curinvs e1) e2) e3
  | JCEderef(e1,fi) ->
      let curinvs = expr curinvs e1 in
      begin match term_of_expr e1 with
      | None -> curinvs
      | Some t1 ->
	  match destruct_pointer t1 with
	  | None,_ -> curinvs
	  | Some vi,offt ->
	      let offt = match offt with
		| None -> raw_term(JCTconst(JCCinteger "0"))
		| Some offt -> offt
	      in
	      let vt = raw_term(JCTvar vi) in
	      let st = match vi.jc_var_info_type with
		| JCTpointer(st,_,_) -> st
		| _ -> assert false
	      in
	      let mint = raw_term(JCToffset(Offset_min,vt,st)) in
	      let maxt = raw_term(JCToffset(Offset_max,vt,st)) in
	      let mina = raw_asrt(JCArelation(mint,Ble_int,offt)) in
	      let maxa = raw_asrt(JCArelation(offt,Ble_int,maxt)) in
	      let pre = curinvs.jc_absinv_normal in
	      let pre = test_assertion mgr pre mina in
	      let pre = test_assertion mgr pre maxa in
	      { curinvs with jc_absinv_normal = pre; }
      end

let find_target_assertions targets s =
  List.fold_left 
    (fun acc target -> 
      if target.jc_target_statement == s then target::acc else acc
    ) [] targets
    
let rec ai_statement abs curinvs s =
  let mgr = abs.jc_absint_manager in
  let targets = find_target_assertions abs.jc_absint_target_assertions s in
  List.iter (fun target ->
    target.jc_target_invariant <- mkinvariant mgr curinvs.jc_absinv_normal
  ) targets;
  let env = abs.jc_absint_function_environment in
  let pre = curinvs.jc_absinv_normal in
  let postexcl = curinvs.jc_absinv_exceptional in
  let postret = curinvs.jc_absinv_return in
  match s.jc_statement_node with
  | JCSdecl (vi, eo, s) ->
      let vit = var_term vi in
      let vars = Vai.all_variables vit in
      let env = 
	Environment.add (Abstract1.env pre) (Array.of_list vars) [||] 
      in 
      Abstract1.change_environment_with mgr pre env false;
      let pre = match eo with
	| None -> pre
        | Some e -> assignment mgr pre vit e
      in
      let curinvs = { curinvs with jc_absinv_normal = pre; } in
      ai_statement abs curinvs s
  | JCSassign_var (vi, e) ->
      let vit = var_term vi in
      { curinvs with jc_absinv_normal = assignment mgr pre vit e; }
  | JCSassign_heap(e1,fi,e2) ->
      begin match term_of_expr e1 with
      | None -> curinvs (* TODO *)
      | Some t1 ->
	  let dereft = 
	    type_term (JCTderef(t1,fi)) fi.jc_field_info_type
	  in
	  let vars = Vai.all_variables dereft in
	  let env = Abstract1.env pre in
	  let vars = 
	    List.filter (fun va -> not (Environment.mem_var env va)) vars
	  in
	  begin if vars != [] then
	    let env = 
	      Environment.add env (Array.of_list vars) [||] 
	    in 
	    Abstract1.change_environment_with mgr pre env false
	  end;
	  { curinvs with jc_absinv_normal = assignment mgr pre dereft e2; }
      end
  | JCSassert(_,a) ->
      { curinvs with jc_absinv_normal = test_assertion mgr pre a; }
  | JCSblock sl ->
      List.fold_left (ai_statement abs) curinvs sl
  | JCSif (e, ts, fs) ->
      let copyinvs = copy_invariants mgr curinvs in
      let tpre = test_expr ~neg:false mgr pre e in
      let tinvs = { curinvs with jc_absinv_normal = tpre; } in
      let tinvs = ai_statement abs tinvs ts in
      let copy_pre = copyinvs.jc_absinv_normal in
      let fpre = test_expr ~neg:true mgr copy_pre e in
      let finvs = { copyinvs with jc_absinv_normal = fpre; } in
      let finvs = ai_statement abs finvs fs in
      join_invariants mgr tinvs finvs
  | JCSreturn_void ->
      let pre = Abstract1.bottom mgr (Abstract1.env pre) in
      let postret = Abstract1.top mgr env in
      { curinvs with jc_absinv_normal = pre; jc_absinv_return = postret; }
  | JCSreturn(_,e) ->
      let pre = Abstract1.bottom mgr (Abstract1.env pre) in
      let postret = join mgr postret pre in
      { curinvs with jc_absinv_normal = pre; jc_absinv_return = postret; }
  | JCSthrow(ei,_) ->
      let bot = Abstract1.bottom mgr (Abstract1.env pre) in
      let postexc = pre in 
      (* TODO: add thrown value as abstract variable. *)
      let postexc =
	try join mgr (List.assoc ei postexcl) postexc
	with Not_found -> postexc
      in
      let postexcl = (ei, postexc) :: (List.remove_assoc ei postexcl) in
      { curinvs with jc_absinv_normal = bot; jc_absinv_exceptional = postexcl; }
  | JCSpack _ | JCSunpack _ ->
      curinvs
  | JCStry(s,hl,fs) ->
      let curinvs = ai_statement abs curinvs s in
      let postexcl = curinvs.jc_absinv_exceptional in
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
	      let postret = Abstract1.bottom mgr env in
	      let excinvs = {
		jc_absinv_normal = postexc;
		jc_absinv_exceptional = [];
		jc_absinv_return = postret;
	      } in
	      let excinvs = ai_statement abs excinvs s in
	      join_invariants mgr curinvs excinvs
	    with Not_found -> curinvs
	  ) { curinvs with jc_absinv_exceptional = curpostexcl; } hl
      in
      (* BAD: ai_statement abs curinvs fs *)
      begin match fs.jc_statement_node with 
      | JCSblock [] -> curinvs
      | _ -> assert false (* TODO: apply finally stmt to all paths. *)
      end
  | JCSloop (la, ls) ->
      let loop_invariants = abs.jc_absint_loop_invariants in
      let loop_iterations = abs.jc_absint_loop_iterations in
      let num = 
	try Hashtbl.find loop_iterations la.jc_loop_tag 
	with Not_found -> 0
      in
      Hashtbl.replace loop_iterations la.jc_loop_tag (num + 1);
      if num < abs.jc_absint_widening_threshold then
	let nextinvs = ai_statement abs (copy_invariants mgr curinvs) ls in
(* Begin hack - Nicolas *)
(* sufficient to infer most *simple* loop invariant (see cousot76.jc, loop.jc, etc.) *)
	let wideninvs = widen_invariants mgr curinvs nextinvs in
	let nextinvs = ai_statement abs (copy_invariants mgr wideninvs) ls in
(* End hack - Nicolas *)
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
(* 	  ai_statement abs (copy_invariants mgr wideninvs) s *)
	  (* Propagate to assertions. *)
	  let copyinvs = copy_invariants mgr wideninvs in
	  let bot = Abstract1.bottom mgr (Abstract1.env pre) in
	  { copyinvs with jc_absinv_normal = bot; }
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
	let loopinvs = Hashtbl.find loop_invariants la.jc_loop_tag in
	let loopinv = loopinvs.jc_absinv_normal in
	(* Abstract1.minimize mgr loopinv; NOT IMPLEMENTED IN APRON *)
	if Abstract1.is_top mgr loopinv = Manager.True then
	  ()
	else if Abstract1.is_bottom mgr loopinv = Manager.True then
	  la.jc_loop_invariant <- raw_asrt JCAfalse
	else
	  let a = mkinvariant mgr loopinv in
	  if Jc_options.verbose then
	    printf 
	      "%a@[<v 2>Inferring loop invariant@\n%a@]@."
	      Loc.report_position s.jc_statement_loc
	      Jc_output.assertion a;
	  la.jc_loop_invariant <- make_and [la.jc_loop_invariant; a]
      with Not_found -> () end
  | JCSassign_var _ | JCSassign_heap _ | JCSassert _ 
  | JCSreturn_void | JCSreturn _ | JCSthrow _ | JCSpack _ | JCSunpack _ 
  | JCScall _ ->
      ()

let ai_function mgr targets (fi, fs, sl) =
  try
    let env = Environment.make [||] [||] in
    
    (* Add global variables as abstract variables in [env]. *)
    let globvars =
      Hashtbl.fold (fun _ (vi, _) acc -> Vai.all_variables(var_term vi) @ acc)
	Jc_norm.variables_table []
    in
    let env = Environment.add env (Array.of_list globvars) [||] in
    
    (* Add parameters as abstract variables in [env]. *)
    let params =
      List.fold_left (fun acc vi -> Vai.all_variables(var_term vi) @ acc)
	[] fi.jc_fun_info_parameters
    in
    let env = Environment.add env (Array.of_list params) [||] in

    let abs = { 
      jc_absint_manager = mgr;
      jc_absint_function_environment = env;
      jc_absint_function_name = fi.jc_fun_info_name;
      jc_absint_widening_threshold = 1;
      jc_absint_loop_invariants = Hashtbl.create 0;
      jc_absint_loop_iterations = Hashtbl.create 0;
      jc_absint_target_assertions = targets;
    } in
    
    (* TODO: add \return as abstract variable. *)

    (* add parameters specs *)
    let cstrs =
      List.fold_left
 	(fun acc vi -> match vi.jc_var_info_type with
 	| JCTpointer(st,n1opt,n2opt) ->
 	    let vt = raw_term(JCTvar vi) in
 	    let mincstr = match n1opt with
	      | None -> []
	      | Some n1 ->
 		  let mint = raw_term (JCToffset(Offset_min,vt,st)) in
 		  let n1t =
 		    raw_term (JCTconst(JCCinteger(Num.string_of_num n1)))
 		  in
 		  let mina = raw_asrt (JCArelation(mint,Ble_int,n1t)) in
 		  [mina]
 	    in
 	    let maxcstr = match n2opt with
	      | None -> []
	      | Some n2 ->
 		  let maxt = raw_term (JCToffset(Offset_max,vt,st)) in
 		  let n2t =
 		    raw_term (JCTconst(JCCinteger(Num.string_of_num n2)))
 		  in
 		  let maxa = raw_asrt (JCArelation(n2t,Ble_int,maxt)) in
 		  [maxa]
 	    in
 	    mincstr @ maxcstr @ acc
 	| _ -> acc
 	) [] fi.jc_fun_info_parameters
     in
     let cstrs = List.map (linstr_of_assertion env) cstrs in
     let lincons = Parser.lincons1_of_lstring env cstrs in
     let initpre = Abstract1.top mgr env in
     Abstract1.meet_lincons_array_with mgr initpre lincons;

    (* Annotation inference on the function body. *)
    let initinvs = {
      jc_absinv_normal = initpre;
      jc_absinv_exceptional = [];
      jc_absinv_return = Abstract1.bottom mgr env;
    } in
    ignore (List.fold_left (ai_statement abs) initinvs sl);
    List.iter (record_invariants abs) sl;
    List.iter 
      (fun target -> 
	if Jc_options.verbose then
	  printf 
	    "%a@[<v 2>Inferring assert invariant@\n%a@]@."
	    Loc.report_position target.jc_target_location
	    Jc_output.assertion target.jc_target_invariant 
      ) targets
      
  with Manager.Error exc ->
    Manager.print_exclog std_formatter exc;
    printf "@."


(*****************************************************************************)
(* From terms and assertions to ATP formulas and the opposite way.           *)
(*****************************************************************************)

module Vwp : sig

  val variable : term -> string
  val offset_min_variable : term -> struct_info -> string
  val offset_max_variable : term -> struct_info -> string
  val strlen_variable : term -> string

  val term : string -> term

end = struct

  let variable_table = Hashtbl.create 0
  let offset_min_variable_table = Hashtbl.create 0
  let offset_max_variable_table = Hashtbl.create 0
  let strlen_variable_table = Hashtbl.create 0
  let term_table = Hashtbl.create 0

  let variable t = 
    let t1 = deep_raw_term t in
    let s = term_name t1 in
    begin try 
      let t2 = Hashtbl.find variable_table s in
      assert (t1 = t2)
    with Not_found ->
      Hashtbl.add variable_table s t1;
      Hashtbl.add term_table s t
    end;
    s

  let offset_min_variable t st = 
    let t1 = deep_raw_term t in
    let s = "__jc_offset_min_" ^ (term_name t1) in
    begin try 
      let t2 = Hashtbl.find offset_min_variable_table s in
      assert (t1 = t2)
    with Not_found ->
      Hashtbl.add offset_min_variable_table s t1;
      let tmin = type_term (JCToffset(Offset_min,t,st)) integer_type in
      Hashtbl.add term_table s tmin
    end;
    s

  let offset_max_variable t st = 
    let t1 = deep_raw_term t in
    let s = "__jc_offset_max_" ^ (term_name t1) in
    begin try 
      let t2 = Hashtbl.find offset_max_variable_table s in
      assert (t1 = t2)
    with Not_found ->
      Hashtbl.add offset_max_variable_table s t1;
      let tmax = type_term (JCToffset(Offset_max,t,st)) integer_type in
      Hashtbl.add term_table s tmax
    end;
    s

  let strlen_variable t = 
    let t1 = deep_raw_term t in
    let s = "__jc_strlen_" ^ (term_name t1) in
    begin try 
      let t2 = Hashtbl.find strlen_variable_table s in
      assert (t1 = t2)
    with Not_found ->
      Hashtbl.add strlen_variable_table s t1;
      let tmax = type_term (JCTapp(strlen_f,[t])) integer_type in
      Hashtbl.add term_table s tmax
    end;
    s

  let term s = Hashtbl.find term_table s

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

let rec free_variables t =
  fold_term
    (fun acc t -> match t.jc_term_node with
    | JCTvar vi ->
	VarSet.add vi acc
    | _ -> acc
    ) VarSet.empty t

let rec atp_of_term t = 
  match t.jc_term_node with
  | JCTconst c ->
      begin match c with
      | JCCinteger s -> 
	  Atp.Fn(s,[])
      | JCCboolean _ | JCCvoid | JCCnull | JCCreal _ -> 
	  assert false
      end
  | JCTvar _ | JCTderef _ ->
      Atp.Var (Vwp.variable t)
  | JCTbinary(t1,bop,t2) ->
      Atp.Fn(atp_arithmetic_of_binop bop, List.map atp_of_term [t1;t2])
  | JCTunary(uop,t1) ->
      Atp.Fn(Jc_output.unary_op uop, [atp_of_term t1])
  | JCToffset(Offset_min,t,st) ->
      Atp.Var (Vwp.offset_min_variable t st)
  | JCToffset(Offset_max,t,st) ->
      Atp.Var (Vwp.offset_max_variable t st)
  | JCTapp(f,[t]) ->
      if f.jc_logic_info_name = "strlen" then
	Atp.Var (Vwp.strlen_variable t)
      else assert false
  | JCTapp _ -> 
      assert false
  | JCTshift _ | JCTsub_pointer _ | JCTold _
  | JCTinstanceof _ | JCTcast _ | JCTif _ | JCTrange _ ->
      assert false

let rec term_of_atp tm =
  let tnode = match tm with
    | Atp.Var s -> 
	(Vwp.term s).jc_term_node
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
  | JCAquantifier(q,vi,a) ->
      let f = atp_of_asrt a in
      let fvars = Atp.fv f in
      let varsets = List.map (fun v -> free_variables (Vwp.term v)) fvars in
      let vars = List.fold_left2
	(fun acc va vs -> 
	  if VarSet.mem vi vs then StringSet.add va acc else acc) 
	(StringSet.singleton vi.jc_var_info_name) fvars varsets
      in
      let vars = StringSet.elements vars in
      let rec quant f = function
	| [] -> f
	| v::r -> 
	    match q with 
	    | Forall -> quant (Atp.Forall(v,f)) r
	    | Exists -> quant (Atp.Exists(v,f)) r
      in
      quant f vars
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
    | Atp.Forall _ | Atp.Exists _ -> assert false
  in
  raw_asrt anode


(*****************************************************************************)
(* Computing weakest preconditions.                                          *)
(*****************************************************************************)

let is_function_level posts =
  List.length posts.jc_post_modified_vars = 1

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

let rec wp_statement = 
  let var_of_term = Hashtbl.create 0 in
  (* Terms should be raw only. *)
  let unique_var_for_term t ty =
    try Hashtbl.find var_of_term t
    with Not_found ->
      let vi = var ty (term_name t) in
      Hashtbl.add var_of_term t vi;
      vi
  in
  fun target s curposts ->
    if s == target.jc_target_statement then
      let a = raw_asrt(JCAimplies(target.jc_target_invariant,
                                  target.jc_target_assertion)) in
      { curposts with jc_post_normal = Some (deep_raw_asrt a); }
    else match s.jc_statement_node with
    | JCSdecl(vi,eo,s) ->
	let curposts = wp_statement target s curposts in
	let post = match curposts.jc_post_normal with
	  | None -> None
	  | Some a -> 
	      let a = match eo with
		| None -> a
		| Some e ->
		    match raw_term_of_expr e with
		    | None -> a
		    | Some t2 ->
			let t1 = raw_term (JCTvar vi) in
			let bop = 
			  equality_operator_for_type vi.jc_var_info_type in
			let eq = raw_asrt (JCArelation(t1,bop,t2)) in
			raw_asrt (JCAimplies(eq,a))
	      in
	      Some (raw_asrt (JCAquantifier(Forall,vi,a)))
	in
	let curposts = remove_modified_var curposts vi in
	{ curposts with jc_post_normal = post; }
    | JCSassign_var(vi,e) ->
	let vit = raw_term(JCTvar vi) in
	let copyvi = copyvar vi in
	let post = match curposts.jc_post_normal with
	  | None -> None
	  | Some a -> 
	      let a = replace_term_in_assertion vit copyvi a in
	      match raw_term_of_expr e with
	      | None -> Some a
	      | Some t2 ->
		  let t1 = raw_term (JCTvar copyvi) in
		  let bop = equality_operator_for_type vi.jc_var_info_type in
		  let eq = raw_asrt (JCArelation(t1,bop,t2)) in
		  Some (raw_asrt (JCAimplies(eq,a)))
	in
	let curposts = add_modified_var curposts copyvi in
	let curposts = 
	  if is_function_level curposts then curposts
	  else
	    (* Also add regular variable, for other branches in loop. *)
	    add_modified_var curposts vi 
	in
	{ curposts with jc_post_normal = post; }
    | JCSassign_heap(e1,fi,e2) ->
	begin match raw_term_of_expr e1 with
	| None -> curposts (* TODO *)
	| Some t1 ->
	    let dereft = raw_term (JCTderef(t1,fi)) in
	    let vi = unique_var_for_term dereft fi.jc_field_info_type in
	    let copyvi = copyvar vi in
	    let post = match curposts.jc_post_normal with
	      | None -> None
	      | Some a -> 
		  let a = replace_term_in_assertion dereft copyvi a in
		  match raw_term_of_expr e2 with
		  | None -> Some a
		  | Some t2 ->
		      let t1 = raw_term (JCTvar copyvi) in
		      let bop = 
			equality_operator_for_type fi.jc_field_info_type in
		      let eq = raw_asrt (JCArelation(t1,bop,t2)) in
		      Some (raw_asrt (JCAimplies(eq,a)))
	    in
	    let curposts = add_modified_var curposts copyvi in
	    let curposts = 
	      if is_function_level curposts then curposts
	      else
		(* Also add regular variable, for other branches in loop. *)
		add_modified_var curposts vi 
	    in
	    { curposts with jc_post_normal = post; }
	end
    | JCSassert(_,a1) ->
	let post = match curposts.jc_post_normal with
	  | None -> None
	  | Some a -> Some (raw_asrt (JCAimplies(a1,a)))
	in
	{ curposts with jc_post_normal = post; }
    | JCSblock sl ->
	List.fold_right (wp_statement target) sl curposts
    | JCSif(e,ts,fs) ->
	let tposts = wp_statement target ts curposts in
	let tpost = match tposts.jc_post_normal with
	  | None -> None
	  | Some a -> 
	      let ta = raw_asrt_of_expr e in
	      Some (raw_asrt (JCAimplies(ta,a)))
	in
	let fposts = wp_statement target fs curposts in
	let fpost = match fposts.jc_post_normal with
	  | None -> None
	  | Some a -> 
	      let fa = raw_not_asrt (raw_asrt_of_expr e) in
	      Some (raw_asrt (JCAimplies(fa,a)))
	in
	let post = match tpost,fpost with
	  | None,opta | opta,None -> opta
	  | Some ta,Some fa -> Some (make_and [ta;fa])
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
	      let excposts = wp_statement target s curposts in
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
	let bodyposts = wp_statement target s tmpposts in
	let bodyvs,_ = pop_modified_vars bodyposts in
	let vs = VarSet.union handlvs bodyvs in
	let curposts = add_modified_vars curposts vs in
	{ curposts with jc_post_normal = bodyposts.jc_post_normal; }
    | JCSloop(la,ls) ->
	let curposts = { curposts with jc_post_normal = None; } in
	let loopposts = push_modified_vars curposts in
	let loopposts = wp_statement target ls loopposts in
	let vs,loopposts = pop_modified_vars loopposts in
	let post = match loopposts.jc_post_normal with
	  | None -> None
	  | Some a ->
	      (* Prefix by loop invariant in left-hand side of implication.*)
	      (*let impl = raw_asrt(JCAimplies(la.jc_loop_invariant,a)) in*)
	      let impl = a in
	      Some (VarSet.fold 
		(fun vi a -> raw_asrt (JCAquantifier(Forall,vi,a))) vs impl)
	in
	{ curposts with jc_post_normal = post; }
    | JCScall(vio,f,args,s) -> 
	curposts

let rec collect_expr_asserts s e =
  let collect = collect_expr_asserts s in
  match e.jc_expr_node with
  | JCEconst _ | JCEvar _ -> []
  | JCEderef(e1,fi) ->
      begin match term_of_expr e1 with
      | None -> []
      | Some t1 ->
	  match destruct_pointer t1 with
	  | None,_ -> []
	  | Some vi,offt ->
	      let offt = match offt with
		| None -> raw_term(JCTconst(JCCinteger "0"))
		| Some offt -> offt
	      in
	      let vt = raw_term(JCTvar vi) in
	      let st = match vi.jc_var_info_type with
		| JCTpointer(st,_,_) -> st
		| _ -> assert false
	      in
	      let mint = raw_term (JCToffset(Offset_min,vt,st)) in
	      let maxt = raw_term (JCToffset(Offset_max,vt,st)) in
	      let mina = raw_asrt (JCArelation(mint,Ble_int,offt)) in
	      let maxa = raw_asrt (JCArelation(offt,Ble_int,maxt)) in
	      [{ 
		jc_target_statement = s;
		jc_target_location = e.jc_expr_loc;
		jc_target_assertion = make_and [mina;maxa];
		jc_target_invariant = raw_asrt JCAfalse;
	      }]
      end
  | JCEbinary(e1,_,e2) | JCEshift(e1,e2) | JCEsub_pointer(e1,e2) -> 
      collect e1 @ (collect e2)
  | JCEunary(_,e1) | JCEinstanceof(e1,_) | JCEcast(e1,_)
  | JCErange_cast(_,e1) | JCEoffset(_,e1,_) | JCEalloc(e1,_) | JCEfree e1 ->
      collect e1
  | JCEif(e1,e2,e3) ->
      collect e1 @ (collect e2) @ (collect e3)

let rec collect_asserts targets s =
  match s.jc_statement_node with
  | JCSdecl(_,Some e,s) -> 
      collect_asserts (collect_expr_asserts s e @ targets) s
  | JCSdecl(_,None,s) -> 
      collect_asserts targets s
  | JCScall(_,_,els,s) ->
      collect_asserts 
	(List.flatten (List.map (collect_expr_asserts s) els) @ targets) s
  | JCSblock sl ->
      List.fold_left collect_asserts targets sl
  | JCSif(e,ts,fs) ->
      collect_asserts (collect_asserts 
	(collect_expr_asserts s e @ targets) ts) fs
  | JCStry(s,hl,fs) ->
      let targets = collect_asserts targets s in
      let targets = 
	List.fold_left (fun targets (_,_,s) -> collect_asserts targets s) targets hl
      in
      collect_asserts targets fs
  | JCSloop(_,ls) ->
      collect_asserts targets ls
  | JCSassert(_,a) ->
      { 
	jc_target_statement = s;
	jc_target_location = s.jc_statement_loc;
	jc_target_assertion = a;
	jc_target_invariant = raw_asrt JCAfalse;
      } :: targets
  | JCSassign_var(_,e1) | JCSreturn(_,e1) | JCSthrow(_,Some e1) 
  | JCSpack(_,e1,_) | JCSunpack(_,e1,_) ->
      collect_expr_asserts s e1 @ targets
  | JCSassign_heap(e1,fi,e2) ->
      let derefe = loc_expr (JCEderef(e1,fi)) s.jc_statement_loc in
      collect_expr_asserts s e1 @ (collect_expr_asserts s derefe)
      @ (collect_expr_asserts s e2) @ targets
  | JCSreturn_void | JCSthrow(_,None) ->
      targets

let simplify =
  let mgr = Polka.manager_alloc_strict () in
  function a ->
    let dnf = Atp.dnf (atp_of_asrt a) in
    let vars = Atp.fv dnf in
    let vars = List.map Vwp.term vars in
    let vars = List.map Vai.variable_of_term vars in
    let env = Environment.make (Array.of_list vars) [||] in
    let disjuncts = Atp.disjuncts dnf in
    let disjuncts = List.map Atp.conjuncts disjuncts in
    let disjuncts = List.map (List.map asrt_of_atp) disjuncts in

    let strlen_vars = List.filter Vai.is_strlen_variable vars in
    let cstrs = List.map (fun va ->
      let zero = raw_term(JCTconst(JCCinteger "0")) in
      raw_asrt(JCArelation(Vai.term va,Bge_int,zero))
    ) strlen_vars in
    let cstrs = List.map (linstr_of_assertion env) cstrs in
    let strlen_lincons = Parser.lincons1_of_lstring env cstrs in

    let abstract_disjuncts,other_disjuncts = 
      List.fold_right (fun conjunct (abstractl,otherl) ->
	try 
	  if Jc_options.debug then
	    printf "asrt conjunct : %a@."
	      (Pp.print_list (fun fmt () -> printf " /\\ ") 
		 Jc_output.assertion)
	      conjunct;
	  let absval = Abstract1.top mgr env in
	  (* Overapproximate conjunct. *)
	  let cstrs = 
	    List.fold_left
	      (fun acc a -> match linstr_of_assertion env a with
	      | "" -> acc (* failwith "Not supported" *)
	      | s ->  s::acc) [] conjunct 
	  in
	  if Jc_options.debug then
	    printf "linstr conjunct : %a@." 
	      (Pp.print_list (fun fmt () -> printf " /\\ ") 
		 (fun fmt s -> print_string s))
	      cstrs;
	  let lincons = 
	    Parser.lincons1_of_lstring env cstrs 
	  in
	  Abstract1.meet_lincons_array_with mgr absval lincons;
	  if Jc_options.debug then
	    printf "abstract conjunct : %a@." Abstract1.print absval;
	  if Abstract1.is_bottom mgr absval = Manager.True then
	    abstractl, otherl
	  else
	    let test_absval = Abstract1.copy mgr absval in
	    Abstract1.meet_lincons_array_with mgr test_absval strlen_lincons;
	    if Abstract1.is_bottom mgr test_absval = Manager.True then
	      abstractl, otherl
	    else
	      absval :: abstractl, otherl
	with Parser.Error _ | Failure _ ->
	  abstractl, make_and (List.map presentify conjunct) :: otherl
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
    make_or disjuncts

let wp_function targets (fi,fs,sl) =
  List.iter (fun target ->
    let initposts = {
      jc_post_normal = None;
      jc_post_exceptional = [];
      jc_post_modified_vars = [];
    } in
    let initposts = push_modified_vars initposts in
    let posts = List.fold_right (wp_statement target) sl initposts in
    let vs,posts = pop_modified_vars posts in
    assert (posts.jc_post_modified_vars = []);
    match posts.jc_post_normal with
    | None -> ()
    | Some a -> 
	let qf = 
	  VarSet.fold (fun vi a -> raw_asrt (JCAquantifier(Forall,vi,a))) vs a
	in
	if Jc_options.debug then
	  printf "@[<v 2>Raw precondition@\n%a@]@." Jc_output.assertion qf; 
	let qf = (atp_of_asrt qf) in
	if Jc_options.debug then
	  printf "@[<v 2>Before quantifier elimination@\n%a@]@." 
	    (fun fmt fm -> Atp.printer fm) qf; 
	let qe = Atp.integer_qelim qf in
	if Jc_options.debug then
	  printf "@[<v 2>After quantifier elimination@\n%a@]@." 
	    (fun fmt fm -> Atp.printer fm) qe; 
	let qe = simplify (asrt_of_atp (Atp.dnf qe)) in
	match qe.jc_assertion_node with
	| JCAfalse ->
	    if Jc_options.verbose then
	      printf "%a@[<v 2>No inferred precondition for function %s@."
		Loc.report_position target.jc_target_location
		fi.jc_fun_info_name
	| _ ->
	    if Jc_options.verbose then
	      printf "%a@[<v 2>Inferring precondition@\n%a@]@\nfor function %s@."
		Loc.report_position target.jc_target_location
		Jc_output.assertion qe fi.jc_fun_info_name ;
	    fs.jc_fun_requires <- make_and [fs.jc_fun_requires; qe]
  ) targets
    

(*****************************************************************************)
(* Main function.                                                            *)
(*****************************************************************************)

let tautology a =
  let qf = Atp.generalize (atp_of_asrt a) in
  let qe = Atp.integer_qelim qf in
  let qe = asrt_of_atp qe in
  match qe.jc_assertion_node with
  | JCAtrue -> true
  | _ -> false

let code_function = function
  | fi,fs,None -> ()
  | fi,fs,Some sl ->
      begin match Jc_options.ai_domain with
      | "box" -> 
	  let mgr = Box.manager_alloc () in
	  ai_function mgr [] (fi,fs,sl)
      | "oct" -> 
	  let mgr = Oct.manager_alloc () in
	  ai_function mgr [] (fi,fs,sl)
      | "pol" -> 
	  let mgr = Polka.manager_alloc_strict () in
	  ai_function mgr [] (fi,fs,sl)
      | "wp" ->
	  let targets = List.fold_left collect_asserts [] sl in
	  wp_function targets (fi,fs,sl)
      | "boxwp" | "octwp" | "polwp" ->
	  let targets = List.fold_left collect_asserts [] sl in
	  begin match Jc_options.ai_domain with
	  | "boxwp" -> 
	      let mgr = Box.manager_alloc () in
	      ai_function mgr targets (fi,fs,sl) 
	  | "octwp" -> 
	      let mgr = Oct.manager_alloc () in
	      ai_function mgr targets (fi,fs,sl) 
	  | "polwp" -> 
	      let mgr = Polka.manager_alloc_strict () in
	      ai_function mgr targets (fi,fs,sl) 
	  | _ -> assert false
	  end;
	  let targets = 
	    List.fold_right (fun target acc ->
	      target.jc_target_invariant <- simplify target.jc_target_invariant;
	      let impl = raw_asrt(JCAimplies(target.jc_target_invariant,
		                             target.jc_target_assertion)) in
	      if tautology impl then acc else target :: acc
	    ) targets []
	  in
	  wp_function targets (fi,fs,sl)
      | _ -> assert false
      end
  
(*
Local Variables: 
compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
End: 
*)
