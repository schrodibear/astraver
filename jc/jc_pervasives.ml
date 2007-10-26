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

open Format
open Jc_env
open Jc_envset
open Jc_fenv
open Jc_ast


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
    | JCTpointer (s,None,None) -> 
	fprintf fmt "%s[..]" s.jc_struct_info_name
    | JCTpointer (s,Some a,None) -> 
	fprintf fmt "%s[%s..]" s.jc_struct_info_name (Num.string_of_num a)
    | JCTpointer (s,None,Some b) -> 
	fprintf fmt "%s[..%s]" s.jc_struct_info_name (Num.string_of_num b)
    | JCTpointer (s,Some a,Some b) -> 
	if Num.eq_num a b then
	  fprintf fmt "%s[%s]" s.jc_struct_info_name (Num.string_of_num a)
	else
	  fprintf fmt "%s[%s..%s]" s.jc_struct_info_name
	    (Num.string_of_num a) (Num.string_of_num b)
    | JCTnull -> fprintf fmt "(nulltype)"  


let num_of_constant loc c =
(*
  try
*)
    match c with
      | JCCinteger n -> Num.num_of_string n
      | _ -> invalid_arg ""
(*
  with
      Invalid_argument _ ->
	Jc_options.parsing_error loc "invalid integer constant"
*)
	  
let zero = Num.num_of_int 0
let minus_one = Num.num_of_int (-1)


(* operators *)

let is_relation_binary_op = function
  | Blt_int | Blt_real | Bgt_int | Bgt_real
  | Ble_int | Ble_real | Bge_int | Bge_real
  | Beq_int | Beq_real | Beq_pointer | Beq_bool
  | Bneq_int | Bneq_real | Bneq_pointer | Bneq_bool -> true
  | _ -> false

let is_logical_binary_op = function
  | Bland | Blor | Bimplies | Biff -> true
  | _ -> false

let is_arithmetic_binary_op = function
  | Badd_int | Badd_real | Bsub_int | Bsub_real
  | Bmul_int | Bmul_real | Bdiv_int | Bdiv_real | Bmod_int -> true
  | _ -> false

let is_bitwise_binary_op = function
  | Bbw_and | Bbw_or | Bbw_xor 
  | Bshift_left | Blogical_shift_right | Barith_shift_right -> true
  | _ -> false

let is_logical_unary_op = function
  | Unot -> true
  | _ -> false

let is_arithmetic_unary_op = function
  | Uplus_int | Uminus_int | Uplus_real | Uminus_real -> true
  | _ -> false

let is_bitwise_unary_op = function
  | Ubw_not -> true
  | _ -> false


let rec is_constant_term t =
  match t.jc_term_node with
    | JCTrange (None, None) (* CORRECT ? *)
    | JCTconst _ -> true
    | JCTvar _ | JCTshift _ | JCTsub_pointer _ | JCTderef _
    | JCTapp _ | JCTold _ | JCToffset _
    | JCTinstanceof _ | JCTcast _ | JCTif _ -> false
    | JCTbinary (t1, _, t2) | JCTrange (Some t1, Some t2) ->
	is_constant_term t1 && is_constant_term t2
    | JCTunary (_, t) | JCTrange (Some t, None) | JCTrange (None, Some t) ->
	is_constant_term t

let rec is_constant_assertion a =
  match a.jc_assertion_node with
    | JCAtrue | JCAfalse -> true
    | JCArelation (t1, _, t2) -> 
	is_constant_term t1 && is_constant_term t2
    | JCAand al | JCAor al ->
	List.for_all is_constant_assertion al
    | JCAimplies (a1, a2) | JCAiff (a1, a2) ->
	is_constant_assertion a1 && is_constant_assertion a2
    | JCAnot a | JCAquantifier (_, _, a) | JCAold a 
	-> is_constant_assertion a
    | JCAapp _ | JCAinstanceof _ | JCAmutable _ | JCAtagequality _
	-> false
    | JCAbool_term t -> is_constant_term t
    | JCAif (t, a1, a2) ->
	is_constant_term t &&
	  is_constant_assertion a1 &&
	  is_constant_assertion a2

(* native types *)

let unit_type = JCTnative Tunit
let boolean_type = JCTnative Tboolean
let integer_type = JCTnative Tinteger
let real_type = JCTnative Treal
let null_type = JCTnull

(* temporary variables *)

let tempvar_count = ref 0
(* let reset_tmp_var () = tempvar_count := 0 *)
let tmp_var_name () = 
  incr tempvar_count; "jessie_" ^ string_of_int !tempvar_count

(* constants *)

let const c =
  match c with
    | JCCvoid -> unit_type,c
    | JCCinteger _ -> integer_type,c
    | JCCreal _ -> real_type,c
    | JCCboolean _ -> boolean_type,c
    | JCCnull -> null_type,c

(* variables *)

let var_tag_counter = ref 0

let var ?(static=false) ?(formal=false) ty id =
  incr var_tag_counter;
  let vi = {
    jc_var_info_tag = !var_tag_counter;
    jc_var_info_name = id;
    jc_var_info_final_name = Jc_envset.get_unique_name id;
    jc_var_info_type = ty;
    jc_var_info_formal = formal;
    jc_var_info_assigned = false;
    jc_var_info_static = static;
  }
  in vi

let newvar ty = var ty (tmp_var_name())

let newrefvar ty = 
  let vi = newvar ty in
    vi.jc_var_info_assigned <- true;
    vi

let copyvar vi =
  incr var_tag_counter;
  { vi with 
    jc_var_info_tag = !var_tag_counter; 
    jc_var_info_name = 
      "__jc_" ^ (string_of_int !var_tag_counter) ^ vi.jc_var_info_name;
    jc_var_info_final_name = 
      "__jc_" ^ (string_of_int !var_tag_counter) ^ vi.jc_var_info_final_name;
  }

(* exceptions *)

let exception_tag_counter = ref 0

let exception_info ty id =
  incr exception_tag_counter;
  let ei = {
    jc_exception_info_tag = !exception_tag_counter;
    jc_exception_info_name = id;
    jc_exception_info_type = ty;
  }
  in ei


(* logic functions *)

let empty_effects = 
  { jc_effect_alloc_table = StringSet.empty;
    jc_effect_tag_table = StringSet.empty;
    jc_effect_memories = FieldSet.empty;
    jc_effect_globals = VarSet.empty;
    jc_effect_mutable = StringSet.empty;
    jc_effect_committed = StringSet.empty;
  }

let empty_logic_info =
  {
    jc_logic_info_tag = 0;
    jc_logic_info_name = "";
    jc_logic_info_result_type = None;
    jc_logic_info_parameters = [];
    jc_logic_info_effects = empty_effects;
    jc_logic_info_calls = []; 
  }

let logic_fun_tag_counter = ref 0

let make_logic_fun name ty =
  incr logic_fun_tag_counter;
  { jc_logic_info_tag = !logic_fun_tag_counter;
    jc_logic_info_name = name;
    jc_logic_info_result_type = Some ty;
    jc_logic_info_parameters = [];
    jc_logic_info_effects = empty_effects;
    jc_logic_info_calls = [];
  }

let real_of_integer = make_logic_fun "real_of_int" real_type

(* logic predicates *)

let make_rel name =
  incr logic_fun_tag_counter;
  { jc_logic_info_tag = !logic_fun_tag_counter;
    jc_logic_info_name = name;
    jc_logic_info_result_type = None;
    jc_logic_info_parameters = [];
    jc_logic_info_effects = empty_effects;
    jc_logic_info_calls = [];
  }

    
(* programs *)

let empty_fun_effect =
  { jc_reads = empty_effects;
    jc_writes = empty_effects;
    jc_raises = ExceptionSet.empty ;
  }

let fun_tag_counter = ref 0

let make_fun_info name ty =
  incr fun_tag_counter;
  { jc_fun_info_tag = !fun_tag_counter;
    jc_fun_info_name = name;
    jc_fun_info_parameters = [];
    jc_fun_info_return_type = ty;
    jc_fun_info_calls = [];
    jc_fun_info_logic_apps = [];
    jc_fun_info_effects = empty_fun_effect;
 }


let real_of_integer_ = make_fun_info "real_of_integer" real_type

let rec iter_term f t =
  f t;
  match t.jc_term_node with
  | JCTconst _ | JCTvar _ | JCTrange(None,None) -> ()
  | JCTbinary(t1,_,t2) | JCTshift(t1,t2) | JCTsub_pointer(t1,t2) 
  | JCTrange(Some t1,Some t2) ->
      iter_term f t1; iter_term f t2
  | JCTunary(_,t1) | JCTderef(t1,_) | JCTold t1 | JCToffset(_,t1,_)
  | JCTinstanceof(t1,_) | JCTcast(t1,_) | JCTrange(Some t1,None)
  | JCTrange(None,Some t1) ->
      iter_term f t1
  | JCTapp(_,tl) ->
      List.iter (iter_term f) tl
  | JCTif(t1,t2,t3) ->
      iter_term f t1; iter_term f t2; iter_term f t3

let rec fold_term f acc t =
  let acc = f acc t in
  match t.jc_term_node with
  | JCTconst _ | JCTvar _ | JCTrange(None,None) -> acc
  | JCTbinary(t1,_,t2) | JCTshift(t1,t2) | JCTsub_pointer(t1,t2) 
  | JCTrange(Some t1,Some t2) ->
      let acc = fold_term f acc t1 in
      fold_term f acc t2
  | JCTunary(_,t1) | JCTderef(t1,_) | JCTold t1 | JCToffset(_,t1,_)
  | JCTinstanceof(t1,_) | JCTcast(t1,_) | JCTrange(Some t1,None)
  | JCTrange(None,Some t1) ->
      fold_term f acc t1
  | JCTapp(_,tl) ->
      List.fold_left (fold_term f) acc tl
  | JCTif(t1,t2,t3) ->
      let acc = fold_term f acc t1 in
      let acc = fold_term f acc t2 in
      fold_term f acc t3

let rec post_map_term f t =
  let tnode = match t.jc_term_node with
    | JCTconst _ | JCTvar _ | JCTrange(None,None) as tnode -> tnode
    | JCTbinary(t1,bop,t2) ->
	JCTbinary(post_map_term f t1,bop,post_map_term f t2) 
    | JCTunary(uop,t1) ->
	JCTunary(uop,post_map_term f t1)
    | JCTshift(t1,t2) ->
	JCTshift(post_map_term f t1,post_map_term f t2)
    | JCTsub_pointer(t1,t2) ->
	JCTsub_pointer(post_map_term f t1,post_map_term f t2)
    | JCTderef(t1,fi) ->
	JCTderef(post_map_term f t1,fi)
    | JCTapp(li,tl) ->
	JCTapp(li,List.map (post_map_term f) tl)
    | JCTold t ->
	JCTold(post_map_term f t)
    | JCToffset(off,t,st) ->
	JCToffset(off,post_map_term f t,st)
    | JCTinstanceof(t,st) ->
	JCTinstanceof(post_map_term f t,st)
    | JCTcast(t,st) ->
	JCTcast(post_map_term f t,st)
    | JCTif(t1,t2,t3) ->
	JCTif(post_map_term f t1,post_map_term f t2,post_map_term f t3)
    | JCTrange(Some t1,Some t2) ->
	JCTrange(Some (post_map_term f t1),Some (post_map_term f t2))
    | JCTrange(Some t1,None) ->
	JCTrange(Some (post_map_term f t1),None)
    | JCTrange(None,Some t2) ->
	JCTrange(None,Some (post_map_term f t2))
  in
  f tnode

let rec pre_map_term f t =
  let tnode = match f t with
    | Some tnode -> tnode
    | None -> match t.jc_term_node with
      | JCTconst _ | JCTvar _ | JCTrange(None,None) as tnode -> tnode
      | JCTbinary(t1,bop,t2) ->
	  JCTbinary(pre_map_term f t1,bop,pre_map_term f t2) 
      | JCTunary(uop,t1) ->
	  JCTunary(uop,pre_map_term f t1)
      | JCTshift(t1,t2) ->
	  JCTshift(pre_map_term f t1,pre_map_term f t2)
      | JCTsub_pointer(t1,t2) ->
	  JCTsub_pointer(pre_map_term f t1,pre_map_term f t2)
      | JCTderef(t1,fi) ->
	  JCTderef(pre_map_term f t1,fi)
      | JCTapp(li,tl) ->
	  JCTapp(li,List.map (pre_map_term f) tl)
      | JCTold t ->
	  JCTold(pre_map_term f t)
      | JCToffset(off,t,st) ->
	  JCToffset(off,pre_map_term f t,st)
      | JCTinstanceof(t,st) ->
	  JCTinstanceof(pre_map_term f t,st)
      | JCTcast(t,st) ->
	  JCTcast(pre_map_term f t,st)
      | JCTif(t1,t2,t3) ->
	  JCTif(pre_map_term f t1,pre_map_term f t2,pre_map_term f t3)
      | JCTrange(Some t1,Some t2) ->
	  JCTrange(Some (pre_map_term f t1),Some (pre_map_term f t2))
      | JCTrange(Some t1,None) ->
	  JCTrange(Some (pre_map_term f t1),None)
      | JCTrange(None,Some t2) ->
	  JCTrange(None,Some (pre_map_term f t2))
  in
  { t with jc_term_node = tnode; }


let raw_asrt a = {
  jc_assertion_node = a;
  jc_assertion_loc = Loc.dummy_position;
  jc_assertion_label = "";
}

let default_behavior = { 
  jc_behavior_throws = None;
  jc_behavior_assumes = None;
  jc_behavior_assigns = None;
  jc_behavior_ensures = raw_asrt JCAtrue
}

  
(*
Local Variables: 
compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
End: 
*)
