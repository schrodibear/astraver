(**************************************************************************)
(*                                                                        *)
(*  The Why/Caduceus/Krakatoa tool suite for program certification        *)
(*  Copyright (C) 2002-2007                                               *)
(*    Romain BARDOU                                                       *)
(*    Jean-François COUCHOT                                               *)
(*    Mehdi DOGGUY                                                        *)
(*    Jean-Christophe FILLIÂTRE                                           *)
(*    Thierry HUBERT                                                      *)
(*    Claude MARCHÉ                                                       *)
(*    Yannick MOY                                                         *)
(*    Christine PAULIN                                                    *)
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

(* $Id: jc_pervasives.ml,v 1.60 2007-12-06 15:26:17 nrousset Exp $ *)

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
    match c with
      | JCCinteger n -> Num.num_of_string n
      | _ -> invalid_arg ""
	  
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

let var ?(unique=true) ?(static=false) ?(formal=false) ty id =
  incr var_tag_counter;
  let vi = {
    jc_var_info_tag = !var_tag_counter;
    jc_var_info_name = id;
    jc_var_info_final_name = 
      if unique then Jc_envset.get_unique_name id else id;
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
    jc_effect_through_params = VarSet.empty;
    jc_effect_mutable = StringSet.empty;
    jc_effect_committed = StringSet.empty;
  }

let empty_logic_info =
  {
    jc_logic_info_tag = 0;
    jc_logic_info_name = "";
    jc_logic_info_final_name = "";
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
    jc_logic_info_final_name = Jc_envset.get_unique_name name;
    jc_logic_info_result_type = Some ty;
    jc_logic_info_parameters = [];
    jc_logic_info_effects = empty_effects;
    jc_logic_info_calls = [];
  }

let real_of_integer = make_logic_fun "real_of_int" real_type
let full_separated = make_logic_fun "full_separated" null_type

(* logic predicates *)

let make_rel name =
  incr logic_fun_tag_counter;
  { jc_logic_info_tag = !logic_fun_tag_counter;
    jc_logic_info_name = name;
    jc_logic_info_final_name = Jc_envset.get_unique_name name;
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
    jc_fun_info_final_name = Jc_envset.get_unique_name name;
    jc_fun_info_parameters = [];
    jc_fun_info_return_type = ty;
    jc_fun_info_calls = [];
    jc_fun_info_logic_apps = [];
    jc_fun_info_effects = empty_fun_effect;
 }


let real_of_integer_ = make_fun_info "real_of_integer" real_type

let option_compare comp opt1 opt2 = match opt1,opt2 with
  | None,None -> 0
  | None,Some _ -> -1
  | Some _,None -> 1
  | Some x,Some y -> comp x y

let rec list_compare comp ls1 ls2 = match ls1,ls2 with
  | [],[] -> 0
  | [],_ -> -1
  | _,[] -> 1
  | x1::r1,x2::r2 -> 
      let compx = comp x1 x2 in 
      if compx = 0 then list_compare comp r1 r2 else compx



(* terms *)

let term_no_loc t ty = {
  jc_term_node = t;
  jc_term_type = ty;
  jc_term_loc = Loc.dummy_position;
  jc_term_label = "";
}

let rec term_of_expr e =
  let node = match e.jc_expr_node with
    | JCEconst c -> JCTconst c
    | JCEvar vi -> JCTvar vi
    | JCEbinary (e1, op, e2) -> JCTbinary (term_of_expr e1, op, term_of_expr e2) 
    | JCEunary (op, e) -> JCTunary (op, term_of_expr e)
    | JCEshift (e1, e2) -> JCTshift (term_of_expr e1, term_of_expr e2)
    | JCEsub_pointer (e1, e2) -> JCTsub_pointer (term_of_expr e1, term_of_expr e2)
    | JCEderef (e, fi) -> JCTderef (term_of_expr e, fi)
    | JCEinstanceof (e, si) -> JCTinstanceof (term_of_expr e, si)
    | JCEcast (e, si) -> JCTcast (term_of_expr e, si)
    | JCEif (e1, e2, e3) -> JCTif (term_of_expr e1, term_of_expr e2, term_of_expr e3)
    | JCEoffset (ok, e, si) -> JCToffset (ok, term_of_expr e, si)
    | JCErange_cast _ | JCEalloc _ | JCEfree _ -> assert false
  in
    { jc_term_node = node;
      jc_term_type = e.jc_expr_type;
      jc_term_loc = e.jc_expr_loc;
      jc_term_label = "" }

let term_var_no_loc vi = term_no_loc (JCTvar vi) vi.jc_var_info_type

let zerot = term_no_loc (JCTconst (JCCinteger "0")) integer_type
let minusonet = term_no_loc (JCTconst (JCCinteger "-1")) integer_type
let nullt = term_no_loc (JCTconst (JCCnull)) JCTnull

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

let term_num t = match t.jc_term_node with
  | JCTconst _ -> 1
  | JCTvar _ -> 3
  | JCTbinary _ -> 5
  | JCTshift _ -> 7
  | JCTsub_pointer _ -> 11
  | JCTunary _ -> 13
  | JCTderef _ -> 17
  | JCTold _ -> 19
  | JCToffset _ -> 23
  | JCTinstanceof _ -> 31
  | JCTcast _ -> 37
  | JCTrange _ -> 41
  | JCTapp _ -> 43
  | JCTif _ -> 47

(* Comparison based only on term structure, not types not locations. *)
let rec raw_term_compare t1 t2 =
  match t1.jc_term_node, t2.jc_term_node with
  | JCTconst c1,JCTconst c2 -> 
      Pervasives.compare c1 c2
  | JCTvar v1,JCTvar v2 -> 
      Pervasives.compare v1.jc_var_info_tag v2.jc_var_info_tag
  | JCTbinary(t11,op1,t12),JCTbinary(t21,op2,t22) -> 
      let compop = Pervasives.compare op1 op2 in
      if compop = 0 then 
	let comp1 = raw_term_compare t11 t21 in
	if comp1 = 0 then raw_term_compare t12 t22 else comp1
      else compop
  | JCTshift(t11,t12),JCTshift(t21,t22)
  | JCTsub_pointer(t11,t12),JCTshift(t21,t22) ->
      let comp1 = raw_term_compare t11 t21 in
      if comp1 = 0 then raw_term_compare t12 t22 else comp1
  | JCTunary(op1,t11),JCTunary(op2,t21) ->
      let compop = Pervasives.compare op1 op2 in
      if compop = 0 then raw_term_compare t11 t21 else compop
  | JCTold t11,JCTold t21 ->
      raw_term_compare t11 t21
  | JCTderef(t11,fi1),JCTderef(t21,fi2) ->
      let compfi = 
	Pervasives.compare fi1.jc_field_info_tag fi2.jc_field_info_tag
      in
      if compfi = 0 then raw_term_compare t11 t21 else compfi
  | JCToffset(ok1,t11,st1),JCToffset(ok2,t21,st2) ->
      let compok = Pervasives.compare ok1 ok2 in
      if compok = 0 then
	let compst = 
	  Pervasives.compare st1.jc_struct_info_name st2.jc_struct_info_name
	in
	if compst = 0 then raw_term_compare t11 t21 else compst
      else compok
  | JCTinstanceof(t11,st1),JCTinstanceof(t21,st2) 
  | JCTcast(t11,st1),JCTcast(t21,st2) ->
      let compst = 
	Pervasives.compare st1.jc_struct_info_name st2.jc_struct_info_name
      in
      if compst = 0 then raw_term_compare t11 t21 else compst
  | JCTrange(t11opt,t12opt),JCTrange(t21opt,t22opt) ->
      let comp1 = option_compare raw_term_compare t11opt t21opt in
      if comp1 = 0 then 
	option_compare raw_term_compare t12opt t22opt
      else comp1
  | JCTapp(li1,ts1),JCTapp(li2,ts2) ->
      let compli = 
	Pervasives.compare li1.jc_logic_info_tag li2.jc_logic_info_tag
      in
      if compli = 0 then
	list_compare raw_term_compare ts1 ts2
      else compli
  | JCTif(t11,t12,t13),JCTif(t21,t22,t23) ->
      let comp1 = raw_term_compare t11 t21 in
      if comp1 = 0 then 
	let comp2 = raw_term_compare t12 t22 in
	if comp2 = 0 then raw_term_compare t13 t23 else comp2
      else comp1
  | _ -> term_num t2 - term_num t1

let raw_term_equal t1 t2 = raw_term_compare t1 t2 = 0

let tag_num tag = match tag.jc_tag_node with
  | JCTtag _ -> 1
  | JCTbottom -> 3
  | JCTtypeof _ -> 5

let raw_tag_compare tag1 tag2 =
  match tag1.jc_tag_node,tag2.jc_tag_node with
    | JCTtag st1,JCTtag st2 ->
        Pervasives.compare st1.jc_struct_info_name st2.jc_struct_info_name
    | JCTbottom,JCTbottom -> 0
    | JCTtypeof(t1,st1),JCTtypeof(t2,st2) ->
        let compst = 
	  Pervasives.compare st1.jc_struct_info_name st2.jc_struct_info_name
        in
        if compst = 0 then raw_term_compare t1 t2 else compst
  | _ -> tag_num tag2 - tag_num tag1

let assertion_num a = match a.jc_assertion_node with
  | JCAtrue -> 1
  | JCAfalse -> 3
  | JCArelation _ -> 5
  | JCAand _ -> 7
  | JCAor _ -> 11
  | JCAimplies _ -> 13
  | JCAiff _ -> 17
  | JCAnot _ -> 19
  | JCAapp _ -> 23
  | JCAquantifier _ -> 31
  | JCAold _ -> 37
  | JCAinstanceof  _ -> 41
  | JCAbool_term _ -> 43
  | JCAif _ -> 47
  | JCAmutable _ -> 49
  | JCAtagequality _ -> 51

(* Comparison based only on assertion structure, not locations. *)
let rec raw_assertion_compare a1 a2 =
  match a1.jc_assertion_node, a2.jc_assertion_node with
    | JCAtrue,JCAtrue | JCAfalse,JCAfalse -> 0
    | JCArelation(t11,op1,t12),JCArelation(t21,op2,t22) ->
        let compop = Pervasives.compare op1 op2 in
        if compop = 0 then 
	  let comp1 = raw_term_compare t11 t21 in
	  if comp1 = 0 then raw_term_compare t12 t22 else comp1
        else compop
    | JCAand als1,JCAand als2 | JCAor als1,JCAor als2 ->
	list_compare raw_assertion_compare als1 als2
    | JCAimplies(a11,a12),JCAimplies(a21,a22) 
    | JCAiff(a11,a12),JCAiff(a21,a22) ->
        let comp1 = raw_assertion_compare a11 a21 in
        if comp1 = 0 then raw_assertion_compare a12 a22 else comp1
    | JCAnot a1,JCAnot a2 | JCAold a1,JCAold a2 ->
        raw_assertion_compare a1 a2
    | JCAapp(li1,tls1),JCAapp(li2,tls2) ->
        let compli = 
	  Pervasives.compare li1.jc_logic_info_tag li2.jc_logic_info_tag
        in
        if compli = 0 then
  	  list_compare raw_term_compare tls1 tls2
        else compli
    | JCAquantifier(q1,vi1,a1),JCAquantifier(q2,vi2,a2) ->
        let compq = Pervasives.compare q1 q2 in
        if compq = 0 then 
	  let compvi = Pervasives.compare vi1 vi2 in
	  if compvi = 0 then raw_assertion_compare a1 a2 else compvi
        else compq
    | JCAinstanceof(t1,st1),JCAinstanceof(t2,st2) ->
        let compst = 
	  Pervasives.compare st1.jc_struct_info_name st2.jc_struct_info_name
        in
        if compst = 0 then raw_term_compare t1 t2 else compst
    | JCAbool_term t1,JCAbool_term t2 ->
        raw_term_compare t1 t2
    | JCAif(t1,a11,a12),JCAif(t2,a21,a22) ->
        let comp0 = raw_term_compare t1 t2 in
        if comp0 = 0 then 
	  let comp1 = raw_assertion_compare a11 a21 in
	  if comp1 = 0 then raw_assertion_compare a12 a22 else comp1
        else comp0
    | JCAmutable(t1,st1,tag1),JCAmutable(t2,st2,tag2) ->
        let compst = 
	  Pervasives.compare st1.jc_struct_info_name st2.jc_struct_info_name
        in
        if compst = 0 then
	  let comptag = raw_tag_compare tag1 tag2 in
	  if comptag = 0 then raw_term_compare t1 t2 else comptag
        else compst
    | JCAtagequality(tag11,tag12,so1),JCAtagequality(tag21,tag22,so2) ->
        let compso = option_compare Pervasives.compare so1 so2 in
        if compso = 0 then
	  let comptag = raw_tag_compare tag11 tag21 in
	  if comptag = 0 then raw_tag_compare tag12 tag22 else comptag
        else compso
    | _ -> assertion_num a1 - assertion_num a2

let raw_assertion_equal a1 a2 = raw_assertion_compare a1 a2 = 0

let rec is_numeric_term t =
  match t.jc_term_node with
    | JCTconst _ -> true
    | JCTvar _ | JCTshift _ | JCTsub_pointer _ | JCTderef _
    | JCToffset _ | JCTinstanceof _ | JCTrange _ -> false
    | JCTbinary (t1, _, t2) -> is_numeric_term t1 && is_numeric_term t2
    | JCTunary (_, t) | JCTold t | JCTcast (t, _) -> is_numeric_term t
    | JCTapp _ -> false (* TODO ? *)
    | JCTif _ -> false (* TODO ? *)


(* assertions *)

let raw_asrt a = 
(*
  eprintf "Warning: calling raw_asrt may lose tracability@.";
*)
{
  jc_assertion_node = a;
  jc_assertion_loc = Loc.dummy_position;
  jc_assertion_label = "";
}


let true_assertion = raw_asrt JCAtrue
let is_true a = (a.jc_assertion_node = JCAtrue)

let make_and al = 
  (* optimization *)
  let al = List.filter (fun a -> not (is_true a)) al in
  let anode = match al with
    | [] -> JCAtrue
    | [a] -> a.jc_assertion_node
    | a::tl -> JCAand al
  in
  raw_asrt anode

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

(* fun specs *)

let default_behavior = { 
  jc_behavior_throws = None;
  jc_behavior_assumes = None;
  jc_behavior_assigns = None;
  jc_behavior_ensures = raw_asrt JCAtrue
}

let contains_normal_behavior fs =
  List.exists 
    (fun (_, _, b) -> b.jc_behavior_throws = None) 
    fs.jc_fun_behavior

let contains_exceptional_behavior fs =
  List.exists
    (fun (_, _, b) -> b.jc_behavior_throws <> None)
    fs.jc_fun_behavior

let is_purely_exceptional_fun fs =
  not (contains_normal_behavior fs) && 
    contains_exceptional_behavior fs


let rec skip_shifts e = match e.jc_expr_node with
  | JCEshift(e,_) -> skip_shifts e
  | _ -> e

let rec skip_term_shifts t = match t.jc_term_node with
  | JCTshift(t,_) -> skip_term_shifts t
  | _ -> t

let rec skip_tloc_range t = match t with
  | JCLSrange(t,_,_) -> skip_tloc_range t
  | _ -> t

(* option *)

let select_option opt default = match opt with Some v -> v | None -> default
  
(*
  Local Variables: 
  compile-command: "LC_ALL=C make -C .. bin/jessie.byte"
  End: 
*)

