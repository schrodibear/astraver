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
    jc_var_info_final_name = id;
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
  { jc_effect_alloc_table = StringSet.empty ;
    jc_effect_tag_table = StringSet.empty ;
    jc_effect_memories = FieldSet.empty ;
  }

let logic_fun_tag_counter = ref 0

let make_term_op name ty =
  incr logic_fun_tag_counter;
  { jc_logic_info_tag = !logic_fun_tag_counter;
    jc_logic_info_name = name;
    jc_logic_info_result_type = Some ty;
    jc_logic_info_parameters = [];
    jc_logic_info_effects = empty_effects;
    jc_logic_info_calls = [];
  }

let eq_int_bool = make_term_op "eq_int_bool" boolean_type
let neq_int_bool = make_term_op "neq_int_bool" boolean_type
let neq_pointer_bool = make_term_op "neq_pointer_bool" boolean_type
let add_int = make_term_op "add_int" integer_type
let sub_int = make_term_op "sub_int" integer_type
let mul_int = make_term_op "mul_int" integer_type
let div_int = make_term_op "div_int" integer_type
let mod_int = make_term_op "mod_int" integer_type
let minus_int = make_term_op "neg_int" integer_type

let add_real = make_term_op "add_real" real_type
let sub_real = make_term_op "sub_real" real_type
let mul_real = make_term_op "mul_real" real_type
let div_real = make_term_op "div_real" real_type

let shift = make_term_op "shift" unit_type   

let real_of_integer = make_term_op "real_of_int" real_type

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

let gt_int = make_rel "gt_int"
let lt_int = make_rel "lt_int"
let ge_int = make_rel "ge_int"
let le_int = make_rel "le_int"
let eq = make_rel "eq"
let neq = make_rel "neq"
let band = make_rel "band"
let bor = make_rel "bor"

    
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

let gt_int_ = make_fun_info "gt_int_" boolean_type
let lt_int_ = make_fun_info "lt_int_" boolean_type 
let ge_int_ = make_fun_info "ge_int_" boolean_type
let le_int_ = make_fun_info "le_int_" boolean_type 
let eq_int_ = make_fun_info "eq_int_" integer_type
let neq_int_ = make_fun_info "neq_int_" integer_type

let add_int_ = make_fun_info "add_int" integer_type
let sub_int_ = make_fun_info "sub_int" integer_type
let mul_int_ = make_fun_info "mul_int" integer_type
let div_int_ = make_fun_info "div_int" integer_type
let mod_int_ = make_fun_info "mod_int" integer_type

let add_real_ = make_fun_info "add_real" real_type
let sub_real_ = make_fun_info "sub_real" real_type
let mul_real_ = make_fun_info "mul_real" real_type
let div_real_ = make_fun_info "div_real" real_type

let uplus_int = make_fun_info "uplus_int" integer_type
let uminus_int = make_fun_info "neg_int" integer_type
let uplus_real = make_fun_info "uplus_real" integer_type
let uminus_real = make_fun_info "uminus_real" integer_type

let eq_pointer = make_fun_info "eq_pointer" integer_type
let neq_pointer = make_fun_info "neq_pointer" integer_type

let and_ = make_fun_info "and" boolean_type
let or_ = make_fun_info "or" boolean_type
let not_ = make_fun_info "not" boolean_type

let shift_ = make_fun_info "shift" unit_type   

let real_of_integer_ = make_fun_info "real_of_int" real_type

(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
