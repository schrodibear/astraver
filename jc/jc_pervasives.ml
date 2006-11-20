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

(* native types *)

let unit_type = JCTnative `Tunit
let boolean_type = JCTnative `Tboolean
let integer_type = JCTnative `Tinteger
let real_type = JCTnative `Treal


(* logic functions *)


let make_term_op name ty =
  { jc_logic_info_name = name;
    jc_logic_info_result_type = Some ty;
  }

let eq_int_bool = make_term_op "eq_int_bool" boolean_type
let neq_int_bool = make_term_op "neq_int_bool" boolean_type
let neq_pointer_bool = make_term_op "neq_pointer_bool" boolean_type
let add_int = make_term_op "add_int" integer_type
let sub_int = make_term_op "sub_int" integer_type
let mul_int = make_term_op "mul_int" integer_type
let div_int = make_term_op "div_int" integer_type
let mod_int = make_term_op "mod_int" integer_type

(* logic predicates *)

let make_rel name =
  { jc_logic_info_name = name;
    jc_logic_info_result_type = None }

let gt_int = make_rel "gt_int"
let lt_int = make_rel "lt_int"
let ge_int = make_rel "ge_int"
let le_int = make_rel "le_int"
let eq = make_rel "eq"
let neq = make_rel "neq"

    
(* programs *)

let fun_tag_counter = ref 0

let make_fun_info name ty =
  incr fun_tag_counter;
  { jc_fun_info_tag = !fun_tag_counter;
    jc_fun_info_name = name;
    jc_fun_info_parameters = [];
    jc_fun_info_return_type = ty;
    jc_fun_info_calls = [];
    jc_fun_info_logic_apps = [];
    jc_fun_info_effects = { jc_writes_fields = FieldSet.empty } 
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
let uminus_int = make_fun_info "uminus_int" integer_type
let uplus_real = make_fun_info "uplus_real" integer_type
let uminus_real = make_fun_info "uminus_real" integer_type

let and_ = make_fun_info "and" boolean_type
let or_ = make_fun_info "or" boolean_type
let not_ = make_fun_info "not" boolean_type
    


(*
Local Variables: 
compile-command: "make -C .. bin/jessie.byte"
End: 
*)
