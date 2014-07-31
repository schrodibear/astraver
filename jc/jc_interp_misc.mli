(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2014                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud                   *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud                              *)
(*    Yannick MOY, Univ. Paris-sud                                        *)
(*    Romain BARDOU, Univ. Paris-sud                                      *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud  (former Caduceus front-end)        *)
(*    Nicolas ROUSSET, Univ. Paris-sud (on Jessie & Krakatoa)             *)
(*    Ali AYAD, CNRS & CEA Saclay      (floating-point support)           *)
(*    Sylvie BOLDO, INRIA              (floating-point support)           *)
(*    Jean-Francois COUCHOT, INRIA     (sort encodings, hyps pruning)     *)
(*    Mehdi DOGGUY, Univ. Paris-sud    (Why GUI)                          *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Lesser General Public            *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

open Jc_env
open Jc_envset
open Jc_fenv

open Jc_region

open Jc_why_output_ast

(** {1 Preliminaries} *)

val find_struct : string -> struct_info

(** {1 Environment} *)

val safety_checking : unit -> bool

val variant_checking : unit -> bool

val in_current_behavior : < name : string; .. > list -> bool

val in_default_behavior : < name : string; .. > list -> bool

val is_current_behavior : string -> bool

val set_current_behavior : string -> unit

val reset_current_behavior : unit -> unit

val get_current_spec : unit -> fun_spec

val set_current_spec : fun_spec -> unit

val reset_current_spec : unit -> unit

val fresh_loop_label : unit -> label_info

val fresh_reinterpret_label : unit -> label_info

(** {1 helpers for Output module} *)

val make_subtag : term -> term -> assertion

val make_eq : term -> term -> assertion
(** builds eq(t1,t2) *)

val make_select: term -> term -> term
(** builds select(t1,t2) *)

val make_or_term : term -> term -> term

val make_and_term : term -> term -> term

val make_not_term : term -> term

val make_eq_term : jc_type -> term -> term -> term

val make_eq_pred : jc_type -> term -> term -> assertion

val make_if_term : term -> term -> term -> term

(** {1 Types} *)

val why_unit_type : logic_type

val why_integer_type : logic_type

val tr_base_type : ?region:RegionTable.key -> jc_type -> logic_type

val tr_var_base_type : var_info -> logic_type

val tr_var_type : var_info -> why_type

val raw_pset_type : logic_type -> logic_type

val raw_memory_type : logic_type -> logic_type -> logic_type

val memory_type : mem_class -> logic_type

val is_memory_type : logic_type -> bool

val tr_li_model_mem_arg_3 :
  label_in_name:bool -> label -> MemClass.t * RegionTable.key -> string * term * logic_type

val deconstruct_memory_type_args : logic_type -> logic_type * logic_type

val pointer_class_model_type : pointer_class -> logic_type

val tag_id_type : root_info -> logic_type

val tag_table_type : root_info -> logic_type

val raw_alloc_table_type : logic_type -> logic_type

val alloc_table_type : alloc_class -> logic_type

val is_alloc_table_type : logic_type -> bool

val raw_tag_table_type: logic_type -> logic_type

(**  {1 Variables} *)

(** {1 others} *)

(* horror... *)
val ref_term :
  (?subst:(term VarMap.t) ->
    type_safe:bool ->
    global_assertion:bool ->
    relocate:bool ->
    label -> label -> Jc_fenv.term -> term)
  ref

val any_value : region -> jc_type -> expr

val make_valid_pred :
  in_param:bool -> equal:bool -> ?left:bool -> ?right:bool -> alloc_class -> pointer_class -> why_decl

val make_fresh_pred : alloc_class -> pointer_class -> why_decl

val make_instanceof_pred :
  arg:(assertion, _, term -> term -> assertion, [`Range_l_r | `Singleton], _, _) arg ->
    alloc_class -> pointer_class -> why_decl

val make_alloc_pred : alloc_class -> pointer_class -> why_decl

val make_valid_pred_app :
  in_param:bool -> equal:bool ->
  alloc_class * RegionTable.key -> pointer_class -> term -> term option -> term option -> assertion

val make_alloc_param :
   arg:(why_decl, check_size:bool -> why_decl, _, [`Range_0_n | `Singleton], _, 'r) arg ->
     alloc_class -> pointer_class -> 'r

val make_conversion_params : pointer_class -> why_decl list

val param : type_safe:bool -> var_info -> string * logic_type

val tparam : label_in_name:bool -> label -> var_info -> string * term * logic_type

val tr_li_model_args_3 :
  label_in_name:bool ->
  ?region_assoc:(RegionTable.key * RegionTable.key) list ->
  ?label_assoc:(LogicLabelSet.elt * LogicLabelSet.elt) list ->
  effect -> (string * term * logic_type) list

val tr_li_model_mem_args_5 :
  label_in_name:bool ->
  ?region_assoc:(RegionTable.key * RegionTable.key) list ->
  ?label_assoc:(LogicLabelSet.elt * LogicLabelSet.elt) list ->
  effect ->
  ((MemClass.t * InternalRegion.t) * (string * term * logic_type)) list

val tag_table_var : VariantOrd.t * RegionTable.key -> expr

val tvar : label_in_name:bool -> label -> var_info -> term

val var: var_info -> expr

val plain_var : string -> expr

val ttag_table_var : label_in_name:bool -> label -> VariantOrd.t * RegionTable.key -> term

val talloc_table_var : label_in_name:bool -> label -> AllocClass.t * RegionTable.key -> bool * term

val tmemory_var : label_in_name:bool -> label -> MemClass.t * RegionTable.key -> term

val lvar : constant:bool -> label_in_name:bool -> label -> string -> term

val lvar_name : label_in_name:bool -> ?label_assoc:(label * label) list -> label -> string -> string

val plain_memory_var : mem_class * RegionTable.key -> expr

val memory_var : ?test_current_function:bool -> MemClass.t * RegionTable.key -> expr

val alloc_table_var : ?test_current_function:bool -> AllocClass.t * RegionTable.key -> expr

val plain_alloc_table_var : alloc_class * RegionTable.key -> expr

val alloc_arguments : alloc_class * RegionTable.key -> pointer_class -> expr list

val plain_tag_table_var : root_info * RegionTable.key -> expr

val make_arguments :
  callee_reads:effect ->
  callee_writes:effect ->
  region_assoc:(RegionTable.key * RegionTable.key) list ->
  param_assoc:(VarOrd.t * ('a, 'b) Jc_ast.expr) list ->
  with_globals:bool ->
  with_body:bool ->
  string ->
  expr list ->
  assertion * string * (StringSet.elt * logic_type) list * expr * expr * expr list

val define_locals :
  ?reads:(string * logic_type) list ->
  ?writes:(string * logic_type) list ->
  expr -> expr


val tr_li_model_at_args_3 :
  label_in_name:bool ->
  ?region_assoc:(RegionTable.key * RegionTable.key) list ->
  ?label_assoc:(LogicLabelSet.elt * LogicLabelSet.elt) list ->
  effect -> (string * term * logic_type) list

val root_model_type : root_info -> logic_type

val pointer_type : alloc_class -> pointer_class -> logic_type

val raw_pointer_type : logic_type -> logic_type

val bitvector_type : logic_type

(** {2 building output terms} *)

val const_of_num :  Num.num -> term

val const_of_int :  int -> term

val const : Jc_ast.const -> constant
(** constant *)

val make_select : term -> term -> term

val make_select_fi : field_info -> term -> term
(** dereferencing, builds select(f.name,t) *)

val make_select_committed : pointer_class -> term -> term
(** builds select("committed",t) *)

val make_subtag_bool : term -> term -> term

val tr_logic_pred_call :
  label_in_name:bool ->
  region_assoc:(RegionTable.key * RegionTable.key) list ->
  label_assoc:(LogicLabelSet.elt * LogicLabelSet.elt) list ->
  logic_info ->
  term list -> assertion
(** call logic predicate, handling regions and labels *)

val tr_logic_fun_call :
  label_in_name:bool ->
  region_assoc:(RegionTable.key * RegionTable.key) list ->
  label_assoc:(LogicLabelSet.elt * LogicLabelSet.elt) list ->
  logic_info -> term list -> term

val make_int_of_tag : struct_info -> term

val make_typeof : term -> term
(** typeof expression in logic *)

val make_instanceof : term -> struct_info -> assertion

val make_instanceof_bool : term -> struct_info -> term

(** {2 helpers for effects information} *)

val collect_li_reads : StringSet.t -> logic_info -> StringSet.t
(** effects of a predicate of logic function *)

val all_effects : effect -> string list

val location_list' : term list -> term

val local_read_effects : callee_reads:effect -> callee_writes:effect -> string list

val local_write_effects : callee_reads:effect -> callee_writes:effect -> string list

val write_effects :
  callee_reads:effect ->
  callee_writes:effect ->
  region_list:RegionTable.key list ->
  params:var_info list -> string list

val read_effects :
  callee_reads:effect ->
  callee_writes:effect ->
  region_list:RegionTable.key list ->
  params:var_info list -> string list

val write_parameters :
  type_safe:bool ->
  region_list:RegionTable.key list ->
  callee_reads:effect ->
  callee_writes:effect ->
  params:var_info list ->
  (string * logic_type) list

val read_parameters :
  type_safe:bool ->
  region_list:RegionTable.key list ->
  callee_reads:effect ->
  callee_writes:effect ->
  params:var_info list ->
  already_used:StringSet.elt list ->
  (string * logic_type) list

val write_locals :
  region_list:RegionTable.key list ->
  callee_reads:effect ->
  callee_writes:effect ->
  params:var_info list ->
  (string * logic_type) list

val read_locals :
  region_list:RegionTable.key list ->
  callee_reads:effect ->
  callee_writes:effect ->
  params:var_info list ->
  (string * logic_type) list


(** {1 Misc} *)

val specialized_functions : (string * string StringMap.t) Jc_pervasives.StringHashtblIter.t
