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

open Env
open Envset
open Fenv

open Region

open Output_ast

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

val fresh_statement_label : unit -> label_info

(** {1 Types} *)

val ty : jc_type -> some_ty_opt

val type_ : ('a, _) ty_opt -> jc_type -> 'a logic_type

val why_type : ('a, 'b) ty_opt -> jc_type -> 'a why_type

val some_logic_type : jc_type -> some_logic_type

val some_why_type: jc_type -> some_why_type

val some_var_why_type : var_info -> some_why_type

val some_var_logic_type : var_info -> some_logic_type

val raw_pset_type : 'a logic_type -> 'b logic_type

val raw_memory_type : 'a logic_type -> 'b logic_type -> 'c logic_type

val memory_type : mem_class -> 'a logic_type

val is_memory_type : 'a logic_type -> bool

val li_model_mem_arg_3 :
  label_in_name:bool -> label -> MemClass.t * RegionTable.key -> string * some_term * some_logic_type

val pointer_class_model_type : pointer_class -> 'a logic_type

val tag_id_type : root_info -> 'a logic_type

val tag_table_type : root_info -> 'a logic_type

val raw_alloc_table_type : 'a logic_type -> 'b logic_type

val alloc_table_type : alloc_class -> 'a logic_type

val is_alloc_table_type : 'a logic_type -> bool

val raw_tag_table_type: 'a logic_type -> 'b logic_type

(**  {1 Variables} *)

(** {1 others} *)

(* horror... *)
type term = { mutable term : 'a 'b.
                       ('a, 'b) ty_opt ->
                ?subst:(some_term Envset.VarMap.t) ->
                type_safe:bool -> global_assertion:bool -> relocate:bool
                -> label -> label -> Fenv.term -> 'a Output_ast.term }

val term : term

val nondet_value : ('a, 'b) ty_opt -> jc_type -> 'a expr

val make_conversion_params : pointer_class -> [`Module of [`Safe | `Unsafe]] why_decl list

val param : ('a, 'b) ty_opt -> var_info -> string * 'a logic_type

val some_param : var_info -> string * some_logic_type

val tparam : ('a, 'b) ty_opt -> label_in_name:bool -> label -> var_info -> string * 'a Output_ast.term * 'a logic_type

val some_tparam : label_in_name:bool -> label -> var_info -> string * some_term * some_logic_type

val li_model_args_3 :
  label_in_name:bool ->
  ?region_assoc:(RegionTable.key * RegionTable.key) list ->
  ?label_assoc:(LogicLabelSet.elt * LogicLabelSet.elt) list ->
  effect -> (string * some_term * some_logic_type) list

val li_model_mem_args_5 :
  label_in_name:bool ->
  ?region_assoc:(RegionTable.key * RegionTable.key) list ->
  ?label_assoc:(LogicLabelSet.elt * LogicLabelSet.elt) list ->
  effect ->
  ((MemClass.t * InternalRegion.t) * (string * some_term * some_logic_type)) list

val tag_table_var : VariantOrd.t * RegionTable.key -> 'a expr

val tvar : label_in_name:bool -> label -> var_info -> 'a Output_ast.term

val var: var_info -> 'a expr

val plain_var : string -> 'a expr

val ttag_table_var : label_in_name:bool -> label -> VariantOrd.t * RegionTable.key -> bool * 'a Output_ast.term

val talloc_table_var : label_in_name:bool -> label -> AllocClass.t * RegionTable.key -> bool * 'a Output_ast.term

val tmemory_var : label_in_name:bool -> label -> MemClass.t * RegionTable.key -> 'a Output_ast.term

val lvar : constant:bool -> label_in_name:bool -> label -> string -> 'a Output_ast.term

val lvar_name : label_in_name:bool -> ?label_assoc:(label * label) list -> label -> string -> string

val plain_memory_var : mem_class * RegionTable.key -> 'a expr

val memory_var : ?test_current_function:bool -> MemClass.t * RegionTable.key -> 'a expr

val alloc_table_var : ?test_current_function:bool -> AllocClass.t * RegionTable.key -> 'a expr

val plain_alloc_table_var : alloc_class * RegionTable.key -> 'a expr

val plain_tag_table_var : root_info * RegionTable.key -> 'a expr

val make_arguments :
  callee_reads:effect ->
  callee_writes:effect ->
  region_assoc:(RegionTable.key * RegionTable.key) list ->
  param_assoc:(VarOrd.t * ('a, 'b) Ast.expr) list ->
  with_globals:bool ->
  with_body:bool ->
  string ->
  some_expr list ->
  pred * string * (StringSet.elt * some_logic_type) list * some_expr * some_expr * some_expr list

val define_locals :
  ?reads:(string * some_logic_type) list ->
  ?writes:(string * some_logic_type) list ->
  'a expr -> 'a expr


val li_model_at_args_3 :
  label_in_name:bool ->
  ?region_assoc:(RegionTable.key * RegionTable.key) list ->
  ?label_assoc:(LogicLabelSet.elt * LogicLabelSet.elt) list ->
  effect -> (string * some_term * some_logic_type) list

val root_model_type : root_info -> 'a logic_type

val pointer_type : alloc_class -> pointer_class -> 'a logic_type

val raw_pointer_type : 'a logic_type -> 'b logic_type

val bitvector_type : unit -> 'a logic_type

(** {2 building output terms} *)

val const : ('a, 'b) ty_opt -> Ast.const -> 'a constant
(** constant *)

val logic_pred_call :
  label_in_name:bool ->
  region_assoc:(RegionTable.key * RegionTable.key) list ->
  label_assoc:(LogicLabelSet.elt * LogicLabelSet.elt) list ->
  logic_info ->
  some_term list -> pred
(** call logic predicate, handling regions and labels *)

val logic_fun_call :
  label_in_name:bool ->
  region_assoc:(RegionTable.key * RegionTable.key) list ->
  label_assoc:(LogicLabelSet.elt * LogicLabelSet.elt) list ->
  logic_info -> some_term list -> 'a Output_ast.term

(** {2 helpers for effects information} *)

val collect_li_reads : StringSet.t -> logic_info -> StringSet.t
(** effects of a predicate of logic function *)

val all_effects : effect -> string list

val pset_union_of_list : 'a Output_ast.term list -> 'a Output_ast.term

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
  (string * some_logic_type) list

val read_parameters :
  type_safe:bool ->
  region_list:RegionTable.key list ->
  callee_reads:effect ->
  callee_writes:effect ->
  params:var_info list ->
  already_used:StringSet.elt list ->
  (string * some_logic_type) list

val write_locals :
  region_list:RegionTable.key list ->
  callee_reads:effect ->
  callee_writes:effect ->
  params:var_info list ->
  (string * some_logic_type) list

val read_locals :
  region_list:RegionTable.key list ->
  callee_reads:effect ->
  callee_writes:effect ->
  params:var_info list ->
  (string * some_logic_type) list


(** {1 Misc} *)

val specialized_functions : (string * string StringMap.t) Common.StringHashtblIter.t
