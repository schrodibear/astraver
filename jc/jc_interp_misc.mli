(**************************************************************************)
(*                                                                        *)
(*  The Why platform for program certification                            *)
(*                                                                        *)
(*  Copyright (C) 2002-2011                                               *)
(*                                                                        *)
(*    Jean-Christophe FILLIATRE, CNRS & Univ. Paris-sud 11                *)
(*    Claude MARCHE, INRIA & Univ. Paris-sud 11                           *)
(*    Yannick MOY, Univ. Paris-sud 11                                     *)
(*    Romain BARDOU, Univ. Paris-sud 11                                   *)
(*                                                                        *)
(*  Secondary contributors:                                               *)
(*                                                                        *)
(*    Thierry HUBERT, Univ. Paris-sud 11  (former Caduceus front-end)     *)
(*    Nicolas ROUSSET, Univ. Paris-sud 11 (on Jessie & Krakatoa)          *)
(*    Ali AYAD, CNRS & CEA Saclay         (floating-point support)        *)
(*    Sylvie BOLDO, INRIA                 (floating-point support)        *)
(*    Jean-Francois COUCHOT, INRIA        (sort encodings, hyps pruning)  *)
(*    Mehdi DOGGUY, Univ. Paris-sud 11    (Why GUI)                       *)
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



(** {1 Preliminaries} *)

val find_struct : string -> Jc_env.struct_info


type forall_or_let = 
  | JCforall of string * Output.logic_type
  | JClet of string * Output.term

val logic_int_of_enum : Jc_env.enum_info -> string
val logic_enum_of_int : Jc_env.enum_info -> string
val safe_fun_enum_of_int : Jc_env.enum_info -> string
val fun_enum_of_int : Jc_env.enum_info -> string

val logic_enum_of_bitvector : Jc_env.enum_info -> string
val logic_bitvector_of_enum : Jc_env.enum_info -> string

val mod_of_enum : Jc_env.enum_info -> string

val fun_any_enum : Jc_env.enum_info -> string

val logic_real_of_bitvector : string
val logic_integer_of_bitvector : string
val logic_bitvector_of_integer : string

val logic_bitvector_of_variant : Jc_env.root_info -> string
val logic_variant_of_bitvector : Jc_env.root_info -> string





(** {1 Environment} *)

val safety_checking : unit -> bool

val variant_checking : unit -> bool

val in_current_behavior : < name : string; .. > list -> bool

val in_default_behavior : < name : string; .. > list -> bool

val is_current_behavior : string -> bool

val set_current_behavior : string -> unit

val reset_current_behavior : unit -> unit

val get_current_spec : unit -> Jc_fenv.fun_spec

val set_current_spec : Jc_fenv.fun_spec -> unit

val reset_current_spec : unit -> unit

(*
val get_current_fun : unit -> Jc_fenv.fun_info

val set_current_fun : Jc_fenv.fun_info -> unit

val reset_current_fun : unit -> unit
  *)
val fresh_loop_label : unit -> Jc_env.label_info




(** {1 helpers for Output module} *)

val make_subtag : Output.term -> Output.term -> Output.assertion

val make_eq : Output.term -> Output.term -> Output.assertion
(** builds eq(t1,t2) *)

val make_select: Output.term -> Output.term -> Output.term
(** builds select(t1,t2) *)

val make_or_term : Output.term -> Output.term -> Output.term

val make_and_term : Output.term -> Output.term -> Output.term

val make_not_term : Output.term -> Output.term

val make_eq_term : Jc_env.jc_type -> Output.term -> Output.term -> Output.term

val make_eq_pred : Jc_env.jc_type -> Output.term -> Output.term -> Output.assertion


val make_if_term : Output.term -> Output.term -> Output.term -> Output.term



(** {1 Types} *)

val why_unit_type : Output.logic_type
val why_integer_type : Output.logic_type

val tr_base_type : ?region:Jc_region.RegionTable.key ->
           Jc_env.jc_type -> Output.logic_type

val tr_var_base_type : Jc_env.var_info -> Output.logic_type

val tr_var_type : Jc_env.var_info -> Output.why_type

val raw_pset_type : Output.logic_type -> Output.logic_type

val raw_memory_type : 
  Output.logic_type -> Output.logic_type -> Output.logic_type

val memory_type : Jc_env.mem_class -> Output.logic_type

val is_memory_type : Output.logic_type -> bool

val tmemory_param : label_in_name:bool ->
           Jc_env.label ->
           Jc_envset.MemClass.t * Jc_region.RegionTable.key ->
           string * Output.term * Output.logic_type

val deconstruct_memory_type_args : Output.logic_type -> Output.logic_type * Output.logic_type

val pointer_class_model_type : Jc_env.pointer_class -> Output.logic_type

val tag_id_type : Jc_env.root_info -> Output.logic_type

val tag_table_type : Jc_env.root_info -> Output.logic_type

val raw_alloc_table_type : Output.logic_type -> Output.logic_type

val alloc_table_type : Jc_env.alloc_class -> Output.logic_type

val is_alloc_table_type : Output.logic_type -> bool




(**  {1 Variables} *)





(** {1 others} *)

(* horror... *)
val ref_term : 
  (?subst:(Output.term Jc_envset.VarMap.t) -> 
    type_safe:bool ->
    global_assertion:bool ->
    relocate:bool ->
    Jc_env.label -> Jc_env.label -> Jc_fenv.term -> Output.term)
  ref

val any_value : Jc_env.region -> Jc_env.jc_type -> Output.expr

val eq_of_enum : Jc_env.enum_info -> string

val make_valid_pred : in_param:bool -> equal:bool ->
           ?left:bool ->
           ?right:bool ->
           Jc_env.alloc_class -> Jc_env.pointer_class -> Output.why_decl

val make_valid_pred_app : in_param:bool -> equal:bool ->
           Jc_env.alloc_class * Jc_region.RegionTable.key ->
           Jc_env.pointer_class ->
           Output.term ->
           Output.term option -> Output.term option -> Output.assertion

val make_alloc_param : check_size:bool ->
           Jc_env.alloc_class -> Jc_env.pointer_class -> Output.why_decl

val make_conversion_params : Jc_env.pointer_class -> Output.why_decl list

val param : type_safe:bool -> Jc_env.var_info -> string * Output.logic_type

val tparam : label_in_name:bool ->
           Jc_env.label ->
           Jc_env.var_info -> string * Output.term * Output.logic_type

val tmodel_parameters : label_in_name:bool ->
           ?region_assoc:(Jc_region.RegionTable.key *
                          Jc_region.RegionTable.key)
                         list ->
           ?label_assoc:(Jc_envset.LogicLabelSet.elt *
                         Jc_envset.LogicLabelSet.elt)
                        list ->
           Jc_fenv.effect -> (string * Output.term * Output.logic_type) list

val tmemory_detailed_params : label_in_name:bool ->
           ?region_assoc:(Jc_region.RegionTable.key *
                          Jc_region.RegionTable.key)
                         list ->
           ?label_assoc:(Jc_envset.LogicLabelSet.elt *
                         Jc_envset.LogicLabelSet.elt)
                        list ->
           Jc_fenv.effect ->
           ((Jc_envset.MemClass.t * Jc_region.InternalRegion.t) *
            (string * Output.term * Output.logic_type))
           list

val tag_table_var : Jc_envset.VariantOrd.t * Jc_region.RegionTable.key -> Output.expr

val tvar : label_in_name:bool ->
           Jc_env.label -> Jc_env.var_info -> Output.term

val var: Jc_env.var_info -> Output.expr

val plain_var : string -> Output.expr

val ttag_table_var : label_in_name:bool ->
           Jc_env.label ->
           Jc_envset.VariantOrd.t * Jc_region.RegionTable.key -> Output.term

val talloc_table_var : label_in_name:bool ->
  Jc_env.label ->
  Jc_envset.AllocClass.t * Jc_region.RegionTable.key -> 
  bool * Output.term

val tmemory_var : label_in_name:bool ->
           Jc_env.label ->
           Jc_envset.MemClass.t * Jc_region.RegionTable.key -> Output.term

val lvar : constant:bool ->
           label_in_name:bool -> Jc_env.label -> string -> Output.term

val plain_memory_var : Jc_env.mem_class * Jc_region.RegionTable.key -> Output.expr

val memory_var : ?test_current_function:bool ->
           Jc_envset.MemClass.t * Jc_region.RegionTable.key -> Output.expr

val alloc_table_var : ?test_current_function:bool ->
           Jc_envset.AllocClass.t * Jc_region.RegionTable.key -> Output.expr

val plain_alloc_table_var : Jc_env.alloc_class * Jc_region.RegionTable.key -> Output.expr

val alloc_arguments : Jc_env.alloc_class * Jc_region.RegionTable.key ->
           Jc_env.pointer_class -> Output.expr list

val plain_tag_table_var : Jc_env.root_info * Jc_region.RegionTable.key -> Output.expr

val make_arguments : callee_reads:Jc_fenv.effect ->
           callee_writes:Jc_fenv.effect ->
           region_assoc:(Jc_region.RegionTable.key *
                         Jc_region.RegionTable.key)
                        list ->
           param_assoc:(Jc_envset.VarOrd.t * ('a, 'b) Jc_ast.expr) list ->
           with_globals:bool ->
           with_body:bool ->
           string ->
           Output.expr list ->
           Output.assertion * string *
           (Jc_envset.StringSet.elt * Output.logic_type) list * Output.expr *
           Output.expr * Output.expr list

val define_locals : ?reads:(string * Output.logic_type) list ->
           ?writes:(string * Output.logic_type) list ->
           Output.expr -> Output.expr




val talloc_table_params : label_in_name:bool ->
           ?region_assoc:(Jc_region.RegionTable.key *
                          Jc_region.RegionTable.key)
                         list ->
           ?label_assoc:(Jc_envset.LogicLabelSet.elt *
                         Jc_envset.LogicLabelSet.elt)
                        list ->
           Jc_fenv.effect -> (string * Output.term * Output.logic_type) list

val root_model_type : Jc_env.root_info -> Output.logic_type

val pointer_type : 
  Jc_env.alloc_class -> Jc_env.pointer_class -> Output.logic_type

val raw_pointer_type : Output.logic_type -> Output.logic_type

val bitvector_type : Output.logic_type

val logic_field_of_union : Jc_env.field_info -> string

val logic_union_of_field : Jc_env.field_info -> string

(** {2 building output terms} *)

val const_of_num :  Num.num -> Output.term
val const : Jc_ast.const -> Output.constant
(** constant *)


val make_select_fi : Jc_env.field_info -> Output.term -> Output.term
(** dereferencing, builds select(f.name,t) *)

val make_select_committed : Jc_env.pointer_class -> Output.term -> Output.term
(** builds select("committed",t) *)

val make_subtag_bool : Output.term -> Output.term -> Output.term

val make_logic_pred_call : 
  label_in_name:bool ->
  region_assoc:(Jc_region.RegionTable.key *
                  Jc_region.RegionTable.key) list ->
  label_assoc:(Jc_envset.LogicLabelSet.elt *
                 Jc_envset.LogicLabelSet.elt) list ->
  Jc_fenv.logic_info -> 
  Output.term list -> Output.assertion
(** call logic predicate, handling regions and labels *)

val make_logic_fun_call : label_in_name:bool ->
           region_assoc:(Jc_region.RegionTable.key *
                         Jc_region.RegionTable.key)
                        list ->
           label_assoc:(Jc_envset.LogicLabelSet.elt *
                        Jc_envset.LogicLabelSet.elt)
                       list ->
           Jc_fenv.logic_info -> Output.term list -> Output.term

val make_int_of_tag : Jc_env.struct_info -> Output.term

val make_typeof : Jc_env.struct_info ->
           Jc_region.RegionTable.key -> Output.term -> Output.term
(** typeof expression in logic *)

val make_instanceof : Output.term ->
  Output.term -> Jc_env.struct_info -> Output.assertion



(** {2 helpers for effects information} *)

val logic_info_reads : Jc_envset.StringSet.t ->
           Jc_fenv.logic_info -> Jc_envset.StringSet.t
(** effects of a predicate of logic function *)

val all_effects : Jc_fenv.effect -> string list


val location_list' : Output.term list -> Output.term

val local_read_effects : callee_reads:Jc_fenv.effect ->
           callee_writes:Jc_fenv.effect -> string list

val local_write_effects : callee_reads:Jc_fenv.effect ->
           callee_writes:Jc_fenv.effect -> string list

val write_effects : 
  callee_reads:Jc_fenv.effect ->
  callee_writes:Jc_fenv.effect ->
  region_list:Jc_region.RegionTable.key list ->
  params:Jc_env.var_info list -> string list
  
val read_effects : 
  callee_reads:Jc_fenv.effect ->
  callee_writes:Jc_fenv.effect ->
  region_list:Jc_region.RegionTable.key list ->
  params:Jc_env.var_info list -> string list

val write_parameters :  type_safe:bool ->
           region_list:Jc_region.RegionTable.key list ->
           callee_reads:Jc_fenv.effect ->
           callee_writes:Jc_fenv.effect ->
           params:Jc_env.var_info list -> (string * Output.logic_type) list

val read_parameters : type_safe:bool ->
           region_list:Jc_region.RegionTable.key list ->
           callee_reads:Jc_fenv.effect ->
           callee_writes:Jc_fenv.effect ->
           params:Jc_env.var_info list ->
           already_used:Jc_envset.StringSet.elt list ->
           (string * Output.logic_type) list

val write_locals : region_list:Jc_region.RegionTable.key list ->
           callee_reads:Jc_fenv.effect ->
           callee_writes:Jc_fenv.effect ->
           params:Jc_env.var_info list -> (string * Output.logic_type) list

val read_locals : region_list:Jc_region.RegionTable.key list ->
           callee_reads:Jc_fenv.effect ->
           callee_writes:Jc_fenv.effect ->
           params:Jc_env.var_info list -> (string * Output.logic_type) list



(** {1 Misc} *)

val specialized_functions: 
  (string * string Jc_envset.StringMap.t) Jc_pervasives.StringHashtblIter.t
