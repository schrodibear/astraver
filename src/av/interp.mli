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
open Output_ast

module O = Output

val term :
  ('a, 'b) ty_opt ->
  ?subst:some_term VarMap.t ->
  type_safe:bool ->
  global_assertion:bool ->
  relocate:bool ->
  label -> label -> logic_info Ast.term -> 'a term

val some_term :
  ?subst:some_term VarMap.t ->
  type_safe:bool ->
  global_assertion:bool ->
  relocate:bool ->
  label ->
  label ->
  < label : label option; mark : string; node : logic_info Ast.term_node;
    pos : Loc.position; region : region;
    set_label : label option -> unit; set_region : region -> unit;
    typ : jc_type > ->
  some_term

val named_term :
  ('a, 'b) ty_opt ->
  type_safe:bool ->
  global_assertion:bool ->
  relocate:bool ->
  label -> label -> logic_info Ast.term -> 'a term

val tag :
  type_safe:bool ->
  global_assertion:bool ->
  relocate:bool ->
  label ->
  label -> < node : logic_info Ast.tag_node; .. > -> 'a term

val predicate :
  type_safe:bool ->
  global_assertion:bool ->
  relocate:bool -> label -> label -> logic_info Ast.assertion -> pred

val named_predicate :
  type_safe:bool ->
  global_assertion:bool ->
  ?kind:vc_kind ->
  ?mark_recursively:bool ->
  relocate:bool -> label -> label -> logic_info Ast.assertion -> pred

val pset :
  ('a, 'b) ty_opt ->
  type_safe:bool ->
  global_assertion:bool ->
  label ->
  < label : label option; node : logic_info Ast.location_set_node;
    pos : Loc.position; region : region;
    set_label : label option -> unit; set_region : region -> unit;
    typ : jc_type > ->
  'a term

val collect_locations :
  type_safe:bool ->
  global_assertion:bool ->
  in_clause:[< `Allocates | `Assigns | `Reads > `Allocates ] ->
  label ->
  logic_info Ast.location ->
  bool StringMap.t *
  ('a term * fun_effect) list Region.MemoryMap.t ->
  bool StringMap.t *
  ('a term * fun_effect) list Region.MemoryMap.t

val collect_pset_locations :
  ('a, 'b) ty_opt ->
  type_safe:bool ->
  global_assertion:bool ->
  label -> logic_info Ast.location -> 'a term

val external_region : ?region_list:region list -> 'a * region -> bool

val assigns :
  type_safe:bool ->
  ?region_list:region list ->
  label ->
  fun_effect ->
  (Loc.position * logic_info Ast.location list) option -> pred

val loop_assigns :
  type_safe:bool ->
  ?region_list:region list ->
  label -> fun_effect -> logic_info Ast.location list option -> pred

val reads :
  type_safe:bool ->
  global_assertion:bool ->
  logic_info Ast.location list -> mem_class * region -> 'a term

val assumption :
  logic_info Ast.assertion list -> pred -> void expr
val check : logic_info Ast.assertion list -> pred -> void expr
val expr :
  ('a, 'b) ty_opt -> (logic_info, fun_info) Ast.expr -> 'a expr
val some_expr : (logic_info, fun_info) Ast.expr -> some_expr
val axiomatic_decl : Typing.axiomatic_decl -> [ `Theory of [ `Nonrec ] ] why_decl_group list
val logic_fun :
  logic_info ->
  logic_info Ast.term_or_assertion -> some_entry list
val axiomatic : string -> Typing.axiomatic_data -> some_entry list
val allocates :
  internal:label option ->
  type_safe:bool ->
  ?region_list:region list ->
  fun_effect -> (Loc.position * Fenv.location list) option -> pred

val prop :
  Lexing.position * Lexing.position ->
  string ->
  is_axiom:bool ->
  label list ->
  logic_info Ast.assertion -> some_entry list

val prepare_fun : fun_info -> fun_spec -> unit

val func :
  fun_info ->
  Lexing.position * Lexing.position ->
  logic_info Ast.fun_spec ->
  (logic_info, fun_info) Ast.expr option -> some_entry list
val logic_type : string * type_var_info list -> some_entry list
val enums : enum_info list -> some_entry list
val enum_cast : enum_info * enum_info -> some_entry list
val exception_ : exception_info -> [ `Module of [ `Safe | `Unsafe ] ] why_decl_group
val exceptions : unit -> some_entry list
val variable : var_info -> [ `Module of [ `Safe | `Unsafe ] ] why_decl_group
val memory : mem_class * region -> [ `Module of [ `Safe | `Unsafe ] ] why_decl_group
val alloc_table : alloc_class * region -> [ `Module of  [ `Safe | `Unsafe ] ] why_decl_group
val tag_table : root_info * region -> [ `Module of  [ `Safe | `Unsafe ] ] why_decl_group
val globals : unit -> some_entry list
val dummies : some_entry list
val struc : struct_info -> some_entry list
val root : root_info -> some_entry list
val alloc :
  arg:('a expr,
       check_size:bool ->
       unbounded integer number expr -> 'a expr,
       'b, [ `Range_0_n | `Singleton ], 'c, 'r)
      arg ->
  alloc_class * region -> pointer_class -> 'r
val free :
  safe:bool ->
  alloc_class * region ->
  pointer_class -> 'a expr -> void expr
val valid_pre : in_param:bool -> effect -> var_info -> pred
val instanceof_pre : effect -> var_info -> pred
