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

open Output_ast


(** {1 Main translation functions} *)


(** {2 effects} *)
val reads :
  type_safe:bool ->
  global_assertion:bool ->
  Fenv.logic_info Ast.location list ->
  Env.mem_class * Env.region -> term

val collect_pset_locations :
  type_safe:bool ->
  global_assertion:bool ->
  Env.label ->
  Fenv.logic_info Ast.location ->
  term

(** {2 types} *)

val tr_logic_type :
  string * Type_var.t list ->
  why_decl list -> why_decl list

val struc :
  Env.struct_info -> why_decl list -> why_decl list

val root :
  Env.root_info -> why_decl list -> why_decl list

val tr_enum_type :
  Env.enum_info -> why_decl list -> why_decl list

val tr_enum_type_pair :
  Env.enum_info ->
  Env.enum_info -> why_decl list -> why_decl list

(** {2 variables and heap} *)

val tr_variable :
  Env.var_info ->
  'a -> why_decl list -> why_decl list

val tr_region :
  Env.region -> why_decl list -> why_decl list

val tr_memory :
  Env.mem_class * Env.region ->
  why_decl list -> why_decl list

val tr_alloc_table :
  Env.alloc_class * Env.region ->
  why_decl list -> why_decl list

val tr_tag_table :
  Env.root_info * Env.region ->
  why_decl list -> why_decl list

(** {2 exceptions} *)


val tr_exception :
  Env.exception_info ->
  why_decl list -> why_decl list


(** {2 terms and propositions} *)

val term_coerce :
  type_safe:'a ->
  global_assertion:bool ->
  Env.label ->
  ?cast:bool ->
  Why_loc.position ->
  Env.jc_type ->
  Env.jc_type ->
  < region : Region.RegionTable.key; .. > ->
    term -> term

val term :
  ?subst:term Envset.VarMap.t ->
  type_safe:bool ->
  global_assertion:bool ->
  relocate:bool ->
  Env.label ->
  Env.label ->
  Fenv.logic_info Ast.term -> term

val assertion :
  type_safe:bool ->
  global_assertion:bool ->
  relocate:bool ->
  Env.label ->
  Env.label ->
  Fenv.logic_info Ast.assertion -> assertion


(** {2 theories} *)

val tr_axiom :
  Why_loc.position ->
  string ->
  is_axiom:bool ->
  Env.label list ->
  Fenv.logic_info Ast.assertion ->
  why_decl list -> why_decl list

val tr_axiomatic_decl :
  why_decl list ->
  Typing.axiomatic_decl -> why_decl list

(** {2 functions} *)

val pre_tr_fun :
  Fenv.fun_info ->
  'a -> Fenv.logic_info Ast.fun_spec -> 'b -> 'c -> 'c

val tr_fun :
  Fenv.fun_info ->
  Why_loc.position ->
  Fenv.fun_spec ->
  (Fenv.logic_info, Fenv.fun_info) Ast.expr option ->
  why_decl list -> why_decl list

val tr_specialized_fun :
  string ->
  string ->
  string Envset.StringMap.t ->
  why_decl list -> why_decl list

(** {2 locations and explanations} *)

(*
val print_locs : Format.formatter -> unit
  *)

(*
  Local Variables:
  compile-command: "unset LANG; make -j -C .. bin/jessie.byte"
  End:
*)
