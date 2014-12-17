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

open Jc_why_output_ast


(** {1 Main translation functions} *)


(** {2 effects} *)
val reads :
  type_safe:bool ->
  global_assertion:bool ->
  Jc_fenv.logic_info Jc_ast.location list ->
  Jc_env.mem_class * Jc_env.region -> term

val collect_pset_locations :
  type_safe:bool ->
  global_assertion:bool ->
  Jc_env.label ->
  Jc_fenv.logic_info Jc_ast.location ->
  term

(** {2 types} *)

val tr_logic_type :
  string * Jc_type_var.t list ->
  why_decl list -> why_decl list

val tr_struct :
  Jc_env.struct_info -> why_decl list -> why_decl list

val tr_root :
  Jc_env.root_info -> why_decl list -> why_decl list

val tr_enum_type :
  Jc_env.enum_info -> why_decl list -> why_decl list

val tr_enum_type_pair :
  Jc_env.enum_info ->
  Jc_env.enum_info -> why_decl list -> why_decl list

(** {2 variables and heap} *)

val tr_variable :
  Jc_env.var_info ->
  'a -> why_decl list -> why_decl list

val tr_region :
  Jc_env.region -> why_decl list -> why_decl list

val tr_memory :
  Jc_env.mem_class * Jc_env.region ->
  why_decl list -> why_decl list

val tr_alloc_table :
  Jc_env.alloc_class * Jc_env.region ->
  why_decl list -> why_decl list

val tr_tag_table :
  Jc_env.root_info * Jc_env.region ->
  why_decl list -> why_decl list

(** {2 exceptions} *)


val tr_exception :
  Jc_env.exception_info ->
  why_decl list -> why_decl list


(** {2 terms and propositions} *)

val term_coerce :
  type_safe:'a ->
  global_assertion:bool ->
  Jc_env.label ->
  ?cast:bool ->
  Loc.position ->
  Jc_env.jc_type ->
  Jc_env.jc_type ->
  < region : Jc_region.RegionTable.key; .. > ->
    term -> term

val term :
  ?subst:term Jc_envset.VarMap.t ->
  type_safe:bool ->
  global_assertion:bool ->
  relocate:bool ->
  Jc_env.label ->
  Jc_env.label ->
  Jc_fenv.logic_info Jc_ast.term -> term

val assertion :
  type_safe:bool ->
  global_assertion:bool ->
  relocate:bool ->
  Jc_env.label ->
  Jc_env.label ->
  Jc_fenv.logic_info Jc_ast.assertion -> assertion


(** {2 theories} *)

val tr_axiom :
  Loc.position ->
  string ->
  is_axiom:bool ->
  Jc_env.label list ->
  Jc_fenv.logic_info Jc_ast.assertion ->
  why_decl list -> why_decl list

val tr_axiomatic_decl :
  why_decl list ->
  Jc_typing.axiomatic_decl -> why_decl list

(** {2 functions} *)

val pre_tr_fun :
  Jc_fenv.fun_info ->
  'a -> Jc_fenv.logic_info Jc_ast.fun_spec -> 'b -> 'c -> 'c

val tr_fun :
  Jc_fenv.fun_info ->
  Loc.position ->
  Jc_fenv.fun_spec ->
  (Jc_fenv.logic_info, Jc_fenv.fun_info) Jc_ast.expr option ->
  why_decl list -> why_decl list

val tr_specialized_fun :
  string ->
  string ->
  string Jc_envset.StringMap.t ->
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
