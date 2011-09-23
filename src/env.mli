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



(*s Environment for imperative programs.
 
   Here we manage the global environment, which is imperative,
   and we provide a functional local environment. 
  
   The most important functions, [is_in_env], [type_in_env] and [fold_all]
   first look in the local environment then in the global one. *)

open Cc
open Logic
open Types
open Ast

module StringMap : Map.S with type key = string
module StringSet : Set.S with type elt = string

(*s type schemes *)

module Vset : Set.S with type elt = type_var
module Vmap : Map.S with type key = type_var

type 'a scheme = private { scheme_vars : Vset.t; scheme_type : 'a }
val empty_scheme : 'a -> 'a scheme

(*s AST for typed programs are decorated with local environments *)

type local_env

type typing_info = { 
  t_loc : Loc.position;
  t_env : local_env;
  t_label : label;
  mutable t_userlabel : label;
  t_result_name : Ident.t;
  t_result_type : type_v;
  t_effect : Effect.t;
  t_post : postcondition option 
}
  
type typed_expr = typing_info Ast.t

(*s global environment *)

val add_global : Ident.t -> type_v -> typed_expr option -> unit
val add_global_gen : Ident.t -> type_v scheme -> typed_expr option -> unit
val is_global : Ident.t -> bool
val iter_global : (Ident.t * Types.type_v scheme -> unit) -> unit
val lookup_global : Ident.t -> type_v

(*s types (only global) *)

val add_type : Loc.position -> Ident.t list -> Ident.t -> unit
val is_type : Ident.t -> bool
val type_arity : Ident.t -> int

val iter_type : (Ident.t -> int -> unit) -> unit
val fold_type : (Ident.t -> int -> 'a -> 'a) -> 'a -> 'a

(*s algebraic types (only global) *)

val set_constructors : Ident.t -> Ident.t list -> unit
val is_alg_type : Ident.t -> bool
val alg_type_constructors : Ident.t -> Ident.t list

(*s exceptions (only global) *)

val add_exception : Ident.t -> pure_type option -> unit
val is_exception : Ident.t -> bool
val find_exception : Ident.t -> pure_type option

(*s logical elements *)

type var_subst = type_var Vmap.t

val add_global_logic : Ident.t -> logic_type scheme -> unit
val find_global_logic : Ident.t -> var_subst * logic_type

val iter_global_logic : (Ident.t -> logic_type scheme -> unit) -> unit
val fold_global_logic : (Ident.t -> logic_type scheme -> 'a -> 'a) -> 'a -> 'a
val is_global_logic : Ident.t -> bool
val is_logic_function : Ident.t -> bool

(*s a table keeps the program (for extraction) *)

val find_pgm : Ident.t -> typed_expr option

(*s local environments *)

val empty_progs : unit -> local_env
val empty_logic : unit -> local_env

val add : ?generalize:bool -> Ident.t -> type_v -> local_env -> local_env
val is_local : local_env -> Ident.t -> bool

val find_type_var : Ident.t -> local_env -> type_var

(*s access in env (local then global) *)

val type_in_env : local_env -> Ident.t -> type_v
val is_in_env : local_env -> Ident.t -> bool
val is_ref : local_env -> Ident.t -> bool

val fold_all : (Ident.t * type_v -> 'a -> 'a) -> local_env -> 'a -> 'a

val add_rec : Ident.t -> local_env -> local_env
val is_rec : Ident.t -> local_env -> bool

(*s logical elements *)

val add_logic : Ident.t -> pure_type -> local_env -> local_env
val find_logic : Ident.t -> local_env -> pure_type

val type_v_of_logic : pure_type list -> pure_type -> type_v

(* type variables and generalization/specialization *)

val new_type_var : ?user:bool -> unit -> type_var

val type_var_name : type_var -> string (* for error messages only *)

val generalize_logic_type : logic_type -> logic_type scheme
val generalize_alg_type : alg_type_def -> alg_type_def scheme
val generalize_type_v : type_v -> type_v scheme
val generalize_predicate : predicate -> predicate scheme
val generalize_predicate_def : predicate_def -> predicate_def scheme
val generalize_inductive_def : inductive_def -> inductive_def scheme
val generalize_function_def : function_def -> function_def scheme
val generalize_sequent : sequent -> sequent scheme

val specialize_type_scheme : type_v scheme -> var_subst * type_v
val specialize_logic_type : logic_type scheme -> var_subst * logic_type
val specialize_alg_type : alg_type_def scheme -> var_subst * alg_type_def
val specialize_predicate : predicate scheme -> var_subst * predicate
val specialize_predicate_def : 
  predicate_def scheme -> var_subst * predicate_def
val specialize_inductive_def : 
  inductive_def scheme -> var_subst * inductive_def
val specialize_function_def : 
  function_def scheme -> var_subst * function_def
val specialize_sequent : sequent scheme -> var_subst * sequent

val subst_sequent : var_subst -> sequent -> sequent

val specialize_cc_type : Cc.cc_type -> var_subst * Cc.cc_type
val specialize_validation : 
  Cc.cc_type -> Cc.validation -> var_subst * Cc.cc_type * Cc.validation

val specialize_cc_functional_program : 
  Cc.cc_type -> Cc.cc_functional_program 
  -> var_subst * Cc.cc_type * Cc.cc_functional_program

val instantiate_specialized : var_subst -> instance -> unit

val instantiate_logic_type : logic_type scheme -> instance -> logic_type
val instantiate_predicate : predicate scheme -> instance -> predicate
val instantiate_predicate_def : 
  predicate_def scheme -> instance -> predicate_def
val instantiate_inductive_def : 
  inductive_def scheme -> instance -> inductive_def
val instantiate_function_def : 
  function_def scheme -> instance -> function_def
val instantiate_sequent : sequent scheme -> instance -> sequent

(*s Labels *)

module Label : sig 
  type t 
  val empty : t
  val add : string -> t -> t
  val mem : string -> t -> bool
end

(* debug *)

val dump_type_var : (type_var -> unit) ref

(* misc *)

val bad_arity : Ident.t list -> bool

