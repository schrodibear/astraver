(*
 * The Why certification tool
 * Copyright (C) 2002 Jean-Christophe FILLIATRE
 * 
 * This software is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public
 * License version 2, as published by the Free Software Foundation.
 * 
 * This software is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * 
 * See the GNU General Public License version 2 for more details
 * (enclosed in the file GPL).
 *)

(*i $Id: env.mli,v 1.30 2004-07-13 11:31:24 filliatr Exp $ i*)

(*s Environment for imperative programs.
 
   Here we manage the global environment, which is imperative,
   and we provide a functional local environment. 
  
   The most important functions, [is_in_env], [type_in_env] and [fold_all]
   first look in the local environment then in the global one. *)

open Logic
open Types
open Ast

(*s local environments *)

type local_env

val empty : local_env
val add : Ident.t -> type_v -> local_env -> local_env
val add_set : Ident.t -> local_env -> local_env
val is_local : local_env -> Ident.t -> bool
val is_local_set : local_env -> Ident.t -> bool

(*s typed programs *)

type typing_info = 
  { loc : Loc.t;
    env : local_env;
    label : label;
    obligations : assertion list;
    kappa : type_c }
  
type typed_program = typing_info Ast.t

type 'a scheme = private { scheme_vars : string list; scheme_type : 'a }

type type_info = Set | TypeV of type_v

(*s global environment *)

val add_global : Ident.t -> type_v -> typed_program option -> unit
val add_global_gen : Ident.t -> type_info scheme -> typed_program option -> unit
val add_global_set : Ident.t -> unit
val is_global : Ident.t -> bool
val is_global_set : Ident.t -> bool
val lookup_global : Ident.t -> type_v

val all_vars : unit -> Ident.set
val all_refs : unit -> Ident.set

(*s exceptions (only global) *)

val add_exception : Ident.t -> pure_type option -> unit
val is_exception : Ident.t -> bool
val find_exception : Ident.t -> pure_type option

(*s a table keeps the program (for extraction) *)

val find_pgm : Ident.t -> typed_program option

(*s a table keeps the initializations of mutable objects *)

val initialize : Ident.t -> term -> unit
val find_init : Ident.t -> term

(*s access in env (local then global) *)

val type_in_env : local_env -> Ident.t -> type_v
val is_in_env : local_env -> Ident.t -> bool
val is_ref : local_env -> Ident.t -> bool

val fold_all : (Ident.t * type_info -> 'a -> 'a) -> local_env -> 'a -> 'a

val add_rec : Ident.t -> local_env -> local_env
val is_rec : Ident.t -> local_env -> bool

(*s Logical environment *)

val add_global_logic : Ident.t -> logic_type scheme -> unit
val iter_global_logic : (Ident.t -> logic_type scheme -> unit) -> unit

type logical_env

val add_logic : 
  ?generalize:bool -> Ident.t -> type_v -> logical_env -> logical_env
val is_logic : Ident.t -> logical_env -> bool

val new_type_var : unit -> type_var

val generalize_logic_type : logic_type -> logic_type scheme
val generalize_type_v : type_v -> type_info scheme
val generalize_predicate : predicate -> predicate scheme
val generalize_predicate_def : predicate_def -> predicate_def scheme

val specialize_type_scheme : type_info scheme -> type_var list * type_v
val specialize_logic_type : logic_type scheme -> type_var list * logic_type
val specialize_predicate : predicate scheme -> type_var list * predicate
val specialize_predicate_def : 
  predicate_def scheme -> type_var list * predicate_def

val find_logic : Ident.t -> logical_env -> type_var list * logic_type

val logical_env : local_env -> logical_env

(*s Labels *)

module Label : sig 
  type t 
  val empty : t
  val add : string -> t -> t
  val mem : string -> t -> bool
end
