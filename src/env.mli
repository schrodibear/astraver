(* Certification of Imperative Programs / Jean-Christophe Filli�tre *)

(*i $Id: env.mli,v 1.12 2002-05-07 15:53:23 filliatr Exp $ i*)

open Logic
open Types
open Ast

(* Environment for imperative programs.
 * 
 * Here we manage the global environment, which is imperative,
 * and we provide a functional local environment. 
 *
 * The most important functions, is_in_env, type_in_env and fold_all
 * first look in the local environment then in the global one.
 *)

(* local environments *)

type local_env

val empty : local_env
val add : Ident.t -> type_v -> local_env -> local_env
val add_set : Ident.t -> local_env -> local_env
val is_local : local_env -> Ident.t -> bool
val is_local_set : local_env -> Ident.t -> bool

(* typed programs *)

type typing_info = 
  { env : local_env;
    label : label;
    kappa : type_c }
  
type typed_program = typing_info Ast.t

(* global environment *)

val add_global : Ident.t -> type_v -> typed_program option -> unit
val add_global_set : Ident.t -> unit
val is_global : Ident.t -> bool
val is_global_set : Ident.t -> bool
val lookup_global : Ident.t -> type_v

val all_vars : unit -> Ident.set
val all_refs : unit -> Ident.set

(* a table keeps the program (for extraction) *)

val find_pgm : Ident.t -> typed_program option

(* a table keeps the initializations of mutable objects *)

val initialize : Ident.t -> term -> unit
val find_init : Ident.t -> term

(* access in env (local then global) *)

val type_in_env : local_env -> Ident.t -> type_v
val is_in_env : local_env -> Ident.t -> bool
val is_ref : local_env -> Ident.t -> bool

type type_info = Set | TypeV of type_v
val fold_all : (Ident.t * type_info -> 'a -> 'a) -> local_env -> 'a -> 'a

val add_rec : Ident.t -> local_env -> local_env
val is_rec : Ident.t -> local_env -> bool

