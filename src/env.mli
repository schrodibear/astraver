(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: env.mli,v 1.4 2002-03-01 12:03:44 filliatr Exp $ i*)

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
val add : (Ident.t * type_v) -> local_env -> local_env
val add_set : Ident.t -> local_env -> local_env
val is_local : local_env -> Ident.t -> bool
val is_local_set : local_env -> Ident.t -> bool

(* typed programs *)

type typing_info = 
  { env : local_env;
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

type type_info = Set | TypeV of type_v
val fold_all : (Ident.t * type_info -> 'a -> 'a) -> local_env -> 'a -> 'a

(* local environnements also contains a list of recursive functions
 * with the associated variant *)

val add_recursion : Ident.t * (Ident.t * variant) -> local_env -> local_env
val find_recursion : Ident.t -> local_env -> Ident.t * variant

(* We also maintain a table of the currently edited proofs of programs
 * in order to add them in the environnement when the user does Save *)

(*i
val new_edited : Ident.t -> type_v * typed_program -> unit
val is_edited : Ident.t -> bool
val register : Ident.t -> Ident.t -> unit
i*)

