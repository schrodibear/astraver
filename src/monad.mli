(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: monad.mli,v 1.19 2002-09-18 06:27:31 filliatr Exp $ i*)

(*s Main part of the translation of imperative programs into functional ones
    (with module [Mlize]) *)

open Logic
open Types
open Ast
open Cc
open Env

(*s Translation of types *)

val trad_type_v : Rename.t -> local_env -> type_v -> cc_type
val trad_type_c : Rename.t -> local_env -> type_c -> cc_type
val trad_imp_type  : Rename.t -> local_env -> type_v -> cc_type
val trad_type_in_env : Rename.t -> local_env -> Ident.t -> cc_type

(*s Basic monadic operators. They operate over values of type [interp] i.e.
    functions building a [cc_term] given a renaming structure. *)

type interp = Rename.t -> predicate cc_term

(* The [unit] operator encapsulates a term in a computation. *)

type result = 
  | Value of term
  | Exn of Ident.t * term option

val unit : typing_info -> result -> interp

(* [compose k1 e1 e2] evaluates computation [e1] of type [k1] and 
   passes its result (actually, a variable naming this result) to a
   second computation [e2]. [apply] is a variant of [compose] where
   [e2] is abstracted (typically, a function) and thus must be applied
   to its input. *)

val compose : 
  typing_info -> interp -> typing_info -> (Ident.t -> interp) -> interp
val apply   : 
  typing_info -> interp -> typing_info -> (Ident.t -> interp) -> interp

(*s Monadic operator to raise exceptions *)

val exn : typing_info -> Ident.t -> term option -> interp

(*s Other monadic operators. *)

val cross_label : string -> interp -> interp

val insert_pre : local_env -> precondition -> interp -> interp

val insert_many_pre : local_env -> precondition list -> interp -> interp

val abstraction : typing_info -> interp -> interp

val fresh : Ident.t -> (Ident.t -> interp) -> interp

(*s Well-founded recursion. *)

val wfrec : variant -> typing_info -> (interp -> interp) -> interp

val wfrec_with_binders : 
  cc_binder list -> variant -> typing_info -> (interp -> interp) -> interp

(*s Table for recursive functions' interpretation *)

val is_rec : Ident.t -> bool
val find_rec : Ident.t -> interp
val with_rec : Ident.t -> interp -> ('a -> 'b) -> 'a -> 'b
