(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: ltyping.mli,v 1.4 2002-07-08 13:21:27 filliatr Exp $ i*)

(*s Typing on the logical side *)

open Logic
open Types
open Ptree
open Ast
open Env

val type_v : 
  Loc.t -> LabelSet.t -> local_env -> logical_env -> ptype_v -> type_v

val type_c :
  Loc.t -> LabelSet.t -> local_env -> logical_env -> ptype_c -> type_c

val predicate : 
  LabelSet.t -> logical_env -> lexpr -> predicate

val term : 
  LabelSet.t -> logical_env -> lexpr -> term * pure_type

val type_pre : LabelSet.t -> logical_env -> lexpr pre -> precondition
val type_post : LabelSet.t -> logical_env -> lexpr post -> postcondition

val binders : 
  Loc.t -> LabelSet.t -> local_env -> logical_env -> 
  ptype_v binder list -> 
  type_v binder list * local_env * logical_env

(* errors *)

val expected_num : Loc.t -> 'a
