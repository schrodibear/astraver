(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: ltyping.mli,v 1.1 2002-07-05 16:14:09 filliatr Exp $ i*)

(*s Typing on the logical side *)

open Logic
open Types
open Ast
open Env

val type_v : 
  Loc.t option -> LabelSet.t -> local_env -> logical_env -> 
  parsed_type_v -> type_v

val type_c :
  Loc.t option -> LabelSet.t -> local_env -> logical_env -> 
  parsed_type_c -> type_c

val predicate : 
  LabelSet.t -> logical_env -> ppredicate -> predicate

val term : 
  LabelSet.t -> logical_env -> ppredicate -> term * pure_type

val type_pre : LabelSet.t -> logical_env -> ppredicate pre -> precondition
val type_post : LabelSet.t -> logical_env -> ppredicate post -> postcondition

val binders : 
  Loc.t option -> LabelSet.t -> local_env -> logical_env -> 
  ppredicate ptype_v binder list -> 
  type_v binder list * local_env * logical_env

(* errors *)

val expected_cmp : Loc.t -> 'a
val expected_num : Loc.t -> 'a
