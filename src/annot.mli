(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: annot.mli,v 1.1 2002-10-15 09:05:53 filliatr Exp $ i*)

open Env
open Types
open Logic
open Ast

val force_post :
  local_env -> postcondition option -> typed_program -> typed_program

val create_postval : 'a -> 'a asst option

val change_desc : 'a Ast.t -> 'a Ast.t_desc -> 'a Ast.t

val while_post_block :
  local_env -> predicate asst option -> variant ->
  typed_program -> postcondition

val normalize : typed_program -> typed_program
