(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: annot.mli,v 1.2 2002-10-16 13:46:19 filliatr Exp $ i*)

open Env
open Types
open Logic
open Ast

val force_post :
  local_env -> postcondition option -> typed_program -> typed_program

val create_postval : 'a -> 'a asst option

val change_desc : 'a Ast.t -> 'a Ast.t_desc -> 'a Ast.t

val while_post_block :
  local_env -> predicate asst option -> variant -> typed_program -> assertion

val normalize : typed_program -> typed_program
