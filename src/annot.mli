(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: annot.mli,v 1.3 2002-10-17 12:52:20 filliatr Exp $ i*)

open Env
open Types
open Logic
open Ast

(*s Default exceptional postcondition (inserted when not given) *)

val default_post : assertion

(*s Maximum of two postconditions. [sup q q'] is made of postconditions
    from [q], when not the default postcondition, and from [q'] otherwise. *)

val sup : postcondition option -> postcondition option -> postcondition option

(*s automatic postcondition for a loop body, i.e. [I and var < var@L] *)

val while_post_block :
  local_env -> predicate asst option -> variant -> typed_program -> 
  postcondition

(*s [normalise p] inserts some automatic annotation on the outermost
    construct of [p] *)

val normalize : typed_program -> typed_program


(*s Useful functions to change the program tree or its annotations,
    to be reused in [Wp] *)

val force_post :
  local_env -> postcondition option -> typed_program -> typed_program

val create_postval : 'a -> 'a asst option

val change_desc : 'a Ast.t -> 'a Ast.t_desc -> 'a Ast.t

