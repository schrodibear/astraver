(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: types.mli,v 1.11 2002-07-08 09:02:28 filliatr Exp $ i*)

open Logic

(*s Pre- and postconditions. *)

type 'a pre = 
  { p_assert : bool; 
    p_name : Ident.name; 
    p_value : 'a }

type 'a asst = { a_name : Ident.name; a_value : 'a }

type 'a post = 'a asst

type precondition = predicate pre

type assertion = predicate asst

type postcondition = assertion

(*s Binders. *)

type 'a binder_type =
  | BindType of 'a
  | BindSet
  | Untyped

type 'a binder = Ident.t * 'a binder_type

(*s Typed types *)

type type_v = 
  | Ref of type_v
  | Array of term * type_v
  | Arrow of type_v binder list * type_c
  | PureType of pure_type

and type_c = 
  { c_result_name : Ident.t;
    c_result_type : type_v;
    c_effect : Effect.t;
    c_pre    : precondition list;
    c_post   : postcondition option }

