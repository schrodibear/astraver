(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: types.mli,v 1.10 2002-07-05 16:14:09 filliatr Exp $ i*)

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

(*s Types of values... *)

type 'a ptype_v =
  | Ref       of 'a ptype_v
  | Array     of term * 'a ptype_v   (* size x type *)
  | Arrow     of 'a ptype_v binder list * 'a ptype_c
  | PureType  of pure_type

(* ... and types of computations. *)

and 'a ptype_c =
  { c_result_name : Ident.t;
    c_result_type : 'a ptype_v;
    c_effect : Effect.t;
    c_pre    : 'a pre list;
    c_post   : 'a post option }

type type_v = predicate ptype_v
type type_c = predicate ptype_c
