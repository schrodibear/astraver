(* Certification of Imperative Programs / Jean-Christophe Filliâtre *)

(*i $Id: types.mli,v 1.8 2002-03-15 10:00:13 filliatr Exp $ i*)

open Logic

(*s Pre- and postconditions. *)

type precondition = 
  { p_assert : bool; 
    p_name : Ident.name; 
    p_value : predicate }

type assertion  = { a_name : Ident.name; a_value : predicate }

type postcondition = assertion

(*s Binders. *)

type 'a binder_type =
  | BindType of 'a
  | BindSet
  | Untyped

type 'a binder = Ident.t * 'a binder_type

(*s Variant. *)

type variant = term * predicate * pure_type (* phi, R, A *)

(*s Types of values... *)

type type_v =
  | Ref       of type_v
  | Array     of term * type_v   (* size x type *)
  | Arrow     of type_v binder list * type_c
  | PureType  of pure_type

(* ... and types of computations. *)

and type_c =
  { c_result_name : Ident.t;
    c_result_type : type_v;
    c_effect : Effect.t;
    c_pre    : precondition list;
    c_post   : postcondition option }

