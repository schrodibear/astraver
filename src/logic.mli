
(*i $Id: logic.mli,v 1.6 2002-04-10 08:35:18 filliatr Exp $ i*)

(*s Logic. *)

type constant =
  | ConstInt of int
  | ConstBool of bool
  | ConstUnit
  | ConstFloat of float

type term =
  | Tvar of Ident.t
  | Tbound of Ident.bound
  | Tconst of constant
  | Tapp of Ident.t * term list

type substitution = term Ident.map
type var_substitution = Ident.t Ident.map

(*s Pure types. *)

type pure_type =
  | PTint
  | PTbool
  | PTfloat
  | PTunit
  | PTarray of term * pure_type
  | PTexternal of Ident.t

type predicate =
  | Pvar of Ident.t
  | Papp of Ident.t * term list
  | Ptrue
  | Pfalse
  | Pimplies of predicate * predicate
  | Pif of term * predicate * predicate
  | Pand of predicate * predicate
  | Por of predicate * predicate
  | Pnot of predicate
  | Forall of Ident.t * Ident.bound * pure_type * predicate

  


